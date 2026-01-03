#include "mth_utils.h"

namespace multi_theory_horn {

    static int get_num_conjuncts(const z3::expr& e) {
        if (e.is_and()) {
            return e.num_args();
        }
        return 1;
    }

    static bool is_uninterpreted_predicate(const z3::expr& e) {
        return e.decl().decl_kind() == Z3_OP_UNINTERPRETED;
    }

    static bool is_signed_bv_op(Z3_decl_kind k) {
        switch (k) {
            case Z3_OP_SLEQ:
            case Z3_OP_SGEQ:
            case Z3_OP_SLT:
            case Z3_OP_SGT:
            case Z3_OP_BSDIV:
            case Z3_OP_BSREM:
            case Z3_OP_BSMOD:
            case Z3_OP_BSMUL_NO_OVFL:
            case Z3_OP_BSMUL_NO_UDFL:
            case Z3_OP_BSDIV_I:
                return true;
            default:
                return false;
        }
    }

    static void set_signedness(Signedness& current, bool is_signed, bool is_unsigned) {
        assert(!(is_signed && is_unsigned) && "Expression cannot be both signed and unsigned");

        if (is_signed) {
            if (current == Signedness::UNKNOWN) {
                current = Signedness::SIGNED;
            }
            else if (current == Signedness::UNSIGNED) {
                current = Signedness::CONFLICT;
            }
        }
        else if (is_unsigned) {
            if (current == Signedness::UNKNOWN) {
                current = Signedness::UNSIGNED;
            }
            else if (current == Signedness::SIGNED) {
                current = Signedness::CONFLICT;
            }
        }
        else {
            current = Signedness::UNKNOWN;
        }
    }

    static bool is_unsigned_bv_op(Z3_decl_kind k) {
        switch (k) {
            case Z3_OP_ULEQ:
            case Z3_OP_UGEQ:
            case Z3_OP_ULT:
            case Z3_OP_UGT:
            case Z3_OP_BUDIV:
            case Z3_OP_BUREM:
            case Z3_OP_BUMUL_NO_OVFL:
            case Z3_OP_BUDIV_I:
                return true;
            default:
                return false;
        }
    }

    static bool is_bit_manipulating_bv_op(Z3_decl_kind k) {
        switch (k) {
            case Z3_OP_CONCAT:
            case Z3_OP_EXTRACT:
            case Z3_OP_REPEAT:
            case Z3_OP_BAND:
            case Z3_OP_BOR:
            case Z3_OP_BNOT:
            case Z3_OP_BXOR:
            case Z3_OP_BNAND:
            case Z3_OP_BNOR:
            case Z3_OP_BXNOR:
            case Z3_OP_SIGN_EXT:
            case Z3_OP_ZERO_EXT:
            case Z3_OP_BSHL:
            case Z3_OP_BLSHR:
            case Z3_OP_BASHR:
            case Z3_OP_ROTATE_LEFT:
            case Z3_OP_ROTATE_RIGHT:
            case Z3_OP_EXT_ROTATE_LEFT:
            case Z3_OP_EXT_ROTATE_RIGHT:
                return true;
            default:
                return false;
        }
    }

    static bool is_sign_neutral_bv_op(Z3_decl_kind k) {
        return (Z3_OP_BNUM <= k && k <= Z3_OP_BMUL) || (Z3_OP_TRUE <= k && k <= Z3_OP_OEQ);
    }

    static void analyze_expr(z3::expr const& e, bool is_uninterpreted_predicate_arg, ClauseAnalysisResult& result) {
        if (e.is_quantifier()) {
            // In case of horn clauses, this shouldn't be reached
            // This should be unrecahable as quantifiers should not be present
            // in the CHC body.
            UNREACHABLE();
        }
        else if (e.is_var()) {
            result.all_vars.insert(e);
            if (is_uninterpreted_predicate_arg) {
                result.bound_vars.insert(e);
            }
        }
        else {
            // is_app
            if (e.is_const())
                return;

            // Analyze signedness and bit-manipulating ops
            Z3_decl_kind k = e.decl().decl_kind();
            bool is_sign_neutral = is_sign_neutral_bv_op(k);
            bool is_signed = is_signed_bv_op(k);
            bool is_unsigned = is_unsigned_bv_op(k);
            bool is_bit_manipulating = is_bit_manipulating_bv_op(k);
            bool is_sign_known = is_signed || is_unsigned;
            assert(is_sign_known || is_sign_neutral || is_bit_manipulating && "Dealing with an unknown application");
            if (is_bit_manipulating) {
                result.has_bit_manipulating_apps = true;
            }

            set_signedness(result.is_signed, is_signed, is_unsigned);

            for (unsigned i = 0; i < e.num_args(); ++i) {
                analyze_expr(e.arg(i), is_uninterpreted_predicate_arg, result);
            }
        }
    }

    static void analyze_uninterpreted_predicate(z3::expr const& e, ClauseAnalysisResult& result) {
        for (unsigned i = 0; i < e.num_args(); ++i) {
            analyze_expr(e.arg(i), /*is_uninterpreted_predicate_arg*/ true, result);
        }
    }

    static void analyze_rule(z3::expr const& body, z3::expr const& head, ClauseAnalysisResult& result) {
        int conjunct_count = get_num_conjuncts(body);
        for (int i = 0; i < conjunct_count; ++i) {
            z3::expr conjunct = (conjunct_count == 1) ? body : body.arg(i);
            // Check if the conjunct is a predicate application
            if (is_uninterpreted_predicate(conjunct)) {
                analyze_uninterpreted_predicate(conjunct, result);
            }
            else {
                analyze_expr(conjunct, /*is_uninterpreted_predicate_arg*/ false, result);
            }
        }
    }

    // Checks if all vars have the same bv_size, and sets result.bv_size accordingly.
    // If not, result.bv_size is set to UNDETERM_BV_SIZE.
    static void analyze_vars(z3::expr_vector const& vars, ClauseAnalysisResult& result) {
        unsigned common_bv_size = UNDETERM_BV_SIZE;
        bool first = true;
        for (unsigned i = 0; i < vars.size(); ++i) {
            z3::sort var_sort = vars[i].get_sort();
            assert(var_sort.is_bv() && "Variable is expected to be of bv sort");
            unsigned var_bv_size = var_sort.bv_size();
            assert(var_bv_size > 0 && "Bit-vector size must be greater than 0");
            if (first) {
                common_bv_size = var_bv_size;
                first = false;
                continue;
            }
            if (var_bv_size != common_bv_size) {
                common_bv_size = UNDETERM_BV_SIZE;
                break;
            }
        }
        result.bv_size = common_bv_size;
    }

    z3::expr_vector get_clause_vars(z3::expr const& clause) {
        z3::context& c = clause.ctx();
        z3::expr_vector vars(c);
        for (int j = 0; j < Z3_get_quantifier_num_bound(c, clause); j++) {
            z3::symbol sym = z3::symbol(c, Z3_get_quantifier_bound_name(c, clause, j));
            z3::expr var = c.constant(sym, z3::sort(c, Z3_get_quantifier_bound_sort(c, clause, j)));
            vars.push_back(var);
        }
        return vars;
    }

    ClauseAnalysisResult analyze_clause(z3::context& ctx, z3::expr const& clause) {
        assert(clause.is_quantifier() && "The clause must be a quantifier");
        ClauseAnalysisResult result(ctx);

        z3::expr_vector vars = get_clause_vars(clause);
        analyze_vars(vars, result);

        // TODO: Implement query analysis
        if (clause.is_exists())
            NOT_IMPLEMENTED();
        else if (clause.is_forall()) {
            assert(clause.body().is_implies() && "The clause body must be an implication");
            z3::expr body = clause.body().arg(0);
            z3::expr head = clause.body().arg(1);

            // TODO: Implement query analysis
            if (head.is_false())
                NOT_IMPLEMENTED();

            analyze_rule(body, head, result);
        }
        else {
            // Clause should be a forall or exists clause
            UNREACHABLE();
        }

        return result;
    }

    // ====================================================================
    // ClauseAnalysisResult methods
    // ====================================================================

    std::ostream& operator<<(std::ostream& os, const ClauseAnalysisResult& result) {
        os << "Clause Analysis Result:" << std::endl;
        os << "  Signedness: ";
        switch (result.is_signed) {
            case Signedness::UNKNOWN:
                os << "UNKNOWN";
                break;
            case Signedness::SIGNED:
                os << "SIGNED";
                break;
            case Signedness::UNSIGNED:
                os << "UNSIGNED";
                break;
            case Signedness::CONFLICT:
                os << "CONFLICT";
                break;
        }
        os << std::endl;

        os << "  BV Size: ";
        if (result.is_bv_size_determined()) {
            os << result.bv_size;
        } else {
            os << "UNDETERMINED";
        }
        os << std::endl;

        os << "  Has Bit-Manipulating Apps: " << (result.has_bit_manipulating_apps ? "Yes" : "No") << std::endl;

        os << "  Bound Variables: ";
        int num_bound_vars = result.bound_vars.size();
        for (int i = 0; i < num_bound_vars; ++i) {
            auto var = *std::next(result.bound_vars.begin(), i);
            os << var;
            if (i != num_bound_vars - 1) {
                os << ", ";
            }
        }
        os << std::endl;

        os << "  All Variables: ";
        int num_all_vars = result.all_vars.size();
        for (int i = 0; i < num_all_vars; ++i) {
            auto var = *std::next(result.all_vars.begin(), i);
            os << var;
            if (i != num_all_vars - 1) {
                os << ", ";
            }
        }
        os << std::endl;
        return os;
    }
}