#include "mth_utils.h"

namespace multi_theory_horn {
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
        } else {
            // Otherwise, don't change the current signedness
            return;
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

    // This function is a "hack" to extract the variable index from a z3::expr variable.
    // The Z3 C++ API does not expose a direct method to get the variable index.
    // Therefore, we convert the variable to string and parse the index.
    // When printing a variable, Z3 uses the format (:var <index>)
    static int extract_var_index(z3::expr const& var) {
        assert(var.is_var() && "Expression is not a variable");
        std::string var_str = var.to_string();
        size_t start_pos = var_str.find(":var ") + 5; // Length of ":var " is 5
        size_t end_pos = var_str.find(")", start_pos);
        std::string index_str = var_str.substr(start_pos, end_pos - start_pos);
        return std::stoi(index_str);
    }

    static void analyze_expr(z3::expr const& e, bool in_pred_body, ClauseAnalysisResult& result) {
        if (e.is_quantifier()) {
            // In case of horn clauses, this shouldn't be reached
            // This should be unrecahable as quantifiers should not be present
            // in the CHC body.
            UNREACHABLE();
        }
        else if (e.is_var()) {
            result.all_vars.insert(e);
            int var_index = extract_var_index(e);
            result.var_index_map.emplace(e, var_index);
            if (in_pred_body) {
                result.in_pred_body_vars.insert(e);
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
                analyze_expr(e.arg(i), in_pred_body, result);
            }
        }
    }

    static void analyze_uninterpreted_predicate(z3::expr const& e, bool is_in_body, ClauseAnalysisResult& result) {
        for (unsigned i = 0; i < e.num_args(); ++i) {
            analyze_expr(e.arg(i), /*in_pred_body*/ is_in_body, result);
        }
    }

    static void analyze_rule(z3::expr const& body, z3::expr const& head, ClauseAnalysisResult& result) {
        z3::expr_vector conjuncts = get_conjuncts(body);
        int conjunct_count = conjuncts.size();
        for (int i = 0; i < conjunct_count; ++i) {
            z3::expr conjunct = conjuncts[i];
            // Check if the conjunct is a predicate application
            if (is_uninterpreted_predicate(conjunct)) {
                analyze_uninterpreted_predicate(conjunct, /*is_in_body*/ true, result);
            }
            else {
                analyze_expr(conjunct, /*in_pred_body*/ false, result);
            }
        }

        assert(is_uninterpreted_predicate(head) && "The head of a rule must be an uninterpreted predicate");
        analyze_uninterpreted_predicate(head, /*is_in_body*/ false, result);
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
    // MTHFixedpointSet methods
    // ====================================================================

    bool MTHFixedpointSet::check_and_set_signedness(bool incoming_sign) {
        if (!global_is_signed.has_value()) {
            global_is_signed = incoming_sign;
            return true;
        }
        return global_is_signed.value() == incoming_sign;
    }

    bool MTHFixedpointSet::hasBVSolver() const {
        return bv_solver.has_value();
    }

    z3::fixedpoint& MTHFixedpointSet::getOrInitBVSolver() {
        if (!bv_solver.has_value())
            bv_solver.emplace(ctx);
        return *bv_solver;
    }

    z3::fixedpoint& MTHFixedpointSet::getBVSolver() {
        assert(bv_solver.has_value() && 
            "BV Solver not found.");
        return *bv_solver;
    }

    bool MTHFixedpointSet::hasIAUFSolver(unsigned bv_size) const {
        return iauf_solvers.find(bv_size) != iauf_solvers.end();
    }

    z3::fixedpoint& MTHFixedpointSet::getOrInitIAUFSolver(unsigned bv_size) {
        auto it = iauf_solvers.find(bv_size);
        if (it != iauf_solvers.end())
            return it->second;
        
        auto result = iauf_solvers.emplace(
            std::piecewise_construct,
            std::forward_as_tuple(bv_size),
            std::forward_as_tuple(ctx)
        );

        return result.first->second;
    }

    z3::fixedpoint& MTHFixedpointSet::getIAUFSolver(unsigned bv_size) {
        auto it = iauf_solvers.find(bv_size);
        assert(it != iauf_solvers.end() && "IAUF Solver not found for the requested bv_size.");
        return it->second;
    }

    z3::symbol MTHFixedpointSet::get_fresh_rule_name(bool is_query) {
        std::string name_str = is_query ? query_name : rule_name;
        name_str += std::to_string(rule_count);
        rule_count++;
        return ctx.str_symbol(name_str.c_str());
    }

    std::ostream & operator<<(std::ostream& os, const MTHFixedpointSet& mth_fp_set) {
        os << "MTHFixedpointSet - ";
        if (mth_fp_set.global_is_signed.has_value()) {
            os << "(Global Signedness: " << (mth_fp_set.global_is_signed.value() ? "SIGNED" : "UNSIGNED") << ")" << std::endl;
        } else {
            os << "(Global Signedness: UNDETERMINED)" << std::endl;
        }

        if (mth_fp_set.bv_solver.has_value()) {
            os << "  BV Solver: Initialized" << std::endl;
            os << *(mth_fp_set.bv_solver);
        } else {
            os << "  BV Solver: Not Initialized" << std::endl;
        }
        os << std::endl;

        os << "  IAUF Solvers:" << std::endl;
        if (mth_fp_set.iauf_solvers.empty()) {
            os << "    None" << std::endl;
        } else {
            for (const auto& [bv_size, solver] : mth_fp_set.iauf_solvers) {
                os << "    BV Size " << bv_size << ": Initialized" << std::endl;
                os << solver;
                os << std::endl;
            }
        }
        os << std::endl;
        return os;
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

        os << "  In Predicate Body: ";
        int num_in_pred_body = result.in_pred_body_vars.size();
        for (int i = 0; i < num_in_pred_body; ++i) {
            auto var = *std::next(result.in_pred_body_vars.begin(), i);
            os << var;
            if (i != num_in_pred_body - 1) {
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

        os << "  Variable Index Map: " << std::endl;
        for (const auto& [var, index] : result.var_index_map) {
            os << "    " << var << " -> " << index << std::endl;
        }
        os << std::endl;
        return os;
    }
}