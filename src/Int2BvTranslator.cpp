// Int2BvTranslator.cpp

#include "Int2BvTranslator.h"

namespace multi_theory_horn {

    Int2BvTranslator::Int2BvTranslator(z3::context& c, unsigned bv_size) : 
        ctx(c),
        m_bv_size(bv_size)
    {}

    void Int2BvTranslator::reset() {
        m_translate.clear();
        m_vars.clear();
    }

    bool Int2BvTranslator::is_special_basic(const z3::expr& e) const {
        return is_basic(e) && (e.is_ite() || e.is_eq());
    }

    bool Int2BvTranslator::is_basic(const z3::expr& e) const {
        Z3_decl_kind f = e.decl().decl_kind();
        return (Z3_OP_TRUE <= f && f <= Z3_OP_OEQ);
    }

    z3::expr Int2BvTranslator::translate(const z3::expr& e) {
        Z3_ast key = e; // implicit cast to Z3_ast
        auto it = m_translate.find(key);
        // This condition is important, it prevents redundant work
        if (it != m_translate.end())
            return it->second;

        z3::expr r(ctx);    
        if (e.is_quantifier()) {
            // In case of horn clauses, this shouldn't be reached
            ASSERT_FALSE("Quantifiers should not be present in CHC Int expressions");
            r = e; 
        }
        else if (e.is_var()) {
            // map each int variable to a BV var of same name
            // TODO: Deal with vars
            // TODO: Need to find a case in which this is needed
            NOT_IMPLEMENTED();
        }
        else { // is_app
            if (e.is_const() && !e.is_numeral()) {
                // Note: numerals are handled in translate_bv: Z3_OP_ANUM
                // Constants are apps with no arguments
                std::string name = e.decl().name().str();
                r = ctx.bv_const(name.c_str(), m_bv_size);
                m_vars.push_back(key);
            }
            else if (is_special_basic(e)) {
                r = translate_special_basic(e);
            }
            else if (is_basic(e)) {
                r = translate_basic(e);
            }
            else { // is_int
                // Translate arguments
                assert(e.is_int() && "Expected an Int expression");
                r = translate_int(e);
            }
        }

        m_translate.emplace(key, r);
        return r;
    }

    z3::expr Int2BvTranslator::translate_int(const z3::expr& e) {
        // Get INT operation kind
        Z3_decl_kind f = e.decl().decl_kind();

        // Collect arguments
        std::vector<z3::expr> args;
        for (unsigned i = 0; i < e.num_args(); ++i)
            args.push_back(translate(e.arg(i)));
        
        // Result expression
        z3::expr r(ctx);

        switch (f) {
            // Arithmetic
            case Z3_OP_ANUM:
                // Translate numeral to BV
                assert(e.is_numeral() && "Z3_OP_ANUM should only be used with numerals");
                r = ctx.bv_val(e.get_numeral_int64(), m_bv_size);
                break;
            case Z3_OP_AGNUM:
            case Z3_OP_TO_REAL:
            case Z3_OP_TO_INT:
            case Z3_OP_IS_INT:
            case Z3_OP_DIV:
                ASSERT_FALSE("We're not supposed to encounter real numbers");
                break;
            case Z3_OP_LE:
                r = args[0] <= args[1];
                break;
            case Z3_OP_GE:
                r = args[0] >= args[1];
                break;
            case Z3_OP_LT:
                r = args[0] < args[1];
                break;
            case Z3_OP_GT:
                r = args[0] > args[1];
                break;
            case Z3_OP_ADD:
                r = args[0] + args[1];
                break;
            case Z3_OP_SUB:
                r = args[0] - args[1];
                break;
            case Z3_OP_UMINUS:
                r = -args[0];
                break;
            case Z3_OP_MUL:
                r = args[0] * args[1];
                break;
            case Z3_OP_IDIV:
                r = args[0] / args[1];
                break;          
            case Z3_OP_REM:
                // Use signed version of rem
                r = srem(args[0], args[1]);
                break;
            case Z3_OP_MOD:
                // Use signed version of mod
                r = smod(args[0], args[1]);
                break;
            case Z3_OP_POWER:
            case Z3_OP_ABS:
                ASSERT_FALSE("NOT SUPPORTED through z3++.h");
                break;
            default:
                // fallback: treat as uninterpreted
                // std::cout << f << std::endl;
                ASSERT_FALSE("Unsupported Int operation");
        }

        return r;
    }

    z3::expr Int2BvTranslator::translate_special_basic(const z3::expr& e) {
        assert(is_basic(e) && "Expected a basic expression (equality or ite)");
        if (e.is_ite()) {
            // ite is translated to ite
            z3::expr cond = translate(e.arg(0));
            z3::expr then_branch = translate(e.arg(1));
            z3::expr else_branch = translate(e.arg(2));
            return ite(cond, then_branch, else_branch);
        }
        else {
            // Equality
            z3::expr lhs = translate(e.arg(0));
            z3::expr rhs = translate(e.arg(1));
            return lhs == rhs;
        }
        return e;
    }

    z3::expr Int2BvTranslator::translate_basic(const z3::expr& e) {
        assert(!is_special_basic(e) && "Expected a basic expression (not ite or equality)");
        z3::expr_vector new_args(ctx);
        for (unsigned i = 0; i < e.num_args(); ++i) {
            new_args.push_back(translate(e.arg(i)));
        }
        
        // Create a new application with the translated arguments
        return e.decl()(new_args);
    }

} // namespace multi_theory_horn
