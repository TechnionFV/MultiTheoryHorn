// Bv2IntTranslator.cpp

#include "Bv2IntTranslator.h"

namespace multi_theory_horn {

    Bv2IntTranslator::Bv2IntTranslator(z3::context& c, bool is_signed, const VarMap& bv2int_var_map): 
        ctx(c),
        m_is_signed(is_signed),
        m_vars(c),
        m_UF_counter(0),
        m_bv2int_var_map(bv2int_var_map)
    {}

    void Bv2IntTranslator::reset() {
        m_translate.clear();
        m_lemmas.clear();
    }

    bool Bv2IntTranslator::is_special_basic(const z3::expr& e) const {
        return is_basic(e) && (e.is_ite() || e.is_eq());
    }

    bool Bv2IntTranslator::is_basic(const z3::expr& e) const {
        Z3_decl_kind f = e.decl().decl_kind();
        return (Z3_OP_TRUE <= f && f <= Z3_OP_OEQ);
    }

    bool Bv2IntTranslator::is_casting(const z3::expr& e) const {
        Z3_decl_kind f = e.decl().decl_kind();
        return f == Z3_OP_BV2INT || f == Z3_OP_INT2BV;
    }

    bool Bv2IntTranslator::is_bv_relation(const z3::expr& e) const {
        Z3_decl_kind f = e.decl().decl_kind();
        bool has_bv_arg = any_of(e.args(), [&](z3::expr arg) { return arg.is_bv(); });
        return Z3_OP_ULEQ <= f && f <= Z3_OP_SGT && has_bv_arg;
    }

    z3::expr Bv2IntTranslator::translate(const z3::expr& e) {
        Z3_ast key = e; // implicit cast to Z3_ast
        auto it = m_translate.find(key);
        // This condition is important, it prevents redundant work
        if (it != m_translate.end()) 
            return it->second;

        z3::expr r(ctx);    
        if (e.is_quantifier()) {
            // In case of horn clauses, this shouldn't be reached
            // This should be unrecahable as quantifiers should not be present
            // in the CHC BV expressions.
            UNREACHABLE();
        }
        else if (e.is_var()) {
            // This should be unreachable as we declare variables
            // as constants (0-arity apps)
            UNREACHABLE();
        }
        else { // is_app
            if (e.is_const() && !e.is_numeral()) {
                // Note: numerals are handled in translate_bv: Z3_OP_BNUM
                // Constants are apps with no arguments
                std::string name = e.decl().name().str();
                if (m_bv2int_var_map.find(e.decl()) != m_bv2int_var_map.end()) {
                    // If we have a mapping for this constant, use it
                    r = m_bv2int_var_map.at(e.decl());
                } else {
                    // Otherwise, create a new integer constant
                    r = ctx.int_const(name.c_str());
                }
                // We only support constants (vars) of Bit-vector sort!
                assert(e.get_sort().is_bv() && "Expected a BV sort for constant");
                unsigned k = e.get_sort().bv_size();
                create_bound_lemma(r, k);
                m_vars.push_back(r);
            }
            else if (is_special_basic(e)) {
                // Handle special basic cases: ite and eq
                r = translate_special_basic(e);
            }
            else if (is_basic(e)) {
                // && || implies iff, etc..
                r = translate_basic(e);
            }
            else if (is_bv_relation(e)){
                assert(e.is_bool() && "Expected a BV relation expression");
                r = translate_bv_rel(e);
            }
            else if (is_casting(e)) {
                r = translate_cast(e);
            }
            else { // is_bv
                r = translate_bv(e);
            }
        }

        // Simplify the result expression
        r = r.simplify();
        m_translate.emplace(key, r);
        return r;
    }

    z3::expr Bv2IntTranslator::translate_bv(const z3::expr& e) {
        // Get BV operation kind
        Z3_decl_kind f = e.decl().decl_kind();

        // Collect arguments
        std::vector<z3::expr> args;
        for (unsigned i = 0; i < e.num_args(); ++i)
            args.push_back(translate(e.arg(i)));
        
        // Result expression
        z3::expr r(ctx);
        unsigned k;
        uint64_t N;
        switch (f) {
            case Z3_OP_BNUM:
                assert(e.is_numeral() && "Z3_OP_BNUM should only be used with numerals");
                r = (m_is_signed) ? ctx.int_val(e.get_numeral_int()) : ctx.int_val(e.get_numeral_uint());
                break;
            case Z3_OP_BNEG:
                k = e.arg(0).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = umod(ctx.int_val(N) - args[0], k);
                break;

            case Z3_OP_BADD:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = umod(args[0] + args[1], k);
                break;
            case Z3_OP_BSUB:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = umod(args[0] - args[1], k);
                break;
            case Z3_OP_BMUL:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = umod(args[0] * args[1], k);
                break;
            
            case Z3_OP_BSDIV:
            case Z3_OP_BSDIV_I:
                ASSERT_FALSE("Signed division not implemented");
                break;
            case Z3_OP_BUDIV:
            case Z3_OP_BUDIV_I:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = if_eq(args[1], 0, ctx.int_val(N - 1), args[0] / args[1]);
                break;
            case Z3_OP_BSREM:
            case Z3_OP_BSREM_I:
                ASSERT_FALSE("Signed remainder not implemented");
                break;
            case Z3_OP_BUREM:
            case Z3_OP_BUREM_I:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = if_eq(args[1], 0, args[0], args[0] % args[1]);
                break;
            case Z3_OP_BSMOD:
            case Z3_OP_BSMOD_I:
                ASSERT_FALSE("Signed modulus not implemented");
                break;

            case Z3_OP_BNOT:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = ctx.int_val(N) - args[0] - ctx.int_val(1);
                break;
            case Z3_OP_BAND:
            case Z3_OP_BOR:
            case Z3_OP_BXOR:
            case Z3_OP_BNAND:
            case Z3_OP_BNOR:
            case Z3_OP_BXNOR:
                k = e.arg(1).get_sort().bv_size();
                r = create_bitwise_uf(f, args[0], args[1], k);
                break;

            case Z3_OP_CONCAT:
                k = e.arg(1).get_sort().bv_size();
                N = (uint64_t)1 << k;
                r = (args[0] * ctx.int_val(N)) + args[1];
                break;
            case Z3_OP_EXTRACT: {
                // Extract bits from a BV
                // (arg1 div 2^l) mod 2^(h-l+1)
                unsigned high = e.hi();
                unsigned low = e.lo();
                k = high - low + 1;
                unsigned divL = (uint64_t)1 << (low);
                r = umod(args[0] / ctx.int_val(divL), high - low + 1);
                break;
            }
            case Z3_OP_ZERO_EXT: {
                // Zero extension doesn't change the underlying integer value
                r = args[0];
                break;
            }
            case Z3_OP_SIGN_EXT:
                // Implement only if needed
                ASSERT_FALSE("Sign extension not implemented");
                break;

            case Z3_OP_REPEAT:
            case Z3_OP_BREDOR:
            case Z3_OP_BREDAND:
            case Z3_OP_BCOMP:
                ASSERT_FALSE("Implement only if needed");
                break;

            case Z3_OP_BSHL:
                k = e.arg(1).get_sort().bv_size();
                r = umod(args[0] * pow2(args[1]), k);
                break;
            case Z3_OP_BLSHR:
                k = e.arg(1).get_sort().bv_size();
                r = args[0] / pow2(args[1]);
                break;
            case Z3_OP_BASHR:
            case Z3_OP_ROTATE_LEFT:
            case Z3_OP_ROTATE_RIGHT:
            case Z3_OP_EXT_ROTATE_LEFT:
            case Z3_OP_EXT_ROTATE_RIGHT:
                ASSERT_FALSE("Implement only if needed");
                break;

            case Z3_OP_BIT2BOOL:
            case Z3_OP_SBV2INT:
            case Z3_OP_CARRY:
            case Z3_OP_XOR3:
                ASSERT_FALSE("NOT SUPPORTED through z3++.h");
                break;
            case Z3_OP_BSMUL_NO_OVFL:
            case Z3_OP_BUMUL_NO_OVFL:
            case Z3_OP_BSMUL_NO_UDFL:
            default:
                // std::cout << f << std::endl;
                ASSERT_FALSE("Unsupported BV operation");
        }

        return r;
    }

    z3::expr Bv2IntTranslator::translate_cast(const z3::expr& e) {
        assert(is_casting(e) && "Expected a casting operation (bv2int or int2bv)");
        Z3_decl_kind f = e.decl().decl_kind();

        if (f == Z3_OP_BV2INT)
            ASSERT_FALSE("Bv2Int not implemented (unclear why this would even be needed)");
        
        // It's int2bv
        // Get the bv-size parameter
        z3::parameter p(e, 0);
        unsigned bv_size = p.get_int();

        if (e.arg(0).is_numeral()) {
            return umod(e.arg(0), bv_size);
        }
        else if (is_basic(e.arg(0))) {
            // This is the way to turn a BV basic boolean operation into an Int
            return ite(translate_basic(e.arg(0)), 
                ctx.int_val(1), ctx.int_val(0));
        }
        else if (is_bv_relation(e.arg(0))) {
            // This is the way to turn a BV relation into an Int
            return ite(translate_bv_rel(e.arg(0)), 
                ctx.int_val(1), ctx.int_val(0));
        }
        else {
            // Otherwise, we don't know how to handle this case
            ASSERT_FALSE("Unsupported argument for int2bv");
            return e;
        }
    }

    z3::expr Bv2IntTranslator::translate_bv_rel(const z3::expr& e) {
        Z3_decl_kind f = e.decl().decl_kind();
        unsigned k = e.arg(1).get_sort().bv_size();
        std::vector<z3::expr> args;
        for (unsigned i = 0; i < e.num_args(); ++i)
            args.push_back(translate(e.arg(i)));

        z3::expr r(ctx);
        switch (f) {
            case Z3_OP_ULEQ:
            case Z3_OP_SLEQ:
                r = args[0] <= args[1];
                break;
            case Z3_OP_UGEQ:
            case Z3_OP_SGEQ:
                r = args[0] >= args[1];
                break;
            case Z3_OP_ULT:
            case Z3_OP_SLT:
                r = args[0] < args[1];
                break;
            case Z3_OP_UGT:
            case Z3_OP_SGT:
                r = args[0] > args[1];
                break;
            default:
                ASSERT_FALSE("Unsupported BV signed relation operation");
        }
        return r;
    }

    z3::expr Bv2IntTranslator::translate_special_basic(const z3::expr& e) {
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

    z3::expr Bv2IntTranslator::translate_basic(const z3::expr& e) {
        assert(!is_special_basic(e) && "Expected a basic expression (not ite or equality)");
        z3::expr_vector new_args(ctx);
        for (unsigned i = 0; i < e.num_args(); ++i) {
            new_args.push_back(translate(e.arg(i)));
        }
        
        // Create a new application with the translated arguments
        return e.decl()(new_args);
    }

    z3::expr Bv2IntTranslator::create_bitwise_uf(const Z3_decl_kind& f, const z3::expr& arg1, const z3::expr& arg2, unsigned k)
    {
        // Information to infer
        std::string opname;
        // bit_tt(a,b) builds the "1/0" truth table ite expression
        std::function<z3::expr(z3::expr,z3::expr)> bit_tt;

        switch (f) {
        case Z3_OP_BAND:
            opname = "AND";
            bit_tt = [&](z3::expr a, z3::expr b){
                        return ite(a == ctx.int_val(1) && b == ctx.int_val(1), 
                            ctx.int_val(1), ctx.int_val(0));
                    };
            break;
        case Z3_OP_BOR:
            opname = "OR";
            bit_tt = [&](z3::expr a, z3::expr b){
                        return ite(a == ctx.int_val(1) || b == ctx.int_val(1), 
                            ctx.int_val(1), ctx.int_val(0));
                    };
            break;
        case Z3_OP_BXOR:
            opname = "XOR";
            bit_tt = [&](z3::expr a, z3::expr b){
                        return ite(a == ctx.int_val(1) ^ b == ctx.int_val(1), 
                            ctx.int_val(1), ctx.int_val(0));
                    };
            break;
        case Z3_OP_BNAND:
            opname = "NAND";
            bit_tt = [&](z3::expr a, z3::expr b){
                        return ite(a == ctx.int_val(1) && b == ctx.int_val(1), 
                            ctx.int_val(0), ctx.int_val(1));
                    };
            break;
        case Z3_OP_BNOR:
            opname = "NOR";
            bit_tt = [&](z3::expr a, z3::expr b){
                        return ite(a == ctx.int_val(1) || b == ctx.int_val(1), 
                            ctx.int_val(0), ctx.int_val(1));
                    };
            break;
        case Z3_OP_BXNOR:
            opname = "XNOR";
            bit_tt = [&](z3::expr a, z3::expr b){
                        return ite(a == ctx.int_val(1) ^ b == ctx.int_val(1), 
                            ctx.int_val(0), ctx.int_val(1));
                    };
            break;
        default:
            ASSERT_FALSE("unsupported bitwise op");
        }

        // Build the uninterpreted function
        std::string uf_name = "__UF_" + opname + "_" + std::to_string(m_UF_counter++);
        z3::func_decl uf = ctx.function(uf_name.c_str(), ctx.int_sort(), ctx.int_sort(), ctx.int_sort());
        z3::expr res = uf(arg1, arg2);

        // Bound lemma
        create_bound_lemma(res, k);

        // per-bit lemmas
        for (unsigned i = 0; i < k; ++i) {
            z3::expr ai = bseli(arg1, i);
            z3::expr bi = bseli(arg2, i);
            z3::expr ci = bseli(res, i);
            m_lemmas.push_back(ci == bit_tt(ai, bi));
        }

        return res;
    }


    void Bv2IntTranslator::create_bound_lemma(z3::expr& var, unsigned k) {
        // Create a lemma for the variable var, which is an Int variable
        // with bounds [0, 2^k - 1] if unsigned, or [-2^(k-1), 2^(k-1) - 1] if signed.
        int64_t N = (int64_t)1 << k;
        z3::expr lemma = (m_is_signed) ? (var >= ctx.int_val(0)) && (var < ctx.int_val(N)) 
                                       : (var > ctx.int_val(-N)) && (var < ctx.int_val(N));
        m_lemmas.push_back(lemma);
    }

    z3::expr Bv2IntTranslator::bseli(const z3::expr& e, unsigned i) {
        // (e div 2^i) mod 2
        uint64_t N = (uint64_t)1 << i;
        return umod(e / ctx.int_val(N), 1);
    }

    z3::expr Bv2IntTranslator::umod(const z3::expr& e, unsigned k) {
        // unsigned modulo N = 2^k
        uint64_t N = (uint64_t)1 << k;
        return z3::mod(e, ctx.int_val(N));
    }

    z3::expr Bv2IntTranslator::uts(const z3::expr& e, unsigned k) {
        // 2 * umod(e, k - 1) - e
        return (ctx.int_val(2) * umod(e, k - 1)) - e;
    }

    z3::expr Bv2IntTranslator::pow2(const z3::expr& e) {
        // 2^e
        if (e.is_numeral()) {
            return ctx.int_val(1 << e.get_numeral_uint());
        }
        
        // This is a strong assertion
        // If e is not a numeral, the computation would be a series of if_eq
        // TODO: If ultimately we want to support non-numeral exponents,
        // TODO: we can observe Nikolaj's implementation of pow2 in the Z3 API
        ASSERT_FALSE("Expected a numeral for exponent in pow2");
    }

    z3::expr Bv2IntTranslator::if_eq(const z3::expr& e, unsigned k, const z3::expr& th, const z3::expr& el){
        if (e.is_numeral()) {
            if (e.get_numeral_uint() == k){
                return th;
            } else {
                return el;
            }
        }
        return ite(e == ctx.int_val(k), th, el);
    }

} // namespace multi_theory_horn
