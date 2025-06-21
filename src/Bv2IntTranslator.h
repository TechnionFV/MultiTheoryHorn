// Bv2IntTranslator.h

#pragma once
#include "utils.h"
#include <z3++.h>
#include <unordered_map>
#include <vector>
#include <algorithm>

namespace multi_theory_horn {

    class Bv2IntTranslator {
        z3::context&      ctx;

        // Map each original BV expr AST to its translated Int expr
        // This is used to cache results of translations
        std::unordered_map<Z3_ast, z3::expr, AstHash, AstEq> m_translate;
        // collected BV variables (are collected to later be used to create lemmas)
        std::vector<Z3_ast> m_vars;

        uint64_t m_UF_counter;

        // A set of lemmas specfiying the bounds on the new variables
        std::vector<z3::expr> m_lemmas;

        z3::expr bseli(const z3::expr& e, unsigned i);
        z3::expr umod(const z3::expr& e, unsigned k);
        z3::expr uts(const z3::expr& e, unsigned k);

        // Custom implementation of common operations which could simplify
        // the final expression
        z3::expr amod(const z3::expr& e, unsigned k);
        z3::expr pow2(const z3::expr& e);
        z3::expr mul(const z3::expr& x, const z3::expr& y);
        z3::expr add(const z3::expr& x, const z3::expr& y);
        z3::expr if_eq(const z3::expr& e, unsigned k, const z3::expr& th, const z3::expr& el);

        // Helper utility functions
        bool is_basic(const z3::expr& e) const;
        bool is_casting(const z3::expr& e) const;
        bool is_special_basic(const z3::expr& e) const;
        bool is_bv_relation(const z3::expr& e) const;

        // Core translation routines
        z3::expr translate_bv(const z3::expr& e);
        z3::expr translate_cast(const z3::expr& e);
        z3::expr translate_bv_rel(const z3::expr& e);
        z3::expr translate_basic(const z3::expr& e);
        z3::expr translate_special_basic(const z3::expr& e);
        
        z3::expr create_bitwise_uf(const Z3_decl_kind& f, const z3::expr& arg1, const z3::expr& arg2, unsigned k);
        void create_lemma(z3::expr& var, unsigned k);
    public:
        explicit Bv2IntTranslator(z3::context& c);
        void reset();

        // Translate any expr; caches results in m_translate
        z3::expr translate(const z3::expr& e);

        // Accessors for the collected vars/preds
        const std::vector<Z3_ast>& vars() const   { return m_vars; }
        const std::vector<z3::expr>& lemmas() const { return m_lemmas; }
    };
} // namespace multi_theory_horn
