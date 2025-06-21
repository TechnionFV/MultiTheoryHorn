// Bv2IntTranslator.h

#pragma once
#include "utils.h"
#include <iostream>
#include <z3++.h>
#include <unordered_map>
#include <vector>
#include <algorithm>

namespace multi_theory_horn {

    class Int2BvTranslator {
        z3::context&      ctx;
        unsigned          m_bv_size; // Size of the BV type to translate to
        
        std::vector<Z3_ast> m_vars;
        // This map is used to cache translations
        std::unordered_map<Z3_ast, z3::expr, AstHash, AstEq> m_translate;

        bool is_special_basic(const z3::expr& e) const;
        bool is_basic(const z3::expr& e) const;

        // Core translation routines
        z3::expr translate_int(const z3::expr& e);
        z3::expr translate_basic(const z3::expr& e);
        z3::expr translate_special_basic(const z3::expr& e);

    public:
        explicit Int2BvTranslator(z3::context& c, unsigned bv_size);

        // This must be invoked before starting a new translation
        // It clears the cache and resets the translator state
        void reset();

        // Translate any expr; caches results in m_translate
        z3::expr translate(const z3::expr& e);
        
        // Accessors for the collected vars
        const std::vector<Z3_ast>& vars() const   { return m_vars; }
    };
} // namespace multi_theory_horn
