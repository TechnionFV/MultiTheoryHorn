// Add not implemented macro

#pragma once
#include <cassert>
#include <iostream>
#include <z3++.h>

namespace multi_theory_horn {

    // Hash / equality for Z3 AST pointers
    struct AstHash {
        std::size_t operator()(Z3_ast a) const noexcept { return reinterpret_cast<std::size_t>(a); }
    };
    struct AstEq {
        bool operator()(Z3_ast a, Z3_ast b) const noexcept { return a == b; }
    };

    template<typename S, typename T>
    bool any_of(S const& set, T const& p) {
        for (auto const& s : set)
            if (p(s))
                return true;
        return false;
    }

    #define NDEBUG 0

    #define NOT_IMPLEMENTED() \
        do { \
            std::cerr << "Not implemented: " << __FILE__ << ":" << __LINE__ << std::endl; \
            assert(false && "Not implemented"); \
            exit(1); \
        } while (0)

    #define UNREACHABLE() \
        do { \
            std::cerr << "Unreachable code reached: " << __FILE__ << ":" << __LINE__ << std::endl; \
            assert(false && "Unreachable code reached"); \
            exit(1); \
        } while (0)

    // Add assert(false) with message macro
    #define ASSERT_FALSE(msg) \
        do { \
            std::cerr << "Assertion failed: " << msg << " at " << __FILE__ << ":" << __LINE__ << std::endl; \
            assert(false && msg); \
            exit(1); \
        } while (0)
}