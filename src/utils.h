// Add not implemented macro

#pragma once
#include <cassert>
#include <iostream>
#include <unordered_map>
#include <z3++.h>

namespace multi_theory_horn {

    struct AstHash {
        std::size_t operator()(Z3_ast a) const noexcept {
            return reinterpret_cast<std::size_t>(a);
        }
    };
    struct AstEq {
        bool operator()(Z3_ast a, Z3_ast b) const noexcept {
            return a == b;
        }
    };

    class PredicateMap {
        using Map = std::unordered_map<
            Z3_ast,
            Z3_ast,
            AstHash,
            AstEq
        >;

        Map Theta;

    public:
        void insert(z3::func_decl const& p1, z3::func_decl const& p2) {
            // The interface constraint is p1 -> p2
            // The key is the destination predicate p2 because of the
            // assumption that each predicate has at most one predecessor
            Z3_ast key2 = p2;
            assert(Theta.find(key2) == Theta.end() && 
                "PredicateMap: first predicate is already mapped");
            Theta.emplace(key2, p1);
        }

        Z3_ast find_pred(z3::func_decl const& dst) const {
            // Given a destination predicate, return the source predicate
            Z3_ast key = dst;
            auto it = Theta.find(key);
            if (it == Theta.end()) return nullptr;
            return it->second;
        }
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