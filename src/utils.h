// Add not implemented macro

#pragma once
#include <cassert>
#include <iostream>
#include <map>
#include <unordered_map>
#include <optional>
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


    struct compare_func_decl {
		bool operator() (const z3::func_decl& lhs, const z3::func_decl& rhs) const {
			return lhs.id() < rhs.id();
		}
	};

    using VarMap = std::map<z3::func_decl, z3::expr, compare_func_decl>;

    class PredicateMap {
        using Map = std::map<
            z3::func_decl,
            z3::expr,
            compare_func_decl
        >;

        std::map<z3::func_decl, z3::expr_vector, compare_func_decl> srcVarMap;
        std::map<z3::func_decl, z3::expr_vector, compare_func_decl> dstVarMap;
        Map Theta;

    public:
        void insert(z3::expr& p1, z3::expr& p2) {
            // The interface constraint is p1 -> p2
            // The key is the destination predicate p2 because of the
            // assumption that each predicate has at most one predecessor
            assert(Theta.find(p2.decl()) == Theta.end() && 
                "PredicateMap: first predicate is already mapped");
            Theta.emplace(p2.decl(), p1);
            srcVarMap.emplace(p1.decl(), p1.args());
            dstVarMap.emplace(p2.decl(), p2.args());
        }

        std::optional<z3::expr> find_pred(const z3::func_decl& dst) const {
            // Given a destination predicate, return the source predicate
            auto it = Theta.find(dst);
            if (it != Theta.end()) {
                return it->second; // Return the source predicate
            }
            return std::nullopt; // Not found
        }

        std::optional<z3::func_decl> find_next(const z3::expr& src) const {
            // Look if there's a key that its value is the src argument
            //! We assume that there's at one such key
            for (const auto& pair : Theta)
                if (pair.second.decl().id() == src.decl().id())
                    return pair.first;

            return std::nullopt;
        }

        z3::expr_vector get_src_vars(const z3::func_decl& src) const {
            // Get the source variables for a given destination predicate
            auto it = srcVarMap.find(src);
            assert(it != srcVarMap.end() && 
                "PredicateMap: source variables not found for the given predicate");
            return it->second; // Return the source variables
        }

        z3::expr_vector get_dst_vars(const z3::func_decl& dst) const {
            // Get the destination variables for a given source predicate
            auto it = dstVarMap.find(dst);
            assert(it != dstVarMap.end() && 
                "PredicateMap: destination variables not found for the given predicate");
            return it->second; // Return the destination variables
        }
    };

    template<typename S, typename T>
    bool any_of(S const& set, T const& p) {
        for (auto const& s : set)
            if (p(s))
                return true;
        return false;
    }

    inline int sign_extend(int raw, unsigned width) {
        // keep only the low 'width' bits
        int mask = (1 << width) - 1;
        int u   = raw & mask;
        // if top bit set, subtract 2^width
        if (u & (1 << (width-1)))
            u -= (1 << width);
        return u;
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

    // Debug message macro
    // #define DEBMSG
    #ifdef DEBMSG
    #define DEBUG_MSG(cmd) \
        do                 \
        {                  \
            std::cout << "-------------------------------------------------------" << std::endl;     \
            cmd;           \
        } while (0)
    #else
    #define DEBUG_MSG(cmd) \
        do                 \
        {                  \
        } while (0)
    #endif
}