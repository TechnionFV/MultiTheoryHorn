#pragma once

#include <z3++.h>
#include <map>
#include <optional>
#include <set>
#include "utils.h"

namespace multi_theory_horn {
    struct CHC {
        z3::expr_vector const vars;
        z3::expr body_preds;
        z3::expr body_formula;
        z3::expr head;

        CHC(z3::expr_vector const& v, z3::expr bp, z3::expr bf, z3::expr h)
            : vars(v), body_preds(bp), body_formula(bf), head(h) {}

        z3::expr get_rule_expr() const {
            assert(!head.is_true() || !head.is_false() && 
                        "Head of normal CHC rule cannot be a boolean expression");
            return z3::forall(vars, z3::implies(body_preds && body_formula, head));
        }

        z3::expr get_query_expr() const {
            assert(head.is_false() && 
                        "Head of query CHC must be false");
            return z3::exists(vars, body_preds && body_formula);
        }

        z3::expr get_body_expr() const {
            return body_preds && body_formula;
        }
    };

    enum class Theory { IAUF, BV };

    enum class Signedness { UNKNOWN, SIGNED, UNSIGNED, CONFLICT };
    static constexpr unsigned UNDETERM_BV_SIZE = std::numeric_limits<unsigned>::max();
    struct ClauseAnalysisResult {
        Signedness is_signed;
        unsigned bv_size; // UNDETERM_BV_SIZE if not uniquely determined.
        bool has_bit_manipulating_apps;
        // Variables that do not occur in any predicate application
        // in the body of the clause.
        std::set<z3::expr, compare_expr> bound_vars;
        std::set<z3::expr, compare_expr> all_vars;

        ClauseAnalysisResult(z3::context& ctx)
            : bound_vars(), all_vars(), is_signed(Signedness::UNKNOWN), bv_size(UNDETERM_BV_SIZE),
              has_bit_manipulating_apps(false) {}

        bool is_bv_size_determined() const {
            return bv_size != UNDETERM_BV_SIZE;
        }

        bool is_signedness_determined() const {
            return is_signed != Signedness::UNKNOWN && is_signed != Signedness::CONFLICT;
        }

        // Declare operator<< for easy printing
        friend std::ostream& operator<<(std::ostream& os, const ClauseAnalysisResult& result);
    };

    /// @brief Return an expr_vector containing all the variables of the CHC clause.
    /// A CHC clause is of the form:
    /// forall x1 ... xn. (body => head)
    /// @param clause The CHC clause to extract variables from.
    /// @return An expr_vector containing all the variables of the CHC clause.
    z3::expr_vector get_clause_vars(z3::expr const& clause);

    /// @brief Analyze the given CHC clause and return the result. We try to infer:
    /// - The signedness of the bit-vector operations in the clause.
    /// - The bit-vector size used in the clause.
    /// - Whether the clause contains bit-manipulating operations.
    /// - The free variables in the body of the clause.
    /// @param ctx The Z3 context.
    /// @param clause The CHC clause to analyze.
    /// @return The result of the clause analysis in a ClauseAnalysisResult struct.
    ClauseAnalysisResult analyze_clause(z3::context& ctx, z3::expr const& clause);

} // namespace multi_theory_horn