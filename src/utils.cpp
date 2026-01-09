#include "utils.h"

namespace multi_theory_horn {

    /// @brief An auxiliary function for recursively getting conjuncts.
    /// @param e The expression to analyze.
    /// @param conjuncts The vector to store the resulting conjuncts.
    static void get_conjuncts_impl(const z3::expr& e, z3::expr_vector& conjuncts) {
        if (e.is_and()) {
            for (unsigned i = 0; i < e.num_args(); ++i) {
                get_conjuncts_impl(e.arg(i), conjuncts);
            }
        } else {
            conjuncts.push_back(e);
        }
    }

    z3::expr_vector get_conjuncts(const z3::expr& e) {
        z3::expr_vector conjuncts(e.ctx());
        get_conjuncts_impl(e, conjuncts);
        return conjuncts;
    }
} // namespace multi_theory_horn