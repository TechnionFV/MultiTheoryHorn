#include "utils.h"

namespace utils {

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

    //==============================================================================
    //                              PUBLIC METHODS
    //==============================================================================
    z3::expr_vector get_conjuncts(const z3::expr& e) {
        z3::expr_vector conjuncts(e.ctx());
        get_conjuncts_impl(e, conjuncts);
        return conjuncts;
    }

    int64_t sign_extend(uint64_t raw, unsigned width) {
        // keep only the low 'width' bits
        int64_t mask = (1 << width) - 1;
        int64_t u    = raw & mask;
        // if top bit set, subtract 2^width
        if (u & (1 << (width-1)))
            u -= (1 << width);
        return u;
    }

    bool is_uninterpreted_predicate(const z3::expr& e) {
        return e.decl().decl_kind() == Z3_OP_UNINTERPRETED;
    }

    int64_t get_signed_bv_lower_bound(unsigned bv_size) {
        return -(int64_t(1) << (bv_size - 1));
    }

    int64_t get_signed_bv_upper_bound(unsigned bv_size) {
        return (int64_t(1) << (bv_size - 1)) - 1;
    }

    uint64_t get_unsigned_bv_upper_bound(unsigned bv_size) {
        if (bv_size >= 64)
            return std::numeric_limits<uint64_t>::max();
        return (uint64_t(1) << bv_size) - 1;
    }

    uint64_t get_unsigned_bv_lower_bound(unsigned bv_size) {
        return 0;
    }
} // namespace utils