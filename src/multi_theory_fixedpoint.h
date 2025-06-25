//------------------------------------------------------------------------------
// multi_theory_fixedpoint.h
// Multi-Theory Fixedpoint Engine Header
// Based on the paper: // TODO: Fill in the paper reference
//------------------------------------------------------------------------------
#pragma once
#include <z3++.h>
#include <stack>
#include "utils.h"
#include "Bv2IntTranslator.h"
#include "Int2BvTranslator.h"

namespace multi_theory_horn {
    enum class Theory { IAUF, BV };

    class MT_fixedpoint {
    private:
        z3::context& m_ctx;
        z3::fixedpoint m_fp_int;
        z3::fixedpoint m_fp_bv;
        unsigned m_bv_size;

        PredicateMap m_int2bv_map;
        PredicateMap m_bv2int_map;

        std::unordered_map<Z3_ast, z3::expr, AstHash, AstEq> p_to_fact_map;

        std::string kAdded_fact_name = "__added_fact__";
        unsigned added_fact_counter = 0;

        // TODO: Add documentation
        z3::expr_vector get_quantifier_bounded_vars(z3::expr const& clause);
        void add_predicate_fact(z3::expr_vector const& vars, z3::expr const& p_expr, Theory theory);

    public:

        //--------------------------------------------------------------------------
        // Construction / destruction
        //--------------------------------------------------------------------------
        explicit MT_fixedpoint(z3::context& ctx, unsigned bv_size);

        //--------------------------------------------------------------------------
        // Quick access to the underlying fixedpoint engine
        //--------------------------------------------------------------------------
        z3::fixedpoint& engine_int()    { return m_fp_int; }
        z3::fixedpoint& engine_bv()     { return m_fp_bv; }

        //--------------------------------------------------------------------------
        // Re-implemented / enhanced queries
        //--------------------------------------------------------------------------
        /// \brief The query method for the multi-theory fixedpoint engine.
        /// The query should be over theory2 as the second theory
        /// is our starting point of the "backward" query algorithm.
        /// \param vars The variables to be used in the query.
        /// \param q_pred The predicate in the body of the query.
        /// \param q_phi The formula to be queried.
        /// \param theory The theory indicating the engine to which the query belongs.
        z3::check_result query(z3::expr_vector const& vars, z3::expr& q_pred, z3::expr& q_phi, Theory theory);

        //--------------------------------------------------------------------------
        // Forwarding of fixepoint most common calles
        //--------------------------------------------------------------------------
        
        /// \brief Add a rule to the appropriate fixedpoint engine.
        /// \param rule The rule to add.
        /// \param theory The theory indicating the engine to which the rule belongs.
        void add_rule(z3::expr& rule, Theory theory, z3::symbol const& name);

        /// \brief Register a relation (predicate) in the appropriate fixedpoint engine.
        /// \param p The predicate to register.
        /// \param theory The theory indicating the engine to which the predicate belongs.
        void register_relation(z3::func_decl& p, Theory theory);

        //--------------------------------------------------------------------------
        // Extra methods for multi-theory fixedpoint
        //--------------------------------------------------------------------------
        
        /// @brief Adds an interface constraint (mapping) between two predicates
        /// in different theories.
        /// @param p_1 The source predicate.
        /// @param theory_1 The theory of the source predicate.
        /// @param p_2 The target predicate.
        /// @param theory_2 The theory of the target predicate.
        /// The param should be implicitly known but it was added for clarity.
        void add_interface_constraint(z3::func_decl const& p_1, Theory theory_1,
                                      z3::func_decl const& p_2, Theory theory_2);

    };

    inline std::ostream & operator<<(std::ostream & out, MT_fixedpoint f) { 
        return out << "Integer Fixedpoint:\n" << f.engine_int() << "\n\n"
                    << "Bit-vector Fixedpoint:\n" << f.engine_bv();
    }
} // namespace multi_theory_horn