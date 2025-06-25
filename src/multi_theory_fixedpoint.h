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


    class MT_fixedpoint {
    private:
        z3::context& m_ctx;
        z3::fixedpoint m_fp_int;
        z3::fixedpoint m_fp_bv;
        unsigned m_bv_size;

        PredicateMap m_int2bv_map;
        PredicateMap m_bv2int_map;

        using CHCFactConfig = std::pair<CHC, z3::symbol>;
        std::unordered_map<Z3_ast, CHCFactConfig, AstHash, AstEq> p_to_fact_map;

        std::string kAdded_fact_name = "__added_fact__";
        unsigned added_fact_counter = 0;

        /// @brief Extracts the bounded variables from a quantifier clause.
        /// @param clause The quantifier clause from which to extract the bounded variables.
        /// @return A vector of expressions representing the bounded variables in the clause.
        z3::expr_vector get_quantifier_bounded_vars(z3::expr const& clause);

        /// @brief A function that return a conjunction of bit-vector bound expressions
        /// of the form `0 <= var < 2^bv_size` for each variable in `vars`.
        /// @param vars The vector of bit-vector variables for which to create the bound expressions.
        z3::expr get_bv_expr_bound(z3::expr_vector const& vars);

        /// @brief Adds behind the scenes a fact corresponding to the predicate given by p_expr
        /// which is the destination of an interface constraint.
        /// @param vars The variables of the predicate fact.
        /// @param p_expr The fact's head (the destination predicate of the interface constraint).
        /// @param theory The theory of the source predicate of the interface constraint.
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
        // TODO: Consider changing to CHC
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
        /// @param p2_vars The variables of the target predicate.
        /// @param p2_head The expression of the target predicate, which is going to 
        /// be used to create a fact in the target theory.
        void add_interface_constraint(z3::func_decl const& p_1, Theory theory_1,
                                      z3::func_decl const& p_2, Theory theory_2,
                                      z3::expr_vector const& p2_vars, z3::expr const& p2_head);

    };

    inline std::ostream & operator<<(std::ostream & out, MT_fixedpoint f) { 
        return out << "Integer Fixedpoint:\n" << f.engine_int() << "\n\n"
                    << "Bit-vector Fixedpoint:\n" << f.engine_bv();
    }
} // namespace multi_theory_horn