//------------------------------------------------------------------------------
// multi_theory_fixedpoint.h
// Multi-Theory Fixedpoint Engine Header
// Based on the paper: // TODO: Fill in the paper reference
//------------------------------------------------------------------------------
#pragma once
#include <z3++.h>
#include <stack>
#include "utils.h"
#include "mth_utils.h"
#include "Bv2IntTranslator.h"
#include "Int2BvTranslator.h"

namespace multi_theory_horn {
    class MT_fixedpoint {
    private:
        z3::context& m_ctx;

        MTHFixedpointSet m_mth_fp_set;
        z3::expr_vector m_original_clauses;
        std::map<z3::expr, ClauseAnalysisResult, compare_expr> m_clause_analysis_map;
        PredicateMap m_interface_constraint_map;

        using PredicateToExprMap = std::map<z3::func_decl, z3::expr, compare_func_decl>;
        using CHCFactConfig = std::pair<CHC, z3::symbol>;
        using PredicateToCHCConfigMap = std::map<z3::func_decl, CHCFactConfig, compare_func_decl>;
        PredicateToExprMap m_interface_src_strengthening_map;
        PredicateToCHCConfigMap m_interface_dst_fact_map;

        z3::fixedpoint m_fp_int;
        z3::fixedpoint m_fp_bv;
        unsigned m_bv_size;
        bool m_is_signed; // Whether to treat bit-vectors as signed or unsigned
        bool m_simplify; // Whether to simplify the translations
        bool m_int2bv_preprocess; // Whether to preprocess integer translator formulas

        PredicateMap m_int2bv_map;
        PredicateMap m_bv2int_map;

        std::unordered_map<Z3_ast, CHCFactConfig, AstHash, AstEq> m_p_to_fact_map;
        std::map<z3::func_decl, z3::expr, compare_func_decl> m_p_to_strengthening_expr_map;

        std::string kAdded_fact_name = "__added_fact__";
        unsigned added_fact_counter = 0;

        std::string get_fresh_added_fact_name();

        /// @brief A method that finds the leaf predicate of a refutation.
        /// @param refutation The refutation expression to analyze.
        z3::expr get_refutation_leaf_pred(z3::expr const& refutation) const;

        /// @brief A method that creates a phi constraint based on the values the leaf
        /// predicate is assigned
        /// @param q The leaf predicate of the refutation.
        /// @param vars The vector of variables of the leaf predicate.
        /// @return A phi constraint of the form `var_1 == q.arg(0) && var_2 == q.arg(1) && ...`
        z3::expr get_refutation_leaf_phi(z3::expr const& q, z3::expr_vector const& vars) const;

        /// @brief A function that return a conjunction of bit-vector bound expressions
        /// of the form `0 <= var < 2^bv_size` for each variable in `vars`.
        /// @param vars The vector of bit-vector variables for which to create the bound expressions.
        z3::expr get_bv_expr_bounds(z3::expr_vector const& vars) const;

        /// @brief Adds behind the scenes a fact corresponding to the predicate given by p_expr
        /// which is the destination of an interface constraint.
        /// @param key The key ast of the source predicate. Its key is used to identify the fact that
        /// corresponds to this predicate through the p_to_fact_map.
        /// @param p_expr The fact's head (the destination predicate of the interface constraint).
        /// @param theory The theory of the source predicate of the interface constraint.
        void add_predicate_fact(z3::func_decl const& key, z3::expr const& p_expr, Theory theory);

        /// @brief Checks the signedness consistency of the clause analysis result.
        /// @param clause_analysis The clause analysis result to check.
        void check_signedness_consistency(ClauseAnalysisResult const& clause_analysis);

        /// @brief Populates the fixedpoint engines before executing queries.
        /// This includes going over the original clauses, their analysis results,
        /// and adding them to the appropriate fixedpoint engine after translation
        /// if necessary.
        /// @param query The query expression.
        /// @param query_analysis The analysis result of the query.
        void populate_MTH_fixedpoint_engines(const z3::expr& query, 
                                             ClauseAnalysisResult const& query_analysis);

        /// @brief Adds a behind the scenes fact corresponding to the predicate given by p_expr
        /// which is the destination of an interface constraint.
        /// @param src_decl The key func_decl of the source predicate.
        /// @param dst_expr The fact's head (the destination predicate of the interface constraint).
        /// @param dst_fp The fixedpoint engine of the destination predicate.
        /// @param is_dst_int Whether the destination theory is integer theory.
        /// If yes, then bound constraints are added to the generated fact.
        void add_predicate_fact(z3::func_decl const& src_decl, z3::expr const& dst_expr,
                                z3::fixedpoint& dst_fp, bool is_dst_int);
        
        /// @brief Adds an interface constraint (mapping) between two predicates
        /// in different theories.
        /// @param p1_expr The source predicate.
        /// @param p2_expr The target predicate.
        /// @param fp2 The solver of the target to which we add a fact.
        /// @param is_dst_int Whether the destination theory is integer theory.
        /// If yes, then bound constraints are added to the generated fact.
        void add_interface_constraint(z3::expr p1_expr, z3::expr p2_expr, z3::fixedpoint& fp2, bool is_dst_int);

        /// @brief Generates all needed interface constraints between all
        /// populated fixedpoint engines.
        void generate_interface_constraints();

    public:

        //--------------------------------------------------------------------------
        // Construction / destruction
        //--------------------------------------------------------------------------
        explicit MT_fixedpoint(z3::context& ctx, bool is_signed, unsigned bv_size, bool int2bv_preprocess = true, bool simplify = true);
        explicit MT_fixedpoint(z3::context& ctx, bool int2bv_preprocess = true, bool simplify = true);

        /// @brief Initializes the multi-theory fixedpoint engine from
        /// an existing BV fixedpoint engine.
        /// @param fp The existing BV fixedpoint engine.
        void from_solver(z3::fixedpoint& fp);

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
        /// \param vars The vector of variables to be used in the query.
        /// \param q_pred The predicate in the body of the query.
        /// \param q_phi The formula to be queried.
        /// \param theory The theory indicating the engine to which the query belongs.
        z3::check_result query(z3::expr_vector& vars, z3::expr& q_pred, z3::expr& q_phi, Theory theory);

        /// \brief The query method for the multi-theory fixedpoint engine.
        /// \param query The query expression.
        /// \return The result of the query.
        z3::check_result query(z3::expr& query);

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
        /// @param p1_expr The source predicate.
        /// @param theory_1 The theory of the source predicate.
        /// @param p2_expr The target predicate.
        /// @param theory_2 The theory of the target predicate.
        /// @note It's required to pass the expresion of the predicate to also
        /// be able to extract the variables used in each predicate.
        void add_interface_constraint(z3::expr p1_expr, Theory theory_1, 
                                      z3::expr p2_expr, Theory theory_2);

    };

    inline std::ostream & operator<<(std::ostream & out, MT_fixedpoint f) { 
        return out << "Integer Fixedpoint:\n" << f.engine_int() << "\n\n"
                    << "Bit-vector Fixedpoint:\n" << f.engine_bv();
    }
} // namespace multi_theory_horn