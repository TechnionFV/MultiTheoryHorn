//------------------------------------------------------------------------------
//  multi_theory_fixedpoint.cpp
//------------------------------------------------------------------------------
#include "multi_theory_fixedpoint.h"

namespace multi_theory_horn {

    // TODO: Currently keep the implementation, delete later
    z3::expr_vector MT_fixedpoint::get_quantifier_bounded_vars(z3::expr const& clause) {
        z3::expr_vector variables(m_ctx);
        for (int j = 0; j < Z3_get_quantifier_num_bound(m_ctx, clause); j++) {
            z3::symbol sym = z3::symbol(m_ctx, Z3_get_quantifier_bound_name(m_ctx, clause, j));
            z3::expr var = m_ctx.constant(sym, z3::sort(m_ctx, Z3_get_quantifier_bound_sort(m_ctx, clause, j)));
            variables.push_back(var);
        }
        return variables;
    }

    void MT_fixedpoint::add_predicate_fact(z3::expr_vector const& vars, z3::expr const& head, Theory theory) {
        std::string fact_name_str = kAdded_fact_name + std::to_string(added_fact_counter);
        z3::symbol fact_name = m_ctx.str_symbol(fact_name_str.c_str());
        z3::expr added_fact(m_ctx);
        if (theory == Theory::IAUF) {
            CHC fact(vars, m_ctx.bool_val(true), get_bv_expr_bound(vars), head);
            added_fact = fact.get_rule_expr();
            m_fp_int.add_rule(added_fact, fact_name);
            // Store the fact in the fact map with added_fact's AST as the key
            Z3_ast ast = added_fact;
            p_to_fact_map.emplace(ast, std::make_pair(fact, fact_name));
        }
        else if (theory == Theory::BV) {
            CHC fact(vars, m_ctx.bool_val(true), m_ctx.bool_val(true), head);
            added_fact = fact.get_rule_expr();
            m_fp_bv.add_rule(added_fact, fact_name);
            // Store the fact in the fact map with added_fact's AST as the key
            Z3_ast ast = added_fact;
            p_to_fact_map.emplace(ast, std::make_pair(fact, fact_name));
        }
        else
            ASSERT_FALSE("Invalid theory for predicate fact addition");
    }

    z3::expr MT_fixedpoint::get_bv_expr_bound(z3::expr_vector const& vars){
        uint64_t N = (uint64_t)1 << m_bv_size;
        z3::expr_vector bound_lemmas(m_ctx);
        for (const z3::expr& var : vars) {
            assert(var.is_bv());
            bound_lemmas.push_back(var >= m_ctx.int_val(0) && var < m_ctx.int_val(N));
        }

        return z3::mk_and(bound_lemmas);
    }

    //==============================================================================
    //                              PUBLIC METHODS
    //==============================================================================
    MT_fixedpoint::MT_fixedpoint(z3::context& ctx, unsigned bv_size)
        : m_ctx(ctx),m_fp_int(ctx), m_fp_bv(ctx),
          m_bv_size(bv_size) {
        // Set the solvers to use spacer engines for integer and bit-vector theories.
        z3::params p(ctx);
        p.set("engine", "spacer");
        m_fp_int.set(p);
        m_fp_bv.set(p);
    }

    void MT_fixedpoint::add_rule(z3::expr& rule, Theory theory, z3::symbol const& name) {
        switch (theory) {
            case Theory::IAUF:
                m_fp_int.add_rule(rule, name);
                break;
            case Theory::BV:
                m_fp_bv.add_rule(rule, name);
                break;
            default:
                UNREACHABLE();
        }
    }

    void MT_fixedpoint::register_relation(z3::func_decl& p, Theory theory) {
        switch (theory) {
            case Theory::IAUF:
                m_fp_int.register_relation(p);
                break;
            case Theory::BV:
                m_fp_bv.register_relation(p);
                break;
            default:
                UNREACHABLE();
        }
    }

    void MT_fixedpoint::add_interface_constraint(z3::func_decl const& p_1, Theory theory_1, 
                                                 z3::func_decl const& p_2, Theory theory_2,
                                                 z3::expr_vector const& p2_vars, z3::expr const& p2_head) {
        if (theory_1 == Theory::IAUF && theory_2 == Theory::BV)
            m_int2bv_map.insert(p_1, p_2);
        else if (theory_1 == Theory::BV && theory_2 == Theory::IAUF)
            m_bv2int_map.insert(p_1, p_2);
        else
            ASSERT_FALSE("theory_1 and theory_2 must be different theories");
        
        // Add a fact for the interface predicate in the second theory
        add_predicate_fact(p2_vars, p2_head, theory_2);
    }

    z3::check_result MT_fixedpoint::query(z3::expr_vector const& vars, z3::expr& q_pred, z3::expr& q_phi, Theory theory) {
        struct QueryConfig {
            z3::expr& p; // The query's predicate expression
            z3::expr& phi; // The query's phi formula expression
            Theory i; // The theory we're currently processing
            QueryConfig(z3::expr& _p, z3::expr& _phi, Theory _i)
                : p(_p), phi(_phi), i(_i) {}
        };

        std::stack<QueryConfig> S;
        S.push(QueryConfig(q_pred, q_phi, theory)); // line 2

        while (!S.empty()) { // line 3
            QueryConfig config = S.top(); S.pop(); // line 4

            // line 5 
            // Construct the query
            z3::expr p_query = z3::exists(vars, config.p && config.phi);
            z3::check_result res;
            if (config.i == Theory::IAUF) {
                res = engine_int().query(p_query);
            } else if (config.i == Theory::BV) {
                res = engine_bv().query(p_query);
            } else {
                ASSERT_FALSE("Unsupported theory in MT_fixedpoint::query");
            }
            
            Theory next_theory = (config.i == Theory::IAUF) ? Theory::BV : Theory::IAUF; // line 6
            
            if (res == z3::unsat) { // line 7
                if (!S.empty()) { // line 8
                    // line 9
                    if (config.i == Theory::IAUF) {
                        // Work with the integer engine
                        z3::func_decl p_decl = config.p.decl();
                        z3::expr p_interp = engine_int().get_cover_delta(-1, p_decl);

                        Int2BvTranslator int2bv_t(m_ctx, m_bv_size);
                        z3::expr bv_p_interp = int2bv_t.translate(p_interp);

                        // Get all info
                        Z3_ast key = p_interp;
                        auto it = p_to_fact_map.find(key);
                        assert(it != p_to_fact_map.end() && "Fact not found in the map");
                        CHCFactConfig fact_config = it->second; // get the config
                        z3::symbol fact_name = fact_config.second; // get CHC fact name
                        
                        // Strengthn the phi
                        // TODO: Check this works correctly (is it enough to access through fact_config?)
                        // TODO: Otherwise use erase(it) and emplace again
                        fact_config.first.body_formula = fact_config.first.body_formula && bv_p_interp;
                        z3::expr new_fact = fact_config.first.get_rule_expr();
                        m_fp_bv.update_rule(new_fact, fact_name);
                    }
                    else if (config.i == Theory::BV) {
                        // Work with the bit-vector engine
                        z3::func_decl p_decl = config.p.decl();
                        z3::expr p_interp = engine_bv().get_cover_delta(-1, p_decl);
                        Bv2IntTranslator bv2int_t(m_ctx);
                        z3::expr int_p_interp = bv2int_t.translate(p_interp);

                        // Go over all the lemmas and conjoin them with the tranlsated predicate
                        z3::expr_vector lemmas(m_ctx);
                        // TODO: Make sure this actually works!!
                        // TODO: There's a small fear that the lemmas would contain &_k symbols that need to be registered?
                        for (const z3::expr& lemma : bv2int_t.lemmas()) {
                            lemmas.push_back(lemma);
                        }
                        int_p_interp = int_p_interp && z3::mk_and(lemmas);

                        Z3_ast key = p_interp;
                        auto it = p_to_fact_map.find(key);
                        assert(it != p_to_fact_map.end() && "Fact not found in the map");
                        CHCFactConfig fact_config = it->second; // get the config
                        z3::symbol fact_name = fact_config.second; // get CHC fact name
                        
                        // Strengthn the phi
                        // TODO: Check this works correctly (is it enough to access through fact_config?)
                        // TODO: Otherwise use erase(it) and emplace again
                        fact_config.first.body_formula = fact_config.first.body_formula && int_p_interp;
                        z3::expr new_fact = fact_config.first.get_rule_expr();
                        m_fp_bv.update_rule(new_fact, fact_name);
                    }
                    else {
                        ASSERT_FALSE("Unsupported theory in MT_fixedpoint::query");
                    }

                } // line 10
            }
            else if (res == z3::sat) { // line 11
                if (config.i == Theory::IAUF) {
                    // line 12
                    z3::expr g_refutation = engine_int().get_answer();
                    Int2BvTranslator int2bv_t(m_ctx, m_bv_size);
                    // TODO: Delete
                    std::cout << "Refutation:\n" << g_refutation << std::endl;
                    // TODO: Extract the refutation leaf somehow!
                    // q, phi = get_refutation_leaf(g_refutation);
                    // q_tag = m_bv2int_map.find_pred(q);
                    // if (q_tag) { // line 13
                    //     // line 14
                    //     z3::expr phi_trans = int2bv_t.translate(phi);
                    //     S.push(QueryConfig(q_tag, phi_trans, next_theory));
                    // }
                    // else { // line 15
                    //     // line 16
                    //     return z3::sat;
                    // } // line 17
                }
                else if (config.i == Theory::BV) {
                    // line 12
                    z3::expr g_refutation = engine_bv().get_answer();
                    Bv2IntTranslator bv2int_t(m_ctx);
                    // TODO: Delete
                    std::cout << "Refutation:\n" << g_refutation << std::endl;
                    // TODO: Extract the refutation leaf somehow!
                    // q, phi = get_refutation_leaf(g_refutation);
                    // q_tag = m_int2bv_map.find_pred(q);
                    // if (q_tag) { // line 13
                    //     // line 14
                    //     z3::expr phi_trans = bv2int_t.translate(phi);
                    //     S.push(QueryConfig(q_tag, phi_trans, next_theory));

                    //     // Go over all the lemmas and conjoin them with the tranlsated predicate
                    //     z3::expr_vector lemmas(m_ctx);
                    //     // TODO: Make sure this actually works!!
                    //     // TODO: There's a small fear that the lemmas would contain &_k symbols that need to be registered?
                    //     for (const z3::expr& lemma : bv2int_t.lemmas()) {
                    //         lemmas.push_back(lemma);
                    //     }
                    //     phi_trans = phi_trans && z3::mk_and(lemmas);
                    // }
                    // else { // line 15
                    //     // line 16
                    //     return z3::sat;
                    // } // line 17
                }
                else {
                    ASSERT_FALSE("Unsupported theory in MT_fixedpoint::query");
                }

            } // line 18
            else { // z3::unknown
                // Propagate unknown result
                return z3::unknown;
            }
        } // line 19

        return z3::unsat; // line 20
    }

} // namespace multi_theory_horn