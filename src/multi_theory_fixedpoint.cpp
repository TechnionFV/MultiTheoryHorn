//------------------------------------------------------------------------------
//  multi_theory_fixedpoint.cpp
//------------------------------------------------------------------------------
#include "multi_theory_fixedpoint.h"

namespace multi_theory_horn {

    static bool is_hyper_res(z3::expr const& e) {
        return e.decl().decl_kind() == Z3_OP_PR_HYPER_RESOLVE;
    }

    /// @brief Checks if the given predicate is user-visible according to its name.
    /// A non-visitble predicate is one that is created by the fixedpoint
    /// engine to represent a refutation and is of the form `query!X` where `X` is a number.
    /// @param p The predicate to check.
    /// @return true if the predicate is user-visible, i.e. created by the user and
    /// false otherwise.
    static bool is_user_visible_predicate(z3::func_decl const& p) {
        std::string p_name = p.name().str();

        // Check if p has a name of the form query!X where X is a number
        if (p_name.find("query!") == 0) {
            // Check that the rest of the string is a number
            std::string num_str = p_name.substr(6);
            if (std::all_of(num_str.begin(), num_str.end(), ::isdigit)) {
                return false;
            }
        }

        return true;
    }

    // Creates a copy of the given predicate with the same name but with bv_size
    // concatenated to it.
    // The sort and range of the old predicate should be bit-vectors and bool respectively.
    // The new predicate will have int sorts for its arguments.
    static z3::func_decl bv_predicate_to_int(const z3::func_decl& p_old, unsigned bv_size) {
        z3::context& ctx = p_old.ctx();
        std::string p_name_str = p_old.name().str() + "_" + std::to_string(bv_size);
        z3::symbol p_name = ctx.str_symbol(p_name_str.c_str());

        // Create the new argument sorts
        unsigned arity = p_old.arity();
        std::vector<z3::sort> arg_sorts;
        for (unsigned i = 0; i < arity; ++i) {
            z3::sort old_sort = p_old.domain(i);
            assert (old_sort.is_bv() && "Sort should be BV");
            arg_sorts.push_back(ctx.int_sort());
        }

        // Create the new return sort
        assert(p_old.range().is_bool() && "Predicate return sort should be bool");
        z3::sort ret_sort = p_old.range();

        // Create the new predicate
        z3::func_decl p_new = ctx.function(p_name, arity, arg_sorts.data(), ret_sort);
        return p_new;
    }

    static VarMap build_bv2int_var_map(z3::context& ctx, z3::expr_vector& bv_vars_exprs, ClauseAnalysisResult& clause_analysis) {
        VarMap bv_to_int_var_map;
        for (const z3::expr& var_bv : clause_analysis.all_vars) {
            int var_index = clause_analysis.var_index_map.at(var_bv);
            std::string var_name = bv_vars_exprs[var_index].decl().name().str();
            // Create a new corresponding variable of int sort
            z3::expr new_var_int = ctx.int_const(var_name.c_str());
            // Emplace the variable in the map.
            bv_to_int_var_map.emplace(var_bv, new_var_int);
        }
        return bv_to_int_var_map;
    }
    
    static z3::expr translate_BV_CHC_rule(const z3::expr& clause,
                                          ClauseAnalysisResult& clause_analysis,
                                          Bv2IntTranslator& translator) {
        DEBUG_MSG(OUT() << "Translating BV CHC rule: " << clause << std::endl << "With BV to int VarMap:\n"
                        << dump(translator.bv2int_var_map()) << std::endl);
        z3::context& ctx = clause.ctx();
        const VarMap& new_vars_map = translator.bv2int_var_map();

        unsigned num_vars = clause_analysis.all_vars.size();
        z3::expr_vector new_vars(ctx);
        new_vars.resize(num_vars);
        for (const z3::expr& var_bv : clause_analysis.all_vars) {
            int var_index = clause_analysis.var_index_map.at(var_bv);
            assert(var_index >= 0 && static_cast<unsigned>(var_index) < num_vars);
            z3::expr tmp = new_vars_map.at(var_bv);
            new_vars.set(var_index, tmp);
        }

        assert(clause.is_forall() && "Clause must be a forall");
        z3::expr underlying_clause = clause.body();
        assert(underlying_clause.is_implies() && "Clause must be an implication");
        z3::expr body = underlying_clause.arg(0);
        z3::expr head = underlying_clause.arg(1);

        // TODO: Maybe inline the following logic in the translator itself.
        int num_conjuncts = get_num_conjuncts(body);
        z3::expr_vector new_conjunct(ctx);
        for (int i = 0; i < num_conjuncts; ++i) {
            z3::expr conjunct = (num_conjuncts == 1) ? body : body.arg(i);
            z3::expr translated_conjunct(ctx);
            if (is_uninterpreted_predicate(conjunct)) {
                z3::func_decl p_new = bv_predicate_to_int(conjunct.decl(), clause_analysis.bv_size);
                z3::expr translated_arg(ctx);
                z3::expr_vector new_args(ctx);
                for (unsigned j = 0; j < conjunct.num_args(); ++j) {
                    z3::expr arg = conjunct.arg(j);
                    translated_arg = translator.translate(arg);
                    new_args.push_back(translated_arg);
                }
                translated_conjunct = p_new(new_args);
            }
            else {
                translated_conjunct = translator.translate(conjunct);
            }
            new_conjunct.push_back(translated_conjunct);
        }

        // Go over all_vars and check if the variable is NOT in a predicate's app body.
        // If it is not in a predicate's app body, then we need to add bounds for it.
        VarLemmaMap const& var_lemmas = translator.lemmas();
        for (const z3::expr& var_bv : clause_analysis.all_vars) {
            z3::expr var_int = new_vars_map.at(var_bv);
            if (clause_analysis.in_pred_body_vars.find(var_bv) == clause_analysis.in_pred_body_vars.end()) {
                // Variable is not in a predicate body, add its bound lemma
                auto it = var_lemmas.find(var_int);
                assert(it != var_lemmas.end() && "Lemma for variable not found");
                new_conjunct.push_back(it->second);
            }
        }

        z3::expr new_body = z3::mk_and(new_conjunct);
        z3::expr new_head(ctx);
        assert(is_uninterpreted_predicate(head) && "Head must be an uninterpreted predicate");
        z3::func_decl p_head_new = bv_predicate_to_int(head.decl(), clause_analysis.bv_size);
        z3::expr_vector new_head_args(ctx);
        for (unsigned j = 0; j < head.num_args(); ++j) {
            z3::expr arg = head.arg(j);
            z3::expr translated_arg = translator.translate(arg);
            new_head_args.push_back(translated_arg);
        }
        new_head = p_head_new(new_head_args);
        z3::expr new_clause = z3::forall(new_vars, z3::implies(new_body, new_head));
        DEBUG_MSG(OUT() << "Translated BV CHC rule to int CHC rule: " << new_clause << std::endl);
        return new_clause;
    }

    z3::expr MT_fixedpoint::get_bv_expr_bound(z3::expr_vector const& vars) const {
        unsigned bv_size = m_bv_size;
        bool is_signed = m_is_signed;

        int64_t N = (int64_t)1 << bv_size;
        int64_t N_half = (int64_t)1 << (bv_size - 1);
        z3::expr_vector bound_lemmas(m_ctx);
        z3::expr tmp(m_ctx);
        // TODO: Consider being consistent with the rest of project and use <=
        for (const z3::expr& var : vars) {
            assert(var.is_int());
            if (is_signed)
                tmp = (var >= m_ctx.int_val(-N_half)) && (var < m_ctx.int_val(N_half));
            else
                tmp = (var >= m_ctx.int_val(0)) && (var < m_ctx.int_val(N));
            bound_lemmas.push_back(tmp);
        }

        return z3::mk_and(bound_lemmas);
    }

    z3::expr MT_fixedpoint::get_refutation_leaf_pred(z3::expr const& refutation) const {
        // The refutation is a modus ponens tree
        // The first argument is the hyper-resolution predicate
        z3::expr hyper_res_pred = refutation.arg(0);

        // Take the query predicate
        z3::expr q_pred = hyper_res_pred.arg(1);

        // If the query predicate is a hyper-resolution predicate, we need to find the leaf
        while (is_hyper_res(q_pred)) {
            q_pred = q_pred.arg(1);
        }

        return q_pred;
    }

    z3::expr MT_fixedpoint::get_refutation_leaf_phi(z3::expr const& q, z3::expr_vector const& vars) const {
        assert(vars.size() == q.num_args() && 
               "The number of variables in the map must match the number of arguments in the query predicate");
        z3::expr_vector conjuncts(m_ctx);
        for (unsigned i = 0; i < vars.size(); ++i) {
            conjuncts.push_back(vars[i] == q.arg(i));
        }
        return z3::mk_and(conjuncts);
    }

    void MT_fixedpoint::add_predicate_fact(z3::func_decl const& key, z3::expr const& head, Theory theory) {
        z3::expr_vector vars = head.args();
        std::string fact_name_str = kAdded_fact_name + std::to_string(added_fact_counter);
        z3::symbol fact_name = m_ctx.str_symbol(fact_name_str.c_str());
        z3::expr added_fact(m_ctx);
        if (theory == Theory::IAUF) {
            CHC fact(vars, m_ctx.bool_val(true), get_bv_expr_bound(vars), head);
            added_fact = fact.get_rule_expr();
            m_fp_int.add_rule(added_fact, fact_name);
            // Store the fact in the fact map with the head predicate decl AST as the key
            Z3_ast ast = key;
            p_to_fact_map.emplace(ast, std::make_pair(fact, fact_name));
        }
        else if (theory == Theory::BV) {
            CHC fact(vars, m_ctx.bool_val(true), m_ctx.bool_val(true), head);
            added_fact = fact.get_rule_expr();
            m_fp_bv.add_rule(added_fact, fact_name);
            // Store the fact in the fact map with the head predicate decl AST as the key
            Z3_ast ast = key;
            p_to_fact_map.emplace(ast, std::make_pair(fact, fact_name));
        }
        else
            ASSERT_FALSE("Invalid theory for predicate fact addition");
    }

    void MT_fixedpoint::add_variable_map(z3::expr_vector bv_vars, z3::expr_vector int_vars) {
        assert(bv_vars.size() == int_vars.size() && "The size of bv_vars and int_vars must be the same");
        
        // This is used only to create an assertion
        [[maybe_unused]] auto arg_is_const = [](const z3::expr& e) {
            // Checks if e is an argument (an app of arity 0)
            return e.is_const() && !e.is_numeral();
        };
        
        for (int i = 0; i < bv_vars.size(); ++i) {
            assert(arg_is_const(bv_vars[i]) && "bv_vars must contain a BV variable");
            assert(arg_is_const(int_vars[i]) && "int_vars must contain an int variable");

            DEBUG_MSG(OUT() << "Adding variable map: " 
                << bv_vars[i] << " <-> " << int_vars[i] << std::endl);

            // Insert the int variable into the bv2int_var_map
            m_bv2int_var_map.emplace(bv_vars[i], int_vars[i]);
            // Insert the bv variable into the int2bv_var_map
            m_int2bv_var_map.emplace(int_vars[i], bv_vars[i]);
        }
    }

    //==============================================================================
    //                              PUBLIC METHODS
    //==============================================================================
    MT_fixedpoint::MT_fixedpoint(z3::context& ctx, bool is_signed, unsigned bv_size, bool int2bv_preprocess, bool simplify)
        : m_ctx(ctx), m_fp_int(ctx), m_fp_bv(ctx), m_mth_fp_set(ctx),
          m_bv_size(bv_size), m_is_signed(is_signed),
          m_int2bv_preprocess(int2bv_preprocess), m_simplify(simplify) {
        // Set the solvers to use spacer engines for integer and bit-vector theories.
        // TODO: Introduce fp.set instead of initializing here.
        z3::params p(ctx);
        p.set("engine", "spacer");
        p.set("fp.xform.slice", false);
        p.set("fp.xform.inline_linear", false);
        p.set("fp.xform.inline_eager", false);
        m_fp_int.set(p);
        m_fp_bv.set(p);
    }

    MT_fixedpoint::MT_fixedpoint(z3::context& ctx, bool int2bv_preprocess, bool simplify)
        : MT_fixedpoint(ctx, true, 4, int2bv_preprocess, simplify) {
        // TODO: In the future, only initialize the context.
        // TODO: The rest of the class fields will be inferred automatically.
    }

    void MT_fixedpoint::from_solver(z3::fixedpoint& fp) {
        // TODO: Understand whether it's needed to deal with assertions.
        DEBUG_MSG(OUT() << "Importing rules from fixedpoint solver:\n" << fp << std::endl);
        z3::expr_vector clauses = fp.rules();

        std::map<z3::expr, ClauseAnalysisResult, compare_expr> clause_analysis_map;

        // The first loop analyzes the clauses to determine the global signedness
        // which is needed before we do anything else.
        // Also, to do the analysis only once, we store the analysis results in a map.
        for (auto clause : clauses) {
            DEBUG_MSG(OUT() << "Analyzing clause:\n" << clause << std::endl);
            ClauseAnalysisResult clause_analysis = analyze_clause(m_ctx, clause);
            DEBUG_MSG(OUT() << clause_analysis);

            if (clause_analysis.has_conflicting_signedness())
                ASSERT_FALSE("Clause has conflicting signedness information");

            if (clause_analysis.is_signedness_determined()) {
                bool clause_is_signed = clause_analysis.get_is_signed();
                if (!m_mth_fp_set.check_and_set_signedness(clause_is_signed)) {
                    ASSERT_FALSE("Conflicting signedness information between clauses");
                }
            }

            clause_analysis_map.emplace(clause, clause_analysis);            
        }

        std::optional<bool> global_signedness = m_mth_fp_set.get_global_signedness();
        if (!global_signedness.has_value())
            ASSERT_FALSE("Could not determine global signedness from the clauses");

        bool is_signed = global_signedness.value();
        for (auto clause : clauses) {
            z3::symbol name = m_mth_fp_set.get_fresh_rule_name();
            auto clause_analysis = clause_analysis_map.at(clause);

            if (clause_analysis.has_bit_manipulating_apps ||
                !clause_analysis.is_bv_size_determined()) {
                m_mth_fp_set.getOrInitBVSolver().add_rule(clause, name);
            }
            else {
                // Bv size is determined and there are no bit-manipulating apps
                unsigned bv_size = clause_analysis.bv_size;
                z3::expr_vector bv_vars_exprs = get_clause_vars(clause);
                VarMap bv_to_int_var_map = build_bv2int_var_map(m_ctx, bv_vars_exprs, clause_analysis);
                // Initialize a translator with no_overflow guarantee
                Bv2IntTranslator translator(m_ctx, is_signed, bv_size, /*simplify*/ true, /*no_overflow*/ true, bv_to_int_var_map);
                z3::expr int_clause = translate_BV_CHC_rule(clause, clause_analysis, translator);
                m_mth_fp_set.getOrInitIAUFSolver(bv_size).add_rule(int_clause, name);
            }
        }

        DEBUG_MSG(OUT() << "The set of solvers after importing rules:\n" << m_mth_fp_set << std::endl);
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

    void MT_fixedpoint::add_interface_constraint(z3::expr p1_expr, Theory theory_1, 
                                                 z3::expr p2_expr, Theory theory_2) {
        if (theory_1 == Theory::IAUF && theory_2 == Theory::BV) {
            m_int2bv_map.insert(p1_expr, p2_expr);
            // Map the variables to allow translation between the two theories
            add_variable_map(p2_expr.args(), p1_expr.args());
        }
        else if (theory_1 == Theory::BV && theory_2 == Theory::IAUF) {
            m_bv2int_map.insert(p1_expr, p2_expr);
            // Map the variables to allow translation between the two theories
            add_variable_map(p1_expr.args(), p2_expr.args());
        }
        else
            ASSERT_FALSE("theory_1 and theory_2 must be different theories");
        
        // Add a fact for the interface predicate in the second theory
        DEBUG_MSG(OUT() << "Adding interface constraint: " 
            << p1_expr << " ------> " << p2_expr << std::endl);
        
        // Initialize the strengthening expression of the source predicate to true
        p_to_strengthening_expr_map.emplace(p1_expr.decl(), m_ctx.bool_val(true));

        add_predicate_fact(p1_expr.decl(), p2_expr, theory_2);
    }

    z3::check_result MT_fixedpoint::query(z3::expr_vector& vars, z3::expr& q_pred, z3::expr& q_phi) {
        // TODO: Implement generic query that infers the theory from the predicate
        // TODO: Try and make take a single expr argument for the query instead of predicate and phi separately
        NOT_IMPLEMENTED();
    }

    z3::check_result MT_fixedpoint::query(z3::expr_vector& vars, z3::expr& q_pred, z3::expr& q_phi, Theory theory) {
        bool is_signed = m_is_signed;
        unsigned bv_size = m_bv_size;

        struct QueryConfig {
            z3::expr_vector vars; // The variables in the query
            z3::expr p; // The query's predicate expression
            z3::expr phi; // The query's phi formula expression
            Theory i; // The theory we're currently processing
            QueryConfig(z3::expr_vector& _vars, z3::expr& _p, z3::expr& _phi, Theory _i)
                : vars(_vars), p(_p), phi(_phi), i(_i) {}
        };

        std::stack<QueryConfig> S;
        S.push(QueryConfig(vars, q_pred, q_phi, theory)); // line 2

        while (!S.empty()) { // line 3
            QueryConfig config = S.top(); // line 4

            // line 5 
            // Construct the query
            z3::expr p_query(m_ctx);
            z3::check_result res;
            if (config.i == Theory::IAUF) {
                p_query = z3::exists(config.vars, config.p && config.phi);
                DEBUG_MSG(OUT() << "Integer engine:\n" << engine_int() << std::endl);
                DEBUG_MSG(OUT() << "Querying integer engine with:\n" << p_query << std::endl);
                res = engine_int().query(p_query);
            } else if (config.i == Theory::BV) {
                p_query = z3::exists(config.vars, config.p && config.phi);
                DEBUG_MSG(OUT() << "Bit-vector engine:\n" << engine_bv() << std::endl);
                DEBUG_MSG(OUT() << "Querying bit-vector engine with:\n" << p_query << std::endl);
                res = engine_bv().query(p_query);
            } else {
                ASSERT_FALSE("Unsupported theory in MT_fixedpoint::query");
            }
            
            Theory next_theory = (config.i == Theory::IAUF) ? Theory::BV : Theory::IAUF; // line 6
            
            if (res == z3::unsat) { // line 7
                S.pop(); // line 8
                if (!S.empty()) { // line 9
                    // line 10
                    if (config.i == Theory::IAUF) {
                        // Work with the integer engine
                        z3::func_decl p_decl = config.p.decl();
                        z3::expr p_interp = engine_int().get_cover_delta(-1, p_decl);
                        p_interp = p_interp.substitute(config.p.args());
                        DEBUG_MSG(OUT() << "Interpretation of " << p_decl.name() << ":\n" << p_interp << std::endl);

                        // Initialize the translator
                        Int2BvTranslator int2bv_t(m_ctx, is_signed, bv_size, m_simplify);
                        z3::expr bv_p_interp = int2bv_t.translate(p_interp, /*preprocess*/ m_int2bv_preprocess);
                        DEBUG_MSG(OUT() << "Translated interpretation of " << p_decl.name() << ":\n" << bv_p_interp << std::endl);

                        // Strengthen the strengthening expression
                        auto st_it = p_to_strengthening_expr_map.find(p_decl);
                        assert(st_it != p_to_strengthening_expr_map.end());
                        if (!p_interp.is_true())
                            st_it->second = st_it->second && p_interp;

                        // Get all info
                        Z3_ast key = p_decl;
                        //! We assume at most one fact is registered for each predicate
                        auto it = p_to_fact_map.find(key);
                        assert(it != p_to_fact_map.end() && "Fact not found in the map");
                        CHCFactConfig* fact_config = &it->second; // get the config
                        z3::symbol fact_name = fact_config->second; // get CHC fact name
                        DEBUG_MSG(OUT() << "Fact name: " << fact_name << std::endl);
                        DEBUG_MSG(OUT() << "Old fact: " << fact_config->first.get_rule_expr() << std::endl);
                        
                        // Strengthen the fact
                        if (!bv_p_interp.is_true())
                            fact_config->first.body_formula = fact_config->first.body_formula && bv_p_interp;
                        z3::expr new_fact = fact_config->first.get_rule_expr();
                        DEBUG_MSG(OUT() << "New fact: " << new_fact << std::endl);

                        m_fp_bv.update_rule(new_fact, fact_name);
                    }
                    else if (config.i == Theory::BV) {
                        // Work with the bit-vector engine
                        z3::func_decl p_decl = config.p.decl();
                        z3::expr p_interp = engine_bv().get_cover_delta(-1, p_decl);
                        p_interp = p_interp.substitute(config.p.args());
                        DEBUG_MSG(OUT() << "Interpretation of " << p_decl.name() << ":\n" << p_interp << std::endl);
                        
                        // Initialize the translator
                        Bv2IntTranslator bv2int_t(m_ctx, is_signed, bv_size, m_simplify);
                        z3::expr int_p_interp = bv2int_t.translate(p_interp);
                        // Go over all the lemmas and conjoin them with the tranlsated predicate
                        z3::expr_vector lemmas(m_ctx);
                        for (const auto& kv : bv2int_t.lemmas()) {
                            lemmas.push_back(kv.second);
                        }
                        int_p_interp = int_p_interp && z3::mk_and(lemmas);
                        DEBUG_MSG(OUT() << "Translated interpretation of " << p_decl.name() << ":\n" << int_p_interp << std::endl);

                        // Strengthen the strengthening expression
                        auto st_it = p_to_strengthening_expr_map.find(p_decl);
                        assert(st_it != p_to_strengthening_expr_map.end());
                        if (!p_interp.is_true())
                            st_it->second = st_it->second && p_interp;

                        // Get all info
                        Z3_ast key = p_decl;
                        //! We assume at most one fact is registered for each predicate
                        auto it = p_to_fact_map.find(key);
                        assert(it != p_to_fact_map.end() && "Fact not found in the map");
                        CHCFactConfig* fact_config = &it->second; // get the config
                        z3::symbol fact_name = fact_config->second; // get CHC fact name
                        DEBUG_MSG(OUT() << "Fact name: " << fact_name << std::endl);
                        DEBUG_MSG(OUT() << "Old fact: " << fact_config->first.get_rule_expr() << std::endl);

                        // Strengthn the fact
                        if (!int_p_interp.is_true())
                            fact_config->first.body_formula = fact_config->first.body_formula && int_p_interp;
                        z3::expr new_fact = fact_config->first.get_rule_expr();
                        DEBUG_MSG(OUT() << "New fact: " << new_fact << std::endl);

                        m_fp_int.update_rule(new_fact, fact_name);
                    }
                    else {
                        ASSERT_FALSE("Unsupported theory in MT_fixedpoint::query");
                    }

                } // line 11
            }
            else if (res == z3::sat) { // line 12
                if (config.i == Theory::IAUF) {
                    // line 13
                    z3::expr g_refutation = engine_int().get_answer();
                    DEBUG_MSG(OUT() << "Refutation:\n" << g_refutation << std::endl);

                    Int2BvTranslator int2bv_t(m_ctx, is_signed, bv_size, m_simplify);
                    
                    // Extract the refutation leaf predicate
                    z3::expr q = get_refutation_leaf_pred(g_refutation);
                    DEBUG_MSG(OUT() << "Refutation leaf predicate: " << q << std::endl);

                    // If we're dealing with a non user-visible predicate, use the query
                    // predicate from the config, otherwise use the query predicate from the refutation
                    z3::func_decl search_decl = (is_user_visible_predicate(q.decl())) ? q.decl() : config.p.decl();
                    
                    if (auto q_tag = m_bv2int_map.find_pred(search_decl)) { // line 14
                        // line 15
                        z3::expr_vector original_vars = m_bv2int_map.get_dst_vars(search_decl);
                        z3::expr phi = get_refutation_leaf_phi(q, original_vars);
                        DEBUG_MSG(OUT() << "phi: " << phi << std::endl);

                        z3::expr phi_trans = int2bv_t.translate(phi, /*preprocess*/ m_int2bv_preprocess);
                        DEBUG_MSG(OUT() << "Translated phi: " << phi_trans << std::endl);
                        z3::expr_vector translated_vars = int2bv_t.vars();
                        
                        z3::expr q_tag_new = q_tag.value().decl()(translated_vars);
                        DEBUG_MSG(OUT() << "q' (with translated vars) = " << q_tag_new << std::endl);

                        auto st_it = p_to_strengthening_expr_map.find(q_tag.value().decl());
                        assert(st_it != p_to_strengthening_expr_map.end() && "Strengthening expression not found");
                        z3::expr query_phi = phi_trans || !(st_it->second);

                        S.push(QueryConfig(translated_vars, q_tag_new, query_phi, next_theory));
                    }
                    else { // line 16
                        // line 17
                        return z3::sat;
                    } // line 18
                }
                else if (config.i == Theory::BV) {
                    // line 13
                    z3::expr g_refutation = engine_bv().get_answer();
                    DEBUG_MSG(OUT() << "Refutation:\n" << g_refutation << std::endl);

                    Bv2IntTranslator bv2int_t(m_ctx, is_signed, bv_size, m_simplify);

                    // Extract the refutation leaf predicate
                    z3::expr q = get_refutation_leaf_pred(g_refutation);
                    DEBUG_MSG(OUT() << "Refutation leaf predicate: " << q << std::endl);
                    
                    // If we're dealing with a non user-visible predicate, use the query
                    // predicate from the config, otherwise use the query predicate from the refutation
                    z3::func_decl search_decl = (is_user_visible_predicate(q.decl())) ? q.decl(): config.p.decl();

                    if (auto q_tag = m_int2bv_map.find_pred(search_decl)) { // line 14
                        // line 15
                        z3::expr_vector original_vars = m_int2bv_map.get_dst_vars(search_decl);
                        z3::expr phi = get_refutation_leaf_phi(q, original_vars);
                        DEBUG_MSG(OUT() << "phi: " << phi << std::endl);

                        z3::expr phi_trans = bv2int_t.translate(phi);
                        // Go over all the lemmas and conjoin them with the tranlsated predicate
                        z3::expr_vector lemmas(m_ctx);
                        for (const auto& kv : bv2int_t.lemmas()) {
                            lemmas.push_back(kv.second);
                        }
                        phi_trans = (phi_trans) && z3::mk_and(lemmas);
                        DEBUG_MSG(OUT() << "Translated phi: " << phi_trans << std::endl);
                        z3::expr_vector translated_vars = bv2int_t.vars();
                        
                        z3::expr q_tag_new = q_tag.value().decl()(translated_vars);
                        DEBUG_MSG(OUT() << "q' (with translated vars) = " << q_tag_new << std::endl);
                        
                        auto st_it = p_to_strengthening_expr_map.find(q_tag.value().decl());
                        assert(st_it != p_to_strengthening_expr_map.end() && "Strengthening expression not found");
                        z3::expr query_phi = phi_trans || !(st_it->second);

                        S.push(QueryConfig(translated_vars, q_tag_new, query_phi, next_theory));
                    }
                    else { // line 16
                        // line 17
                        return z3::sat;
                    } // line 18
                }
                else {
                    ASSERT_FALSE("Unsupported theory in MT_fixedpoint::query");
                }

            } // line 19
            else { // z3::unknown
                // Propagate unknown result
                return z3::unknown;
            }
        } // line 20

        return z3::unsat; // line 21
    }

} // namespace multi_theory_horn