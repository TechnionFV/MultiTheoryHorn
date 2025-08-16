#include "Int2BvPreprocessor.h"

namespace multi_theory_horn {
    Int2BvPreprocessor::Int2BvPreprocessor(z3::context& c, unsigned bv_size, bool is_signed) :
        m_ctx(c),
        m_bv_size(bv_size),
        m_is_signed(is_signed),
        m_vars_bound_lemmas(c)
    {}

    void Int2BvPreprocessor::reset() {
        m_handled_vars.clear();
        m_vars_bound_lemmas = z3::expr_vector(m_ctx);
        m_const_out_of_bounds.clear();
        m_func_app_out_of_bounds.clear();
        m_literals.clear();
    }

    int Int2BvPreprocessor::calc_num_of_conjuncts(const z3::expr& e) const {
        if (e.is_and()) {
            return e.num_args();
        }
        return 1;
    }

    int Int2BvPreprocessor::calc_num_of_disjuncts(const z3::expr& e) const {
        if (e.is_or()) {
            return e.num_args();
        }
        return 1;
    }

    bool Int2BvPreprocessor::is_const_variable(const z3::expr& e) const {
        // Check if the expression is a variable (0-arity application)
        return e.is_const() && !e.is_numeral() && !e.is_bool();
    }

    z3::expr Int2BvPreprocessor::create_term_out_of_bounds_expr(const z3::expr& e) const {
        Z3_decl_kind e_kind = e.decl().decl_kind();
        z3::expr res(m_ctx);

        if (m_is_signed) {
            int64_t N = (int64_t)1 << (m_bv_size - 1);
            switch (e_kind) {
                case Z3_OP_ADD:
                case Z3_OP_SUB:
                case Z3_OP_MUL:
                    res = !create_bounds_expr(e);
                    break;
                case Z3_OP_UMINUS:
                    res = (e.arg(0) == m_ctx.int_val(-N));
                    break;
                case Z3_OP_DIV:
                case Z3_OP_IDIV:
                    res = ((e.arg(0) == m_ctx.int_val(-N)) && (e.arg(1) == m_ctx.int_val(-1)));
                    break;
                default:
                    UNREACHABLE();
            }
        }
        else {
            int64_t N = (uint64_t)1 << m_bv_size;
            switch (e_kind) {
                case Z3_OP_ADD:
                    res = (e > m_ctx.int_val(N - 1));
                    break;
                case Z3_OP_SUB:
                    res = (e.arg(0) < e.arg(1));
                    break;
                case Z3_OP_MUL:
                    res = (e > m_ctx.int_val(N - 1));
                    break;
                case Z3_OP_UMINUS:
                    res = (e.arg(0) != m_ctx.int_val(0));
                    break;
                default:
                    UNREACHABLE();
            }
        }
        return res;
    }

    void Int2BvPreprocessor::handle_term(const z3::expr& e, z3::expr_vector& func_app_out_of_bounds) const {
        Z3_decl_kind e_kind = e.decl().decl_kind();
        if (m_is_signed) {
            // Handle signed operations
            if (e_kind == Z3_OP_ADD || e_kind == Z3_OP_SUB ||
                e_kind == Z3_OP_MUL || e_kind == Z3_OP_UMINUS ||
                e_kind == Z3_OP_DIV || e_kind == Z3_OP_IDIV) {
                z3::expr out_of_bounds_expr = create_term_out_of_bounds_expr(e);
                func_app_out_of_bounds.push_back(out_of_bounds_expr);
            }
        }
        
        if (e_kind == Z3_OP_ADD || e_kind == Z3_OP_SUB ||
            e_kind == Z3_OP_MUL || e_kind == Z3_OP_UMINUS) {
            // Handle unsigned operations
            z3::expr out_of_bounds_expr = create_term_out_of_bounds_expr(e);
            func_app_out_of_bounds.push_back(out_of_bounds_expr);
        }
    }
    
    z3::expr Int2BvPreprocessor::create_bounds_expr(const z3::expr& term) const {
        if (m_is_signed) {
            int64_t N = (int64_t)1 << (m_bv_size - 1);
            return (term >= m_ctx.int_val(-N)) && (term <= m_ctx.int_val(N - 1));
        }

        int64_t N = (uint64_t)1 << m_bv_size;
        return (term >= m_ctx.int_val(0)) && (term <= m_ctx.int_val(N - 1));
    }

    bool Int2BvPreprocessor::is_const_in_bounds(const z3::expr& const_e) const {
        assert(const_e.is_numeral() && "Expected a constant expression");
        if (m_is_signed) {
            int64_t N = (int64_t)1 << (m_bv_size - 1);
            return const_e.get_numeral_int() >= -N && const_e.get_numeral_int() <= N - 1;
        }

        int64_t N = (uint64_t)1 << m_bv_size;
        return const_e.get_numeral_int() >= 0 && const_e.get_numeral_int() <= N - 1;
    }

    void Int2BvPreprocessor::populate_data_structures(const z3::expr& e) {
        int n_conjuncts = calc_num_of_conjuncts(e);

        m_const_out_of_bounds.resize(n_conjuncts);
        m_func_app_out_of_bounds.resize(n_conjuncts);
        m_literals.resize(n_conjuncts);

        for (int i = 0; i < n_conjuncts; ++i) {
            z3::expr conjunct = (n_conjuncts == 1) ? e : e.arg(i);
            int n_disjuncts = calc_num_of_disjuncts(conjunct);

            m_const_out_of_bounds[i].resize(n_disjuncts, false);
            m_func_app_out_of_bounds[i].resize(n_disjuncts, z3::expr_vector(m_ctx));
            m_literals[i].resize(n_disjuncts, z3::expr(m_ctx));

            for (int j = 0; j < n_disjuncts; ++j) {
                z3::expr literal = (n_disjuncts == 1) ? conjunct : conjunct.arg(j);
                z3::expr_vector literal_func_app_out_of_bounds(m_ctx);
                bool literal_const_out_of_bounds = false;

                analyze_literal(literal, literal_const_out_of_bounds, literal_func_app_out_of_bounds);

                m_literals[i][j] = literal;
                m_const_out_of_bounds[i][j] = literal_const_out_of_bounds;
                m_func_app_out_of_bounds[i][j] = literal_func_app_out_of_bounds;
            }
        }
    }
    
    void Int2BvPreprocessor::analyze_literal(const z3::expr& literal, bool& const_out_of_bounds,
                                             z3::expr_vector& func_app_out_of_bounds) {
        if (literal.is_true() || literal.is_false()) {
            return;
        }
        else if (literal.is_numeral()) {
            bool in_bounds = is_const_in_bounds(literal);
            const_out_of_bounds |= !in_bounds;
        }
        else if (is_const_variable(literal) && 
                 m_handled_vars.find((Z3_ast)literal) == m_handled_vars.end()) {
            // Add the variable to the cache if not already handled
            m_handled_vars.insert((Z3_ast)literal);
            z3::expr var_bound_expr = create_bounds_expr(literal);
            m_vars_bound_lemmas.push_back(var_bound_expr);
        }
        else {
            handle_term(literal, func_app_out_of_bounds);

            for (unsigned i = 0; i < literal.num_args(); ++i) {
                analyze_literal(literal.arg(i), const_out_of_bounds, func_app_out_of_bounds);
            }
        }
    }

    int Int2BvPreprocessor::get_num_of_conjuncts() const {
        assert(m_literals.size() > 0 && "Data structures not populated");
        return m_literals.size();
    }

    int Int2BvPreprocessor::get_num_of_disjuncts(int conjunct) const {
        assert(conjunct >= 0 && conjunct < m_literals.size() && "Invalid conjunct index");
        return m_literals[conjunct].size();
    }

    z3::expr Int2BvPreprocessor::create_SAT_out_of_bounds_expr(const z3::expr& e) const {
        z3::expr bounds = z3::mk_and(m_vars_bound_lemmas);
        z3::expr rest = m_ctx.bool_val(false);
        int n_conjuncts = get_num_of_conjuncts();
        
        for (int i = 0; i < n_conjuncts; ++i) {
            int n_disjuncts = get_num_of_disjuncts(i);
            bool const_out_of_bounds = false;
            for (int j = 0; j < n_disjuncts; ++j) {
                if(!m_const_out_of_bounds[i][j]) {
                    const_out_of_bounds = true;
                    break;
                }
            }

            // An optimization instead of creating a large expression
            if (!const_out_of_bounds) {
                continue;
            }
            else {
                z3::expr conjuncts = m_ctx.bool_val(true);
                for (int j = 0; j < n_disjuncts; ++j) {
                    if (m_const_out_of_bounds[i][j]) {
                        continue;
                    }
                    
                    conjuncts = conjuncts && (!m_literals[i][j] || z3::mk_or(m_func_app_out_of_bounds[i][j]));
                }
                rest = rest || conjuncts;
            }
        }
        z3::expr res(m_ctx);
        res = e && bounds && rest;
        return res.simplify();
    }

    z3::expr Int2BvPreprocessor::create_UNSAT_out_of_bounds_expr(const z3::expr& e) const {
        z3::expr bounds = z3::mk_and(m_vars_bound_lemmas);
        z3::expr rest = m_ctx.bool_val(true);
        int n_conjuncts = get_num_of_conjuncts();
        
        for (int i = 0; i < n_conjuncts; ++i) {
            int n_disjuncts = get_num_of_disjuncts(i);
            bool const_out_of_bounds = true;
            for (int j = 0; j < n_disjuncts; ++j) {
                if(!m_const_out_of_bounds[i][j]) {
                    const_out_of_bounds = false;
                    break;
                }
            }

            // An optimization instead of creating a large expression
            if (const_out_of_bounds) {
                continue;
            }
            else {
                z3::expr conjunct = m_ctx.bool_val(false);
                for (int j = 0; j < n_disjuncts; ++j) {
                    conjunct = conjunct || m_literals[i][j];
                }
                z3::expr disjuncts = m_ctx.bool_val(false);
                for (int j = 0; j < n_disjuncts; ++j) {
                    if (m_const_out_of_bounds[i][j]) {
                        continue;
                    }
                    
                    disjuncts = disjuncts || z3::mk_or(m_func_app_out_of_bounds[i][j]);
                }
                rest = rest && (conjunct || disjuncts);
            }
        }
        z3::expr res(m_ctx);
        res = !e && bounds && rest;
        return res;
    }

    z3::expr Int2BvPreprocessor::create_SAT_out_of_bounds(const z3::expr& e) {
        populate_data_structures(e);
        return create_SAT_out_of_bounds_expr(e);
    }

    z3::expr Int2BvPreprocessor::create_UNSAT_out_of_bounds(const z3::expr& e) {
        populate_data_structures(e);
        return create_UNSAT_out_of_bounds_expr(e);
    }

    z3::expr Int2BvPreprocessor::preprocess(const z3::expr& e) {
        populate_data_structures(e);
        z3::expr psi = create_SAT_out_of_bounds_expr(e);
        z3::expr psi_tag = create_UNSAT_out_of_bounds_expr(e);
        // TODO: Continue logic ...
        return psi;
    }
} // namespace multi_theory_horn