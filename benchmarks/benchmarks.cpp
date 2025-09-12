/*
    When adding a benchmark:
    - Function must take unsigned int (bv_size) and return check_result.
    - Add its name/function to REGISTRY in run_benchmarks_cli.

    Exit codes:
    - 0: SAT
    - 1: UNSAT
    - 2: UNKNOWN
    - 3: Error

    Usage:
    - See print_help() for CLI instructions.
    - Run: ./benchmarks --help
*/

#include <z3++.h>
#include "multi_theory_fixedpoint.h"

#include <string>
#include <fstream>
#include <unordered_map>
#include <functional>
#include <vector>
#include <stdexcept>
#include <cstring>

using namespace z3;
using namespace multi_theory_horn;

// -------- Helpers --------
bool gno_int2bv_preprocess = false;

expr bounds(context& c, const expr& e, bool is_signed, unsigned int k) {
    if (is_signed) {
        uint64_t N = (uint64_t)1 << (k - 1);
        int64_t lower_bound = get_signed_bv_lower_bound(k);
        int64_t upper_bound = get_signed_bv_upper_bound(k);
        return (c.int_val(lower_bound) <= e) && (e <= c.int_val(upper_bound));
    }
    assert(k <= 64 && "Bit-vector size too large");
    uint64_t upper_bound = get_unsigned_bv_upper_bound(k);
    uint64_t lower_bound = get_unsigned_bv_lower_bound(k);
    return (c.int_val(lower_bound) <= e) && (e <= c.int_val(upper_bound));
}

params get_bv_params(context& c) {
    params param(c);
    param.set("engine", "spacer");
    //set_param("verbose", 10);
    param.set("fp.xform.slice", false);
    param.set("fp.xform.inline_linear", false);
    param.set("fp.xform.inline_eager", false);
    return param;
}

// ===================== [max_bv] =====================
check_result max_bv_base(unsigned int size, bool is_sat) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    // func_decl p = function("p", bv_sort, bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr z = c.bv_const("z", size);
    expr a = c.bv_const("a", size);
    expr i = c.bv_const("i", size);

    expr_vector vars(c);
    vars.push_back(y);
    vars.push_back(z);
    vars.push_back(a);
    vars.push_back(i);

    // Rules
    // x > y, x - y >= z --> p(y,z,x,0)
    expr rule1 = forall(x, y, z, implies(ugt(x, y) && uge(x - y, z), p(y, z, x, c.bv_val(0, size))));
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(y,z,a,i), i < z --> p(y,z,a-1,i+1)
    expr rule2 = forall(vars, implies(p(y, z, a, i) && ult(i, z), p(y, z, a - c.bv_val(1, size), i + c.bv_val(1, size))));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(y,z,a,i), !(i < z), !(a == max(a,y)) --> false
    expr bad_phi = !(a == (a ^ ((a ^ y) & ite(ult(a, y), c.bv_val(-1, size), c.bv_val(0, size)))));
    if (!is_sat) {
        // p(y,z,a,i), !(i < z), (a == max(a,y)) --> false
        bad_phi = !bad_phi;
    }
    expr query = exists(vars, p(y, z, a, i) && !ult(i, z) && bad_phi);
    check_result result = fp.query(query);

    return result;
}
check_result max_bv(unsigned int size) { return max_bv_base(size, /*is_sat=*/true); }
check_result max_bv_unsat(unsigned int size) { return max_bv_base(size, /*is_sat=*/false); }
// ===================== [max_bv] =====================


// ===================== [max_multi] =====================
check_result max_multi_base(unsigned int size, bool is_sat) { // int - - -> bv , unsigned variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ false, size, /* int2bv_preprocess */ !gno_int2bv_preprocess);

    // Declare int relations
    func_decl p_int = function("p_int", int_sort, int_sort, int_sort, int_sort, bool_sort);
    func_decl q_int = function("q_int", int_sort, int_sort, bool_sort);

    // Declare bv relations
    func_decl q_bv = function("q_bv", bv_sort, bv_sort, bool_sort);

    // Register relations
    mtfp.register_relation(p_int, Theory::IAUF);
    mtfp.register_relation(q_int, Theory::IAUF);
    mtfp.register_relation(q_bv, Theory::BV);

    // int variables
    expr x_int = c.int_const("x_int");
    expr y_int = c.int_const("y_int");
    expr z_int = c.int_const("z_int");
    expr a_int = c.int_const("a_int");
    expr i_int = c.int_const("i_int");

    // bv variables
    expr x_bv = c.bv_const("x_bv", size);
    expr y_bv = c.bv_const("y_bv", size);
    expr z_bv = c.bv_const("z_bv", size);
    expr a_bv = c.bv_const("a_bv", size);
    expr i_bv = c.bv_const("i_bv", size);

    // int rules
    // x > y, x - y >= z, bounds(x), bounds(y), bounds(z) --> p(y,z,x,0)
    expr rule1_int = forall(x_int, y_int, z_int, implies((x_int > y_int) && (x_int - y_int >= z_int) && bounds(c, x_int, false, size) && bounds(c, y_int, false, size) && bounds(c, z_int, false, size), p_int(y_int, z_int, x_int, c.int_val(0))));
    symbol name1 = c.str_symbol("rule1_int");
    mtfp.add_rule(rule1_int, Theory::IAUF, name1);

    // p(y,z,a,i), i < z --> p(y,z,a - 1,i + 1)
    expr rule2_int = forall(y_int, z_int, a_int, i_int, implies(p_int(y_int, z_int, a_int, i_int) && (i_int < z_int), p_int(y_int, z_int, a_int - 1, i_int + 1)));      
    symbol name2 = c.str_symbol("rule2_int");
    mtfp.add_rule(rule2_int, Theory::IAUF, name2);

    // p(y,z,a,i), !(i < z) --> q(y,a)
    expr rule3_int = forall(y_int, z_int, a_int, i_int, implies(p_int(y_int, z_int, a_int, i_int) && !(i_int < z_int), q_int(y_int, a_int)));       
    symbol name3 = c.str_symbol("rule3_int");
    mtfp.add_rule(rule3_int, Theory::IAUF, name3);

    // interface constraint int - - -> bv
    // q(y,a) - - - -> q'(y',a')
    mtfp.add_interface_constraint(q_int(y_int, a_int), Theory::IAUF, q_bv(y_bv, a_bv), Theory::BV);       

    // bv query
    // q'(y',a'), !(a' == max(y',a')) --> false
    expr_vector query_vars(c);
    query_vars.push_back(y_bv);
    query_vars.push_back(a_bv);
    expr query_bv_pred = q_bv(y_bv, a_bv);
    expr query_bv_phi =  !(a_bv == (a_bv ^ ((a_bv ^ y_bv) & ite(ult(a_bv, y_bv), c.bv_val(-1, size), c.bv_val(0, size)))));
    if (!is_sat)
        query_bv_phi = !query_bv_phi;
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);      

    return result;
}
check_result max_multi(unsigned int size) { return max_multi_base(size, true); }
check_result max_multi_unsat(unsigned int size) { return max_multi_base(size, false); }
// ===================== [max_multi] =====================


// ===================== [opposite_signs_bv] =====================
check_result opposite_signs_bv_base(unsigned int size, bool is_sat) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr a = c.bv_const("a", size);
    expr b = c.bv_const("b", size);

    expr_vector vars(c);
    vars.push_back(x);
    vars.push_back(a);
    vars.push_back(b);

    // Rules
    // x > 0 --> p(x,0,0)
    expr rule1 = forall(x, implies(x > 0, p(x, c.bv_val(0, size), c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,a,b), a < x --> p(x,a + 1,b - 1)
    expr rule2 = forall(vars, implies(p(x, a, b) && (a < x), p(x, a + 1, b - 1)));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,a,b), !(a < x), !(a,b have opposite signs) --> false
    expr bad_phi = !((a ^ b) < 0);
    if (!is_sat) {
        // p(x,a,b), !(a < x), (a,b have opposite signs) --> false
        bad_phi = !bad_phi;
    }
    expr query = exists(vars, p(x, a, b) && !(a < x) && bad_phi);        
    check_result result = fp.query(query);

    return result;
}

check_result opposite_signs_bv(unsigned int size) { return opposite_signs_bv_base(size, /*is_sat=*/true); }
check_result opposite_signs_bv_unsat(unsigned int size) { return opposite_signs_bv_base(size, /*is_sat=*/false); }
// ===================== [opposite_signs_bv] =====================


// ===================== [opposite_signs_multi] =====================
check_result opposite_signs_multi_base(unsigned int size, bool is_sat) {      // int - - -> bv, signed variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ true, size, /* int2bv_preprocess */ !gno_int2bv_preprocess);

    // Declare int relations
    func_decl p_int = function("p_int", int_sort, int_sort, int_sort, bool_sort);
    func_decl q_int = function("q_int", int_sort, int_sort, bool_sort);

    // Declare bv relations
    func_decl q_bv = function("q_bv", bv_sort, bv_sort, bool_sort);

    // Register relations
    mtfp.register_relation(p_int, Theory::IAUF);
    mtfp.register_relation(q_int, Theory::IAUF);
    mtfp.register_relation(q_bv, Theory::BV);

    // int variables
    expr x_int = c.int_const("x_int");
    expr a_int = c.int_const("a_int");
    expr b_int = c.int_const("b_int");

    // bv variables
    expr a_bv = c.bv_const("a_bv", size);
    expr b_bv = c.bv_const("b_bv", size);

    // int rules
    // x > 0, bounds(x) --> p(x,0,0)
    expr rule1_int = forall(x_int, implies(x_int > 0 && bounds(c,x_int,true,size), p_int(x_int, c.int_val(0), c.int_val(0))));
    symbol name1 = c.str_symbol("rule1_int");
    mtfp.add_rule(rule1_int, Theory::IAUF, name1);

    // p(x,a,b), a < x --> p(x,a + 1,b - 1)
    expr rule2_int = forall(x_int, a_int, b_int, implies(p_int(x_int, a_int, b_int) && (a_int < x_int), p_int(x_int, a_int + 1, b_int - 1)));
    symbol name2 = c.str_symbol("rule2_int");
    mtfp.add_rule(rule2_int, Theory::IAUF, name2);

    // p(x,a,b), !(a < x) --> q(a,b)
    expr rule3_int = forall(x_int, a_int, b_int, implies(p_int(x_int, a_int, b_int) && !(a_int < x_int), q_int(a_int, b_int)));
    symbol name3 = c.str_symbol("rule3_int");
    mtfp.add_rule(rule3_int, Theory::IAUF, name3);

    // interface constraint int - - -> bv
    // q(a,b) - - - -> q'(a',b')
    mtfp.add_interface_constraint(q_int(a_int, b_int), Theory::IAUF, q_bv(a_bv, b_bv), Theory::BV);       

    // bv query
    // q'(a',b'), !(a,b have opposite signs) --> false
    expr_vector query_vars(c);
    query_vars.push_back(a_bv);
    query_vars.push_back(b_bv);
    expr query_bv_pred = q_bv(a_bv, b_bv);
    expr query_bv_phi = !((a_bv ^ b_bv) < 0);
    if (!is_sat)
        query_bv_phi = !query_bv_phi;
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);

    return result;
}
check_result opposite_signs_multi(unsigned int size) { return opposite_signs_multi_base(size, /*is_sat=*/true); }
check_result opposite_signs_multi_unsat(unsigned int size) { return opposite_signs_multi_base(size, /*is_sat=*/false); }
// ===================== [opposite_signs_multi] =====================


// ===================== [abs_bv] =====================
check_result abs_bv_base(unsigned int size, bool is_sat) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr i = c.bv_const("i", size);

    // Rules
    // x != 2^(k-1), y == |x| --> p(x,y,0)
    uint64_t min_bv = (uint64_t)1 << (size - 1);
    expr rule1 = forall(x, y, implies((x != c.bv_val(min_bv,size)) && (y == (c.bv_val(1,size) | ite(x >= 0, c.bv_val(0, size), c.bv_val(-1, size))) * x), p(x, y, c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,i), i < y --> p(x,y,i + 1)
    expr rule2 = forall(x, y, i, implies(p(x, y, i) && (i < y), p(x, y, i + 1)));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,i), !(i < y), !(x <= i) --> false
    expr bad_phi = !(x <= i);
    if (!is_sat) {
        // p(x,y,i), !(i < y), (x <= i) --> false
        bad_phi = !bad_phi;
    }
    expr query = exists(x, y, i, p(x, y, i) && !(i < y) && bad_phi);
    check_result result = fp.query(query);

    return result;
}

check_result abs_bv(unsigned int size) { return abs_bv_base(size, /*is_sat=*/true); }
check_result abs_bv_unsat(unsigned int size) { return abs_bv_base(size, /*is_sat=*/false); }
// ===================== [abs_bv] =====================

// ===================== [abs_multi] =====================
check_result abs_multi_base(unsigned int size, bool is_sat) {      // bv - - -> int, signed variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ true, size, /* int2bv_preprocess */ !gno_int2bv_preprocess);

    // Declare bv relations
    func_decl p_bv = function("p_bv", bv_sort, bv_sort, bool_sort);

    // Declare int relations
    func_decl p_int = function("p_int", int_sort, int_sort, bool_sort);
    func_decl q_int = function("q_int", int_sort, int_sort, int_sort, bool_sort);

    // Register relations
    mtfp.register_relation(p_bv, Theory::BV);
    mtfp.register_relation(p_int, Theory::IAUF);
    mtfp.register_relation(q_int, Theory::IAUF);
    
    // bv variables
    expr x_bv = c.bv_const("x_bv", size);
    expr y_bv = c.bv_const("y_bv", size);
    
    // int variables
    expr x_int = c.int_const("x_int");
    expr y_int = c.int_const("y_int");
    expr i_int = c.int_const("i_int");

    // bv rules
    // x != 2^(k-1), y == |x| --> p(x,y)
    uint64_t min_bv = (uint64_t)1 << (size - 1);
    expr rule1_bv = forall(x_bv, y_bv, implies((x_bv != c.bv_val(min_bv, size)) && (y_bv == (c.bv_val(1, size) | ite(x_bv >= 0, c.bv_val(0, size), c.bv_val(-1, size))) * x_bv), p_bv(x_bv, y_bv)));     
    symbol name1 = c.str_symbol("rule1_bv");
    mtfp.add_rule(rule1_bv, Theory::BV, name1);

    // interface constraint bv - - -> int
    mtfp.add_interface_constraint(p_bv(x_bv, y_bv), Theory::BV, p_int(x_int, y_int), Theory::IAUF);

    // int rules
    // p'(x,y) --> q'(x',y',0)
    expr rule2_int = forall(x_int, y_int, implies(p_int(x_int, y_int), q_int(x_int, y_int, c.int_val(0))));     
    symbol name2 = c.str_symbol("rule2_int");
    mtfp.add_rule(rule2_int, Theory::IAUF, name2);

    // q'(x',y',i), i < y' --> q(x',y',i + 1)
    expr rule3_int = forall(x_int, y_int, i_int, implies(q_int(x_int, y_int, i_int) && (i_int < y_int), q_int(x_int, y_int, i_int + 1)));
    symbol name3 = c.str_symbol("rule3_int");
    mtfp.add_rule(rule3_int, Theory::IAUF, name3);

    // int query
    // q'(x',y',i), !(i < y'), !(x' <= i) --> false
    expr_vector query_vars(c);
    query_vars.push_back(x_int);
    query_vars.push_back(y_int);
    query_vars.push_back(i_int);
    expr query_int_pred = q_int(x_int, y_int, i_int);
    expr query_int_phi = !(i_int < y_int) && !(x_int <= i_int);
    if (!is_sat) {
        // q'(x',y',i), !(i < y'), (x' <= i) --> false
        query_int_phi = !(i_int < y_int) && (x_int <= i_int);
    }
    check_result result = mtfp.query(query_vars, query_int_pred, query_int_phi, Theory::IAUF);      

    return result;
}

check_result abs_multi(unsigned int size) { return abs_multi_base(size, /*is_sat=*/true); }
check_result abs_multi_unsat(unsigned int size) { return abs_multi_base(size, /*is_sat=*/false); }
// ===================== [abs_multi] =====================


// ===================== [cond_negate_bv] =====================
check_result cond_negate_bv_base(unsigned int size, bool is_sat) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr i = c.bv_const("i", size);
    expr b = c.bv_const("b", size);

    // Rules
    // x > y, y > 0 --> p(x,y,0)
    expr rule1 = forall(x, y, implies(x > y && y > c.bv_val(0, size), p(x, y, c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,i), i < y --> p(x,y,i + 2)
    expr rule2 = forall(x, y, i, implies(p(x, y, i) && (i < y), p(x, y, i + 2)));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,i), !(i < y), b == ite(i <= x,1,0), !((x ^ (-b)) + b == -x) --> false
    expr bad_phi = !(((x ^ (-b)) + b) == -x);
    if (!is_sat) {
        // p(x,y,i), !(i < y), b == ite(i <= x,1,0), ((x ^ (-b)) + b == -x) --> false
        bad_phi = !bad_phi;
    }
    expr query = exists(x, y, i, b, p(x, y, i) && !(i < y) && (b == ite(i <= x, c.bv_val(1, size), c.bv_val(0, size))) && bad_phi);
    check_result result = fp.query(query);

    return result;
}

check_result cond_negate_bv(unsigned int size) { return cond_negate_bv_base(size, /*is_sat=*/true); }
check_result cond_negate_bv_unsat(unsigned int size) { return cond_negate_bv_base(size, /*is_sat=*/false); }
// ===================== [cond_negate_bv] =====================


// ===================== [cond_negate_multi] =====================
check_result cond_negate_multi_base(unsigned int size, bool is_sat) {      // int - - -> bv, signed variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ true, size, /* int2bv_preprocess */ !gno_int2bv_preprocess);

    // Declare int relations
    func_decl p_int = function("p_int", int_sort, int_sort, int_sort, bool_sort);
    func_decl q_int = function("q_int", int_sort, int_sort, int_sort, bool_sort);

    // Declare bv relations
    func_decl q_bv = function("q_bv", bv_sort, bv_sort, bv_sort, bool_sort);

    // Register relations
    mtfp.register_relation(p_int, Theory::IAUF);
    mtfp.register_relation(q_int, Theory::IAUF);
    mtfp.register_relation(q_bv, Theory::BV);

    // int variables
    expr x_int = c.int_const("x_int");
    expr y_int = c.int_const("y_int");
    expr i_int = c.int_const("i_int");
    expr b_int = c.int_const("b_int");

    // bv variables
    expr x_bv = c.bv_const("x_bv", size);
    expr i_bv = c.bv_const("i_bv", size);
    expr b_bv = c.bv_const("b_bv", size);

    // int rules
    // x > y, y > 0, bounds(x), bounds(y) --> p(x,y,0)
    expr rule1_int = forall(x_int, y_int, implies(x_int > y_int && y_int > 0 && bounds(c, x_int, true, size) && bounds(c, y_int, true, size), p_int(x_int, y_int, c.int_val(0))));
    symbol name1 = c.str_symbol("rule1_int");
    mtfp.add_rule(rule1_int, Theory::IAUF, name1);

    // p(x,y,i), i < y --> p(x,y,i + 2)
    expr rule2_int = forall(x_int, y_int, i_int, implies(p_int(x_int, y_int, i_int) && (i_int < y_int), p_int(x_int, y_int, i_int + 2)));
    symbol name2 = c.str_symbol("rule2_int");
    mtfp.add_rule(rule2_int, Theory::IAUF, name2);

    // p(x,y,i), !(i < y) --> q(x,i,b)
    expr rule3_int = forall(x_int, y_int, i_int, b_int, implies(p_int(x_int, y_int, i_int) && !(i_int < y_int), q_int(x_int, i_int, b_int)));
    symbol name3 = c.str_symbol("rule3_int");
    mtfp.add_rule(rule3_int, Theory::IAUF, name3);

    // interface constraint int - - -> bv
    // q(x,i) - - - -> q'(x',i')
    mtfp.add_interface_constraint(q_int(x_int, i_int, b_int), Theory::IAUF, q_bv(x_bv, i_bv, b_bv), Theory::BV);

    // bv query
    // q'(x',i', b'), b' == ite(i' <= x',1,0), !((x' ^ (-b')) + b' == -x') --> false
    expr_vector query_vars(c);
    query_vars.push_back(x_bv);
    query_vars.push_back(i_bv);
    query_vars.push_back(b_bv);
    expr query_bv_pred = q_bv(x_bv, i_bv, b_bv);
    expr query_bv_phi = (b_bv == ite(i_bv <= x_bv, c.bv_val(1, size), c.bv_val(0, size))) && !(((x_bv ^ (-b_bv)) + b_bv) == -x_bv);
    if (!is_sat) {
        // q'(x',i', b'), b' == ite(i' <= x',1,0), ((x' ^ (-b')) + b' == -x') --> false
        query_bv_phi = (b_bv == ite(i_bv <= x_bv, c.bv_val(1, size), c.bv_val(0, size))) && (((x_bv ^ (-b_bv)) + b_bv) == -x_bv);;
    }
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);

    return result;
}

check_result cond_negate_multi(unsigned int size) { return cond_negate_multi_base(size, /*is_sat=*/true); }
check_result cond_negate_multi_unsat(unsigned int size) { return cond_negate_multi_base(size, /*is_sat=*/false); }
// ===================== [cond_negate_multi] =====================


// ===================== [swap_bv] =====================
check_result swap_bv_base(unsigned int size, bool is_sat) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p0 = function("p0", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p1 = function("p1", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p2 = function("p2", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p3 = function("p3", bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p4 = function("p4", bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p0);
    fp.register_relation(p1);
    fp.register_relation(p2);
    fp.register_relation(p3);
    fp.register_relation(p4);

    // Set engine to Spacer explicitly (optional — it's the default)
    params param(c);
    param.set("engine", "spacer");
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr x1 = c.bv_const("x1", size);
    expr x2 = c.bv_const("x2", size);
    expr y = c.bv_const("y", size);
    expr y1 = c.bv_const("y1", size);
    expr y2 = c.bv_const("y2", size);
    expr z = c.bv_const("z", size);
    expr z1 = c.bv_const("z1", size);
    expr a = c.bv_const("a", size);
    expr b = c.bv_const("b", size);

    // Rules
    // x != y, y != z, x != z --> p0(x,y,z)
    expr rule1 = forall(x, y, z, implies(x != y && y != z && x != z, p0(x, y, z)));
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p0(x,y,z), x > y, x1 == x ^ y, y1 == y ^ x1, x2 == x1 ^ y1 --> p1(x2,y1,z)
    expr_vector vars2(c);
    vars2.push_back(x);
    vars2.push_back(y);
    vars2.push_back(z);
    vars2.push_back(x1);
    vars2.push_back(x2);
    vars2.push_back(y1);
    expr rule2 = forall(vars2, implies(p0(x, y, z) && ugt(x, y) && (x1 == (x ^ y)) && (y1 == (y ^ x1)) && (x2 == (x1 ^ y1)), p1(x2, y1, z)));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p0(x,y,z), !(x > y) --> p1(x,y,z)
    expr rule3 = forall(x, y, z, implies(p0(x, y, z) && !ugt(x, y), p1(x, y, z)));
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // p1(x,y,z), y > z, y1 == y ^ z, z1 == z ^ y1, y2 == y1 ^ z1 --> p2(x,y2,z1)
    expr_vector vars4(c);
    vars4.push_back(x);
    vars4.push_back(y);
    vars4.push_back(z);
    vars4.push_back(y1);
    vars4.push_back(y2);
    vars4.push_back(z1);
    expr rule4 = forall(vars4, implies(p1(x, y, z) && ugt(y, z) && (y1 == (y ^ z)) && (z1 == (z ^ y1)) && (y2 == (y1 ^ z1)), p2(x, y2, z1)));
    symbol name4 = c.str_symbol("rule4");
    fp.add_rule(rule4, name4);

    // p1(x, y, z), !(y > z) --> p2(x, y, z)
    expr rule5 = forall(x, y, z, implies(p1(x, y, z) && !ugt(y, z), p2(x, y, z)));
    symbol name5 = c.str_symbol("rule5");
    fp.add_rule(rule5, name5);

    // p2(x,y,z), x > y, x1 == x ^ y, y1 == y ^ x1, x2 == x1 ^ y1 --> p3(x2,y1,z,0)
    expr rule6 = forall(vars2, implies(p2(x, y, z) && ugt(x, y) && (x1 == (x ^ y)) && (y1 == (y ^ x1)) && (x2 == (x1 ^ y1)), p3(x2, y1, z, c.bv_val(0, size))));
    symbol name6 = c.str_symbol("rule6");
    fp.add_rule(rule6, name6);

    // p2(x,y,z), !(x > y) --> p3(x,y,z,0)
    expr rule7 = forall(x, y, z, implies(p2(x, y, z) && !ugt(x, y), p3(x, y, z, c.bv_val(0, size))));
    symbol name7 = c.str_symbol("rule7");
    fp.add_rule(rule7, name7);

    // p3(x,y,z,a), a < y - x --> p3(x,y,z,a+1) 
    expr rule8 = forall(x, y, z, a, implies(p3(x, y, z, a) && ult(a, y - x), p3(x, y, z, a + 1)));
    symbol name8 = c.str_symbol("rule8");
    fp.add_rule(rule8, name8);

    // p3(x,y,z,a), !(a < y - x) --> p4(x,z,a,0) 
    expr rule9 = forall(x, y, z, a, implies(p3(x, y, z, a) && !ult(a, y - x), p4(x, z, a, c.bv_val(0,size))));
    symbol name9 = c.str_symbol("rule9");
    fp.add_rule(rule9, name9);

    // p4(x,z,a,b), b < z - x --> p4(x,z,a,b+1) 
    expr rule10 = forall(x, z, a, b, implies(p4(x, z, a, b) && ult(b, z - x), p4(x, z, a, b + 1)));
    symbol name10 = c.str_symbol("rule10");
    fp.add_rule(rule10, name10);

    // p4(x,z,a,b), !(b < z - x), !(a < b) --> false
    expr bad_phi = !(ult(a, b));
    if (!is_sat) {
        // p4(x,z,a,b), !(b < z - x), (a < b) --> false
        bad_phi = !bad_phi;
    }
    expr query = exists(x, z, a, b, p4(x, z, a, b) && !ult(b, z - x) && bad_phi);
    check_result result = fp.query(query);

    return result;
}

check_result swap_bv(unsigned int size) { return swap_bv_base(size, /*is_sat=*/true); }
check_result swap_bv_unsat(unsigned int size) { return swap_bv_base(size, /*is_sat=*/false); }
// ===================== [swap_bv] =====================


// ===================== [swap_multi] =====================
check_result swap_multi_base(unsigned int size, bool is_sat) { // bv - - -> int, unsigned variables, multiple loops
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ false, size, /* int2bv_preprocess */ !gno_int2bv_preprocess);

    // Declare bv relations
    func_decl p0_bv = function("p0_bv", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p1_bv = function("p1_bv", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p2_bv = function("p2_bv", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl p3_bv = function("p3_bv", bv_sort, bv_sort, bv_sort, bool_sort);

    // Declare int relations
    func_decl p3_int = function("p3_int", int_sort, int_sort, int_sort, bool_sort);
    func_decl p3prime_int = function("p3prime_int", int_sort, int_sort, int_sort, int_sort, bool_sort);
    func_decl p4_int = function("p4_int", int_sort, int_sort, int_sort, int_sort, bool_sort);

    // Register relations
    mtfp.register_relation(p0_bv, Theory::BV);
    mtfp.register_relation(p1_bv, Theory::BV);
    mtfp.register_relation(p2_bv, Theory::BV);
    mtfp.register_relation(p3_bv, Theory::BV);
    mtfp.register_relation(p3_int, Theory::IAUF);
    mtfp.register_relation(p3prime_int, Theory::IAUF);
    mtfp.register_relation(p4_int, Theory::IAUF);

    // bv variables
    expr x = c.bv_const("x", size);
    expr x1 = c.bv_const("x1", size);
    expr x2 = c.bv_const("x2", size);
    expr y = c.bv_const("y", size);
    expr y1 = c.bv_const("y1", size);
    expr y2 = c.bv_const("y2", size);
    expr z = c.bv_const("z", size);
    expr z1 = c.bv_const("z1", size);

    // int variables
    expr x_int = c.int_const("x_int");
    expr y_int = c.int_const("y_int");
    expr z_int = c.int_const("z_int");
    expr a_int = c.int_const("a_int");
    expr b_int = c.int_const("b_int");

    // bv rules
    // x != y, y != z, x != z --> p0(x,y,z)
    expr rule1_bv = forall(x, y, z, implies(x != y && y != z && x != z, p0_bv(x, y, z)));
    symbol name1 = c.str_symbol("rule1_bv");
    mtfp.add_rule(rule1_bv, Theory::BV, name1);

    // p0(x,y,z), x > y, x1 == x ^ y, y1 == y ^ x1, x2 == x1 ^ y1 --> p1(x2,y1,z)
    expr_vector vars2(c);
    vars2.push_back(x);
    vars2.push_back(y);
    vars2.push_back(z);
    vars2.push_back(x1);
    vars2.push_back(x2);
    vars2.push_back(y1);
    expr rule2_bv = forall(vars2, implies(p0_bv(x, y, z) && ugt(x, y) && (x1 == (x ^ y)) && (y1 == (y ^ x1)) && (x2 == (x1 ^ y1)), p1_bv(x2, y1, z)));
    symbol name2 = c.str_symbol("rule2_bv");
    mtfp.add_rule(rule2_bv, Theory::BV, name2);

    // p0(x,y,z), !(x > y) --> p1(x,y,z)
    expr rule3_bv = forall(x, y, z, implies(p0_bv(x, y, z) && !ugt(x, y), p1_bv(x, y, z)));
    symbol name3 = c.str_symbol("rule3_bv");
    mtfp.add_rule(rule3_bv, Theory::BV, name3);

    // p1(x,y,z), y > z, y1 == y ^ z, z1 == z ^ y1, y2 == y1 ^ z1 --> p2(x,y2,z1)
    expr_vector vars4(c);
    vars4.push_back(x);
    vars4.push_back(y);
    vars4.push_back(z);
    vars4.push_back(y1);
    vars4.push_back(y2);
    vars4.push_back(z1);
    expr rule4_bv = forall(vars4, implies(p1_bv(x, y, z) && ugt(y, z) && (y1 == (y ^ z)) && (z1 == (z ^ y1)) && (y2 == (y1 ^ z1)), p2_bv(x, y2, z1)));
    symbol name4 = c.str_symbol("rule4_bv");
    mtfp.add_rule(rule4_bv, Theory::BV, name4);

    // p1(x, y, z), !(y > z) --> p2(x, y, z)
    expr rule5_bv = forall(x, y, z, implies(p1_bv(x, y, z) && !ugt(y, z), p2_bv(x, y, z)));
    symbol name5 = c.str_symbol("rule5_bv");
    mtfp.add_rule(rule5_bv, Theory::BV, name5);

    // p2(x,y,z), x > y, x1 == x ^ y, y1 == y ^ x1, x2 == x1 ^ y1 --> p3(x2,y1,z)
    expr rule6_bv = forall(vars2, implies(p2_bv(x, y, z) && ugt(x, y) && (x1 == (x ^ y)) && (y1 == (y ^ x1)) && (x2 == (x1 ^ y1)), p3_bv(x2, y1, z)));
    symbol name6 = c.str_symbol("rule6_bv");
    mtfp.add_rule(rule6_bv, Theory::BV, name6);

    // p2(x,y,z), !(x > y) --> p3(x,y,z)
    expr rule7_bv = forall(x, y, z, implies(p2_bv(x, y, z) && !ugt(x, y), p3_bv(x, y, z)));
    symbol name7 = c.str_symbol("rule7_bv");
    mtfp.add_rule(rule7_bv, Theory::BV, name7);

    // interface constraint bv - - -> int
    // p3(x,y,z) - - - -> p3_int(x',y',z')
    mtfp.add_interface_constraint(p3_bv(x, y, z), Theory::BV, p3_int(x_int, y_int, z_int), Theory::IAUF);

    // p3_int(x,y,z) --> p3'_int(x,y,z,0)
    expr rule8_int = forall(x_int, y_int, z_int, implies(p3_int(x_int, y_int, z_int), p3prime_int(x_int, y_int, z_int, c.int_val(0))));
    symbol name8 = c.str_symbol("rule8_int");
    mtfp.add_rule(rule8_int, Theory::IAUF, name8);

    // p3'_int(x,y,z,a), a < y - x --> p3'_int(x,y,z,a+1)
    expr rule9_int = forall(x_int, y_int, z_int, a_int, implies(p3prime_int(x_int, y_int, z_int, a_int) && (a_int < y_int - x_int), p3prime_int(x_int, y_int, z_int, a_int + 1)));
    symbol name9 = c.str_symbol("rule9_int");
    mtfp.add_rule(rule9_int, Theory::IAUF, name9);

    // p3'_int(x,y,z,a), !(a < y - x) --> p4_int(x,z,a,0)
    expr rule10_int = forall(x_int, y_int, z_int, a_int, implies(p3prime_int(x_int, y_int, z_int, a_int) && !(a_int < y_int - x_int), p4_int(x_int, z_int, a_int, c.int_val(0))));
    symbol name10 = c.str_symbol("rule10_int");
    mtfp.add_rule(rule10_int, Theory::IAUF, name10);

    // p4_int(x,z,a,b), b < z - x --> p4_int(x,z,a,b+1)
    expr rule11_int = forall(x_int, z_int, a_int, b_int, implies(p4_int(x_int, z_int, a_int, b_int) && (b_int < z_int - x_int), p4_int(x_int, z_int, a_int, b_int + 1)));
    symbol name11 = c.str_symbol("rule11_int");
    mtfp.add_rule(rule11_int, Theory::IAUF, name11);

    // int query
    // p4_int(x,z,a,b), !(b < z - x), !(a < b) --> false
    expr_vector query_vars(c);
    query_vars.push_back(x_int);
    query_vars.push_back(z_int);
    query_vars.push_back(a_int);
    query_vars.push_back(b_int);
    expr query_int_pred = p4_int(x_int, z_int, a_int, b_int);
    expr query_int_phi = !(b_int < z_int - x_int) && !(a_int < b_int);
    if (!is_sat) {
        // p4_int(x,z,a,b), !(b < z - x), (a < b) --> false
        query_int_phi = !(b_int < z_int - x_int) && (a_int < b_int);   
    }
    
    check_result result;
    result = mtfp.query(query_vars, query_int_pred, query_int_phi, Theory::IAUF);

    return result;
}

check_result swap_multi(unsigned int size) { return swap_multi_base(size, /*is_sat=*/true); }
check_result swap_multi_unsat(unsigned int size) { return swap_multi_base(size, /*is_sat=*/false); }
// ===================== [swap_multi] =====================


// ===================== [swap2_bv] =====================
check_result swap2_bv_base(unsigned int size, bool is_sat) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl r0 = function("r0", bv_sort, bv_sort, bool_sort);
    func_decl r1 = function("r1", bv_sort, bv_sort, bool_sort);
    func_decl r2 = function("r2", bv_sort, bv_sort, bool_sort);
    func_decl r3 = function("r3", bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);
    fp.register_relation(r0);
    fp.register_relation(r1);
    fp.register_relation(r2);
    fp.register_relation(r3);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr a = c.bv_const("a", size);
    expr b = c.bv_const("b", size);

    // Rules
    // ugt(x,y), ugt(y,0) --> p(x,y,0,0)
    expr rule1 = forall(x, y, implies(ugt(x, y) && ugt(y, 0), p(x, y, c.bv_val(0, size), c.bv_val(0, size))));
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,a,b), ult(b,y) --> p(x,y,a+1,b+1) 
    expr rule2 = forall(x, y, a, b, implies(p(x, y, a, b) && ult(b, y), p(x, y, a + c.bv_val(1, size), b + c.bv_val(1, size))));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,a,b), !ult(b,y) --> q(x,a,b)
    expr rule3 = forall(x, y, a, b, implies(p(x, y, a, b) && !ult(b, y), q(x, a, b)));
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(x,a,b), ult(a,x) --> q(x,a+1,b)
    expr rule4 = forall(x, a, b, implies(q(x, a, b) && ult(a, x), q(x, a + c.bv_val(1, size), b)));
    symbol name4 = c.str_symbol("rule4");
    fp.add_rule(rule4, name4);

    // q(x,a,b), !ult(a,x) --> r0(a,b)
    expr rule5 = forall(x, a, b, implies(q(x, a, b) && !ult(a, x), r0(a, b)));
    symbol name5 = c.str_symbol("rule5");
    fp.add_rule(rule5, name5);

    // r0(a,b) --> r1(a^b,b)
    expr rule6 = forall(a, b, implies(r0(a, b), r1(a ^ b, b)));
    symbol name6 = c.str_symbol("rule6");
    fp.add_rule(rule6, name6);

    // r1(a,b) --> r2(a,b^a)
    expr rule7 = forall(a, b, implies(r1(a, b), r2(a, b ^ a)));
    symbol name7 = c.str_symbol("rule7");
    fp.add_rule(rule7, name7);

    // r2(a,b) --> r3(a^b,b)
    expr rule8 = forall(a, b, implies(r2(a, b), r3(a ^ b, b)));
    symbol name8 = c.str_symbol("rule8");
    fp.add_rule(rule8, name8);

    // r3(a,b) && !(ult(a,b)) --> false
    expr bad_phi = !ult(a, b);
    if (!is_sat)
        bad_phi = !bad_phi;
    expr query = exists(a, b, r3(a, b) && bad_phi);
    check_result result = fp.query(query);

    return result;
}

check_result swap2_bv(unsigned int size) { return swap2_bv_base(size, /*is_sat=*/true); }
check_result swap2_bv_unsat(unsigned int size) { return swap2_bv_base(size, /*is_sat=*/false); }
// ===================== [swap2_bv] =====================


// ===================== [swap2_multi] =====================
check_result swap2_multi_base(unsigned int size, bool is_sat) { // int - - -> bv , unsigned variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ false, size, /* int2bv_preprocess */ !gno_int2bv_preprocess);

    // Declare int relations
    func_decl p_int = function("p_int", int_sort, int_sort, int_sort, int_sort, bool_sort);
    func_decl q_int = function("q_int", int_sort, int_sort, int_sort, bool_sort);
    func_decl r_int = function("r_int", int_sort, int_sort, int_sort, int_sort, int_sort, bool_sort);

    // Declare bv relations
    func_decl r0_bv = function("r0_bv", bv_sort, bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);

    // Register relations
    mtfp.register_relation(p_int, Theory::IAUF);
    mtfp.register_relation(q_int, Theory::IAUF);
    mtfp.register_relation(r_int, Theory::IAUF);
    mtfp.register_relation(r0_bv, Theory::BV);

    // int variables
    expr x_int = c.int_const("x_int");
    expr y_int = c.int_const("y_int");
    expr a_int = c.int_const("a_int");
    expr b_int = c.int_const("b_int");
    expr c_int = c.int_const("c_int");
    expr d_int = c.int_const("d_int");
    expr e_int = c.int_const("e_int");

    // bv variables
    expr a_bv = c.bv_const("a_bv", size);
    expr b_bv = c.bv_const("b_bv", size);
    expr c_bv = c.bv_const("c_bv", size);
    expr d_bv = c.bv_const("d_bv", size);
    expr e_bv = c.bv_const("e_bv", size);

    // int rules
    // ugt(x,y), ugt(y,0) --> p(x,y,0,0)
    expr rule1_int = forall(x_int, y_int, implies((x_int > y_int) && (y_int > 0) && bounds(c, x_int, false, size) && bounds(c, y_int, false, size), p_int(x_int, y_int, c.int_val(0), c.int_val(0))));
    symbol name1 = c.str_symbol("rule1_int");
    mtfp.add_rule(rule1_int, Theory::IAUF, name1);

    // p(x,y,a,b), ult(b,y) --> p(x,y,a+1,b+1) 
    expr rule2_int = forall(x_int, y_int, a_int, b_int, implies(p_int(x_int, y_int, a_int, b_int) && (b_int < y_int), p_int(x_int, y_int, a_int + c.int_val(1), b_int + c.int_val(1))));
    symbol name2 = c.str_symbol("rule2_int");
    mtfp.add_rule(rule2_int, Theory::IAUF, name2);

    // p(x,y,a,b), !ult(b,y) --> q(x,a,b)
    expr rule3_int = forall(x_int, y_int, a_int, b_int, implies(p_int(x_int, y_int, a_int, b_int) && !(b_int < y_int), q_int(x_int, a_int, b_int)));
    symbol name3 = c.str_symbol("rule3_int");
    mtfp.add_rule(rule3_int, Theory::IAUF, name3);

    // q(x,a,b), ult(a,x) --> q(x,a+1,b)
    expr rule4_int = forall(x_int, a_int, b_int, implies(q_int(x_int, a_int, b_int) && (a_int < x_int), q_int(x_int, a_int + c.int_val(1), b_int)));
    symbol name4 = c.str_symbol("rule4_int");
    mtfp.add_rule(rule4_int, Theory::IAUF, name4);

    // q(x,a,b), !ult(a,x) --> r_int(a,b)
    expr_vector rule5_vars(c);
    rule5_vars.push_back(x_int);
    rule5_vars.push_back(a_int);
    rule5_vars.push_back(b_int);
    rule5_vars.push_back(c_int);    
    rule5_vars.push_back(d_int);
    rule5_vars.push_back(e_int);
    expr rule5_int = forall(rule5_vars, implies(q_int(x_int, a_int, b_int) && !(a_int < x_int), r_int(a_int, b_int, c_int, d_int, e_int)));
    symbol name5 = c.str_symbol("rule5_int");
    mtfp.add_rule(rule5_int, Theory::IAUF, name5);

    // interface constraint int - - -> bv
    // r_int(a,b) - - - -> r0(a',b')
    mtfp.add_interface_constraint(r_int(a_int, b_int, c_int, d_int, e_int), Theory::IAUF, r0_bv(a_bv, b_bv, c_bv, d_bv, e_bv), Theory::BV);

    // bv query
    // r0(a,b,c,d,e) && c=a^b && d=c^b && e=c^d && !(ult(e,d)) --> false
    expr_vector query_vars(c);
    query_vars.push_back(a_bv);
    query_vars.push_back(b_bv);
    query_vars.push_back(c_bv);
    query_vars.push_back(d_bv);
    query_vars.push_back(e_bv);
    expr query_bv_pred = r0_bv(a_bv, b_bv, c_bv, d_bv, e_bv);
    expr query_bv_phi = (c_bv == (a_bv ^ b_bv)) && (d_bv == (c_bv ^ b_bv)) && (e_bv == (c_bv ^ d_bv)) && !(ult(e_bv, d_bv));
    if (!is_sat) {
        // r0(a,b,c,d,e) && c=a^b && d=c^b && e=c^d && (ult(e,d)) --> false
        query_bv_phi = (c_bv == (a_bv ^ b_bv)) && (d_bv == (c_bv ^ b_bv)) && (e_bv == (c_bv ^ d_bv)) && (ult(e_bv, d_bv));
    }
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);

    return result;
}

check_result swap2_multi(unsigned int size) { return swap2_multi_base(size, /*is_sat=*/true); }
check_result swap2_multi_unsat(unsigned int size) { return swap2_multi_base(size, /*is_sat=*/false); }
// ===================== [swap2_multi] =====================

// ======================= MAIN LOGIC =======================

enum ExitCode {
    EXIT_SAT     = 0,
    EXIT_UNSAT   = 1,
    EXIT_UNKNOWN = 2,
    EXIT_ERROR   = 3,
    EXIT_NOTHING = 4
};

std::pair<std::string, ExitCode> result_to_string_and_code(check_result cr) {
    switch (cr) {
        case sat:     return {"SAT", EXIT_SAT};
        case unsat:   return {"UNSAT", EXIT_UNSAT};
        case unknown: return {"UNKNOWN", EXIT_UNKNOWN};
    }
    UNREACHABLE();
    return {"ERROR", EXIT_ERROR};
}

static void print_help() {
    OUT() <<
        "Usage:\n"
        "  benchmarks --bench <name> --size <k>\n"
        "Options:\n"
        "  --bench <name>   Benchmark to run (see --list)\n"
        "  --size  <k>      Bit-vector size (unsigned integer > 0)\n"
        "  --list           Print enabled benchmarks\n"
        "  --help           Show this help\n"
        "  --quiet          Don't print anything\n"
        "  --brunch         Print results in BRUNCH_STAT format (bench, size, result)\n"
        "  --no_preprocess  Don't preprocess int2bv translator inputs\n"
        "  --output <file>  Redirect output to given file\n"
        "\n"
        "Exit codes: 0=SAT, 1=UNSAT, 2=UNKNOWN, 3=error\n";
}

static int run_benchmarks_cli(int argc, char** argv) {
    using BenchFn = std::function<check_result(unsigned int)>;
    struct Benchmark {
        BenchFn fn;
        bool enabled;
    };

    // TODO [Omer]: Decide which benchmarks to disable
    const std::unordered_map<std::string, Benchmark> REGISTRY = {
        {"max_bv",                      {max_bv,                        false}},
        {"max_multi",                   {max_multi,                     true}},
        {"opposite_signs_bv",           {opposite_signs_bv,             false}},
        {"opposite_signs_multi",        {opposite_signs_multi,          true}},
        {"abs_bv",                      {abs_bv,                        false}},
        {"abs_multi",                   {abs_multi,                     true}},
        {"cond_negate_bv",              {cond_negate_bv,                false}},
        {"cond_negate_multi",           {cond_negate_multi,             true}},
        {"swap_bv",                     {swap_bv,                       false}},
        {"swap_multi",                  {swap_multi,                    false}},
        {"swap2_bv",                    {swap2_bv,                      false}},
        {"swap2_multi",                 {swap2_multi,                   false}},
        {"max_bv_unsat",                {max_bv_unsat,                  false}},
        {"max_multi_unsat",             {max_multi_unsat,               false}},
        {"opposite_signs_bv_unsat",     {opposite_signs_bv_unsat,       false}},
        {"opposite_signs_multi_unsat",  {opposite_signs_multi_unsat,    false}},
        {"abs_bv_unsat",                {abs_bv_unsat,                  false}},
        {"abs_multi_unsat",             {abs_multi_unsat,               false}},
        {"cond_negate_bv_unsat",        {cond_negate_bv_unsat,          false}},
        {"cond_negate_multi_unsat",     {cond_negate_multi_unsat,       false}},
        {"swap_bv_unsat",               {swap_bv_unsat,                 false}},
        {"swap_multi_unsat",            {swap_multi_unsat,              false}},
        {"swap2_bv_unsat",              {swap2_bv_unsat,                false}},
        {"swap2_multi_unsat",           {swap2_multi_unsat,             false}}
    };

    std::string bench = "";
    unsigned int size = 0;
    bool quiet = false, brunch = false;
    std::string output_path;

    // Parse args
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "--help") == 0) {
            print_help();
            return EXIT_NOTHING;
        } else if (std::strcmp(argv[i], "--list") == 0) {
            for (const auto& kv : REGISTRY) {
                if (kv.second.enabled)
                    OUT() << kv.first << "\n";
            }
            return EXIT_NOTHING;
        } else if (std::strcmp(argv[i], "--bench") == 0 && i + 1 < argc) {
            bench = argv[++i];
        } else if (std::strcmp(argv[i], "--size") == 0 && i + 1 < argc) {
            try {
                size = static_cast<unsigned int>(std::stoul(argv[++i]));
            } catch (...) {
                OUT() << "error: --size expects a positive integer\n";
                return EXIT_ERROR;
            }
            if (size == 0) {
                OUT() << "error: --size must be > 0\n";
                return EXIT_ERROR;
            }
        } else if (std::strcmp(argv[i], "--quiet") == 0) {
            quiet = true;
        } else if (std::strcmp(argv[i], "--brunch") == 0) {
            brunch = true;
        } else if (std::strcmp(argv[i], "--output") == 0 && i + 1 < argc) {
            output_path = argv[++i];
        } else if (std::strcmp(argv[i], "--no_preprocess") == 0) {
            gno_int2bv_preprocess = true;
        } else if (std::strcmp(argv[i], "--debug") == 0) {
            // hidden dev option
            set_mtfp_debug(true);
        } else {
            OUT() << "error: unknown or malformed argument: " << argv[i] << "\n";
            return EXIT_ERROR;
        }
    }

    if (bench.empty() || size == 0) {
        OUT() << "error: missing required args. Use --bench <name> and --size <k>\n";
        return EXIT_ERROR;
    }

    if (brunch && quiet) {
        OUT() << "error: --brunch and --quiet are incompatible\n";
        return EXIT_ERROR;
    }

    // Set up output redirection if requested
    std::ofstream ofs;
    if (!output_path.empty()) {
        ofs.open(output_path);
        if (!ofs) {
            OUT() << "error: failed to open output file '" << output_path << "'\n";
            return EXIT_ERROR;
        }
        // Point the project-wide OUT() at the file
        set_output_stream(ofs);
    }

    auto it = REGISTRY.find(bench);
    if (it == REGISTRY.end()) {
        OUT() << "error: unknown benchmark '" << bench << "'. Use --list to see options.\n";
        return EXIT_ERROR;
    }

    int exit_code = EXIT_ERROR;
    try {
        // Call the benchmark
        check_result r = it->second.fn(size);
        auto [result_str, code] = result_to_string_and_code(r);
        exit_code = code;

        if (brunch) {
            OUT() << "BRUNCH_STAT bench "  << bench      << "\n";
            OUT() << "BRUNCH_STAT size "   << size       << "\n";
            OUT() << "BRUNCH_STAT result " << result_str << "\n";
        } else if (!quiet) {
            OUT() << result_str << " - (Exit code: " << code << ")\n";
        }
    } catch (const std::exception& e) {
        OUT() << "error: exception thrown: " << e.what() << "\n";
        exit_code = EXIT_ERROR;
    } catch (...) {
        OUT() << "error: unknown exception thrown during execution\n";
        exit_code = EXIT_ERROR;
    }

    return exit_code;
}

// Slim main
int main(int argc, char** argv) {
    return run_benchmarks_cli(argc, argv);
}
