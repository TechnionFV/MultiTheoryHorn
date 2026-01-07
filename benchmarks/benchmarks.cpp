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
// -------- Helpers --------

params get_bv_params(context& c) {
    params param(c);
    param.set("engine", "spacer");
    //set_param("verbose", 10);
    param.set("fp.xform.slice", false);
    param.set("fp.xform.inline_linear", false);
    param.set("fp.xform.inline_eager", false);
    return param;
}

// ========================= [max-inv] =========================
// unsigned benchmark
check_result max_inv(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);

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
    // fragment: IA[size]
    expr rule1 = forall(x, y, z, implies(ugt(x, y) && uge(x - y, z), p(y, z, x, c.bv_val(0, size))));
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(y,z,a,i), i < z --> p(y,z,a-1,i+1)
    // fragment: IA[size]
    expr rule2 = forall(vars, implies(p(y, z, a, i) && ult(i, z), p(y, z, a - c.bv_val(1, size), i + c.bv_val(1, size))));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(y,z,a,i), !(i < z) --> q(y,a)
    // fragment: IA[size]
    expr rule3 = forall(vars, implies(p(y, z, a, i) && !ult(i, z), q(y, a)));
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(y,a), !(a == max(a,y)) --> false
    // fragment: BV
    expr_vector query_vars(c);
    query_vars.push_back(y);
    query_vars.push_back(a);
    expr query_pred = q(y, a); 
    expr bad_phi = !(a == (a ^ ((a ^ y) & ite(ult(a, y), c.bv_val(-1, size), c.bv_val(0, size)))));

    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: q^{size} --> q
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// ========================= [max-inv] =========================

// ====================== [opposite-signs] =====================
// signed benchmark
check_result opposite_signs(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);

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
    // fragment: IA[size]
    expr rule1 = forall(x, implies(x > 0, p(x, c.bv_val(0, size), c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,a,b), a < x --> p(x,a + 1,b - 1)
    // fragment: IA[size]
    expr rule2 = forall(vars, implies(p(x, a, b) && (a < x), p(x, a + c.bv_val(1, size), b - c.bv_val(1, size))));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,a,b), !(a < x) --> q(a,b)
    // fragment: IA[size]
    expr rule3 = forall(vars, implies(p(x, a, b) && !(a < x), q(a, b)));
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(a,b), !(a,b have opposite signs) --> false
    // fragment: BV
    expr_vector query_vars(c);
    query_vars.push_back(a);
    query_vars.push_back(b);
    expr query_pred = q(a, b);
    expr bad_phi = !((a ^ b) < 0);
    
    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: q^{size} --> q
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// ====================== [opposite-signs] =====================

// ========================== [abs-ge] =========================
// signed benchmark
check_result abs_ge(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr i = c.bv_const("i", size);

    expr_vector vars(c);
    vars.push_back(x);
    vars.push_back(y);
    vars.push_back(i);

    // Rules
    // x != -2^(k-1), y == |x| --> p(x,y,0)
    // fragment: BV
    expr min_val = shl(c.bv_val(1,size), c.bv_val(size - 1,size));
    expr rule1 = forall(x, y, implies((x != min_val) && (y == (c.bv_val(1,size) | ite(x >= 0, c.bv_val(0, size), c.bv_val(-1, size))) * x), p(x, y, c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,i), i < y --> p(x,y,i + 1)
    // fragment: IA[size]
    expr rule2 = forall(vars, implies(p(x, y, i) && (i < y), p(x, y, i + c.bv_val(1, size))));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,i), !(i < y) --> q(x,i)
    // fragment: IA[size]
    expr rule3 = forall(vars, implies(p(x, y, i) && !(i < y), q(x, i)));      
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(x,i), !(x <= i) --> false
    // fragment: IA[size]
    expr_vector query_vars(c);
    query_vars.push_back(x);
    query_vars.push_back(i);
    expr query_pred = q(x, i); 
    expr bad_phi = !(x <= i);

    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: p --> p^{size}
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// ========================== [abs-ge] =========================

// ======================== [cond-negate] ======================
// signed benchmark
check_result cond_negate(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr i = c.bv_const("i", size);
    expr b = c.bv_const("b", size);

    // Rules
    // x > y, y > 0 --> p(x,y,0)
    // fragment: IA[size]
    expr rule1 = forall(x, y, implies(x > y && y > c.bv_val(0, size), p(x, y, c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,i), i < y --> p(x,y,i + 2)
    // fragment: IA[size]
    expr rule2 = forall(x, y, i, implies(p(x, y, i) && (i < y), p(x, y, i + 2)));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,i), !(i < y) --> q(x,i)
    // fragment: IA[size]
    expr rule3 = forall(x, y, i, implies(p(x, y, i) && !(i < y), q(x, i)));      
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(x,i), b == ite(i <= x,1,0), !((x ^ (-b)) + b == -x) --> false
    // fragment: BV
    expr_vector query_vars(c);
    query_vars.push_back(x);
    query_vars.push_back(i);
    query_vars.push_back(b);
    expr query_pred = q(x, i);
    expr bad_phi = (b == ite(i <= x, c.bv_val(1, size), c.bv_val(0, size))) && !(((x ^ (-b)) + b) == -x);

    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: q^{size} --> q
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// ======================== [cond-negate] ======================

// =========================== [swap] ==========================
// unsigned benchmark
check_result swap(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl r = function("r", bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);
    fp.register_relation(r);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr a = c.bv_const("a", size);
    expr b = c.bv_const("b", size);
    expr a1 = c.bv_const("a1", size);
    expr b1 = c.bv_const("b1", size);

    // Rules
    // ugt(x,y), ugt(y,0) --> p(x,y,0,0)
    // fragment: IA[size]
    expr rule1 = forall(x, y, implies(ugt(x, y) && ugt(y, 0), p(x, y, c.bv_val(0, size), c.bv_val(0, size))));
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,a,b), ult(b,y) --> p(x,y,a+1,b+1) 
    // fragment: IA[size]
    expr rule2 = forall(x, y, a, b, implies(p(x, y, a, b) && ult(b, y), p(x, y, a + c.bv_val(1, size), b + c.bv_val(1, size))));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,a,b), !ult(b,y) --> q(x,a,b)
    // fragment: IA[size]
    expr rule3 = forall(x, y, a, b, implies(p(x, y, a, b) && !ult(b, y), q(x, a, b)));
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(x,a,b), ult(a,x) --> q(x,a+1,b)
    // fragment: IA[size]
    expr rule4 = forall(x, a, b, implies(q(x, a, b) && ult(a, x), q(x, a + c.bv_val(1, size), b)));
    symbol name4 = c.str_symbol("rule4");
    fp.add_rule(rule4, name4);

    // q(x,a,b), !ult(a,x) --> r(a,b)
    // fragment: IA[size]
    expr rule5 = forall(x, a, b, implies(q(x, a, b) && !ult(a, x), r(a, b)));
    symbol name5 = c.str_symbol("rule5");
    fp.add_rule(rule5, name5);

    // r(a,b), a1 = a ^ b, b1 = b ^ a1, !ult(a1^b1, b1) --> false 
    // fragment: BV
    expr_vector query_vars(c);
    query_vars.push_back(a);
    query_vars.push_back(b);
    query_vars.push_back(a1);
    query_vars.push_back(b1);
    expr query_pred = r(a, b);
    expr bad_phi = (a1 == (a ^ b)) && (b1 == (b ^ a1)) && !ult((a1 ^ b1), b1);

    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: r^{size} --> r
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// =========================== [swap] ==========================

// ================== [opposite-signs-concat] ==================
// signed benchmark
check_result opposite_signs_concat(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    unsigned int d_size = size * 2;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bv_d_sort = c.bv_sort(d_size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bool_sort);
    func_decl r = function("r", bv_d_sort, bv_d_sort, bv_d_sort, bool_sort);
    func_decl s = function("s", bv_d_sort, bv_d_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);
    fp.register_relation(r);
    fp.register_relation(s);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr a = c.bv_const("a", size);
    expr b = c.bv_const("b", size);
    expr d = c.bv_const("d", size);
    
    expr a2 = c.bv_const("a2", d_size);
    expr b2 = c.bv_const("b2", d_size);
    expr i = c.bv_const("x", d_size);

    // Rules

    // x > 0 --> p(x,0,0)
    // fragment: IA[size]
    expr rule1 = forall(x, implies(x > 0, p(x, c.bv_val(0, size), c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,a,b), a < x --> p(x,a + 1,b - 1)
    // fragment: IA[size]
    expr rule2 = forall(x, a, b, implies(p(x, a, b) && (a < x), p(x, a + c.bv_val(1, size), b - c.bv_val(1, size))));
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,a,b), !(a < x) --> q(a,b)
    // fragment: IA[size]
    expr rule3 = forall(x, a, b, implies(p(x, a, b) && !(a < x), q(a, b)));
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(a,b), a2=concat(a,d), b2=concat(b,d), i=concat(0,d) --> r(a2,b2,i)
    // fragment: BV
    expr_vector vars(c);
    vars.push_back(a);
    vars.push_back(b);
    vars.push_back(d);
    vars.push_back(a2);
    vars.push_back(b2);
    vars.push_back(i);
    expr zero = c.bv_val(0, size);
    expr rule4 = forall(vars, implies(q(a,b) && (a2 == concat(a,d)) && (b2 == concat(b,d)) && (i == concat(zero,d)), r(a2,b2,i)));
    symbol name4 = c.str_symbol("rule4");
    fp.add_rule(rule4, name4);

    // r(a2,b2,i), i > 0 --> r(a2 - 1, b2 - 1, i - 1)
    // fragment: IA[2*size]
    expr rule5 = forall(a2, b2, i, implies(r(a2,b2,i) && i > 0, r(a2 - c.bv_val(1, d_size), b2 - c.bv_val(1, d_size), i - c.bv_val(1, d_size))));
    symbol name5 = c.str_symbol("rule5");
    fp.add_rule(rule5, name5);

    // r(a2,b2,i), !(i > 0) --> s(a2, b2)
    // fragment: IA[2*size]
    expr rule6 = forall(a2, b2, i, implies(r(a2,b2,i) && !(i > 0), s(a2, b2)));
    symbol name6 = c.str_symbol("rule6");
    fp.add_rule(rule6, name6);

    // s(a2,b2), !(a,b have opposite signs) --> false
    // fragment: BV
    expr_vector query_vars(c);
    query_vars.push_back(a2);
    query_vars.push_back(b2);
    expr query_pred = s(a2, b2);
    expr bad_phi = !((a2 ^ b2) < 0);

    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: q^{size} --> q, r --> r^{2*size}, s^{2*size} --> s
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// ================== [opposite-signs-concat] ==================

// ==================== [cond-negate-concat] ===================
// signed benchmark
check_result cond_negate_concat(unsigned int size, bool is_multi) {
    context c;
    fixedpoint fp(c);

    unsigned int d_size = size * 2;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bv_d_sort = c.bv_sort(d_size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);
    func_decl q = function("q", bv_sort, bv_sort, bool_sort);
    func_decl r = function("r", bv_d_sort, bv_d_sort, bv_d_sort, bool_sort);
    func_decl s = function("s", bv_d_sort, bv_d_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);
    fp.register_relation(q);
    fp.register_relation(r);
    fp.register_relation(s);

    params param = get_bv_params(c);
    fp.set(param);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr i = c.bv_const("i", size);
    expr d = c.bv_const("d", size);

    expr x2 = c.bv_const("x2", d_size);
    expr i2 = c.bv_const("i2", d_size);
    expr j = c.bv_const("j", d_size);
    expr b = c.bv_const("b", d_size);

    // Rules
    
    // x > y, y > 0 --> p(x,y,0)
    // fragment: IA[size]
    expr rule1 = forall(x, y, implies(x > y && y > c.bv_val(0, size), p(x, y, c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,i), i < y --> p(x,y,i + 2)
    // fragment: IA[size]
    expr rule2 = forall(x, y, i, implies(p(x, y, i) && (i < y), p(x, y, i + 2)));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,i), !(i < y) --> q(x,i)
    // fragment: IA[size]
    expr rule3 = forall(x, y, i, implies(p(x, y, i) && !(i < y), q(x, i)));      
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);

    // q(x,i), x2=concat(x,d), i2=concat(i,d), j=concat(0,d) --> r(x2,i2,j)
    // fragment: BV
    expr_vector vars(c);
    vars.push_back(x);
    vars.push_back(i);
    vars.push_back(d);
    vars.push_back(x2);
    vars.push_back(i2);
    vars.push_back(j);
    expr zero = c.bv_val(0, size);
    expr rule4 = forall(vars, implies(q(x,i) && (x2 == concat(x,d)) && (i2 == concat(i,d)) && (j == concat(zero,d)), r(x2,i2,j)));
    symbol name4 = c.str_symbol("rule4");
    fp.add_rule(rule4, name4);

    // r(x2,i2,j), j > 0 --> r(x2 - 1, i2 - 1, j - 1)
    // fragment: IA[2*size]
    expr rule5 = forall(x2, i2, j, implies(r(x2,i2,j) && j > 0, r(x2 - c.bv_val(1, d_size), i2 - c.bv_val(1, d_size), j - c.bv_val(1, d_size))));
    symbol name5 = c.str_symbol("rule5");
    fp.add_rule(rule5, name5);

    // r(x2,i2,j), !(j > 0) --> s(x2, i2)
    // fragment: IA[2*size]
    expr rule6 = forall(x2, i2, j, implies(r(x2,i2,j) && !(j > 0), s(x2, i2)));
    symbol name6 = c.str_symbol("rule6");
    fp.add_rule(rule6, name6);

    // s(x2,i2), b == ite(i2 <= x2,1,0), !((x2 ^ (-b)) + b == -x2) --> false
    // fragment: BV
    expr_vector query_vars(c);
    query_vars.push_back(x2);
    query_vars.push_back(i2);
    query_vars.push_back(b);
    expr query_pred = s(x2, i2);
    expr bad_phi = (b == ite(i2 <= x2, c.bv_val(1, d_size), c.bv_val(0, d_size))) && !(((x2 ^ (-b)) + b) == -x2);
    
    check_result result = check_result::unknown;

    if (is_multi) {
        // interface constraints: q^{size} --> q, r --> r^{2*size}, s^{2*size} --> s
        MT_fixedpoint mtfp(c);
        mtfp.from_solver(fp);
        result = mtfp.query(query_vars, query_pred, bad_phi); 
    } else { // bv only
        expr query = exists(query_vars, query_pred && bad_phi);
        result = fp.query(query);
    }

    return result;
}
// ==================== [cond-negate-concat] ===================

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
        "  --multi          Use the underlying multi-theory solver"
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
    using BenchFn = std::function<check_result(unsigned int,bool)>;
    struct Benchmark {
        BenchFn fn;
        bool enabled;
    };

    const std::unordered_map<std::string, Benchmark> REGISTRY = {
        {"max-inv",                     {max_inv,                       true}},
        {"opposite-signs",              {opposite_signs,                true}},
        {"abs-ge",                      {abs_ge,                        true}},
        {"cond-negate",                 {cond_negate,                   true}},
        {"swap",                        {swap,                          true}},
        {"opposite-signs-concat",       {opposite_signs_concat,         true}},
        {"cond-negate-concat",          {cond_negate_concat,            true}},
    };

    std::string bench = "";
    unsigned int size = 0;
    bool quiet = false, brunch = false, multi = false;
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
        } else if (std::strcmp(argv[i], "--multi") == 0) {
            multi = true;
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
        check_result r = it->second.fn(size, multi);
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
