// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

expr bounds(context& c, const expr& e, bool is_signed, unsigned int k) {
    if (is_signed) {
        int N = (uint64_t)1 << (k - 1);
        return (c.int_val(-N) <= e) && (e < c.int_val(N));
    }
    uint64_t N = (uint64_t)1 << k;
    return (c.int_val(0) <= e) && (e < c.int_val(N));
}

check_result swap2_multi(unsigned int size) { // int - - -> bv , unsigned variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ false, size);

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
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: swap2_multi <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = swap2_multi(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
