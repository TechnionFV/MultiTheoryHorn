// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result abs_multi(unsigned int size) {      // bv - - -> int, signed variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ true, size);

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
    check_result result = mtfp.query(query_vars, query_int_pred, query_int_phi, Theory::IAUF);

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: abs_multi <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = abs_multi(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
