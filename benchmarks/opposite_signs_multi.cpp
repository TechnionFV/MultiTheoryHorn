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

check_result opposite_signs_multi(unsigned int size) {      // int - - -> bv, signed variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ true, size);

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
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);      

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: opposite_signs_multi <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = opposite_signs_multi(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
