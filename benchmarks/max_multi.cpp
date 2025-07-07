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

check_result max_multi(unsigned int size) { // int - - -> bv , unsigned variables
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ false, size);

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
    check_result result = mtfp.query(query_vars, query_bv_pred, query_bv_phi, Theory::BV);      

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: max_multi <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = max_multi(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
