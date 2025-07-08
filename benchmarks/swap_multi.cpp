// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result swap_multi(unsigned int size) {      // bv - - -> int, unsigned variables, multiple loops
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    MT_fixedpoint mtfp(c, /* is_signed */ false, size);

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
    
    check_result result;
    result = mtfp.query(query_vars, query_int_pred, query_int_phi, Theory::IAUF);

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: swap_multi <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = swap_multi(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
