// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result swap_bv(unsigned int size) {
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
    //set_param("verbose", 10);
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
    expr rule10 = forall(x, z, a, b, implies(p4(x, z, a, b) && ult(a, z - x), p4(x, z, a, b + 1)));
    symbol name10 = c.str_symbol("rule10");
    fp.add_rule(rule10, name10);

    // p4(x,z,a,b), !(b < z - x), !(a < b) --> false
    expr query = exists(x, z, a, b, p4(x, z, a, b) && !ult(a, z - x) && !(ult(a, b)));
    check_result result = fp.query(query);

    // std::cout << "\nSpacer's output:\n";
    // std::cout << fp.get_answer() << "\n";

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: swap_bv <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = swap_bv(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
