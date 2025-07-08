// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result swap2_bv(unsigned int size) {
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

    // Set engine to Spacer explicitly (optional — it's the default)
    params param(c);
    param.set("engine", "spacer");
    param.set("fp.xform.slice", false);
    param.set("fp.xform.inline_linear", false);
    param.set("fp.xform.inline_eager", false);
    //set_param("verbose", 10);
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
    expr query = exists(a, b, r3(a, b) && !ult(a, b));
    check_result result = fp.query(query);

    // std::cout << "\nSpacer's output:\n";
    // std::cout << fp.get_answer() << "\n";

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: swap2_bv <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = swap2_bv(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
