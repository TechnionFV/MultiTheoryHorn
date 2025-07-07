// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result max_bv(unsigned int size) {
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

    // Set engine to Spacer explicitly (optional — it's the default)
    params param(c);
    param.set("engine", "spacer");
    //set_param("verbose", 10);
    param.set("fp.xform.slice", false);
    param.set("fp.xform.inline_linear", false);
    param.set("fp.xform.inline_eager", false);
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
    expr query = exists(vars, p(y, z, a, i) && !ult(i, z) && !(a == (a ^ ((a ^ y) & ite(ult(a, y), c.bv_val(-1, size), c.bv_val(0, size))))));
    check_result result = fp.query(query);

    // std::cout << "\nSpacer's output:\n";
    // std::cout << fp.get_answer() << "\n";

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: max_bv <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = max_bv(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
