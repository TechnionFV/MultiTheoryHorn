// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result opposite_signs_bv(unsigned int size) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);

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
    expr query = exists(vars, p(x, a, b) && !(a < x) && !((a ^ b) < 0));        
    check_result result = fp.query(query);

    // std::cout << "\nSpacer's output:\n";
    // std::cout << fp.get_answer() << "\n";

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: opposite_signs_bv <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = opposite_signs_bv(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
