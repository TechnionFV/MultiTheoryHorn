// bench/max_bv.cpp
#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

check_result abs_bv(unsigned int size) {
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
    expr y = c.bv_const("y", size);
    expr i = c.bv_const("i", size);

    // Rules
    // x != 2^(k-1), y == |x| --> p(x,y,0)
    uint64_t min_bv = (uint64_t)1 << (size - 1);
    expr rule1 = forall(x, y, implies((x != c.bv_val(min_bv,size)) && (y == (c.bv_val(1,size) | ite(x >= 0, c.bv_val(0, size), c.bv_val(-1, size))) * x), p(x, y, c.bv_val(0, size))));     
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    // p(x,y,i), i < y --> p(x,y,i + 1)
    expr rule2 = forall(x, y, i, implies(p(x, y, i) && (i < y), p(x, y, i + 1)));      
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // p(x,y,i), !(i < y), !(x <= i) --> false
    expr query = exists(x, y, i, p(x, y, i) && !(i < y) && !(x <= i));        
    check_result result = fp.query(query);

    // std::cout << "\nSpacer's output:\n";
    // std::cout << fp.get_answer() << "\n";

    return result;
}

int main(int argc, char **argv) {
    if (argc != 2) {
      std::cerr << "usage: abs_bv <bv_size>\n";
      return 1;
    }
    unsigned int sz = std::stoi(argv[1]);

    auto res = abs_bv(sz);

    std::cout << (res==sat ? "SAT\n" :
                  res==unsat ? "UNSAT\n" : "UNKNOWN\n");
    return 0;
}
