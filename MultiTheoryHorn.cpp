#include <iostream>
#include "z3++.h"

using namespace z3;

int main() {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl init = function("init", int_sort, bool_sort);
    func_decl step = function("step", int_sort, int_sort, bool_sort);
    func_decl bad = function("bad", int_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(init);
    fp.register_relation(step);
    fp.register_relation(bad);

    // Set engine to Spacer explicitly (optional — it's the default)
    params p(c);
    p.set("engine", "spacer");
    //set_param("verbose", 10);
    fp.set(p);

    // Variables
    expr x = c.int_const("x");
    expr x1 = c.int_const("x1");

    // Rules
    expr rule1 = forall(x,implies(x==0, init(x)));                  // init(x) :- x == 0.
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1,name1);                              
    expr rule2 = forall(x, implies(init(x), step(x, x + 1)));       // step(x, x+1) :- init(x).
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);
    expr rule3 = forall(x,x1,implies(step(x, x1), init(x1)));       // init(x1) :- step(x, x1).
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);
    expr rule4 = forall(x, implies(x < 0, bad(x)));                 // bad(x) :- x >= 5.
    symbol name4 = c.str_symbol("rule4");
    fp.add_rule(rule4, name4);                 

    // Query
    std::cout << "Query: Can the system reach a bad state?\n";
    expr query = exists(x, init(x) && bad(x));

    check_result result = fp.query(query);

    if (result == sat) {
        std::cout << "SAT: Bad state is reachable.\n";
    }
    else if (result == unsat) {
        std::cout << "UNSAT: Bad state is unreachable.\n";
    }
    else {
        std::cout << "UNKNOWN.\n";
    }

    std::cout << "\nSpacer's output:\n";
    std::cout << fp.get_answer() << "\n";

    std::cout << "\n The satisfying interpretation:\n";
    std::cout << "init:\n" << fp.get_cover_delta(-1, init) << "\n";
    std::cout << "step:\n" << fp.get_cover_delta(-1, step) << "\n";
    std::cout << "bad:\n" << fp.get_cover_delta(-1, bad) << "\n";

    return 0;
}
