#include <iostream>
#include "z3++.h"

using namespace z3;

void int_example() {
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
    expr rule1 = forall(x, implies(x == 0, init(x)));                   // init(x) :- x == 0.
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);
    expr rule2 = forall(x, implies(init(x), step(x, x + 1)));           // step(x, x+1) :- init(x).
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);
    expr rule3 = forall(x, x1, implies(step(x, x1), init(x1)));         // init(x1) :- step(x, x1).
    symbol name3 = c.str_symbol("rule3");
    fp.add_rule(rule3, name3);
    expr rule4 = forall(x, implies(x < 1, bad(x)));                     // bad(x) :- x < 0.
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

    // How to use update_rule(): The new rule should be subsumed in the old rule.
    expr rule4new = forall(x, implies(x < 1 && x < 0, bad(x)));
    fp.update_rule(rule4new, name4);
    std::cout << "\n\nQuery: Can the refined system reach a bad state?\n";
    result = fp.query(query);
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
}

void bv_example() {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    unsigned int size = 4;
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl inv = function("inv", bv_sort, bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(inv);

    // Set engine to Spacer explicitly (optional — it's the default)
    params p(c);
    p.set("engine", "spacer");
    //set_param("verbose", 10);
    fp.set(p);

    // Variables
    expr x = c.bv_const("x", size);
    expr y = c.bv_const("y", size);
    expr z = c.bv_const("z", size);
    expr a = c.bv_const("a", size);
    expr i = c.bv_const("i", size);
    
    expr_vector vars(c);
    vars.push_back(x);
    vars.push_back(y);
    vars.push_back(z);
    vars.push_back(a);
    vars.push_back(i);

    // Rules
    expr rule1 = forall(x, y, z, implies(x > y && z >= 0 && x - y >= z, inv(x,y,z,x,c.bv_val(0,size))));    // x > y, z >= 0, z <= x - y --> inv(x,y,z,x,0)
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    expr rule2 = forall(vars, implies(inv(x,y,z,a,i) && i < z, inv(x,y,z,a - 1,i + 1)));                    // inv(x,y,z,a,i), i < z --> inv(x,y,z,a-1,i+1)
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    // Query
    //expr query = exists(vars, inv(x,y,z,a,i) && y > x);
    //expr query = exists(vars, inv(x, y, z, a, i) && !(i < z) && !(a == x - z));
    expr query = exists(vars, inv(x, y, z, a, i) && !(i < z) && !(a == (a ^ ((a ^ y) & ite(a < y, c.bv_val(-1, size), c.bv_val(0, size))))));
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
}

int main() {
    
    try {
        //int_example();
        bv_example();
    }
    catch (exception& ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }
    Z3_finalize_memory();
    return 0;
}
