#include <iostream>
#include <z3++.h>
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

expr bounds(context& c, const expr& e, unsigned int k) {
    uint64_t N = (uint64_t)1 << k;
    return (c.int_val(0) <= e) && (e < c.int_val(N));
}

check_result max_unsigned_multi(unsigned int size) {
    context c;

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort int_sort = c.int_sort();
    sort bool_sort = c.bool_sort();
	
    MT_fixedpoint mtfp(c, size);

    // Declare int relations
    func_decl p_int = function("p_int", int_sort, int_sort, int_sort, int_sort, int_sort, bool_sort);
    func_decl q_int = function("q_int", int_sort, int_sort, int_sort, int_sort, int_sort, bool_sort);

    // Declare bv relations
    func_decl q_bv = function("q_bv", bv_sort, bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);

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

    expr_vector vars_int(c);
    vars_int.push_back(x_int);
    vars_int.push_back(y_int);
    vars_int.push_back(z_int);
    vars_int.push_back(a_int);
    vars_int.push_back(i_int);

    // bv variables
    expr x_bv = c.bv_const("x_bv", size);
    expr y_bv = c.bv_const("y_bv", size);
    expr z_bv = c.bv_const("z_bv", size);
    expr a_bv = c.bv_const("a_bv", size);
    expr i_bv = c.bv_const("i_bv", size);

    expr_vector vars_bv(c);
    vars_bv.push_back(x_bv);
    vars_bv.push_back(y_bv);
    vars_bv.push_back(z_bv);
    vars_bv.push_back(a_bv);
    vars_bv.push_back(i_bv);

    // int rules
    expr rule1_int = forall(x_int, y_int, z_int, implies((x_int > y_int) && (x_int - y_int >= z_int) && bounds(c,x_int,size) && bounds(c, y_int, size) && bounds(c, z_int, size), p_int(x_int, y_int, z_int, x_int, c.int_val(0))));      // x > y, z <= x - y, bounds(x), bounds(y), bounds(z) --> p(x,y,z,x,0)
    symbol name1 = c.str_symbol("rule1_int");
    mtfp.add_rule(rule1_int, Theory::IAUF, name1);

    expr rule2_int = forall(vars_int, implies(p_int(x_int, y_int, z_int, a_int, i_int) && (i_int < z_int), p_int(x_int, y_int, z_int, a_int - 1, i_int + 1)));      // p(x,y,z,a,i), i < z --> p(x,y,z,a - 1,i + 1)
    symbol name2 = c.str_symbol("rule2_int");
    mtfp.add_rule(rule2_int, Theory::IAUF, name2);

    expr rule3_int = forall(vars_int, implies(p_int(x_int, y_int, z_int, a_int, i_int) && !(i_int < z_int), q_int(x_int, y_int, z_int, a_int, i_int)));     // p(x,y,z,a,i), !(i < z) --> q(x,y,z,a,i)
    symbol name3 = c.str_symbol("rule3_int");
    mtfp.add_rule(rule3_int, Theory::IAUF, name3);

    // interface constraint int --> bv
    mtfp.add_interface_constraint(q_int, Theory::IAUF, q_bv, Theory::BV);

    // bv query
    expr query_bv_pred = q_bv(x_bv, y_bv, z_bv, a_bv, i_bv);
    expr query_bv_phi =  !(a_bv == (a_bv ^ ((a_bv ^ y_bv) & ite(ult(a_bv, y_bv), c.bv_val(-1, size), c.bv_val(0, size)))));
    check_result result = mtfp.query(vars_bv, query_bv_pred, query_bv_phi, Theory::BV);

    if (result == sat) {
        std::cout << "SAT: Bad state is reachable.\n";
    }
    else if (result == unsat) {
        std::cout << "UNSAT: Bad state is unreachable.\n";
    }
    else {
        std::cout << "UNKNOWN.\n";
    }

    return result;
}

check_result max_unsigned_bv(unsigned int size) {
    context c;
    fixedpoint fp(c);

    // Declare sorts
    sort bv_sort = c.bv_sort(size);
    sort bool_sort = c.bool_sort();

    // Declare relations
    func_decl p = function("p", bv_sort, bv_sort, bv_sort, bv_sort, bv_sort, bool_sort);

    // Register them with the fixedpoint engine (required)
    fp.register_relation(p);

    // Set engine to Spacer explicitly (optional — it's the default)
    params param(c);
    param.set("engine", "spacer");
    //set_param("verbose", 10);
    fp.set(param);

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
    expr rule1 = forall(x, y, z, implies(ugt(x, y) && uge(x - y, z), p(x, y, z, x, c.bv_val(0u, size))));                                               // x > y, z >= 0, z <= x - y --> p(x,y,z,x,0)
    symbol name1 = c.str_symbol("rule1");
    fp.add_rule(rule1, name1);

    expr rule2 = forall(vars, implies(p(x, y, z, a, i) && ult(i, z), p(x, y, z, a - c.bv_val(1u, size), i + c.bv_val(1u, size))));                      // p(x,y,z,a,i), i < z --> p(x,y,z,a-1,i+1)
    symbol name2 = c.str_symbol("rule2");
    fp.add_rule(rule2, name2);

    expr query = exists(vars, p(x, y, z, a, i) && !ult(i, z) && !(a == (a ^ ((a ^ y) & ite(ult(a, y), c.bv_val(-1, size), c.bv_val(0, size))))));
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

    return result;
}

int main() {
    try {
        unsigned int size = 4;
        //max_unsigned_bv(size);
        //max_unsigned_multi(size);
    }
    catch (exception& ex) {
        std::cout << "unexpected error: " << ex << "\n";
    }
    Z3_finalize_memory();
    return 0;
}