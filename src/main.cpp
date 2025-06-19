#include <iostream>
#include <z3++.h>
#include "Bv2IntTranslator.h"
#include "Int2BvTranslator.h"
#include "multi_theory_fixedpoint.h"

using namespace z3;
using namespace multi_theory_horn;

int main() {
    z3::context c;

    const unsigned bv_size = 4;
    sort bv = c.bv_sort(bv_size);

    // Declare variables
    expr x = c.bv_const("x", bv_size);
    expr y = c.bv_const("y", bv_size);
    expr z = c.bv_const("z", bv_size);
    expr a = c.bv_const("a", bv_size);
    expr b = c.bv_const("b", bv_size);
    expr i = c.bv_const("i", bv_size);

    expr m1 = c.bv_val(15, 4);
    expr m2 = c.bv_val(18, 5);
    expr zero = c.bv_val(0, 2);

    // mask = a ⊕ ((a ⊕ y) & -(a < y)) → b' = a
    // expr mask = a ^ ((a ^ y) & - int2bv(bv_size, ult(a, y)));

    // mask = a + b
    // expr mask = a + b;
    expr mask = int2bv(bv_size, (ule(x, y) && ule(y, z))) + x;
    // expr mask = int2bv(bv_size, c.int_val(55));
    // expr mask = concat(m1, zero);
    // expr mask = ite(uge(x, y), a + b, x * b) + m1;
    // expr mask = a ^ ((a ^ y) & z);
    // expr mask = x / m1;
    std::cout << "Original mask: " << mask << std::endl;

    for (auto sub_expr : mask) {
        std::cout << "Sub-expression: " << sub_expr;
        std::cout << " (is app: " << sub_expr.is_app() << ")" << std::endl;
    }

    // Translate using Bv2IntTranslator
    Bv2IntTranslator bv2int_t(c);
    expr translated_mask = bv2int_t.translate(mask);
    std::cout << "Translated mask is of type: " << translated_mask.get_sort() << std::endl;
    std::cout << "Translated mask is bv: " << translated_mask.is_bv() << std::endl;
    std::cout << "Translated mask is int: " << translated_mask.is_int() << std::endl;
    std::cout << "Translated vars number: " << bv2int_t.vars().size() << std::endl;
    std::cout << std::endl;
    std::cout << "Translated mask: " << translated_mask << std::endl;
    std::cout << "Translated lemmas:" << std::endl;
    for (auto& lemma : bv2int_t.lemmas()) {
        std::cout << lemma << std::endl;
    }

    // MT_fixedpoint mt_fp(c);
    // std::cout << mt_fp << std::endl;
}

// int main() {
//     z3::context c;

//     sort int_sort = c.int_sort();

//     // Declare variables
//     expr x = c.int_const("x");
//     expr y = c.int_const("y");
//     expr z = c.int_const("z");
//     expr a = c.int_const("a");
//     expr b = c.int_const("b");
//     expr i = c.int_const("i");
//     expr m1 = c.int_val(-7);
//     expr m2 = c.int_val(3);
//     expr zero = c.int_val(0);

//     // mask = a + b
//     // expr mask = a + b;
//     // expr mask = (x < y) + z; //! Incorrect expression
//     expr mask = m1 / m2;

//     std::cout << "Original mask: " << mask << std::endl;
//     for (auto sub_expr : mask) {
//         std::cout << "Sub-expression: " << sub_expr;
//         std::cout << " (is app: " << sub_expr.is_app() << ")" << std::endl;
//     }

//     // Translate using Bv2IntTranslator
//     Int2BvTranslator int2bv_t(c, 4);
//     expr translated_mask = int2bv_t.translate(mask);
//     std::cout << "Translated mask: " << translated_mask << std::endl;
//     std::cout << "Translated mask is of type: " << translated_mask.get_sort() << std::endl;
//     std::cout << "Translated mask is bv: " << translated_mask.is_bv() << std::endl;
//     std::cout << "Translated mask is int: " << translated_mask.is_int() << std::endl;
//     std::cout << "Translated vars number: " << int2bv_t.vars().size() << std::endl;

// }