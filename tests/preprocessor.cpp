#include <iostream>
#include <vector>
#include <cstring>
#include <z3++.h>
#include "Int2BvPreprocessor.h"

using namespace z3;
using namespace multi_theory_horn;

int verbose = 0;

// ANSI color codes
constexpr const char* RED   = "\033[31m";
constexpr const char* GREEN = "\033[32m";
constexpr const char* RESET = "\033[0m";

// Generic function to check equivalence of two expressions
void check_equivalent(context& c, const expr& pre, const expr& wanted, const std::string& test_name = "") {
    solver s(c);
    s.add(pre != wanted);

    if (!test_name.empty()) std::cout << "Test: " << test_name << std::endl;

    if (s.check() == unsat) {
        std::cout << GREEN << "[PASS]" << RESET << " Expressions are EQUIVALENT." << std::endl;
        if (verbose) {
            std::cout << "Preprocessed:\n" << pre << std::endl;
            std::cout << "Wanted:\n" << wanted << std::endl;
        }
    } else {
        std::cout << RED << "[FAIL]" << RESET << " Expressions are NOT EQUIVALENT." << std::endl;
        std::cout << "Preprocessed:\n" << pre << std::endl;
        std::cout << "Wanted:\n" << wanted << std::endl;

        model m = s.get_model();
        std::cout << "Counterexample:" << std::endl;
        for (unsigned i = 0; i < m.size(); ++i) {
            func_decl v = m[i];
            std::cout << "  " << v.name() << " = " << m.get_const_interp(v) << std::endl;
        }
    }

    std::cout << "========================================" << std::endl;
}

// Struct to define a test case
struct SATOutOfBoundsTest {
    expr input;
    expr expected;
    std::string name;
};


struct UNSATOutOfBoundsTest {
    expr input;
    expr expected;
    std::string name;
};

// Run a batch of SATOutOfBounds tests
void run_SATOutOfBounds_tests(context& c, Int2BvPreprocessor& preprocessor,
                              const std::string& bench_name,
                              const std::vector<SATOutOfBoundsTest>& tests) 
{
    for (size_t i = 0; i < tests.size(); ++i) {
        const auto& test = tests[i];
        std::string full_name = bench_name + " Test " + std::to_string(i+1) + ": " + test.name;

        expr preprocessed = preprocessor.create_SAT_out_of_bounds(test.input);
        check_equivalent(c, preprocessed, test.expected, full_name);
        preprocessor.reset(); // Reset preprocessor for next test
    }
}

void run_UNSATOutOfBounds_tests(context& c, Int2BvPreprocessor& preprocessor,
                                const std::string& bench_name,
                                const std::vector<UNSATOutOfBoundsTest>& tests) 
{
    for (size_t i = 0; i < tests.size(); ++i) {
        const auto& test = tests[i];
        std::string full_name = bench_name + " Test " + std::to_string(i+1) + ": " + test.name;

        expr preprocessed = preprocessor.create_UNSAT_out_of_bounds(test.input);
        check_equivalent(c, preprocessed, test.expected, full_name);
        preprocessor.reset(); // Reset preprocessor for next test
    }
}

int main(int argc, char* argv[]) {
    // Parse command line arguments
    verbose = 0;
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "--verbose") == 0 || std::strcmp(argv[i], "-v") == 0) {
            verbose = 1;
        }
    }

    context c;
    expr x = c.int_const("x");
    expr y = c.int_const("y");

    // TODO: Test also the signed case
    Int2BvPreprocessor preprocessor(c, 4, false);

    // SATOutOfBounds tests
    // expr, wanted, name
    std::vector<SATOutOfBoundsTest> sat_tests = {
        { x < (y + 1), (x >= 0) && (x <= 15) && (y == 15), "x < y + 1" },
        { (x <= y - 1) || (x >= y + 1), c.bool_val(false), "x <= y - 1 || x >= y + 1" }
    };

    run_SATOutOfBounds_tests(c, preprocessor, "[SATOutOfBounds]", sat_tests);

    std::vector<UNSATOutOfBoundsTest> unsat_tests = {
        { x < (y + 1), c.bool_val(false), "x < y + 1" },
        { (x <= y - 1) || (x >= y + 1), (x == 0 && y == 0) || (x == 15 && y == 15), "x <= y - 1 || x >= y + 1" }
    };

    run_UNSATOutOfBounds_tests(c, preprocessor, "[UNSATOutOfBounds]", unsat_tests);

    return 0;
}
