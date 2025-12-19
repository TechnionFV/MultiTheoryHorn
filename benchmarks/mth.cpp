#include <z3++.h>
#include "multi_theory_fixedpoint.h"

#include <string>
#include <fstream>

using namespace z3;
using namespace multi_theory_horn;

static check_result solve_mth(const std::string& input_path, bool no_preprocess) {
    // TODO: Think how I should construct an MTH that is not yet configured with
    // is_signed, bv_size, int2bv_preprocess, simplify, etc. Will probably need
    // to edit the constructors.
    return z3::unknown;
}

enum ExitCode {
    EXIT_SAT     = 0,
    EXIT_UNSAT   = 1,
    EXIT_UNKNOWN = 2,
    EXIT_ERROR   = 3,
    EXIT_NOTHING = 4
};

struct CLIOptions {
    bool quiet = false;
    bool brunch = false;
    bool no_preprocess = false;
    std::string output_path;
    std::string input_path;
    std::string bench;
};

std::pair<std::string, ExitCode> result_to_string_and_code(check_result cr) {
    switch (cr) {
        case sat:     return {"SAT", EXIT_SAT};
        case unsat:   return {"UNSAT", EXIT_UNSAT};
        case unknown: return {"UNKNOWN", EXIT_UNKNOWN};
    }
    UNREACHABLE();
    return {"ERROR", EXIT_ERROR};
}

static void print_help() {
    OUT() <<
        "Usage:\n"
        "  mth --input <smt_file>\n"
        "Options:\n"
        "  --help           Show this help message\n"
        "  --quiet          Don't print anything\n"
        "  --brunch         Print results in BRUNCH_STAT format (bench, size, result)\n"
        "  --no_preprocess  Don't preprocess int2bv translator inputs\n"
        "  --output <file>  Redirect output to given file\n"
        "\n"
        "Exit codes: 0=SAT, 1=UNSAT, 2=UNKNOWN, 3=error\n";
}

static std::string extract_bench_name_from_path(const std::string& path) {
    // Find the last '/' or '\' character
    size_t last_slash_pos = path.find_last_of("/\\");
    size_t start = (last_slash_pos == std::string::npos) ? 0 : last_slash_pos + 1;

    // Find the last '.' character after the last slash
    size_t last_dot_pos = path.find_last_of('.');
    size_t end = (last_dot_pos == std::string::npos || last_dot_pos < start) ? path.length() : last_dot_pos;

    return path.substr(start, end - start);
}

/// @brief Parses the command-line arguments.
/// @return true if parsing was successful and we should proceed, false otherwise.
static bool parse_cl(int argc, char** argv, CLIOptions& cl_opt, ExitCode& code) {    
    // Parse args
    for (int i = 1; i < argc; ++i) {
        if (std::strcmp(argv[i], "--help") == 0) {
            print_help();
            code = EXIT_NOTHING;
            return false;
        } else if (std::strcmp(argv[i], "--debug") == 0) {
            // hidden dev option
            set_mtfp_debug(true);
        } else if (std::strcmp(argv[i], "--brunch") == 0) {
            cl_opt.brunch = true;
        } else if (std::strcmp(argv[i], "--quiet") == 0) {
            cl_opt.quiet = true;
        } else if (std::strcmp(argv[i], "--output") == 0 && i + 1 < argc) {
            cl_opt.output_path = argv[++i];
        } else if (std::strcmp(argv[i], "--input") == 0 && i + 1 < argc) {
            cl_opt.input_path = argv[++i];
        } else if (std::strcmp(argv[i], "--no_preprocess") == 0) {
            cl_opt.no_preprocess = true;
        }  else {
            OUT() << "error: unknown or malformed argument: " << argv[i] << "\n";
            code = EXIT_ERROR;
            return false;
        }
    }

    if (cl_opt.input_path.empty()) {
        OUT() << "error: missing input argument. Use --input <smt_file>\n";
        code = EXIT_ERROR;
        return false;
    } else {
        // Check if the input path is valid
        std::ifstream ifs(cl_opt.input_path);
        if (!ifs) {
            OUT() << "error: input file '" << cl_opt.input_path << "' does not exist or is not accessible\n";
            code = EXIT_ERROR;
            return false;
        }

        cl_opt.bench = extract_bench_name_from_path(cl_opt.input_path);
    }

    if (cl_opt.brunch && cl_opt.quiet) {
        OUT() << "error: --brunch and --quiet are incompatible\n";
        code = EXIT_ERROR;
        return false;
    }

    // Set up output redirection if requested
    std::ofstream ofs;
    if (!cl_opt.output_path.empty()) {
        ofs.open(cl_opt.output_path);
        if (!ofs) {
            OUT() << "error: failed to open output file '" << cl_opt.output_path << "'\n";
            code = EXIT_ERROR;
            return false;
        }
        // Point the project-wide OUT() at the file
        set_output_stream(ofs);
    }

    return true;
}

int main(int argc, char** argv) {
    CLIOptions cl_opt;
    ExitCode exit_code;
    if (!parse_cl(argc, argv, cl_opt, exit_code)) {
        return exit_code;
    }

    exit_code = EXIT_ERROR;
    try {
        // TODO: Implement a class that parses MTH files and returns
        // an appropriate MT_fixedpoint instance ready to be solved.
        check_result result = solve_mth(cl_opt.input_path, cl_opt.no_preprocess);
        auto [result_str, code] = result_to_string_and_code(result);
        exit_code = code;

        if (cl_opt.brunch) {
            OUT() << "BRUNCH_STAT bench "  << cl_opt.bench      << "\n";
            // TODO: Think if size stat is needed or not
            // OUT() << "BRUNCH_STAT size "   << "<SIZE>"          << "\n";
            OUT() << "BRUNCH_STAT result " << result_str        << "\n";
        } else if (!cl_opt.quiet) {
            OUT() << result_str << " - (Exit code: " << code << ")\n";
        }
    } catch (const std::exception& e) {
        OUT() << "error: exception thrown: " << e.what() << "\n";
        exit_code = EXIT_ERROR;
    } catch (...) {
        OUT() << "error: unknown exception thrown during execution\n";
        exit_code = EXIT_ERROR;
    }

    return exit_code;

    return EXIT_ERROR;
}