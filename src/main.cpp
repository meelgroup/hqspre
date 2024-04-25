// $Id: main.cpp 1174 2016-10-14 06:55:31Z wimmer $

#include <cstdlib>
#include <csignal>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <vector>
#include <set>
#include <iterator>
#include <boost/iostreams/filtering_stream.hpp>
#include <boost/iostreams/copy.hpp>
#include <boost/iostreams/filter/gzip.hpp>
#include <boost/program_options.hpp>
#include "aux.hpp"
#include "formula.hpp"

using namespace hqspre;

std::vector<std::vector<Variable>> computeDCDependencies(Formula& dqbf)
{
    // First minimize the dependencies
    dqbf.applyDependencyScheme(DependencyScheme::GATE, DependencyOperation::REMOVE);
    dqbf.applyDependencyScheme(DependencyScheme::RP_REF_QUADRANGLE, DependencyOperation::REMOVE);

    // Then maximize the dependencies in a copy of the formula
    Formula modified_max = dqbf;
    modified_max.applyDependencyScheme(DependencyScheme::GATE, DependencyOperation::ADD);
    modified_max.applyDependencyScheme(DependencyScheme::RP_REF_QUADRANGLE, DependencyOperation::ADD);

    std::vector<std::vector<Variable>> result(dqbf.maxVarIndex() + 1);
    for (Variable var = dqbf.minVarIndex(); var <= dqbf.maxVarIndex(); ++var) {
        if (!dqbf.isExistential(var)) continue;

        const auto& max_dep = modified_max.getDependencies(var);
        const auto& min_dep = dqbf.getDependencies(var);
        std::set_difference(max_dep.cbegin(), max_dep.cend(), min_dep.cbegin(), min_dep.cend(), std::back_inserter(result[var]));
    }

    return result;
}

void writeFormulaDC(Formula& original, std::ostream& stream)
{
    if (!stream) {
        std::cerr << "[ERROR] Could not write to output stream!" << std::endl;
        std::exit(-1);
    }

    const auto dc_deps = computeDCDependencies(original);

    unsigned int num_dc = 0;
    for (const auto& dcs: dc_deps) num_dc += dcs.size();
    std::cout << "num_dc = " << num_dc << std::endl;

    stream << "p cnf " << original.maxVarIndex() + 1 << " " << original.numClauses() << std::endl;

    // print deleted variables
    stream << "e ";
    for (Variable var = original.minVarIndex(); var <= original.maxVarIndex(); ++var) {
        if (original.varDeleted(var)) stream << var << " ";
    }
    stream << "0\n";

    // print universal variables
    unsigned int num_univ = 0;
    stream << "a ";
    for (Variable var = original.minVarIndex(); var <= original.maxVarIndex(); ++var) {
        if (original.isUniversal(var)) {
            stream << var << " ";
            ++num_univ;
        }
    }
    stream << "0\n";

    // print existential variables which cannot depend on all universals
    std::vector<Variable> skipped_vars;
    for (Variable var = original.minVarIndex(); var <= original.maxVarIndex(); ++var) {
        if (!original.isExistential(var)) continue;
        if (original.numDependencies(var) + dc_deps[var].size() >= num_univ) {
           skipped_vars.push_back(var);
           continue;
        }

        const auto& dep_min = original.getDependencies(var);
        stream << "d " << var << " ";
        std::copy(dep_min.cbegin(), dep_min.cend(), std::ostream_iterator<Variable>(stream, " "));

        for (const Variable dep: dc_deps[var]) stream << "-" << dep << " ";
        stream << "0\n";
    }

    // print existential variable which can depend on all universals.
    if (!skipped_vars.empty()) {
        stream << "e ";
        for (const Variable var: skipped_vars) {
            stream << var << " ";
        }
        stream << "0\n";
    }

    original.writeClauses(stream, nullptr);
}

// We need the processed formula as a global variable.
// Otherwise we cannot access it using signal handlers.
Formula dqbf;


void signalHandler( int signum )
{
    std::cout << "Interrupt signal (" << signum << ") received.\n";
    dqbf.setInterrupt(true);

    // Remove the signal handler.
    std::signal(SIGINT, nullptr);
    std::signal(SIGUSR1, nullptr);
}


int main(int argc, char** argv)
{

    std::cout << "\n\nc This is the HQS Preprocessor for QBF and DQBF, compiled on " << __DATE__ << " at " << __TIME__ << std::endl << std::endl;
#ifndef NDEBUG
    std::cout << "This is the debug version.\n";
#endif

    // Get default values for preprocessor options
    Settings setting = dqbf.getSettings();
    std::string in_name("");
    std::string out_name("");

    // Preprocessing options
    bool preprocessing = true;
    bool compress_output = true;
    unsigned int timeout = 0;
    bool use_limits = true;

    // Declaration of parameters:
    boost::program_options::options_description public_options("Options");
    public_options.add_options()
      ("help,h", "Show available options")
      ("dqbf",      boost::program_options::value<bool>(&setting.force_dqbf),      "Treat the formula always as a DQBF")
      ("v,verbosity",   boost::program_options::value<unsigned int>(&setting.verbosity)->default_value(setting.verbosity),"Set verbosity of the preprocessor")
      ("outfile,o", boost::program_options::value<std::string>(&out_name), "Write the result to the given file")
      ("compress", boost::program_options::value<bool>(&compress_output)->default_value(true), "Rename variables in the output file")
    ;

    boost::program_options::options_description depend_options("Dependency scheme options");
    depend_options.add_options()
	  ("std", "Apply standard dependency scheme")
	  ("sstd", "Apply strict standard dependency scheme")
	  ("tri", "Apply reflexive triangle dependency scheme")
	  ("quad", "Apply reflexive quadrangle dependency scheme")
	  ("gate", "Use gate detection")
	  ("rpath", "Use resolution paths for the dependency scheme")
	  ("add,a", "Add dependencies using the selected dependency scheme")
	  ("remove,r", "Remove dependencies using the selected dependency scheme")
	  ("dc", "Maximize number of don't cares")
	  ;

    boost::program_options::options_description pre_options("Preprocessor options");
    pre_options.add_options()
	  ("preprocess",  boost::program_options::value<bool>(&preprocessing)->default_value(preprocessing), "Enable/disable the preprocessor")
          ("timeout",     boost::program_options::value<unsigned int>(&timeout)->default_value(timeout),  "Set a time limit (0 = none)")
	  ("max_loops",   boost::program_options::value<unsigned int>(&setting.max_loops)->default_value(setting.max_loops), "Set maximal number of preprocessor loops")
	  ("univ_reduct", boost::program_options::value<bool>(&setting.univ_reduction)->default_value(setting.univ_reduction),   "Use universal reduction")
	  ("bce",         boost::program_options::value<unsigned int>(&setting.bce)->default_value(setting.bce),      "Use blocked clause elimination, 0: no, 1: old, 2: new")
	  ("hidden",      boost::program_options::value<unsigned int>(&setting.hidden)->default_value(setting.hidden),   "Add hidden literals before BCE, 0: no, 1: incomplete, 2: complete")
	  ("covered",     boost::program_options::value<bool>(&setting.covered)->default_value(setting.covered),      "Add covered literals before BCE")
	  ("ble",         boost::program_options::value<bool>(&setting.ble)->default_value(setting.ble),   "Use blocked literal elimination for universal literals")
	  ("bla",         boost::program_options::value<bool>(&setting.bla)->default_value(setting.bla),   "Use blocked literal addition for universal literals")
	  ("bia",         boost::program_options::value<bool>(&setting.bia)->default_value(setting.bia),  "Use blocked implication addition")
	  ("max_clause_size", boost::program_options::value<unsigned int>(&setting.max_clause_size)->default_value(setting.max_clause_size), "Maximal size of clause using hidden and covered literals")
	  ("hse",         boost::program_options::value<bool>(&setting.hse)->default_value(setting.hse),           "Use hidden subsumption elimination")
	  ("hec",         boost::program_options::value<bool>(&setting.hec)->default_value(setting.hec),           "Find hidden equivalences and contradictions")
	  ("ic",          boost::program_options::value<bool>(&setting.impl_chains)->default_value(setting.impl_chains),   "Eliminate implication chains")
	  ("contra",      boost::program_options::value<bool>(&setting.contradictions)->default_value(setting.contradictions),        "Find contradictions")
	  ("substitute",  boost::program_options::value<bool>(&setting.substitution)->default_value(setting.substitution),    "Use gate substitution")
	  ("max_substitution_cost", boost::program_options::value<int>(&setting.max_substitution_cost)->default_value(setting.max_substitution_cost), "Maximal substitution costs")
	  ("max_substitution_loops", boost::program_options::value<unsigned int>(&setting.max_substitution_loops)->default_value(setting.max_substitution_loops), "Maximal substitution loops")
	  ("rewrite",     boost::program_options::value<bool>(&setting.rewrite)->default_value(setting.rewrite),      "Use gate rewriting")
	  ("self_sub",    boost::program_options::value<bool>(&setting.self_subsumption)->default_value(setting.self_subsumption),      "Eliminate self-subsuming literals")
	  ("subsumption", boost::program_options::value<bool>(&setting.subsumption)->default_value(setting.subsumption),   "Eliminate subsumed clauses")
	  ("resolution",  boost::program_options::value<bool>(&setting.resolution)->default_value(setting.resolution),    "Eliminate variables by resolution")
          ("max_resolution_cost", boost::program_options::value<int>(&setting.max_resolution_cost)->default_value(setting.max_resolution_cost), "Maximal resolution costs")
	  ("sat_const",   boost::program_options::value<bool>(&setting.sat_const)->default_value(setting.sat_const),     "Detect constants with SAT-based techniques")
	  ("sat_impl",    boost::program_options::value<bool>(&setting.sat_impl)->default_value(setting.sat_impl),      "Detect implications with SAT-based techniques")
          ("univ_exp",    boost::program_options::value<unsigned int>(&setting.univ_expand)->default_value(setting.univ_expand),   "Apply universal expansion")
	  ("incomplete",  boost::program_options::value<bool>(&setting.sat_incomplete)->default_value(setting.sat_incomplete),"Apply incomplete decision procedures")
	  ("cons_check",  boost::program_options::value<bool>(&setting.do_consistency_check)->default_value(setting.do_consistency_check),    "Enable/disable consistency checks in preprocessor")
	  ("use_limits",  boost::program_options::value<bool>(&use_limits)->default_value(use_limits),    "Enable/disable process limits")
	  ("preserve_gates",  boost::program_options::value<bool>(&setting.preserve_gates)->default_value(setting.preserve_gates),    "Enable/disable gates protection")
	  ;

    boost::program_options::options_description hidden_options("Options");
    hidden_options.add_options()
    ("infile,i", boost::program_options::value<std::string>(&in_name), "Input file name")
    ;

    boost::program_options::options_description all_options("All options");
    all_options.add(public_options).add(hidden_options).add(pre_options).add(depend_options);

    boost::program_options::positional_options_description p;
    p.add("infile", -1);

    boost::program_options::variables_map vm;
    boost::program_options::store(boost::program_options::command_line_parser(argc, argv).options(all_options).positional(p).run(), vm);
    boost::program_options::notify(vm);

    // Evaluation of parameters
    if (vm.count("help")) {
        std::cout << "Call with\n  " << argv[0] << "<options> <input file>\n\n" << public_options << "\n" << depend_options << "\n" << pre_options << "\n";
        std::exit(0);
    }

    if (in_name == "") {
        std::cerr << "[ERROR] No input file given." << std::endl;
        std::exit(-1);
    }

    if (vm.count("std") && vm.count("sstd")) {
        std::cerr << "[ERROR] Standard and strict standard dependencies may not be use at the same time." << std::endl;
        std::exit(-1);
    }

    if (vm.count("add") && vm.count("remove")) {
        std::cerr << "[ERROR] Adding and removing dependencies cannot be done at the same time." << std::endl;
        std::exit(-1);
    }

    std::string tag;
    DependencyOperation operation = DependencyOperation::DO_NOTHING;
    if (vm.count("add")) {
        operation = DependencyOperation::ADD;
        tag = "add";
    } else if (vm.count("remove")) {
        operation = DependencyOperation::REMOVE;
        tag = "rem";
    }

    std::signal(SIGINT, signalHandler);

    // Now commit all settings to the solver
    dqbf.setSettings(setting);
    dqbf.useProcessLimits(use_limits);

    std::cout << "c infile = " << in_name << std::endl;
    const std::string ext = in_name.substr(in_name.length() - 3, 3);
    try {
        if (ext == ".gz" || ext == ".GZ") {
            std::ifstream in(in_name, std::ios_base::in | std::ios_base::binary);
            if (!in) {
                std::cerr << "[ERROR] Could not open input file '" << in_name << "'!" << std::endl;
                std::exit(-1);
            }
            boost::iostreams::filtering_istream in_filter;
            in_filter.push(boost::iostreams::gzip_decompressor());
            in_filter.push(in);
            in_filter >> dqbf;
            in.close();
        } else {
            std::ifstream in(in_name);
            if (!in) {
                std::cerr << "[ERROR] Could not open input file '" << in_name << "'!" << std::endl;
                std::exit(-1);
            }
            in >> dqbf;
            in.close();
        }

        if (timeout > 0) createTimeout(timeout, signalHandler);

        val_assert(dqbf.checkConsistency());

        const unsigned int exist_vars = dqbf.numEVars();
        const unsigned int univ_vars = dqbf.numUVars();
        const unsigned int clauses = dqbf.numClauses();
        const unsigned int dependencies = dqbf.numDependencies();
        const unsigned int literals = dqbf.numLiterals();

        if (!vm.count("dc")) {
            std::cout << "c exist_vars_before = " << exist_vars  << std::endl;
            std::cout << "c univ_vars_before = " << univ_vars  << std::endl;
            std::cout << "c literals_before = " << literals << std::endl;
            std::cout << "c clauses_before = " << clauses << std::endl;
        }

        // Apply basic preprocessing.
        if (preprocessing) {
            dqbf.preprocess();
        }


        // If removing dependencies and gate detection is enabled, first detect gates.
        if (vm.count("gate") && operation == DependencyOperation::REMOVE) {
            dqbf.applyDependencyScheme(DependencyScheme::GATE, operation);
            tag += "_gate";
        }

        // Now apply the requested dependency scheme.
        if (vm.count("std") && !vm.count("rpath")) {
            dqbf.applyDependencyScheme(DependencyScheme::STANDARD, operation);
            tag += "_std";
        } else if (vm.count("sstd") && !vm.count("rpath")) {
            dqbf.applyDependencyScheme(DependencyScheme::STRICT_STANDARD, operation);
            tag += "_sstd";
        } else if (vm.count("tri") && !vm.count("rpath")) {
            tag += "_tri";
            dqbf.applyDependencyScheme(DependencyScheme::REF_TRIANGLE, operation);
        } else if (vm.count("quad") && !vm.count("rpath")) {
            tag += "_quad";
            dqbf.applyDependencyScheme(DependencyScheme::REF_QUADRANGLE, operation);
        } else if (vm.count("std")  && vm.count("rpath"))  {
            tag += "_std_rpath";
            dqbf.applyDependencyScheme(DependencyScheme::RP_STANDARD, operation);
        } else if (vm.count("sstd") && vm.count("rpath")) {
            tag += "_sstd_rpath";
            dqbf.applyDependencyScheme(DependencyScheme::RP_STRICT_STANDARD, operation);
        } else if (vm.count("tri") && vm.count("rpath")) {
            tag += "_tri_rpath";
            dqbf.applyDependencyScheme(DependencyScheme::RP_REF_TRIANGLE, operation);
        } else if (vm.count("quad") && vm.count("rpath")) {
            tag += "_quad_rpath";
            dqbf.applyDependencyScheme(DependencyScheme::RP_REF_QUADRANGLE, operation);
        }

        // If adding dependencies is requested and gate detection enabled, add
        // dependencies using gate detection as the last step.
        if (vm.count("gate") && operation == DependencyOperation::ADD) {
            dqbf.applyDependencyScheme(DependencyScheme::GATE, operation);
            tag += "_gate";
        }

        std::signal(SIGINT, nullptr);
        std::signal(SIGUSR1, nullptr);

        // Output some statistics.
        if (!vm.count("dc")) {
            dqbf.printStatistics(std::cout);
            std::cout << std::endl;
            std::cout << "c preprocess -> after / before" << std::endl;
            std::cout << "c exist_vars = " << dqbf.numEVars() << " / " << exist_vars << std::endl;
            std::cout << "c univ_vars  = " << dqbf.numUVars() << " / " << univ_vars << std::endl;
            std::cout << "c literals   = " << dqbf.numLiterals() << " / " << literals << std::endl;
            std::cout << "c clauses    = " << dqbf.numClauses() << " / " << clauses <<  std::endl;
            std::cout << "c dependies  = " << dqbf.numDependencies() << " / " << dependencies << std::endl;
            std::cout << "c maxVarIndex() = " << dqbf.maxVarIndex() << std::endl;
        }

    } catch (UNSATException& e) {
        std::cout << "Preprocessor determined unsatisfiability." << std::endl;

        std::ofstream out;
        if (out_name != "") {
            const std::string ext = out_name.substr(out_name.length() - 3, 3);
            boost::iostreams::filtering_ostream out_filter;
            if (ext == ".gz" || ext == ".GZ") {
                out.open(out_name, std::ios_base::out | std::ios_base::binary);
                if (!out) {
                    std::cerr << "[ERROR] Could not open output file '" << out_name << "'!" << std::endl;
                    std::exit(-1);
                }
                out_filter.push(boost::iostreams::gzip_compressor());
            } else {
                out.open(out_name);
                if (!out) {
                    std::cerr << "[ERROR] Could not open output file '" << out_name << "'!" << std::endl;
                    std::exit(-1);
                }
            }
            out_filter.push(out);
            out_filter << "p cnf 0 1" << std::endl << "0" << std::endl;
        }
        return 20;
    } catch (SATException& e) {
        std::cout << "Preprocessor determined satisfiability." << std::endl;
        std::ofstream out;
        if (out_name != "") {
            const std::string ext = out_name.substr(out_name.length() - 3, 3);
            boost::iostreams::filtering_ostream out_filter;
            if (ext == ".gz" || ext == ".GZ") {
                out.open(out_name, std::ios_base::out | std::ios_base::binary);
                if (!out) {
                    std::cerr << "[ERROR] Could not open output file '" << out_name << "'!" << std::endl;
                    std::exit(-1);
                }
                out_filter.push(boost::iostreams::gzip_compressor());
            } else {
                out.open(out_name);
                if (!out) {
                    std::cerr << "[ERROR] Could not open output file '" << out_name << "'!" << std::endl;
                    std::exit(-1);
                }
            }
            out_filter.push(out);
            out_filter << "p cnf 0 0" << std::endl;
        }
        return 10;
    }

    if (out_name != "") {
        const std::string ext = out_name.substr(out_name.length() - 3, 3);
        if (ext == ".gz" || ext == ".GZ") {
            std::ofstream out(out_name, std::ios_base::out | std::ios_base::binary);
            if (!out) {
                std::cerr << "[ERROR] Could not open output file '" << out_name << "'!" << std::endl;
            std::exit(-1);
            }
            boost::iostreams::filtering_ostream out_filter;
            out_filter.push(boost::iostreams::gzip_compressor());
            out_filter.push(out);
            if (vm.count("dc")) writeFormulaDC(dqbf, out_filter);
            else dqbf.write(out_filter, compress_output);
        } else {
            std::ofstream out(out_name);
            if (!out) {
                std::cerr << "[ERROR] Could not open output file '" << out_name << "'!" << std::endl;
                std::exit(-1);
            }
            if (vm.count("dc")) writeFormulaDC(dqbf, out);
            else dqbf.write(out, compress_output);
        }
    } else if (vm.count("dc") && !vm.count("out_file")) writeFormulaDC(dqbf, std::cout);

    return 0;
}
