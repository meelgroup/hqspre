#include <string>
#include <sstream>
#include <set>
#include <vector>
#include <algorithm>
#include <iostream>
#include <iterator>
#include "aux.hpp"
#include "formula.hpp"

/**
 * \file formula_inout.cpp
 * \brief Implementation of methods and functions for reading and writing formulas.
 * \author Ralf Wimmer
 * \date 01/2016
 */


namespace hqspre {

/**
 * \brief Reads a formula in DQDIMACS format from an input stream
 *
 * If the current formula is not empty, it is cleared first by calling Formula::reset().
 */
void Formula::read(std::istream& stream)
{
    val_assert(prefix != nullptr);

    reset();

    std::string token;
    unsigned int num_vars = 0;
    unsigned int num_clauses = 1;
    unsigned int clauses_read = 0;
    std::set<Variable> universal_vars;
    std::vector<Variable> var_map;

    while (!stream.eof()) {
        stream >> token;

        if (token == "p") {
            // header
            std::string s;
            stream >> s; // cnf
            stream >> num_vars;
            stream >> num_clauses;
            var_map.resize(num_vars + 1, 0);
            clauses.reserve(num_clauses + 1);
            setMaxVarIndex(num_vars);
        } else if (token == "a") {
            // list of universally quantified variables
            while (stream) {
                Variable var = 0;
                stream >> var;
                if (var == 0) break;
                val_assert(var <= maxVarIndex());
                var_map[var] = addUVar();
                universal_vars.insert(var_map[var]);
            }
        } else if (token == "e") {
            // existential variable depending on all universal vars 
            // declared so far.
            Variable exist_var = 0;
            while (stream) {
                stream >> exist_var;
                if (exist_var == 0) break;
                val_assert(exist_var <= maxVarIndex());
                if (prefix->type() == PrefixType::DQBF) {
                    var_map[exist_var] = addEVar(universal_vars);
                } else {
                    var_map[exist_var] = addEVar();
                }
            }
        } else if (token == "d") {
            // If we have a QBF prefix and encounter a "d"-line,
            // we have to switch to DQBF.
            if (prefix->type() == PrefixType::QBF) {
                if (setting.verbosity > 1) {
                    std::cout << "Switching to DQBF prefix representation\n";
                }
                dqbf_prefix = qbf_prefix->convertToDQBF();
                delete prefix;
                prefix = dqbf_prefix;
                qbf_prefix = nullptr;
            }
            // existential variable with dependencies
            Variable exist_var = 0;
            Variable all_var = 0;

            stream >> exist_var;
            val_assert(exist_var <= maxVarIndex());

            std::set<Variable> deps;
            while (stream) {
                stream >> all_var;
                if (all_var == 0) break;
                deps.insert(var_map[all_var]);
            }
            var_map[exist_var] = addEVar(deps);
        } else if (token == "c") {
            std::getline(stream, token); // consume the rest of the line
        } else {
            // clause
            std::vector<Literal> clause;
            int lit = atoi(token.c_str());
            do {
                if (lit == 0) break;
                const Variable var = var_map[abs(lit)];
                clause.push_back(var2lit(var, lit < 0));
                stream >> lit;
            } while (stream);
            addClause(std::move(clause));
            ++clauses_read;
            if (clauses_read == num_clauses) break;
        }
    }

    // Check if we can switch from DQBF to QBF
    if (!setting.force_dqbf && prefix->type() == PrefixType::DQBF && isQBF()) {
        val_assert(qbf_prefix == nullptr && dqbf_prefix != nullptr);
        if (setting.verbosity > 1) {
            std::cout << "Switching to QBF prefix representation.\n";
        }
        qbf_prefix = dqbf_prefix->convertToQBF();
        delete dqbf_prefix;
        dqbf_prefix = nullptr;
        prefix = qbf_prefix;
    }
}


/**
 * \brief Writes the current formula in DQDIMACS format to the given output stream.
 *
 * If the formula is a QBF, then the output file is actually in QDIMACS format.
 * \param stream output stream to which the formula should be written
 * \param compact rename the variables such that there are no deleted variables in between
 */
void Formula::write(std::ostream& stream, bool compact) const
{
    val_assert(prefix != nullptr);

    if (!stream) {
        std::cerr << "[ERROR] Could not write to output stream!" << std::endl;
        std::exit(-1);
    }

    const_cast<Formula*>(this)->updateVars();
    val_assert(checkConsistency());

    std::vector<Variable> translation_table(maxVarIndex() + 1, 0);
    Variable current = 0;
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (varDeleted(var)) continue;
        if (compact) { translation_table[var] = ++current; }
        else translation_table[var] = var;
    }

    // If necessary, print the translation table
    if (compact) {
        for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
            if (!varDeleted(var)) {
                stream << "c ren " << var << " -> " << translation_table[var] << std::endl;
            }
        }
    }
    // print the header
    stream << "p cnf " << (compact ? current : maxVarIndex()) << " " << numClauses() << std::endl;
    prefix->write(stream, &translation_table);
    writeClauses(stream, &translation_table);

}

/**
 * \brief Print all clauses in DIMACS format to the given stream.
 */
void Formula::writeClauses(std::ostream& stream, std::vector<Variable>* translation_table) const
{
    auto trans = [translation_table](Literal lit) {
        if (translation_table == nullptr) return lit;
        else return var2lit((*translation_table)[lit2var(lit)], isNegative(lit));
    };

    // Print the clauses.
    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        for (const Literal lit: clauses[c_nr]) {
		  stream << lit2dimacs(trans(lit)) << " ";
        }
        stream << "0\n";
    }

    for (Literal lit: unit_stack) {
        stream << lit2dimacs(lit) << " 0" << std::endl;
    }
}


std::ostream& operator<<(std::ostream& stream, const Formula& formula)
{
    formula.write(stream);
    return stream;
}


std::istream& operator>>(std::istream& stream, Formula& formula)
{
    formula.read(stream);
    return stream;
}


} // end namespace hqspre
