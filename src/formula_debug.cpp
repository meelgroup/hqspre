#include <algorithm>
#include <iostream>
#include "formula.hpp"

/**
 * \file formula_debug.cpp
 * \brief Functions for debugging formula operations
 * \author Ralf Wimmer
 * \date 2016
 */


namespace hqspre {

/**
 * \brief Check if the formula is in a consistent state.
 * \return true if no inconsistencies could be detected.
 *
 * Executed checks:
 * - the cached number of existential and universal variables is correct
 * - all deleted clauses are empty
 * - all available clause numbers (Formula::deleted_clause_numbers)
 *   correspond to deleted clauses.
 * - if \f$x\in D_y\f$ then \f$y\in D_x\f$ and vice versa.
 * - if \f$(a,b)\f$ is a binary clause, we have the implications
 *   \f$\neg a\rightarrow b\f$ and \f$\neg b\rightarrow a\f$.
 * - If c_nr occurs in an occurrence list, then clause c_nr is not
 *   deleted and contains the corresponding literal.
 */
bool Formula::checkConsistency() const
{
    if (!setting.do_consistency_check) return true;

    if (setting.verbosity > 3 ) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    // Check the prefix
    if (prefix == nullptr) {
        std::cerr << "[ERROR] Prefix is null.\n";
        return false;
    }

    if (prefix->type() == PrefixType::QBF && qbf_prefix == nullptr) {
        std::cerr << "[ERROR] Prefix is a QBF prefix, but qbf_prefix is null\n";
        return false;
    }

    if (prefix->type() == PrefixType::DQBF && dqbf_prefix == nullptr) {
        std::cerr << "[ERROR] Prefix is a DQBF prefix, but dqbf_prefix is null\n";
        return false;
    }

    if (qbf_prefix != nullptr && dqbf_prefix != nullptr) {
        std::cerr << "[ERROR] Both qbf_prefix and dqbf_prefix are in use.\n";
        return false;
    }

    if (!prefix->checkConsistency()) return false;

    for (Variable var: deleted_var_numbers) {
        if (!varDeleted(var)) {
            std::cerr << "[ERROR] Variable marked as deleted by is not.\n";
            return false;
        }
    }

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        if (!clauses[c_nr].checkConsistency()) return false;
    }

    // Clauses do not contain deleted variables
    for (const auto& clause: clauses) {
        for (const Literal lit: clause) {
            if (varDeleted(lit2var(lit))) {
                std::cerr << "[ERROR] Clause contains a deleted variable (var = " << lit2var(lit) << ")" << std::endl;
                return false;
            }
        }
    }

    // Implications do not contain deleted variables
    for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit) {
        const Variable var = lit2var(lit);
        if (varDeleted(var) && !implications[lit].empty()) {
            std::cerr << "[ERROR] Implication list of deleted literal " << lit2dimacs(lit) << " is not empty." << std::endl;
            return false;
        }

        for (BinaryClause impl: implications[lit]) {
            Literal literal = impl.getLiteral();
            if (varDeleted(lit2var(literal))) {
                std::cerr << "[ERROR] Literal " << lit2dimacs(literal) << " is implied, but deleted." << std::endl;
                return false;
            }
        }
    }

    // All deleted clauses are empty
    for (unsigned int c_nr: deleted_clause_numbers) {
        if (!clauses[c_nr].empty()) {
            std::cerr << "[ERROR] Clause " << c_nr << " is deleted, but not empty.\n";
            return false;
        }
        if (!clauseDeleted(c_nr)) {
            std::cerr << "[ERROR] Clause number " << c_nr << " is available but clause not deleted.\n";
            return false;
        }
    }


    // Consistency of implications
    for (Literal a = minLitIndex(); a <= maxLitIndex(); ++a) {
        for (BinaryClause bclause: implications[a]) {
            const Literal b = bclause.getLiteral();
            if (implications[negate(b)].find(negate(a)) == implications[negate(b)].cend()) {
                std::cerr << "[ERROR]" << lit2dimacs(a) << " implies " << lit2dimacs(b) << ", but " << lit2dimacs(negate(b))
                          << " does not imply " << lit2dimacs(negate(a)) << ".\n";
                return false;
            }
        }
    }

    // Consistency of occurrence lists
    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;

        for (Literal lit: clauses[c_nr]) {
            if (std::find(occ_list[lit].cbegin(), occ_list[lit].cend(), c_nr) == occ_list[lit].cend()) {
                std::cerr << "[ERROR] Literal " << lit2dimacs(lit) << " appears in clause #" << c_nr
                          << ", but " << c_nr << " not in occ_list[" << lit << "].\n";
                return false;
            }
        }
    }
    for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit) {
        for (unsigned int c_nr: occ_list[lit]) {
            if (clauseDeleted(c_nr)) {
                std::cerr << "[ERROR] Deleted clause #" << c_nr << " appears in the occurrence list of literal " << lit2dimacs(lit) << ".\n";
                return false;
            }
            if (std::find(clauses[c_nr].cbegin(), clauses[c_nr].cend(), lit) == clauses[c_nr].cend()) {
                std::cerr << "[ERROR] Clause #" << c_nr << " appears in the occurrence list of literal " << lit2dimacs(lit)
                          << ", but the literal not in the clause.\n";
                return false;
            }
        }
    }

    // The _seen vector has to be cleared
    for (bool b: _seen) {
        if (b) {
            std::cerr << "[ERROR] Seen vector is not cleared.\n";
            return false;
        }
    }
    return true;
}


bool Formula::checkSeen() const
{
    bool error = false;
    for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit) {
        if (_seen[lit]) {
            std::cout << lit2dimacs(lit) << " is already seen" << std::endl;
            error = true;
        }
    }
    val_assert(!error);
    return error;
}


Literal Formula::getAssignment(Literal lit) const
{
    if (assignment[lit2var(lit)] == TruthValue::TRUE) {
        return lit;
    } else if (assignment[lit2var(lit)] == TruthValue::FALSE) {
        return negate(lit);
    } else {
        return 0;
    }
}


void Formula::printFullOccurenceList(Variable var, std::ostream& stream) const
{
    assert(var <= maxVarIndex());
    printOccurenceList(var2lit(var), stream);
    printOccurenceList(negate(var2lit(var)), stream);
}


void Formula::printOccurenceList(Literal lit, std::ostream& stream) const
{
    assert(lit <= maxLitIndex());
    stream << "occurrences of " << lit2dimacs(lit) << " (" << occ_list[lit].size() << " entries) :" << std::endl;
    for (unsigned int cl_nr : occ_list[lit] ) {
        stream << "#" << cl_nr << ": " << clauses[cl_nr] << std::endl;
    }
}


void Formula::printImplications(Literal lit, std::ostream& stream) const
{
    assert(lit <= maxLitIndex());
    stream << "implications of " << lit2dimacs(lit) << " (" << implications[lit].size() << ") :" << std::endl;
    stream << lit2dimacs(lit) << " => ";
    for (BinaryClause cl : implications[lit] ) {
        stream << lit2dimacs(cl.getLiteral()) << " ";
    }
    stream << std::endl;
}


void Formula::printAllClauses(bool print_implications, std::ostream& stream) const
{
    stream << "clause database:" << std::endl;
    for (unsigned int i = 0; i != clauses.size(); ++i) {
        if (clauseDeleted(i) ) continue;
        stream << (i+1) << ": " << clauses[i] << std::endl;
    }

    if (print_implications) {
        stream << "clause implications: " << std::endl;
        for (Literal l = minLitIndex(); l <= maxLitIndex(); ++l) {
             printImplications(l, stream);
        }
    }
}

} // end namespace hqspre
