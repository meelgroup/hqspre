#include <vector>
#include <algorithm>
#include <iostream>
#include "formula.hpp"
#include "bool_vector.hpp"
#include "aux.hpp"

/**
 * \file formula_unit_pure.cpp
 * \brief Implementation of unit propagation and pure literal detection
 * \author Ralf Wimmer
 * \date 02/2016
 */

namespace hqspre {

/**
 * \brief Puts a literal onto the unit stack.
 *
 * If the same literal has already been with assigned opposite sign, an
 * UNSATException is thrown.
 *
 * \param lit the unit literal
 * \param allow_universal If false, a universal unit literals leads to an
 *        UNSATException. However, for universal pure literals this is not
 *        correct. In this case, the parameter can be set to true.
 * \throw UNSATException if a universal unit literal is added and allow_universal is false.
 * \throw UNSATException if the same unit literal just with opposite sign has beed added before.
 */
void Formula::pushUnit(Literal lit, bool allow_universal)
{
    if (!allow_universal && isUniversal(lit2var(lit))) throw UNSATException("Universal literal is unit.", this);

    if ( (isNegative(lit) && assignment[lit2var(lit)] == TruthValue::TRUE)
         || (isPositive(lit) && assignment[lit2var(lit)] == TruthValue::FALSE)) {
        throw UNSATException("Contradicting unit literals", this);
    }

    unit_stack.push_back(lit);
    assignment[lit2var(lit)] = (isNegative(lit) ? TruthValue::FALSE : TruthValue::TRUE);
    ++stat_unit_pure;
}


/**
 * \brief Processes unit clauses until none is left.
 *
 * Satisfied clauses are deleted, the negated unit literal is
 * removed from all clauses in which it appears, potentially leading
 * to new unit clauses. This is iterated until the formula does not
 * change anymore.
 * \return true iff the formula was modified.
 * \throws UNSATException if unitPropagation() determins a conflict.
 */
bool Formula::unitPropagation()
{
    if (unit_stack.empty()) return false;

    unsigned int count = 0;

    // Process all variables on the 'unit_stack'.
    while (!unit_stack.empty()) {
        const Literal top_lit = unit_stack.back();
        unit_stack.pop_back();
        const Literal neg_top_lit = negate(top_lit);
        const Variable top_var = lit2var(top_lit);
        if (varDeleted(top_var)) continue;

        if (setting.verbosity > 2) {
            std::cout << "c " << __FUNCTION__ << "(): " << lit2dimacs(top_lit)
                      << "(" << (isExistential(lit2var(top_lit))?"E":"U") << ") is unit.\n";
        }

        // Delete all clauses in which 'top_lit' occurs
        while (!occ_list[top_lit].empty()) {
            const unsigned int c_nr = occ_list[top_lit].front();
            val_assert(!clauseDeleted(c_nr));
            // check for new pures after deletion of the clause
            checkPure(clauses[c_nr], top_lit);
            removeClause(c_nr);
        }
        val_assert(occ_list[top_lit].empty());

        // Delete ~top_lit from all clauses where it occurs
        // If the clause is binary, it becomes unit -> call pushUnit()
        // If the clause is ternary, it becomes binary and we must
        //   update the implications.

        // Because 'removeClause(c_nr)' modifies occ_list,
        // we may not simply iterate over it to delete the
        // satisfied clauses.
        std::vector<unsigned int> to_be_removed;
        for (unsigned int c_nr: occ_list[neg_top_lit]) {
            val_assert(!clauseDeleted(c_nr));
            clause_modified[c_nr] = true;
            auto& c = clauses[c_nr];
            // binary clauses become unit
            if (c.size() == 2) {
                if (c[0] == neg_top_lit) pushUnit(c[1]);
                else pushUnit(c[0]);
                to_be_removed.push_back(c_nr);
            } else {
                removeLiteral(c_nr, neg_top_lit);
            }
        }
        for (const unsigned int c_nr: to_be_removed) {
            removeClause(c_nr);
        }
        occ_list[neg_top_lit].clear();

        // now clear implications of propagates lit
        implications[top_lit].clear();
        implications[neg_top_lit].clear();

        // remove variable
        removeVar(top_var);
        ++count;
    }

    if (setting.verbosity > 2 && count > 0) {
        std::cout << "c " << __FUNCTION__ << " removed " << count << " unit and pure literals.\n";
    }

    return count > 0;
}

/**
 * \brief Searches for pure literals and eliminates them.
 *
 * A literal is pure if it appears in the whole formula only in one polarity.
 * Existential pure literals can be set to true, universal pure literals to false.
 * This is done by calling pushUnit (setting allow_universal to true).
 * \throw UNSATException if propagating the pure literals leads to a conflict.
 * \return true if the formula was modified.
 */
bool Formula::findPure()
{
    val_assert_msg(unit_stack.empty(), "You must call Formula::unitPropagation() first!");
    const unsigned int old_stat_unit_pure = stat_unit_pure;
    bool again = true;

    while (again) {
        again = false;

        for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit) {
            if (occ_list[lit].empty() && !occ_list[negate(lit)].empty()) {
                // literal 'lit' is pure
                if (setting.verbosity > 2) {
                    std::cout << "c " << __FUNCTION__ << "() " << lit2dimacs(negate(lit)) << " is pure" << std::endl;
                }

                if (isExistential(lit2var(lit))) {
                    pushUnit(negate(lit), true);
                    again = true;
                    unitPropagation();
                } else if (isUniversal(lit2var(lit))) {
                    pushUnit(lit, true);
                    again = true;
                    unitPropagation();
                }
            } else if (setting.impl_chains) {
                checkImplicationChain(lit);
            }
        }
    }

    return (stat_unit_pure > old_stat_unit_pure);
}


/**
 * \brief Checks whether a literal is pure if one additional clause where
 * lit appears positively would be deleted
 *
 * This method is used in formula_bce for a quick check whether a literal 
 * is pure after a blocked clause is eliminated
 *
 * \return true if literal would be pure
 */
bool Formula::checkPure(Literal lit) const
{
    return ((occ_list[lit].size() == 1) && !occ_list[negate(lit)].empty());
}


/**
 * \brief Checks whether there will be new pure literals after "clause" is deleted
 *
 * Checks every literal in clause except the "except_lit"
 */
void Formula::checkPure(const Clause& clause, Literal except_lit)
{
    for (Literal lit : clause ) {
        if (lit != except_lit && assignment[lit2var(lit)] == TruthValue::UNKNOWN && checkPure(lit)) {
            if (isExistential(lit2var(lit))) {
                pushUnit(negate(lit), true);
            } else {
                pushUnit(lit, true);
            }
        }
    }
}

} // end namespace hqspre
