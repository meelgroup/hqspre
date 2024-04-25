#ifndef HQSPRE_FORMULA_BLOCKED_ET_AL_IPP_
#define HQSPRE_FORMULA_BLOCKED_ET_AL_IPP_

/**
 * \file formula_blocked_et_al.ipp
 * \brief Implementation of template functions for blocked clause elimination
 * \author Ralf Wimmer
 * \date 02/2016
 */

namespace hqspre {

/**
 * \brief Check if the given clause is blocked.
 * \param current_clause the clause that is to be checked.
 * \return the blocking lit if the clause is blocked, otherwise 0
 * \pre The clause needs to be sorted and may not contain duplicate literals.
 * \pre Assumes that "_seen" vector was initialized with current_clause
 * \note The clause does not need to be contained in the formula.
 */
template <typename Container>
Literal Formula::clauseBlocked(const Container& current_clause) const
{
    for (Literal blocking_lit: current_clause)
    {
        if (isUniversal(lit2var(blocking_lit))) continue;

        if (clauseBlockedByLit(blocking_lit)) {
            return blocking_lit;
        }
    }
    return 0;
}


/**
 * \brief Check if the given clause is blocked by given lit.
 * \param current_clause the clause that is to be checked.
 * \param lit the lit for which blocking status is currently checked.
 * \return true if the clause is blocked.
 * \pre Assumes that "_seen" vector was initialized with corresponding clause
 * \note The clause does not need to be contained in the formula.
 * \note The clause does not to be sorted
 */
inline bool Formula::clauseBlockedByLit(const Literal blocking_lit) const
{
    const Variable blocking_var = lit2var(blocking_lit);
    const Literal neg_lit = negate(blocking_lit);

    for (const unsigned int other_c_nr: occ_list[neg_lit])
    {
        val_assert(!clauseDeleted(other_c_nr));

        const Clause& other_clause = clauses[other_c_nr];

        process_limit.decreaseLimitBy(2, other_clause.size());

        bool tautology = false;
        // Now check for every other literal in other_clause, whether we gain an tautology
        for (Literal lit : other_clause) {
            // "clause" contains a negated lit -> resolvent is potential tautology
            if ( _seen[negate(lit)] && lit2var(lit) != blocking_var) {
                // check for correct dependencies
                if (dependenciesSubset(lit2var(lit), blocking_var)) {
                    tautology = true;
                    break;
                }
            }
        }

        // If at least one resolvent does not become a tautology, "clause" is not blocked
        if (!tautology) {
            return false;
        }
    } // end for (other_clause)
    return true;
}


} // end namespace hqspre

#endif
