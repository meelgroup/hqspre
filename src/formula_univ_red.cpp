#include <algorithm>
#include <set>
#include <vector>
#include <iostream>
#include "formula.hpp"

/**
 * \file formula_univ_red.cpp
 * \brief Implementation of universal reduction
 * \author Ralf Wimmer
 * \date 02/2016
 */

namespace hqspre {

/**
 * \brief Performs universal reduction on a single clause.
 *
 * Universal reduction removes a universal literal \f$u\f$ from
 * a clause \f$C\f$ if \f$C\f$ does not contain any existential literal
 * which depends on \f$u\f$.
 * \param clause the clause that is to be reduced
 * \param c_nr the ID of the clause, if the clause is already in the database, and -1 otherwise.
 * \return true if the clause was modified
 * \throws UNSATException if universal reduction yields the empty clause (and `c_nr` is not negative)
 */
bool Formula::universalReduction(Clause& clause, int c_nr)
{
    val_assert(prefix != nullptr);
    removed_lits.clear();
    ScopeTimer univ_red(univ_reduction_time);

    if (prefix->type() == PrefixType::QBF) {
        val_assert(qbf_prefix != nullptr && dqbf_prefix == nullptr);

        // For QBF, determine the maximal existential level in the clause
        int max_level = -1;
        for (const Literal lit: clause)
        {
            if (isExistential(lit2var(lit))) {
                max_level = std::max(max_level, (int)qbf_prefix->getLevel(lit2var(lit)));
            }
        }

        // Perform the reduction: all universal literals with a higher level
        // than 'max_level' can be removed.
        unsigned int next_free = 0;
        for (unsigned int curr_index = 0; curr_index < clause.size(); ++curr_index) {
            const Variable var = lit2var(clause[curr_index]);
            if (isExistential(var) || (int)qbf_prefix->getLevel(var) <= max_level) {
                // clause[curr_index] cannot be deleted
                if (next_free != curr_index) {
                    clause[next_free] = clause[curr_index];
                }
                ++next_free;
            } else {
                removed_lits.push_back(clause[curr_index]);
            }
        }

        // If necessary, shrink the clause and update the occurrence/implication lists
        if (!removed_lits.empty()) {
            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "() removed " << removed_lits.size() << " literal(s) from clause " << clause << " of length " << clause.size() << std::endl;
            }
            if (c_nr >= 0) {
                clause_modified[c_nr] = true;
                if (clause.size() == 2) {
                    // remove implications
                    if (removed_lits.size() == 2) {
                        removeImplication(negate(removed_lits[0]), removed_lits[1]);
                        removeImplication(negate(removed_lits[1]), removed_lits[0]);
                    } else {
                        removeImplication(negate(clause[0]), removed_lits[0]);
                        removeImplication(negate(removed_lits[0]), clause[0]);
                    }
                }
                // update occurrence lists
                for (const Literal lit: removed_lits) {
                    removeFromOccList(lit, c_nr);
                }
                clause_sizes[c_nr] = next_free;
            }

            clause.resize(next_free);
            clause.computeSignature();

            if (c_nr >= 0) {
                // Check for unit clauses and implications
                if (clause.empty()) throw UNSATException("Universal reduction created an empty clause.", this);
                else if (clause.size() == 1) {
                    const Literal unit = clause[0];
                    removeClause(c_nr);
                    pushUnit(unit);
                } else if (clause.size() == 2) {
                    addImplication(negate(clause[0]), clause[1], c_nr);
                    addImplication(negate(clause[1]), clause[0], c_nr);
                }
            }
            stat_univ_reduction += removed_lits.size();
            return true;
        } else return false;

    } else {
        // formula is a DQBF
        val_assert(prefix->type() == PrefixType::DQBF && dqbf_prefix != nullptr);

        const unsigned int num_univ = numUVars();

        // If all literals are existential, we can skip the clause
        if (std::all_of(clause.cbegin(), clause.cend(),
                [this](Literal lit) { return isExistential(lit2var(lit));}
        )) return false;

        if (std::any_of(clause.cbegin(), clause.cend(),
                [this](Literal lit) { return dqbf_prefix->inRMB(lit2var(lit)); }
        )) return false;

        // Compute the union of the dependency sets of all existential variables
        // in the clause.
        std::set<Variable> dependencies;
        for (const Literal lit: clause) {
            const Variable var = lit2var(lit);
            if (isExistential(var)) fast_set_union(dqbf_prefix->getDependencies(var), dependencies);
            if (dependencies.size() == num_univ) return false;
        }

        // Perform the reduction
        unsigned int next_free = 0;
        for (unsigned int curr_index = 0; curr_index < clause.size(); ++curr_index) {
            const Variable var = lit2var(clause[curr_index]);
            if (isExistential(var) || dependencies.find(var) != dependencies.cend()) {
                // clause[curr_index] cannot be deleted
                if (next_free != curr_index) {
                    clause[next_free] = clause[curr_index];
                }
                ++next_free;
            } else {
                val_assert(isUniversal(lit2var(clause[curr_index])));
                removed_lits.push_back(clause[curr_index]);
            }
        }

        if (next_free == 0) {
            throw UNSATException("Universal reduction created an empty clause.", this);
            return true;
        }

        // If necessary, shrink the clause
        if (!removed_lits.empty()) {
            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "() removed " << removed_lits.size() << " literal(s) from clause " << clause << " of length " << clause.size() << std::endl;
            }
            if (c_nr >= 0) {
                clause_modified[c_nr] = true;
                if (clause.size() == 2) {
                    // remove implications
                    if (removed_lits.size() == 2) {
                        removeImplication(negate(removed_lits[0]), removed_lits[1]);
                        removeImplication(negate(removed_lits[1]), removed_lits[0]);
                    } else {
                        removeImplication(negate(clause[0]), removed_lits[0]);
                        removeImplication(negate(removed_lits[0]), clause[0]);
                    }
                }
                // update occurrence lists
                for (const Literal lit: removed_lits) {
                    removeFromOccList(lit, c_nr);
                }
                clause_sizes[c_nr] = next_free;
            }
            clause.resize(next_free);
            clause.computeSignature();
            stat_univ_reduction += removed_lits.size();

            if (c_nr >= 0) {
                // Check for unit clauses and implications
                if (clause.empty()) {
                    throw UNSATException("Universal reduction created an empty clause.", this);
                    return true;
                } else if (clause.size() == 1) {
                    pushUnit(clause[0]);
                    removeClause(c_nr);
                } else if (clause.size() == 2) {
                    addImplication(negate(clause[0]), clause[1], c_nr);
                    addImplication(negate(clause[1]), clause[0], c_nr);
                }
            }
            return true;
        } else return false;
    }
    return false;
}



/**
 * \brief Performs universal reduction on the whole formula.
 *
 * Universal reduction removes a universal literal \f$u\f$ from
 * a clause \f$C\f$ if \f$C\f$ does not contain any existential literal
 * which depends on \f$u\f$.
 * \return true if the formula was modified
 * \throws UNSATException if universal reduction yields the empty clause
 */
bool Formula::universalReduction()
{
    val_assert(prefix != nullptr);

    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    bool modified = false;

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        if (universalReduction(clauses[c_nr], c_nr)) modified = true;
    }

    return modified;
}


} // end namespace hqspre
