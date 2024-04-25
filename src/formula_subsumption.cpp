#include <vector>
#include <algorithm>
#include <map>
#include <limits>
#include <iostream>
#include "formula.hpp"

/**
 * \file formula_subsumption.cpp
 * \brief Subsumption checking
 * \author Ralf Wimmer
 * \date 02/2016
 */

//#define COMPLETE_FORWARDSUB

namespace hqspre {

/**
 * \brief Finds and removes all clauses that are subsumed by `short_clause`
 *
 * If the formula contains clauses \f$C\f$ and \f$C'\f$ such that
 * \f$C\subseteq C'\f$, then \f$C'\f$ can be deleted. The result is
 * a logically equivalent formula.
 *
 * This function checks if `short_clause` subsumes any of the formula's clauses.
 * All subsumed clauses are deleted. If `short_clause` is already part of the
 * formula, we have to take care that we do not delete it as each clause is a
 * subset of itself. To avoid this, the parameter `c_nr` is the clause ID if
 * `short_clause` is contained in the formula (otherwise set `c_nr` to a negative value).
 *
 * \param short_clause the clause for which we check if it subsumes any other clause
 * \param c_nr the ID of `short_clause` if it is part of the formula, -1 otherwise
 * \return the number of deleted clauses
 * \sa Formula::binarySubsumption()
 * \sa Formula::narySubsumption()
 */
unsigned int Formula::isBackwardSubsuming(const Clause& short_clause, int c_nr)
{
    val_assert(!short_clause.empty());

    // determine a literal which appears in the fewest clauses
    std::vector<std::size_t> subsumed;
    const Literal min_lit = getSubsumerCandidate(short_clause);

    // Mark every literal in short_clause
    setSeen2(short_clause);

    const auto short_clause_size = short_clause.size();

    for (unsigned int other_c_nr: occ_list[min_lit]) {
        if (c_nr == static_cast<int>(other_c_nr)) continue;

        const Clause& other_clause = clauses[other_c_nr];

        // If short clause is longer, it cannot subsume the other one
        if (short_clause.size() > other_clause.size()) continue;
        // Check matching signatures
        if ((short_clause.getSignature() & ~other_clause.getSignature()) != 0) continue;

        size_t count = 0;

        // Count literals in "other_clause" which also appears in "short_clause"
        // If we reached the size of the short clause we are done
        for (Literal lit : other_clause) {
            if (_seen2[lit]) {
                ++count;
                if (count == short_clause_size) {
                    subsumed.push_back(other_c_nr);
                    break;
                }
            }
        }
    }
    for (const auto del_c_nr: subsumed) {
        if (setting.verbosity > 2) {
            std::cout << "c " << __FUNCTION__ << " clause #" << c_nr << ": " << short_clause << " subsumes #" << del_c_nr << ": " << clauses[del_c_nr] << std::endl;
        }
         removeClause(del_c_nr);
    }
    stat_subsumption += subsumed.size();
    clearSeen2(short_clause);

    return subsumed.size();
}

/**
 * \brief Checks whether a clause is subsumed by an existing binary clause in the database
 *
 * If the formula contains clauses \f$C\f$ and \f$C'\f$ such that
 * \f$C\subsetneq C'\f$, then \f$C'\f$ can be deleted. The result is
 * a logically equivalent formula.
 *
 * This function checks if `clause` is subsumed by any of the formulas binary clauses.
 * \param clause the clause for which we check if it subsumed
 * \param sign the signatur of `clause`, due to efficency reasons it is assumed that
 *        this value is computated in advance
 * \param except ID of the clause `clause` which should be skipped (as each clause subsumes itself)
 * \return true if the clause is subsumed
 */
template< typename Container >
bool Formula::isForwardSubsumedByBinary(const Container& clause, int except)
{
    for (const Literal check_lit : clause)
    {
        const Literal neg_lit = negate(check_lit);
        process_limit.decreaseLimitBy(implications[neg_lit].size());

        for (BinaryClause bin_clause: implications[neg_lit])
        {
            // Skip explicit stated exception clause
            const unsigned int& clauseid = bin_clause.getClauseID();
            if (static_cast<int>(clauseid) == except) continue;

            const Literal& sec_lit = bin_clause.getLiteral();
            // If literal-ID is already larger than largest ID of current clause
            // the binary can never subsume the current clause
            if (sec_lit > *clause.rbegin()) continue;

            // Found subsumption
            if (_seen[sec_lit]) {
                val_assert(!clauseDeleted(clauseid));
                val_assert(clauses[clauseid].size() == 2);
                clauses[clauseid].setStatus(ClauseStatus::MANDATORY);
                if (setting.verbosity > 2) {
                    std::cout << "c " << __FUNCTION__ << " clause " << lit2dimacs(check_lit) << " " << lit2dimacs(sec_lit) << " subsumes ";
                    for (Literal lit : clause) {
                        std::cout << lit2dimacs(lit) << " ";
                    }
                    std::cout << std::endl;
                }
                return true;
            }
        }
    }

    return false;
}

/**
 * \brief Checks whether a clause is subsumed by an existing non-binary clause in the database
 *
 * If the formula contains clauses \f$C\f$ and \f$C'\f$ such that
 * \f$C\subsetneq C'\f$, then \f$C'\f$ can be deleted. The result is
 * a logically equivalent formula.
 *
 * This function checks if `clause` is subsumed by any of the formulas non-binary clauses.
 * \param clause the clause for which we check if it subsumed
 * \param sign the signatur of `clause`, due to efficency reasons it is assumed that
 *        this value is computated in advance
 * \param except ID of the clause `clause` which should be skipped (as each clause subsumes itself)
 * \return true if the clause is subsumed
 */
template< typename Container >
bool Formula::isForwardSubsumed(const Container& clause, const uint64_t sign, int except)
{
#ifndef NDEBUG
    for (Literal lit : clause) {
        val_assert(_seen[lit]);
    }
#endif

    if (isForwardSubsumedByBinary(clause, except)) return true;

    const Literal check_lit = getSubsumerCandidate(clause);

    for (unsigned int other_c_nr: occ_list[check_lit]) {
        // Skip explicit stated exception clause
        if (except == static_cast<int>(other_c_nr)) continue;

        const Clause& other_clause = clauses[other_c_nr];

        // Skip to short clauses
        if (other_clause.size() > clause.size()) continue;
        // Check matching signatures
        if ((other_clause.getSignature() & ~sign) != 0) continue;

        bool is_subsumed = true;

        for (Literal lit : other_clause) {
            // If there is a literal in "other_clause" which is not contained in "clause"
            // "other_clause" cannot subsume "clause"
            if (!_seen[lit]) {
                is_subsumed = false;
                break;
            }
        }

        if (is_subsumed) {
            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << " clause " << other_clause << " subsumes ";
                for (Literal lit : clause) {
                    std::cout << lit2dimacs(lit) << " ";
                }
                std::cout << std::endl;
            }
            return true;
        }
    }
    return false;
}


// explicit instantiation of template arguments for this function
template bool Formula::isForwardSubsumed(const std::set<Literal>& clause, const uint64_t sign, int except);
template bool Formula::isForwardSubsumed(const std::vector<Literal>& clause, const uint64_t sign, int except);

bool Formula::isForwardSubsumed(const Clause& clause, int except)
{
    return isForwardSubsumed(clause.getLiterals(), clause.getSignature(), except);
}


/**
 * \brief Finds and removes subsumed clauses.
 *
 * If the formula contains clauses \f$C\f$ and \f$C'\f$ such that
 * \f$C\subsetneq C'\f$, then \f$C'\f$ can be deleted. The result is
 * a logically equivalent formula.
 * \return true iff the formula was modified.
 * \sa Formula::binarySubsumption()
 * \sa Formula::narySubsumption()
 */
bool Formula::removeSubsumedClauses()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }
    ScopeTimer subsumption(subsumption_time);

    const unsigned int old_stat_subsumption = stat_subsumption;

    for (std::size_t c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        const unsigned int num_del = isBackwardSubsuming(clauses[c_nr], c_nr);
        if (num_del > 0) {
            clauses[c_nr].setStatus(ClauseStatus::MANDATORY);
        }
    }

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " found " << (stat_subsumption - old_stat_subsumption) << " subsumed clauses" << std::endl;
    }
    return (stat_subsumption > old_stat_subsumption);
}

template<typename Container>
Literal Formula::getSubsumerCandidate(const Container& clause) const
{
    size_t min_occ = std::numeric_limits<size_t>::max();
    Literal min_lit = 0;
    for (Literal lit : clause) {
        if (occ_list[lit].size() < min_occ) {
            min_occ = occ_list[lit].size();
            min_lit = lit;
        }
    }
    val_assert(min_lit != 0);
    return min_lit;
}

  /**
 * \brief Returns true if 'clause' contains the literal 'other_lit'
 *
 * The clause needs to be in increasing order.
 * \sa Formula::selfSubsumingResolution()
 */
static bool almostSubsumedByBinary(const Clause& clause, Literal other_lit)
{
    for (Literal lit: clause) {
        if (lit == other_lit) {
            return true;
        } else if (lit > other_lit) {
            return false;
        }
    }

    return false;
}


/**
 * \brief Returns true if the clause c2 is -- with the exception of almostLit -- a subset of c.
 *
 * In this case resolution of c and c2 w.r.t. almostLit returns a subset of c.
 * \sa Formula::selfSubsumingResolution()
 */
static bool almostSubsumedByNary(const Clause& c, const Clause& c2, Literal almostLit)
{
    val_assert(c.size() >= c2.size());

    unsigned int i = 0;
    unsigned int j = 0;

    const auto c_size = c.size();
    const auto c2_size = c2.size();

    while (i != c_size && j != c2_size)
    {
        if (c[i] == c2[j]) {
            ++i;
            ++j;
        } else if (c[i] == almostLit) {
            ++i;
        } else if (c2[j] == negate(almostLit)) {
            ++j;
        } else if (c[i] < c2[j]) {
            ++i;
        } else {
            return false;
        }
    }

    if (j != c2_size) return false;
    return true;
}


/**
 * \brief Tries to make clauses shorter by resolution.
 *
 * If c1 and c2 are clauses such that c1 contains literal l and
 * c2 !l and the resolvent of c1 and c2 w.r.t. l is a subset of c1,
 * then c1 can be replaced by the resolvent. This is known as
 * self-subsuming resolution.
 * This method tries to make clauses as short as possible by applying
 * self-subsuming resolution.
 * \return true if the formula was modified.
 */
bool Formula::selfSubsumingResolution()
{
    // For all n-nary clauses c = (l1,l2,...,ln)
    // check if there exists a clause c' = (-l1,l2,...,lm) with m<=n
    // -> replace c by c'' = (l2,...ln)

    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer self_sub_timer(self_subsumption_time);
    process_limit.setLimit(PreproMethod::SELF_SUBSUMPTION);

    const unsigned int old_stat_selfsubsuming = stat_selfsubsuming_resolution;
    const unsigned int old_stat_subsumption = stat_subsumption;
    unsigned int subsumed_clauses = 0;

    // collect all candidates
    candidates.clear();
    candidates.resize(clauses.size());
    variable_score.clear();
    variable_score.resize(clauses.size(), 0);

    for (unsigned int cl_nr = 0; cl_nr != clauses.size(); ++cl_nr) {
        if (clauseDeleted(cl_nr)) continue;
        if (clauseOptional(cl_nr)) continue;
        // ignore all clauses with size 2 -> they cannot be candidates for selfsubsumption
        if (clauses[cl_nr].size() < 3) continue;
        variable_score[cl_nr] = clauses[cl_nr].size();
        candidates.insert(cl_nr);
    }

    bool subsumed = false;

    // Iterate over all candidates
    while (!candidates.empty()) {

        if (process_limit.reachedLimit()) {
            if (setting.verbosity > 1) {
                std::cout << "c terminate " << __FUNCTION__ << " due to process limit.\n";
            }
            break;
        }
        if (interrupt) break;

        subsumed = false;
        unsigned int c_nr = candidates.top();

        for (unsigned int i = 0; i != clauses[c_nr].size(); ++i) {
            // Clause could be potentially deleted due to universal reduction after removing a literal
            // due to self-subsumption
            if (clauseDeleted(c_nr)) break;
            const auto& c = clauses[c_nr];

            // Skip binary clauses, they can never be self-subsuming
            // Clause can get binary due selfsubsumption
            if (c.size() < 3) break;

            const Literal x = c[i];

            // self subsumption with binary clause c'
            for (BinaryClause clause: implications[x])
            {
                const Literal impl = clause.getLiteral();

                uint32_t binsign = 0;
                addSignatureLit(binsign, lit2var(x));
                addSignatureLit(binsign, lit2var(impl));

                // Skip if signatures do not match
                if ((binsign & ~c.getVarSignature()) != 0) {
                    continue;
                }

                process_limit.decreaseLimitBy(c.size());
                if (almostSubsumedByBinary(c, impl))
                {
                    ++stat_selfsubsuming_resolution;
                    if (setting.verbosity > 2) {
                        std::cout << "c " << __FUNCTION__ << " removes " << lit2dimacs(x) << " from clause " << c << " due to binary " << lit2dimacs(negate(x)) << " " << lit2dimacs(impl) << std::endl;
                    }

                    // Reset index if literal was further reduced by universal reduction
                    // Otherwise
                    if (removeLiteral(c_nr, x)) i = -1;
                    else --i;
                    subsumed = true;
                    const unsigned int bin_c_nr = clause.getClauseID();
                    clauses[bin_c_nr].setStatus(ClauseStatus::MANDATORY);
                    break;
                }
            } // end for (clause)

            // self subsumption with n-nary clause c'
            if (!subsumed)
            {
                const Literal x_neg = negate(x);
                for (unsigned int c_nr2: occ_list[x_neg])
                {
                    const auto& c2 = clauses[c_nr2];
                    if (c2.size() > c.size()) continue;
                    // We already have checked binary clauses
                    if (c2.size() < 3) continue;
                    // Skip if signatures do not match
                    if ((c2.getVarSignature() & ~c.getVarSignature()) != 0 ) {
                        continue;
                    }

                    process_limit.decreaseLimitBy(c.size() + c2.size());
                    if (almostSubsumedByNary(c, c2, x))
                    {
                        ++stat_selfsubsuming_resolution;
                        if (setting.verbosity > 2) {
                            std::cout << "c " << __FUNCTION__ << " removes " << lit2dimacs(x) << " from clause " << c << " due to clause " << c2 << std::endl;
                        }
                        // Reset index if literal was further reduced by universal reduction
                        // Otherwise
                        if (removeLiteral(c_nr, x)) i = -1;
                        else --i;
                        subsumed = true;
                        clauses[c_nr2].setStatus(ClauseStatus::MANDATORY);
                        break;
                    }
                }
            }
        }

        if (subsumed) {
		  // Check whether reduced clause now subsumes other clauses
		  // Clause size can be 0, if the clause is reduced to a unit due to universal reduction
		  // In this case we have nothing to do here
            if (clauses[c_nr].size() > 0) {
                isBackwardSubsuming(clauses[c_nr], c_nr);
                // Add new candidates which can be selfsubsumed with the newly generated clause
                for (Literal lit : clauses[c_nr]) {
                    for (unsigned int occ_nr : occ_list[negate(lit)]) {
                        if (!candidates.inHeap(occ_nr)) {
                            candidates.insert(occ_nr);
                        }
                    }
                }
            }
            ++subsumed_clauses;
        }
    }

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " found " << (stat_selfsubsuming_resolution - old_stat_selfsubsuming) << " self-subsumed literals in " << subsumed_clauses << " clauses and " << (stat_subsumption - old_stat_subsumption) << " subsumptions\n";
    }

    return (subsumed_clauses > 0);
}


} // end namespace hqspre
