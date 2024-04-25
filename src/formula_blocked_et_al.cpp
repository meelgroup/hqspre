#include <iostream>
#include <vector>
#include "formula.hpp"

/**
 * \file formula_blocked_et_al.cpp
 * \brief Implementation of hidden tautology elimination, hidden subsumption elimination
 * \author Sven Reimer
 * \date 06/2016
 */

namespace hqspre {

/**
 * \brief Checks if the resolvent of two clauses is a tautology.
 * \pre The literals of the other clause should be marked in the "_seen" datastructure
 * \param clause the clause containing the pivot variable
 * \param pivot_var the pivot variable
 * \return true if the resolvent of c1 and c2 w.r.t. pivot_var is a tautology
 */
template <typename Container>
bool Formula::checkResolventTautology(const Container& clause, Variable pivot_var) const
{
  for (Literal lit : clause ) {
	// skip pivot var
	if (lit2var(lit) == pivot_var ) continue;
	// found tautology
	if (_seen[negate(lit)]) {
	  if (dependenciesSubset(lit2var(lit), pivot_var)) {
		return true;		
	  }
	}
  }
  return false;
}


/* \brief Tries to add blocking universal literals, such that clause is tautology.
 * \param clause a copy of the clause as an ordered container into which the covered literals are inserted.
 * \note clause will not be extended, it is only checked whether literals can be added such that the resulting clause will be a tautology
 * \return true if clause is tautology
 */
template <typename Container>
bool Formula::addBlockingLiterals(const Container& clause)
{
    // BLA is only sound for QBF!
    if (prefix->type() == PrefixType::DQBF) return false;

    for (Literal lit : clause) {
        if (isExistential(lit2var(lit))) continue;

        if (clauseBlockedByLit(negate(lit))) {
            ++stat_bla;
            clearSeen(clause);
            return true;
        }
    }
    return false;
}

/*
 * \brief Checks whether a literal blockes one of its clauses
 *
 * Updates the candidates for potential new blocked clauses
 */
bool Formula::checkBlockedLit(Literal lit)
{
    bool modified = false;
    const size_t osize = occ_list[lit].size();

    for (unsigned int i = 0; i != osize; ++i) {
        unsigned int c_nr = occ_list[lit][i];
        if (clauseDeleted(c_nr)) continue;
        if (setting.preserve_gates && clause_gate[c_nr]) continue;

        const Clause& clause = clauses[c_nr];
        setSeen(clause);
        if (clauseBlockedByLit(lit)) {
            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "(): clause " << clause << " is blocked by " << lit2dimacs(lit) << " occ sizes: " << occ_list[lit].size() << " " << occ_list[negate(lit)].size() << std::endl;
            }

            if (isExistential(lit2var(lit))) {
                for (Literal clit : clause ) {
                    if (clit != lit && !isDontTouch(lit2var(clit))) {
                        // Check whether lit will be pure after deletion of blocked clause
                        if (checkPure(clit)) {
                            if (isExistential(lit2var(clit))) {
                                pushUnit(negate(clit), true);
                            } else {
                                pushUnit(clit, true);
                            }
                        } else if (!candidates.inHeap(negate(clit))) {
                            candidates.insert(negate(clit));
                        }
                    }
                }
                std::vector<unsigned int> tmp_clause(clause.size());
                for (unsigned int j = 0; j != clause.size(); ++j ) {
                    tmp_clause[j] = clause[j];
                }
                removeClause(c_nr);
                for (Literal tmp_lit : tmp_clause ) {
                    if (checkImplicationChain(tmp_lit)) {
                        std::cout << "implication chains performed for " << lit2dimacs(lit) << std::endl;
                    }
                }
                ++stat_bce;
            } else {
                if (setting.verbosity > 2) {
                    std::cout << "c " << __FUNCTION__ << "(): universal literal " << lit2dimacs(lit) <<  " blocking clause " << clause << std::endl;
                }
                ++stat_ble;
                removeLiteral(c_nr, lit);
            }
            modified = true;
        }
        clearSeen(clause);
    }
    return modified;
}


/**
 * \brief Tries to add further implications to the formula which are blocked.
 * \return true if the formula was modified.
 */
bool Formula::addBlockedImplications()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }
    unsigned int count = 0;

    std::vector<Literal> bin_clause(2, 0);
    for (Literal lit1 = minLitIndex(); lit1 < maxLitIndex(); ++lit1) {
        const Variable var1 = lit2var(lit1);
        if (varDeleted(var1)) continue;
        for (Literal lit2 = lit1 + 1; lit2 <= maxLitIndex(); ++lit2) {
            const Variable var2 = lit2var(lit2);
            if (varDeleted(var2) || var1 == var2) continue;
            if (hasImplication(negate(lit1), lit2)) continue;

            bin_clause[0] = lit1;
            bin_clause[1] = lit2;
            if (clauseBlocked(bin_clause)) {
                addClause(bin_clause, false, true, ClauseStatus::OPTIONAL);
                ++count;
            }
        }
    }

    stat_bia += count;

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << "(): added " << count << " blocked binary clauses." << std::endl;
    }
    return count > 0;
  }

/**
 * \brief Removes the clause "c_nr" due to hidden tautology or blocked clause elimination and updates internal candidate lists
 */
void Formula::removeClauseAndUpdateCandidates(unsigned int c_nr)
{
    checkPure(clauses[c_nr], 0);

    // Recreate original clause
    // Since it will be deleted in the next step and the upcoming
    // Implication chain check should be applied without this clause
    std::vector<unsigned int> org_clause(clauses[c_nr].size());
    for (unsigned int j = 0; j != clauses[c_nr].size(); ++j ) {
        org_clause[j] = clauses[c_nr][j];
    }

    // Delete clause and its occurences
    removeClause(c_nr);
    unitPropagation();

    // No update of candidates needed if implication chains and blocked clauses are not active
    if (!setting.impl_chains && !setting.bce) return;

    // Check whether new implication chains are produced
    // And update candidates
    for (Literal lit : org_clause)
    {
        unsigned int check_lit = lit;
        if (setting.impl_chains) {
            unsigned int check_lit = checkImplicationChain(lit);
            if (check_lit != 0) {
                ++stat_impl_chains;
                if (setting.bce > 0) {
                    // add new candidates if bce is applied
                    for (unsigned int occ_nr : occ_list[check_lit] ) {
                        if (clauseDeleted(occ_nr)) continue;
                        if (!blocked_candidates.inHeap(occ_nr)) {
                            blocked_candidates.insert(occ_nr);
                        }
                    }
                }
            } else {
                check_lit = lit;
            }
        }

        // Update candidates
        if (setting.bce > 0) {
            // add new candidates if bce is applied
            for (unsigned int occ_nr : occ_list[negate(check_lit)] ) {
                if (clauseDeleted(occ_nr)) continue;
                if (!blocked_candidates.inHeap(occ_nr)) {
                    blocked_candidates.insert(occ_nr);
                }
            }
        }
    }
}

/**
 * \brief Finds and removes hidden tautologies, blocked clauses, subsumptions from the formula.
 *
 * \return true iff the formula was modified.
 */
bool Formula::removeBlockedAndFriends()
{
    bool modified = false;

    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer bce(bce_time);
    process_limit.setLimit(PreproMethod::BCE);

    const unsigned int old_stat_hte = stat_hte;
    const unsigned int old_stat_bce = stat_bce;
    const unsigned int old_stat_hse = stat_hse;
    const unsigned int old_stat_bla = stat_bla;
    const unsigned int old_stat_impl_chains = stat_impl_chains;

    val_assert(_seen.size() > maxLitIndex());
    std::vector<Literal> clause;


    initCandidateLists();

    while (!blocked_candidates.empty()) {
        if (interrupt) break;

        const unsigned int c_nr = blocked_candidates.top();
        if (clauseDeleted(c_nr)) { continue; }
        if (setting.preserve_gates && clause_gate[c_nr]) { continue; }

        if (process_limit.reachedLimit()) {
            if (setting.verbosity > 1) {
                std::cout << "c terminate " << __FUNCTION__ << " due to process limit.\n";
            }
            break;
        }

        const Clause& c( clauses[c_nr] );
        uint64_t sign = 0;

        clause.resize(c.size());

        for (unsigned int j = 0; j != c.size(); ++j) {
            clause[j] = c[j];
            val_assert(!_seen[c[j]]);
            _seen[c[j]] = true;
        }

        bool hidden_tautology = false;

        if (setting.hidden || setting.covered || setting.bla) {
            // use incomplete hidden literal addition
            if (setting.hidden == 1) {
                hidden_tautology = addHiddenLiteralsBinary(c_nr, clause, sign);
            }
            // use complete hidden literal addition
            else if (setting.hidden == 2) {
                hidden_tautology = addHiddenLiterals(c_nr, clause, sign);
            }

            // add covered literals (if clause in not already a hidden tautology)
            if (!hidden_tautology && setting.covered) {
                hidden_tautology = addCoveredLiterals(clause, sign);
            }

            // adds blocked universal literals
            if (!hidden_tautology && setting.bla) {
                hidden_tautology = addBlockingLiterals(clause);
            }
        }

        if (hidden_tautology)
        {
            ++stat_hte;
            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "(): clause " << c << " is a hidden tautology." << std::endl;
            }

            removeClauseAndUpdateCandidates(c_nr);
            modified = true;
        }
        // check for blocked clauses
        else {
            bool clause_blocked = false;

            if (setting.bce > 0) {

                if (clauseBlocked(clause)) {
                    if (setting.verbosity > 2) {
                        std::cout << "c " << __FUNCTION__ << "(): clause " << clauses[c_nr] << " is (hidden) blocked." << std::endl;
                    }
                    ++stat_bce;

                    removeClauseAndUpdateCandidates(c_nr);
                    modified = true;
                    clause_blocked = true;
                }
            }

            // check for hidden subsumptions if clause is not a tautology or blocked
            // also skip if we applied complete hidden literal addition.
            // In this case the hidden subsumption check was done implicitely during the hidden literal addtion
            if (setting.hidden != 2 && setting.hse && !clause_blocked) {
                bce_time.stop();
                hse_time.start();

                // Check of subsumption, excluded current clause id "i"
                if (isForwardSubsumed(clause, sign, c_nr)) {

                    ++stat_hse;
                    if (setting.verbosity > 2) {
                        std::cout << "c " << __FUNCTION__ << "(): clause " << c << " is (hidden) subsumed." << std::endl;
                    }

                    removeClauseAndUpdateCandidates(c_nr);
                    modified = true;
                }
                hse_time.stop();
                bce_time.start();
            }
        }
        clearSeen(clause);
    }

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " found " << (stat_hte - old_stat_hte) << " hidden tautologies, " << (stat_bce - old_stat_bce) << " hidden blocked clauses with " << (stat_bla - old_stat_bla) << " added blocked literals and " << (stat_hse - old_stat_hse) << " hidden subsumptions. Additionally " << (stat_impl_chains - old_stat_impl_chains) << " implication chains are found." << std::endl;
    }

    if (numClauses() == 0) throw SATException(this);
    return modified;
}

  /**
 * \brief Adds hidden literals obtained by only checking binary clauses

 * Also checks if the given clause is a hidden tautology.
 * \return true if `clause` is a hidden tautology
 * \pre Assumes that "_seen" vector was initialized with "clause"
 * \param clause the clause to check
 * \param sign the signature of `clause`
 * \param c_nr the clause ID of `clause`
 */
bool Formula::addHiddenLiteralsBinary(const int c_nr, std::vector<Literal>& clause, uint64_t& sign) const
{
    unsigned int csize = clause.size();

    for (unsigned int i = 0; i != csize; ++i) {
        const Literal l0 = clause[i];
        addSignatureLit(sign, l0);

        process_limit.decreaseLimitBy(implications[negate(l0)].size());

        for (BinaryClause bin : implications[negate(l0)]) {
            // Skip currently considered binary clause
            if (static_cast<int>(bin.getClauseID()) == c_nr ) {
                continue;
            }

            const Literal impl = bin.getLiteral();
            // We found a hidden tautology!
            if (_seen[impl]) {
                return true;
            } else if (!_seen[negate(impl)]) {
                // otherwise add hidden literal
                clause.push_back( negate(impl) );
                ++csize;
                _seen[negate(impl)] = true;
            }
        }
    }

    return false;
}

  /**
 * \brief Adds hidden literals to a given clause.
 * also checks for hidden tautologies
 * \param c_nr the ID of the clause which is to be extended.
 * \param clause a copy of the clause as an ordered container into which the hidden literals are inserted.
 * \note Only the copy of the clause is modified, the original clause in clauses[c_nr] stays untouched.
 * \pre Assumes that "_seen" vector was initialized with "clause"
 * \return true if clause is a hidden tautology
 */
bool Formula::addHiddenLiterals(const int c_nr, std::vector<Literal>& clause, uint64_t& sign) const
{
    unsigned int csize = clause.size();

    for (unsigned int c = 0; c != csize; ++c)
    {
        Literal cur_lit = clause[c];
        addSignatureLit(sign, cur_lit);

        // proceed all clauses in which the current literal occurs
        for (unsigned int j = 0; j != occ_list[cur_lit].size(); ++j ) {
            int other_c_nr = occ_list[cur_lit][j];
            if (clauseDeleted(other_c_nr) || c_nr == other_c_nr) continue; // skip the clause c
            const Clause& other = clauses[other_c_nr];
            // Clause "other" can never contain a hidden literal if it is larger or at the same size as current clause
            if (other.size() > clause.size() + 1) continue;
            // Either this clause was already successful used -> always skip
            // Or clause was used unsuccessfully -> skip this time until it might get candidate again
            if (other.isMarked()) { continue; }

            bool candidate_found = false;
            Literal candidate = 0;

            process_limit.decreaseLimitBy(3, clause.size() + other.size());

            // Now check whether we can add a hidden literal by "other"
            for (Literal lit : other) {
                // Literal not in clause -> candidate for adding hidden literal
                if (!_seen[lit]) {
                    // We have already found a candidate? There can never be more than one
                    // -> clause can not used to add a hidden literal
                    if (candidate != 0) {
                        candidate_found = false;
                        break;
                    }
                    candidate = lit;
                    candidate_found = true;
                }
            }

            // Mark current clause as touched, so that we do not check it again
            // until it becomes necessary
            other.mark(1);

            // We did not find any candidate?
            // That means all literals in "other" are already in "clause"
            // -> "other" subsumes the current clause and we have found a hidden subsumption
            if (candidate == 0) {
                // reset clause marking
                for (unsigned int c_nr = 0; c_nr <= maxClauseIndex(); ++c_nr) {
                    clauses[c_nr].unMark();
                }
                return true;
            }
            // We found a candidate for adding a hidden literal
            // -> add negated literal to clause
            else if (candidate_found) {
                val_assert(candidate != 0 && !_seen[candidate]);
                // If negated candidate is already in clause, we would add a duplicated literal
                // -> skip in this case
                if (!_seen[negate(candidate)]) {
                    ++csize;
                    const Literal hidden_lit = negate(candidate);
                    _seen[hidden_lit] = true;
                    clause.push_back(hidden_lit);

                    // Unmark occurence list of added literal
                    // These clauses are candidates again for producing a new hidden literal
                    for (unsigned int k = 0; k != occ_list[hidden_lit].size(); ++k) {
                        clauses[occ_list[hidden_lit][k]].unMark(1);
                    }
                }
                // Mark current clause as used, so that we do not check it again for "clause"
                // Since "other" produced a hidden literal, it can never be a candidate for
                // adding another hidden literal
                other.mark(2);
            }
        }
    }

    // reset clause marking
    for (unsigned int c_nr = 0; c_nr <= maxClauseIndex(); ++c_nr) {
        clauses[c_nr].unMark();
    }
    return false;
}

/**
 * \brief Adds covered literals to a given clause.
 * \param c_nr the number of the clause which is to be extended.
 * \param clause a copy of the clause as an ordered container into which the covered literals are inserted.
 * \note Only the copy of the clause is modified, the original clause in clauses[c_nr] stays untouched.
 * \pre Assumes that "_seen" vector was initialized with "clause"
 * \return true if clause is a hidden tautology
 */
bool Formula::addCoveredLiterals(std::vector<Literal>& clause, uint64_t& sign) const
{
 
  size_t csize = clause.size();
  for (unsigned int i = 0; i != csize; ++i) {
        const Literal pivot = clause[i];
        addSignatureLit(sign, pivot);
        if (isUniversal(lit2var(pivot))) continue;

        bool first = true;
        std::vector<Literal> candidate_literals;

        const std::vector<unsigned int>& resolution_partners = occ_list[negate(pivot)];
        for (unsigned int partner_index: resolution_partners) {
            // Check if clause (resolved)_pivot _clauses[partner_index] is a tautology
            if (clauseDeleted(partner_index)) continue;
            process_limit.decreaseLimitBy(3, clauses[partner_index].size());
            if (checkResolventTautology(clauses[partner_index], lit2var(pivot))) continue;

            if (first) {
                first = false;
                process_limit.decreaseLimitBy(clauses[partner_index].size());
                for (Literal literal: clauses[partner_index]) {
                  if (literal != negate(pivot) && dependenciesSubset(lit2var(literal), lit2var(pivot))) {
					val_assert(!_seen2[literal]);
					_seen2[literal] = true;
					candidate_literals.push_back(literal);
                  }
                }
            } else {
				for (Literal partner_lit : clauses[partner_index] ) {
				  if ( !dependenciesSubset(lit2var(partner_lit), lit2var(pivot))) continue;
				  // "partner_lit" is part of candidates -> add to intersection
				  else if (_seen2[partner_lit])
					{
					  // mark "partner_lit" as part of the intersection
					  _seen2[partner_lit] = 'i';
					}
                }

				// Update candidates by intersection values
				// Update also the _seen2 vector
				unsigned int j = 0;
				for (unsigned int i = 0; i != candidate_literals.size(); ++i) {
				  Literal lit = candidate_literals[i];
				  val_assert(_seen2[lit] != false);
				  
				  if (_seen2[lit] == 'i' ) {
					// literal is part of the intersection
					candidate_literals[j] = lit;
					_seen2[lit] = true;
					++j;
				  } else {
					// literal not part of intersection -> unmark literal
					_seen2[lit] = false;
				  }
				}
				candidate_literals.resize(j);
				
                // Intersection empty -> We are done for the current pivot element
				// At this point all literals in the _seen2 vector are cleaned -> no update needed
                if (candidate_literals.empty()) break;
			}
        }

        // clear all remaining marked literals
        clearSeen2(candidate_literals);

        for (Literal literal: candidate_literals) {

            // Found hidden tautology
            if (_seen[negate(literal)]) {
                return true;
            }
            else if(!_seen[literal]) {
                clause.push_back(literal);
                ++csize;
                _seen[literal] = true;
            }
        }
  }

    return false;
}


} // end namespace hqspre
