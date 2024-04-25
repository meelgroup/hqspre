#include <vector>
#include <set>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <stack>
#include "formula.hpp"
#include "aux.hpp"

/**
 * \file formula.cpp
 * \brief Implementation of basic functions for variable, clause, and dependency management
 * \author Ralf Wimmer
 * \date 12/2015-03/2016
 */


namespace hqspre {

/**
 * \brief Performs preprocessing on the formula.
 */
void Formula::preprocess()
{
    ScopeTimer prepro(prepro_time);
    if (setting.verbosity > 0) {
        std::cout << "c Preprocessing ..." << std::endl;
        if (setting.max_loops == 0) {
            std::cout << "c Warning! No preprocessing loops given" << std::endl;
        }
    }

    if (interrupt) return;

    blocked_candidates.resize(clauses.size());

    // Do initial unit and pure propagation
    val_assert(checkConsistency());
    fastPreprocess();
    val_assert(checkConsistency());

    if (setting.preserve_gates) determineGates();

    bool again = true;
    bool temp_hidden = setting.hidden;

    while (again) {
        if (interrupt) return;

        again = false;

        if (stat_prepro_loops >= setting.max_loops) {
            break;
        }
        ++stat_prepro_loops;
        if (setting.verbosity > 1) {
            std::cout << "c Preprocessing loop #" << stat_prepro_loops << std::endl;
        }

        val_assert(checkConsistency());

        // Substitution
        if (setting.substitution && stat_prepro_loops <= setting.max_substitution_loops && applySubstitution()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (setting.verbosity > 1) {
                std::cout << "c Loop " << stat_prepro_loops << " substitutions " << stat_substitution << " rewritings " << stat_rewriting << std::endl;
            }
        }

        // Subsumption checks
        if (setting.subsumption && removeSubsumedClauses()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Always skip hidden literals in first run
        if (stat_prepro_loops == 1 ) setting.hidden = false;

        // Blocked clause and friends (tautology/subsumption) elimination
        if ((setting.bce || setting.hse) && removeBlockedAndFriends()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }
        if (stat_prepro_loops == 1 ) setting.hidden = temp_hidden;

        if (setting.hec && findHiddenEquivAndContraDefinitions() ) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Self-subsuming resolution
        if (setting.self_subsumption && selfSubsumingResolution()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Elimination of implication chains
        if (setting.impl_chains && findImplicationChains()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Variable elimination by resolution
        if (setting.resolution && applyResolution()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Subsumption checks
        if (setting.subsumption && removeSubsumedClauses()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Detecting contradictions
        if (setting.contradictions && findContradictions()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Finding constant variables (a.k.a. backbones) by SAT calls
        if (stat_prepro_loops == 1) {
            if (setting.sat_const && findConstantsBySAT()) {
                again = true;
                fastPreprocess();
                val_assert(checkConsistency());
                if (interrupt) return;
            }
            if (setting.bia && addBlockedImplications()) {
                again = true;
                fastPreprocess();
                val_assert(checkConsistency());
                if (interrupt) return;
            }

            // Finding implications (= implied binary clauses) by SAT calls
            if (setting.sat_impl && findImplicationsBySAT()) {
                again = true;
                fastPreprocess();
                val_assert(checkConsistency());
                if (interrupt) return;
            }

            determineGates();
            removeOptionalClauses();
            if (interrupt) return;
        } else if (stat_prepro_loops <= setting.max_substitution_loops) {
            determineGates();
            removeOptionalClauses();
        }

        // Incomplete SAT/UNSAT checks
        if (stat_prepro_loops == 1 && setting.sat_incomplete) {
            checkSAT();
            checkUNSAT();
        }

        // Apply universal expansion
        if (setting.univ_expand == 1 && applyUniversalExpansion()) {
            again = true;
            val_assert(checkConsistency());
            if (interrupt) return;
        }
        else if (setting.univ_expand == 2 && applyUniversalExpansion2()) {
            again = true;
            val_assert(checkConsistency());
            if (interrupt) return;
        }

        // Subsumption checks
        if (setting.subsumption && removeSubsumedClauses()) {
            again = true;
            fastPreprocess();
            val_assert(checkConsistency());
            if (interrupt) return;
        }


        // Incomplete SAT/UNSAT checks
        if (stat_prepro_loops == 1 && setting.sat_incomplete) {
            checkSAT();
            if (interrupt) return;
            checkUNSAT();
            if (interrupt) return;
        }


        updateVars();
        if (interrupt) return;
    } // end main prepro loop

    // If the formula is propositional, but could not be solved
    // by the SAT solver within the given time limit, abort the
    // preprocessing phase.
    if (numUVars() == 0) {
        checkSAT();
        if (interrupt) return;
    }


    val_assert(checkConsistency());
    if (setting.verbosity > 0) std::cout << std::endl;
}

/**
 * \brief Performs preprocessing on the formula.
 * Does not touch any gate defining variables and clauses
 * \return The set of found gates
 */
std::vector<Gate> Formula::preprocessGates()
{
    setPreserveGates(true);
    preprocess();

    auto result = determineGates();

    for (Gate& gate: result) {
        for (unsigned int c_nr: gate.encoding_clauses) removeClause(c_nr);
        gate.encoding_clauses.clear();
    }

    return result;
}


  /**
 * \brief Applies unit propagation, equivalance checking, pure literal detection and implication chains
 *
 * Should be called after an expensive preprocessor method for quick and cheap detection of
 * new units.
 */
void Formula::fastPreprocess()
{
    const unsigned int old_stat_unit_pure = stat_unit_pure;
    const unsigned int old_stat_impl_chains = stat_impl_chains;
    unitPropagation();
    findEquivalences();
    const unsigned int before_pure = stat_unit_pure;
    findPure();

    if (setting.verbosity > 1 && (stat_unit_pure > old_stat_unit_pure)) {
        std::cout << "c " << __FUNCTION__ << " detects " << (stat_unit_pure - old_stat_unit_pure) << " new units (" << (before_pure - old_stat_unit_pure) << " via unit prop, and " << (stat_unit_pure - before_pure) << " via pure detection). Found " << (stat_impl_chains - old_stat_impl_chains) << " new implication chains." << std::endl;
    }
}

/**
 * \brief Checks which variables still occur in the matrix.
 *
 * Marks all variables which do not occur in the matrix as deleted.
 * For QBFs, subsequent blocks with the same quantifier are merged.
 */
void Formula::updateVars()
{
    val_assert(prefix != nullptr);
    val_assert(unit_stack.empty());

    // Determine which variables actually occur in the formula.
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (!varDeleted(var) && occ_list[var2lit(var, false)].empty() && occ_list[var2lit(var, true)].empty()) {
            removeVar(var);
        }
    }

    prefix->updateVars();
}


/**
 * \brief Returns the accumulated number of dependencies of all existential variables.
 */
unsigned int Formula::numDependencies() const noexcept
{
    val_assert(prefix != nullptr);

    return prefix->numDependencies();
}


/**
 * \brief Checks if `var1`'s dependencies are a subset of `var2`'s dependencies.
 *
 * If `var1` is universal, this function returns whether `var2` depends on `var1`.
 * If both variables are existential, this function checks whether the dependency
 * set of `var1` is a subset of `var2`'s dependencies.
 *
 * \note `var2` has to be existential.
 */
bool Formula::dependenciesSubset(Variable var1, Variable var2) const
{
    val_assert(prefix != nullptr);

    return prefix->dependenciesSubset(var1, var2);
}


/**
 * \brief Inserts a clause into the occurrence lists and implication lists.
 *
 * \note Only for internal use.
 * \param c_nr the number of the newly created clause
 * \param check_subsumption if true, it is checked whether the clause subsumes other clauses in database
 * \return the clause ID if the clause was actually added; -2 if the clause was a tautology; -1 if the clause was unit.
 */
int Formula::addClauseToLists(unsigned int c_nr, bool check_subsumption)
{
    val_assert(c_nr <= maxClauseIndex());
    val_assert(!clauseDeleted(c_nr));

    auto& clause = clauses[c_nr];

#ifndef NDEBUG
    for (const Literal lit: clause) {
        if (varDeleted(lit2var(lit))) {
            std::cerr << "[ERROR] Variable " << lit2var(lit) << " is deleted in clause " << clause << std::endl;
        }
        val_assert_msg(!varDeleted(lit2var(lit)), "Trying to add a clause with a deleted variable");
    }
#endif

    if (clause.isTautology()) {
        if (setting.verbosity > 2) {
            std::cout << "c " << __FUNCTION__ << "(" << c_nr << ") Ignoring tautology " << clause << std::endl;
        }
        clause.clear();
        clause.setStatus(ClauseStatus::DELETED);
        deleted_clause_numbers.push_back(c_nr);
        return -2;
    }

    // Perform universal reduction
    if (setting.univ_reduction) universalReduction(clause);

    clause_sizes[c_nr] = clause.size();

    if (clause.empty()) {
        throw UNSATException("Trying to add an empty clause!", this);
        return -2;
    }

    if (clause.size() == 1) {
        pushUnit(clause[0]);
        clause.clear();
        clause.setStatus(ClauseStatus::DELETED);
        deleted_clause_numbers.push_back(c_nr);
        return -1;
    }

    // mark clause as modified
    if (clause_modified.size() <= c_nr) clause_modified.resize(c_nr + 1, false);
    if (clause_gate.size() <= c_nr) clause_gate.resize(c_nr + 1, false);

    clause_modified[c_nr] = true;

    // fill occurrence lists
    for (Literal lit: clause) {
        occ_list[lit].push_back(c_nr);
    }

    if (check_subsumption) {
        const auto num_subsumed = isBackwardSubsuming(clauses[c_nr], c_nr);
        if (num_subsumed > 0) {
            clauses[c_nr].setStatus(ClauseStatus::MANDATORY);
            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "(" << clauses[c_nr] << ") removed " << num_subsumed << " subsumed clauses." << std::endl;
            }
        }
    }

    // For binary clauses, add implications.
    // Attention! first check subsumptions, then add implications!
    // Otherwise we might remove the implication in subsumption check.
    if (clause.size() == 2) {
        // binary clauses are additionally stored as implications.
        addImplication(negate(clause[0]), clause[1], c_nr);
        addImplication(negate(clause[1]), clause[0], c_nr);
    }

    val_assert(clauses[c_nr].checkConsistency());
    return c_nr;
}


/**
 * \brief Adds a clause to the formula.
 *
 * \note Calling this function is only allowed as long as none of
 *       the functions has been called which modify the formula
 *       (like unitPropagation(), findPure(), ...)
 * \param _clause vector with the literals of the clause
 * \param needs_sorting if true, the clause is sorted and duplicate literals are removed.
 * \pre If needs_sorting is false, the caller has to guarantee that the literals are
 *      ordered in increasing order and that no literal appears more than once.
 * \param check_subsumption if true, it is checked whether the clause subsumes other clauses in database
 * \return the clause ID if the clause was actually added; -2 if the clause was a tautology; -1 if the clause was unit.
 * \throw UNSATException if an empty clause is added.
 */
int Formula::addClause(const std::vector<Literal>& _clause, bool needs_sorting, bool check_subsumption, ClauseStatus status)
{
    if (_clause.empty()) {
        throw UNSATException("Trying to add an empty clause", this);
    }

    if (_clause.size() == 1) {
        pushUnit(_clause[0]);
        return -1;
    }

    unsigned int c_nr = 0;
    assert(clauses.size() == clause_sizes.size());

    // Try to recycle clause numbers where possible.
    if (deleted_clause_numbers.empty()) {
        clause_sizes.push_back(_clause.size());
        clauses.emplace_back(_clause, needs_sorting, status);
        c_nr = clauses.size() - 1;
    } else {
        c_nr = deleted_clause_numbers.back();
        deleted_clause_numbers.pop_back();
        clause_sizes[c_nr] = clauses[c_nr].size();
        clauses[c_nr] = Clause(_clause, needs_sorting, status);
    }

    return addClauseToLists(c_nr, check_subsumption);
}


/**
 * \brief Adds a clause to the formula.
 *
 * \note Calling this function is only allowed as long as none of
 *       the functions has been called which modify the formula
 *       (like unitPropagation(), findPure(), ...)
 * \param _clause vector with the literals of the clause
 * \return the clause ID if the clause was actually added; -2 if the clause was a tautology; -1 if the clause was unit.
 * \throw UNSATException if an empty clause is added.
 */
int Formula::addClause(const Clause& _clause)
{
    if (_clause.empty()) {
        throw UNSATException("Trying to add an empty clause", this);
    }

    if (_clause.isTautology()) return -2;

    if (_clause.size() == 1) {
        pushUnit(_clause[0]);
        return -1;
    }

    unsigned int c_nr = 0;
    val_assert(clauses.size() == clause_sizes.size());

    // Try to recycle clause numbers where possible.
    if (deleted_clause_numbers.empty()) {
        clause_sizes.push_back(_clause.size());
        clauses.push_back(_clause);
        c_nr = clauses.size() - 1;
    } else {
        c_nr = deleted_clause_numbers.back();
        deleted_clause_numbers.pop_back();
        clause_sizes[c_nr] = _clause.size();
        clauses[c_nr] = _clause;
    }

    return addClauseToLists(c_nr);
}


/**
 * \brief Adds a clause to the formula.
 *
 * \note Calling this function is only allowed as long as none of
 *       the functions has been called which modify the formula
 *       (like unitPropagation(), findPure(), ...)
 * \param _clause vector with the literals of the clause
 * \return the clause ID if the clause was actually added; -2 if the clause was a tautology; -1 if the clause was unit.
 * \throw UNSATException if an empty clause is added.
 */
int Formula::addClause(Clause&& _clause)
{
    if (_clause.empty()) {
        throw UNSATException("Trying to add an empty clause", this);
    }

    if (_clause.isTautology()) return -2;

    if (_clause.size() == 1) {
        pushUnit(_clause[0]);
        return -1;
    }

    unsigned int c_nr = 0;
    val_assert(clauses.size() == clause_sizes.size());

    // Try to recycle clause numbers where possible.
    if (deleted_clause_numbers.empty()) {
        clause_sizes.push_back(_clause.size());
        clauses.push_back(std::move(_clause));
        c_nr = clauses.size() - 1;
    } else {
        c_nr = deleted_clause_numbers.back();
        deleted_clause_numbers.pop_back();
        clause_sizes[c_nr] = _clause.size();
        clauses[c_nr] = std::move(_clause);
    }

    return addClauseToLists(c_nr);
}


/**
 * \brief Adds a clause to the formula.
 *
 * \note Calling this function is only allowed as long as none of
 *       the functions has been called which modify the formula
 *       (like unitPropagation(), findPure(), ...)
 * \param _clause vector with the literals of the clause
 * \param needs_sorting if true, the clause is sorted and duplicate literals are removed.
 * \pre If needs_sorting is false, the caller has to guarantee that the literals are
 *      ordered in increasing order and that no literal appears more than once.
 * \param check_subsumption if true, it is checked whether the clause subsumes other clauses in database
 * \return the clause ID if the clause was actually added; -1 if the clause was a tautology.
 * \throw UNSATException if an empty clause is added.
 */
int Formula::addClause(std::vector<Literal>&& _clause, bool needs_sorting, bool check_subsumption, ClauseStatus status)
{
    if (_clause.empty()) {
        throw UNSATException("Trying to add an empty clause", this);
    }

    if (_clause.size() == 1) {
        pushUnit(_clause[0]);
        return -1;
    }

    unsigned int c_nr = 0;
    val_assert(clauses.size() == clause_sizes.size());

    // Try to recycle clause numbers where possible.
    if (deleted_clause_numbers.empty()) {
        clause_sizes.push_back(_clause.size());
        clauses.emplace_back(std::move(_clause), needs_sorting, status);
        c_nr = clauses.size() - 1;
    } else {
        c_nr = deleted_clause_numbers.back();
        deleted_clause_numbers.pop_back();
        clause_sizes[c_nr] = _clause.size();
        clauses[c_nr] = Clause(std::move(_clause), needs_sorting, status);
    }

    return addClauseToLists(c_nr, check_subsumption);
}


/**
 * \brief Removes a clause from the formula.
 *
 * \param c_nr the ID of the clause
 * \note This function modifies Formula::occ_list and Formula::implications.
 *       Therefore Formula::removeClause may not be called while iterating over
 *       one of these lists.
 * \note The removed clause may not be accessed anymore.
 */
void Formula::removeClause(const unsigned int c_nr)
{
    val_assert(c_nr < clauses.size());
    if (clauseDeleted(c_nr)) {
        val_assert(clauses[c_nr].empty());
        return;
    }

    for (Literal lit: clauses[c_nr]) {
        // remove c_nr from occ_list[lit]:
        removeFromOccList(lit, c_nr);
    }

    if (clauses[c_nr].size() == 2) {
        // remove both implications
        removeImplication(negate(clauses[c_nr][0]), clauses[c_nr][1]);
        removeImplication(negate(clauses[c_nr][1]), clauses[c_nr][0]);
    }

    // clear the clause and free its number
    clauses[c_nr].clear();
    clauses[c_nr].setStatus(ClauseStatus::DELETED);
    clause_sizes[c_nr] = 0;
    clause_modified[c_nr] = true;
    deleted_clause_numbers.push_back(c_nr);
}


/**
 * \brief Removes all clauses which are marked as optional.
 * \return true if the formula was modified
 * \sa Formula::removeClause(unsigned int)
 */
bool Formula::removeOptionalClauses()
{
    unsigned int count = 0;

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseOptional(c_nr)) {
            removeClause(c_nr);
            ++count;
        }
    }

    return count > 0;
}


/**
 * \brief Removes the given literal from a clause.
 * \param c_nr the ID of the clause from this the literal is to be deleted
 * \param lit the literal to be deleted
 * \pre The literal has to be contained in the clause. Otherwise the
 *      result is undefined.
 * \return Returns true if clause was further reduced by universal reduction
 */
bool Formula::removeLiteral(const unsigned int c_nr, const Literal lit)
{
    val_assert(!clauseDeleted(c_nr));
    val_assert(std::find(clauses[c_nr].cbegin(), clauses[c_nr].cend(), lit) != clauses[c_nr].cend());

    auto& clause = clauses[c_nr];
    bool result = false;

    // If the clause is currently binary, it becomes unit.
    if (clause.size() == 2) {
        val_assert(clause[0] == lit || clause[1] == lit);
        if (clause[0] == lit) pushUnit(clause[1]);
        else pushUnit(clause[0]);
        removeClause(c_nr);
        return true;
    }

    // Remove the clause from the literal's occurrence list.
    removeFromOccList(lit, c_nr);

    // Remove the literal from the clause.
    clause.erase(std::remove(clause.begin(), clause.end(), lit), clause.end());
    clause.computeSignature();

    // Perform universal reduction
    if (setting.univ_reduction) result = universalReduction(clause, c_nr);

    // If the clause is now binary, add the implications.
    if (clause.size() == 2) {
        addImplication(negate(clause[0]), clause[1], c_nr);
        addImplication(negate(clause[1]), clause[0], c_nr);
    }

    clause_modified[c_nr] = true;
    clause_sizes[c_nr] = clause.size();

    return result;
}


/**
 * \brief Replace, in the whole formula, a literal by another one.
 *
 * The negated literal is replaced by the negated replacement, i.e.,
 * afterwards the formula does not contain var(lit) anymore.
 * \pre var(lit) != var(replacement)
 * \param lit the literal that is to be replaced
 * \param replacement the replacement of the literal
 */

void Formula::replaceLiteral(const Literal lit, const Literal replacement)
{
    replaceLiteralMono(lit, replacement);
    replaceLiteralMono(negate(lit), negate(replacement));
    removeVar(lit2var(lit));
    unitPropagation();
}

/**
 * \brief Replace a literal by another one in all clauses.
 *
 * \note The negated literal is not replaced!
 * \pre \f$var(lit) \neq var(replacement)\f$
 * \pre \f$var(replacement) \not\in clause\f$
 * \param lit the literal that is to be replaced
 * \param replacement the replacement literal of the literal `lit`
 */
void Formula::replaceLiteralMono(const Literal lit, const Literal replacement)
{
    val_assert(!varDeleted(lit2var(lit)));
    val_assert(lit2var(lit) != lit2var(replacement));

    const Literal neg_lit = negate(lit);
    const Literal neg_replacement = negate(replacement);

    // Remove all implications of ~lit
    for (auto impl: implications[neg_lit]) {
        removeImplication(negate(impl.getLiteral()), lit);
    }
    implications[neg_lit].clear();

    while (!occ_list[lit].empty()) {
        const unsigned int c_nr = occ_list[lit].back();
        clause_modified[c_nr] = true;
        occ_list[lit].pop_back();
        auto& clause = clauses[c_nr];
        bool skip = false;

        if (lit < replacement) {
            unsigned int l_pos = 0;
            // find the position of 'lit'
            while (clause[l_pos] != lit) ++l_pos;
            // copy all literals between lit and replacement one position to the left
            while (l_pos + 1 < clause.size() && clause[l_pos + 1] <= replacement) {
                clause[l_pos] = clause[l_pos+1];
                ++l_pos;
            }
            if (clause[l_pos] == replacement) {
                // The clause already contains the replacement
                // -> move all literals right of l_pos one position left and
                //    shorten the clause by one
                while (l_pos + 1 < clause.size()) {
                    clause[l_pos] = clause[l_pos + 1];
                    ++l_pos;
                }

                // shrink the clause length by 1
                clause.resize(clause.size() - 1);

                // if the clause has become binary, add to implication lists
                if (clause.size() == 2) {
                    addImplication(negate(clause[0]), clause[1], c_nr);
                    addImplication(negate(clause[1]), clause[0], c_nr);
                }

                // if the clause has become unit, propagate it.
                if (clause.size() == 1) {
                    pushUnit(clause[0]);
                    skip = true;
                }
            } else {
                clause[l_pos] = replacement;

                // check for tautology
                if (l_pos > 0 && clause[l_pos - 1] == neg_replacement) skip = true;
                else if (l_pos < clause.size() - 1 && clause[l_pos + 1] == neg_replacement) skip = true;

                if (!skip) {
                    occ_list[replacement].push_back(c_nr);
                    if (clause.size() == 2) {
                        addImplication(negate(clause[0]), clause[1], c_nr);
                        addImplication(negate(clause[1]), clause[0], c_nr);
                    }
                }
            }
        } else {
            // lit > replacement
            int l_pos = clause.size() - 1;
            while (clause[l_pos] > lit) --l_pos;
            while (l_pos > 0 && clause[l_pos - 1] >= replacement) {
                clause[l_pos] = clause[l_pos - 1];
                --l_pos;
            }

            if (clause[l_pos] == replacement) {
                // The clause already contained the replacement -> shorten it
                while (l_pos < (int)clause.size() - 1) {
                    clause[l_pos] = clause[l_pos + 1];
                    ++l_pos;
                }

                // shrink the clause length by 1
                clause.resize(clause.size() - 1);

                // if the clause has become binary, add to implication lists
                if (clause.size() == 2) {
                    addImplication(negate(clause[0]), clause[1], c_nr);
                    addImplication(negate(clause[1]), clause[0], c_nr);
                }

                // if the clause has become unit, propagate it.
                if (clause.size() == 1) {
                    pushUnit(clause[0]);
                    skip = true;
                }
            } else {
                clause[l_pos] = replacement;

                // check for tautology
                if (l_pos > 0 && clause[l_pos - 1] == neg_replacement) skip = true;
                else if (l_pos < (int)clause.size() - 1 && clause[l_pos + 1] == neg_replacement) skip = true;

                if (!skip) {
                    occ_list[replacement].push_back(c_nr);
                    if (clause.size() == 2) {
                        addImplication(negate(clause[0]), clause[1], c_nr);
                        addImplication(negate(clause[1]), clause[0], c_nr);
                    }
                }
            }
        }

        if (skip) {
            removeClause(c_nr);
            clause_sizes[c_nr] = 0;
        } else {
            if (setting.univ_reduction) universalReduction(clause, c_nr);
            clause.computeSignature();
            clause_sizes[c_nr] = clause.size();
            // clause can be removed/identified as unit in universalReduction()
            if (clause.size() != 0) {
                const unsigned int num_subsumed = isBackwardSubsuming(clause, c_nr);
                if (num_subsumed > 0 && setting.verbosity > 2) {
                    std::cout << "c " << __FUNCTION__ << " removed " << num_subsumed << " subsumed clauses.\n";
                }
            }
        }
    }

    val_assert(occ_list[lit].empty());
    val_assert(implications[negate(lit)].empty());
}


/**
 * \brief Resets the formula and clears all the data.
 *
 * Afterwards, the list of variables and clauses as well as
 * all auxiliary data structures (implications, occurrence lists)
 * are empty. The statistics variables are reset to 0.
 */
void Formula::reset()
{
    val_assert(prefix != nullptr);
    prefix->clear();
    clauses.clear();
    clause_modified.clear();
    occ_list.clear();
    implications.clear();
    deleted_clause_numbers.clear();
    deleted_var_numbers.clear();
    unit_stack.clear();
    assignment.clear();
    dont_touch.clear();
    variable_score.clear();
    clause_sizes.clear();
    candidates.clear();
    blocked_candidates.clear();
    _seen.clear();
    _seen2.clear();

    stat_unit_pure = 0;
    stat_univ_reduction = 0;
    stat_univ_expansion = 0;
    stat_bce = 0;
    stat_hte = 0;
    stat_hse = 0;
    stat_impl_chains = 0;
    stat_contradictions = 0;
    stat_subsumption = 0;
    stat_resolution = 0;
    stat_selfsubsuming_resolution = 0;
    stat_equiv = 0;
    stat_hidden_equiv = 0;
    stat_hidden_unit = 0;
    stat_equiv_gates = 0;
    stat_substitution = 0;
    stat_unit_by_sat = 0;
    stat_impl_by_sat = 0;
    stat_sat_calls = 0;
    stat_prepro_loops = 0;

    unit_sat_time.reset();
    impl_sat_time.reset();
    incomplete_sat_time.reset();
    impl_chain_time.reset();
    equiv_time.reset();
    contra_time.reset();
    univ_reduction_time.reset();
    univ_expansion_time.reset();
    bce_time.reset();
    hse_time.reset();
    gate_detection_time.reset();
    gate_sub_time.reset();
    gate_rewrite_time.reset();
    resolution_time.reset();
    self_subsumption_time.reset();
    subsumption_time.reset();
    dependency_time.reset();
    prepro_time.reset();
}


/**
 * \brief Creates a copy of a given variable.
 *
 * The copy has the same dependencies as the copied variable.
 * \return the index of the copy
 */
Variable Formula::copyVar(const Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(!varDeleted(var));

    const Variable new_var = nextVar();
    val_assert(minVarIndex() <= new_var && new_var <= maxVarIndex());
    val_assert(varDeleted(new_var));
    prefix->makeCopy(new_var, var);
    return new_var;
}


/**
 * \brief Checks if start_lit implies target_var or NOT(target_var) taking transitivity into account.
 *
 * \return a pair (a,b) such that a = true means start_lit implies target_var and
 *         b = true that start_lit implies NOT(target_var).
 */
std::pair<bool,bool> Formula::hasImplicationTransitive(Literal start_lit, Variable target_var) const
{
    val_assert(start_lit < implications.size());

    std::stack<Literal> front( {start_lit} );
    std::vector<bool> reached(implications.size(), false);
    reached[start_lit] = true;

    while (!front.empty()) {
        const Literal top = front.top();
        front.pop();
        for (BinaryClause succ: implications[top]) {
            const Literal lit = succ.getLiteral();
            if (!reached[lit]) {
                reached[lit] = true;
                front.push(lit);
            }
        }
    }
    return std::make_pair(reached[var2lit(target_var, false)], reached[var2lit(target_var, true)]);
}


/**
 * \brief Checks if the DQBF is actually a QBF with a linearly ordered quantifier prefix
 *
 * This is done by testing whether for the dependency sets \f$D_y\f$ and \f$D_{y'}\f$ of all
 * pairs \f$y,y'\f$ of existential variables either \f$D_y\subseteq D_{y'}\f$ or 
 * \f$D_{y'}\subseteq D_y\f$ holds.
 *
 * \todo Check if the signature approach (cf. subsumption checks) makes this
 *       procedure more efficient. A signature can be defined by hashing the
 *       the variables in the dependency set of an existential variable to
 *       the range 0...63 and setting the corresponding bit position in the
 *       signature to 1. If sig(prefix[i]) & ~sig(prefix[j]) != 0, then prefix[i]
 *       cannot be a subset of prefix[j]. However, since the dependency sets are
 *       typically larger than an average clause, this might not help much.
 */
bool Formula::isQBF() const noexcept
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() != PrefixType::DQBF || dqbf_prefix != nullptr);

    if (prefix->type() == PrefixType::QBF && qbf_prefix != nullptr && dqbf_prefix == nullptr) return true;
    return dqbf_prefix->isQBF();
}


/**
 * \brief If the current formula has an equivalent QBF prefix, this function constructs
 *        such a QBF prefix.
 * \pre This function requires that the DQBF has an equivalent QBF prefix.
 */
void Formula::convertToQBF()
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() == PrefixType::QBF || isQBF());

    if (prefix->type() == PrefixType::QBF && qbf_prefix != nullptr) return;

    QBFPrefix* new_prefix = dqbf_prefix->convertToQBF();
    delete prefix;
    qbf_prefix = new_prefix;
    prefix = new_prefix;
    dqbf_prefix = nullptr;
}


void Formula::initCandidateLists()
{
    blocked_candidates.clear();
    blocked_candidates.resize(clauses.size());
    for (unsigned c_nr = 0; c_nr != clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        if (!blocked_candidates.inHeap(c_nr) ) {
            blocked_candidates.insert(c_nr);
        }
    }
}

/**
 * \brief Counts occurences of all literals and stores it into `variable_score`
 */
void Formula::countOccurences()
{
    variable_score.resize(maxLitIndex() + 1, 0);

    for (Literal l = minLitIndex(); l <= maxLitIndex(); ++l) {
        variable_score[l] = occ_list[l].size();
    }
}

/**
 * \brief Counts occurences of all variables and stores it into `variable_score`
 */
void Formula::countOccurencesVar()
{
    variable_score.resize(maxVarIndex() + 1, 0);

    for (Variable v = minVarIndex(); v <= maxVarIndex(); ++v) {
        variable_score[v] = occ_list[var2lit(v)].size() + occ_list[negate(var2lit(v))].size();
    }
}

/**
 * \brief Counts implications of all variables and stores it into `variable_score`
 */
void Formula::countImplications()
{
    val_assert(variable_score.size() > maxLitIndex() );

    for (Literal l = minLitIndex(); l <= maxLitIndex(); ++l) {
        variable_score[l] = implications[l].size();
    }
}

/**
 * \brief Prints some statistics about the effectiveness of the preprocessor.
 */
void Formula::printStatistics(std::ostream& stream) const
{
    stream    << "c num_unit_pure.................= " << stat_unit_pure << std::endl
              << "c num_univ_reduction............= " << stat_univ_reduction << std::endl
              << "c num_univ_expansion............= " << stat_univ_expansion << std::endl
              << "c num_equiv.....................= " << stat_equiv << std::endl
              << "c num_blocked_clauses...........= " << stat_bce << std::endl
              << "c num_blocked_univ_literals.....= " << stat_ble << std::endl
              << "c num_added_blocked_literals....= " << stat_bla << std::endl
              << "c num_added_blocked_implications= " << stat_bia << std::endl
              << "c num_hidden_tautologies........= " << stat_hte << std::endl
              << "c num_hidden_subsumptions.......= " << stat_hse << std::endl
              << "c num_impl_chains...............= " << stat_impl_chains << std::endl
              << "c num_contradictions............= " << stat_contradictions << std::endl
              << "c num_hidden_equiv..............= " << stat_hidden_equiv << std::endl
              << "c num_hidden_unit...............= " << stat_hidden_unit << std::endl
              << "c num_substitution..............= " << stat_substitution << std::endl
              << "c num_rewritings................= " << stat_rewriting << std::endl
              << "c num_subsumption...............= " << stat_subsumption << std::endl
              << "c num_selfsubsuming_resolution..= " << stat_selfsubsuming_resolution << std::endl
              << "c num_resolution................= " << stat_resolution << std::endl
              << "c num_unit_by_sat...............= " << stat_unit_by_sat << std::endl
              << "c num_impl_by_sat...............= " << stat_impl_by_sat << std::endl
              << "c num_sat_calls.................= " << stat_sat_calls << std::endl
              << "c num_dep_schemes...............= " << stat_dep_schemes << std::endl
              << "c num_preprocessor_loops........= " << stat_prepro_loops << std::endl
              << std::setprecision(2) << std::fixed
              << "c time_univ_reduction...........= " << univ_reduction_time.read() << "s" << std::endl
              << "c time_univ_expansion...........= " << univ_expansion_time.read() << "s" << std::endl
              << "c time_equiv....................= " << equiv_time.read() << "s" << std::endl
              << "c time_hidden_equiv_contra......= " << hidden_equiv_contra_time.read() << "s" << std::endl
              << "c time_blocked_clauses..........= " << bce_time.read() << "s" << std::endl
              << "c time_hidden_subsumptions......= " << hse_time.read() << "s" << std::endl
              << "c time_impl_chains..............= " << impl_chain_time.read() << "s" << std::endl
              << "c time_contradictions...........= " << contra_time.read() << "s" << std::endl
              << "c time_substitution.............= " << gate_sub_time.read() << "s" << std::endl
              << "c time_rewriting................= " << gate_rewrite_time.read() << "s" << std::endl
              << "c time_subsumption..............= " << subsumption_time.read() << "s" << std::endl
              << "c time_selfsubsuming_resolution.= " << self_subsumption_time.read() << "s" << std::endl
              << "c time_resolution...............= " << resolution_time.read() << "s" << std::endl
              << "c time_unit_by_sat..............= " << unit_sat_time.read() << "s" << std::endl
              << "c time_impl_by_sat..............= " << impl_sat_time.read() << "s" << std::endl
              << "c time_incomplete_sat_checks....= " << incomplete_sat_time.read() << "s" << std::endl
              << "c time_dep_schemes..............= " << dependency_time.read() << "s" << std::endl
              << "c time_gate_detection...........= " << gate_detection_time.read() << "s" << std::endl
              << "c time_preprocessing............= " << prepro_time.read() << "s" << std::endl;
}

std::ostream& operator<<(std::ostream& stream, const Gate& gate)
{
    stream << lit2dimacs(gate.output_literal) << " = ";
    if (gate.type == GateType::AND_GATE) stream << "AND( ";
    else if (gate.type == GateType::XOR_GATE) stream << "XOR( ";
    else stream << "UNKNOWN( ";
    for (Literal lit: gate.input_literals) stream << lit2dimacs(lit) << " ";
    stream << ")";

    return stream;
}




} // end namespace hqspre
