#include <vector>
#include <iostream>
#include <limits>
#include <algorithm>
#include <map>
#include "formula.hpp"
#include "process_limits.hpp"

/**
 * \file formula_resolution.cpp
 * \brief Implementation of resolution-based operations on formulas
 * \author Ralf Wimmer
 * \author Sven Reimer
 * \date 2016
 */


namespace hqspre {

/**
 * \brief Checks if an existential variable can be eliminated by resolution.
 *
 * This is the case if none of the resolvents w.r.t. the given variable
 * is a tautology because of a universal variable that is right of the
 * eliminated variable in the quantifier prefix.
 * \pre The formula must be a QBF
 * \return true iff the variable can be eliminated 
 */
bool Formula::isResolvable(const Variable var) const
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    if (!isExistential(var)) return false;
    if (prefix->inRMB(var) && (!setting.preserve_gates || !gate_output[var])) return true;

    return false;
}

/**
 * \brief Determines which variables may be eliminated using resolution.
 *
 * A variable \f$ x\f$ may be eliminated if
 * - it is a Tseitin variable (i.e., encodes a gate output)
 * - if the dependency sets of all literals the literal \f$ x\f$ appear with in the
 *   same clause are a subset of \f$x\f$'s dependency set.
 * - the same as the second condition only for \f$\neg x\f$.
 * \return a vector of resolvable variables
 * \param gates_only if true then only gate outputs are determined. The other two possibilities are ignored.
 */
std::vector<Variable> Formula::getResolvableVariables() const
{
    if (!setting.preserve_gates) {
        const auto& rmb = prefix->getRMB();
        if (!rmb.empty() && isExistential(*(rmb.begin()))) {
            return std::vector<Variable>(rmb.cbegin(), rmb.cend());
        } else {
            return std::vector<Variable>();
        }
    }

    std::vector<Variable> result;
    result.reserve(maxVarIndex() + 1);

    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isExistential(var) && isResolvable(var)) result.push_back(var);
    }

    if (setting.verbosity > 2) {
        std::cout << "c " << __FUNCTION__ << "() found " << result.size() << " resolvable variables." << std::endl;
    }

    return result;
}


/**
 * \brief Computes the costs of eliminating an existential variable by resolution.
 * \param var the variable to be eliminated
 * \return the number of literals by which the formula length increases.
 */
int Formula::computeResolutionCosts(const Variable var) const
{
    const Literal lit_pos = var2lit(var, false);
    const Literal lit_neg = var2lit(var, true);

    const int opv = occ_list[lit_pos].size();
    const int onv = occ_list[lit_neg].size();

    if (opv == 0 && onv == 0) return std::numeric_limits<int>::max();

    process_limit.decreaseLimitBy(occ_list[lit_pos].size());
    process_limit.decreaseLimitBy(occ_list[lit_neg].size());

    int spv = 0;
    for (unsigned int c_nr: occ_list[lit_pos]) spv += clauses[c_nr].size();

    int snv = 0;
    for (unsigned int c_nr: occ_list[lit_neg]) snv += clauses[c_nr].size();

    val_assert(opv + onv > 0);
    val_assert(spv >= 2 * opv);
    val_assert(snv >= 2 * onv);

    const int cost = opv * ( snv - onv ) + onv * ( spv - opv ) - spv - snv;
    return cost;
}


/**
 * \brief Eliminates an existential variable by resolution
 *
 * The caller has to check if elimination by resolution is allowed.
 * This is the case if (1) the eliminated variable is a gate output,
 * (2) the eliminated variable depends on at least the same variables
 * as all variable it appears with positively in the same clause,
 * (3) the same as 2, but in clauses with positive occurrence of the
 * eliminated variable.
 *
 * The function performs universal reduction on the resolvents before
 * adding them.
 * \param[in] var the variable that should be eliminated by resolution
 * \param[out] recalc_lits collection of literals whose costs have to be updated
 */
void Formula::eliminateVariableE(Variable var, std::set<Variable>& recalc_vars)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(isExistential(var));
    val_assert(isResolvable(var));
    val_assert(recalc_vars.empty());

    if (setting.verbosity > 2) {
        std::cout << "c Length before resolving variable " << var << ": " << numLiterals();
    }

    const Literal lit_pos = var2lit(var, false);
    const Literal lit_neg = var2lit(var, true);

    for (const unsigned int clause_pos: occ_list[lit_pos]) {
        // Ignore the optional clauses
        if (clauseDeleted(clause_pos)) continue;
        if (clauseOptional(clause_pos)) continue;

        process_limit.decreaseLimitBy(3, occ_list[lit_neg].size());

        for (const unsigned int clause_neg: occ_list[lit_neg]) {
            // Ignore the optional clauses
            if (clauseDeleted(clause_pos)) break;
            if (clauseDeleted(clause_neg)) continue;
            if (clauseOptional(clause_neg)) continue;

            process_limit.decreaseLimitBy(3, clauses[clause_pos].size() + clauses[clause_neg].size());
            const auto resolvent = resolve(clauses[clause_pos], clauses[clause_neg], var);

            if (!resolvent.isTautology()) {
                // update costs for all literals in newly introduced clauses
                auto pos = recalc_vars.begin();
                for (Literal lit: resolvent) {
                    pos = recalc_vars.insert(pos, lit2var(lit));
                }
                addClause(std::move(resolvent));
            }
        }
    }

    process_limit.decreaseLimitBy(2, occ_list[lit_neg].size() + occ_list[lit_pos].size());

    // Delete all clauses (incl. the optional ones) that contain the eliminated variable
    while (!occ_list[lit_pos].empty()) {
        // update costs for all literals in removed clauses
        const Clause& clause = clauses[occ_list[lit_pos].front()];
        auto pos = recalc_vars.begin();
        for (Literal lit: clause) {
            pos = recalc_vars.insert(pos, lit2var(lit));
        }
        removeClause(occ_list[lit_pos].front());
    }

    while (!occ_list[lit_neg].empty()) {
        // update costs for all literals in removed clauses
        const Clause& clause = clauses[occ_list[lit_neg].front()];
        auto pos = recalc_vars.begin();
        for (Literal lit: clause) {
            pos = recalc_vars.insert(pos, lit2var(lit));
        }
        removeClause(occ_list[lit_neg].front());
    }
    removeVar(var);

    // Propagate possible new units
    unitPropagation();

    if (setting.verbosity > 2) {
        std::cout << " length after: " << numLiterals() << std::endl;
    }

    ++stat_resolution;
}


/**
 * \brief Tries to eliminate existential variables by resolution.
 *
 * First we check, which variables can be eliminated, see
 * Formula::getResolvableVariables(bool) const. Since this is
 * rather expensive if done completely, we first restrict ourselves
 * to gate detection. Only if all gate outputs (for which this
 * is feasible) have been eliminated, we switch to a complete
 * determination of resolvable variables. Variables are eliminated
 * as long as the cost of their eliminated is less than a constant
 * (currently: 0).
 * \return true if the formula was modified.
 */
bool Formula::applyResolution()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer resolution(resolution_time);
    process_limit.setLimit(PreproMethod::RESOLUTION);

    gateDependencies(DependencyOperation::ADD);

    unsigned int count = 0;
    unsigned int old_size = 0;
    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (!clauseDeleted(c_nr)) old_size += clauses[c_nr].size();
    }
    unsigned int new_size = old_size;

    std::set<Variable> recalc_vars;
    variable_score.resize(maxVarIndex() + 1, 0);
    candidates.clear();
    candidates.resize(maxVarIndex() + 1);

    const auto resolvable_vars = getResolvableVariables();
    if (setting.verbosity > 2) {
        std::cout << "c " << __FUNCTION__ << " " << resolvable_vars.size() << " resolvable variables.\n";
    }

    for (Variable var: resolvable_vars) {
        variable_score[var] = computeResolutionCosts(var);
        candidates.insert(var);
    }

    while (!candidates.empty()) {

        if (interrupt) break;

        if (process_limit.reachedLimit()) {
            if (setting.verbosity > 1 ) {
                std::cout << "c terminate " << __FUNCTION__ << " due to process limit" << std::endl;
            }
            break;
        }

        const Variable next_var = candidates.top();

        if (variable_score[next_var] > setting.max_resolution_cost ) {
		  // Candidate list is sorted -> if we found a candidate which is too expensive, every remaining is too expensive
		  break;
		}
		  
		if( varDeleted(next_var) || !isResolvable(next_var)) {
            // skip variables that are already deleted or not resolvable
            continue;
        }

        eliminateVariableE(next_var, recalc_vars);

        if (stat_resolution % 100 == 0) fastPreprocess();

        if (setting.verbosity > 2) {
            std::cout << "c " << __FUNCTION__ << "() eliminated variable " << next_var << ",  costs = " << variable_score[next_var] << std::endl;
        }

        if (interrupt) break;

        // now update costs
        for (Variable var : recalc_vars ) {
            if ( var != next_var && isExistential(var) )
            {
                // If out-of-order resolution is enabled, check
                // if the variable can still be eliminated.
                const bool resolvable = isResolvable(var);
                if (!resolvable && candidates.inHeap(var)) {
                    candidates.remove(var);
                    continue;
                }

                if (resolvable) {
                    const int old_cost = variable_score[var];
                    variable_score[var] = computeResolutionCosts(var);
                    // variable might be removed earlier from heap -> reinsert
                    if (!candidates.inHeap(var)) {
                        candidates.insert(var);
                    }
                    // Update heap only if new costs are lower
                    else if (old_cost > variable_score[var] )
                    {
                        candidates.update(var);
                    }
                }
            }
        }
        recalc_vars.clear();

        ++count;
    }

    if (setting.verbosity > 1) {
        new_size = 0;
        for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
            if (!clauseDeleted(c_nr)) new_size += clauses[c_nr].size();
        }
        std::cout << "c resolution eliminated " << count << " variables" << std::endl; 
    }

    return count > 0;
}

  /**
 * \brief Checks whether the variable `var` can be eliminated as part of an implication chain
 *
 * This function eliminates the implication chain.
 * \return the replaced literal if the variable was eliminated, otherwise 0
 * \sa Formular::findImplicationChains()
 */
Literal Formula::checkImplicationChain(const Literal lit)
{
    const Variable var = lit2var(lit);

    if (!isExistential(var)) return 0;
    if (setting.preserve_gates && gate_output[var]) return 0;
    if (occ_list[lit].size() != 1) return 0;
    const Literal neg_lit = negate(lit);
    if (implications[neg_lit].size() != 1) return 0;

    const Literal other_lit = (implications[neg_lit].begin())->getLiteral();
    if (!dependenciesSubset(lit2var(other_lit), var)) return 0;

    if (setting.verbosity > 2) {
        std::cout << "c " << __FUNCTION__ << "() replaced literal " << lit2dimacs(neg_lit) << " by literal " << lit2dimacs(other_lit) << std::endl;
    }

    removeClause(occ_list[lit].front());
    replaceLiteral(neg_lit, other_lit);

    val_assert(occ_list[lit].empty());
    val_assert(occ_list[neg_lit].empty());

    ++stat_impl_chains;

    unitPropagation();
    return other_lit;
}


/**
 * \brief Finds and eliminates implication chains.
 *
 * This is a special case of variable elimination by resolution,
 * where the eliminated variable occurs positively (or negatively)
 * only in a single clause.
 * \return true if the formula was modified.
 */
bool Formula::findImplicationChains()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer impl_chain(impl_chain_time);

    const unsigned int old_stat_impl_chains = stat_impl_chains;

    for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit) {
        if (interrupt) break;
        checkImplicationChain(lit);
    }

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << "() replaced " << (stat_impl_chains - old_stat_impl_chains) << " variables." << std::endl;
    }
    return stat_impl_chains > old_stat_impl_chains;
}

} // end namespace hqspre
