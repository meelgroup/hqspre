#include <vector>
#include <map>
#include <iostream>
#include <limits>
#include <stack>
#include "aux.hpp"
#include "formula.hpp"
#include <antom/antom.hpp>

/**
 * \file formula_univ_expand.cpp
 * \brief Implementation of universal expansion
 * \author Ralf Wimmer
 * \date 2016
 */

namespace hqspre {

/**
 * \brief Tries to estimate the costs of universal expansion
 *
 * The function returns as the first entry of the return value the
 * number of existential variables that need to be doubled. The second
 * entry is the number of additional clauses after expansion.
 * These numbers are over-approximations as some of the variables might
 * be unit or clauses tautologies.
 */
std::pair<int,int> Formula::computeExpansionCosts(Variable uvar) const
{
    int result_vars = 0; // number of additional existential variables
    int result_clauses = 0; // number of additional clauses

    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isExistential(var) && depends(var, uvar)) ++result_vars;
    }

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr) || clauseOptional(c_nr)) continue;
        bool contains_uvar = false;
        bool to_copy = false;

        for (Literal lit: clauses[c_nr]) {
            const Variable var = lit2var(lit);
            if (var == uvar) contains_uvar = true;
            else if (isExistential(var) && depends(var, uvar)) to_copy = true;
        }
        if (to_copy && !contains_uvar) result_clauses += 1;
    }

    return std::make_pair(result_vars, result_clauses);
}

void Formula::markTransitiveUnits(std::stack<Literal>& units, std::vector<bool>& marked)
{
    while (!units.empty()) {
        const Literal top = units.top();
        units.pop();
        for (BinaryClause succ: implications[top]) {
            const Literal lit = succ.getLiteral();
            if (!marked[lit]) {
                marked[lit] = true;
                units.push(lit);
            }
        }
    }
}

/**
 * \brief Tries to estimate the costs of universal expansion
 *
 * The function returns difference of total literals of the formula
 * This number is an over-approxmimation as further units and subsumptions
 * are not taken into account.
 */
int Formula::computeExpansionCosts2(Variable uvar, const std::set<Variable>& pseudo_deps)
{
    int result_lits = 0; // number of additional literals

    // mark new units
    std::vector<bool> new_units_pos(maxLitIndex() + 1, false);
    std::vector<bool> new_units_neg(maxLitIndex() + 1, false);

    std::stack<Literal> front;

    // Binary clause becomes unit after expansion, mark new units
    for (BinaryClause bin_clause : implications[var2lit(uvar)] ) {
        new_units_neg[bin_clause.getLiteral()] = true;
        front.push(bin_clause.getLiteral());
    }

    // Now mark also transitive units
    markTransitiveUnits(front, new_units_neg);

    for (BinaryClause bin_clause : implications[negate(var2lit(uvar))] ) {
        new_units_pos[bin_clause.getLiteral()] = true;
        front.push(bin_clause.getLiteral());
    }

    // Now mark also transitive units
    markTransitiveUnits(front, new_units_pos);

    // Now determine and mark pseudo dependencies
    std::vector<bool> is_pseudo_dep(maxVarIndex() + 1, false);

    for (Variable var : pseudo_deps) {
        is_pseudo_dep[var] = true;
    }

    bool to_copy = false;
    bool contains_uvar_pos = false;
    bool contains_uvar_neg = false;
    bool pos_satisfied = false;
    bool neg_satisfied = false;
    unsigned int pos_clause_size = 0;
    unsigned int neg_clause_size = 0;

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        if (clauseOptional(c_nr)) {
            result_lits -= clauses[c_nr].size();
            continue;
        }

        to_copy = false;
        contains_uvar_pos = false;
        contains_uvar_neg = false;
        pos_satisfied = false;
        neg_satisfied = false;
        pos_clause_size = clauses[c_nr].size();
        neg_clause_size = pos_clause_size;

        // Assume clause will be deleted
        result_lits -= pos_clause_size;

        process_limit.decreaseLimitBy(6, clauses[c_nr].size());

        for (Literal lit: clauses[c_nr]) {
            const Variable var = lit2var(lit);
            if (var == uvar) {
                contains_uvar_pos = isPositive(lit);
                contains_uvar_neg = !contains_uvar_pos;
                continue;
            }
            // we have to copy each clause where an existential literal exists which depends on "uvar"
            else if (isExistential(var) && depends(var, uvar) && !is_pseudo_dep[var]) {
                to_copy = true;
            }

            // lit will be unit in positive part of expansion
            // -> clause will be satisfied in positive expansion part
            if (new_units_pos[lit]) {
                pos_satisfied = true;
            }
            // ~lit will be unit in positive expansion
            // -> literal will be deleted in positive expansion part
            else if (new_units_pos[negate(lit)]) {
                --pos_clause_size;
            }

            // lit will be unit in negative part of expansion
            // -> clause will be satisfied in negative expansion part
            if (new_units_neg[lit]) {
                neg_satisfied = true;
            }
            // ~lit will be unit in negative expansion
            // -> literal will be deleted in negative expansion part
            else if (new_units_neg[negate(lit)]) {
                --neg_clause_size;
            }
        }

        // expanding universal var will be deleted in positive expansion
        if (contains_uvar_pos) {
            --pos_clause_size;
            // Binary clause containing expanding var will be deleted after expansion
            if (pos_clause_size == 1 || pos_satisfied) {
                pos_clause_size = 0;
            }
            result_lits += pos_clause_size;
        }
        // expanding universal var will be deleted in negative expansion
        else if (contains_uvar_neg) {
            --neg_clause_size;
            // Binary clause containing expanding var will be deleted after expansion
            if (neg_clause_size == 1 || neg_satisfied) {
                neg_clause_size = 0;
            }
            result_lits += neg_clause_size;
        }
        // clause does not contain any universal literal
        // -> will be possibly copied
        else {
            // Reset clause size in case clause will be satisfied
            if (pos_satisfied) pos_clause_size = 0;
            if (neg_satisfied) neg_clause_size = 0;

            result_lits += pos_clause_size;
            // We have to copy the clause
            if (to_copy && !contains_uvar_neg) {
                result_lits += neg_clause_size;
            }
        }
    }

    return result_lits;
}

/**
 * \brief Applies universal expansion to those universal variables which can cheaply be eliminated.
 * \return True if the formula was modified.
 */
bool Formula::applyUniversalExpansion()
{
    if (prefix->type() == PrefixType::DQBF) return applyUniversalExpansionDQBF();

    if (setting.verbosity > 0) std::cout << "c " << __FUNCTION__ << "()\n";
    int count = 0;
    if (numUVars() <= 6) {
        const unsigned int old_num_clauses = numClauses();
        for (Variable uvar = minVarIndex(); uvar <= maxVarIndex(); ++uvar) {
            if (interrupt) break;

            if (isUniversal(uvar)) {
                eliminateVariableU(uvar);
                ++count;
            }
            if (numClauses() > 2 * old_num_clauses) break;
        }
        if (setting.verbosity > 1) {
            std::cout << "c " << __FUNCTION__ << "() expanded " << count << " universal variables.\n";
        }
        return count > 0;
    }

    if (prefix->type() == PrefixType::QBF && count < 30) {
        const unsigned int old_size = numLiterals();
        std::set<Variable> pseudo_deps;
        for (int level = qbf_prefix->getMaxLevel(); level >= 0; --level) {
            if (interrupt) break;
            if (qbf_prefix->getLevelQuantifier(level) != VariableStatus::UNIVERSAL) continue;

            const auto& block = qbf_prefix->getVarBlock(level);
            if (block.size() > 20) continue;

            while (!block.empty()) {
                if (numLiterals() > 1.5 * old_size) break;
                int next_var = -1;
                int min_cost = std::numeric_limits<int>::max();
                int varcost = 0;
                for (Variable uvar: block) {
                    if (interrupt) break;
                    auto cost = computeExpansionCosts(uvar);
                    sstdQuadDep(uvar, true, true, &pseudo_deps);
                    cost.first -= pseudo_deps.size();
                    pseudo_deps.clear();
                    varcost = cost.first;
                    if (cost.second < min_cost) { next_var = uvar; min_cost = cost.second; }
                }
                if (interrupt) break;

                if (next_var > 0 && varcost < 20 && min_cost < 100) {
                    eliminateVariableU(next_var);
                    applyResolution();
                    ++count;
                } else break;
            }
        }

        if (setting.verbosity > 1) {
            std::cout << "c " << __FUNCTION__ << "() expanded " << count << " universal variables.\n";
        }

        return count > 0;
    }

    return false;
}

bool Formula::applyUniversalExpansion2()
{
    if (prefix->type() == PrefixType::DQBF) return applyUniversalExpansionDQBF();

    if (setting.verbosity > 1) std::cout << "c " << __FUNCTION__ << "()\n";

    ScopeTimer univ_expansion(univ_expansion_time);
    if (prefix->type() == PrefixType::QBF) {

    unsigned int count = 0;

    candidates.resize(maxVarIndex() + 1);

    // All universal variables and its pseudo dependencies
    std::vector<std::set< Variable > > var_candidates(maxVarIndex()+1);

    // collect all universal variables
    for (unsigned int i = 0; i <= qbf_prefix->getMaxLevel(); ++i) {
        if (interrupt) break;
        // ERROR: formula k_dum_n-12.qdimacs, settings --rewrite 1 --bce 1 , blocks.size()==0, get assert fault
        for (Variable var : qbf_prefix->getVarBlock(i)) {
            if (isExistential(var)) break;
                std::set<Variable> pseudo_deps;
                //std::cout << "calc dep scheme for var " << var << std::endl;
                //sstdQuadDep(var, true, true, &pseudo_deps);
                var_candidates[var] = pseudo_deps;
            }
        }

        // maximum formula size after expansion
        if (setting.max_expansion_size == 0) {
            // set fixed value in first call.
            setting.max_expansion_size = numLiterals() << 1;
        }


        while (true) {
            if (interrupt) break;

			if (numUVars() <= 6) {
			  const unsigned int old_num_clauses = numClauses();
			  for (Variable uvar = minVarIndex(); uvar <= maxVarIndex(); ++uvar) {
				if (isUniversal(uvar)) {
				  eliminateVariableU(uvar);
				  ++count;
				}
				if (numClauses() > 2 * old_num_clauses) break;
			  }

			  if (numUVars() == 0) {
				return count>0;
			  }
			}

			unsigned int current_count = count;
			unsigned int literals = numLiterals();
			std::set<Variable> pseudo_deps;
			// Now try to remove a whole quantifier level
			for (int level = qbf_prefix->getMaxLevel(); level >= 0; --level) {
			  // Exit routine if we expand our maximal expansion size
			  if (literals > setting.max_expansion_size ) {
				if (setting.verbosity > 1) {
				  std::cout << "c " << __FUNCTION__ << "() expanded " << count << " universal variables.\n";
				}
				return count > 0;
			  }

			  if (qbf_prefix->getLevelQuantifier(level) != VariableStatus::UNIVERSAL) continue;

			  const auto& block = qbf_prefix->getVarBlock(level);
			  if (block.size() > 20) continue;
			  if (setting.verbosity > 2) {
				std::cout << "c " << __FUNCTION__ << " removing quantifier level " << level << " with " << block.size() << " variables " << std::endl;
			  }

			  unsigned int old_size = literals;
			  while (!block.empty()) {
				int next_var = -1;
				int min_cost = std::numeric_limits<int>::max();
				for (Variable uvar: block) {
				  // sstdQuadDep(uvar, true, true, &pseudo_deps);
				  const int cost = computeExpansionCosts2(uvar, pseudo_deps);
				  pseudo_deps.clear();
				  if (cost < min_cost) { next_var = uvar; min_cost = cost; }
				}

				eliminateVariableU(next_var);
				if (interrupt) break;
				applyResolution();
				literals = numLiterals();
				++count;
				if (literals > 1.5 * old_size) break;
			  }

			  if (block.empty()) {
				updateVars();
				level = qbf_prefix->getMaxLevel();
			  }
			}
			// We have done nothing -> break routine
			if (count == current_count) break;
			if (interrupt) break;
		}
        if (setting.verbosity > 1) {
            std::cout << "c " << __FUNCTION__ << "() expanded " << count << " universal variables.\n";
        }
        return count > 0;
    }
    return false;
}



bool Formula::applyUniversalExpansionDQBF()
{
    val_assert(prefix->type() == PrefixType::DQBF);
    val_assert(dqbf_prefix != nullptr);

    if (setting.verbosity > 1) std::cout << "c " << __FUNCTION__ << "()\n";

    antom::Antom antom;
    std::vector<Variable> var1_minus_var2;
    std::vector<Variable> var2_minus_var1;
    antom.setMaxIndex(maxVarIndex() + 100);
    Variable current = maxVarIndex() + 1;
    std::vector<Literal> bin_clause(2,0);
    std::vector<Literal> clause;

    // Add hard constraints: eliminate all 2-cycles
    for (Variable var1 = minVarIndex(); var1 <= maxVarIndex(); ++var1) {
        if (!isExistential(var1) || prefix->inRMB(var1)) continue;
        for (Variable var2 = var1 + 1; var2 <= maxVarIndex(); ++var2) {
            if (!isExistential(var2) || prefix->inRMB(var2)) continue;
            if (dependenciesSubset(var1, var2) || dependenciesSubset(var2, var1)) continue;
            var1_minus_var2.clear();
            var2_minus_var1.clear();
            const auto& dep1 = dqbf_prefix->getDependencies(var1);
            const auto& dep2 = dqbf_prefix->getDependencies(var2);
            two_sided_difference(dep1.cbegin(), dep1.cend(), dep2.cbegin(), dep2.cend(), std::back_inserter(var1_minus_var2), std::back_inserter(var2_minus_var1));
            val_assert(!var1_minus_var2.empty() && !var2_minus_var1.empty());
            const Variable edge1_2 = current++;
            const Variable edge2_1 = current++;

            // Eliminate either "edge1" or "edge2"
            bin_clause[0] = var2lit(edge1_2);
            bin_clause[1] = var2lit(edge2_1);
            antom.addClause(bin_clause);

            // edge1
            clause.clear();
            bin_clause[0] = var2lit(edge1_2, true);
            for (Variable uvar: var1_minus_var2) {
                bin_clause[1] = var2lit(uvar, false);
                antom.addClause(bin_clause);
                clause.push_back(var2lit(uvar, true));
            }
            clause.push_back(var2lit(edge1_2, false));
            antom.addClause(clause);

            // edge2
            clause.clear();
            bin_clause[0] = var2lit(edge2_1, true);
            for (Variable uvar: var2_minus_var1) {
                bin_clause[1] = var2lit(uvar, false);
                antom.addClause(bin_clause);
                clause.push_back(var2lit(uvar, true));
            }
            clause.push_back(var2lit(edge2_1, false));
            antom.addClause(clause);
        }
    }

    // Add soft clauses
    clause.resize(1, 0);
    for (Variable uvar = minVarIndex(); uvar <= maxVarIndex(); ++uvar) {
        if (isUniversal(uvar)) {
            clause[0] = var2lit(uvar, false);
            antom.addSoftClause(clause);
        }
    }

    // Solve and determine optimal solution:
    unsigned int optimum = 0;
    const auto result = antom.maxSolve(optimum, 1);
    if (result != ANTOM_SAT) {
        if (setting.verbosity > 1) { std::cout << "c Antom could not find a solution for universal expansion.\n"; }
        return false;
    }
    const std::vector<unsigned int>& model = antom.model();
    std::vector<Variable> to_eliminate;
    to_eliminate.reserve(optimum);
    for (const Literal lit: model) {
        if (isPositive(lit) && lit <= maxLitIndex()) to_eliminate.push_back(lit2var(lit));
    }

    if (setting.verbosity > 1) {
        std::cout << "c Need to eliminate " << to_eliminate.size() << " univ vars out of " << numUVars() << ": ";
        for (auto v: to_eliminate) std::cout << v << " ";
        std::cout << std::endl;
    }

    const auto old_size = numLiterals();
    std::set<Variable> pseudo_deps;
    unsigned int count = 0;

    while (true) {
        int next_var = -1;
        int min_cost = std::numeric_limits<int>::max();
        for (Variable uvar: to_eliminate) {
            if (varDeleted(uvar)) continue;
            sstdQuadDep(uvar, true, true, &pseudo_deps);
            const int cost = computeExpansionCosts2(uvar, pseudo_deps);
            pseudo_deps.clear();
            if (cost < min_cost) { next_var = uvar; min_cost = cost; }
        }

        std::cout << "min_cost = " << min_cost <<std::endl;
        if (next_var >= 0 && min_cost < 0.1 * old_size) {
            eliminateVariableU(next_var);
            ++count;
            if (interrupt) break;
            applyResolution();
            if (numLiterals() > 1.1 * old_size) break;
        } else break;
    }
    return count > 0;
}


/**
 * \brief Eliminates a universal variable by expansion.
 * \param var the universal variable to be eliminated
 * \note This function creates new variables which serve as
 *       copies of those existential variables which depend
 *       upon `var`.
 * \todo If \f$x\f$ is the eliminated universal variable,
 *       \f$y\f$ an existential one, and there is an implication
 *       like \f$x\rightarrow y\f$, one can replace \f$y\f$ in
 *       the 1-cofactor by 1. The remaining three cases
 *       are similar. We could look for such implications using
 *       a SAT-solver or check if the implication is a blocked
 *       (binary clause).
 * \todo Make universal expansion work for QBF prefixes as well
 */
void Formula::eliminateVariableU(const Variable var)
{
    typedef enum {
        NOT_AT_ALL = 0,
        POSITIVE = 1,
        NEGATIVE = 2
    } Occurrence;

    val_assert(prefix != nullptr);
    val_assert_msg(isUniversal(var), "You can only expand universal variables!");
    val_assert_msg(unit_stack.empty(), "You must call Formula::unitPropagation() first!");

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << "(" << var << ")\nc |-> size before: " << numLiterals() << std::endl;
    }

    // Remove all pseudo-dependencies of the expanded variable.
    std::set<Variable> pseudo_deps;
    sstdQuadDep(var, true, true, &pseudo_deps);

    const Literal u_pos = var2lit(var, false);
    const Literal u_neg = var2lit(var, true);

    // Clauses that will be deleted
    std::vector<unsigned int> to_delete;
    // Clauses that will be added
    std::vector<std::vector<Literal>> to_add;
    // Mapping the dependent literals to their copies
    std::map<Literal, Literal> lit_map;

    // Create a copy of each dependent var and store it in 'var_map'
    const Variable old_maxVarIndex = maxVarIndex();
    for (Variable e_var = minVarIndex(); e_var <= old_maxVarIndex; ++e_var) {
        if (!isExistential(e_var)) continue;
        if (!depends(e_var, var)) continue;
        if (pseudo_deps.find(e_var) != pseudo_deps.cend()) continue;

        const Variable e_var_copy = copyVar(e_var);
        val_assert(isExistential(e_var_copy));
        lit_map[var2lit(e_var, false)] = var2lit(e_var_copy, false);
        lit_map[var2lit(e_var, true) ] = var2lit(e_var_copy, true);
    }

    if (setting.verbosity > 2) {
        std::cout << "c |-> Dependency scheme removed " << pseudo_deps.size() << " out of " << (lit_map.size() / 2) + pseudo_deps.size() << " dependencies.\n";
    }

    std::vector<Literal> new_clause;
    new_clause.reserve(50);

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;

        Occurrence contains_u = NOT_AT_ALL;
        bool contains_dependent_var = false;

        // Check if the clause contains the eliminated universal variables
        // or any variable which needs to be copied.
        for (const Literal lit: clauses[c_nr]) {
            if (lit == u_pos) contains_u = POSITIVE;
            else if (lit == u_neg) contains_u = NEGATIVE;
            else if (isExistential(lit2var(lit)) && lit_map.find(lit) != lit_map.cend()) {
                contains_dependent_var = true;
            }
        }

        if (contains_u == NOT_AT_ALL && !contains_dependent_var) {
            // clause remains unchanged
            continue;
        } else if (clauseOptional(c_nr)) {
            // delete optional clauses that would not remain unchanged
            to_delete.push_back(c_nr);
            continue;
        } else if (contains_u == POSITIVE) {
            // clause[c_nr] contains 'var' positively
            // -> only remove u_pos
            removeLiteral(c_nr, u_pos);
        } else if (contains_u == NEGATIVE) {
            // clause contains 'var' negatively
            // -> remove ~var and replace the dependent variables by their copies
            for (const Literal lit: clauses[c_nr]) {
                if (lit == u_neg) continue;
                const auto copy_found = lit_map.find(lit);
                if (copy_found != lit_map.cend()) {
                    new_clause.push_back(copy_found->second);
                } else new_clause.push_back(lit);
            }

            to_add.push_back(std::move(new_clause));
            new_clause.clear();
            to_delete.push_back(c_nr);
        } else if (contains_u == NOT_AT_ALL && contains_dependent_var) {
            // clause does not contain 'var', but exist. vars that depend upon it
            // -> Add a copy of the clause with replaced variables.
            for (const Literal lit: clauses[c_nr]) {
                const auto copy_found = lit_map.find(lit);
                if (copy_found != lit_map.cend()) {
                    new_clause.push_back(lit_map[lit]);
                } else new_clause.push_back(lit);
            }

            to_add.push_back(std::move(new_clause));
            new_clause.clear();
        }
    } // end for c_nr


    // Remove old and add new clauses
    for (const unsigned int c_nr: to_delete) removeClause(c_nr);
    for (std::vector<Literal>& clause: to_add) addClause(std::move(clause));

    // Delete the expanded variable
    removeVar(var);
    ++stat_univ_expansion;

	fastPreprocess();

    if (setting.verbosity > 1) {
        std::cout << "c |-> size after univ. expansion: " << numLiterals() << std::endl;
    }

	if (numClauses() == 0) throw SATException(this);
}


} // end namespace hqspre
