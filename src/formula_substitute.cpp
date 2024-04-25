#include <vector>
#include <cstdlib>
#include <iostream>
#include "formula.hpp"

/**
 * \file formula_substitute.cpp
 * \brief Implementation of gate substitution and gate rewriting
 * \author Ralf Wimmer
 * \author Paolo Marin
 * \date 06/2016
 */

namespace hqspre {

/**
 * \brief Replaces a Tseitin variable by its gate definition.
 *
 * This function can be used to eliminate existential variables
 * which result from Tseitin transformation. It typically creates
 * fewer clauses than variable elimination by resolution.<br>
 * See: Een, Biere: <i>Effective Preprocessing in SAT through
 *      Variable and Clause Elimination</i>, SAT 2005.
 * \param g the gate defining the substituted variable
 */
bool Formula::substituteGate(const Gate& g)
{
    const int approx_costs = computeSubstitutionCosts(g);
    if (approx_costs > setting.max_substitution_cost + 80) {
        if (setting.verbosity > 2) {
            std::cout << "c Skipping substition of gate " << g << " (estimated cost = " << approx_costs << ")\n";
        }
        return false;
    }

    const Literal o_lit = g.output_literal;
    const Literal no_lit = negate(o_lit);
    std::vector<Clause> to_add;

    int actual_costs = 0;

    if (setting.verbosity > 2) {
        std::cout << "c Substituting gate " << g << " (approx. costs = " << approx_costs << ") ... " << std::endl;
    }

    for (unsigned int c_nr: g.encoding_clauses) {
        const auto& clause = clauses[c_nr];
        if (clause.containsLiteral(o_lit)) {
            for (unsigned int other_c_nr: occ_list[no_lit]) {
                if (isNegative(o_lit)) {
                    to_add.push_back(resolve(clauses[other_c_nr], clause, lit2var(o_lit)));
                } else {
                    to_add.push_back(resolve(clause, clauses[other_c_nr], lit2var(o_lit)));
                }
                auto& lastclause = to_add.back();
                if (lastclause.isTautology()) {
                    to_add.pop_back();
                } else {
                    actual_costs += lastclause.size();
                }
            }
        } else if (clause.containsLiteral(no_lit)) {
            for (unsigned int other_c_nr: occ_list[o_lit]) {
                if (isPositive(o_lit)) {
                    to_add.push_back(resolve(clauses[other_c_nr], clause, lit2var(o_lit)));
                } else {
                    to_add.push_back(resolve(clause, clauses[other_c_nr], lit2var(o_lit)));
                }
                auto& lastclause = to_add.back();

                if (lastclause.isTautology()) {
                    to_add.pop_back();
                } else {
                    actual_costs += lastclause.size();
                }
            }
        } else {
            std::cerr << "[ERROR] Clause " << clause << " does not contain output literal " << lit2dimacs(o_lit) << std::endl;
            val_assert(false);
        }

    }

    for (unsigned int c_nr: occ_list[o_lit])  actual_costs -= clauses[c_nr].size();
    for (unsigned int c_nr: occ_list[no_lit]) actual_costs -= clauses[c_nr].size();

    if (actual_costs > setting.max_substitution_cost) {
        if (setting.verbosity > 2) {
            std::cout << "c Substitution aborted. Costs of " << actual_costs << " are too high." << std::endl;
        }
        return false;
    }


    // Delete the clauses that are no longer needed
    while (!occ_list[o_lit].empty()) {
        removeClause(occ_list[o_lit].front());
    }
    while (!occ_list[no_lit].empty()) {
        removeClause(occ_list[no_lit].front());
    }


    for (const Clause& c: to_add) {
        setSeen(c);
        if (!isForwardSubsumed(c, -1)) {
            clearSeen(c);
            addClause(std::move(c));
        } else {
            clearSeen(c);
            actual_costs -= c.size();
        }
    }

    removeVar(lit2var(o_lit));

    ++stat_substitution;

    return true;
}

/**
 * \brief Replaces a Tseitin variable by a double-Plaisted encoding
 *
 * This function can be used to replace existential variables
 * which result from Tseitin transformation by splitting a gate's output
 * with two monotone outputs.<br>
 * See: Giunchiglia, Marin, Narizzano: <i>sQueezeBF: An Effective Preprocessor
 *      for QBFs based on Equivalence Reasoning</i>, SAT 2010.
 * \param g the gate defining the substituted variable
 */
void Formula::rewriteGate(const Gate& g)
{
    if (varDeleted(lit2var(g.output_literal))) return;

    if (setting.verbosity > 2) {
        std::cout << __FUNCTION__ << "() Rewriting gate " << g << std::endl;
    }

    ScopeTimer gate_rewrite(gate_rewrite_time);

    std::vector<Literal> new_clause;
    std::vector<std::vector<Literal>> to_add;
    std::vector<unsigned int> to_delete;
    to_delete.reserve(occ_list[g.output_literal].size() + occ_list[negate(g.output_literal)].size());

    Literal y = g.output_literal;
    Literal y_neg = negate(y);

    val_assert(!varDeleted(lit2var(y)));

    // new variable representing the second output of the gate in the
    // modified Plaisted encoding
    const Literal z = var2lit(copyVar(lit2var(y)), false);
    const Literal z_neg = negate(z);

    if (setting.verbosity > 2) {
        std::cout << "c " << __FUNCTION__ << "(): Variable " << lit2var(y) << " doubled as " << lit2var(z) << std::endl;
    }

    for (unsigned int c_nr: g.encoding_clauses) {
      removeClause(c_nr);
    }

    if (g.type == GateType::AND_GATE) {
        // add efficiency clause
        new_clause.clear();
        new_clause.push_back(y_neg);
        new_clause.push_back(z_neg);
        to_add.push_back(std::move(new_clause));
        // if y = AND (y1,...,y_n) replace
        // * (C v y) by (C v y1),...,(C v y_n)
        // * (C v !y) by (C v !y1 v ... v !y_n)
        // Clauses where y occurs negatively are modified so that y_neg is replaced by z;
        // Clauses where y occurs stay unmodified
        replaceLiteralMono(y_neg, z);

        // rebuild gate encoding
        // long clause
        new_clause.clear();
        new_clause.push_back(z_neg);
        for (const Literal lit: g.input_literals) {
            // Skip literal if variable was deleted before
            if (varDeleted(lit2var(lit))) continue;
            new_clause.push_back(negate(lit));
        }
        to_add.push_back(std::move(new_clause));
        // short clauses
        for (const Literal lit: g.input_literals) {
            new_clause.clear();
            new_clause.push_back(y_neg);
            new_clause.push_back(lit);
            // Skip clause if variable was deleted before
            to_add.push_back(std::move(new_clause));
        }


    } else if (g.type == GateType::XOR_GATE) {
        // add efficiency clause
        std::swap(y, y_neg);
        new_clause.clear();
        new_clause.push_back(y_neg);
        new_clause.push_back(z_neg);
        to_add.push_back(std::move(new_clause));

        replaceLiteralMono(y_neg, z);

        val_assert(g.input_literals.size() == 2);
        const Literal a = g.input_literals[0];
        const Literal b = g.input_literals[1];

        for (const unsigned int c_nr: occ_list[y]) {
            if (clauseOptional(c_nr)) {
                // delete all optional clauses that contain y
                to_delete.push_back(c_nr);
                continue;
            }
        }
        for (const unsigned int c_nr: occ_list[y_neg]) {
            if (clauseOptional(c_nr)) {
                // delete all optional clauses that contain y_neg
                to_delete.push_back(c_nr);
                continue;
            }
        }
        new_clause.clear();
        new_clause.push_back(z_neg);
        new_clause.push_back(a);
        new_clause.push_back(b);
        to_add.push_back(std::move(new_clause));

        new_clause.clear();
        new_clause.push_back(z_neg);
        new_clause.push_back(negate(a));
        new_clause.push_back(negate(b));
        to_add.push_back(std::move(new_clause));

        new_clause.clear();
        new_clause.push_back(y_neg);
        new_clause.push_back(negate(a));
        new_clause.push_back(b);
        to_add.push_back(std::move(new_clause));

        new_clause.clear();
        new_clause.push_back(y_neg);
        new_clause.push_back(a);
        new_clause.push_back(negate(b));
        to_add.push_back(std::move(new_clause));

    } else {
        std::cerr << "[WARNING] Unsupported gate type for rewriting." << std::endl;
        return;
    }

    for (unsigned int c_nr: to_delete) removeClause(c_nr);
    for (unsigned int i = 0; i < to_add.size(); ++i) {
        addClause(std::move(to_add[i]));
    }

    ++stat_rewriting;
}


/**
 * \brief Computes the cost of replacing a Tseitin variable by its gate definition.
 *
 * The costs are given as the number of literals by which the formula size increases.
 * Negative costs means that the formula becomes shorter. The value is only an
 * over-approximation as it does not take into account that substitution may lead
 * to tautological clauses or duplicate literals.
 *
 * \todo Better estimation of the substitution costs by taking into
 *       account that resolvents of gate-defining clauses are often
 *       tautologies.
 */
int Formula::computeSubstitutionCosts(const Gate& g) const
{
    int result = 0;
    int pos_cost = 0;
    int neg_cost = 0;

    for (unsigned int c_nr: occ_list[g.output_literal]) {
        if (!clauseOptional(c_nr)) pos_cost += (clauses[c_nr].size() - 1);
    }

    for (unsigned int c_nr: occ_list[negate(g.output_literal)]) {
        if (!clauseOptional(c_nr)) neg_cost += (clauses[c_nr].size() - 1);
    }

    for (unsigned int c_nr: g.encoding_clauses) {
        if (clauses[c_nr].containsLiteral(g.output_literal)) result += (clauses[c_nr].size() - 1) * neg_cost;
        else result += (clauses[c_nr].size() - 1) * pos_cost;
    }
    result -= (pos_cost + neg_cost + occ_list[g.output_literal].size() + occ_list[negate(g.output_literal)].size());

    return result;
}



/**
 * \brief Eliminates Tseitin variables by substitution.
 *
 * Substitution first determines the encoded gates. These gates
 * are handled in reverse topological order, i.e., from the circuit
 * outputs to the circuit inputs. This avoids that substitution
 * re-introduces variables which have already been substituted.
 * The substitution of a gates is only performed if it increases
 * the formula size by at most some Settings::max_substitution_cost literals.
 * \sa Formula::substitutionCosts(const Gate&)
 * \return true if the formula was modified
 */
bool Formula::applySubstitution()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer gate_sub(gate_sub_time);

    // Clear the clause_modified bit.
    std::fill(clause_modified.begin(), clause_modified.end(), false);

    unsigned int old_stat_substitute = stat_substitution;
    const std::vector<Gate> gates = determineGates();

    for (auto it = gates.crbegin(); it != gates.crend(); ++it) {

        if (interrupt) break;

        // Check if any of the gate's clauses has been
        // deleted (by subsumption checks during substitution
        // of other clauses)
        bool gate_available = true;
        for (unsigned int c_nr: it->encoding_clauses) {
            if ((clause_modified[c_nr]) || clauseDeleted(c_nr)){
                gate_available = false;
                break;
            }
        }
        if (!gate_available) continue;

        if (setting.preserve_gates) {
            if (!gate_input[lit2var(it->output_literal)] && substituteGate(*it)) {
                gate_output[lit2var(it->output_literal)] = false;
                for (unsigned int i_lit: it->input_literals) {
                    --gate_input[lit2var(i_lit)];
                }
            }
        } else {
            if (substituteGate(*it)) {
                gate_sub_time.start();
            } else if (setting.rewrite) {
                gate_sub_time.stop();
                rewriteGate(*it);
                gate_sub_time.start();
            }
        }
    }

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " removed " << (stat_substitution - old_stat_substitute) << " of " << gates.size() << " gates.\n";
    }

    if (setting.preserve_gates) determineGates();

    return stat_substitution > old_stat_substitute;
}


} // end namespace hqspre
