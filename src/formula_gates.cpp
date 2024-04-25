#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <stack>
#include <functional>
#include <iterator>
#include <iostream>
#include "formula.hpp"

/**
 * \file formula_gates.cpp
 * \brief Implementation of gate detection
 * \author Ralf Wimmer
 * \date 01/2016
 */

namespace hqspre {


/**
 * \brief Checks if a given variable is suited to be a gate output.
 *
 * A variable can only be a gate output if it is existential and depends
 * at least on the variable the gate inputs depend on. This function does
 * not check if all necessary clauses are present.
 * \param output_var the variable that is assumed to be a gate output
 * \param clause a clause that contains the gate inputs and the gate output
 * \return true if the described conditions are satisfied
 * \sa Formula::determineGates()
 */
bool Formula::checkGatePrecondition(Variable output_var, const Clause& clause) const
{
    if (isUniversal(output_var)) return false;
    for (auto lit: clause) {
        const auto current_var = lit2var(lit);
        if (current_var == output_var) continue;
        if (!dependenciesSubset(current_var, output_var)) return false;
    }
    return true;
}

/**
 * \brief Adds the dependencies of a single gate to gateDep
 *
 * This function is used by the gate detection for analyzing
 * whether a gate would create a cycle in the circuit.
 * \sa cyclicDep
 * \sa Formula::detectGates()
 */
static void addDep(std::vector<std::vector<Variable>>& gateDep, Variable base_var, const std::vector<Variable>& parents)
{
    if (gateDep[base_var].empty()) gateDep[base_var] = parents;
    else std::copy(parents.cbegin(), parents.cend(), std::back_inserter(gateDep[base_var]));
}


/**
 * \brief Returns true if adding another gate would create a cyclic dependency.
 *
 * This function is used by the gate detection for analyzing whether a gate
 * would create a cycle in the circuit.
 * \sa addDep
 * \sa Formula::detectGates
 */
static bool cyclicDep(std::vector<std::vector<Variable>>& gateDep, Variable base_var, const std::vector<Variable>& parents)
{
    std::stack<Variable> pending;
    std::vector<bool> processed(gateDep.size(), false);

    for (const Variable p: parents) {
        val_assert(p != base_var);
        pending.push(p);
    }

    while (!pending.empty()) {
        const Variable pt = pending.top();
        pending.pop();

        if (!processed[pt]) {
            const auto& dep = gateDep[pt];
            processed[pt] = true;

            for (const Variable p: dep) {
                if (p == base_var) return true;
                else if (!processed[p]) pending.push(p);
            }
        }
    }
    return false;
}


/**
 * \brief Checks if two clauses contain the same variables (with different polarities).
 * \pre Requires c1 and c2 to be sorted.
 * \pre Clauses must not be tautological or contain duplicate literals.
 */
static bool sameVars(const Clause& c1, const Clause& c2)
{
    if (c1.size() != c2.size()) return false;
    for (unsigned int i = 0; i < c1.size(); ++i) {
        if (lit2var(c1[i]) != lit2var(c2[i])) return false;
    }
    return true;
}

/**
 * \brief Counts the number of positive literals in a clause.
 */
static unsigned int posCount(const Clause& clause)
{
    return std::count_if(clause.cbegin(), clause.cend(), isPositive);
}


/**
 * \brief Performs gate detection on a quantified formula in CNF.
 *
 * We can detect 2-input XOR and multi-input AND-gates with arbitrarily
 * negated inputs and outputs. The gates are returned in topological order
 * (from inputs to outputs).
 * \sa Formula::substituteGate(const Gate&)
 */
const std::vector<Gate> Formula::determineGates()
{
    if (!unit_stack.empty()) unitPropagation();

    ScopeTimer gate_detection(gate_detection_time);

    val_assert(clause_gate.size() >= clauses.size());
    val_assert(gate_output.size() > maxVarIndex());
    val_assert(gate_input.size() > maxVarIndex());

    // Clear the vector that contains the information which clauses
    // encode gates and which variables are gate in- and outputs.
    std::fill(clause_gate.begin(), clause_gate.end(), false);
    std::fill(gate_output.begin(), gate_output.end(), false);
    std::fill(gate_input.begin(), gate_input.end(), 0);

    // The vector with the found gates
    std::vector<Gate> gates;

    // Dependency graph of the gate outputs on the gate inputs.
    // Used to avoid cyclic dependencies, which are not sound in a circuit.
    std::vector<std::vector<Variable>> gateDep(maxVarIndex() + 1);

    // Used to store the inputs of the currently detected gate
    std::vector<Variable> parents;
    parents.reserve(6);

    // Used for AND-gates to store the clauses which encode the implications.
    std::vector<unsigned int> clause_ids;
    clause_ids.reserve(6);


    // Looking for (multi-)AND-gates with arbitrarily negated inputs and output
    const unsigned int num_clauses = clauses.size();
    for (unsigned int c_nr = 0; c_nr < num_clauses; ++c_nr) {
        if (clauseDeleted(c_nr) || clauses[c_nr].size() <= 2 || clause_gate[c_nr]) continue;

        for (unsigned int l_nr = 0; l_nr < clauses[c_nr].size(); ++l_nr)
        {
            const Literal base_lit = clauses[c_nr][l_nr];
            const Variable base_var = lit2var(base_lit);
            if (gate_output[base_var]) continue;

            parents.clear();
            clause_ids.clear();
            bool has_imp = true;
            for (Literal lit: clauses[c_nr]) {
                if (lit == base_lit) continue;
                const int bin_id = getImplicationClause(base_lit, negate(lit));
                if (bin_id < 0) { has_imp = false; break; }
                parents.push_back(lit2var(lit));
                clause_ids.push_back(bin_id);
            }
            if (!has_imp) continue;
            if (!checkGatePrecondition(base_var, clauses[c_nr])) continue;

            // Check for cyclic dependencies
            if (gate_input[base_var] > 0 && cyclicDep(gateDep, base_var, parents)) continue;

            addDep(gateDep, base_var, parents);
            gate_output[base_var] = true;
            for (Variable p: parents) ++gate_input[p];

            // We have found an AND-gate
            Gate g;
            g.type = GateType::AND_GATE;
            g.output_literal = base_lit;
            g.encoding_clauses.reserve(clauses[c_nr].size());
            g.input_literals.reserve(clauses[c_nr].size() - 1);
            g.encoding_clauses.push_back(c_nr);
            clause_gate[c_nr] = true;
            clauses[c_nr].setStatus(ClauseStatus::MANDATORY);
            for (unsigned int bin_id: clause_ids) {
                g.encoding_clauses.push_back(bin_id);
                clauses[bin_id].setStatus(ClauseStatus::MANDATORY);
                clause_gate[bin_id] = true;
            }
            for (Literal lit: clauses[c_nr]) {
                if (lit != base_lit) g.input_literals.push_back(negate(lit));
            }

            gates.push_back(std::move(g));
            break;
        }
    }


    // Looking for XOR-gates with arbitrarily negated inputs and output
    for (Variable base_var = 1; base_var <= maxVarIndex(); ++base_var)
    {
        if (isUniversal(base_var)) continue;
        if (gate_output[base_var]) continue;
        if (occ_list[var2lit(base_var, false)].size() < 2 || occ_list[var2lit(base_var, true)].size() < 2) continue;

        const Literal base_lit_pos = var2lit(base_var, false);
        const Literal base_lit_neg = var2lit(base_var, true);
        bool found_gate = false;

        for (unsigned int p1 = 0; p1 < occ_list[base_lit_pos].size(); ++p1) {
            const auto i1 = occ_list[base_lit_pos][p1];
            val_assert(!clauseDeleted(i1));
            const auto& c1 = clauses[i1];
            if (c1.size() != 3) continue;
            if (clause_gate[i1]) continue;
            if (!checkGatePrecondition(base_var, c1)) continue;

            for (unsigned int p2 = p1 + 1; p2 < occ_list[base_lit_pos].size(); ++p2) {
                const unsigned int i2 = occ_list[base_lit_pos][p2];
                val_assert(!clauseDeleted(i2));
                const auto& c2 = clauses[i2];
                if (clause_gate[i2]) continue;
                if (!sameVars(c1,c2)) continue;

                for (unsigned int p3 = 0; p3 < occ_list[base_lit_neg].size(); ++p3) {
                    const unsigned int i3 = occ_list[base_lit_neg][p3];
                    val_assert(!clauseDeleted(i3));
                    const auto& c3 = clauses[i3];
                    if (clause_gate[i3]) continue;
                    if (!sameVars(c1,c3)) continue;

                    for (unsigned int p4 = p3 + 1;  p4 < occ_list[base_lit_neg].size(); ++p4) {
                        const unsigned int i4 = occ_list[base_lit_neg][p4];
                        val_assert(!clauseDeleted(i4));
                        const auto& c4 = clauses[i4];
                        if (clause_gate[i4]) continue;
                        if (!sameVars(c1,c4)) continue;

                        if (c1 == c2 || c1 == c3 || c1 == c4 || c2 == c3 || c2 == c4 || c3 == c4) continue;

                        const auto pc1 = posCount(c1);
                        const auto pc2 = posCount(c2);
                        const auto pc3 = posCount(c3);
                        const auto pc4 = posCount(c4);

                        if( !( (  ( pc1 & 1 ) &&  ( pc2 & 1 ) &&  ( pc3 & 1 ) &&  ( pc4 & 1 ) ) ||
                               ( !( pc1 & 1 ) && !( pc2 & 1 ) && !( pc3 & 1 ) && !( pc4 & 1 ) ) ) )
                        {
                            // mixed polarities -> skipping
                            continue;
                        }

                        parents.resize(2);
                        bool base_found = false;
                        if (c1[0] == base_lit_pos) {
                            parents[0] = lit2var(c1[1]);
                            parents[1] = lit2var(c1[2]);
                            if (gate_input[base_var] == 0 || !cyclicDep(gateDep, base_var, parents)) {
                                addDep(gateDep, base_var, parents);
                                base_found = true;
                            }
                        } else if (c1[1] == base_lit_pos) {
                            parents[0] = lit2var(c1[0]);
                            parents[1] = lit2var(c1[2]);
                            if (gate_input[base_var] == 0 || !cyclicDep(gateDep, base_var, parents)) {
                                addDep(gateDep, base_var, parents);
                                base_found = true;
                            }
                        } else if (c1[2] == base_lit_pos) {
                            parents[0] = lit2var(c1[0]);
                            parents[1] = lit2var(c1[1]);
                            if (gate_input[base_var] == 0 || !cyclicDep(gateDep, base_var, parents)) {
                                addDep(gateDep, base_var, parents);
                                base_found = true;
                            }
                        }

                        if (!base_found) continue;

                        // Now 'base_var' is the output of an XOR gate.
                        Gate g;
                        g.type = GateType::XOR_GATE;
                        g.output_literal = var2lit(base_var, (pc1 & 1) == 1);
                        g.input_literals = {var2lit(parents[0]), var2lit(parents[1])};
                        g.encoding_clauses = { i1, i2, i3, i4 };
                        clauses[i1].setStatus(ClauseStatus::MANDATORY);
                        clause_gate[i1] = true;
                        clauses[i2].setStatus(ClauseStatus::MANDATORY);
                        clause_gate[i2] = true;
                        clauses[i3].setStatus(ClauseStatus::MANDATORY);
                        clause_gate[i3] = true;
                        clauses[i4].setStatus(ClauseStatus::MANDATORY);
                        clause_gate[i4] = true;
                        gates.push_back(std::move(g));

                        ++gate_input[parents[0]];
                        ++gate_input[parents[1]];
                        gate_output[base_var] = true;
                        found_gate = true;
                        break;
                    } // for c4
                    if (found_gate) break;
                } // for c3
                if (found_gate) break;
            } // for c2
            if (found_gate) break;
        } // for c1
    } // for base_var


    // Create a topological ordering of the variables in gateDep.
    std::vector<int> which_gate(maxVarIndex() + 1, -1);
    for (unsigned int i = 0; i < gates.size(); ++i) which_gate[lit2var(gates[i].output_literal)] = i;

    std::vector<bool> processed(maxVarIndex() + 1, false);
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        processed[var] = !gate_output[var];
    }

    // dfs is a recursive function which performs depth-first search on the
    // graph defined by the gate dependencies.
    std::vector<Variable> order;
    order.reserve(gates.size());
    std::function<void(int)> dfs = [this, &gateDep, &processed, &dfs, &order](Variable var) -> void
        {
            for (Variable dep: gateDep[var]) {
                if (!processed[dep]) dfs(dep);
            }
            processed[var] = true;
            order.push_back(var);
        }; // end lambda function

    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (!processed[var] && gate_input[var] == 0) dfs(var);
    }

    std::vector<Gate> result;
    result.reserve(gates.size());
    for (Variable var: order) {
        val_assert(which_gate[var] != -1);
        result.push_back(std::move(gates[which_gate[var]]));
    }

    return result;
}


} // end namespace hqspre
