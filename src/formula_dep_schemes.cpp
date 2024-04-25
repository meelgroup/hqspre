#include <vector>
#include <stack>
#include <iostream>
#include "formula.hpp"

/**
 * \file formula_dep_schemes.cpp
 * \brief Implementation of dependency schemes for DQBF
 * \author Ralf Wimmer
 * \date 12/2015--03/2016
 */

namespace hqspre {

/**
 * \brief Tries to find paths in the clause-literal incidence graph.
 *
 * \param start_lits the literals the paths may start at
 * \param forbidden a functor telling over which variable nodes the paths may not run
 * \param[out] seen a vector which stores the variables that can be reached by paths.
 * \sa stdTriDep(bool, bool)
 * \sa invStdTriDep(bool, bool)
 * \sa sstdQuadDep(bool, bool)
 * \sa invSstdQuadDep(bool, bool)
 */
template <typename Function>
void Formula::searchPath(
    const std::vector<Literal>& start_lits,
    Function forbidden,
    std::vector<unsigned char>& seen) const
{
    val_assert(seen.size() > maxLitIndex());
    std::stack<Literal> open_lits;

    // Invariant:
    // - only literals are added to open_vars for which seen[lit] = false;
    // - all literals in open_vars are marked with seen[lit] = true
    // This ensures that no literal is added to open_vars twice.
    for (Literal lit: start_lits) {
        if (!seen[lit]) open_lits.push(lit);
        seen[lit] = true;
    }

    while (!open_lits.empty()) {
        const Literal current_lit = open_lits.top();
        open_lits.pop();
        for (unsigned int c_nr: occ_list[current_lit]) {
            val_assert(!clauseDeleted(c_nr));
            if (clauseOptional(c_nr)) continue; ///< \todo May we skip optional clauses?

            for (Literal next_lit: clauses[c_nr]) {
                if (!seen[next_lit] && !forbidden(next_lit)) open_lits.push(next_lit);
                if (!seen[negate(next_lit)] && !forbidden(negate(next_lit))) open_lits.push(negate(next_lit));

                seen[next_lit] = true;
                seen[negate(next_lit)] = true;
            }
        }
    }
}


/**
 * \brief Tries to find resolution paths in the clause-literal incidence graph.
 *
 * A resolution path connects clauses in which the connecting variable
 * appears in different polarities. Additionally, the same variable may not
 * be used twice in sequence along the path.
 * \param start_lits the literals the resolution paths may start at
 * \param forbidden a functor telling over which variable nodes the paths may not run
 * \param[out] seen a vector which stores the variables that can be reached by paths.
 * \sa stdTriDep(bool, bool)
 * \sa invStdTriDep(bool, bool)
 * \sa sstdQuadDep(bool, bool)
 * \sa invSstdQuadDep(bool, bool)
 */
template <typename Function>
void Formula::searchResolutionPath(
    const std::vector<Literal>& start_lits,
    Function forbidden,
    std::vector<unsigned char>& seen) const
{
    val_assert(seen.size() > maxLitIndex());
    std::stack<Literal> open_lits;

    // Invariant:
    // - only literals are added to open_vars for which seen[lit] = false;
    // - all literals in open_vars are marked with seen[lit] = true
    // This ensures that no literal is added to open_vars twice.
    for (Literal lit: start_lits) {
        for (unsigned int c_nr: occ_list[lit]) {
            val_assert(!clauseDeleted(c_nr));
            if (clauseOptional(c_nr)) continue; ///< \todo May we skip optional clauses?

            for (Literal next_lit: clauses[c_nr]) {
                if (!forbidden(next_lit) && !seen[next_lit]) {
                    open_lits.push(next_lit);
                }
                seen[next_lit] = true;
            }
        }
    }

    while (!open_lits.empty()) {
        const Literal current_lit = negate(open_lits.top());
        open_lits.pop();
        for (unsigned int c_nr: occ_list[current_lit]) {
            val_assert(!clauseDeleted(c_nr));
            if (clauseOptional(c_nr)) continue; ///< \todo May we skip optional clauses?

            for (Literal next_lit: clauses[c_nr]) {
                if (!seen[next_lit] && !forbidden(next_lit)) {
                    open_lits.push(next_lit);
                }
                seen[next_lit] = true;
            }
        }
    }
}


bool Formula::invStdTriDep(bool resolution_paths, bool triangle)
{
    bool modified = false;
    for (Variable u_var = minVarIndex(); u_var <= maxVarIndex(); ++u_var) {
        if (!isUniversal(u_var)) continue;
        if (invStdTriDep(u_var, resolution_paths, triangle)) modified = true;
    }

    return modified;
}

/**
 * \brief Implementation of the standard and reflexive triangle dependency scheme for addinging pseudo-dependencies
 *
 * The dependency scheme can either use normal
 * or resolution paths. Identified pseudo-dependencies are
 * added to the dependency sets.
 * \note For a QBF prefix, the function may only be called if the
 *       parameter `pseudo_deps` is not nullptr.
 * \param resolution_paths if true, use resolution paths
 * \param triangle if true, use the reflexive triangle dependency scheme
 * \param pseudo_deps if not nullptr, the addable dependencies are stored in pseudo_deps; otherwise they are added.
 * \return true if the formula was modified
 * \sa stdTriDep(bool, bool)
 * \sa sstdQuadDep(bool, bool)
 * \sa invSstdQuadDep(bool, bool)
 */
bool Formula::invStdTriDep(Variable u_var, bool resolution_paths, bool triangle, std::set<Variable>* pseudo_deps)
{
    val_assert(minVarIndex() <= u_var && u_var <= maxVarIndex());
    val_assert(isUniversal(u_var));
    val_assert(prefix != nullptr);
    val_assert(dqbf_prefix != nullptr || pseudo_deps != nullptr);

    int count = 0;

    const auto forbidden = [this, u_var](Literal lit) -> bool
    {
        return this->isUniversal(lit2var(lit)) || !this->depends(lit2var(lit), u_var);
    };

    if (resolution_paths) {
        searchResolutionPath({var2lit(u_var, true), var2lit(u_var, false)}, forbidden, _seen);
    } else {
        searchPath({var2lit(u_var, true), var2lit(u_var, false)}, forbidden, _seen);
    }

    for (Variable e_var = 1; e_var <= maxVarIndex(); ++e_var) {
        if (!isExistential(e_var) || depends(e_var, u_var)) continue;

        const Literal ep = var2lit(e_var, false);
        const Literal en = var2lit(e_var, true);

        if ( (triangle && (!_seen[ep] || !_seen[en]))
              || (!triangle && !_seen[ep] && !_seen[en]) ) {
            if (pseudo_deps == nullptr) addDependency(u_var, e_var);
            else pseudo_deps->insert(e_var);
            ++count;
        }
    }

    clearSeen();
    stat_dep_schemes += count;
    return count > 0;
}


bool Formula::invSstdQuadDep(bool resolution_paths, bool quadrangle)
{
    bool modified = false;
    for (Variable u_var = minVarIndex(); u_var <= maxVarIndex(); ++u_var) {
        if (!isUniversal(u_var)) continue;
        if (invSstdQuadDep(u_var, resolution_paths, quadrangle)) modified = true;
    }

    return modified;
}


/**
 * \brief Implementation of the strict standard and reflexive quadrangle dependency scheme for addinging pseudo-dependencies
 *
 * The dependency scheme can either use normal
 * or resolution paths. Identified pseudo-dependencies are
 * added to the dependency sets.
 * \note For a QBF prefix, the function may only be called if the
 *       parameter `pseudo_deps` is not nullptr.
 * \param resolution_paths if true, use resolution paths
 * \param quadrangle if true, use the reflexive quadrangle dependency scheme
 * \param pseudo_deps if not nullptr, the addable dependencies are stored in pseudo_deps; otherwise they are added.
 * \return true if the formula was modified
 * \sa stdTriDep(bool, bool)
 * \sa invStdTriDep(bool, bool)
 * \sa sstdQuadDep(bool, bool)
 */
bool Formula::invSstdQuadDep(Variable u_var, bool resolution_paths, bool quadrangle, std::set<Variable>* pseudo_deps)
{
    val_assert(prefix != nullptr);
    val_assert(dqbf_prefix != nullptr || pseudo_deps != nullptr);

    int count = 0;
    std::vector<unsigned char>& seen_pos = _seen;
    std::vector<unsigned char> seen_neg(maxLitIndex() + 1, false);

    const auto forbidden = [this, u_var](Literal lit) -> bool
    {
        return this->isUniversal(lit2var(lit)) || !this->depends(lit2var(lit), u_var);
    };

    if (resolution_paths) {
        searchResolutionPath({var2lit(u_var,false)}, forbidden, seen_pos);
        searchResolutionPath({var2lit(u_var, true)}, forbidden, seen_neg);
    } else {
        searchPath({var2lit(u_var,false)}, forbidden, seen_pos);
        searchPath({var2lit(u_var, true)}, forbidden, seen_neg);
    }

    for (Variable e_var = 1; e_var <= maxVarIndex(); ++e_var) {
        if (!isExistential(e_var) || depends(e_var, u_var)) continue;

        const Literal ep = var2lit(e_var, false);
        const Literal en = var2lit(e_var, true);

        if (quadrangle) {
            if ( (!seen_pos[ep] || !seen_neg[ep]) && (!seen_neg[ep] || !seen_pos[en])) {
                if (pseudo_deps == nullptr) addDependency(u_var, e_var);
                else pseudo_deps->insert(e_var);
                ++count;
            }
        } else {
            if ( (!seen_pos[ep] && !seen_pos[en]) || (!seen_neg[ep] && !seen_neg[en])) {
                if (pseudo_deps == nullptr) addDependency(u_var, e_var);
                else pseudo_deps->insert(e_var);
                ++count;
            }
        }
    }

    clearSeen();
    stat_dep_schemes += count;
    return count > 0;
}


bool Formula::stdTriDep(bool resolution_paths, bool triangle)
{
    bool modified = false;
    for (Variable u_var = minVarIndex(); u_var <= maxVarIndex(); ++u_var) {
        if (!isUniversal(u_var)) continue;
        if (stdTriDep(u_var, resolution_paths, triangle)) modified = true;
    }

    return modified;
}


/**
 * \brief Implementation of the standard and reflexive triangle dependency scheme for removing pseudo-dependencies
 *
 * The dependency scheme can either use normal
 * or resolution paths. Identified pseudo-dependencies are
 * removed from the dependency sets.
 * \note For a QBF prefix, the function may only be called if the
 *       parameter `pseudo_deps` is not nullptr.
 * \param u_var the universal variables whose dependencies are to be analyzed
 * \param resolution_paths if true, use resolution paths
 * \param triangle if true use the reflexive triangle instead of the standard dependency scheme
 * \param pseudo_deps if not nullptr, the removable dependencies are stored in pseudo_deps; otherwise they are removed.
 * \return true if the formula was modified
 * \sa invStdTriDep(bool, bool)
 * \sa sstdQuadDep(bool, bool)
 * \sa invSstdQuadDep(bool, bool)
 */
bool Formula::stdTriDep(Variable u_var, bool resolution_paths, bool triangle, std::set<Variable>* pseudo_deps)
{
    val_assert(minVarIndex() <= u_var && u_var <= maxVarIndex());
    val_assert(isUniversal(u_var));
    val_assert(prefix != nullptr);
    val_assert(dqbf_prefix != nullptr || pseudo_deps != nullptr);

    int count = 0;
    const auto forbidden = [this, u_var](Literal lit) -> bool
    {
        return isUniversal(lit2var(lit)) || !depends(lit2var(lit), u_var);
    };

    // Peforming depth-first search starting at 'u_var'.
    if (resolution_paths)
        searchResolutionPath({var2lit(u_var, true), var2lit(u_var,false)}, forbidden, _seen);
    else {
        searchPath({var2lit(u_var, true), var2lit(u_var,false)}, forbidden, _seen);
    }

    for (Variable e_var = 1; e_var <= maxVarIndex(); ++e_var) {
        if (!isExistential(e_var) || !depends(e_var, u_var)) continue;

        const Literal ep = var2lit(e_var, false);
        const Literal en = var2lit(e_var, true);

        if ( (triangle && (!_seen[en] || !_seen[ep]))
             || (!triangle && !_seen[en] && !_seen[ep]) ) {
            if (pseudo_deps == nullptr) removeDependency(e_var, u_var);
            else pseudo_deps->insert(e_var);
            ++count;
        }
    }

    clearSeen();
    stat_dep_schemes -= count;
    return count > 0;
}


bool Formula::sstdQuadDep(bool resolution_paths, bool quadrangle)
{
    bool modified = false;
    for (Variable u_var = minVarIndex(); u_var <= maxVarIndex(); ++u_var) {
        if (!isUniversal(u_var)) continue;
        if (sstdQuadDep(u_var, resolution_paths, quadrangle)) modified = true;
    }

    return modified;
}


/**
 * \brief Implementation of the strict standard and reflexive quadrangle dependency scheme for removing pseudo-dependencies
 *
 * The dependency scheme can either use normal
 * or resolution paths. Identified pseudo-dependencies are
 * removed from the dependency sets.
 * \note For a QBF prefix, the function may only be called if the
 *       parameter `pseudo_deps` is not nullptr.
 * \param resolution_paths if true, use resolution paths
 * \param quadrangle if true, reflexive quadrangle dependencies are computed
 * \param pseudo_deps if not nullptr, the removable dependencies are stored in pseudo_deps; otherwise they are removed.
 * \return true if the formula was modified
 * \sa stdTriDep(bool, bool)
 * \sa invStdTriDep(bool, bool)
 * \sa invSstdQuadDep(bool, bool)
 */
bool Formula::sstdQuadDep(Variable u_var, bool resolution_paths, bool quadrangle, std::set<Variable>* pseudo_deps)
{
    val_assert(minVarIndex() <= u_var && u_var <= maxVarIndex());
    val_assert(isUniversal(u_var));
    val_assert(prefix != nullptr);
    val_assert(dqbf_prefix != nullptr || pseudo_deps != nullptr);

    int count = 0;
    std::vector<unsigned char>& seen_pos = _seen;
    std::vector<unsigned char> seen_neg(maxLitIndex() + 1, false);

    const auto forbidden = [this, u_var](Literal lit) -> bool
    {
        return isUniversal(lit2var(lit)) || !depends(lit2var(lit), u_var);
    };

    seen_pos.assign(seen_pos.size(), false);
    seen_neg.assign(seen_neg.size(), false);

    if (resolution_paths) {
        // Peforming depth-first search starting at 'u_var'.
        searchResolutionPath({var2lit(u_var, false)}, forbidden, seen_pos);

        // Peforming depth-first search starting at '!u_var'.
        searchResolutionPath({var2lit(u_var, true)}, forbidden, seen_neg);
    } else {
        // Peforming depth-first search starting at 'u_var'.
        searchPath({var2lit(u_var, false)}, forbidden, seen_pos);

        // Peforming depth-first search starting at '!u_var'.
        searchPath({var2lit(u_var, true)}, forbidden, seen_neg);
    }

    for (Variable e_var = 1; e_var <= maxVarIndex(); ++e_var) {
        if (!isExistential(e_var) || !depends(e_var, u_var)) continue;

        const Literal ep = var2lit(e_var, false);
        const Literal en = var2lit(e_var, true);

        if (quadrangle) {
            if ( (!seen_pos[ep] || !seen_neg[ep]) || (!seen_neg[ep] && !seen_pos[en]) ) {
                if (pseudo_deps == nullptr) removeDependency(e_var, u_var);
                else pseudo_deps->insert(e_var);
                ++count;
            }
        } else {
            if ( (!seen_pos[en] && !seen_pos[ep]) || (!seen_neg[en] && !seen_neg[ep]) ) {
                if (pseudo_deps == nullptr) removeDependency(e_var, u_var);
                else pseudo_deps->insert(e_var);
                ++count;
            }
        }
    }

    clearSeen();
    stat_dep_schemes -= count;
    return count > 0;
}


/**
 * \brief Uses gate detection to identify pseudo-dependencies.
 * \param operation specifies whether pseudo-dependencies are added, removed, or only identified.
 * \param gate_outputs if not nullptr, it contains afterwards the gate output variables
 *        in topological order.
 * \return true if the formula was modified.
 */
bool Formula::gateDependencies(DependencyOperation operation)
{
    val_assert(prefix != nullptr);
    val_assert(operation != DependencyOperation::REMOVE || prefix->type() == PrefixType::DQBF);

    int count = 0;

    const std::vector<Gate> gates = determineGates();

    if (operation == DependencyOperation::ADD) {
        // We can make all gate outputs depend on all universal variables
        // as they are implied by the gate inputs
        for (const auto& g: gates) {
            const Variable output_var = lit2var(g.output_literal);
            count += prefix->numUVars() - numDependencies(output_var);
            prefix->moveToRMB(output_var);
        }
    } else if (operation == DependencyOperation::REMOVE) {
        for (const auto& g: gates) {
            const Variable outp_var = lit2var(g.output_literal);
            std::set<Variable> new_deps;
            for (unsigned int inp_lit: g.input_literals) {
                const Variable inp_var = lit2var(inp_lit);
                if (isUniversal(inp_var)) new_deps.insert(inp_var);
                else {
                    const auto& inp_deps = dqbf_prefix->getDependencies(inp_var);
                    new_deps.insert(inp_deps.cbegin(), inp_deps.cend());
                }
            }
            count += new_deps.size() - dqbf_prefix->numDependencies(outp_var);
            dqbf_prefix->setDependencies(outp_var, std::move(new_deps));
        }
    }

    stat_dep_schemes += count;
    return count != 0;
}


/**
 * \brief Applies a dependency scheme to the formula to manipulate the dependency sets.
 * \param scheme specifies which dependency scheme is applied
 * \param operation determines whether dependencies should be added or removed
 * \param gate_outputs if scheme is DependencyScheme::GATE, this parameter is filled with the gate ouputs.
 * \return true if the formula was modified.
 */
bool Formula::applyDependencyScheme(
    DependencyScheme scheme,
    DependencyOperation operation)
{
    val_assert(prefix != nullptr);
    val_assert_msg(prefix->type() == PrefixType::DQBF, "Dependency schemes are currently only supported for DQBF prefixes");
    val_assert(dqbf_prefix != nullptr);

    ScopeTimer dependency(dependency_time);

    switch(scheme) {
    case DependencyScheme::TRIVIAL:
        return false;
    case DependencyScheme::STANDARD:
        if (operation == DependencyOperation::REMOVE)   return stdTriDep(false, false);
        else if (operation == DependencyOperation::ADD) return invStdTriDep(false, false);
        break;
    case DependencyScheme::STRICT_STANDARD:
        if (operation == DependencyOperation::REMOVE)   return sstdQuadDep(false, false);
        else if (operation == DependencyOperation::ADD) return invSstdQuadDep(false, false);
        break;
    case DependencyScheme::REF_TRIANGLE:
        if (operation == DependencyOperation::REMOVE)   return stdTriDep(false, true);
        else if (operation == DependencyOperation::ADD) return invStdTriDep(false, true);
        break;
    case DependencyScheme::REF_QUADRANGLE:
        if (operation == DependencyOperation::REMOVE)   return sstdQuadDep(false, true);
        else if (operation == DependencyOperation::ADD) return invSstdQuadDep(false, true);
        break;
    case DependencyScheme::RP_STANDARD:
        if (operation == DependencyOperation::REMOVE)   return stdTriDep(true, false);
        else if (operation == DependencyOperation::ADD) return invStdTriDep(true, false);
        break;
    case DependencyScheme::RP_STRICT_STANDARD:
        if (operation == DependencyOperation::REMOVE)   return sstdQuadDep(true, false);
        else if (operation == DependencyOperation::ADD) return invSstdQuadDep(true, false);
        break;
    case DependencyScheme::RP_REF_TRIANGLE:
        if (operation == DependencyOperation::REMOVE)   return stdTriDep(true, true);
        else if (operation == DependencyOperation::ADD) return invStdTriDep(true, true);
        break;
    case DependencyScheme::RP_REF_QUADRANGLE:
        if (operation == DependencyOperation::REMOVE)   return sstdQuadDep(true, true);
        else if (operation == DependencyOperation::ADD) return invSstdQuadDep(true, true);
        break;
    case DependencyScheme::GATE:
        return gateDependencies(operation);
        break;
    default:
        std::cerr << "[ERROR] Invalid dependency scheme." << std::endl;
        return false;
        break;
    } // end switch

    return false;
}


} // end namespace hqspre
