#include <vector>
#include <stack>
#include <iostream>
#include "aux.hpp"
#include "formula.hpp"
#include "bool_vector.hpp"

/**
 * \file formula_equiv.cpp
 * \brief Detection of equivalent variables
 * \author Ralf Wimmer
 * \date 02/2016
 */

namespace hqspre {

/**
 * \brief Tarjan's algorithm for computing strongly connected components.
 */
static void visitSCC(
    const std::vector<std::set<BinaryClause>>& implications,
    Literal n,
    int& calls,
    std::vector<int>& scc,
    std::vector<int>& root,
    int& nextscc,
    std::stack<Literal>& stk)
{
    if (root[n] != -1) return;

    root[n] = calls;
    scc[n] = -1;
    stk.push(n);

    const int savecalls = calls;
    ++calls;

    for (BinaryClause clause: implications[n]) {
        const Literal impl = clause.getLiteral();
        visitSCC(implications, impl, calls, scc, root, nextscc, stk);

        if (scc[impl] == -1 &&
            root[impl] != -1 &&
            root[impl] < root[n] )
        {
            root[n] = root[impl];
        }
    }

    if (root[n] == savecalls)
    {
        Literal m = 0;
        do {
            m = stk.top();
            stk.pop();

            scc[m] = nextscc;
        }
        while (m != n);

        ++nextscc;
    }
}


/**
 * \brief Tries to find equivalent literals by SCC decomposition of the implication graph.
 *
 * This function analyzes the graph formed by the implications.
 * All literals in the same strongly connected component are equivalent.
 * They are replaced by a single representative.
 * \throws UNSATException if an SCC contains more than one universal literal.
 * \throws UNSATException if an SCC contains a universal literal and an existential
 *         one that does not depend upon it.
 * \return true if the formula was modified.
 */
bool Formula::findEquivalences()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer equiv(equiv_time);
    unsigned int count = 0;

    // First determine the strongly connected components of the implication graph
    std::vector<int> root(maxLitIndex() + 1, -1);
    std::vector<int> scc(maxLitIndex() + 1, -1);
    int calls = 0;
    int nextscc = 0;
    std::stack<Literal> stk;

    std::vector<Literal> candidates;
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if ( !varDeleted(var) && !implications[var2lit(var,false)].empty() && !implications[var2lit(var,true)].empty())
        {
            candidates.push_back(var2lit(var, false));
            candidates.push_back(var2lit(var, true));
        }
    }

    for (const Literal lit: candidates) {
        visitSCC(implications, lit, calls, scc, root, nextscc, stk );
    }

    if (interrupt) return false;

    // Check if there is an SCC which contains a variable both
    // positively and negatively. Then the formula is UNSAT.
    std::vector<std::vector<Literal> > sccs( nextscc );

    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        const Literal pos = var2lit(var, false);
        const Literal neg = var2lit(var, true);

        if (scc[ pos ] != -1 && scc[ pos ] == scc[ neg ] ) {
            // var and ~var in the same SCC -> UNSAT
            throw UNSATException("A literal and its negation in one SCC", this);
        }
        if (scc[pos] != -1) sccs[scc[pos]].push_back(pos);
        if (scc[neg] != -1) sccs[scc[neg]].push_back(neg);
    }

    // Now 'sccs' is a vector of the all SCCs.
    for (const auto& p: sccs)
    {
        if (interrupt) break;
        if (p.size() < 2) continue;
        count += replaceSCC(p);
    }

    stat_equiv += count;

    if (setting.verbosity > 1 && count > 0) {
        std::cout << "c " << __FUNCTION__ << " found " << count <<  " equivalences" << std::endl;
    }
    return count > 0;
}


/**
 * \brief Replaces an SCC in the implication graph by a single literal.
 *
 * \throws UNSATException if an SCC contains more than one universal literal.
 * \throws UNSATException if an SCC contains a universal literal and an existential
 *         one that does not depend upon it.
 * \return the number of eliminated variables.
 */
unsigned int Formula::replaceSCC(const std::vector<Literal>& scc)
{
    val_assert(prefix != nullptr);

    // count universals on scc
    unsigned int countUniversal = 0;
    Literal universal_literal = 0;
    unsigned int count = 0;

    for (const Literal q: scc)
    {
        if (isUniversal(lit2var(q))) {
            ++countUniversal;
            universal_literal = q;
        }
    } // end loop over scc

    if (countUniversal > 1) {
        // More than one universal variable in an SCC -> UNSAT
        throw UNSATException("More than one universal variable in one SCC", this);
    } else if (countUniversal == 1) {
        // Check if all existential variables in this SCC depend on the universal one.
        // If no: UNSAT
        // If yes: all existential variables can be replaced by the universal one.

        const Variable univ_var = lit2var(universal_literal);
        val_assert(isUniversal(univ_var));
        val_assert(!varDeleted(univ_var));

        for (const Literal q: scc) {
            if (q == universal_literal) continue;
            if (varDeleted(lit2var(q))) continue;

            const Variable current_var = lit2var(q);
            val_assert(isExistential(current_var));

            if (!depends(current_var, univ_var)) {
                // The current SCC contains a universal variable and
                // an existential one that does not depend on the universal.
                // -> UNSAT
                throw UNSATException("Existential variable equivalent to a universal one, but independent of it", this);
            } else {
                // Replace q by universal_literal:
                replaceLiteral(q, universal_literal);
                val_assert(occ_list[q].empty() && occ_list[negate(q)].empty());

                if (setting.verbosity > 2 ) {
                    std::cout << "c " << __FUNCTION__ << "(): replacing " << lit2dimacs(q) << " by univ. literal " << lit2dimacs(universal_literal) << std::endl;
                }

                ++count;
            }
        } // end for
    } // end if (countUniversal == 1)
    else {
        val_assert(countUniversal == 0);

        // At this position the following holds:
        // - SCC contains more than one variable
        // - SCC contains only existential variables
        // - SCC does not contain x and -x at the same time
        // To do:
        // - replace all variables in the SCC by an arbitrary representative
        // - the dependency set of the representative is the intersection of
        //   all dependency sets

        const Literal replacement = scc.front();
        const Variable replacement_var = lit2var(replacement);
        if (varDeleted(replacement_var)) return count;
        // new dependencies for the equivalent variables. At the end it should
        // contain the intersection of the dependency sets of all equivalent variables.

        for (const Literal q: scc) {
            if (q == replacement) continue;
            if (varDeleted(lit2var(q))) continue;

            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "(): replacing " << lit2dimacs(q) << " by exist. literal " << lit2dimacs(replacement) << std::endl;
            }

            prefix->intersectDependencies(replacement_var, lit2var(q));
            replaceLiteral(q, replacement);
            count++;
        }
    } // end if (countUniversal == 0)

    return count;
}

  /**
   * \brief Tries to find binary clauses which complete a equivalence or contradiction definition
   *
   * If the clause (a * b), exists, the method tries to add (~a * ~b), (~a * b) and (a * b)
   * Therefore it is checked whether these clauses are (hidden) blocked within the formula
   * Also performs the variable replacement and/ unit propagation if the search was successful
   * \return true if the formula was modified
   */
bool Formula::findHiddenEquivAndContraDefinitions()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }

    ScopeTimer hidden_ec(hidden_equiv_contra_time);
    process_limit.setLimit(PreproMethod::HEC);

    const unsigned int old_stat_hidden_unit = stat_hidden_unit;
    const unsigned int old_stat_hidden_equiv = stat_hidden_equiv;

    std::vector<Literal> binary_clause(2, 0);
    std::vector<Literal> scc;
    uint64_t sign = 0ul;
    bool found = false;

    for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit) {
        if (interrupt) break;
        binary_clause[0] = lit;
        // reset equivalence container
        scc.clear();
        scc.push_back(lit);

        if (process_limit.reachedLimit()) {
            if (setting.verbosity > 1) {
                std::cout << "c terminate " << __FUNCTION__ << " due to process limit.\n";
            }
            break;
        }

        for (BinaryClause bin : implications[lit]) {
            found = false;
            // remove hidden literals from previous run
            binary_clause.resize(2);
            // first search for equivalence
            binary_clause[1] = negate(bin.getLiteral());
            val_assert(!_seen[binary_clause[0]]);
            val_assert(!_seen[binary_clause[1]]);
            _seen[binary_clause[0]] = true;
            _seen[binary_clause[1]] = true;
            // Add hidden literals and check for tautology
            found = addHiddenLiterals(-1, binary_clause, sign);

            if (!found) {
                // Clause is no hidden tautology => check for hidden blocked clause
                found = clauseBlocked(binary_clause);
            }
            clearSeen(binary_clause);

            if (found) {
                if (setting.verbosity > 2) {
                    std::cout << "c " << __FUNCTION__ << " found equiv binary " << lit2dimacs(binary_clause[0]) << " " << lit2dimacs(binary_clause[1]) << " => " << lit2dimacs(lit) << " and " << lit2dimacs(bin.getLiteral()) << " are hidden equivalent" <<  std::endl;
                }

                // We have to add the clause temporarily, otherwise upcoming checks may become unsound
                std::vector<Literal> added_clause {binary_clause[0], binary_clause[1]};
                addClause(std::move(added_clause), true, false, ClauseStatus::OPTIONAL);
                scc.push_back(bin.getLiteral());
            }

            found = false;
            // remove hidden literals
            binary_clause.resize(2);
            // now search for contradiction
            binary_clause[1] = bin.getLiteral();
            val_assert(!_seen[binary_clause[0]]);
            val_assert(!_seen[binary_clause[1]]);
            _seen[binary_clause[0]] = true;
            _seen[binary_clause[1]] = true;
            // Add hidden literals and check for tautology
            found = addHiddenLiteralsBinary(-1, binary_clause, sign);

            if (!found) {
                // Clause is no hidden tautology => check for hidden blocked clause
                found = clauseBlocked(binary_clause);
            }
            clearSeen(binary_clause);

            if (found) {
                if (setting.verbosity > 2) {
                    std::cout << "c " << __FUNCTION__ << " found contradiction binary (hidden tautology) " << lit2dimacs(binary_clause[0]) << " " << lit2dimacs(binary_clause[1]) << " => " << lit2dimacs(binary_clause[1]) << " is a hidden unit" << std::endl;
                }
                // We have to add the clause temporarily, otherwise upcoming checks may become unsound
                std::vector<Literal> added_clause {binary_clause[0], binary_clause[1]};
                addClause(std::move(added_clause), true, false, ClauseStatus::OPTIONAL);
                pushUnit(binary_clause[1]);
                ++stat_hidden_unit;
            }
        }

        // After all checks for a literal was done, we can now propagate the found units and equivalences
        // It's possible unsafe to perform these operations immediately after a unit/equivalence was detected
        unitPropagation();
        if (scc.size() > 1) {
            const unsigned int new_equiv = replaceSCC(scc);
            stat_equiv += new_equiv;
            stat_hidden_equiv += new_equiv;
        }
    }

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " found " << (stat_hidden_unit - old_stat_hidden_unit)
                  << " new units via contradictions and " << (stat_hidden_equiv - old_stat_hidden_equiv)
                  << " new equivalences" << std::endl;
    }
    return (stat_hidden_unit > old_stat_hidden_unit) || (stat_hidden_equiv > old_stat_hidden_equiv);
}


/**
 * \brief Tries to find unit literals by analyzing contradicting implication chains.
 *
 * If a literal \f$a\f$ transitively implies \f$\neg a\f$, then \f$\neg a\f$ is a unit literal.
 * This is done by investigating the implication graph defined by the data structure
 * 'implications'.
 * \return true if the formula was modified
 */
bool Formula::findContradictions()
{
    if (setting.verbosity > 0) {
        std::cout << "c " << __FUNCTION__ << std::endl;
    }
    ScopeTimer contra(contra_time);

    process_limit.setLimit(PreproMethod::CONTRA);

    unsigned int count = 0;
    const unsigned int litcount = maxLitIndex() + 1;

    std::vector<int> usedSource;
    usedSource.reserve( litcount );
    std::vector<int> usedTarget;
    usedTarget.reserve( litcount );
    std::vector<int> usedSourceMap( litcount, -1 );
    std::vector<int> usedTargetMap( litcount, -1 );

    for (Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit )
    {
        if (interrupt) return false;

        if (!implications[lit].empty()) {
            usedSourceMap[lit] = static_cast<int>( usedSource.size() );
            usedSource.push_back(lit);

            usedTargetMap[ negate(lit) ] = static_cast<int>( usedTarget.size() );
            usedTarget.push_back( negate(lit) );
        }
    }

    typedef std::vector<BoolVector> ReachMatrix;
    ReachMatrix reach( usedSource.size() );

    for( Literal lit = minLitIndex(); lit <= maxLitIndex(); ++lit )
    {
        if (interrupt) return false;
        if (usedSourceMap[ lit ] == -1) continue;

        BoolVector& reach_n = reach[ usedSourceMap[ lit ] ];
        val_assert( reach_n.uninitialized() );
        reach_n.initialize( usedTarget.size(), false );

        process_limit.decreaseLimitBy(implications[lit].size());

        for( BinaryClause impl: implications[lit] )
        {
            reach_n.set( usedTargetMap[ impl.getLiteral() ], true );
        }
    }

    for (unsigned int via = 0; via != usedSource.size(); ++via)
    {
        if (interrupt) return false;

        const int viaTarget =  usedTargetMap[ usedSource[ via ] ];
        if( viaTarget == -1 ) continue;

        const auto& reach_via = reach[via];

        if (process_limit.reachedLimit()) {
            if (setting.verbosity > 1 ) {
                std::cout << "c building structure of " << __FUNCTION__ << " terminated due to process limit" << std::endl;
            }
            // Deactivate this method if we run into our limits and no new information is obtained
            if (count == 0) {
                setContradictionChecking(false);
            }
            break;
        }

        process_limit.decreaseLimitBy(2, usedSource.size());

        for( unsigned int from = 0; from != usedSource.size(); ++from )
        {
            BoolVector& reach_from = reach[ from ];

            if( !reach_from.get( viaTarget ) ) continue;

            reach_from |= reach_via;
        }
    }

    // check for i -> !i (i.e., we have the unit literal !i)
    for (unsigned int i = 0; i != usedSource.size(); ++i)  {
        const int j = usedTargetMap[ negate( usedSource[ i ] ) ];

        if (reach[i].get(j) ) {

            if (setting.verbosity > 2) {
                std::cout << "c " << __FUNCTION__ << "(): " << lit2dimacs( usedSource[ i ] ) << " -> " << lit2dimacs( usedTarget[ j ] ) << std::endl;
            }
            ++count;
            pushUnit(usedTarget[j]);
        }
    }

    unitPropagation();

    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " found " << count << " contradictions" << std::endl;
    }

    stat_contradictions += count;
    return count > 0;
}

} // end namespace hqspre
