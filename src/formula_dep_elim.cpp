#include <vector>
#include <utility>
#include "formula.hpp"

/**
 * \file formula_dep_elim.cpp
 * \brief Implementation of dependency elimination
 * \author Ralf Wimmer
 * \date 02/2016
 */


namespace hqspre {

/**
 * \brief Eliminates a single dependency from the formula.
 *
 * If the dependency \f$x\in D_y\f$ is to be eliminated, this is done
 * by introducing two additional variables \f$y^0\f$ and \f$y^1\f$ and
 * adding clauses for \f$y \equiv((x\land y^1)\lor(\neg x\land y^0))\f$.
 * Then the new variables can be independent of \f$x\f$.
 * In case that there is an implication \f$(\neg)x\to (\neg)y\f$, we can omit
 * one of the new variables.
 * Afterwards, \f$y\f$ is a Tseitin variable (for a multiplexer output)
 * and depends on all universal variables.
 *
 * \todo Use a SAT call to test for an implication between \f$x\f$ and \f$y\f$.
 */
void Formula::eliminateDependency(Variable x, Variable y)
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() == PrefixType::DQBF);
    val_assert(dqbf_prefix != nullptr);
    val_assert(minVarIndex() <= x && x <= maxVarIndex());
    val_assert(minVarIndex() <= y && y <= maxVarIndex());
    val_assert(isUniversal(x));
    val_assert(isExistential(y));

    // ITE(a,b,c)=d
    //    is the same as
    // (a,c,~d), (~a,b,~d), (~a,~b,d), (a,~c,d)

    TruthValue v0 = TruthValue::UNKNOWN;
    TruthValue v1 = TruthValue::UNKNOWN;

    // If we have an implication x => y then y1 must be 1. In this case
    // we can simplify the clauses by removing the one that contains y1.
    // The one that contains ~y1 can be removed as well because it simplifies
    // to (~x or y1) which is equivalent to x => y.
    // A similar argumentation applies for the other cases x => ~y, ~x => y, ~x => ~y.
    auto implied = hasImplicationTransitive(var2lit(x, false), y);
    if (implied.first)  v1 = TruthValue::TRUE;
    if (implied.second) v1 = TruthValue::FALSE;

    implied = hasImplicationTransitive(var2lit(x, true), y);
    if (implied.first)  v0 = TruthValue::FALSE;
    if (implied.second) v0 = TruthValue::FALSE;

    // Create two new existential variables y0, y1
    removeDependency(x,y);
    Variable y0 = 0;
    Variable y1 = 0;

    // Add clauses for y = ITE(x, y1, y0)
    if (v0 == TruthValue::UNKNOWN) {
        y0 = copyVar(y);
        addClause( {var2lit(x, false), var2lit(y0, false), var2lit(y, true)}  );
        addClause( {var2lit(x, false), var2lit(y0, true),  var2lit(y, false)} );
    }

    if (v1 == TruthValue::UNKNOWN) {
        y1 = copyVar(y);
        addClause( {var2lit(x, true),  var2lit(y1, false), var2lit(y, true)}  );
        addClause( {var2lit(x, true),  var2lit(y1, true),  var2lit(y, false)} );
    }

    // make y depend on all universal variables
    prefix->moveToRMB(y);
}


} // end namespace hqspre
