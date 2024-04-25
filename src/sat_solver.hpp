#ifndef HQSPRE_SAT_SOLVER_HPP_
#define HQSPRE_SAT_SOLVER_HPP_

#include <vector>
#include <antom/antom.hpp>
#include "aux.hpp"
#include "literal.hpp"
#include "clause.hpp"
#include "timer.hpp"

/**
 * \file sat_solver.hpp
 * \author Ralf Wimmer
 * \date 2016-08
 * \brief Implementation of a consistent interface for different SAT solvers.
 */

namespace hqspre {

/**
 * \brief Base class for different SAT solvers.
 *
 * It provides a common interface to solvers like Antom, Picosat, and Lingeling.
 * The interface is taylored towards the usage in the HQSpre preprocessor and
 * does not provide access to all supported functions.
 */
class SatSolverInterface
{
public:
    SatSolverInterface() = default;
    SatSolverInterface(const SatSolverInterface&) = delete;
    SatSolverInterface(SatSolverInterface&&) = default;
    virtual ~SatSolverInterface() = default;
    SatSolverInterface& operator=(const SatSolverInterface&) = delete;
    SatSolverInterface& operator=(SatSolverInterface&&) = default;

    /**
     * \brief Gives the solver a hint on the number of used variables.
     */
    virtual void setMaxIndex(Variable var) = 0;

    /**
     * \brief Adds a clause to the SAT solver's clause database.
     */
    virtual void addClause(std::vector<unsigned int>& clause) = 0;

    /**
     * \brief Adds a unit clause to the SAT solver's clause database.
     */
    virtual bool addUnit(Literal lit) = 0;

    /**
     * \brief Instructs the decision heuristics of the SAT solver how to assign variables first.
     *
     * If `value` is true, then the decision heuristics tries value `true` first
     * when assigning `var`, otherwise `false`.
     */
    virtual void setPolarity(Variable var, bool value) = 0;

    /**
     * \brief Sets a time limit (in seconds) for the solution of the formula.
     */
    virtual void setTimeout(double time) = 0;

    /**
     * \brief Solves the formula.
     * \return TruthValue::TRUE if the formula is satisfiable, TruthValue::FALSE if it
     *         is unsatisfiable, and TruthValue::UNKNOWN if the formula could not be solved.
     */
    virtual TruthValue solve() = 0;

    /**
     * \brief Solves the formula under the given assumptions.
     * \return TruthValue::TRUE if the formula is satisfiable, TruthValue::FALSE if it
     *         is unsatisfiable, and TruthValue::UNKNOWN if the formula could not be solved.
     */
    virtual TruthValue solve(const std::vector<Literal>& assumptions) = 0;


    /**
     * \brief Returns the value of the given variable in the computed satisfying assignment.
     * \pre SatSolver::solve must be called before and the formula must have been determined
     *      to be satisfiable. Otherwise the behavior of this function is undefined.
     */
    virtual TruthValue getValue(Variable var) = 0;

private:
};


/**
 * \brief An interface for the Antom SAT solver by Tobias Schubert and Sven Reimer
 */
class Antom: public SatSolverInterface
{
public:
    Antom():
        SatSolverInterface(),
        solver()
    {}

    virtual ~Antom() = default;

    virtual void setMaxIndex(Variable var) override
    {
        solver.setMaxIndex(var);
    }

    virtual void addClause(std::vector<unsigned int>& clause) override
    {
        solver.addClause(clause);
    }

    virtual bool addUnit(Literal lit) override
    {
        return solver.addUnit(lit);
    }

    virtual void setPolarity(Variable var, bool value) override
    {
        // force solver to take a certain polarity
        // strategy = 3 => set always true, strategy = 2 => set always false
        const unsigned int strategy = (value ? 3 : 2);
        solver.setDecisionStrategyForVariable(strategy, var);
    }

    virtual void setTimeout(double time) override
    {
        solver.setCPULimit(time);
    }

    virtual TruthValue solve(const std::vector<Literal>& assumptions) override
    {
        const auto value = solver.solve(assumptions);
        if (value == ANTOM_UNSAT) return TruthValue::FALSE;
        else if (value == ANTOM_SAT) return TruthValue::TRUE;
        else return TruthValue::UNKNOWN;
    }

    virtual TruthValue solve() override
    {
        const auto value = solver.solve();
        if (value == ANTOM_UNSAT) return TruthValue::FALSE;
        else if (value == ANTOM_SAT) return TruthValue::TRUE;
        else return TruthValue::UNKNOWN;
    }

    virtual TruthValue getValue(Variable var) override
    {
        if (solver.model()[var] == 0) return TruthValue::UNKNOWN;
        else if (isNegative(solver.model()[var])) return TruthValue::FALSE;
        else return TruthValue::TRUE;
    }

private:
    antom::Antom solver;
};


} // end namespace hqspre

#endif
