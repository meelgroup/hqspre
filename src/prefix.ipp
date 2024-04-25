#ifndef HQSPRE_PREFIX_IPP_
#define HQSPRE_PREFIX_IPP_

/**
 * \file prefix.ipp
 * \brief Inline functions for manipulating a formula's quantifier prefix
 * \author Ralf Wimmer
 * \date 06/2016
 */

namespace hqspre {

/**
 * \brief Returns true if the variable is universal and has not been deleted.
 */
inline bool Prefix::isUniversal(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    return var_status[var] == VariableStatus::UNIVERSAL;
}


/**
 * \brief Returns true if the variable is existential and has not been deleted.
 */
inline bool Prefix::isExistential(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    return var_status[var] == VariableStatus::EXISTENTIAL;
}


/**
 * \brief Returns true if the variable has been deleted.
 */
inline bool Prefix::varDeleted(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    return var_status[var] == VariableStatus::DELETED;
}


//--------------------------------------------------------


/**
 * \brief Creates a copy of the given variable.
 *
 * The copy inherits the dependencies of the given variable.
 * \return the index of the newly created variable.
 */
inline void Prefix::makeCopy(const Variable var, const Variable original)
{
    val_assert(varDeleted(var));
    val_assert(!varDeleted(original));
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    if (isExistential(original))    Prefix::addEVar(var);
    else if (isUniversal(original)) Prefix::addUVar(var);
}


inline void DQBFPrefix::makeCopy(const Variable var, const Variable original)
{
    val_assert(varDeleted(var));
    val_assert(!varDeleted(original));
    Prefix::makeCopy(var, original);
    if (in_rmb[original]) moveToRMB(var);
    else setDependencies(var, dependencies[original]);
}


inline void QBFPrefix::makeCopy(const Variable var, const Variable original)
{
    val_assert(varDeleted(var));
    val_assert(!varDeleted(original));
    Prefix::makeCopy(var, original);
    depth[var] = depth[original];
    blocks[depth[original]].insert(var);
}

//--------------------------------------------------------

/**
 * \brief Clears the prefix and removes all variables.
 */
inline void Prefix::clear()
{
    var_status.resize(1);
    num_e_vars = 0;
    num_u_vars = 0;
}


/**
 * \brief Clears the prefix and removes all variables.
 */
inline void QBFPrefix::clear()
{
    Prefix::clear();
    depth.resize(1);
    blocks.clear();
}


/**
 * \brief Clears the prefix and removes all variables.
 */
inline void DQBFPrefix::clear()
{
    Prefix::clear();
    dependencies.resize(1);
    rmb.clear();
    in_rmb.resize(1);
    univ_vars.clear();
}

//--------------------------------------------------------


/**
 * \brief Creates a new existential variable
 * \param var the index of the variable that should be created
 */
inline void Prefix::addEVar(const Variable var)
{
    val_assert(varDeleted(var));

    var_status[var] = VariableStatus::EXISTENTIAL;
    ++num_e_vars;
}


inline void QBFPrefix::addEVar(const Variable var)
{
    val_assert(varDeleted(var));
    Prefix::addEVar(var);

    unsigned int var_depth = 0;
    if (blocks.empty()) {
        var_depth = blocks.size();
        blocks.push_back({var});
    } else if (blocks.back().empty() || isExistential(*(blocks.back().begin()))) {
        var_depth = blocks.size() - 1;
        blocks[var_depth].insert(var);
    } else {
        var_depth = blocks.size();
        blocks.push_back({var});
    }
    if (depth.size() <= var) depth.resize(var + 1);
    depth[var] = var_depth;
}


//--------------------------------------------------------


/**
 * \brief Creates a new universal variable.
 * \param var the index of the variable that should be created.
 */
inline void Prefix::addUVar(const Variable var)
{
    val_assert(varDeleted(var));

    var_status[var] = VariableStatus::UNIVERSAL;
    ++num_u_vars;
}


inline void DQBFPrefix::addUVar(const Variable var)
{
    val_assert(varDeleted(var));

    Prefix::addUVar(var);

    // All variables which were in the RMB so far,
    // become ordinary variables.
    for (Variable evar: rmb) {
        in_rmb[evar] = false;
        dependencies[evar] = univ_vars;
    }
    rmb.clear();

    univ_vars.insert(var);
}


inline void QBFPrefix::addUVar(const Variable var)
{
    val_assert(varDeleted(var));

    Prefix::addUVar(var);

    unsigned int var_depth = 0;
    if (blocks.empty()) {
        var_depth = blocks.size();
        blocks.push_back({var});
    } else if (blocks.back().empty() || isUniversal(*(blocks.back().begin()))) {
        var_depth = blocks.size() - 1;
        blocks[var_depth].insert(var);
    } else {
        var_depth = blocks.size();
        blocks.push_back({var});
    }
    if (depth.size() <= var) depth.resize(var + 1);
    depth[var] = var_depth;
}


//--------------------------------------------------------


/**
 * \brief Sets the maximal index of the variables that will be created.
 * \param index the maximal index
 *
 * The function is used to resize the data structures such that all
 * occurring variables can be stored without further size adaptations.
 * Creating more variables than specified is allowed (it is just less
 * efficient).
 */
inline void Prefix::setMaxVarIndex(Variable index)
{
    if (index > maxVarIndex()) {
        var_status.resize(index + 1, VariableStatus::DELETED);
    }
}


inline void DQBFPrefix::setMaxVarIndex(Variable index)
{
    if (index > maxVarIndex()) {
        Prefix::setMaxVarIndex(index);
        dependencies.resize(index + 1);
        in_rmb.resize(index + 1, false);
    }
}

inline void QBFPrefix::setMaxVarIndex(Variable index)
{
    if (index > maxVarIndex()) {
        Prefix::setMaxVarIndex(index);
        depth.resize(index + 1, 0);
    }
}


//--------------------------------------------------------


/**
 * \brief Removes a given variable from the prefix.
 * \param var the index of the variable that should be removed
 */
inline void Prefix::removeVar(Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    if (varDeleted(var)) return;

    if (isExistential(var)) --num_e_vars;
    else if (isUniversal(var)) --num_u_vars;
    var_status[var] = VariableStatus::DELETED;
}


/**
 * \brief Removes a given variable from the prefix.
 * \param var the index of the the variable that should be removed
 */
inline void DQBFPrefix::removeVar(Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    if (varDeleted(var)) return;

    if (isUniversal(var)) univ_vars.erase(var);

    if (in_rmb[var]) {
        in_rmb[var] = false;
        rmb.erase(var);
        for (Variable univ: univ_vars) dependencies[univ].erase(var);
    } else {
        for (Variable dep: dependencies[var]) {
            dependencies[dep].erase(var);
        }
        dependencies[var].clear();
    }

    Prefix::removeVar(var);
}


/**
 * \brief Removes a given variable from the prefix.
 * \param var the index of the variable that should be removed
 */
inline void QBFPrefix::removeVar(Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    if (varDeleted(var)) return;

    const unsigned int var_depth = depth[var];
    blocks[var_depth].erase(var);
    depth[var] = 0;
    Prefix::removeVar(var);
}


//--------------------------------------------------------


/**
 * \brief Returns the type of the prefix.
 */
inline PrefixType DQBFPrefix::type() const noexcept
{
    return PrefixType::DQBF;
}


/**
 * \brief Returns the type of the prefix.
 */
inline PrefixType QBFPrefix::type() const noexcept
{
    return PrefixType::QBF;
}


//--------------------------------------------------------


/**
 * \brief Checks if one variable depends on another one.
 * \pre One variable must be universal, the other one existential
 * \param var1 one of the variables
 * \param var2 the other variable
 * \return true if the existential variable depends on the universal one
 * \note The order in which the variables are given does not matter.
 */
inline bool DQBFPrefix::depends(Variable var1, Variable var2) const
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(!varDeleted(var1) && !varDeleted(var2));
    val_assert(isUniversal(var1) != isUniversal(var2));

    if (in_rmb[var1] || in_rmb[var2]) return true;
    else return dependencies[var1].find(var2) != dependencies[var1].cend();
}


/**
 * \brief Checks if one variable depends on another one.
 * \pre One variable must be universal, the other one existential
 * \param var1 one of the variables
 * \param var2 the other variable
 * \return true if the existential variable depends on the universal one,
 *           i.e., if the existential is right of the universal variable.
 * \note The order in which the variables are given does not matter.
 */
inline bool QBFPrefix::depends(Variable var1, Variable var2) const
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(!varDeleted(var1) && !varDeleted(var2));
    val_assert(isUniversal(var1) != isUniversal(var2));

    if (isUniversal(var1) && getLevel(var1) < getLevel(var2)) return true;
    if (isUniversal(var2) && getLevel(var2) < getLevel(var1)) return true;
    return false;
}


//--------------------------------------------------------


/**
 * \brief Checks if `var1`'s dependencies are a subset of `var2`'s dependencies.
 *
 * If `var1` is universal, this function returns whether `var2` depends on `var1`.
 * If both variables are existential, this function checks whether the dependency
 * set of `var1` is a subset of `var2`'s dependencies.
 *
 * \note `var2` has to be existential.
 */
inline bool DQBFPrefix::dependenciesSubset(Variable var1, Variable var2) const
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(!varDeleted(var1) && !varDeleted(var2));
    val_assert(isExistential(var2));

    if (var1 == var2) return true;
    if (in_rmb[var2]) return true;
    if (in_rmb[var1] && !in_rmb[var2]) return false;
    if (isUniversal(var1)) return depends(var2, var1);
    if (dependencies[var1].size() > dependencies[var2].size()) return false;

    return std::includes(dependencies[var2].cbegin(), dependencies[var2].cend(),
                         dependencies[var1].cbegin(), dependencies[var1].cend());
}


/**
 * \brief Checks if `var1`'s dependencies are a subset of `var2`'s dependencies.
 *
 * If `var1` is universal, this function returns whether `var2` depends on `var1`.
 * If both variables are existential, this function checks whether the dependency
 * set of `var1` is a subset of `var2`'s dependencies.
 * If both variables are universal, the function returns whether 'var1' depends on
 * more variables than 'var2'
 * \note `var2` has to be existential.
 */
inline bool QBFPrefix::dependenciesSubset(Variable var1, Variable var2) const
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(!varDeleted(var1) && !varDeleted(var2));

    if (var1 == var2) return true;
    return getLevel(var1) <= getLevel(var2);
}


//--------------------------------------------------------


inline bool DQBFPrefix::dependsOnAll(Variable var) const
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(!varDeleted(var));
    val_assert(isExistential(var));

    return in_rmb[var];
}


inline bool QBFPrefix::dependsOnAll(Variable var) const
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(!varDeleted(var));
    val_assert(isExistential(var));

    return depth[var] == blocks.size() - 1;
}


//--------------------------------------------------------


inline unsigned int QBFPrefix::getLevel(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    return depth[var];
}


//--------------------------------------------------------



/**
 * \brief Removes a dependency between two variables.
 *
 * If the variables do not depend on each other, this operation
 * does nothing.
 * \pre One variable must be universal, the other one existential.
 */
inline void DQBFPrefix::removeDependency(Variable var1, Variable var2)
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(isUniversal(var1) != isUniversal(var2));
    val_assert(!varDeleted(var1) && !varDeleted(var2));

    if (isExistential(var1) && in_rmb[var1]) {
        dependencies[var1] = univ_vars;
        rmb.erase(var1);
        in_rmb[var1] = false;
    } else if (isExistential(var2) && in_rmb[var2]) {
        dependencies[var2] = univ_vars;
        rmb.erase(var2);
        in_rmb[var2] = false;
    }
    dependencies[var1].erase(var2);
    dependencies[var2].erase(var1);
}


/**
 * \brief Adds a dependency between two variables.
 *
 * If the variables already depend on each other, this operation
 * does nothing.
 * \pre One variable must be universal, the other one existential.
 */
inline void DQBFPrefix::addDependency(Variable var1, Variable var2)
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(!varDeleted(var1) && !varDeleted(var2));
    val_assert(isUniversal(var1) != isUniversal(var2));

    dependencies[var1].insert(var2);
    dependencies[var2].insert(var1);

    if (isExistential(var1) && dependencies[var1].size() == numUVars()) {
        in_rmb[var1] = true;
        rmb.insert(var1);
        dependencies[var1].clear();
    } else if (isExistential(var2) && dependencies[var2].size() == numUVars()) {
        in_rmb[var2] = true;
        rmb.insert(var2);
        dependencies[var2].clear();
    }

}


inline const std::set<Variable>& DQBFPrefix::getDependencies(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(isExistential(var));

    if (in_rmb[var]) return univ_vars;
    else return dependencies[var];
}


inline const std::set<Variable>& QBFPrefix::getVarBlock(unsigned int level) noexcept
{
    val_assert(level < blocks.size());
    return blocks[level];
}


} // end namespace hqspre

#endif
