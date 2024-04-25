#include <ostream>
#include <algorithm>
#include <iterator>
#include <iostream>
#include "prefix.hpp"

/**
 * \file prefix.cpp
 * \brief Functions for manipulating the quantifier prefix of a (D)QBF
 * \author Ralf Wimmer
 * \date 06/2016
 */

namespace hqspre {

/**
 * \brief Returns the existential variables in increasing order.
 */
std::vector<Variable> Prefix::getExistVars() const noexcept
{
    std::vector<Variable> result;
    result.reserve(numEVars());
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isExistential(var)) result.push_back(var);
    }

    return result;
}


/**
 * \brief Returns the universal variables in increasing order.
 */
std::vector<Variable> Prefix::getUnivVars() const noexcept
{
    std::vector<Variable> result;
    result.reserve(numUVars());
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isUniversal(var)) result.push_back(var);
    }

    return result;
}


/**
 * \brief Replaces the dependencies of `var1` by the intersection of
 *        `var1` and `var2`'s dependencies.
 */
void DQBFPrefix::intersectDependencies(const Variable var1, const Variable var2)
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(isExistential(var1) && isExistential(var2));

    if (var1 == var2 || in_rmb[var2]) return;

    std::set<Variable> new_deps;
    std::set_intersection(dependencies[var1].cbegin(), dependencies[var1].cend(),
                          dependencies[var2].cbegin(), dependencies[var2].cend(),
                          std::inserter(new_deps, new_deps.end()));
    setDependencies(var1, std::move(new_deps));
}


/**
 * \brief Replaces the dependencies of `var1` by the intersection of
 *        `var1` and `var2`'s dependencies.
 */
void QBFPrefix::intersectDependencies(const Variable var1, const Variable var2)
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(isExistential(var1) && isExistential(var2));

    if (depth[var2] < depth[var1]) setLevel(var1, depth[var2]);
}


//--------------------------------------------------------



/**
 * \brief Replaces the dependencies of `var1` by the union of
 *        `var1` and `var2`'s dependencies.
 */
void DQBFPrefix::uniteDependencies(const Variable var1, const Variable var2)
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(isExistential(var1) && isExistential(var2));

    if (var1 == var2 || in_rmb[var1]) return;

    std::set<Variable> new_deps;
    std::set_union(dependencies[var1].cbegin(), dependencies[var1].cend(),
                   dependencies[var2].cbegin(), dependencies[var2].cend(),
                   std::inserter(new_deps, new_deps.end()));
    setDependencies(var1, std::move(new_deps));
}


/**
 * \brief Replaces the dependencies of `var1` by the union of
 *        `var1` and `var2`'s dependencies.
 */
void QBFPrefix::uniteDependencies(const Variable var1, const Variable var2)
{
    val_assert(minVarIndex() <= var1 && var1 <= maxVarIndex());
    val_assert(minVarIndex() <= var2 && var2 <= maxVarIndex());
    val_assert(isExistential(var1) && isExistential(var2));

    setLevel(var1, std::max(depth[var1], depth[var2]));
}


//--------------------------------------------------------



bool Prefix::checkConsistency() const
{
    // Correctness of num_u_vars and num_e_vars
    unsigned int e_vars = 0;
    unsigned int u_vars = 0;
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isUniversal(var)) ++u_vars;
        if (isExistential(var)) ++e_vars;
    }

    if (numEVars() != e_vars) {
        std::cerr << "[ERROR] num_e_vars is not correct (actual: " << numEVars() << ", correct: " << e_vars << std::endl;
        return false;
    }
    if (numUVars() != u_vars) {
        std::cerr << "[ERROR] num_u_vars is not correct (actual: " << numUVars() << ", correct: " << u_vars << std::endl;
        return false;
    }

    return true;
}


bool DQBFPrefix::checkConsistency() const
{
    if (!Prefix::checkConsistency()) return false;

    if (dependencies.size() != maxVarIndex() + 1 || in_rmb.size() != maxVarIndex() + 1) {
        std::cerr << "[ERROR] Data structures have wrong size.\n";
        return false;
    }

    if (univ_vars.size() != numUVars()) {
        std::cerr << "[ERROR] numUVars() = " << numUVars() << " != univ_vars.size() = " << univ_vars.size() << std::endl;
        return false;
    }
    for (Variable uvar: univ_vars) {
        if (!isUniversal(uvar)) {
            std::cout << "[ERROR] Variable " << uvar << " is not universal, but in univ_vars.\n";
            return false;
        }
    }

    for (Variable var = 1; var <= maxVarIndex(); ++var) {
        if (in_rmb[var] && rmb.find(var) == rmb.cend()) {
            std::cerr << "[ERROR] RMB-flag of " << var << " set, but variable is not in rmb.\n";
            return false;
        } else if (!in_rmb[var] && rmb.find(var) != rmb.cend()) {
            std::cerr << "[ERROR] RMB-flag of " << var << " not set, but variable is in rmb.\n";
            return false;
        }
    }

    // Consistency of dependency lists
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (varDeleted(var)) continue;
        if (in_rmb[var]) {
            if (!isExistential(var)) {
                std::cerr << "[ERROR] Universal variable " << var << " in DQBF-rmb.\n";
                return false;
            }
            if (!dependencies[var].empty()) {
                std::cerr << "[ERROR] Variable " << var << " is in RMB, but dependency data structure is not empty.\n";
                return false;
            }
            for (Variable univ: univ_vars) {
                if (dependencies[univ].find(var) == dependencies[univ].cend()) {
                    std::cerr << "[ERROR] RMB-Variable " << var << " does not appear in the dependency list of " << univ << std::endl;
                    return false;
                }
            }
            continue;
        }

        // only for non-rmb variables
        for (Variable dep: dependencies[var]) {
            if (varDeleted(dep)) {
                std::cerr << "[ERROR] Variable " << var << " depends on " << dep << ", but " << dep << " is deleted.\n";
                return false;
            }
            if (!in_rmb[dep] && dependencies[dep].find(var) == dependencies[dep].cend()) {
                std::cerr << "[ERROR] Variable " << var << " depends on " << dep << ", but not vice versa.\n";
                return false;
            }
        }
    }

    return true;
}


bool QBFPrefix::checkConsistency() const
{
    if (!Prefix::checkConsistency()) return false;

    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (varDeleted(var)) continue;
        if (depth[var] >= blocks.size()) {
            std::cerr << "[ERROR] Variable " << var << " in a block (" << depth[var] << ") which does not exist!\n";
            return false;
        }

        if (blocks[depth[var]].find(var) == blocks[depth[var]].cend()) {
            std::cerr << "[ERROR] Variable " << var << " is not in the block in which it should be!\n";
            return false;
        }
    }

    for (const auto& block: blocks) {
        if (block.empty()) continue;
        const bool block_exist = isExistential(*(block.cbegin()));
        for (Variable var: block) {
            if (varDeleted(var)) {
                std::cerr << "[ERROR] Variable " << var << " is deleted but still contained in a quantifier block!\n";
                return false;
            }

            if (isExistential(var) != block_exist) {
                std::cerr << "[ERROR] Variable " << var << " is in a block with opposite quantifier!\n";
                return false;
            }
        }
    }

    return true;
}

//-----------------------------------------------------


/**
 * \brief Writes the DQBF prefix to an output stream.
 * \param stream the stream to write to
 * \param translation_table Used to rename the variables in case deleted variables should be omitted
 */
void DQBFPrefix::write(std::ostream& stream, std::vector<Variable>* translation_table) const
{
    auto trans = [translation_table](Variable var) -> Variable
        {
            return (translation_table == nullptr ? var : (*translation_table)[var]);
        };

    // print universal variables
    stream << "a ";
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isUniversal(var)) {
            stream << trans(var) << " ";
        }
    }
    stream << "0" << std::endl;

    // print existential variables which do not depend on all universals
    for (Variable var = 1; var <= maxVarIndex(); ++var) {
        if (!isExistential(var)) continue;
        if (in_rmb[var]) continue;

        stream << "d " << trans(var) << " ";
        for (const Variable dep: dependencies[var]) {
            stream << trans(dep) << " " ;
        }
        stream << "0" << std::endl;
    }

    // print existential variable which depend on all universals.
    if (!rmb.empty()) {
        stream << "e ";
        for (const Variable var: rmb) {
            stream << trans(var) << " ";
        }
        stream << "0" << std::endl;
    }
}

/**
 * \brief Writes the QBF prefix to an output stream.
 * \param stream the stream to write to
 * \param translation_table Used to rename the variables in case deleted variables should be omitted
 */
void QBFPrefix::write(std::ostream& stream, std::vector<Variable>* translation_table) const
{
    auto trans = [translation_table](Variable var) -> Variable
        {
            return (translation_table == nullptr ? var : (*translation_table)[var]);
        };

    for (const auto& block: blocks) {
        if (block.empty()) continue;
        if (isExistential(*(block.begin()))) stream << "e ";
        else stream << "a ";
        for (Variable var: block) stream << trans(var) << " ";
        stream << "0\n";
    }
}


//---------------------------------------------------------


void Prefix::updateVars()
{
}


/**
 * \brief Update the variable data structures.
 *
 * Empty blocks are removed, adjacent blocks with the same
 * quantifier are merged. This changes the depth of the variables.
 */
void QBFPrefix::updateVars()
{
    Prefix::updateVars();

    if (!blocks.empty()) {
        unsigned int pos_done = 0;
        unsigned int pos_curr = 1;
        while (pos_curr < blocks.size()) {
            if (blocks[pos_curr].empty()) {
                ++pos_curr; continue;
            } else if (blocks[pos_done].empty()) {
                blocks[pos_done] = std::move(blocks[pos_curr]);
                blocks[pos_curr].clear();
                ++pos_curr;
            } else if (getLevelQuantifier(pos_done) != getLevelQuantifier(pos_curr)) {
                ++pos_done;
            } else if (getLevelQuantifier(pos_done) == getLevelQuantifier(pos_curr) && pos_curr != pos_done) {
                // Merge the two blocks
                blocks[pos_done].insert(blocks[pos_curr].cbegin(), blocks[pos_curr].cend());
                blocks[pos_curr].clear();
                ++pos_curr;
            } else {
                ++pos_curr;
            }
        }
        if (blocks.size() > pos_done + 1) {
            blocks.resize(pos_done + 1);
            for (unsigned int k = 0; k < blocks.size(); ++k) {
                for (Variable var: blocks[k]) {
                    depth[var] = k;
                }
            }
            val_assert((!blocks.back().empty()) || (numVars() == 0));
        }
    }
}


//---------------------------------------------------------

/**
 * \brief Returns the cumulated number of dependencies of all existential variables.
 */
unsigned int DQBFPrefix::numDependencies() const noexcept
{
    unsigned int num = rmb.size() * numUVars();
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isExistential(var)) num += numDependencies(var);
    }

    return num;
}


/**
 * \brief Returns the cumulated number of dependencies of all existential variables.
 */
unsigned int QBFPrefix::numDependencies() const noexcept
{
    unsigned int result = 0;
    unsigned int univs = 0;
    for (const auto& block: blocks) {
        if (block.empty()) continue;
        if (isExistential(*(block.begin()))) result += univs * block.size();
        else univs += block.size();
    }

    return result;
}

//---------------------------------------------------------

/**
 * \brief Returns the number of dependencies of a given existential variable.
 */
unsigned int DQBFPrefix::numDependencies(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(isExistential(var));

    if (in_rmb[var]) return univ_vars.size();
    else return dependencies[var].size();
}


/**
 * \brief Returns the number of dependencies of a given existential variable.
 */
unsigned int QBFPrefix::numDependencies(Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    if (varDeleted(var)) return 0;

    const unsigned int block_nr = getLevel(var);
    unsigned int result = 0;

    for (unsigned int b = 0; b < block_nr; ++b) {
        if (blocks[b].empty()) continue;
        if (isUniversal(*(blocks[b].begin()))) {
            result += blocks[b].size();
        }
    }

    return result;
}


//---------------------------------------------------------

/**
 * \brief Removes all dependencies of a variable.
 */
void DQBFPrefix::clearDependencies(Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    if (in_rmb[var]) {
        in_rmb[var] = false;
        rmb.erase(var);
        for (Variable univ: univ_vars) {
            dependencies[univ].erase(var);
        }
    } else {
        for (Variable dep: dependencies[var]) {
            dependencies[dep].erase(var);
        }
        dependencies[var].clear();
    }
}


/**
 * Checks if a DQBF is actually a QBF.
 */
bool DQBFPrefix::isQBF() const
{
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (!isExistential(var)) continue;
        if (in_rmb[var]) continue; // variable depends on all universals

        for (Variable other_var = var + 1; other_var <= maxVarIndex(); ++other_var) {
            if (!isExistential(other_var)) continue;
            if (in_rmb[other_var]) continue; // variable depends on all universals

            // remove from the first dep-set each element from the second dep-set
            // remove from the second dep-set each element from the first dep-set
            const auto result = two_sided_difference_empty(dependencies[var].cbegin(),
                                                           dependencies[var].cend(),
                                                           dependencies[other_var].cbegin(),
                                                           dependencies[other_var].cend());
            // if both differences are non-empty, we have a proper DQBF
            if (!result.first && !result.second) return false;
        }
    }
    return true;
}



/**
 * \brief Converts the DQBF prefix into an equivalent QBF prefix (if possible).
 *
 * The QBF prefix is allocated on the heap. The caller is
 * responsible for deleting the object.

 * \pre The DQBF prefix must have an equivalent QBF prefix.
 * \sa DQBFPrefix::isQBF()
 */
QBFPrefix* DQBFPrefix::convertToQBF() const
{
    if (!isQBF()) return nullptr;

    QBFPrefix* result = new QBFPrefix();
    result->setMaxVarIndex(maxVarIndex());

    // Get all existential variables
    std::vector<Variable> exist_vars;
    exist_vars.reserve(numEVars());
    for (Variable var = minVarIndex(); var <= maxVarIndex(); ++var) {
        if (isExistential(var) && !in_rmb[var]) exist_vars.push_back(var);
    }

    // Sort existential variables according to their number of dependencies.
    // This brings them into the right order for the QBF prefix.
    std::sort(exist_vars.begin(), exist_vars.end(),
        [this](Variable a, Variable b)
            {
                return dependencies[a].size() < dependencies[b].size();
            }
    );

    // Insert the universal variables into the order.
    std::vector<bool> finished_universal(maxVarIndex() + 1, false);
    for (const auto exist: exist_vars) {
        for (const auto dep: dependencies[exist]) {
            if (!finished_universal[dep]) {
                finished_universal[dep] = true;
                result->addUVar(dep);
            }
        }
        result->addEVar(exist);
    }

    // Append the remaining universal variables which do not appear in
    // any dependency sets.
    for (Variable univ = minVarIndex(); univ <= maxVarIndex(); ++univ) {
        if (isUniversal(univ) && !finished_universal[univ]) {
                finished_universal[univ] = true;
                result->addUVar(univ);
        }
    }

    // Append the rmb-variables
    for (Variable var: rmb) result->addEVar(var);

    return result;
}


void QBFPrefix::setLevel(Variable var, unsigned int level)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(level <= blocks.size());
    val_assert(!varDeleted(var));

    if (level == depth[var]) return;

    val_assert(level == blocks.size() || blocks[level].empty() || isExistential(var) == isExistential(*(blocks[level].begin())));
    val_assert(level < blocks.size() || blocks.back().empty() || isExistential(*(blocks.back().begin())) != isExistential(var));

    blocks[depth[var]].erase(var);
    depth[var] = level;
    if (level >= blocks.size()) blocks.resize(level + 1);
    blocks[level].insert(var);
}


/**
 * \brief Turns a QBF prefix into an equivalent DQBF prefix.
 *
 * The DQBF prefix is allocated on the heap. The caller is
 * responsible for deleting the object.
 */
DQBFPrefix* QBFPrefix::convertToDQBF() const
{
    DQBFPrefix* result = new DQBFPrefix();
    result->setMaxVarIndex(this->maxVarIndex());
    std::set<Variable> deps;
    for (const auto& block: blocks) {
        for (Variable var: block) {
            if (varDeleted(var)) continue;
            if (isUniversal(var)) {
                result->addUVar(var);
                deps.insert(var);
            } else {
                result->addEVar(var);
                result->setDependencies(var, deps);
            }
        }
    }
    return result;
}


template <typename Container>
void DQBFPrefix::setDependencies(Variable var, const Container& deps)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(isExistential(var));
    val_assert(dependencies.size() > var);

    if (deps.size() == numUVars()) {
        moveToRMB(var);
        return;
    }

    // remove old dependencies
    if (!dependencies[var].empty()) {
        for (Variable dep: dependencies[var]) dependencies[dep].erase(var);
        dependencies[var].clear();
    }

    // add new dependencies
    auto pos = dependencies[var].begin();
    for (Variable dep: deps) {
        dependencies[dep].insert(var);
        pos = dependencies[var].insert(pos, dep);
    }

    in_rmb[var] = false;
}


void DQBFPrefix::setDependencies(Variable var, std::set<Variable>&& deps)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(isExistential(var));

    if (deps.size() == numUVars()) {
        moveToRMB(var);
        return;
    }

    // remove old dependencies
    if (!dependencies[var].empty()) {
        for (Variable dep: dependencies[var]) dependencies[dep].erase(var);
        dependencies[var].clear();
    }

    // add new dependencies
    for (Variable dep: deps) {
        dependencies[dep].insert(var);
    }
    dependencies[var] = std::move(deps);

    in_rmb[var] = false;
}


/**
 * \brief Returns the set of variables in the right-most quantifier block.
 */
const std::set<Variable>& QBFPrefix::getRMB() const noexcept
{
    int max_num = blocks.size() - 1;
    while (max_num >= 0 && blocks[max_num].empty()) --max_num;
    if (max_num < 0 || getLevelQuantifier(max_num) != VariableStatus::EXISTENTIAL) {
        const_cast<QBFPrefix*>(this)->blocks.resize(max_num + 2);
    } else {
        const_cast<QBFPrefix*>(this)->blocks.resize(max_num + 1);
    }

    return blocks.back();
}


/**
 * \brief Returns the set of existential variables in the right-most block.
 *
 * The right-most block consists of all those existential variables which
 * depend on <i>all</i> universal variables. These often play a special role
 * because they can be eliminated by resolution, all gate outputs after
 * Tseitin transformation can be moved to this set etc.
 */
const std::set<Variable>& DQBFPrefix::getRMB() const noexcept
{
    return rmb;
}


//-----------------------------------------------

/**
 * \brief Moves the given variable to the right-most block.
 *
 * Afterwards, the variable depends on all universal variables.
 * \pre The variable must be existential.
 */
void QBFPrefix::moveToRMB(Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(!varDeleted(var));
    val_assert(isExistential(var));

    if (getLevel(var) == blocks.size() - 1) return;
    blocks[depth[var]].erase(var);

    int max_num = blocks.size() - 1;
    while (max_num >= 0 && blocks[max_num].empty()) --max_num;
    if (max_num < 0 || getLevelQuantifier(max_num) != VariableStatus::EXISTENTIAL) {
        blocks.resize(max_num + 2);
    } else {
        blocks.resize(max_num + 1);
    }

    blocks.back().insert(var);
    depth[var] = blocks.size() - 1;
}


/**
 * \brief Moves the given variable to the right-most block.
 *
 * Afterwards, the variable depends on all universal variables.
 * \pre The variable must be existential.
 */
void DQBFPrefix::moveToRMB(Variable var)
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(!varDeleted(var));
    val_assert(isExistential(var));

    if (dependencies[var].size() == numUVars()) return;

    in_rmb[var] = true;
    dependencies[var].clear();
    rmb.insert(var);
    for (Variable univ: univ_vars) dependencies[univ].insert(var);
}


VariableStatus QBFPrefix::getLevelQuantifier(unsigned int level) const noexcept
{
    val_assert(level < blocks.size());
    if (blocks[level].empty()) return VariableStatus::DELETED;
    else if (isExistential(*(blocks[level].begin()))) return VariableStatus::EXISTENTIAL;
    else return VariableStatus::UNIVERSAL;
}

} // end namespace hqspre
