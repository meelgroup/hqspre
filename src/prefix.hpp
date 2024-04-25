#ifndef HQSPRE_PREFIX_HPP_
#define HQSPRE_PREFIX_HPP_

#include <vector>
#include <set>
#include <algorithm>
#include <iosfwd>
#include "aux.hpp"
#include "literal.hpp"

/**
 * \file prefix.hpp
 * \brief Classes for representing a formula's prefix
 * \author Ralf Wimmer
 * \date 06/2016
 */

namespace hqspre {

/**
 * \brief Status of a variable (quantifier/deleted)
 */
enum class VariableStatus: short
{
    EXISTENTIAL, ///< Variable is existential
    UNIVERSAL,   ///< Variable is universal
    DELETED      ///< Variable has been deleted
};


/**
 * \brief Type of the prefix (QBF/DQBF).
 */
enum class PrefixType: short
{
    QBF,        ///< Formula is a standard QBF
    DQBF        ///< Formula is a DQBF
};

/**
 * \brief Representation of a quantifed formula's prefix.
 */
class Prefix
{
public:
    Prefix(): var_status(1, VariableStatus::DELETED) { }
    virtual ~Prefix() = default;

    /**
     * \brief Returns the type of the prefix (QBF vs. DQBF).
     */
    virtual PrefixType type() const noexcept = 0;

    virtual void clear();

    //@{
    /**
     * \name Creating and deleting variables.
     */
    virtual void setMaxVarIndex(Variable index);
    virtual void addEVar(Variable index);
    virtual void addUVar(Variable index);
    virtual void removeVar(Variable index);
    std::vector<Variable> getExistVars() const noexcept;
    std::vector<Variable> getUnivVars() const noexcept;
    virtual void makeCopy(Variable new_var, Variable original);
    virtual void updateVars();
    //@}

    //@{
    /**
     * \name Querying the variable status
     */
    bool isUniversal(Variable var)    const noexcept;
    bool isExistential(Variable var)  const noexcept;
    bool varDeleted(Variable var)     const noexcept;
    //@}

    //@{
    /**
     * \name Number of variables and minimal/maximal indices
     */

    /// Returns the minimal possible index of a variable.
    constexpr static Variable minVarIndex() noexcept { return 1; }

    /// Returns the maximal possible index of a variable.
    Variable maxVarIndex()            const noexcept { return var_status.size() - 1; }

    /// Returns the minimal possible index of a literal.
    constexpr static Literal minLitIndex()  noexcept { return 2; }

    /// Returns the maximal possible index of a literal.
    Literal maxLitIndex()             const noexcept { return 2 * var_status.size() - 1; }

    /// Returns the number of (non-deleted) variables.
    unsigned int numVars()            const noexcept { return num_e_vars + num_u_vars; }

    /// Returns the number of existential variables.
    unsigned int numEVars()           const noexcept { return num_e_vars; }

    /// Returns the number of universal variables.
    unsigned int numUVars()           const noexcept { return num_u_vars; }
    //@}

    //@{
    /**
     * \name Access to dependencies
     */
    /// Returns the number of dependencies of variable `var`
    virtual unsigned int numDependencies(Variable var) const noexcept = 0;

    // Returns the accumulated number of dependencies of all existential variables
    virtual unsigned int numDependencies() const noexcept = 0;

    /// Returns if `var1` depends on `var2`
    virtual bool depends(Variable var1, Variable var2) const = 0;

    /// Returns if `var1`'s dependencies are a subset of `var2`'s dependencies
    virtual bool dependenciesSubset(Variable var1, Variable var2) const = 0;

    /// Returns true if `var` depends on all universal variables
    virtual bool dependsOnAll(Variable var) const = 0;

    /// Replaces `var1`'s dependencies by the intersection of `var1` and `var2`'s dependencies
    virtual void intersectDependencies(Variable var1, Variable var2) = 0;

    /// Replaces `var1`'s dependencies by the union of `var1` and `var2`'s dependencies
    virtual void uniteDependencies(Variable var1, Variable var2) = 0;

    /// Moves an existential variable to the right-most block (i.e., makes it depend on all universals)
    virtual void moveToRMB(Variable index) = 0;

    /// Checks if a variable is contained in the right-most block
    virtual bool inRMB(Variable var) const noexcept = 0;

    /// Returns the variables in the right-most block
    virtual const std::set<Variable>& getRMB() const noexcept = 0;

    //@}

    //@{
    /**
     * \name Input/output
     */

    /// Writes the prefix to an output stream.
    virtual void write(std::ostream& stream, std::vector<Variable>* translation_table = nullptr) const = 0;
    //@}

    //@{
    /**
     * \name Miscellaneous
     */
    virtual bool checkConsistency() const;
    //@}

private:
    std::vector<VariableStatus> var_status; ///< Status of all variables (existential/universal/deleted)
    unsigned int num_u_vars = 0;  ///< Number of universal variables
    unsigned int num_e_vars = 0;  ///< Number of existential variables
};


class DQBFPrefix;

/**
 * \brief Representation of a QBF's prefix.
 */
class QBFPrefix: public Prefix
{
public:
    QBFPrefix(): Prefix(), depth(1, 0), blocks(1, std::set<Variable>()) { }
    virtual ~QBFPrefix() = default;
    virtual PrefixType type() const noexcept override;
    virtual void clear() override;
    virtual bool checkConsistency() const override;

    //@{
    /**
     * \name Creating and deleting variables
     */
    virtual void addEVar(Variable index) override;
    virtual void addUVar(Variable index) override;
    virtual void makeCopy(Variable new_var, Variable original) override;
    virtual void setMaxVarIndex(Variable index) override;
    virtual void removeVar(Variable var) override;
    virtual void updateVars() override;
    //@}

    //@{
    /**
     * \name Access to dependencies
     */
    virtual bool depends(Variable var1, Variable var2) const;
    virtual bool dependenciesSubset(Variable var1, Variable var2) const override;
    virtual bool dependsOnAll(Variable var) const override;
    virtual void write(std::ostream& stream, std::vector<Variable>* output_stream = nullptr) const override;
    virtual void intersectDependencies(Variable var1, Variable var2) override;
    virtual void uniteDependencies(Variable var1, Variable var2) override;
    virtual unsigned int numDependencies(Variable var) const noexcept override;
    virtual unsigned int numDependencies() const noexcept override;
    virtual void moveToRMB(Variable var) override;
    virtual const std::set<Variable>& getRMB() const noexcept;
    virtual bool inRMB(Variable var) const noexcept { return depth[var] == (blocks.size() - 1); }

    //@}

    //@{
    /**
     * \name QBF-specific functions
     */
    DQBFPrefix* convertToDQBF() const;
    unsigned int getLevel(Variable var) const noexcept;
    unsigned int getMaxLevel() const noexcept { return blocks.size() - 1; }
    VariableStatus getLevelQuantifier(unsigned int level) const noexcept;
    void setLevel(Variable var, unsigned int level);
    const std::set<Variable>& getVarBlock(unsigned int level) noexcept;
    //@}

private:
    std::vector<unsigned int> depth; ///< Assigns each variable its quantifier level (starting from 0)
    std::vector<std::set<Variable>> blocks; ///< Contains the variables in each quantifier block
};



/**
 * \brief Representation of a DQBF's prefix.
 */
class DQBFPrefix: public Prefix
{
public:
    DQBFPrefix(): rmb(), dependencies(1), in_rmb(1,false), univ_vars() {}
    virtual ~DQBFPrefix() = default;
    virtual PrefixType type() const noexcept override;
    virtual void clear() override;

    //@{
    /**
     * \name Variable handling
     */
    virtual void addUVar(Variable var) override;
    virtual void removeVar(Variable var) override;
    virtual void makeCopy(Variable new_var, Variable original) override;
    virtual void setMaxVarIndex(Variable index) override;
    //@}

    //@{
    /**
     * \name Dependency handling
     */
    virtual bool depends(Variable var1, Variable var2) const override;
    virtual bool dependenciesSubset(Variable var1, Variable var2) const override;
    virtual bool dependsOnAll(Variable var) const override;
    virtual void intersectDependencies(Variable var1, Variable var2) override;
    virtual void uniteDependencies(Variable var1, Variable var2) override;
    virtual unsigned int numDependencies() const noexcept override;
    virtual unsigned int numDependencies(Variable var) const noexcept override;
    virtual const std::set<Variable>& getRMB() const noexcept;
    virtual bool inRMB(Variable var) const noexcept { return in_rmb[var]; }
    virtual void moveToRMB(Variable var) override;

    template <typename Container> void setDependencies(Variable var, const Container& deps);
    void setDependencies(Variable var, std::set<Variable>&& deps);
    void removeDependency(Variable var1, Variable var2);
    void addDependency(Variable var1, Variable var2);
    const std::set<Variable>& getDependencies(Variable var) const noexcept;
    void clearDependencies(Variable var);
    //@}

    virtual bool checkConsistency() const override;
    virtual void write(std::ostream& stream, std::vector<Variable>* translation_table = nullptr) const override;

    bool isQBF() const;
    QBFPrefix* convertToQBF() const;

private:

    /**
     * \brief The variables in the right-most block
     *
     * The variables which depend on all universal variables (like
     * the Tseitin variables) are stored separately in order to save
     * memory. `rmb` (for ``right-most block'') is the set of all these
     * variables. Their entry in `dependencies` is empty; however
     * they appear in the dependency lists of all universal variables.
     * \sa DQBFPrefix::in_rmb
     * \sa DQBFPrefix::dependencies
     */
    std::set<Variable> rmb;

    /**
     * \brief The dependency sets of all variables except those in the right-most block
     *
     * Apart from the variables in the right-most block, each variable has an entry
     * in dependencies. For an existential variable `evar`, `dependencies[evar]`
     * contains all universal variables on which `evar` depends. For a universal
     * variable `uvar`, `dependencies[uvar]` contains all existential variables which
     * depend on `uvar'.
     * \sa DQBFPrefix::rmb
     * \sa DQBFPrefix::in_rmb
     */
    std::vector<std::set<Variable>> dependencies;

    /**
     * \brief For a variable \f$v\f$, in_rmb[\f$v\f$] is true iff \f$v\f$ depends on all universal variables.
     *
     * Only existential variables can be in the right-most block.
     * \sa DQBFPrefix::rmb
     * \sa DQBFPrefix::dependencies
     */
    std::vector<bool> in_rmb;

    /**
     * \brief The set of all universal variables.
     */
    std::set<Variable> univ_vars;
};

} // end namespace hqspre

#include "prefix.ipp"

#endif
