#ifndef HQSPRE_FORMULA_IPP_
#define HQSPRE_FORMULA_IPP_

/*
 * \file formula.ipp
 * \brief Inline functions for variable, clause, and dependency management
 * \author Ralf Wimmer
 * \date 12/2015-03/2016
 */

namespace hqspre {

/**
 * \brief Constructs an empty formula without variables and clauses.
 */
inline Formula::Formula():
    prefix(nullptr),
    dqbf_prefix(nullptr),
    qbf_prefix(nullptr),
    clauses(),
    clause_modified(),
    clause_gate(),
    gate_output(),
    gate_input(),
    occ_list(),
    implications(),
    deleted_clause_numbers(),
    deleted_var_numbers(),
    unit_stack(),
    assignment(),
    dont_touch(),
    variable_score(),
    clause_sizes(),
    candidates(variable_score),
    blocked_candidates(clause_sizes),
    removed_lits(),
    _seen(),
    setting(),
    process_limit()
{
    qbf_prefix = new QBFPrefix();
    prefix = qbf_prefix;
}


/**
 * \brief Moves a formula into another new formula object.
 */
inline Formula::Formula(Formula&& other):
    prefix(other.prefix),
    dqbf_prefix(other.dqbf_prefix),
    qbf_prefix(other.qbf_prefix),
    clauses(std::move(other.clauses)),
    clause_modified(std::move(other.clause_modified)),
    clause_gate(std::move(other.clause_gate)),
    gate_output(std::move(other.gate_output)),
    gate_input(std::move(other.gate_input)),
    occ_list(std::move(other.occ_list)),
    implications(std::move(other.implications)),
    deleted_clause_numbers(std::move(other.deleted_clause_numbers)),
    deleted_var_numbers(std::move(other.deleted_var_numbers)),
    unit_stack(std::move(other.unit_stack)),
    assignment(std::move(other.assignment)),
    dont_touch(std::move(other.dont_touch)),
    variable_score(std::move(other.variable_score)),
    clause_sizes(std::move(other.clause_sizes)),
    candidates(std::move(other.candidates)),
    blocked_candidates(std::move(other.blocked_candidates)),
    removed_lits(std::move(other.removed_lits)),
    _seen(std::move(other._seen)),
    setting(std::move(other.setting)),
    process_limit(std::move(other.process_limit)),
    interrupt(other.interrupt),
    stat_unit_pure(other.stat_unit_pure),
    stat_univ_reduction(other.stat_univ_reduction),
    stat_univ_expansion(other.stat_univ_expansion),
    stat_bce(other.stat_bce),
    stat_hte(other.stat_hte),
    stat_hse(other.stat_hse),
    stat_ble(other.stat_ble),
    stat_bla(other.stat_bla),
    stat_impl_chains(other.stat_impl_chains),
    stat_contradictions(other.stat_contradictions),
    stat_subsumption(other.stat_subsumption),
    stat_resolution(other.stat_resolution),
    stat_selfsubsuming_resolution(other.stat_selfsubsuming_resolution),
    stat_equiv(other.stat_equiv),
    stat_equiv_gates(other.stat_equiv_gates),
    stat_hidden_equiv(other.stat_hidden_equiv),
    stat_hidden_unit(other.stat_hidden_unit),
    stat_substitution(other.stat_substitution),
    stat_unit_by_sat(other.stat_unit_by_sat),
    stat_impl_by_sat(other.stat_impl_by_sat),
    stat_sat_calls(other.stat_sat_calls),
    stat_prepro_loops(other.stat_prepro_loops),
    stat_dep_schemes(other.stat_dep_schemes)
{
    other.prefix = nullptr;
    other.dqbf_prefix = nullptr;
    other.qbf_prefix = nullptr;
}


/**
 * \brief Creates a copy of a formula.
 */
inline Formula::Formula(const Formula& other):
    prefix(nullptr),
    dqbf_prefix(nullptr),
    qbf_prefix(nullptr),
    clauses(other.clauses),
    clause_modified(other.clause_modified),
    clause_gate(other.clause_gate),
    gate_output(other.gate_output),
    gate_input(other.gate_input),
    occ_list(other.occ_list),
    implications(other.implications),
    deleted_clause_numbers(other.deleted_clause_numbers),
    deleted_var_numbers(other.deleted_var_numbers),
    unit_stack(other.unit_stack),
    assignment(other.assignment),
    dont_touch(other.dont_touch),
    variable_score(other.variable_score),
    clause_sizes(other.clause_sizes),
    candidates(other.candidates),
    blocked_candidates(other.blocked_candidates),
    removed_lits(other.removed_lits),
    _seen(other._seen),
    setting(other.setting),
    process_limit(other.process_limit),
    interrupt(other.interrupt),
    stat_unit_pure(other.stat_unit_pure),
    stat_univ_reduction(other.stat_univ_reduction),
    stat_univ_expansion(other.stat_univ_expansion),
    stat_bce(other.stat_bce),
    stat_hte(other.stat_hte),
    stat_hse(other.stat_hse),
    stat_ble(other.stat_ble),
    stat_bla(other.stat_bla),
    stat_impl_chains(other.stat_impl_chains),
    stat_contradictions(other.stat_contradictions),
    stat_subsumption(other.stat_subsumption),
    stat_resolution(other.stat_resolution),
    stat_selfsubsuming_resolution(other.stat_selfsubsuming_resolution),
    stat_equiv(other.stat_equiv),
    stat_equiv_gates(other.stat_equiv_gates),
    stat_hidden_equiv(other.stat_hidden_equiv),
    stat_hidden_unit(other.stat_hidden_unit),
    stat_substitution(other.stat_substitution),
    stat_unit_by_sat(other.stat_unit_by_sat),
    stat_impl_by_sat(other.stat_impl_by_sat),
    stat_sat_calls(other.stat_sat_calls),
    stat_prepro_loops(other.stat_prepro_loops),
    stat_dep_schemes(other.stat_dep_schemes)
{
    if (other.dqbf_prefix != nullptr) {
        dqbf_prefix = new DQBFPrefix(*(other.dqbf_prefix));
        prefix = dqbf_prefix;
    } else if (other.qbf_prefix != nullptr) {
        qbf_prefix = new QBFPrefix(*(other.qbf_prefix));
        prefix = qbf_prefix;
    }
}


/**
 * \brief Destroys the formula and frees the prefix
 */
inline Formula::~Formula()
{
    val_assert(prefix != nullptr);
    delete prefix;
}


/**
 * \brief Returns the number of active variables.
 *
 * A variable is active if it is contained in at least one clause.
 * \sa Formula::numUVars()
 * \sa Formula::numEVars()
 */
inline unsigned int Formula::numVars() const noexcept
{
    val_assert(prefix != nullptr);
    return prefix->numVars();
}


/**
 * \brief Returns the number of active universal variables.
 *
 * A variable is active if it has not been deleted.
 * \sa Formula::numVars()
 * \sa Formula::numEVars()
 */
inline unsigned int Formula::numUVars() const noexcept
{
    val_assert(prefix != nullptr);
    return prefix->numUVars();
}


/**
 * \brief Returns the number of active existential variables.
 *
 * A variable is active if it has not been deleted.
 * \sa Formula::numVars()
 * \sa Formula::numUVars()
 */
inline unsigned int Formula::numEVars() const noexcept
{
    val_assert(prefix != nullptr);
    return prefix->numEVars();
}


/**
 * \brief Returns the number of literals in the formula.
 *
 * \note The running time is linear in the size of the formula.
 */
inline unsigned int Formula::numLiterals() const noexcept
{
    unsigned int result = 0;
    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (!clauseDeleted(c_nr) && !clauseOptional(c_nr)) {
            result += clauses[c_nr].size();
        }
    }
    return result;
}


/**
 * \brief Returns if a given variable is universal.
 *
 * A variable has one of three states: universal, existential, or deleted.
 * That means deleted variables are neither universal nor existential.
 * \return true iff the variable is universal.
 */
inline bool Formula::isUniversal(Variable var) const noexcept
{
    val_assert(prefix != nullptr);

    return prefix->isUniversal(var);
}


/**
 * \brief Returns if a given variable is existential.
 *
 * A variable has one of three states: universal, existential, or deleted.
 * That means deleted variables are neither universal nor existential.
 * \return true iff the variable is existential.
 */
inline bool Formula::isExistential(Variable var) const noexcept
{
    val_assert(prefix != nullptr);

    return prefix->isExistential(var);
}


/**
 * \brief Returns the maximal valid ID of a variable.
 *
 * Variable IDs always start at 1. Some of the IDs may be
 * inactive because the variables does not appear in the formula
 * anymore. Note that this function does not return the number
 * of active variables.
 * \sa Formula::numVars()
 * \sa Formula::maxLitIndex()
 */
inline Variable Formula::maxVarIndex() const noexcept
{
    val_assert(prefix != nullptr);

    return prefix->maxVarIndex();
}


/**
 * \brief Returns the minimal valid ID of a variable.
 *
 * Variable IDs always start at 1. Some of the IDs may be
 * inactive because the variables does not appear in the formula
 * anymore. Note that this function does not return the number
 * of active variables.
 * \sa Formula::numVars()
 * \sa Formula::maxVarIndex()
 * \sa Formula::maxLitIndex()
 * \sa Formula::minLitIndex()
 */
inline constexpr Variable Formula::minVarIndex() noexcept
{
    return Prefix::minVarIndex();
}


/**
 * \brief Returns the minimal valid ID of a literal.
 *
 * Literal IDs always start at 2. Some of the IDs may be
 * inactive because the corresponding variables has been deleted.
 * Note that this function does not return the number
 * of active literals.
 * \sa Formula::numVars()
 * \sa Formula::maxVarIndex()
 * \sa Formula::minVarIndex()
 * \sa Formula::maxLitIndex()
 */
inline constexpr Literal Formula::minLitIndex() noexcept
{
    return Prefix::minLitIndex();
}


/**
 * \brief Returns the maximal valid ID of a literal.
 *
 * Literal IDs always start at 2. Some of the IDs may be
 * inactive because the corresponding variables has been deleted.
 * Note that this function does not return the number
 * of active literals.
 * \sa Formula::numVars()
 * \sa Formula::maxVarIndex()
 */
inline Literal Formula::maxLitIndex() const noexcept
{
    val_assert(prefix != nullptr);
    return prefix->maxLitIndex();
}


/**
 * \brief Returns if a variable has been deleted.
 *
 * Variables are considered to be deleted if they do not
 * appear in the formula anymore.
 */
inline bool Formula::varDeleted(const Variable var) const noexcept
{
    val_assert(prefix != nullptr);

    return prefix->varDeleted(var);
}

/**
 * \brief Set the "don't touch" status of a variable to the given status
 *
 * Variables can be "don't touch" in context of incremental solving
 */
inline void Formula::setDontTouch(const Variable var, bool status) noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    dont_touch[var] = status;
}


/**
 * \brief Returns if a variable is "don't touch".
 *
 * Variables can be "don't touch" in context of incremental solving
 */
inline bool Formula::isDontTouch(const Variable var) const noexcept
{
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    return dont_touch[var];
}


/**
 * \brief Removes a variable.
 *
 * \pre The variable may not occur in any clause anymore.
 */
inline void Formula::removeVar(const Variable var)
{
    val_assert(prefix != nullptr);
    val_assert(minVarIndex() <= var && var <= maxVarIndex());
    val_assert(!varDeleted(var));
    val_assert(occ_list[var2lit(var, false)].empty());
    val_assert(occ_list[var2lit(var, true)].empty());
    val_assert(implications[var2lit(var, false)].empty());
    val_assert(implications[var2lit(var, true)].empty());

    prefix->removeVar(var);
    deleted_var_numbers.push_back(var);
    assignment[var] = TruthValue::UNKNOWN;
    gate_output[var] = false;
    gate_input[var] = false;
}


/**
 * \brief Removes a clause from the occurrence list of a literal
 */
inline void Formula::removeFromOccList(Literal lit, unsigned int c_nr)
{
    auto position = std::find(occ_list[lit].begin(), occ_list[lit].end(), c_nr);
    if (position != occ_list[lit].end()) {
        *position = occ_list[lit].back();
        occ_list[lit].pop_back();
    }
}


/**
 * \brief Creates a new existential variable and returns its ID.
 */
inline Variable Formula::addEVar()
{
    val_assert(prefix != nullptr);

    const Variable var = nextVar();
    prefix->addEVar(var);
    return var;
}


/**
 * \brief Creates a new existential variable and returns its ID.
 *
 * This function is only available for DQBF prefixes.
 * If the current prefix is a QBF prefix, it is automatically
 * converted to a DQBF prefix!
 * \param deps container with the dependency set of the created variable
 * \pre All variables in the dependency set must be universal (and be created before).
 */
template<typename Container>
inline Literal Formula::addEVar(const Container& deps)
{
    val_assert(prefix != nullptr);

    if (prefix->type() == PrefixType::QBF) {
        if (setting.verbosity > 1) {
            std::cout << "c Switching to DQBF prefix representation\n";
        }
        dqbf_prefix = qbf_prefix->convertToDQBF();
        delete prefix;
        prefix = dqbf_prefix;
        qbf_prefix = nullptr;
    }

    const Variable result = addEVar();
    dqbf_prefix->setDependencies(result, deps);
    return result;
}


/**
 * \brief Creates a new universal variable and returns its ID.
 */
inline Variable Formula::addUVar()
{
    val_assert(prefix != nullptr);

    const Variable var = nextVar();
    prefix->addUVar(var);
    return var;
}


/**
 * \brief Returns the next available variable index.
 *
 * The returned variable index is marked as 'not available'.
 * \note This is the only function which may remove elements from
 *       `deleted_var_numbers`.
 * \sa Formula::addEVar()
 * \sa Formula::addUVar()
 * \sa Formula::copyVar(Variable)
 */
inline Variable Formula::nextVar()
{
    if (deleted_var_numbers.empty()) {
        setMaxVarIndex(maxVarIndex() + 10);
        val_assert(deleted_var_numbers.size() >= 10);
    }

    const Variable result = deleted_var_numbers.back();
    deleted_var_numbers.pop_back();

    val_assert(minVarIndex() <= result && result <= maxVarIndex());
    val_assert(varDeleted(result));

    return result;
}


/**
 * \brief Updates data structures for new variables
 *
 * Resizes all variable-related data structures such that
 * variables up to the given index can be used. The newly
 * created variable numbers are inserted into `deleted_var_numbers`.
 *
 * \param index the largest valid variable ID
 * \sa Formula::nextVar()
 */
inline void Formula::setMaxVarIndex(const Variable index)
{
    if (index <= maxVarIndex()) return;

    const unsigned int old_max_index = maxVarIndex();

    prefix->setMaxVarIndex(index);
    dont_touch.resize(index + 1, false);
    occ_list.resize(2 * index + 2);
    implications.resize(2 * index + 2);
    assignment.resize(index + 1, TruthValue::UNKNOWN);
    _seen.resize(2 * index + 2, false);
    _seen2.resize(2 * index + 2, false);
    gate_output.resize(index + 1, false);
    gate_input.resize(index + 1, 0);

    for (Variable var = index; var > old_max_index; --var) {
        val_assert(minVarIndex() <= var && var <= maxVarIndex());
        val_assert(varDeleted(var));

        deleted_var_numbers.push_back(var);
    }

    val_assert(deleted_var_numbers.size() >= maxVarIndex() - old_max_index);
    val_assert(maxVarIndex() >= index);
}


/**
 * \brief Returns the quantifier level of a variable in a QBF.
 *
 * \pre The formula must be a QBF.
 *
 * The quantifier levels are numbered from left to right,
 * starting with 0 being the left-most (outermost) block.
 */
inline unsigned int Formula::getLevel(Variable var) const noexcept
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() == PrefixType::QBF);
    val_assert(qbf_prefix != nullptr);
    val_assert(minVarIndex() <= var && var <= maxVarIndex());

    return qbf_prefix->getLevel(var);
}


/**
 * \brief Returns the number of clauses.
 */
inline unsigned int Formula::numClauses() const noexcept
{
    return clauses.size() - deleted_clause_numbers.size() + unit_stack.size();
}


/**
 * \brief Returns the maximum used clause ID.
 *
 * Clause IDs are numbered starting from 0. Some of the IDs may no
 * longer be used because clauses have been deleted. This can be checked
 * using Formula::clauseDeleted().
 */
inline unsigned int Formula::maxClauseIndex() const noexcept
{
    val_assert(!clauses.empty());

    return clauses.size() - 1;
}


/**
 * \brief Returns a reference to the clause with the given ID.
 *
 * \pre The accessed clause may not be deleted.
 * \sa Formula::clauseDeleted()
 */
inline const Clause& Formula::getClause(unsigned int c_nr) const noexcept
{
    val_assert(c_nr <= maxClauseIndex());
    val_assert(!clauseDeleted(c_nr));

    return clauses[c_nr];
}


/**
 * \brief Checks if a clause has been deleted.
 */
inline bool Formula::clauseDeleted(unsigned int c_nr) const noexcept
{
    val_assert(c_nr <= maxClauseIndex());

    return clauses[c_nr].getStatus() == ClauseStatus::DELETED;
}


/**
 * \brief Checks if a clause is optional and can be deleted.
 */
inline bool Formula::clauseOptional(unsigned int c_nr) const noexcept
{
    val_assert(c_nr <= maxClauseIndex());

    return clauses[c_nr].getStatus() == ClauseStatus::OPTIONAL;
}

  /**
 * \brief Checks if a clause is mandatory and cannot be deleted.
 */
inline bool Formula::clauseMandatory(unsigned int c_nr) const noexcept
{
    val_assert(c_nr <= maxClauseIndex());

    return clauses[c_nr].getStatus() == ClauseStatus::MANDATORY;
}


/**
 * \brief Returns the number of dependencies of a given variable.
 */
inline unsigned int Formula::numDependencies(Variable var) const noexcept
{
    val_assert(prefix != nullptr);

    return prefix->numDependencies(var);
}


/**
 * \brief Checks if one variable depends on another one.
 * \pre One of the variables needs to be universal, the other one existential.
 * \return true if the dependency between var1 and var2 exists.
 */
inline bool Formula::depends(Variable var1, Variable var2) const
{
    val_assert(prefix != nullptr);
    return prefix->depends(var1, var2);
}


/**
 * \brief Removes a dependency between two variables.
 * \pre One of the variables needs to be universal, the other one existential.
 */
inline void Formula::removeDependency(Variable var1, Variable var2)
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() == PrefixType::DQBF);

    dqbf_prefix->removeDependency(var1, var2);
}


/**
 * \brief Adds a dependency between two variables.
 * \pre One of the variables needs to be universal, the other one existential.
 */
inline void Formula::addDependency(Variable var1, Variable var2)
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() == PrefixType::DQBF);

    dqbf_prefix->addDependency(var1, var2);
}


/**
 * \brief Returns a reference to the dependency set of a given variable.
 */
inline const std::set<Variable>& Formula::getDependencies(Variable var) const
{
    val_assert(prefix != nullptr);
    val_assert(prefix->type() == PrefixType::DQBF);

    return dqbf_prefix->getDependencies(var);
}


/**
 * \brief Adds an implication lit1 => lit2 to the implication data structure
 * \note The equivalent implication ~lit2 => ~lit1 is not added automatically.
 */
inline void Formula::addImplication(Literal lit1, Literal lit2, unsigned int id)
{
    val_assert(lit1 < implications.size());
    val_assert(lit2 < implications.size());

    implications[lit1].insert(BinaryClause(lit2, id));
}


/**
 * \brief Checks if the formula contains an implication lit1 => lit2.
 * \note This does not take transitivity into account.
 */
inline bool Formula::hasImplication(Literal lit1, Literal lit2) const noexcept
{
    val_assert(lit1 >= minLitIndex());
    val_assert(lit2 >= minLitIndex());
    val_assert(lit1 < implications.size());
    val_assert(lit2 < implications.size());

    return implications[lit1].find(BinaryClause(lit2)) != implications[lit1].cend();
}


/**
 * \brief Returns the clause ID of an implication.
 *
 * If there is the implication lit1 => lit2, the ID of the corresponding
 * binary clause is returned. Otherwise the return value is negative.
 */
inline int Formula::getImplicationClause(Literal lit1, Literal lit2) const noexcept
{
    val_assert(lit1 >= minLitIndex());
    val_assert(lit2 >= minLitIndex());
    val_assert(lit1 < implications.size());
    val_assert(lit2 < implications.size());

    const auto found = implications[lit1].find(BinaryClause(lit2));
    if (found == implications[lit1].cend()) return -1;
    else return found->getClauseID();
}


/**
 * \brief Removes the implication lit1 => lit2 from the implication data structure.
 * \note This does neither remove the converse implication ~lit2 => ~lit1 nor the corresponding
 *       binary clause (~lit1, lit2).
 */
inline void Formula::removeImplication(Literal lit1, Literal lit2)
{
    val_assert(lit1 >= minLitIndex());
    val_assert(lit2 >= minLitIndex());
    val_assert(lit1 < implications.size());
    val_assert(lit2 < implications.size());

    implications[lit1].erase(BinaryClause(lit2));
}


/**
 * \brief Returns the assignment of a variable.
 *
 * Value 0 corresponds to unassigned, +1 to TRUE, and -1 to FALSE
 */
inline int32_t Formula::varAssignment(Variable var) const noexcept
{
    if (assignment[var] == TruthValue::UNKNOWN)
        { return 0; }
    else if (assignment[var] == TruthValue::TRUE)
        { return 1; }
    else if (assignment[var] == TruthValue::FALSE)
        { return -1; }
    else
        { val_assert(false); exit(0); }
    return 0;
}


  /**
   * \breif write and read complete settings, useful for reading parsing qdimacs-files
   */
  inline void Formula::setSettings(Settings formula_setting)
  {
	setting = formula_setting;
  }

  inline Settings Formula::getSettings()
  {
	return setting;
  }
  
/**
 * \brief Enables or disables the application of universal reduction.
 */
inline void Formula::setUniveralReduction(bool val) noexcept
{
    setting.univ_reduction = val;
}

inline void Formula::setBlockedClauseElimination(unsigned int val) noexcept
{
    val_assert( val <= 2);
    setting.bce = val;
}

inline void Formula::setHiddenLiterals(unsigned int val) noexcept
{
    setting.hidden = val;
}

inline void Formula::setCoveredLiterals(bool val) noexcept
{
    setting.covered = val;
}

inline void Formula::setBlockedLiteralElimination(bool val) noexcept
{
    setting.ble = val;
}

inline void Formula::setBlockedLiteralAddition(bool val) noexcept
{
    setting.bla = val;
}

inline void Formula::setBlockedImplicationAddition(bool val) noexcept
{
    setting.bia = val;
}

inline void Formula::setMaxClauseSize(unsigned int val) noexcept
{
    setting.max_clause_size = val;
}

inline void Formula::setHiddenSubsumptionElimination(bool val) noexcept
{
    setting.hse = val;
}

inline void Formula::setImplicationChains(bool val) noexcept
{
    setting.impl_chains = val;
}

inline void Formula::setHiddenEquivAndContraChecking(bool val) noexcept
{
    setting.hec = val;
}

inline void Formula::setContradictionChecking(bool val) noexcept
{
    setting.contradictions = val;
}

inline void Formula::setSubstitutions(bool val) noexcept
{
    setting.substitution = val;
}

inline void Formula::setMaxSubstitutionCost(int val) noexcept
{
    setting.max_substitution_cost = val;
}

inline void Formula::setMaxSubstitutionLoops(unsigned int val) noexcept
{
    setting.max_substitution_loops = val;
}

inline void Formula::setRewritings(bool val) noexcept
{
    setting.rewrite = val;
}

inline void Formula::setSelfSubsumption(bool val) noexcept
{
    setting.self_subsumption = val;
}

inline void Formula::setSubsumption(bool val) noexcept
{
    setting.subsumption = val;
}

inline void Formula::setResolution(bool val) noexcept
{
    setting.resolution = val;
}

inline void Formula::setMaxResolutionCost(int val) noexcept
{
    setting.max_resolution_cost = val;
}

inline void Formula::setConstSatCheck(bool val) noexcept
{
    setting.sat_const = val;
}

inline void Formula::setImplSatCheck(bool val) noexcept
{
    setting.sat_impl = val;
}

inline void Formula::setUniversalExpansion(unsigned int val) noexcept
{
    val_assert( val <= 2 );
    setting.univ_expand = val;
}

inline void Formula::setVerbosity(unsigned int val) noexcept
{
    setting.verbosity = val;
}

inline void Formula::setMaxLoops(unsigned int val) noexcept
{
    setting.max_loops = val;
}

inline void Formula::setConsistenceCheck(bool val) noexcept
{
    setting.do_consistency_check = val;
}


inline void Formula::useProcessLimits(bool val) noexcept
{
    process_limit.useLimit(val);
}


inline void Formula::setForceDQBF(bool val) noexcept
{
    setting.force_dqbf = val;

    if (setting.force_dqbf && prefix->type() == PrefixType::QBF) {
        if (setting.verbosity > 1) {
            std::cout << "c Switching to DQBF prefix representation as requested by user.\n";
        }
        dqbf_prefix = qbf_prefix->convertToDQBF();
        delete qbf_prefix;
        qbf_prefix = nullptr;
        prefix = dqbf_prefix;
    }
}


inline void Formula::setIncompleteChecks(bool val) noexcept
{
    setting.sat_incomplete = val;
}


inline void Formula::setPreserveGates(bool val) noexcept
{
    setting.preserve_gates = val;
}

inline void Formula::printSettings(std::ostream& stream) const
{
    stream << setting << std::endl;
}

inline void Formula::clearSeen() const
{
    std::fill(_seen.begin(), _seen.end(), false);
}

template<typename Container>
inline void Formula::clearSeen(const Container& container) const
{
    for (const auto lit: container) {
        _seen[lit] = false;
    }
}

template<typename Container>
inline void Formula::setSeen(const Container& container) const
{
    for (const auto lit: container) {
        val_assert(_seen[lit] == false);
        _seen[lit] = true;
    }
}

  template<typename Container>
inline void Formula::clearSeen2(const Container& container) const
{
    for (const auto lit: container) {
        _seen2[lit] = false;
    }
}

template<typename Container>
inline void Formula::setSeen2(const Container& container) const
{
    for (const auto lit: container) {
        val_assert(_seen2[lit] == false);
        _seen2[lit] = true;
    }
}

} // end namespace hqspre


#endif
