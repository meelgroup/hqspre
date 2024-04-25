#ifndef HQSPRE_FORMULA_HPP_
#define HQSPRE_FORMULA_HPP_

#include <vector>
#include <set>
#include <unordered_set>
#include <exception>
#include <iostream>
#include <string>
#include <map>
#include <stack>
#include "aux.hpp"
#include "literal.hpp"
#include "prefix.hpp"
#include "clause.hpp"
#include "varheap.hpp"
#include "timer.hpp"
#include "settings.hpp"
#include "process_limits.hpp"

/**
 * \file formula.hpp
 * \brief Main header file for DQBF formulas.
 * \author Ralf Wimmer
 * \date 2015-2016
 * \details Contains all functions for manipulating literals and DQBFs.
 */

namespace hqspre {

/**
 * \brief Type of the dependency scheme that is to be applied.
 */
enum class DependencyScheme: int
{
    TRIVIAL = 0,        ///< Trivial dependency scheme as given in the prefix
    STANDARD,           ///< Standard dependency scheme
    STRICT_STANDARD,    ///< Strict standard dependency scheme
    REF_TRIANGLE,       ///< Reflexive triangle dependency scheme
    REF_QUADRANGLE,     ///< Reflexive quadrangle dependency scheme
    RP_STANDARD,        ///< Standard resolution path dependency scheme
    RP_STRICT_STANDARD, ///< Strict standard resolution path dependency scheme
    RP_REF_TRIANGLE,    ///< Reflexive triangle dependency scheme
    RP_REF_QUADRANGLE,  ///< Reflexive quadrangle dependency scheme
    GATE                ///< Gate detection
};


/**
 * \brief How to modify the dependencies
 */
enum class DependencyOperation: int
{
    ADD,       ///< Add dependencies using the selected dependency scheme
    REMOVE,    ///< Remove dependencies using the selected dependency scheme
    DO_NOTHING ///< Do not modify the dependencies.
};


/**
 * \brief Type of a gate.
 */
enum class GateType
{
    AND_GATE, ///< AND-gate
    XOR_GATE, ///< XOR-gate
    MUX_GATE, ///< Multiplexer
    UNKNOWN   ///< unknown (invalid) gate
};



/**
 * \brief Representation of a gate extracted from a formula in CNF.
 */
class Gate
{
public:
    /**
     * \brief Constructs a gate without inputs and unknown type.
     */
    Gate():
        type(GateType::UNKNOWN),
        output_literal(0),
        input_literals(),
        encoding_clauses()
    { }

    GateType type;                         ///< Type of the gate (AND/XOR)
    Literal output_literal;                ///< output literal (might be negated for NAND/EQUIV)
    std::vector<Literal> input_literals;   ///< inputs of the gate (might be negated)
    std::vector<Literal> encoding_clauses; ///< IDs of the clauses encoding the gate
};

std::ostream& operator<<(std::ostream& stream, const Gate& gate);

/**
 * \brief Represents a DQBF with a number of operations on it.
 */
class Formula
{
public:
    //@{
    /**
     * \name Construction, destruction, and assigment
     */

    /**
     * \brief Constructs an empty formula of a given type
     */
    Formula();

    /**
     * \brief Creates a copy of an existing formula.
     */
    Formula(const Formula& other);

    /**
     * \brief Moves an existing formula into a new one.
     */
    Formula(Formula&& other);

    /**
     * \brief Frees the memory occupied by a formula.
     */
    ~Formula() noexcept;

    /**
     * \brief Assigns a new formula to the current object.
     */
    Formula& operator=(const Formula& other) = delete;

    /**
     * \brief Assigns a new formula to the current object (rvalue version)
     */
    Formula& operator=(Formula&& other)      = delete;

    //@}

    //@{
    /**\name Formula input and output
     */
    void read(std::istream& stream);
    void write(std::ostream& stream, bool compact = false) const;
    //@}


    //@{
    /**\name Variable handling
     */
    void setMaxVarIndex(Variable index);
    Variable addUVar();
    Variable addEVar();
    template<typename Container> Variable addEVar(const Container& deps);

    unsigned int numVars()              const noexcept;
    unsigned int numUVars()             const noexcept;
    unsigned int numEVars()             const noexcept;
    unsigned int numLiterals()          const noexcept;
    bool isUniversal(Variable var)      const noexcept;
    bool isExistential(Variable var)    const noexcept;
    unsigned int getLevel(Variable var) const noexcept;
    constexpr static Variable minVarIndex() noexcept;
    Variable maxVarIndex()              const noexcept;
    constexpr static Literal minLitIndex()  noexcept;
    Literal maxLitIndex()               const noexcept;
    void removeVar(Variable var);
    void updateVars();
    bool varDeleted(Variable var)       const noexcept;
    void setDontTouch(Variable var, bool status) noexcept;
    bool isDontTouch(Variable var)      const noexcept;
    //@}


    //@{
    /**\name Clause handling
     */
    unsigned int numClauses() const noexcept;
    unsigned int maxClauseIndex() const noexcept;
    int addClause(const std::vector<Literal>& clause, bool needs_sorting = true, bool check_subsumption = true, ClauseStatus status = ClauseStatus::MANDATORY);
    int addClause(std::vector<Literal>&& clause, bool needs_sorting = true, bool check_subsumption = true, ClauseStatus status = ClauseStatus::MANDATORY);
    int addClause(const Clause& clause);
    int addClause(Clause&& clause);
    const Clause& getClause(unsigned int clause_nr) const noexcept;
    void removeClause(unsigned int c_nr);
    bool removeOptionalClauses();
    bool clauseDeleted(unsigned int c_nr) const noexcept;
    bool clauseOptional(unsigned int c_nr) const noexcept;
    bool clauseMandatory(unsigned int c_nr) const noexcept;
    void writeClauses(std::ostream& stream, std::vector<Variable>* translation_table = nullptr) const;
    //@}

    //@{
    /** \name Gate handling
    */
    Literal addAndGate(Literal input1, Literal input2);
    Literal addNandGate(Literal input1, Literal input2);
    Literal addOrGate(Literal input1, Literal input2);
    Literal addNorGate(Literal input1, Literal input2);
    Literal addXorGate(Literal input1, Literal input2);
    //@}

    //@{
    /**\name Dependency handling
     */
    unsigned int numDependencies() const noexcept;
    unsigned int numDependencies(Variable var) const noexcept;
    bool depends(Variable var1, Variable var2) const;
    void removeDependency(Variable var1, Variable var2);
    void addDependency(Variable var1, Variable var2);
    const std::set<Variable>& getDependencies(Variable var) const;
    bool dependenciesSubset(Variable var1, Variable var2) const;
    //@}


    //@{
    /** \name SAT/QBF-based test for satisfiability
     */
    void checkSAT();
    void checkUNSAT();
     //@}

    //@{
    /**
     * \name Changing the preprocessor settings
     */
    void setSettings(Settings formula_setting);
    Settings getSettings();
    void setUniveralReduction(bool val) noexcept;
    void setBlockedClauseElimination(unsigned int val) noexcept;
    void setHiddenLiterals(unsigned int val) noexcept;
    void setCoveredLiterals(bool val) noexcept;
    void setBlockedLiteralElimination(bool val) noexcept;
    void setBlockedLiteralAddition(bool val) noexcept;
    void setBlockedImplicationAddition(bool val) noexcept;
    void setMaxClauseSize(unsigned int val) noexcept;
    void setHiddenSubsumptionElimination(bool val) noexcept;
    void setImplicationChains(bool val)  noexcept;
    void setContradictionChecking(bool val) noexcept;
    void setHiddenEquivAndContraChecking(bool val) noexcept;
    void setSubstitutions(bool val)      noexcept;
    void setMaxSubstitutionCost(int val) noexcept;
    void setMaxSubstitutionLoops(unsigned int val) noexcept;
    void setRewritings(bool val)         noexcept;
    void setSelfSubsumption(bool val)    noexcept;
    void setSubsumption(bool val)        noexcept;
    void setResolution(bool val)         noexcept;
    void setMaxResolutionCost(int val)   noexcept;
    void setConstSatCheck(bool val)      noexcept;
    void setImplSatCheck(bool val)       noexcept;
    void setVerbosity(unsigned int val)  noexcept;
    void setMaxLoops(unsigned int val)   noexcept;
    void setForceDQBF(bool val)          noexcept;
    void setIncompleteChecks(bool val)   noexcept;
    void setConsistenceCheck(bool val)   noexcept;
    void setUniversalExpansion(unsigned int val) noexcept;
    void setPreserveGates(bool val)      noexcept;
    void useProcessLimits(bool val)      noexcept;
    void setInterrupt(bool val)          noexcept { interrupt = val; }
    //@}


    //@{
    /**\name Preprocessing techniques
     * \todo bool findEquivalentGates();
     * \todo semantic gate detection
     * \todo bool hyperBinaryResolution()
     * \todo bool removeRedundantClausesBySAT()
     * \todo bool UPLA()
     * \todo bool vivification()
     */

    void preprocess();
    std::vector<Gate> preprocessGates();

    // The preprocessor methods
    void fastPreprocess();
    bool unitPropagation();
    bool findPure();
    bool findContradictions();
    bool findEquivalences();
    bool findHiddenEquivAndContraDefinitions();
    bool removeBlockedAndFriends();
    Literal checkImplicationChain(Literal lit);
    bool findImplicationChains();
    bool removeSubsumedClauses();
    bool universalReduction();
    bool applyResolution();
    bool selfSubsumingResolution();
    bool applySubstitution();
    bool applyDependencyScheme(DependencyScheme scheme, DependencyOperation operation);
    bool applyUniversalExpansion();
    bool applyUniversalExpansion2();
    bool applyUniversalExpansionDQBF();
    bool addBlockedImplications();
    bool findConstantsBySAT();
    bool findImplicationsBySAT();
    //@}

    //@{
    /**\name Gate detection
     */
    const std::vector<Gate> determineGates();
    //@}

    //@{
    /**\name Elimination routines
     */
    void eliminateDependency(Variable univ, Variable exist);
    void eliminateVariableE(Variable var, std::set<Variable>& recalc_vars);
    void eliminateVariableU(Variable var);
    //@}

    //{@
    /**\name Miscellaneous
     */
    bool isQBF() const noexcept;
    void convertToQBF();
    void printStatistics(std::ostream& stream) const;
    void printSettings(std::ostream& stream) const;
    //@}

    //@{
    /**\name Debugging functions
     */
    bool checkConsistency() const;
    //@}

private:

    void reset();

    //@{
    /**
     \name Dependency schemes
    */
    template <typename Function>
    void searchPath(
        const std::vector<Literal>& start_lits,
        Function forbidden,
        std::vector<unsigned char>& seen) const;


    template <typename Function>
    void searchResolutionPath(
        const std::vector<Literal>& start_lits,
        Function forbidden,
        std::vector<unsigned char>& seen) const;

    bool stdTriDep(Variable u_var, bool resolution_paths, bool triangle, std::set<Variable>* pseudo_deps = nullptr);
    bool stdTriDep(bool resolution_paths, bool triangle);
    bool sstdQuadDep(Variable u_var, bool resolution_paths, bool quadrangle, std::set<Variable>* pseudo_deps = nullptr);
    bool sstdQuadDep(bool resolution_paths, bool quadrangle);
    bool invStdTriDep(Variable u_var, bool resolution_paths, bool triangle, std::set<Variable>* pseudo_deps = nullptr);
    bool invStdTriDep(bool resolution_paths, bool triangle);
    bool invSstdQuadDep(Variable u_var, bool resolution_paths, bool quadrangle, std::set<Variable>* pseudo_deps = nullptr);
    bool invSstdQuadDep(bool resolution_paths, bool quadrangle);
    bool gateDependencies(DependencyOperation operation);
    //@}

    // For gate detection
    bool checkGatePrecondition(Variable output_var, const Clause& clause) const;

    // Unit propagation and pure literals
    void pushUnit(Literal lit, bool allow_universal = false);
    bool checkPure(Literal lit) const;
    void checkPure(const Clause& clause, Literal except_lit);

    //@{
    /// \name Internal functions for blocked clause elimination
    template <typename Container> Literal clauseBlocked(const Container& clause) const;
    bool clauseBlockedByLit(const Literal blocking_lit) const;
    template <typename Container>
    bool checkResolventTautology(const Container& clause, Variable pivot_var) const;
    bool addHiddenLiterals(const int c_nr, std::vector<Literal>& clause, uint64_t& sign) const;
    bool addHiddenLiteralsBinary(const int c_nr, std::vector<Literal>& clause, uint64_t& sign) const;
    bool addCoveredLiterals(std::vector<Literal>& clause, uint64_t& sign) const;
    template <typename Container> bool addBlockingLiterals(const Container& clause);
    bool checkBlockedLit(uint32_t lit);
    void removeClauseAndUpdateCandidates(unsigned int cl_nr);

    // Experimental function:
    bool pairBlockedClauses();
    //@}

    // Universal expansion
    std::pair<int, int> computeExpansionCosts(Variable uvar) const;
    int computeExpansionCosts2(Variable uvar, const std::set<Variable>& pseudo_deps);
    void markTransitiveUnits(std::stack<Literal>& units, std::vector<bool>& marked);

    // Subsumption checks
    unsigned int isBackwardSubsuming(const Clause& short_clause, int c_nr = -1);
    template <typename Container>
    bool isForwardSubsumed(const Container& clause, const uint64_t sign, int except = -1);
    bool isForwardSubsumed(const Clause& clause, int except = -1);
    template <typename Container> bool isForwardSubsumedByBinary(const Container& clause, int except = -1);
    template <typename Container> unsigned int getSubsumerCandidate(const Container& clause) const;

    // Universal reduction
    bool universalReduction(Clause& clause, int c_nr = -1);

    // Resolution
    int computeResolutionCosts(Variable var) const;
    std::vector<Variable> getResolvableVariables() const;
    bool isResolvable(Variable var) const;

    // Gate substitution
    bool substituteGate(const Gate& g);
    int computeSubstitutionCosts(const Gate& g) const;

    // Gate rewriting, done (according to sQueezeBF's way) when substitution would be too costly
    void rewriteGate(const Gate& g);

    // Equivalence Reduction
    unsigned int replaceSCC(const std::vector<Literal>& scc);

    // Clause modification
    int addClauseToLists(unsigned int c_nr, bool check_subsumption = true);
    bool removeLiteral(unsigned int c_nr, Literal lit);
    void replaceLiteral(Literal lit, Literal replacement);
    void replaceLiteralMono(Literal lit, Literal replacement);
    void addImplication(Literal lit1, Literal lit2, unsigned int id);
    std::pair<bool, bool> hasImplicationTransitive(Literal start_lit, Variable target_var) const;
    bool hasImplication(Literal lit1, Literal lit2) const noexcept;
    int  getImplicationClause(Literal lit1, Literal lit2) const noexcept;
    void removeImplication(Literal lit1, Literal lit2);
    void removeFromOccList(Literal, unsigned int c_nr);

    // Variable functions
    Variable nextVar();
    Variable copyVar(Variable index);

    // Helper functions
    void initCandidateLists();
    void countOccurences();
    void countOccurencesVar();
    void countImplications();
    int32_t varAssignment(Variable var) const noexcept;

    //@{
    /**\name Debugging functions
     */
    bool checkSeen() const;
    Literal getAssignment(Literal lit) const;
    void printFullOccurenceList(Variable var, std::ostream& stream = std::cout) const;
    void printOccurenceList(Literal lit, std::ostream& stream = std::cout) const;
    void printImplications(Literal lit, std::ostream& stream = std::cout) const;
    void printAllClauses(bool print_implications = false, std::ostream& stream = std::cout) const;
    //@}


    // DATA

    /**
     * \brief The quantifier prefix.
     *
     * There are three versions for the quantifier prefix: Formula::prefix
     * is the prefix representation shared by both QBFs and DQBFs. It provides
     * access to all operations that are common for both formula types.
     * In contrast, Formula::qbf_prefix is available only for QBFs and
     * Formula::dqbf_prefix only for DQBFs.
     */
    Prefix* prefix;

    /**
     * \brief The quantifier prefix for DQBFs only.
     *
     * It provides access to all functions to manipulate a DQBF prefix.
     * For all operations that can be applied to QBFs as well, one should
     * use Formula::prefix. Formula::dqbf_prefix is different from nullptr
     * if and only if the formula is a DQBF.
     */
    DQBFPrefix* dqbf_prefix;

    /**
     * \brief The quantifier prefix for QBFs only.
     *
     * It provides access to all functions to manipulate a QBF prefix.
     * For all operations that can be applied to DQBFs as well, one should
     * use Formula::prefix. Formula::qbf_prefix is different from nullptr
     * if and only if the formula is a QBF.
     */
    QBFPrefix* qbf_prefix;

    /**
     * \brief The list of clauses of the formula.
     *
     * Formula::clauses contains all clauses of the formula
     * with the exception of unit clauses, which are stored in
     * Formula::unit_stack until they are propagated. The binary
     * clauses are not only stored in Formula::clauses, but also
     * redundantly in Formula::implications. Note that some of
     * the entries of Formula::clauses might not correspond to
     * valid clauses because they might have been deleted. This
     * can be checked using Formula::clauseDeleted(unsigned int).
     */
    std::vector<Clause> clauses;

    /**
     * \brief Information whether clauses were modified since last reset.
     *
     * Each function which adds, deletes, or modifies a clause
     * marks the clause as modified. This is currently used by
     * Formula::applySubstitution() to check if gates are still
     * valid when they are substituted or rewritten. A gate can get
     * invalid during substitution when one of its defining clauses
     * is removed e.g. by subsumption.
     */
    std::vector<bool> clause_modified;

    /**
     * \brief Information whether a clause encodes a gate.
     *
     * This is used to restrict certain techniques like BCE/HTE/...
     * to clauses which do not encode gates. For circuit-based solvers
     * gate detection is more important than BCE/HTE/...
     */
    std::vector<bool> clause_gate;

    /**
     * \brief Information whether a variable is a gate output.
     *
     * This is used to restrict certain techniques like BCE/HTE/...
     * to variable which are (not) gate outputs. For circuit-based solvers
     * gate detection is more important than BCE/HTE/...
     */
    std::vector<bool> gate_output;

    /**
     * \brief Information how often a variable is used as a gate input.
     *
     * This is used to restrict certain techniques like BCE/HTE/...
     * to clauses are (not) gate inputs. For circuit-based solvers
     * gate detection is more important than BCE/HTE/...
     */
    std::vector<unsigned int> gate_input;

    /**
     * \brief Occurrence lists for all literals.
     *
     * For a literal \f$\ell\f$, Formula::occ_list[\f$\ell\f$] contains the
     * IDs of all clauses that contain \f$\ell\f$.
     */
    std::vector<std::vector<unsigned int>> occ_list;

    /**
     * \brief Stores the implication graph of the binary clauses.
     *
     * Each binary clause \f$(a,b)\f$ corresponds to the two implications
     * \f$\neg a\to b\f$ and \f$\neg b\to a\f$. These implications are stored
     * redundantly in Formula::implications. This is useful not only for
     * equivalence reasoning, but speeds up subsumption checking, hidden
     * literal addition etc.
     */
    std::vector<std::set<BinaryClause>> implications;

    /**
     * \brief Contains the IDs of those clauses which are deleted and therefore available
     *
     * The IDs of clauses that got deleted are recycled when new clauses are
     * added. Formula::deleted_clause_numbers is a list of these IDs.
     */
    std::vector<unsigned int> deleted_clause_numbers;


    /**
     * \brief Contains the IDs of those variables which are deleted and therefore available
     *
     * The IDs of variables that got deleted are recycled when new variables are
     * added. Formula::deleted_var_numbers is a list of these IDs.
     */
    std::vector<unsigned int> deleted_var_numbers;

    /**
     * \brief Stack with unit literals that need to be propagated
     *
     * This stack is used by Formula::pushUnit() and Formula::unitPropagation()
     * for propagating unit literals.
     */
    std::vector<Literal> unit_stack;

    /**
     * \brief Assignment of unit literals; used by Formula::pushUnit() to detect conflicts
     *
     * For each unit literal that is propagated, we store its assignment.
     * We can then recognize conflicting unit clauses (which indicate that the
     * formula is unsatisfiable).
     */
    std::vector<TruthValue> assignment;

    /**
     * \brief States whether a variable may not be touched.
     *
     * This enables us to perform preprocessing for incremental (D)QBF solving.
     * Variables which will appear in clauses that are added later may not be
     * touched (i.e. eliminated, serve as blocking literal of clauses etc.)
     * \note Currently this is not used.
     */
    std::vector<bool> dont_touch;

    /**
     * \brief Vector with costs for each variable, literal, or clause
     *
     * This vector is used together with Formula::candidates to implement
     * a priority queue (min heap). It is used, e.g., to eliminate variables
     * with low costs first.
     */
    std::vector<int> variable_score;

    /**
     * \brief Vector with the length of each clause.
     *
     * This is required for usage in a priority queue.
     */
    std::vector<size_t> clause_sizes;

    /**
     * \brief Priority queue (min heap) for variables, literals, or clauses
     *
     * This priority queue is used together with Formula::variable_score.
     * It is used, e.g., to eliminate variables with low costs first.
     */
    VarHeap<AscendingOrder, int> candidates;


    /**
     * \brief Priority queue (max heap) for usage during "removeBlockedAndFriends"
     */
    VarHeap<DescendingOrder, size_t> blocked_candidates;

    /**
     * \brief Used to temporarily store removed literals during universal reduction
     *
     * This vector is used during universal reduction to store the removed
     * literals. This avoid creating the vector each time a clause is added
     * or modified.
     */
    std::vector<Literal> removed_lits;

    /**
     * \brief A helper vector to store seen literals
     *
     * This vector is used by various methods to memorize which
     * literals have already be seen.
	 * Two data structures are necessary since there are some methods where two independent literals sets have to remembered.
     * \note Due to performance reasons the content of the vector is kept within every hidden/covered literal addition, block clause and friends methods as well as subsumption methods => You have to call "setSeen" and "cleanSeen" manually outside these mehtods.
     * \note All methods assume that the vector is cleared at the beginning of its call (apart from mentioned methods above).
	 * \note seen is currently used for all blocked clause and friends methods (+hidden, covered), dependency schemes, hidden equivalence and contradiction checks, and constant SAT checks
	 * \note seen2 is currently used in subsumption checks and intersection for covered literals
     * \note The user is responsible for clearing the vector, otherwise bad things can happen.
     */
    mutable std::vector<unsigned char> _seen;
    mutable std::vector<unsigned char> _seen2;

    void clearSeen() const;
    template<typename Container> void clearSeen(const Container& container) const;
    template<typename Container> void setSeen(const Container& container) const;
    template<typename Container> void clearSeen2(const Container& container) const;
    template<typename Container> void setSeen2(const Container& container) const;

    /**
     * \brief Preprocessor settings
     *
     * Specifies which techniques should be applied to optimize
     * the formula.
     */
    Settings setting;

    /**
     * \brief Used to abort certain preprocessor methods if they take too long
     *
     * For each method, Formula::process_limit contains a counter which is
     * decremented each time a certain operation is performed (like resolving
     * a clause). If the counter becomes zero, the preprocessing method is
     * aborted.
     */
    mutable ProcessLimit process_limit;

    /**
     * \brief If set to true, the preprocessor stops as soon as possible.
     */
    bool interrupt = false;

    //@{
    /**
     * \name Statistics counter
     */
    unsigned int stat_unit_pure = 0;        ///< How many unit/pure variables have been detected?
    unsigned int stat_univ_reduction = 0;   ///< How many literals have been removed by universal reduction?
    unsigned int stat_univ_expansion = 0;   ///< How many universal variables have been eliminated using expansion?
    unsigned int stat_bce = 0;              ///< How many blocked clauses have been eliminated?
    unsigned int stat_bia = 0;              ///< How many blocked implications have been added?
    unsigned int stat_hte = 0;              ///< How many hidden tautologies have been eliminated?
    unsigned int stat_hse = 0;              ///< How many hidden subsumptions have been eliminated?
    unsigned int stat_ble = 0;              ///< How many blocked universal literals have been eliminated?
    unsigned int stat_bla = 0;              ///< How many blocked universal literals have been added?
    unsigned int stat_impl_chains = 0;      ///< How many implication chains have been eliminated?
    unsigned int stat_contradictions = 0;   ///< How many transitive contradictions have been eliminated?
    unsigned int stat_subsumption = 0;      ///< How many clauses have been deleted by subsumption?
    unsigned int stat_resolution = 0;       ///< How many existential variables have been eliminated using resolution?
    unsigned int stat_selfsubsuming_resolution = 0; ///< How many clauses could be simplified by self-subsuming resolution?
    unsigned int stat_equiv = 0;            ///< How many equivalent variables have been eliminated?
    unsigned int stat_equiv_gates = 0;      ///< How many equivalent gates have been found and eliminated?
    unsigned int stat_hidden_equiv = 0;     ///< How many hidden equivalent variables have been eliminated?
    unsigned int stat_hidden_unit = 0;      ///< How many hidden unit variables have been eliminated?
    unsigned int stat_substitution = 0;     ///< How many existential variables have been eliminated using substitution?
    unsigned int stat_unit_by_sat = 0;      ///< Number of unit clauses found using SAT-solver calls.
    unsigned int stat_rewriting = 0;        ///< How many existential variables have been duplicated using equivalence rewriting?
    unsigned int stat_impl_by_sat = 0;      ///< Number of implications added using SAT-solver calls.
    unsigned int stat_sat_calls = 0;        ///< Number of SAT solver calls
    unsigned int stat_prepro_loops = 0;     ///< Number of performed preprocessor loops
    int stat_dep_schemes = 0;               ///< Change in the number of dependencies by using a dependency scheme.
    //@}

    //@{
    /**
     * \name Timers for the different operations
     */

    /// Timer for different preprocessing techniques
    Timer unit_sat_time;
    Timer impl_sat_time;
    Timer incomplete_sat_time;
    Timer impl_chain_time;
    Timer equiv_time;
    Timer contra_time;
    Timer hidden_equiv_contra_time;
    Timer univ_reduction_time;
    Timer univ_expansion_time;
    Timer bce_time;
    Timer hse_time;
    Timer gate_detection_time;
    Timer gate_sub_time;
    Timer gate_rewrite_time;
    Timer resolution_time;
    Timer self_subsumption_time;
    Timer subsumption_time;
    Timer dependency_time;
    Timer prepro_time;
    //@}
};


/**
 * \brief Exception that is thrown when the formula is recognized to be unsatisfiable.
 */
class UNSATException: public std::exception
{
public:
   UNSATException(Formula* dqbf) : std::exception(), message() {dqbf->printStatistics(std::cout);}

    /**
     * \brief Creates a new UNSATException with a description of its reason
     * \param msg description of the exception's reaon
     * \param dqbf if not nullptr, statistics about preprocessing are printed
     */
    UNSATException(const char * msg, Formula* dqbf = nullptr):
        std::exception(), message(msg)
    {
        if (dqbf != nullptr) dqbf->printStatistics(std::cout);
    }

    /**
     * \brief Creates a new UNSATException with a description of its reason
     * \param msg description of the exception's reaon
     * \param dqbf if not nullptr, statistics about preprocessing are printed
     */
    UNSATException(const std::string& msg, Formula* dqbf = nullptr):
        std::exception(),
        message(msg)
    {
        if (dqbf != nullptr) dqbf->printStatistics(std::cout);
    }

    virtual ~UNSATException() = default;

    /**
     * \brief Returns a description of the reasons why the exception was thrown.
     */
    virtual const char* what() const noexcept override { return message.c_str(); }

private:
    std::string message; ///< Reason for the exception
};


/**
 * \brief Exception that is thrown when the formula is recognized to be satisfiable.
 */
class SATException: public std::exception
{
public:
  SATException(Formula* dqbf) : std::exception(), message() { dqbf->printStatistics(std::cout); }

    /**
     * \brief Creates a new SATException with a description of its reason
     * \param msg description of the exception's reaon
     * \param dqbf if not nullptr, statistics about preprocessing are printed
     */
    SATException(const char * msg, Formula* dqbf = nullptr):
        std::exception(),
        message(msg)
    {
        if (dqbf != nullptr) dqbf->printStatistics(std::cout);
    }

    /**
     * \brief Creates a new SATException with a description of its reason
     * \param msg description of the exception's reaon
     * \param dqbf if not nullptr, statistics about preprocessing are printed
     */
    SATException(const std::string& msg, Formula* dqbf = nullptr):
        std::exception(),
        message(msg)
    {
        if (dqbf != nullptr) dqbf->printStatistics(std::cout);
    }

    virtual ~SATException() = default;

    /**
     * \brief Returns a description of the reasons why the exception was thrown.
     */
    virtual const char* what() const noexcept override { return message.c_str(); }

private:
    std::string message; ///< Reason for the exception
};


/**
 * \brief Output operator for DQBFs.
 *
 * Writes a DQBF in DQDIMACS format to the given stream.
 * \param stream the output stream the formula is written to
 * \param formula the formula that is to be written
 * \return the stream
 * \relates Formula
 */
std::ostream& operator<<(std::ostream& stream, const Formula& formula);


/**
 * \brief Input operator for (D)QBFs (in (D)QDIMACS format)
 *
 * Reads a formula in (D)QDIMACS format from an input stream.
 * \param stream the input stream the formula is read from
 * \param formula the data structure the read formula is stored in
 * \return the stream
 * \relates Formula
 */
std::istream& operator>>(std::istream& stream, Formula& formula);

} // end namespace hqspre

#include "formula.ipp"
#include "formula_blocked_et_al.ipp"

#endif
