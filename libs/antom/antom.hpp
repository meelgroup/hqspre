
#ifndef ANTOM_HPP
#define ANTOM_HPP

/********************************************************************************************
antom.hpp -- Copyright (c) 2014, Tobias Schubert, Sven Reimer

Permission is hereby granted, free of charge, to any person obtaining a copy of this 
software and associated documentation files (the "Software"), to deal in the Software 
without restriction, including without limitation the rights to use, copy, modify, merge, 
publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons 
to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING 
BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
********************************************************************************************/

// Include standard headers.
#include <iostream>
#include <cassert>
#include <vector>
#include <deque>
#include <omp.h>
#include <cstdint>

// Some definitions.
#define ANTOM_UNKNOWN                  0
#define ANTOM_SAT                     10
#define ANTOM_UNSAT                   20
#define ANTOM_UNSAT_WITH_ASSUMPTION   30

#define MEMALLOCATION
//#define PARALLEL

enum preprotype {
  e_pre,
  e_in,
  e_incremental,
};

enum simplifystrategy {
  ANTOM,
  MINISAT,
};

enum restartstrategy {
  LUBY,
  GLUCOSE,
};

template<typename T1, typename T2>
bool sortPairBySecond( const std::pair<T1, T2>& i, const std::pair<T1, T2>& j )
{
  if( i.second != j.second )
    { return ( i.second < j.second ); }
  else
    { return ( i.first < j.first ); }
}

template<typename T1, typename T2>
bool sortPairBySecondReverse( const std::pair<T1, T2>& i, const std::pair<T1, T2>& j )
{
  if( i.second != j.second )
    { return ( i.second > j.second ); }
  else
    { return ( i.first > j.first ); }
}

namespace antom
{
  // Some forward declarations.
  class Core;
  class Control;
  class Preprocessor;

  // The "Antom" class.
  class Antom
  {

  public:

    // Constructor. 
    Antom (uint32_t threads = 1);
   
    // Destructor.
    ~Antom (void); 

	/* Some statistics */
    
    // Returns the ID of the thread that was able to solve the CNF.
    uint32_t solvingThread (void) const; 

    // Returns the number of variables for which memory has been reserved.
    uint32_t variables (void) const;

	// Returns the last used index. Does not necessary meet with "variables()"
	uint32_t lastIndex(void) const;

    // Returns the current number of clauses within the clause database. 
    uint32_t clauses (void) const; 

    // Returns the current number of literals within the clause database. 
    uint32_t literals (void) const;

    // Returns the number of decisions made so far.
    uint32_t decisions (void) const;

    // Returns the number of BCP operations performed so far.
    uint32_t bcps (void) const;

    // Returns the number of implications found so far. 
    unsigned long implications (void) const;

    // Returns the number of conflicts encountered so far.
    uint32_t conflicts (void) const;

    // Returns the number of restarts performed so far.
    uint32_t restarts (void) const;

    // Returns the number of database simplifications performed so far.
    uint32_t simplifications (void) const;

    // Returns the number of binary clauses deduced due to "Lazy Hyper Binary Resolution".
    uint32_t lhbr (void) const;

    // Returns the number of unit clauses deduced due to conflict analysis.
    uint32_t learntUnitClauses (void) const;
    
    // Returns the number of binary clauses deduced due to conflict analysis.
    uint32_t learntBinaryClauses (void) const;
    
    // Returns the number of ternary clauses deduced due to conflict analysis.
    uint32_t learntTernaryClauses (void) const;

    // Returns the number of synchronizations performed so far. 
    uint32_t synchronizations (void) const;

	// Returns the number of inprocessings steps during solving main routine
	uint32_t inprocessings( void ) const;

    // Returns the average "Literals Blocks Distance" of all conflict clauses deduced so far.
    double avgLBD (void) const;

    // Returns the average length of all conflict clauses deduced so far.
    double avgCCLength (void) const;

    // Returns the solver's average decision level before backtracking.
    double avgDL (void) const;

    // Returns the average number of decision levels cleared during conflict analysis. 
    double avgDLclearedCA (void) const;

    // Returns the average number of variables getting unassigned during conflict analysis. 
    double avgVarsUnassignedCA (void) const;

    // Returns a reference to either the satisfying variable assignment (after calling one of the 
    // "solve()" routines) or the set of currently assigned variables (after calling one of the 
    // two "deduceAssumptions()" routines). Example:
    // model[17] =  0 --> x17 = unassigned
    // model[17] = 35 --> x17 = false 
    // model[17] = 34 --> x17 = true
    // In case neither "solve()/maxSolve()" nor "deduceAssumptions()" has been called beforehand, the 
    // vector contains invalid data. 
    const std::vector<uint32_t>& model (void) const;

	    // Creates and returns a fresh variable index not used so far.
    uint32_t newVariable (void); 

	/* solver options */

    // Activates or deactivates "Lazy Hyper Binary Resolution". 
    // val = TRUE  --> LHBR enabled (default).
    // val = FALSE --> LHBR disabled.
    void setLHBR (bool val); 

    // Sets the unit factor of both restart strategies -- Luby & glucose-like -- to "val" (default: 8). 
    // The unit factor directly corresponds to the interval between two restart operations. 
    void setLuby (uint32_t val);

    // Sets the decision strategy of group "group" to mode "val". 
    // Currently, there are four modes that differ wrt. the polarity of a decision variable:
    // 0 (default) --> Use the variable's cached polarity together with antom's "polarity toggling scheme". 
    // 1           --> Use the variable's cached polarity only.
    // 2           --> The polarity will be set to FALSE regardless of the cached value. 
    // 3           --> The polarity will be set to TRUE regardless of the cached value.
    // Furthermore, antom maintains variable orderings: As long the group with the lowest index is non-empty,
	// variables from that group will be preferred to serve as decision variables. By default, all 
    // variables belong to "group 0".
    void setDecisionStrategy (uint32_t val, uint32_t group);

	// Like "setDecisionStrategy()" for a specific variable instead of a group
    void setDecisionStrategyForVariable (uint32_t val, uint32_t var);

    // Sets the restart strategy to model "val":
    // 0 --> Luby (default).
    // 1 --> Glucose-like.       
    void setRestartStrategy (restartstrategy val);

	void setSimplifyStrategy (simplifystrategy val);

    // Sets the decay factor to "val" (default: 1.05). The decay factor is responsible 
    // for controlling how the variable activities evolve during the search process. 
    void setDecayFactor (double val);

    // Sets the maximum variable index to "max". 
    void setMaxIndex (uint32_t max);

    // Sets the group of variable "var" to "grp". See "setDecisionStrategy()" for more details. 
    void setVarGroup (uint32_t var, uint32_t grp);

	void useTernaryClauses (bool val);

	// Returns whether variable was already deleted in pre-/in-processing
	bool isDeleted( uint32_t var ) const;

	// Defines CPU limit in seconds (default: no CPU limit)
	void setCPULimit ( double t );

    // Adds a clause to the clause databases of all threads. Returns FALSE if the CNF formula is unsatisfiable, 
    // otherwise TRUE will be returned. Assumes that the solver is on decision level 0 and that "clause" is not 
    // empty. Furthermore, all literals have to be encoded as follows, having variable indices greater 0:
    //  x3 <--> (3 << 1)     = 6
    // -x3 <--> (3 << 1) + 1 = 7
    // All clauses inserted into the clause database using "addClause()" are assumed to belong to 
    // the original CNF formula (having a "Literals Blocks Distance" of 1). 
    // IN THE MULTI-THREADED MODE, "maxSetIndex()" HAS TO BE CALLED BEFOREHAND.
    bool addClause (std::vector<uint32_t>& clause, uint32_t lbd = 1);

    // Adds a clause to the clause databases of all threads. Returns FALSE if the CNF formula is unsatisfiable, 
    // otherwise TRUE will be returned. Assumes that the solver is on decision level 0 and that "lits != NULL" 
    // and "num > 0" holds. Furthermore, all literals have to be encoded as follows, having variable indices greater 0:
    //  x3 <--> (3 << 1)     = 6
    // -x3 <--> (3 << 1) + 1 = 7
    // All clauses inserted into the clause database using "addClause()" are assumed to belong to 
    // the original CNF formula (having a "Literals Blocks Distance" of 1). 
    // NOTE, THAT THIS VARIANT OF "addClause()" REQUIRES THAT
    // 1) THE CLAUSE TO BE ADDED DOES NOT CONTAIN MULTIPLE COPIES OF THE SAME LITERAL,
    // 2) THE CLAUSE TO BE ADDED IS NOT A TAUTOLOGICAL ONE, AND
    // 3) "setMaxIndex()" HAS BEEN CALLED BEFOREHAND.
    bool addClause (uint32_t* lits, uint32_t num, uint32_t lbd = 1);

	// Add unit clause, using literal encoding as in "addClause()"
	bool addUnit ( uint32_t lit );

	/* MaxSAT interface */

	// Add a clause to the soft clause database
	bool addSoftClause ( std::vector<uint32_t>& clause );

	// Incremental usage of MaxSAT: push-pop semenatics, see also picosat for more details
	// The push-pop concept can only be applied to soft clauses
	
	// 
	// Opens a new context
	void softclause_push ( void );

	// Closes a context
	void softclause_pop ( void );

	// Proceed all soft clauses
	// Count positive and negative occurences of all variables in soft clauses
	// Set decision strategy for the variables such that the polarity with more occurences is prefered
	// If there is no larger occurence value for a polarity, set the decision strategy to "0"
	// If "pos" is false the polarity with less occurences is prefered (default: true)
	void setStrategyforSoftVariables ( bool pos );

	// val = 0 --> switch off incremental mode for maxSAT (default)
	// val = 1 --> use maxSAT part of SAT incrementally (soft clauses are deleted after each call).
	// val = 2 --> use maxSAT part of SAT incrementally (soft clauses are kept after each call).
	void setIncrementalMode ( uint32_t val );

	// Set predefined bounds
	void setMaxBounds ( uint32_t low, uint32_t high );
	void setLowerBound ( uint32_t low );
	void setHigherBound ( uint32_t high );

	// Sort Groups for maxSAT mode
	// val = 0 --> no particular order (default)
	// val = 1 --> lower priority for original variables
	// val = 2 --> random priority
	// val = 3 --> lower priority for pseudo Boolean constraint encoding
	void setSortVarorder( uint32_t val );

	/* Solver interface */

    // Collects data for performing a regression analysis afterwards (--> SATzilla-like SAT solving). 
    // NOTE, THAT "getDataRegressionAnalysis()" CAN BE USED IN SINGLE-THREADED MODE ONLY.
    void getDataRegressionAnalysis (void);

    // Solves the current CNF formula using the most promising configuration of antom. The return values are SAT/UNSAT.
    // NOTE, THAT "solveSATzilla()" CAN BE USED IN SINGLE-THREADED MODE ONLY.
    uint32_t solveSATzilla ( void );

    // Performs unit propagation, taking the current CNF and the specified assumptions into account. Returns 
    // FALSE if a conflict occurs, otherwise the return value is TRUE. NOTE, THAT "deduceAssumptions()" CAN BE 
    // USED IN SINGLE-THREADED MODE ONLY.
    bool deduceAssumptions (void);
    bool deduceAssumptions (const std::vector<uint32_t>& assumptions);

	// Simplify Database
	void simplify( void );

    // Solves the current CNF formula, taking assumptions (if specified) into account. The assumptions have to be encoded in the 
    // same way as the literals of a clause (see "addClause()"). The return values are SAT/UNSAT. In the multi-threaded mode, the 
    // CNF formula gets solved by "m_threads" threads running in parallel, according to the well-known algorithm portfolio scheme. 
    uint32_t solve (void);
    uint32_t solve (const std::vector<uint32_t>& assumptions);

    // Solves the current (partial) MaxSAT formula. Returns SAT/UNSAT and modifies "optimum", representing the minimum number of 
    // unsatisfied clauses. The modes of operation are:
    // mode = 0 --> unsatisfiability-based (multi-threaded: internal portfolio),
    // mode = 1 --> satisfiability-based (multi-threaded: internal portfolio).
    // mode = 2 --> binary search (multi-threaded: internal portfolio).
	// mode 3 and 4 currently not supported
	// mode = 3 --> combined satisfiability/unsatisfiability approach for incremental usage (multi-threaded: internal portfolio).
	// mode = 4 --> combined unsatisfiability/satisfiability approach for incremental usage (multi-threaded: internal portfolio).
    uint32_t maxSolve ( uint32_t& optimum, uint32_t mode );

    uint32_t maxSolve ( const std::vector<uint32_t>& externalAssumptions, uint32_t& optimum, uint32_t mode );

	// Solve in partial Mode
	uint32_t maxSolvePartial( uint32_t& optimum, uint32_t mode );

	uint32_t maxSolvePartial ( const std::vector< uint32_t >& externalAssumptions, uint32_t& optimum, uint32_t mode );

	uint32_t getExtendedResult( void ) const;

	/* Some maxSAT related interface functions */
	void setMaxWidth ( uint32_t width );
	void setSplittedWidth ( uint32_t width );
	void setMaxParts ( uint32_t parts );
	void setSortSoftClauses ( uint32_t val );
	void calcSplitWidth ( void );
	void setSkip ( bool val );
	void setCSC ( uint32_t val );
	void setTrigger ( bool val );
	void setIncompleteMode ( bool val );
	void setHorizontalWidth ( uint32_t val );
	void setGridMode ( uint32_t val );
	void setNetworktype( uint32_t val );

	// Writes current clauses into "db"
	void getClauseDatabase( std::vector< std::vector< uint32_t > >& db );

	// Returns learnt conflict clauses and their "LBD"-value
	// Useful for "Internal constraints replication"
	// See O. Strichman "Accelerating Bounded Model Checking of Safefy Properties" for more details
	std::vector< std::pair<std::vector< uint32_t >, uint32_t > > getConflictClauses( void ) const;

    // Stores the current status of all SAT solving cores.
    void saveStatus (void);

    // Restores the status of all SAT solving cores saved before by "saveStatus()".
    void restoreStatus (void);
    
    // Deletes the status of all SAT solving cores saved before by "saveStatus()". 
    void deleteStatus (void); 

    // Resets all SAT solving cores.
    void reset (void);

	/* Preprocessor interface */

	// De-/activates UPLA in preprocessing (default: TRUE)
	void setUPLA( bool val );

	// De-/activates full subsumption check in preprocessing  (default: TRUE)
	void setSubsumption( bool val );

	// De-/activates variable elimination in preprocessing  (default: TRUE)
	void setVarElim( bool val );

	// Set thresholds for cost (default: 10) and increase factor (default: 0 ) in variable elimination
	void setVarIncrease( uint32_t costs, int increase );

	// Sets maximum number of preprocessing loops (default: 1.000.000)
	void setMaxLoops( uint32_t val );

	// Should variable "var" be a "Don't Touch" variable?
	void setDontTouch( uint32_t var, bool dt = true );

	// Return true if "var" is a "Don't Touch" variable
	bool isDontTouch( uint32_t var );

	// De-/actives preprocessing (default: FALSE)
	void setPreprocessing( bool val );

	// De-/actives inprocessing during solving (default: FALSE)
	void setInprocessing( bool val );

	// De-/active inprocessing during max-antom (default: FALSE)
	void setMaxInprocessing ( bool val );

	// Simplifies the current CNF formula by performing some preprocessing steps.
	// Returns FALSE if the formula is unsatisfiable, otherwise TRUE
	// type = "e_pre" : standard preprocessing
	// type = "e_in" : inprocessing (lightweighted preprocessing)
	// type = "e_incremental" : incremental preprocessing
	// With "e_incremental" the preprocessor only performs preprocessing on the lastly added variables and clauses
	bool preprocess ( preprotype type = e_pre );

	// Be verbose
	void setVerbosity( uint32_t val );

    // For MAX-SAT we store the soft clauses separately
	struct softclause {

	  // Constructor
	  softclause ( uint32_t trigger, const std::vector< uint32_t >& clause ) :
		s_triggerlit(trigger),
		s_clause(clause),
		s_lastAssignment(0),
		s_simultan(0),
		s_contra(0)
	  {};

	  // Destructor
	  ~softclause ( void ) {}

	  //uint32_t s_trigger;
	  uint32_t s_triggerlit;
	  std::vector<uint32_t> s_clause;

	  int s_lastAssignment;

	  uint32_t s_simultan;
	  uint32_t s_contra;
	};

	// Dumps core data as cnf into std::cout
	void dumpCNF( bool printAssignment = false ) const;

	// get trivial Assignemnts of solver core
	void trivialAssignment (void) const;

  private:

	// Datestructure for managing soft clauses in maxantom
	struct Trigger {

	  // Constructor
	  Trigger ( uint32_t size ) :

		currenttrigger(),
		softclauses(),
		mincontra(size),
		hardmincontra(0),
		maxsimultan(0),
		hardmaxsimultan(0),
		optimum(size),
		depth(0),
		assumption(0),
		firstsolved(false)
	  {};

	  // current trigger to maximize
	  std::vector< uint32_t > currenttrigger;
	  // List of indices corresponding to soft clause trigger
	  std::vector< softclause > softclauses;

	  uint32_t mincontra;
	  uint32_t hardmincontra;
	  uint32_t maxsimultan;
	  uint32_t hardmaxsimultan;
  
	  // The local optimum
	  uint32_t optimum;
	  uint32_t depth;

	  uint32_t assumption;

	  bool firstsolved;

	  uint32_t size ( void ) const { return currenttrigger.size(); }
	};

	// Checks whether soft clauses are satisfied "by chance" by the model "model", i.e. the trigger
	// literal in a soft clause is set to TRUE, but the clause is satisfied without the trigger literal
	// Returns the number of overall satisfied soft clauses
	// If unproceeded = true the last assignment will not be stored
	uint32_t countSatisfiedSoftClauses( const std::vector<uint32_t>& model, Antom::Trigger& triggerPart, bool unproceeded = false );
	uint32_t updateTriggerOptimum ( void );

	// Try to flip variables in soft clauses such that new soft clauses are satisfied
	// Returns number of overall satisfied soft clauses
	uint32_t flipVariables( std::vector< uint32_t >& model );

	void mergePartTrigger ( Antom::Trigger& trigger1, Antom::Trigger& trigger2 );
	void checkAllConflictingSoftclauses( void );

	// Search in soft clauses for sorter bypasses by "deduceAssumption"
	void findSorterCSC ( Trigger& trigger );
	void setSorterCSC ( Trigger& trigger );
	void setSoftTrigger( std::vector< uint32_t >& assumptions );
	void setVerticalBypasses( const Antom::Trigger& trigger );
	void setHorizontalBypasses( const std::vector< uint32_t >& inputA, const std::vector< uint32_t >& inputB, const Trigger& trigger );

	uint32_t calcFirstDepth( uint32_t& result, uint32_t& optimum, uint32_t& overalloptimium, std::vector< uint32_t>& externalAssumptions, uint32_t maxmode );

    // Helper functions to generate the "Bitonic Sorting Network" used for (partial) MaxSAT solving.
    // See http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/bitonic/oddn.htm for more details. 
	void createMaximizer ( Antom::Trigger& trigger );
	void createNextPartialMaximizer( void );
	void createPartialMaximizer( uint32_t part );

    void bitonicSort ( Trigger& trigger, uint32_t lo, uint32_t n, bool dir );
    void bitonicMerge ( Trigger& trigger, uint32_t lo, uint32_t n, bool dir );
    void bitonicCompare ( Trigger& trigger, uint32_t i, uint32_t j, bool dir );

	void oddEvenSort( Trigger& trigger, uint32_t lo, uint32_t n);
	void oddEvenMerge( Trigger& trigger, uint32_t lo, uint32_t n, uint32_t r);
	void oddEvenCompare( Trigger& trigger, uint32_t i, uint32_t j );

	// Deactives soft clasues, deletes sorter clauses and variables
	void invalidateSoftClauses( void );

	// Clears all datastructures by deleting every related clause, etc. 
	// with variable indices between "begin" and "end"
	void clearVariables( uint32_t begin, uint32_t end );

	// Copy constructor.
    Antom (const Antom&);

    // Assignment operator.
    Antom& operator = (const Antom&);

    // The number of threads used for solving.
    uint32_t m_threads; 

    // A pointer to the "Control" object.
    Control* m_control;

    // The SAT solving cores.
    std::vector<Core*> m_core; 

    // The SAT solving pre-/inprocessors.
    std::vector<Preprocessor*> m_preprocessor;

	bool m_dopreprocessing;

	// MaxSAT

    std::vector< softclause > m_softclauses;

	std::vector< Trigger > m_partialTriggerParts;
	std::deque< Trigger > m_currentTriggerParts;

	// partial status variables
	uint32_t m_splittedWidth;
	uint32_t m_maxWidth;
	uint32_t m_maxParts;	
	uint32_t m_horizontalwidth;
	uint32_t m_bypassGrid;
	uint32_t m_horizontalbypasses;
	uint32_t m_verticalbypasses;
	uint32_t m_sortsoftclauses;
	uint32_t m_comparator;
	uint32_t m_skipped;
	uint32_t m_setCSC;
	bool m_doskipping;
	bool m_setTrigger;
	bool m_incompleteMode;

	// 0: bitonic sorter
	// 1: odd even sorter
	// (2: pairwise sorter)
	uint32_t m_networktype;

	uint32_t m_triggervar;

	// Bounds for maximization mode
	uint32_t m_low;
	uint32_t m_high;

	// Define different heuristics for decision variables:
	// 0: no prefences (default)
	// 1: prefer sorter network variables 
	// 2: random preferences
	// 3: prefer original problem variables
	uint32_t m_sortvarorder;

	// The ID of the thread that was able to solve the CNF.
    uint32_t m_sID; 

    // For each core we maintain an uint32_teger to represent (temporary) results.
    std::vector<uint32_t> m_result; 

	// For incremental maxsat: 

	// last index of original problem (wtihout sorter network variables)
	uint32_t m_lastIndex;

	// Perform inprocessing during maxsolve?
	bool m_maxInprocess;

	uint32_t m_stacksize;

	// Variable index triggering all property clauses in incremental mode
	std::vector< uint32_t > m_globalPropertyTrigger;

	// Soft clauses stack for incremental push-pop mechanism
	std::vector< uint32_t > m_softstack;

	// Lists of trigger for different incremental depths
	std::vector< std::vector< uint32_t > > m_triggerlists;
	
  };
}

#endif
