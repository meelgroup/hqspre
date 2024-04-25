
/********************************************************************************************
preprocessor.hpp -- Copyright (c) 2016, Sven Reimer

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

#ifndef PREPRO_HPP
#define PREPRO_HPP

#include <algorithm>
#include <iostream>
#include <cassert>
#include <vector>

#include "antom.hpp"
#include "helper.hpp"
#include "clause.hpp"
#include "varheap.hpp"
#include "control.hpp"
#include "statistics.hpp"
#include "watcher.hpp"
#include "reason.hpp"

#include <list>

/* For all routines:
   Add an extra loop, if something changes after unitPropagation, consider the subroutine again
   
   So far:
   At the end of every subroutine unitPropagation is performend, the subroutine does not take the result of the propagation into account
 */

namespace antom {

  class Preprocessor
  {

  public:

	//Constructor.
	Preprocessor ( Core* core );

	//Destructor.
	~Preprocessor ( void ) {};

	// De-/activates UPLA in preprocessing
	void setUPLA ( bool val ) { p_doupla = val; }

	// De-/activates full subsumption check in preprocessing
	void setSubsumption ( bool val ) { p_dosubsumption = val; }

	// De-/activates variable elimination in preprocessing
	void setVarElim ( bool val ) { p_dovarelimination = val; }

	// Set thresholds for cost (default: 10) and increase (default: 0 )
	// Only variables with equal or less "cost" occurences will be considered
	// Variable elimination is only performed if formula is maximum increased by "increase"
	void setVarIncrease( uint32_t costs, int increase )
	{ p_costVal = costs; p_increaseVal = increase; }

	// Sets maximum number of preprocessing loops
	void setMaxLoops ( uint32_t val ) { p_maxloops = val; }

	// Should variable "var" be a "Don't Touch" variable?
	void setDontTouch ( uint32_t var, bool dt = true ) 
	{ 
	  assert( var <= p_variables ); 

	  // Update Preprocessor Data structure if don't touch variables are declared
	  if( p_donttouch.size() <= p_variables )
		{ updateDataStructures(); }

	  p_donttouch[var] = dt; 
	}

	// Returns true, if "var" is a "Don't Toch" variable
	bool isDontTouch ( uint32_t var )
	{ 
	  assert ( var <= p_variables );
	  if( p_donttouch.size() < p_variables )
		{ return false; }
	  return p_donttouch[var];
	}

	// Simplifies the current CNF formula by performing some preprocessing steps.
	// Returns ANTOM_UNSAT if the formula is unsatisfiable, otherwise ANTOM_UNKNOWN
	// type = "e_pre" : standard preprocessing
	// type = "e_in" : inprocessing (lightweighted preprocessing)
	// type = "e_incremental" : incremental preprocessing
	// With e_incremental the preprocessor only performs preprocessing on the lastly added variables and clauses
	uint32_t preprocess ( preprotype type );

	// Some fast preprocessing routines, which can be called often
	// If incremental = TRUE: Just check variables with index >= "p_firstPreIndex"
	bool fastPreprocess ( bool& didsomething, bool incremental = false );

	// Set variable index at which point the next preprocessing starts
	void setPreVarIndex ( uint32_t val )
	{ p_firstPreVarIndex = val; }

	// Set index for internal clause datastructure at which point the next preprocessing starts
	// Assumes that the clause database is not shrinked until next incremental preprocessor call
	void setPreClauseIndex ( void )
	{ p_firstPreClauseIndex = p_clauseDatabase.size()+1; }

	// DEBUGGING
	void printDatabase ( bool printOccur = true, bool printWatches = false ) const;

  private:

    // Resets the Preprocessore. The following status flags/variables remain untouched:
	// * The references of the core
	// * Information about replaced variables and clauses 
	// * Don't touch variables
	// * Overall statistics 
	// * DoPreprocessing and DoInprocessing flags
	void reset (void);

	/* Begin: some helper functions */

    // Updates all data structures depending on the number of variables to be able to handle "p_variables" variables.

	void updateDataStructures ( void );

	// Adds (lit1 + lit2) to binaries. 
	// If (lit1 + lit2) already exists, do nothing#
	// Returns false, if binary already exists
	bool addBinary ( uint32_t lit1, uint32_t lit2, bool learned );

	// Remove the "pos"th binary entry in the binary list of "lit"
	// "pos" and "size" will be updated
	void removeBinary ( uint32_t lit, uint32_t& pos, uint32_t& size );

	// Remove the binary (lit1 + lit2) from binary list of "lit1"
	void removeBinary ( uint32_t lit1, uint32_t lit2 );

	// Removes "clause" from occurence list of "lit"
	void removeFromOccurenceList ( uint32_t lit, CRef cr );

	// Removes every occurence of "clause"
	// Mark "clause" as "to deleted"
	void clearAllOccurences ( CRef cr );

	// Removes "literal" from clause
	// Eventually introduces new binary and mark old n-nary for deletion
	// Returns "true" if n-nary clause is deleted, "false" otherwisse
	bool strengthenClause ( CRef cr, uint32_t literal, bool keepoccurence = false );

	// 1. Extract all binaries of watchlist and push them in extra data structure
	// (this can also be done during "addClause", if preprocessing is enabled)
	// 2. Creates occurence lists
	// Assumes that there are no duplicated binaries in "m_watches"
	void preparePreprocessing ( preprotype type );

	// 1. Push the binaries back to watchlists and
	// 2. Update all watchlists
	void updateWatches ( bool showstats = true );

	bool copyBinaryList ( uint32_t toReplace, uint32_t replace ); 
	void copyOccurenceList ( uint32_t toReplace, uint32_t replace ); 

	void preserveModel( uint32_t resvar );
	// Replace every occurence of "toReplace" with "replace"
	// Refresh occurence lists
	// Preserves model for replaced variable
	bool replaceVariable ( uint32_t toReplace, uint32_t replace );

	// Delete all occurences and clauses of "var" in database
	void deleteVariable ( uint32_t var );

	// Merges two n-nary clauses with common literal "reslit"
	// Store new clause in "newClause"
	void mergeClauses ( Clause& clause1, Clause& clause2, uint32_t reslit, std::vector< uint32_t >& newClause ) const;

	// Merges a n-nary clauses "c" with a binary (reslit + otherlit) and common literal "reslit"
	// Store new clause in "newClause"
	void mergeClauses ( Clause& clause, uint32_t reslit, uint32_t otherlit, std::vector< uint32_t >& newClause ) const;

	// Counts the literals of merge of clause "c1" and "c2"
	// Return 0, if result is a tautology
	uint32_t countMergeClauses ( Clause& clause1, Clause& clause2, uint32_t reslit ) const;

	// Counts the literals of merge of clause "c" and "(reslit + otherlit)"
	// Return 0, if result is a tautology
	uint32_t countMergeClauses ( Clause& clause, uint32_t reslit, uint32_t otherlit ) const;

	// Estimates costs for variable elimination of "var"
	int estimateCosts ( uint32_t var );

	// Estimate costs for variable elimination of "var" with more accurate "countMergeClauses"
	int estimateCosts2 ( uint32_t var ) const;

	// Adds a clause to database
	// Do _not_ update watch lists
	// A binary clause is put into the binary datastructure of preprocessor
	// Updates occurence lists for n-nary clauses
	// This method is only used in the preprocessor 
	bool addClausePrepro (std::vector<uint32_t>& clause);

	/* End: some helper functions */

	// Propagate new units
	// Delete all satisfied clauses and their occurence	
	// Strengthen Clauses
	// Returns "false" if a contradiction occurs (formula is UNSAT), otherwise true
	bool propagateUnits ( void );

	// Detect trivial monotone/pure literals
	// If incremental = TRUE: Just check variables with index >= "p_firstPreIndex"
	bool detectMonotone ( bool& didsomething, bool incremental = false);

	// Search in binary clauses for two cases:
	// 1. [(a + b) * (a+ ~b)] => a is constant, imply a
	// 2. [(a + ~b) * (~a + b )] => a and b are equivalent, replace all occurences of a with b (or b with a)
	// If incremental = TRUE: Just check variables with index >= "p_firstPreIndex"
	bool findBinaryConsAndEquiv ( bool& didsomething, bool incremental = false);

	// Performs full subsumptioncheck over all clauses
	// If incremental = TRUE: Just check variables with index >= "p_firstPreIndex"
	bool fullSubsumptionCheck ( uint32_t& didsomething, bool incremental = false );

	// Mark all n-nary clauses which are subsumed by the binary (i1 + i2)
	// Perform self-subsumption, where one clause is a binary
	void checkBinSub ( uint32_t i1, uint32_t i2 );

	// Checks if "clause" is subsumed by another n-nary clause
	// Assumes that the binary subsumption check was already performed
	bool isSubsumed ( Clause& clause ) const;

	// Checks if "clause" is subsumed by another n-nary clause
	// Assumes that the binary subsumption check was already performed
	bool isSubsumed ( const std::vector< uint32_t >& clause, uint32_t sign ) const;

	// Is "clause" subsumed by some clause in database?
	// Assumes that "clause" is sorted
	bool isForwardSubsumed ( const std::vector< uint32_t >& clause, unsigned long long sign ) const;

	// Performs variable elimination
	// If incremental = TRUE: Just check variables with index >= "p_firstPreIndex"
	bool varElimination ( uint32_t& didsomething, bool incremental = false );

	/* UPLA methods */
	void backtrackUPLA (uint32_t declit);
	void addUnit (uint32_t lit);
	// If incremental = TRUE: Just check variables with index >= "p_firstPreIndex"
	bool upla ( uint32_t& didsomething, bool incremental = false );

	// Restore model for deleted variables
	// This method should be called before model is returned
	// Assumes that model of the solver core is already set to "p_model"
	// First restore replaced, then resolved variables
	// Then update replaced variables
	void extendModel ( void );
	bool restoreReplacedVariables ( void );
	bool restoreVariableEliminations ( void );

	void clearRestoreData(uint32_t begin, uint32_t end);

	// DEBUGGING functions
	void printOccurenceList ( uint32_t lit ) const;
	int isAssigned( uint32_t lit ) const;

	friend class Core;

	/* Core references, see also core.hpp for description */
	Core* p_core;
	Control* p_control;

	bool& p_emptyClause;
	uint32_t& p_variables;
	uint32_t& p_dsImplIndex;
	uint32_t& p_dsEndIndex;
	uint32_t& p_decisionLevel;
	std::vector<unsigned char>& p_assignment;
	std::vector<uint32_t>& p_level;
    std::vector<uint32_t>& p_decisionStack;
	std::vector<uint32_t>& p_model;	
	std::vector< Reason >& p_forcing;
	std::vector< unsigned char >& p_deleted;
	std::vector< CRef >& p_clauseDatabase;
	std::vector< std::vector< Watcher > >& p_binaries;
	ClauseAllocator& p_ca;

	/* Additional preprocessing data structures */
	std::vector< std::vector< CRef > > p_occur;
	std::vector< uint32_t > p_replacedby;
	std::vector< unsigned char > p_donttouch;
	std::vector< uint32_t > p_uplaactivity;
	VarHeap< uint32_t > p_uplaheap;
	std::vector< std::vector< uint32_t > > p_replaces;
	std::vector< uint32_t > p_elimclauses;

	uint32_t p_firstPreVarIndex;
	uint32_t p_firstPreClauseIndex;

	/* Some statistics and control values*/
	uint32_t p_maxloops;
	uint32_t p_lastImplIndex;
	bool p_dosubsumption;
	bool p_doupla;
	bool p_dovarelimination;
	uint32_t p_costVal;
	int p_increaseVal;

	Statistics& p_statistics;

  };
}

#endif
