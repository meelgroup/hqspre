
#ifndef CORE_HPP
#define CORE_HPP

/********************************************************************************************
core.hpp -- Copyright (c) 2016, Tobias Schubert, Sven Reimer

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
#include <sys/resource.h>
#include <algorithm>
#include <iostream>
#include <cassert>
#include <vector>
#include <cstdint>

// Include antom related headers.
#include "clause.hpp"
#include "varheap.hpp"
#include "control.hpp"
#include "preprocessor.hpp"

#include "watcher.hpp"
#include "reason.hpp"

namespace antom
{
  // The "Core" class.
  class Core
  {

  public:

    // Constructor.
    Core (uint32_t id = 0, Control* control = NULL) : 
      m_id(id), 
      m_control(control),
	  m_ca(1024*1024),
      m_emptyClause(false), 
	  m_result(ANTOM_UNKNOWN),
      m_variables(0),
	  m_capacity(0),
	  m_statistics(),
      m_assignment(),
      m_level(),
      m_activity(),
      m_polarity(),
      m_forcing(),
	  m_conflict(),
      m_watches(),
      m_varOrder(),
      m_varGroup(), 
	  m_noOfVarGroups(0),
      m_incVarActivity(1.0),
      m_decisionLevel(0),
      m_decisionStack(),
      m_dl2ds(),
      m_dsEndIndex(1),
      m_dsImplIndex(1),
      m_modeDS(), 
	  m_modeDSforvariables(), 
      m_lhbrEnable(false),             
	  m_seen(),
	  m_touched(),
	  m_conflictLiteral(0),
	  m_conflictClause(),
      m_decayFactor(1.05),
      m_lubyShift(8),
      m_decVarSign(),
      m_restartStrategy(LUBY), 
	  m_simplifyStrategy(ANTOM),
      m_basicOps(0), 
      m_model(),
      m_clauseDatabase(),
	  m_useTernary(false),
      m_solverState(),
	  m_preprocessor(NULL),
	  m_dopreprocessing(false),
	  m_doinprocessing(false),
	  m_deleted()
    {
      // Consistency check.
      assert(m_control != NULL); 

	  // Initialize first varorder level
	  updateVarorder(0);
    }

    // Destructor.
    ~Core (void)
    {
      // Delete the solver state.
      deleteStatus();

	  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
		{ assert( m_varOrder[v] != NULL ); delete m_varOrder[v]; }
    }

	// Get extended solver result 
	uint32_t getExtendedResult( void ) const { return m_result; }

	// De-/activates preprocessing
	// This status bit is needed, since we have to reconstruct the model if we have applied preprocessing
	void setPreprocessing( bool val ) { m_dopreprocessing = val; }

	// De-/activates inprocessing
	void setInprocessing( bool val ) { m_doinprocessing = val; }

	// Set preprocessor
	void setPreprocessor( Preprocessor* prepro )
		{ m_preprocessor = prepro; }
 
    // Returns the number of variables for which memory has been reserved.
    uint32_t variableCapacity (void) const { return m_capacity; }

    // Returns the maximial variable index which is used.
	// Does not necessary correspond with "variableCapacity()"
    uint32_t variables (void) const { return m_variables; }

    // Returns the current number of clauses within the clause database. 
    uint32_t clauses (void) const
    {
      uint32_t cl(0); 
      for (uint32_t v = 1; v <= m_variables; ++v)
		{
		  uint32_t lit(v << 1); 
		  for (uint32_t r = 0; r < 2; ++r)
			{
			  lit ^= 1;
			  const std::vector<Watcher>& watches(m_watches[lit]);
			  size_t size(watches.size()); 
			  for( size_t p = 0; p < size; ++p )
				{
				  // Binaries are only stored in watchlists
				  if( watches[p].isBinary() )
					{ ++cl; }
				}
			}
		}

      return ((cl >> 1) + (uint32_t)m_clauseDatabase.size());
    }

    // Returns the current number of literals within the clause database. 
    uint32_t literals (void) const
    {
      uint32_t li(0); 
      for (uint32_t v = 1; v <= m_variables; ++v)
		{
		  uint32_t lit(v << 1); 
		  for (uint32_t r = 0; r < 2; ++r)
			{
			  lit ^= 1; 
			  const std::vector<Watcher>& watches(m_watches[lit]);
			  size_t size = watches.size(); 
			  for( size_t p = 0; p < size; ++p )
				{
				  // Binary literals are counted twice
				  if( watches[p].isBinary() )
					{ ++li; }
				}
			}
		}
      for (uint32_t c = 0; c < m_clauseDatabase.size(); ++c)
		{
		  li += m_ca.getClause(m_clauseDatabase[c])->length();
		}
      return li; 
    }

    // Returns the number of decisions made so far.
    uint32_t decisions (void) const { return m_statistics.decisions; }

    // Returns the number of BCP operations performed so far.
    uint32_t bcps (void) const { return m_statistics.bcps; }
	
    // Returns the number of implications found so far. 
    unsigned long implications (void) const { return m_statistics.implications; }

    // Returns the number of conflicts encountered so far.
    uint32_t conflicts (void) const { return m_statistics.totalConflicts; }

    // Returns the number of restarts performed so far.
    uint32_t restarts (void) const { return m_statistics.restarts; }

    // Returns the number of database simplifications performed so far.
    uint32_t simplifications (void) const { return m_statistics.simplifications; }

    // Returns the number of binary clauses deduced due to "Lazy Hyper Binary Resolution".
    uint32_t lhbr (void) const { return m_statistics.lhbr; }

    // Returns the number of unit clauses deduced due to conflict analysis.
    uint32_t learntUnitClauses (void) const { return m_statistics.totalLearntUnitClauses; }

    // Returns the number of binary clauses deduced due to conflict analysis.
    uint32_t learntBinaryClauses (void) const { return m_statistics.totalLearntBinaryClauses; }

    // Returns the number of ternary clauses deduced due to conflict analysis.
    uint32_t learntTernaryClauses (void) const { return m_statistics.totalLearntTernaryClauses; }

    // Returns the number of synchronizations performed so far. 
    uint32_t synchronizations (void) const { return m_statistics.synchronizations; }

	// Returns the number of inprocessings steps during solving main routine
	uint32_t inprocessings( void ) const { return m_statistics.inprocessings; }

    // Returns the progress after the search process has been stopped due to reaching the limit wrt. synchronizations.
    double progress (void) const { return m_statistics.progress; }

    // Returns the average "Literals Blocks Distance" of all conflict clauses deduced so far.
    double avgLBD (void) const { return m_statistics.avgLBD(); }
 
    // Returns the average length of all conflict clauses deduced so far.
    double avgCCLength (void) const { return m_statistics.avgCCLength(); }

    // Returns the solver's average decision level before backtracking.
    double avgDL (void) const { return m_statistics.avgDL(); }

    // Returns the average number of decision levels cleared during conflict analysis. 
    double avgDLclearedCA (void) const { return m_statistics.avgDLclearedCA(); }

    // Returns the average number of variables getting unassigned during conflict analysis. 
    double avgVarsUnassignedCA (void) const { return m_statistics.avgVarsUnassignedCA(); }

    // Returns a reference to either the satisfying variable assignment (after calling "solve()") or 
    // the set of currently assigned variables (after calling "deduceAssumptions()"). Example:
    // model[17] =  0 --> x17 = unassigned
    // model[17] = 35 --> x17 = false 
    // model[17] = 34 --> x17 = true
    // In case neither "solve()/maxSolve()" nor "deduceAssumptions()" has been called beforehand, the 
    // vector contains invalid data. 
    const std::vector<uint32_t>& model (void) const { return m_model; }

	// Write trivial assignemnts ( assignemnts on decision level 0 ) into model
	void trivialAssignment( void )
	{ 
      // Has to be executed on decision level 0.
      assert(m_decisionLevel == 0);

      // Clear "m_model".
      for (uint32_t v = 1; v <= m_variables; ++v)
		{ m_model[v] = 0; }

      // Copy all assigned variables to "m_model".
      for (uint32_t d = 1; d < m_dsEndIndex; ++d)
		{ 
		  m_model[m_decisionStack[d] >> 1] = m_decisionStack[d]; 
		}
	}

    // Activates or deactivates "Lazy Hyper Binary Resolution" (LHBR). 
    // val = TRUE  --> LHBR enabled (default).
    // val = FALSE --> LHBR disabled.
    void setLHBR (bool val) { m_lhbrEnable = val; }

    // Sets the unit factor of both restart strategies -- Luby & glucose-like -- to "val" (default: 8). 
    // The unit factor directly corresponds to the interval between two restart operations. 
    void setLuby (uint32_t val) { m_lubyShift = val; }

    // Sets the decision strategy of group "group" to mode "val". 
    // Currently, there are four modes that differ wrt. the polarity of a decision variable:
    // 0 (default) --> Use the variable's cached polarity together with antom's "polarity toggling scheme". 
    // 1           --> Use the variable's cached polarity only.
    // 2           --> The polarity will be set to FALSE regardless of the cached value. 
    // 3           --> The polarity will be set to TRUE regardless of the cached value.
    // Furthermore, antom maintains two variable orderings: "group 0" and "group 1". As long as "group 0" is 
    // non-empty, variables from that group will be preferred to serve as decision variables. By default, all 
    // variables belong to "group 1".
    void setDecisionStrategy (uint32_t val, uint32_t group) 
	{ 
	  assert(val < 4 ); 
	  if( group >= m_noOfVarGroups )
		{ updateVarorder(group); }
	  m_modeDS[group] = val; 
	}

	// Like "setDecisionStrategy()" for a specific variable instead of a group
    void setDecisionStrategyForVariable (uint32_t val, uint32_t var) { assert(val < 4 && var <= m_variables); m_modeDSforvariables[var] = val; }

    // Sets the restart strategy to model "val":
    // 0 --> Luby (default).
    // 1 --> Glucose-like.       
    void setRestartStrategy (restartstrategy val) { assert(val < 2); m_restartStrategy = val; }

	void setSimplifyStrategy (simplifystrategy val) { m_simplifyStrategy = val; }
    
    // Sets the decay factor to "val" (default: 1.05). The decay factor is responsible 
    // for controlling how the variable activities evolve during the search process. 
    void setDecayFactor (double val) { m_decayFactor = val; }

    // Sets the maximum variable index to "max". 
    void setMaxIndex (uint32_t max) 
	{ 
	  assert(max > 0); 
	  if( max < m_variables ) 
		{ return; }
	  updateDataStructures(max); 
	}

    // Sets the group of variable "var" to "grp". See "setDecisionStrategy()" for more details. 
    void setVarGroup (uint32_t var, uint32_t grp) 
	{ 
	  assert(var > 0 && var <= m_variables ); 

	  if( grp >= m_noOfVarGroups )
		{ updateVarorder(grp); }
	  m_varGroup[var] = grp; 
	}

	void useTernaryClauses (bool val)
	{
	  m_useTernary = val;
	}

	// Returns whether variable was already deleted in pre-/in-processing
	bool isDeleted( uint32_t var ) const { assert( var <= m_capacity); return m_deleted[var]; }

	// Returns whether an empty clause is deduced
	bool emptyClause( void ) const { return m_emptyClause; }

	void setCPULimit ( double t ) { m_control->setCPULimit(t); }

    // Adds a clause to the clause database. Returns FALSE if the CNF formula is unsatisfiable,
    // otherwise TRUE will be returned. Assumes that the solver is on decision level 0 and that 
    // "clause" is not empty. Furthermore, all literals have to be encoded as follows, having 
    // variable indices greater 0:
    //  x3 <--> (3 << 1)     = 6
    // -x3 <--> (3 << 1) + 1 = 7
    // All clauses inserted into the clause database using "addClause()" are assumed to belong to 
    // the original CNF formula (having a "Literals Blocks Distance" of 1). 
    // IN THE MULTI-THREADED MODE, "maxSetIndex()" HAS TO BE CALLED BEFOREHAND.
    bool addClause (std::vector<uint32_t>& clause, uint32_t lbd = 1)
    {
      // What about the empty clause?
      if (m_emptyClause)
		{ assert( m_result == ANTOM_UNSAT ); return false; }

      // Are we really on decision level 0?
      assert(m_decisionLevel == 0); 

      // If "clause" is empty, we might have a problem.
      assert(!clause.empty()); 

	  /*
	  std::cout << __func__ << " ";
      for (uint32_t c = 0; c < clause.size(); ++c)
		{
		  std::cout << Lit(clause[c]) << " [" << isAssigned(clause[c]) << "] ";
		}
	  std::cout << std::endl;
	  */

      // Sort "clause" to speedup the checks below.
      std::sort(clause.begin(),clause.end());

      // "Shifted" variable indices are assumed to be greater 1.
      assert(clause.front() > 1); 

	  // FIXME Does only work with clause sorting!
	  if( (clause.back()>>1) > m_variables )
		{ updateDataStructures(clause.back()>>1); }

	  // Assume that variable indices was initialized before using "setMaxIndex()"
	  // FIXME Does only work with clause sorting!
	  assert( (clause.back() >> 1) <= m_variables );

      // Initialization.
      size_t stop(clause.size());
      uint32_t lit(0);
      uint32_t size(0); 

      // Check whether "clause" is already satisfied or represents a tautological clause.  
      // By the way, search for multiple copies of the same literal and literals evaluating to FALSE. 
      for (size_t c = 0; c < stop; ++c)
		{
		  // Get the next literal.
		  uint32_t l(clause[c]);

		  // added variable is either assigned or not deleted
		  assert( !m_deleted[l>>1] || m_assignment[l] || m_assignment[l^1] );

		  // "clause" satisfied by "l"? Do we have a tautological clause?
		  // FIXME Does only work with clause sorting!
		  if (m_assignment[l] || (l ^ 1) == lit)
			{ clause.resize(0); return true; }

		  // Do we have to take the current literal into account?
		  // FIXME Does only work with clause sorting!
		  //if (!m_assignment[l ^ 1])
		  if (!m_assignment[l ^ 1] && l != lit)
			{ clause[size++] = l; lit = l; }
		}

      // Do we have an empty clause? CNF formula unsatisfiable?
      if (size == 0)
		{
		  m_emptyClause = true;
		  m_result = ANTOM_UNSAT;
		  return false;
		}

      // Resize "clause" (necessary for the multi-threaded mode to work correctly).
      clause.resize(size); 

      // Do we have a unit clause?
      if (size == 1)
		{
		  // Push the unit literal as a "fake" implication onto the decision stack.
		  addImplication(clause[0]);
		  
		  // What about the effects of this implication?
		  if (!deduce())
			{ m_emptyClause = true; m_result = ANTOM_UNSAT; return false; }

		  // Everything went fine.
		  return true; 
		}

      // Get both watched literals.
      uint32_t wl0(clause[0]);
      uint32_t wl1(clause[1]); 

      // Do we have a binary clause?
      if (size == 2)
		{
		  // Update "m_activity".
		  increaseActivity( (wl0 >> 1), false );
		  increaseActivity( (wl1 >> 1), false );

		  // Check whether we have that particular binary clause already.
		  std::vector<Watcher>& bWatches(m_watches[wl0]);

		  size_t bSize(bWatches.size()); 
		  for (size_t bW = 0; bW < bSize; ++bW)
			{
			  if (bWatches[bW].isBinary() && bWatches[bW].getSecondLit() == wl1)
				{ return true; }
			}

		  ++m_statistics.staticLength += 2;
		  ++m_statistics.staticClauses;

		  // Update "m_watches".
		  m_watches[wl0].push_back( Watcher(wl1, (lbd > 1)) );
		  m_watches[wl1].push_back( Watcher(wl0, (lbd > 1)) ); 

		  // Everything went fine.
		  return true; 
		}

	  // Copy all literals of "clause" to "cptr" and update "m_activity". 
      for (uint32_t l = 0; l < size; ++l)
		{ 
		  increaseActivity( (clause[l] >> 1), false ); 
		}

	  ++m_statistics.staticLength += size;
	  ++m_statistics.staticClauses;

	  CRef cr = m_ca.alloc(clause, lbd, size );
	  
      // Update "m_watches" and "m_clauseDatabase"
	  attachClause(cr);
 
      // Everything went fine.
      return true;
    }

    // Adds a clause to the clause database. Returns FALSE if the CNF formula is unsatisfiable,
    // otherwise TRUE will be returned. Assumes that the solver is on decision level 0 and that 
    // "lits != NULL" and "num > 0" holds. Furthermore, all literals have to be encoded as follows, 
    // having variable indices greater 0:
    //  x3 <--> (3 << 1)     = 6
    // -x3 <--> (3 << 1) + 1 = 7
    // All clauses inserted into the clause database using "addClause()" are assumed to belong to 
    // the original CNF formula (having a "Literals Blocks Distance" of 1). 
    // NOTE, THAT THIS VARIANT OF "addClause()" REQUIRES THAT
    // 1) THE CLAUSE TO BE ADDED DOES NOT CONTAIN MULTIPLE COPIES OF THE SAME LITERAL,
    // 2) THE CLAUSE TO BE ADDED IS NOT A TAUTOLOGICAL ONE, AND
    // 3) "maxSetIndex()" HAS BEEN CALLED BEFOREHAND.
    bool addClause (uint32_t* lits, uint32_t num, uint32_t lbd = 1)
    {
      // What about the empty clause?
      if (m_emptyClause)
		{ assert( m_result == ANTOM_UNSAT ); return false; }
	  
      // Are we really on decision level 0?
      assert(m_decisionLevel == 0); 

      // Everything ok wrt. "lits" and "num"?
      assert(lits != NULL && num > 0); 

	  /*
	  std::cout << __func__ << " ";
      for (uint32_t c = 0; c < num; ++c)
		{
		  std::cout << Lit(lits[c]) << " [" << isAssigned(lits[c]) << "] ";
		}
	  std::cout << std::endl;
	  */

      uint32_t lit(0);
      uint32_t size(0); 

	  // sort clause for efficent tautology checks
	  std::sort(lits, lits+num);

      // Check whether the clause to be added is already satisfied. 
      // By the way, eliminate literals evaluating to FALSE.
      for (uint32_t c = 0; c < num; ++c)
		{
		  // Get the next literal.
		  uint32_t l(lits[c]);

		  // Consistency check.
		  assert((l >> 1) <= m_variables); 

		  // added variable is either assigned or not deleted
		  assert( !m_deleted[l>>1] || m_assignment[l] || m_assignment[l^1]);

		  // "clause" satisfied by "l"? Do we have a tautological clause?
		  // FIXME Does only work with clause sorting!
		  if (m_assignment[l] || (l ^ 1) == lit)
			{ 
			  return true; 
			}

		  // Do we have to take the current literal into account?
		  // FIXME Does only work with clause sorting!
		  if (!m_assignment[l ^ 1] && l != lit)
			{ 
			  lits[size++] = l;
			  lit = l; 
			}
		}

      // Do we have an empty clause? CNF formula unsatisfiable?
      if (size == 0)
		{ 
		  m_emptyClause = true; 
		  m_result = ANTOM_UNSAT; 
		  return false; 
		}
      
      // Do we have a unit clause?
      if (size == 1)
		{
		  // Push the unit literal as a "fake" implication onto the decision stack.
		  addImplication(lits[0]);
		  // What about the effects of this implication?
		  if (!deduce())
			{ 
			  m_emptyClause = true; 
			  m_result = ANTOM_UNSAT;
			  return false; 
			}

		  // Everything went fine.
		  return true; 
		}

      // Get both watched literals.
      uint32_t wl0(lits[0]);
      uint32_t wl1(lits[1]);

      // Do we have a binary clause?
      if (size == 2)
		{	  
		  // Update "m_activity".
		  increaseActivity( (wl0 >> 1), false);
		  increaseActivity( (wl1 >> 1), false);

		  // Check whether we have that particular binary clause already.
		  std::vector<Watcher>& bWatches(m_watches[wl0]);

		  size_t bSize(bWatches.size()); 
		  for (size_t bW = 0; bW < bSize; ++bW)
			{
			  if (bWatches[bW].isBinary() && bWatches[bW].getSecondLit() == wl1)
				{
				  return true;
				}
			}

		  ++m_statistics.staticLength += 2;
		  ++m_statistics.staticClauses;

		  // Update "m_watches".
		  m_watches[wl0].push_back(Watcher(wl1, (lbd > 1 )));
		  m_watches[wl1].push_back(Watcher(wl0, (lbd > 1 )));

		  // Everything went fine.
		  return true; 
		}
      
      // Consistency check.
      assert(size <= num); 

      // Update "m_activity". 
      for (uint32_t l = 0; l < size; ++l)
		{ 
		  increaseActivity( (lits[l] >> 1), false);
		}

	  CRef cr(m_ca.alloc(lits, lbd, size));

	  ++m_statistics.staticLength += size;
	  ++m_statistics.staticClauses;
  
      // Update "m_watches" and "m_clauseDatabase"
	  attachClause(cr);

      // Everything went fine.
      return true;
    }

    // Performs unit propagation, taking the current CNF and the specified assumptions into 
    // account. Returns FALSE if a conflict occurs, otherwise the return value is TRUE. 
    bool deduceAssumptions (const std::vector<uint32_t>& assumptions)
    {
      // Clear "m_model".
	  std::fill(m_model.begin(), m_model.end(), 0 );

	  // Update "m_varOrder".
	  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
		{ 
		  m_varOrder[v]->clear();
		  m_varOrder[v]->resize(m_variables); 
		}

      // What about the empty clause?
      if (m_emptyClause)
		{ assert( m_result == ANTOM_UNSAT); return false; }

      // If there are no variables, we don't have to perform unit propagation.
      if (m_variables == 0) 
		{ return true; }

      // "deduceAssumptions()" has to be executed on decision level 0.
      assert(m_decisionLevel == 0);

      // Push all assumptions onto the decision stack and perform unit propagation.
      if (!setAssumptions(assumptions))
		{ m_control->setDone(); return false; }

      // Copy all assigned variables to "m_model".
      for (uint32_t d = 1; d < m_dsEndIndex; ++d)
		{ 
		  m_model[m_decisionStack[d] >> 1] = m_decisionStack[d]; 
		}

      // Backtrack to decision level 0.
      if (m_decisionLevel != 0)
		{ backtrack(0); }
	  else
		{ assert ( m_result == ANTOM_UNSAT ); }

	  // Everything went fine.
	  return true; 
	}

	// Returns learnt conflict clauses and their "LBD"-value containing clauses with index <= "lastindex"
	// This method assumes that all learnt clauses can be perceived
	std::vector< std::pair<std::vector< uint32_t >, uint32_t > > getConflictClauses( void ) const
	{
	  assert( m_decisionLevel == 0 );

	  std::vector< std::pair<std::vector< uint32_t >, uint32_t > > result;

	  for( uint32_t i = 0; i != m_clauseDatabase.size(); ++i )
		{
		  // Consider learnt clauses

		  if( m_ca[m_clauseDatabase[i]].isLearned() )
			{
			  std::vector< uint32_t > candidate;

			  const Clause& clause(m_ca[m_clauseDatabase[i]]);
			  uint32_t length(clause.length());
			  uint32_t pos(0);
			  for( ; pos < length; ++pos )
				{
				  assert( ( clause[pos] >> 1 ) <= m_variables );
				  assert( !m_deleted[clause[pos]>>1]);
				  // Skip satisfied conflict clauses
				  if( m_assignment[clause[pos]] )
					{ break; }
				  // Skip unsatisfied literals
				  else if( !m_assignment[clause[pos]^1] )
					{ 
					  candidate.push_back(clause[pos]); 
					}
				}

			  if(pos == length )
				{ result.push_back(std::make_pair(candidate, clause.lbd() ) ); }
			}
		}

	  // Now add binary clauses
	  for( uint32_t v = 1; v <= m_variables; ++v )
		{
		  for( uint32_t literal = (v<<1); literal != ((v<<1)+2); ++literal )
			{
			  const std::vector< Watcher >& watches( m_watches[literal] );
			  for( uint32_t i = 0; i != watches.size(); ++i )
				{
				  if( watches[i].isLearnedBinary() && ( (watches[i].getSecondLit()>>1) > v ) )
					{	
					  assert( !m_deleted[watches[i].getSecondLit()>>1] );
					  std::vector< uint32_t > candidate;
					  candidate.push_back( literal );
					  candidate.push_back( watches[i].getSecondLit() );
					  result.push_back( std::make_pair( candidate, 2 ) );
					}
				}
			}
		}
	  return result;
	}

	// Solves the current CNF formula, taking the specified assumptions into account. The assumptions have to be encoded 
	// in the same way as the literals of a clause (see "addClause()"). The return values are SAT/UNSAT/UNKNOWN. In case 
	// "limit" is not equal to 0, the search process will be stopped after "limit" synchronizations. 
	// NOTE, THAT THE CURRENT VERSION OF "solve()" ASSUMES THAT ALL THREADS HAVE THE SAME SET OF ASSUMPTIONS AND THAT THE 
	// MULTI-THREADED MODE FOLLOWS AN ALGORITHM PORTFOLIO APPROACH. 
	uint32_t solve (const std::vector<uint32_t>& assumptions, unsigned long limit = 0)
	{
	  //std::cout << __func__ << std::endl;
	  //dumpCNF(true);

	  // Initialization.
	  uint32_t* unitClauses(NULL); 
	  uint32_t nxtRestart(256);
	  uint32_t lubyNumber(0); 
	  double learntfactor((double)1/(double)(3));
	  double learntinc(1.1);
	  double adjustconflicts(100.0);
	  uint32_t adjustcounts(100);
	  double adjustinc(1.5);
	  uint32_t learntClausesLimit(clauses()*learntfactor); 

	  if( m_simplifyStrategy == ANTOM )
		{
		  learntClausesLimit = 20000;
		}

	  uint32_t rootLevel(0);
	  uint32_t startPtr(1); 
	  uint32_t endPtr(1); 
	  uint32_t result(ANTOM_UNKNOWN);
	  bool limitSpecified(limit != 0); 

	  // Initilaize start time
	  double timeS(0.0);
	  double timeC(0.0);
	  struct rusage resources;

	  getrusage(RUSAGE_SELF, &resources);
	  timeS  = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
	  m_control->setStartTime(timeS);

	  // If there are no variables, the CNF formula is satisfiable by definition.
	  if (m_variables == 0) 
		{ result = ANTOM_SAT; m_result = ANTOM_SAT; m_control->setDone(); goto Synchronization; }

	  // What about the empty clause?
	  if (m_emptyClause)
		{ result = ANTOM_UNSAT; assert( m_result == ANTOM_UNSAT); m_control->setDone(); goto Synchronization; }

	  m_result = ANTOM_UNKNOWN;

	  // Update "m_varOrder".
	  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
		{ 
		  m_varOrder[v]->clear();
		  m_varOrder[v]->resize(m_variables); 
		}

	  // The SAT solving process has to be started on decision level 0.
	  assert(m_decisionLevel == 0);
	  assert(m_dsEndIndex == m_dsImplIndex); 

	  // Push all assumptions onto the decision stack and perform unit propagation.
	  if (!setAssumptions(assumptions))
		{ result = ANTOM_UNSAT; m_control->setDone(); goto Synchronization; }
     
	  // Initialization.
	  rootLevel = m_decisionLevel;
	        
	  if(limitSpecified)
		{ limit += m_statistics.synchronizations; }

	  // Initialize "m_varOrder".
	  for (uint32_t v = m_variables; v > 0; --v)
		{
		  if ( !m_deleted[v] && !m_assignment[v << 1] && !m_assignment[(v << 1) ^ 1])
			{ 
			  m_varOrder[m_varGroup[v]]->insert(v); 
			  ++m_statistics.usedVariables;
			}
		}

	  // Re-initialize some of our status variables.
	  m_decVarSign[0] = false;
	  m_decVarSign[1] = false; 
	  m_basicOps      = 0; 
	  m_statistics.learnedClauses = 0; 
	  m_statistics.localLBD      = 0; 
 
	  // Consistency check.
	  assert(m_dsEndIndex == m_dsImplIndex); 
      
	  // The main SAT solving loop.
	  while (decide())
		{
		  // Perform "Boolean Constraint Propagation".
		  while ( !deduce() )
			{
			  // Unresolvable conflict?
			  if (m_decisionLevel <= rootLevel)
				{ 
				  result = ANTOM_UNSAT;
				  // Unsatisfiable CNF formula? If the decision level is equal to 0, we either don't 
				  // have assumptions or all assumptions are unit clauses (or at least forced by unit 
				  // clauses). Anyway, the assumptions don't play a role and the CNF formula ist not 
				  // only unsatisfiable under assumptions, but unsatisfiable at all.
				  if (m_decisionLevel == 0)
					{ m_emptyClause = true; m_result = ANTOM_UNSAT; m_control->setDone(); goto Synchronization; }

				  // Backtrack to decision level 0.
				  backtrack(0); 

				  // At this point, the CNF formula is unsatisfiable under assumptions.
				  assert( m_result != ANTOM_UNSAT );

				  m_result = ANTOM_UNSAT_WITH_ASSUMPTION; m_control->setDone(); goto Synchronization;
				}

			  // Analyze the current conflict and backtrack.
			  analyze();

			  // What about the time limit?
			  if ( ( ( m_statistics.totalConflicts & 511 ) == 0 ) && m_control->getCPULimit() > 0.0 )
				{
				  getrusage(RUSAGE_SELF, &resources); 
				  timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
				  if( m_control->reachedTimeout( timeC ) )
					{ 
					  assert( m_result != ANTOM_UNSAT);
					  result = ANTOM_UNKNOWN; 
					  m_result = ANTOM_UNKNOWN; 
					  m_control->setDone(); 
					  goto Synchronization; }

				}
	      
			  // What about synchronizing with other threads?
			  if (m_basicOps >= 6000000)
				{
				  // Increment "m_synchronizations".
				  ++m_statistics.synchronizations; 
		  
				  // Reset "m_basicOps".
				  m_basicOps = 0; 

				  // Initialization.
				  endPtr = m_dsEndIndex; 
				  if (m_decisionLevel != 0)
					{ endPtr = m_dl2ds[1]; }

				  // Consistency check.
				  assert(startPtr <= endPtr); 

				  // Export all assignments made on decision level 0 to the "Control" object.
				  m_control->exportUnitClauses(&m_decisionStack[0], startPtr, endPtr, m_id); 

				Synchronization:

#ifdef PARALLEL		  
#pragma omp barrier
#endif
		  
				  // CNF formula solved?
				  if (m_control->done())
					{ 		 		    
					  // Backtrack to decision level 0 (performed by threads that get aborted only).
					  if (m_decisionLevel > 0)
						{ backtrack(0); }

					  return result; 
					}

				  // Get a pointer to the set of unit clauses found by other threads.
				  unitClauses = m_control->importUnitClauses(m_id);
				  assert(unitClauses != NULL); 

				  // Update "startPtr".
				  startPtr = endPtr; 

#ifdef PARALLEL		  
#pragma omp barrier 
#endif

				  // Import unit clauses found by other threads.
				  uint32_t pos(0); 
				  while (unitClauses[pos] != 0)
					{
					  // Get the next unit clause.
					  uint32_t lit(unitClauses[pos]); 
					  // Consistency check.
					  assert((lit>>1) <= m_variables);
					  assert(lit > 1); 
					  assert( m_decisionLevel == 0 );
		      
					  // "lit" incorrectly assigned on decision level 0?
					  if (m_assignment[lit ^ 1] && m_level[lit >> 1] == 0)
						{
						  // At this point the CNF formula is unsatisfiable.
						  m_emptyClause = true; 
						  result = ANTOM_UNSAT; 
						  m_result = ANTOM_UNSAT;
						  m_control->setDone(); 
						  goto Synchronization;
						}

					  // "lit" currently unassigned or assigned on a decision level greater than 0?
					  if ((!m_assignment[lit] && !m_assignment[lit ^ 1]) || m_level[lit >> 1] > 0)
						{ 
						  // Push "lit" as a "fake" implication onto the decision stack.
						  addImplication(lit);
		      
						  // What about the effects of this implication?
						  if (!deduce())
							{ 
							  // At this point the CNF formula is unsatisfiable.
							  m_emptyClause = true; 
							  result = ANTOM_UNSAT; 
							  m_result = ANTOM_UNSAT;
							  m_control->setDone(); 
							  goto Synchronization;
							}
						}
	 
					  // Increment "pos".
					  ++pos;
					}
				}

			  if( m_simplifyStrategy == MINISAT )
				{
				  if( --adjustcounts == 0 )
					{
					  adjustconflicts *= adjustinc;
					  adjustcounts = (int)adjustconflicts;
					  learntClausesLimit *= learntinc;
					  estimateProgress();
					}
				}
	      	      
			  // Should we check for another restart?
			  if (m_statistics.totalConflicts >= nxtRestart)
				{
				  // Do we use a glucose-like restart strategy?
				  if (m_restartStrategy == GLUCOSE)
					{
					  // Initialization. 
					  double global((double) m_statistics.globalLBD / m_statistics.totalConflicts);
					  double local((double) m_statistics.localLBD / (1 << m_lubyShift)); 
		      
					  // What about performing a restart?
					  if ((0.8 * local) > global) 
						{ 
						  // Increment "m_restarts".
						  ++m_statistics.restarts; 
			  
						  // Backtrack to decision level 0.
						  if (m_decisionLevel > 0)
							{ backtrack(0); }
			  
						  // Flip "m_decVarSign" (in case the decision strategy has been set to mode 0).
						  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
							{
							  if (m_modeDS[v] == 0)
								{ m_decVarSign[v] = m_decVarSign[v] ^ true; }
							}
						}
		      
					  // Update "nxtRestart".
					  nxtRestart += 1 << m_lubyShift; 
		      
					  // Reset "m_localAvgLBD".
					  m_statistics.localLBD = 0; 
					}
				  else if (m_restartStrategy == LUBY)
					{
					  // Increment both, "m_restarts" and "lubyNumber".
					  ++m_statistics.restarts; ++lubyNumber; 
		      
					  // Backtrack to decision level 0.
					  if (m_decisionLevel > 0)
						{ backtrack(0); }
		      
					  // Update "nxtRestart".
					  nxtRestart += luby(lubyNumber) << m_lubyShift; 
		      
					  // Flip "m_decVarSign" (in case the decision strategy has been set to mode 0).
					  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
						{
						  if (m_modeDS[v] == 0)
							{ m_decVarSign[v] = m_decVarSign[v] ^ true; }
						}
					} 
				}

			  // Perform inprocessing... wo only perfrom inprocessing when we are on decision level 0
			  if( m_doinprocessing && ( m_decisionLevel == 0 ) && ( (m_statistics.restarts&255) == 0 ) )
				{
				  if( m_preprocessor->preprocess(e_in) == ANTOM_UNSAT )
					{ 
					  m_emptyClause = true; 
					  result = ANTOM_UNSAT; 
					  m_result = ANTOM_UNSAT; 
					  m_control->setDone(); 
					  goto Synchronization; 
					}
				}
			}

		  // Do we have to stop the search process?
		  if (limitSpecified && m_statistics.synchronizations > limit)
			{
			  // Determine the progress.
			  estimateProgress();

			  // Backtrack to decision level 0.
			  if (m_decisionLevel != 0)
				{ backtrack(0); }
	      
			  // Return unknown.
			  assert( m_result != ANTOM_UNSAT );
			  result = ANTOM_UNKNOWN; 
			  m_result = ANTOM_UNKNOWN;
			  m_control->setDone(); 
			  goto Synchronization;
			}
	  
		  // What about the decision level?
		  if (m_decisionLevel < rootLevel)
			{
			  // Push all assumptions onto the decision stack and perform unit propagation.
			  if (!setAssumptions(assumptions))
				{ 
				  result = ANTOM_UNSAT;
				  m_control->setDone(); 
				  goto Synchronization; 
				}
	      	      
			  // Update "rootLevel".
			  rootLevel = m_decisionLevel;
			}
	  
		  // What about simplifying the clause database?
		  if ( m_statistics.learnedClauses >= learntClausesLimit ) 
			{
			  // Simplify the clause database, in particular perform conflict clause deletion.
			  simplify(true);

			  if( m_simplifyStrategy == ANTOM )
				{
				  // Update "learntClausesLimit".
				  learntClausesLimit *= 1.1;
				}
			}
		}
      
	  // At this point, there's no variable left to serve as a decision variable. 
	  // So, we have found a satisfying variable assignment.
#ifndef NDEBUG
	  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
		{ assert(m_varOrder[v]->empty()); }
#endif
      
	  // Clear "m_model".
	  for (uint32_t v = 1; v <= m_variables; ++v)
		{ m_model[v] = 0; }

	  // Store the satisfying variable assignment in "m_model".
	  for (uint32_t d = 1; d < m_dsEndIndex; ++d)
		{ 
		  m_model[m_decisionStack[d] >> 1] = m_decisionStack[d]; 
		}

	  for (uint32_t v = 1; v < m_variables; ++v)
		{ 
		  if( m_model[v] == 0 && !m_deleted[v])
			{
			  // Push fake assignment to model
			  m_model[v] = (m_model[v]<<1);
			}
		}

	  // Add assignment of replaced variables and resolved literals to model
	  if( m_dopreprocessing || m_doinprocessing )
		{ m_preprocessor->extendModel(); }
      
	  // Backtrack to decision level 0.
	  if (m_decisionLevel != 0)
		{ backtrack(0); }
      
	  // Store the result and terminate execution.
	  assert(m_result != ANTOM_UNSAT);
	  result = ANTOM_SAT;
	  m_result = ANTOM_SAT;
	  m_control->setDone(); 
	  goto Synchronization;
	}

	void clearVariables( uint32_t begin, uint32_t end )
	{
	  assert( begin <= end );

	  // Consistency checks.
	  assert(m_dsEndIndex == m_dsImplIndex); 
	  assert(m_decisionLevel == 0 );

	  size_t csize(m_clauseDatabase.size());
	  // Mark all n-nary clauses with (begin <= variables <= end) as "to delete"
	  for( size_t c = 0; c != csize; ++c )
		{
		  Clause& lits( m_ca[m_clauseDatabase[c]] );

		  uint32_t size(lits.length());
		  for(uint32_t pos = 0; pos != size; ++pos )
			{
			  if( ( (lits[pos]>>1) >= begin ) && ( (lits[pos]>>1) <= end ) )
				{
			  
				  // The clause should not be a forcing clause
				  assert( m_forcing[lits[0] >> 1].noReason() );
				  assert( m_forcing[lits[1] >> 1].noReason() );
				  m_ca[m_clauseDatabase[c]].markForDeletion();
				  break;
				}
			}
		}

	  // Delete all clauses with (begin <= variables <= end) from watchlists 
	  for( uint32_t v = 1; v <= m_variables; ++v )
		{
		  if( v >= begin && v <= end )
			{
			  // Clear some status flags for "v"
			  m_deleted[v] = false;
			  m_preprocessor->p_donttouch[v] = false;

			  // Reset some status values for "v"
			  m_activity[v] = 0.0;
			  m_modeDSforvariables[v] = 0;
			  m_varGroup[v] = 0;
			  m_level[v] = 0;
			  // Clear watchlists of "v"
			  std::vector<Watcher>().swap(m_watches[v<<1]);
			  std::vector<Watcher>().swap(m_watches[(v<<1)^1]);
			}

		  for( uint32_t literal = v<<1; literal < ((v<<1)+2); ++literal )
			{
			  std::vector< Watcher >& watches( m_watches[literal] );
			  size_t size(watches.size());
			  for( size_t i = 0; i != size; ++i )
				{
				  if( watches[i].isBinary() )
					{
					  if( ( (watches[i].getSecondLit()>>1) >= begin ) && ( ( watches[i].getSecondLit()>>1) <= end ) )
						{ 
						  watches[i--] = watches[--size];
						  watches.pop_back();
						}
					}
				  else
					{
					  // Delete all watches of n-nary clauses... will be refilled later
					  watches[i--] = watches[--size];
					  watches.pop_back();
					}
				}
			}
		}

	  // Now delete marked n-nary clauses and rebuild watches
	  for( uint32_t c = 0; c != csize; ++c )
		{
		  Clause& clause(m_ca[m_clauseDatabase[c]]);

		  if( clause.toDelete() )
			{		
			  m_clauseDatabase[c--] = m_clauseDatabase[--csize];
			  m_clauseDatabase.pop_back();
			}
		  else
			{
			  // Update "m_watches".
			  m_watches[clause[0]].push_back(Watcher(m_clauseDatabase[c], clause[1]));
			  m_watches[clause[1]].push_back(Watcher(m_clauseDatabase[c], clause[0]));
			  
			  // Update "m_learntClauses" if necessary.
			  if (clause.isLearned())
				{ ++m_statistics.learnedClauses; }
			}
		}

	  m_preprocessor->clearRestoreData(begin, end);

	  // We may have put a deleted variable as fake implication in the decision stack
	  uint32_t i(1);
	  uint32_t j(1);
	  for( ; i < m_dsEndIndex; ++i )
		{
		  uint32_t var( m_decisionStack[i]>>1 );
		  if( ( var < begin ) || ( var > end ) )
			{
			  m_decisionStack[j] = m_decisionStack[i];
			  ++j;
			}
		  else
			{
			  m_assignment[m_decisionStack[i]] = false;
			  assert( !m_assignment[m_decisionStack[i]^1] );
			  assert( m_forcing[var].noReason());
			}
		}
	  m_dsEndIndex = j;
	  m_dsImplIndex = j;

	  // update m_variables
	  if( end == m_variables )
		{ m_variables = begin-1; }
	}

	// Simplifies the clause database by removing
	// -- clauses satisfied due to an assignment made on decision level 0,
	// -- literals evaluating to false due to an assignment made on decision level 0,
	// -- conflict clauses with a high "Literals Blocks Distance" (requires "extended" set to TRUE). 
	void simplify (bool extended)
	{
	  //std::cout << __func__ << std::endl;

	  // Increment "m_simplifications".
	  ++m_statistics.simplifications;

	  m_statistics.clearClauseStatistics();

	  // Consistency check.
	  assert(m_dsEndIndex == m_dsImplIndex); 

	  // Clear "m_forcing" for all implications forced on decision level 0.
	  // By the way, remove all variables assigned on decision level 0 from "m_varOrder".
	  uint32_t p(1); 
	  while (p < m_dsEndIndex && m_level[m_decisionStack[p] >> 1] == 0)
		{ 
		  uint32_t var(m_decisionStack[p] >> 1); 
		  m_forcing[var].clearReason(); 
		  if (m_varOrder[m_varGroup[var]]->inHeap(var))
			{ m_varOrder[m_varGroup[var]]->remove(var); }
		  ++p;
		}

	  // Update "m_watches".
	  for (uint32_t v = 1; v <= m_variables; ++v)
		{
		  // Initialization.
		  uint32_t pLit(v << 1);
		  uint32_t nLit((v << 1) ^ 1);

		  // Variable "v" assigned on decision level 0?
		  if ((m_assignment[pLit] || m_assignment[nLit]) && m_level[v] == 0)
			{
			  // Clear "m_watches[pLit]/m_watches[nLit]".
			  std::vector<Watcher>().swap(m_watches[pLit]);
			  std::vector<Watcher>().swap(m_watches[nLit]);
			}
		  else
			{
			  ++m_statistics.usedVariables;
			  // Shrink "m_watches[pLit]/m_watches[nLit]".
			  for (uint32_t r = 0; r < 2; ++r)
				{
				  // Flip "pLit" (in order to check both polarities). 
				  pLit ^= 1;

				  // Initialization.
				  std::vector<Watcher>& watches(m_watches[pLit]); 
				  size_t wSize(watches.size());

				  // Increment "m_basicOps".
				  m_basicOps += wSize; 

				  // Shrink "m_watches" by removing binary clauses satisfied on decision level 0. 
				  // Furthermore, all elements corresponding to non-binary clauses are removed, too. 
				  for (size_t w = 0; w < wSize; ++w)
					{
					  
						if ( !watches[w].isBinary() || (m_level[watches[w].getSecondLit()>>1] == 0 && m_assignment[watches[w].getSecondLit()]) )
						{ 
						  watches[w--] = watches[--wSize]; 
						  watches.pop_back(); 
						}
					}

				  // Sort "watches".
				  std::sort(watches.begin(), watches.end(), WatchedSorter()); 

				  // Initialization.
				  uint32_t lit(0); 
				  uint32_t size(0); 

				  // Remove duplicates from "watches".
				  for (size_t w = 0; w < wSize; ++w)
					{
					  assert(watches[w].isBinary()); 
					  
					  if (watches[w].getSecondLit() != lit)
						{ 
						  watches[size++] = watches[w]; 
						  lit = watches[w].getSecondLit(); 
						}
					  else
						{
						  if( watches[w].isLearnedBinary() )
							{ 
							  ++m_statistics.learnedClauses; 
							  m_statistics.learnedLength +=2;
							}
						  else
							{ 
							  ++m_statistics.staticClauses; 
							  m_statistics.staticLength +=2;
							}
						}
					}

				  // Shrink "watches".
				  watches.resize(size); 
				}
			}
		}
      
	  // Initialization.
	  size_t size(m_clauseDatabase.size());

	  std::vector<Clause*> candidates;

	  // Increment "m_basicOps".
	  m_basicOps += size; 

	  // Update "candidates".
	  for (size_t c = 0; c < size; ++c)
		{
		  // Get a pointer to the next clause.
		  Clause& lits(m_ca[m_clauseDatabase[c]]);

		  // "clause" currently not forcing an implication and not marked as "to be deleted"?
		  if ( !m_forcing[lits[0] >> 1].forcedby(m_clauseDatabase[c]) && 
			   !m_forcing[lits[1] >> 1].forcedby(m_clauseDatabase[c]) &&
			   !lits.toDelete() )
			{	

			  // Initialization.
			  uint32_t p(0);
			  uint32_t q(0);
	      
			  // Check whether "clause" is satisfied by an assignment made on decision level 0 or 
			  // if it contains literals evaluating to false due to an assignment made on decision level 0.
			  uint32_t size(lits.length());
			  for( ; p != size; ++p )
				{
				  // Current literal unassigned or assigned on a decision level greater 0?
				  if ((!m_assignment[lits[p]] && !m_assignment[lits[p] ^ 1]) || m_level[lits[p] >> 1] > 0)
					{
					  // At this point, we have to keep the current literal.
					  lits[q++] = lits[p]; 
					}
				  else
					{
					  // Consistency check.
					  assert((m_assignment[lits[p]] || m_assignment[lits[p] ^ 1]) && m_level[lits[p] >> 1] == 0); 

					  // "clause" satisfied by "lits[p]"?
					  if (m_assignment[lits[p]])
						{ break; }

					}
				}

			  // Have we reached the end of the clause?
			  if (p == size)
				{
				  // What about the clause length?
				  if (q > 2)
					{
					  // Update the clause length.
					  lits.setLength(q);

					  m_ca.freeLiterals(p-q);

					  // Update the "Literals Blocks Distance" if necessary.
					  if (lits.lbd() > q)
						{ lits.setLBD(q); }
					}
				  else
					{
					  // At this point we have found a new binary clause to be stored separately.
					  assert(q == 2); 

					  // Check whether we already have that particular binary clause.		      
					  std::vector<Watcher>& watches(m_watches[lits[0]]);

					  size_t wSize(watches.size());
					  size_t w(0); 
					  for (; w < wSize; ++w)
						{
						  assert(watches[w].isBinary()); 
						  if (watches[w].getSecondLit() == lits[1])
							{ break; }
						}
		      
					  // Update "m_watches".
					  if (w == wSize)
						{
						  m_watches[lits[0]].push_back(Watcher(lits[1], lits.isLearned()));
						  m_watches[lits[1]].push_back(Watcher(lits[0], lits.isLearned()));
						}

					  // Mark the clause as "to be deleted".
					  lits.markForDeletion();
					}
				}
			  else
				{

				  // Current clause satisfied by an assignment made on decision level 0, 
				  // so let's mark it as "to be deleted".
				  lits.markForDeletion();
				}
		  
			  // "clause" not part of the original CNF, LBD value greater than 2, and "extended" set to TRUE?
			  if (extended && lits.lbd() > 2)
				{ candidates.push_back(m_ca.getClause(m_clauseDatabase[c])); }
			}
		}

	  // Sort "m_watches" again, since we might have some new binary clauses (mandatory for "saveStatus()" & "restoreStatus()".

	  // Sort "candidates" by decreasing "Literals Blocks Distance" values.
	  std::sort(candidates.begin(), candidates.end(), compareLBD);
	  assert(candidates.empty() || candidates[0]->lbd() >= candidates.back()->lbd()); 
    
	  // Resize "candidates".
	  candidates.resize(candidates.size() >> 1); 

//	  std::cout << "c simplify #" << m_statistics.simplifications << ": " << candidates.size() << " clauses deleted" << std::endl;

	  // Mark all candidates as "to be deleted" by setting 
	  // the corresponding "Literals Blocks Distance" values to 0.
	  while (!candidates.empty())
		{ candidates.back()->markForDeletion(); candidates.pop_back(); }

	  
	  // Remove all clauses marked as "to be deleted" from 
	  // the clause database and update "m_watches". 
	  for (uint32_t c = 0; c < size; ++c)
		{
		  Clause& clause(m_ca[m_clauseDatabase[c]]);
		  // Clause marked for deletion?
		  if (clause.toDelete())
			{	      
			  m_ca.free(m_clauseDatabase[c]);
			  --size;
			  m_clauseDatabase[c] = m_clauseDatabase[size];
			  m_clauseDatabase.pop_back();
			  --c;
			}
		  else
			{
			  // Update "m_watches".
			  attachClause(m_clauseDatabase[c], false);

			  // Update "m_learntClauses" if necessary.
			  if (clause.isLearned())
				{ 
				  ++m_statistics.learnedClauses;
				  m_statistics.learnedLength += clause.length();
				}
			  else
				{
				  ++m_statistics.staticClauses;
				  m_statistics.staticLength += clause.length();
				}
			}
		}

	  for (uint32_t v = 1; v <= m_variables; ++v)
		{
		  uint32_t lit(v << 1); 
		  for (uint32_t r = 0; r < 2; ++r)
			{ 
			  lit ^= 1; 

			  /*		  
			  std::cout << "sort: " << Lit(lit) << " " << m_watches[lit].size() << " " << m_watches.size() << std::endl;
			  */
			  std::sort(m_watches[lit].begin(), m_watches[lit].end(), WatchedSorter()); 
			}
		}

	  checkGarbage();
	  // TODO: 
	  // rebuild heap
	}

	bool checkMaxIndex( uint32_t lastIndex );

	void printDatabase ( bool printOccur = true, bool printWatches = false ) const;

	// Writes current clauses into "db"
	void getClauseDatabase( std::vector< std::vector< uint32_t > >& db )
	{
	  for ( uint32_t v = 0; v != m_variables; ++v )
		{
		  size_t size(m_watches[v<<1].size());
		
		  for( size_t i = 0; i != size; ++i )
			{
			  if( m_watches[v<<1][i].isBinary() )
				{ continue; }

			  uint32_t lit = m_watches[v<<1][i].getSecondLit();
			  if( v > ( lit>>1 ) )
				{
				  std::vector< uint32_t > clause;
				  clause.push_back(v<<1);
				  clause.push_back(lit);
				  db.push_back(clause);
				}
			}
			
		  size = m_watches[(v<<1)^1].size();
	
		  for( size_t i = 0; i != size; ++i )
			{
			  if( m_watches[(v<<1)^1][i].isBinary() )
				{ continue; }

			  uint32_t lit(m_watches[(v<<1)^1][i].getSecondLit());
		
			  if( v > ( lit>>1 ) )
				{
				  std::vector< uint32_t > clause;
				  clause.push_back((v<<1)^1);
				  clause.push_back(lit);
				  db.push_back(clause);
				}
			}
		}
	  
	  for( uint32_t d = 0; d != m_clauseDatabase.size(); ++d )
		{
		  Clause& lits(m_ca[m_clauseDatabase[d]]);
		  assert( !lits.toDelete() );
		  std::vector< uint32_t > clause;

		  uint32_t size(lits.length());
		  for( uint32_t pos = 0; pos < size; ++pos )
			{
			  clause.push_back( lits[pos] ); 
			}
		  db.push_back(clause);
		}
	}

	// Dumps cnf into std::cout
	void dumpCNF( bool printAssignment = false ) const;

	// Saves the current status of the SAT solving core. 
	// The following variables/vectors are not stored:
	// -- "m_control",
	// -- "m_id",
	// -- "m_progress", 
	// -- "m_binaryConflictingClause". 
	void saveStatus (void);

	// Deletes the status of the SAT solving core saved before by "saveStatus()". 
	void deleteStatus (void);

	// Restores the status of the SAT solving core saved before by "saveStatus()".
	void restoreStatus (void);

	// Resets the SAT solving core. The following status flags/variables remain untouched:
	// -- The SAT solving threads unique ID number: "m_id".
	// -- The pointer to the "Control" object: "m_control".
	// -- The number of variables for which memory has been reserved: "m_variables".
	void reset (void);

  private:

	// Updates all data structures depending on the number of variables to be able to handle "var" variables.
	void updateDataStructures(uint32_t var)
	{    

	  if( var <= m_capacity )
		{ 
		  m_variables = var;
		  return; 
		}
  
	  // Update "m_level".
      m_level.resize(var + 1, 0); 

      // Update "m_activity".
      m_activity.resize(var + 1, 0.0);

      // Update "m_polarity".
      m_polarity.resize(var + 1, true); 

      // Update "m_forcing".
      m_forcing.resize(var + 1); 

      // Update "m_model".
      m_model.resize(var + 1, 0);

      // Update "m_dl2ds".
      m_dl2ds.resize(var + 1, 1); 

	  // Update "m_modeDSforvariables"
	  m_modeDSforvariables.resize(var+1,0);

      // Update "m_varGroup".
      m_varGroup.resize(var + 1, 0); 

      // Update "m_deleted".
      m_deleted.resize(var+1, false);

      // Update "m_decisionStack".
      m_decisionStack.resize(var + 1, 0); 

	  m_conflictClause.resize(var+1, 0);

	  m_seen.resize(var+1, false);
	  m_touched.resize(var+1, false);
	  
      // Initialization.
      uint32_t max((var << 1) + 2);

      // Update "m_assignment".
      m_assignment.resize(max, false);

      // Update "m_watches".
      m_watches.resize(max);

      // Update "m_variables" and "m_capacity".
      m_variables = var; 
	  m_capacity = var;
    }

	// Update variable order data structures for "group" var order groups
	void updateVarorder(uint32_t group)
	{
	  assert( group >= m_noOfVarGroups);
	  m_varOrder.resize(group+1);
	  m_modeDS.resize(group+1,0);
	  m_solverState.modeDS.resize(group+1,0);
	  m_solverState.decVarSign.resize(group+1, false);
	  m_decVarSign.resize(group+1, false);

	  
	  for( uint32_t v = m_noOfVarGroups; v <= group; ++v )
		{ 
		  VarHeap<double>* varheap = new VarHeap<double>(m_activity);
		  m_varOrder[v] = varheap;
		}	  
	  
	  m_noOfVarGroups = group+1;
	}

    // Helper function for pushing assumptions onto the decision stack.
    // In case of a conflict, FALSE will be returned, otherwise the 
    // return value is TRUE. 
    bool setAssumptions (const std::vector<uint32_t>& assumptions)
    {
      // What about the empty clause?
      if (m_emptyClause)
		{ assert( m_result == ANTOM_UNSAT); return false; }

      // Initialization.
      size_t aSize(assumptions.size());

      // Set all assignments specified by "assumptions".
      for (size_t a = 0; a < aSize; ++a)
		{
		  // Get the next assignment.
		  uint32_t lit(assumptions[a]);

		  // Variable indices are assumed to be greater 0.
		  assert(lit > 1); 

		  // Increment "m_basicOps".
		  ++m_basicOps; 

		  assert( (lit >> 1) <= m_variables );

		  // "lit" already incorrectly assigned?
		  if (m_assignment[lit ^ 1])
			{
			  m_result = ANTOM_UNSAT_WITH_ASSUMPTION;
			  if (m_decisionLevel != 0)
				{ backtrack(0); }
			  return false; 
			}

		  // "lit" currently unassigned?
		  if (!m_assignment[lit])
			{ 
			  // Push "lit" as a "fake decision" onto the decision stack.
			  addDecision(lit); 
	    
			  // What about the effects of this implication?
			  if ( !deduce() )
				{ 
				  m_result = ANTOM_UNSAT_WITH_ASSUMPTION;
				  backtrack(0); 
				  return false; 
				}
			}
		}

      // Everything went fine.
      return true;
    }

    // Adds a decision to the decision stack.
    void addDecision (uint32_t lit)
    { 
	  //std::cout << "add decision " << Lit(lit) << " on dl: " << (m_decisionLevel+1) << std::endl;

      // Increment "m_decisionLevel".
      ++m_decisionLevel; 

      // The variable corresponding to "lit" has to be undefined.
      assert(!m_assignment[lit] && !m_assignment[lit ^ 1]); 
    
      // Update "m_assignment".
      m_assignment[lit] = true;

	  // Update "m_level".
      m_level[lit >> 1] = m_decisionLevel;

      // Update "m_forcing".
      m_forcing[lit >> 1].clearReason();

      // Update "m_dl2ds".
      m_dl2ds[m_decisionLevel] = m_dsEndIndex;  

      // Push "lit" onto the decision stack.    
      m_decisionStack[m_dsEndIndex++] = lit; 
    }


    // Adds an unconditionally forced implication to the decision stack.
    void addImplication (uint32_t lit)
    {
	  //std::cout << "add unconditional implication " << Lit(lit) << " on dl: " << m_decisionLevel << std::endl;

	  // Update "m_implications".
	  ++m_statistics.implications;

	  // The variable corresponding to "lit" has to be undefined.
	  assert(!m_assignment[lit] && !m_assignment[lit ^ 1]);

	  // Update "m_assignment".
	  m_assignment[lit] = true;

	  // Update "m_level".
	  m_level[lit >> 1] = m_decisionLevel;

	  // Update "m_forcing".
	  m_forcing[lit >> 1] = Reason();

	  // Push "lit" onto the decision stack.
	  m_decisionStack[m_dsEndIndex++] = lit;
    }

    // Adds an implication forced by a non-binary clause to the decision stack.
    void addImplication (uint32_t lit, const CRef& reason)
    {    
	  //std::cout << "add n-nary implication " << Lit(lit) << " on dl: " << m_decisionLevel << std::endl;
      // Update "m_implications".
      ++m_statistics.implications; 
	
      // The variable corresponding to "lit" has to be undefined.
      assert(!m_assignment[lit] && !m_assignment[lit ^ 1]); 

      // Update "m_assignment".
      m_assignment[lit] = true;

      // Update "m_level".
      m_level[lit >> 1] = m_decisionLevel;
      
      // Update "m_forcing".
      m_forcing[lit >> 1] = Reason(reason, false);

      // Push "lit" onto the decision stack.    
      m_decisionStack[m_dsEndIndex++] = lit; 
    }

    // Adds an implication forced by a binary clause to the decision stack.
	  void addBinaryImplication (uint32_t lit, uint32_t forcingLit)
    {     
	  // std::cout << "add binary implication " << Lit(lit) << " forcing: " << Lit(forcingLit) << " on dl: " << m_decisionLevel << std::endl;

	  // Update "m_implications".
	  ++m_statistics.implications; 
	
      // The variable corresponding to "lit" has to be undefined.
      assert(!m_assignment[lit] && !m_assignment[lit ^ 1]); 

    
      // Update "m_assignment".
      m_assignment[lit] = true;

	  assert( !m_assignment[lit^1] );
   
      // Update "m_level".
      m_level[lit >> 1] = m_decisionLevel;
      
      // Update "m_forcing".
      m_forcing[lit >> 1] = Reason(forcingLit, true);

      // Push "lit" onto the decision stack.    
      m_decisionStack[m_dsEndIndex++] = lit; 
    }

    // Adds an implication forced by a binary clause to the decision stack.
    void addTernaryImplication (uint32_t lit, uint32_t forcingLit1, uint32_t forcingLit2)
    {     
	  //std::cout << "add ternary implication " << Lit(lit) << " forcing: " << Lit(forcingLit1) << " " << Lit(forcingLit2) << " on dl: " << m_decisionLevel << std::endl;

      // Update "m_implications".
      ++m_statistics.implications; 

      // The variable corresponding to "lit" has to be undefined.
      assert(!m_assignment[lit] && !m_assignment[lit ^ 1]); 
    
      // Update "m_assignment".
      m_assignment[lit] = true;

      // Update "m_level".
      m_level[lit >> 1] = m_decisionLevel;
      
      // Update "m_forcing".
      m_forcing[lit >> 1] = Reason(forcingLit1, forcingLit2);

      // Push "lit" onto the decision stack.    
      m_decisionStack[m_dsEndIndex++] = lit; 
    }

    // Selects the next decision variable and adds it to the decision stack using "addDecision()".
    // Returns TRUE as long as decision variables (still unassigned variables) are available.
    bool decide (void)
    {
	  // Do we have another variable within "m_varOrder[0]"?
	  for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
		{
		  while (!m_varOrder[v]->empty())
			{
			  // Increment "m_basicOps".
			  ++m_basicOps; 

			  // Get the literal corresponding to the variable with the maximum activity
			  // and take the variable's last polarity into account. If "m_decVarSign" 
			  // is set to TRUE, the cached truth value gets inverted.
			  uint32_t var(m_varOrder[v]->top());
			  uint32_t lit(((var << 1) ^ m_polarity[var]) ^ m_decVarSign[v]);
			  // "lit" currently undefined?
			  if (!m_assignment[lit] && !m_assignment[lit ^ 1])
				{
				  // Increment "m_decisions".
				  ++m_statistics.decisions;

				  // Modify "lit" (in case the decision strategy has been set to mode 2 or mode 3)
				  if (m_modeDS[v] == 2)
					{ 
					  lit = (var << 1) ^ 1; 
					}
				  else
					{ 
					  if (m_modeDS[v] == 3)
						{ 
						  lit = var << 1; 
						}
					}

				  // Do the same for variable specific values
				  if (m_modeDSforvariables[var] == 2)
					{ 
					  lit = (var << 1) ^ 1; 
					}
				  else if (m_modeDSforvariables[var] == 3)
					{
					  lit = var << 1; 
					}
		
				  // Push "lit" as a decision onto the decision stack.
				  addDecision(lit); 
	      
				  // Everything went fine.
				  return true;
				}
			}
		}
 
      // At this point, there's no variable left to serve as a decision variable.
      return false;
    }

	bool deduceBinary ( Watcher& watcher, uint32_t& lit )
	{
	  uint32_t otherlit(watcher.getSecondLit());
	  // At this point, we have either an implication or a conflict.
	  if (m_assignment[otherlit ^ 1])
		{
		  //std::cout << "binary conflict with " << Lit(otherlit) << std::endl;
		  // conflict case
		  m_conflictLiteral = otherlit;
		  m_conflict = Reason(lit, true);
		  return false;  
		}
	  else if ( !m_assignment[otherlit] )
		{
		  // Push the second literal as an implication forced
		  // by a binary clause onto the decision stack.
		  addBinaryImplication(otherlit, lit); 
		}
	  return true;
	}


	bool deduceTernary ( Watcher& watcher, uint32_t& lit )
	{
	  uint32_t secondlit(watcher.getSecondLit());
	  if( m_assignment[secondlit])
		{ return true; }

	  uint32_t thirdlit(watcher.getThirdLit());
	  if( m_assignment[thirdlit])
		{ 
		  // Set second lit to assigned lit
		  watcher.setSecondLit(thirdlit);
		  watcher.setThirdLit(secondlit);
		  return true;
		}

	  // secondlit unassigned, thirdlit assigned to false
	  // -> propagte secondlit
	  if( !m_assignment[secondlit^1] && m_assignment[thirdlit^1] )
		{
		  addTernaryImplication(secondlit, lit, thirdlit); 
		}

	  // thirdlit unassigned, secondlit assigned to false
	  // -> propagte thirdlit
	  else if( m_assignment[secondlit^1] && !m_assignment[thirdlit^1] )
		{
		  addTernaryImplication(thirdlit, lit, secondlit); 

		  // Set second lit to assigned lit
		  watcher.setSecondLit(thirdlit);
		  watcher.setThirdLit(secondlit);
		}
	  // both lits assigned to false
	  // -> conflict
	  else if( m_assignment[secondlit^1] && m_assignment[thirdlit^1] )
		{

		  // conflict case
		  assert( ( m_level[secondlit>>1] == m_level[lit>>1] ) || ( m_level[thirdlit>>1] == m_level[lit>>1] ) );
		  // mark secondlit as conflict
		  m_conflictLiteral = secondlit;
		  // Set lit and thirdlit as reason for conflict
		  m_conflict = Reason(lit, thirdlit);
		  return false;  
		}

	  // add this point secondlit and thirdlit are unassigned
	  // -> continue with bcp
	  return true;
	}

	bool deduceNary ( uint32_t& wpos, uint32_t& size, uint32_t& lit )
	{
	  Watcher& watch(m_watches[lit][wpos]);

	  // Get the literals of the next clause to be checked.
	  Clause& clause(m_ca[watch.getClause()]);

	  // Get the "second" watched literal (the one not equal to "wlit").
	  uint32_t wl(clause[0]); 
	  wl = wl ^ clause[1];
	  wl = wl ^ lit;
		      
	  // Current clause satisfied by "wl"?
	  if (m_assignment[wl])
		{
		  // Update the blocking literal.
		  watch.setBlockingLiteral(wl);
		}
	  else
		{
		  // Initialization ("pos" is set to 2, since there is no need 
		  // to check the current watched literals again).
		  uint32_t clausesize(m_ca[watch.getClause()].length());
			  
		  // Try to find a new watched literal within the remainder of "cLits".
		  // This loop assumes that "m_assignment[0]" and "m_assignment[1]" 
		  // are both set to FALSE.

		  uint32_t pos(2);
		  while( pos < clausesize && m_assignment[clause[pos]^1] )
			{ ++pos; }
					  
		  if(pos != clausesize)
			{
			  // Found new watch
			  // Get the literal checked last.
			  uint32_t newlit(clause[pos]); 
			      
			  // Update "cLits":
			  clause[0]   = wl;
			  clause[1]   = newlit;
			  clause[pos] = lit;

			  // Update "m_watches" for both "lit" and "newlit".
			  m_watches[newlit].push_back(watch);
			  m_watches[lit][wpos--] = m_watches[lit][--size];
			  m_watches[lit].pop_back();
			  return true;
			}
		
		  // At this point, we either have an implication or a conflict.
		      	      
		  // Conflict?
		  if (m_assignment[wl ^ 1])
			{ 
			  m_conflict = Reason(watch.getClause(), false);
			  //std::cout << "n-nary conflict with" << std::endl;
			  //m_conflict.print(m_ca);
			  return false;
			}
		  else
			{
			  // Push "wl" as an implication onto the decision stack.
			  addImplication(wl, watch.getClause());
			}
		}
	  return true;
	}

	// Performs "Boolean Constraint Propagation". In case of a conflict, the reason
	// will be updated and "true" returned, otherwise "false" will be returned
    bool deduce ( void )  
	{
	  // Increment "m_bcps".
      ++m_statistics.bcps;

	  m_conflict.clearReason();

      // Process all assignments not checked so far. 
      while (m_dsImplIndex != m_dsEndIndex)
		{
		  // Get the next assignment.
		  uint32_t wlit(m_decisionStack[m_dsImplIndex++] ^ 1);

		  // "wlit" has to be assigned, since it's part of the decision stack.
		  assert(m_assignment[wlit] || m_assignment[wlit ^ 1]); 

		  // Initialization.
		  std::vector<Watcher>& watches(m_watches[wlit]);

		  uint32_t size((uint32_t)watches.size()); 

		  // Increment "m_basicOps".
		  m_basicOps += size; 
 
		  // Process all clauses in which "wlit" currently serves as a watched literal.
		  for (uint32_t w = 0; w < size; ++w)
			{
			  if( m_assignment[watches[w].getSecondLit()] )
				{ continue; }

			  if( watches[w].isBinary() )
				{
				  if ( !deduceBinary(watches[w], wlit) )
					{ 
					  assert(m_conflict.isBinary());
					  return false; 
					}
				  else
					{ assert(m_conflict.noReason()); continue; }
				}
			  if( watches[w].isTernary() )
				{
				  if( !deduceTernary(watches[w], wlit) )
					{ 
					  assert(m_conflict.isTernary());
					  return false; 
					}

				  else
					{ assert(m_conflict.noReason()); continue; }
				}
			  if( watches[w].isClause() )
				{
				  if ( !deduceNary(w, size, wlit) )
				  	{ 
				  	  assert(m_conflict.isClause());
				  	  return false;
				  	}
				  else
				  	{ assert(m_conflict.noReason()); continue; }
				}
			}
		}

      // Everything went fine.
      return true; 
	}

    // Performs conflict analysis according to the 1UIP scheme and backtracks afterwards.
    void analyze ( void )
    {
      // Increment "m_conflicts".
      ++m_statistics.totalConflicts;

      // Everything OK wrt. "m_reason"?
      assert(m_conflict.hasReason());

      // Update "m_incVarActivity".
      m_incVarActivity *= m_decayFactor;
 
      // Initialization.
      uint32_t elements(0);
      uint32_t pos(m_dsEndIndex - 1); 
      uint32_t uip(0);
	  uint32_t size(1);
	  std::fill(m_seen.begin(), m_seen.end(), false);

	  // Set Reason
	  ReasonComplete cc(m_conflict, m_conflictLiteral, m_ca);

      // Perform conflict analysis according to the 1UIP scheme.
      do
		{
		  // Increment "m_basicOps".
		  ++m_basicOps; 

		  // Analyze the literals of the current conflicting clause.
		  uint32_t reasonsize(cc.size());
		  for( uint32_t cpos = 0; cpos < reasonsize; ++cpos )
			{
			  // Get the index of "clit".
			  uint32_t index(cc[cpos] >> 1); 

			  // "clit" not checked so far and not assigned on decision level 0? 
			  // Checking the decision level on which a particular variable has been 
			  // assigned, requires that assumptions are stored on decision levels 
			  // greater 0. Otherwise we run into problems in the incremental mode. 
			  if (!m_seen[index] && m_level[index] > 0)
				{
				  // Update "seen".
				  m_seen[index] = true;

				  // Increase the activity of the variable corresponding to "clit".
				  increaseActivity(index);

				  // Has "clit" been assigned on the current decision level?
				  if (m_level[index] == m_decisionLevel)
					{ 
					  ++elements; 
					}
				  else
					{ 
					  m_conflictClause[size++] = cc[cpos]; 
					}
				}
			}

		  // Determine the next clause to be processed. 
		  while (!m_seen[m_decisionStack[pos] >> 1]) 
			{ --pos; }

		  uip = m_decisionStack[pos];

		  // Update the status variables.

		  Reason& r(m_forcing[uip>>1]);

		  cc = ReasonComplete(r, uip, m_ca);
		  // Either we reached the last element or there has to be a reason for "uip"
		  assert(elements == 1 || !(m_forcing[uip >> 1].noReason()));
		  --pos;
		  --elements;

		}
      while (elements > 0);

      // Flip the sign of the UIP.
      uip = uip ^ 1;

	  m_conflictClause[0] = uip;
  
      // Do we have an unit clause?
      if (size == 1)
		{
		  // Update some of our statistics related variables. 
		  ++m_statistics.globalLBD; 
		  ++m_statistics.localLBD; 
		  ++m_statistics.learnedLength;
		  ++m_statistics.totalLearntUnitClauses;
		  m_statistics.DLclearedCA += m_decisionLevel; 
		  m_statistics.VarsUnassignedCA += m_dsEndIndex - m_dl2ds[1]; 

		  // Backtrack to decision level 0.
		  backtrack(0);

		  //std::cout << "new unit: " << Lit(uip) << std::endl;

		  // Add the UIP as a "fake" implication to the decision stack.
		  addImplication(uip);

		  return;
		}

	  // Update lbd value and backtrack level
      uint32_t lv(0);
      uint32_t at(1);
      uint32_t lbd(1);
	  std::fill(m_touched.begin(), m_touched.end(), false);
      uint32_t swapLit(m_conflictClause[1]);

      // Perform a simple conflict clause minimization step. See also "Towards Understanding 
      // and Harnessing the Potential of Clause Learning" by Beame, Kautz, and Sabharwal.
	  for (uint32_t l = 1; l < size; ++l)
		{
		  // Get the next literal of "conflictClause".
		  uint32_t lit(m_conflictClause[l]); 
		  uint32_t index(lit>>1);
		  
		  // Do we talk about an implication?
		  if ( (m_forcing[index].hasReason() ) )
			{
			  ReasonComplete rc(m_forcing[index], lit, m_ca);

			  uint32_t rcsize(rc.size());
			  uint32_t rcpos(0);
			  for( ; rcpos != rcsize; ++rcpos )
				{
				  uint32_t curIndex( rc[rcpos]>>1 );
				  if ( !m_seen[curIndex] && m_level[curIndex] > 0 )
					{ break; }
				}

			  // Is it safe to remove "lit"?
			  if( rcpos == rcsize )
				{
				  --size; 
				  m_conflictClause[l] = m_conflictClause[size];
				  // update swaplit
				  if ( l == 1 )
					{ swapLit = m_conflictClause[1]; }
				  --l; 
				  continue;
				}
			}

		  // Do we have to update the backtrack level?
		  if (m_level[index] > lv)
			{ 
			  lv = m_level[index]; 
			  at = l;
			}

		  // Do we have to update the "Literals Blocks Distance"?
		  if (!m_touched[m_level[index]])
			{ 
			  m_touched[m_level[index]] = true; 
			  ++lbd; 
			}
		}
	  
      // If we now removed all literals (except uip), we've got a problem.
      assert(size > 1);
	  
      // Update "m_learnedClauses".
      ++m_statistics.learnedClauses;

      // Do we have a binary clause?
      if (size == 2)
		{	  
		  // Update some of our statistics related variables. 
		  m_statistics.globalLBD += 2; 
		  m_statistics.localLBD += 2; 
		  m_statistics.learnedLength +=2;
		  m_statistics.totalLearnedLength +=2;
		  m_statistics.DLclearedCA += m_decisionLevel - m_level[m_conflictClause[1] >> 1]; 
		  m_statistics.VarsUnassignedCA += m_dsEndIndex - m_dl2ds[m_level[m_conflictClause[1] >> 1] + 1]; 
		  ++m_statistics.totalLearntBinaryClauses; 

		  // Update "m_watches".
		  m_watches[m_conflictClause[1]].push_back( Watcher(uip, true) );
		  m_watches[uip].push_back( Watcher(m_conflictClause[1], true) ); 

		  // Backtrack to the decision level on which "conflictClause[1]" has been assigned.
		  backtrack(m_level[m_conflictClause[1] >> 1]); 

		  // Push the UIP as an implication forced by a binary clause onto the decision stack.
		  addBinaryImplication(uip, m_conflictClause[1]); 

		  return; 
		}
	  else if ( size == 3 )
		{
		  ++m_statistics.totalLearntTernaryClauses;
		}

      // Swap the literal on the second position of "cptr" for the one on 
      // position "at" to have the "correct" pair of watched literals.
      m_conflictClause[1]  = m_conflictClause[at];
      m_conflictClause[at] = swapLit;

      // Update statistics
      m_statistics.globalLBD += lbd; 
      m_statistics.localLBD += lbd; 
      m_statistics.learnedLength += size; 
      m_statistics.totalLearnedLength += size; 
      m_statistics.DLclearedCA += m_decisionLevel - lv; 
	  m_statistics.VarsUnassignedCA += m_dsEndIndex - m_dl2ds[lv + 1]; 

      // Backtrack to decision level "lv".
      backtrack(lv);

      // Create a new clause.
	  CRef cr(m_ca.alloc(m_conflictClause, lbd, size));
	  
      // Add a new clause to the clause database.
	  attachClause(cr);

      // Add the UIP as an implication to the decision stack.
      addImplication(uip, cr);
    }
		
    // Backtracks to decision level "bL". 
    void backtrack (uint32_t bL)
    {
      // "bL" has to be less than the current decision level.
      assert(bL < m_decisionLevel);

      // Update "m_avgDL".
      m_statistics.DL += m_decisionLevel; 

      // Initialization.
      uint32_t stopper(m_dl2ds[bL + 1]);

      // Increment "m_basicOps".
      m_basicOps += m_dsEndIndex - stopper; 
   
      // Undo all variable assignments on decision levels higher than "bL".
      // This loop assumes that we have a dummy assignment at the first 
      // position of the decision stack, which has been assigned on decision level 0. 
      do
		{
		  // Decrement "m_dsEndIndex".
		  --m_dsEndIndex;

		  // Get the next assignment.
		  uint32_t lit(m_decisionStack[m_dsEndIndex]); 

		  // Cache the polarity of the current assignment.
		  m_polarity[lit >> 1] = (lit & 1); 
	  
		  // Undo the current assignment.
		  m_assignment[lit] = false;

		  // Clear forcing clause (needed for incremental mode)
		  m_forcing[lit>>1].clearReason();
	  
		  // Update "m_varOrder".
		  if (!m_varOrder[m_varGroup[lit >> 1]]->inHeap(lit >> 1))
			{
			  m_varOrder[m_varGroup[lit >> 1]]->insert(lit >> 1); 
			}
		}
      while (stopper != m_dsEndIndex); 

      // Consistency check.
      assert(stopper == m_dsEndIndex); 

      // Update "m_decisionLevel".
      m_decisionLevel = bL; 
   
      // Update "m_dsImplIndex".
      m_dsImplIndex = m_dsEndIndex;
    }


    // Increases the activity of variable "var".
    void increaseActivity(uint32_t var, bool checkheap = true)
    {
      // "var" has to be less or equal "m_variables".
      assert(var <= m_variables); 

      // Increase "var's" activity.
      m_activity[var] += m_incVarActivity; 

      // Update the position of "var" within the "m_varOrder".
      if (checkheap && m_varOrder[m_varGroup[var]]->inHeap(var))
		{ m_varOrder[m_varGroup[var]]->update(var); } 

      // Do we have to "normalize" the variables' activities?
      if (m_activity[var] > 1e100)
		{
		  // Increment "m_basicOps".
		  m_basicOps += m_variables; 

		  // Divide all activities by 1e100.
		  for (uint32_t v = 1; v <= m_variables; ++v)
			{ m_activity[v] *= 1e-100; }
	  
		  // Update "m_incVarActivity".
		  m_incVarActivity *= 1e-100;
		}
    }


	void estimateProgress (void) 
	{
	  m_statistics.progress = 0.0; 
	  double div(1.0); 
	  for (uint32_t l = 0; l <= m_decisionLevel; ++l)
		{
		  uint32_t end(m_dsEndIndex); 
		  if (l < m_decisionLevel)
			{ end = m_dl2ds[l + 1]; }
		  if (l != 0)
			{ div *= m_variables + 1; }
		  m_statistics.progress += ((double) end - m_dl2ds[l]) / div; 
		}
	}
	      
    // Returns the i.th element of the "Luby sequence". See "Optimal Speedup 
    // of Las Vegas Algorithms" (Luby, Sinclair, and Zuckerman) for more details.
    uint32_t luby (uint32_t i) const
    {
      // By definition, "i" has to be greater than 0.
      assert(i > 0);
      
      // Variables.
      uint32_t p(2); 
      uint32_t iP1(i + 1); 
      
      // Calculate the i.th element of the Luby sequence.
      while (p < iP1) 
		{ p = p << 1; }
      
      // Return the i.th element.
      if (p == iP1)
		{ return (p >> 1); }
      return luby(i - (p >> 1) + 1);
    }

	// Lifting methods

	std::vector< uint32_t > analyzeLifting (uint32_t* cc );

	// lifts a solution, given by the variables in "assumptions"
	// liftingmodi:
	// 0001 : conflict driven
	// 0010 : brute force driven
	// 0011 : combine 1+2
	// 01xx : add all assumptions at once (only for conflict driven approach)
	// note: needs a negated property
	// the formula with negated property must be UNSAT, with non-negated property SAT
	// Returns lifted solution
	std::vector< uint32_t > solveLifting( std::vector<uint32_t>& assumptions, uint32_t liftingmode, uint32_t sortmode );

	// Returns:
	// "-1" if variable is assigned to false
	// " 1" if variable is assigned to true
	// " 0" if variable is unassigned
	int isAssigned( uint32_t lit ) const;

	void printClause( Clause* clause, bool assignment ) const;

	// Build watchers 
	void attachClause(CRef cr, bool addToDatabase = true)
	{
	  //std::cout << __func__ << " cref: " << cr << std::endl;
	  const Clause& clause(m_ca[cr]);

	  // Special storage for ternary clauses 
	  if( m_useTernary && clause.length() == 3 )
		{

		  m_watches[clause[0]].push_back(Watcher(clause[1], clause[2],TERNARY));
		  m_watches[clause[1]].push_back(Watcher(clause[0], clause[2],TERNARY));
		  m_watches[clause[2]].push_back(Watcher(clause[0], clause[1],TERNARY));

		  /*
			  std::cout << Lit(clause[0]) << ": ";
			  m_watches[clause[0]].back().print(m_ca);		 
			  std::cout << Lit(clause[1]) << ": ";
			  m_watches[clause[1]].back().print(m_ca);
			  std::cout << Lit(clause[2]) << ": ";
			  m_watches[clause[2]].back().print(m_ca);
		  */
		}
	  else
		{
		  m_watches[clause[0]].push_back(Watcher(cr,clause[1],NNARY));
		  m_watches[clause[1]].push_back(Watcher(cr,clause[0],NNARY));
		}

	  if( addToDatabase )
		{
		  // Finally, add the new clause to the clause database.
		  m_clauseDatabase.push_back(cr);
		}

	  /*
	  uint32_t theLit = (127<<1)^1;
	  std::cout << "watches of " << Lit(theLit) << " after attach: " << std::endl;
	  for( uint32_t foo = 0; foo != m_watches[theLit].size(); ++foo)
		{
		  m_watches[theLit][foo].print(m_ca);
		}
	  std::cout << std::endl;
	  */
	}

	// Garbage collection
	
	// relocate all clauses to a new allocator "to"
	void relocAll(ClauseAllocator& to)
	{
	  // All watchers:
	  //
	  for (uint32_t v = 1; v <= m_variables; ++v)
		{
		  for (uint32_t s = 0; s < 2; ++s)
			{
			  uint32_t literal = (v<<1)+s;
			  //std::cout << "relocating watchers of " << Lit(literal) << std::endl;
			  std::vector< Watcher >& watches(m_watches[literal]);
			  size_t wsize(watches.size());
			  for (size_t j = 0; j < wsize; ++j)
				{
				  if( watches[j].isClause() )
					{
					  CRef ref(watches[j].getClause());
					  m_ca.reloc(ref, to);
					  watches[j].setClause(ref);
					}
				}
			}
        }
	
	  // All reasons:
	  //
	  for (uint32_t i = 1; i < m_dsEndIndex; ++i)
		{
		  uint32_t index(m_decisionStack[i]>>1);
		  Reason& reason(m_forcing[index]);
		  if ( reason.isClause() )
			{
			  CRef ref(reason.getClause());
			  m_ca.reloc(ref, to);
			  reason.setClause(ref);
			}
		}
	  
	  // All clauses:
	  //
	  size_t size(m_clauseDatabase.size());
	  for (uint32_t i = 0; i < size; ++i)
	  {
        m_ca.reloc(m_clauseDatabase[i], to);
	  }
	}
	
	void checkGarbage(void)
	{
	  // collect garbage if 20% of the memory is wasted
	  if( m_ca.wasted() > (m_ca.size() * 0.2) )
		{
		  // Initialize the next region to a size corresponding to the estimated utilization degree. This
		  // is not precise but should avoid some unnecessary reallocations for the new region:
		  ClauseAllocator to(m_ca.size() - m_ca.wasted());

		  // reallocate all clauses to new allocator
		  relocAll(to);
		  if (m_control->getVerbosity() >= 2)
			{
			  std::cout << "c Garbage collection: " << m_ca.size()*ClauseAllocator::Unit_Size << " bytes => " << to.size()*ClauseAllocator::Unit_Size << " bytes\n";
			}

		  // move "to" the core allocator "m_ca" 
		  to.moveTo(m_ca);
		}
	}

    // Copy constructor.
    Core (const Core&);

    // Assignment operator.
    Core& operator = (const Core&);

    // Each core has its own unique ID.
    uint32_t m_id; 

    // Each core has a pointer to the "Control" object.
    Control* m_control;

	// The clause allocator
    ClauseAllocator m_ca;

    // A flag indicating whether we have been able to deduce the empty clause.
    // In particular important for the incremental mode to distinguish between
    // "unsatisfiable" and "unsatisfiable under assumptions". 
    bool m_emptyClause;

	// The (extended) result of the last solver call
	uint32_t m_result; 

    // The current number of variables.
    uint32_t m_variables; 

	// The reserved size of the variable related data structures
	uint32_t m_capacity;

	Statistics m_statistics;

    // The (partial) variable assignment.
    std::vector<unsigned char> m_assignment;

    // The decision level on which a particular literal has been assigned.
    std::vector<uint32_t> m_level; 

    // For each variable we store its activity.
    std::vector<double> m_activity;  

    // For each variable we cache its "last" polarity.
    std::vector<unsigned char> m_polarity;

    // For each variable we store whether it is an implication or a decision.
    std::vector<Reason> m_forcing;
	// Temporal storage for last conflict reason
	Reason m_conflict;

    // For each literal we store a vector to represent in which binary & non-binary
    // clauses a particular literal currently serves as a watched literal.
    std::vector<std::vector< Watcher > > m_watches;

    // Some variable activity related variables.
	std::vector< VarHeap<double>* > m_varOrder; 
    std::vector<uint32_t> m_varGroup; 
	uint32_t m_noOfVarGroups;
    double m_incVarActivity;

    // Some decision stack related variables.
    uint32_t m_decisionLevel; 
    std::vector<uint32_t> m_decisionStack;
    std::vector<uint32_t> m_dl2ds;
    uint32_t m_dsEndIndex;
    uint32_t m_dsImplIndex;

    // Some decision strategy related variables. 
	std::vector< uint32_t > m_modeDS; 
	std::vector< uint32_t > m_modeDSforvariables; 

    // Some "Lazy Hyper Binary Resolution" related variables.
    bool m_lhbrEnable; 

    // Some conflict analysis related variables.
	std::vector<unsigned char> m_seen;
	std::vector<unsigned char> m_touched;
	uint32_t m_conflictLiteral; 
	std::vector<uint32_t> m_conflictClause;
    double m_decayFactor; 

    // Some restart related variables.
    uint32_t m_lubyShift; 
	std::vector< bool > m_decVarSign;
    restartstrategy m_restartStrategy; 

	simplifystrategy m_simplifyStrategy;
 
    // Some more status variables.
    unsigned long m_basicOps; 

    // The satisfying variable assignment (in case the CNF formula is 
    // satisfiable and has been solved beforehand; otherwise "m_model" 
    // might contain invalid data).
    std::vector<uint32_t> m_model;
	
    // The clause database.
    std::vector<CRef> m_clauseDatabase;

	// Use special treatment for ternary clauses
	bool m_useTernary;

	SolverState m_solverState; 

	friend class Preprocessor;
	Preprocessor* m_preprocessor;

	bool m_dopreprocessing;
	bool m_doinprocessing;

	// Deleted variables
	std::vector< unsigned char > m_deleted;
  };
}

#endif
