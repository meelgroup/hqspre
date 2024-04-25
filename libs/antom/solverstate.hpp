#ifndef SOLVERSTATE_HPP
#define SOLVERSTATE_HPP

/********************************************************************************************
solverstate.hpp -- Copyright (c) 2016, Tobias Schubert, Sven Reimer

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

#include "helper.hpp"
#include "statistics.hpp"
#include "watcher.hpp"
#include "reason.hpp"

namespace antom {

  // An union to represent the forcing clause of an implication.
  // It's either a pointer to the clause's literals or the second 
  // literal of a binary clause (shifted by 1 with the LSB set to 1).
  // Assumes that the LSB of all pointers are always 0. 
  union forcingType { uint32_t* ptr; uint32_t lit; };

  // A struct to be able to store the current state of the SAT solving core. 
  struct SolverState
  {
	Statistics stats;
	unsigned long basicOps; 
	uint32_t variables; 
	uint32_t decisionLevel;   
	uint32_t dsEndIndex;
	uint32_t dsImplIndex;
	std::vector<uint32_t> modeDS; 
	std::vector<uint32_t> modeDSforvariables; 
	uint32_t lubyShift; 
	restartstrategy restartStrategy; 
	simplifystrategy simplifyStrategy; 
	double incVarActivity;
	double decayFactor; 
	bool emptyClause;
	bool lhbrEnable; 
	std::vector<bool> decVarSign;
	std::vector<unsigned char> assignment;
	std::vector<unsigned char> polarity;
	std::vector<uint32_t> model;
	std::vector<uint32_t> level; 
	std::vector<uint32_t> decisionStack;
	std::vector<uint32_t> dl2ds;   
	std::vector<uint32_t> varGroup;    
	std::vector<double> activity;  
	std::vector<std::vector<Watcher> > watches;
	std::vector<Reason> forcing;
	ClauseAllocator ca;
	std::vector<CRef> clauseDatabase;

	SolverState(void):
	  basicOps(0), 
	  variables(0),
	  decisionLevel(0),
	  dsEndIndex(0),
	  dsImplIndex(0),
	  modeDS(),
	  modeDSforvariables(),
	  lubyShift(0),
	  restartStrategy(LUBY),
	  simplifyStrategy(ANTOM),
	  incVarActivity(0.0),
	  decayFactor(0.0),
	  emptyClause(false),
	  lhbrEnable(false),
	  decVarSign(),
	  assignment(0),
	  polarity(0),
	  model(0),
	  level(0),
	  decisionStack(0),
	  dl2ds(0),
	  varGroup(0),
	  activity(0),
	  watches(),
	  forcing(),
	  ca(0),
	  clauseDatabase()
	{}
	  };
  }

#include "core.hpp"
#include "preprocessor.hpp"

namespace antom {

  // Deletes the status of the SAT solving core saved before by "saveStatus()". 
  void inline Core::deleteStatus (void)
  {
	for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
	  { m_varOrder[v]->deleteStatus(); }

	m_solverState.clauseDatabase.clear();
	for (uint32_t v = 1; v <= m_solverState.variables; ++v)
	  {
		std::vector<Watcher>().swap(m_solverState.watches[v << 1]); 
		std::vector<Watcher>().swap(m_solverState.watches[(v << 1) ^ 1]); 
	  }
	std::vector<uint32_t>().swap(m_solverState.level);  
	std::vector<double>().swap(m_solverState.activity); 
	std::vector<unsigned char>().swap(m_solverState.polarity);
	std::vector<unsigned char>().swap(m_solverState.assignment);    
	std::vector<uint32_t>().swap(m_solverState.model);
	std::vector<uint32_t>().swap(m_solverState.decisionStack);
	std::vector<uint32_t>().swap(m_solverState.dl2ds);   
	std::vector<uint32_t>().swap(m_solverState.varGroup);    
	std::vector<Reason>().swap(m_solverState.forcing);
  }

  // Saves the current status of the SAT solving core. 
  // The following variables/vectors are not stored:
  // -- "m_control",
  // -- "m_id",
  // -- "m_progress", 
  // -- "m_binaryConflictingClause". 
  void inline Core::saveStatus (void)
  {
	// First of all, reset what we have saved so far (wrt. to "watches" and "clauseDatabase"). 

	m_solverState.clauseDatabase.clear();
	for (uint32_t v = 1; v <= m_solverState.variables; ++v)
	  {
		std::vector<Watcher>().swap(m_solverState.watches[v << 1]); 
		std::vector<Watcher>().swap(m_solverState.watches[(v << 1) ^ 1]); 
	  }

	// Now, simplify the clause database.
	simplify(false); 

	// Store the variable ordering.
	for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
	  { 
		m_varOrder[v]->saveStatus(); 
		m_solverState.modeDS[v] = m_modeDS[v];
		m_solverState.decVarSign[v] = m_decVarSign[v];
	  }

	// Store our status variables/flags.
	m_solverState.stats                = m_statistics;
	m_solverState.basicOps             = m_basicOps;
	m_solverState.decisionLevel        = m_decisionLevel;
	m_solverState.dsEndIndex           = m_dsEndIndex;
	m_solverState.dsImplIndex          = m_dsImplIndex;
	m_solverState.modeDSforvariables   = m_modeDSforvariables;
	m_solverState.lubyShift            = m_lubyShift;
	m_solverState.restartStrategy      = m_restartStrategy;
	m_solverState.simplifyStrategy     = m_simplifyStrategy;
	m_solverState.incVarActivity       = m_incVarActivity;
	m_solverState.decayFactor          = m_decayFactor;
	m_solverState.emptyClause          = m_emptyClause;
	m_solverState.lhbrEnable           = m_lhbrEnable;

	// Initialization.
	uint32_t max((m_variables << 1) + 2);

	// Resize the various vectors. 
	m_solverState.level.resize(m_variables + 1, 0); 
	m_solverState.activity.resize(m_variables + 1, 0.0); 
	m_solverState.polarity.resize(m_variables + 1, true); 
	m_solverState.model.resize(m_variables + 1, 0); 
	m_solverState.decisionStack.resize(m_variables + 1, 0); 
	m_solverState.dl2ds.resize(m_variables + 1, 1); 
	m_solverState.varGroup.resize(m_variables + 1, 1); 
	m_solverState.forcing.resize(m_variables + 1); 
	m_solverState.assignment.resize(max, false);
	m_solverState.watches.resize(max); 

	// Store all vectors 1/2. 
	for (uint32_t v = 1; v <= m_variables; ++v)
	  {
		m_solverState.level[v]         = m_level[v]; 
		m_solverState.activity[v]      = m_activity[v]; 
		m_solverState.polarity[v]      = m_polarity[v]; 
		m_solverState.model[v]         = m_model[v]; 
		m_solverState.decisionStack[v] = m_decisionStack[v];
		m_solverState.dl2ds[v]         = m_dl2ds[v]; 
		m_solverState.varGroup[v]      = m_varGroup[v]; 
		m_solverState.forcing[v]       = m_forcing[v]; 
	  }

	// Store all vectors 2/2.
	for (uint32_t p = 2; p < max; ++p)
	  { 
		uint32_t w(0); 
		m_solverState.assignment[p] = m_assignment[p]; 
		std::vector<Watcher>& watches(m_watches[p]); 
		while (w < watches.size() && watches[w].isBinary())
		  { m_solverState.watches[p].push_back(watches[w]); ++w; }
	  }

	m_solverState.ca.allocRegion(m_ca.size());
	// copy Core region to 
	m_ca.copyTo(m_solverState.ca);
	size_t size(m_clauseDatabase.size());
	for (size_t c = 0; c < size; ++c)
	  {
		m_solverState.clauseDatabase.push_back(m_clauseDatabase[c]);
	  }
  }

  // Restores the status of the SAT solving core saved before by "saveStatus()".
  void inline Core::restoreStatus (void)
  {
	m_clauseDatabase.clear();      
	for (uint32_t v = 1; v <= m_variables; ++v)
	  {
		std::vector<Watcher>().swap(m_watches[v << 1]); 
		std::vector<Watcher>().swap(m_watches[(v << 1) ^ 1]); 
	  }

	// Restore the variable ordering.
	for( uint32_t v = 0; v != m_noOfVarGroups; ++v )
	  { 
		m_varOrder[v]->restoreStatus();
		m_modeDS[v] = m_solverState.modeDS[v];
		m_decVarSign[v] = m_solverState.decVarSign[v];
	  }

	m_statistics           = m_solverState.stats;
	// Restore our status variables/flags.
	m_basicOps             = m_solverState.basicOps;
	m_variables            = m_solverState.variables;
	m_decisionLevel        = m_solverState.decisionLevel;
	m_dsEndIndex           = m_solverState.dsEndIndex;
	m_dsImplIndex          = m_solverState.dsImplIndex;
	m_modeDSforvariables   = m_solverState.modeDSforvariables;
	m_lubyShift            = m_solverState.lubyShift;
	m_restartStrategy      = m_solverState.restartStrategy;
	m_simplifyStrategy     = m_solverState.simplifyStrategy;
	m_incVarActivity       = m_solverState.incVarActivity;
	m_decayFactor          = m_solverState.decayFactor;
	m_emptyClause          = m_solverState.emptyClause;
	m_lhbrEnable           = m_solverState.lhbrEnable;

	// Initialization.
	uint32_t max((m_variables << 1) + 2);

	// Resize the various vectors. 
	m_level.resize(m_variables + 1, 0); 
	m_activity.resize(m_variables + 1, 0.0); 
	m_polarity.resize(m_variables + 1, true); 
	m_model.resize(m_variables + 1, 0); 
	m_decisionStack.resize(m_variables + 1, 0); 
	m_dl2ds.resize(m_variables + 1, 1); 
	m_varGroup.resize(m_variables + 1, 0); 
	m_forcing.resize(m_variables + 1); 
	m_assignment.resize(max, false);
	m_watches.resize(max); 

	// Restore all vectors 1/2. 
	for (uint32_t v = 1; v <= m_variables; ++v)
	  {
		m_level[v]         = m_solverState.level[v]; 
		m_activity[v]      = m_solverState.activity[v]; 
		m_polarity[v]      = m_solverState.polarity[v]; 
		m_model[v]         = m_solverState.model[v]; 
		m_decisionStack[v] = m_solverState.decisionStack[v];
		m_dl2ds[v]         = m_solverState.dl2ds[v]; 
		m_varGroup[v]      = m_solverState.varGroup[v]; 
		m_forcing[v]       = m_solverState.forcing[v]; 
	  }

	// Store all vectors 2/2.
	for (uint32_t p = 2; p < max; ++p)
	  { 
		m_assignment[p] = m_solverState.assignment[p]; 
		std::vector<Watcher>& watches(m_solverState.watches[p]); 
		size_t wSize(watches.size());
		for (size_t w = 0; w < wSize; ++w)
		  { m_watches[p].push_back(watches[w]); }
	  }

	// Restore the clause database.
	uint32_t size = (uint32_t)m_solverState.clauseDatabase.size();
	for (uint32_t c = 0; c < size; ++c)
	  {
		m_ca.allocRegion(m_solverState.ca.size());
		m_solverState.ca.copyTo(m_ca);
		m_clauseDatabase.push_back(m_solverState.clauseDatabase[c]);
	  }
  }

  // Resets the SAT solving core. The following status flags/variables remain untouched:
  // -- The SAT solving threads unique ID number: "m_id".
  // -- The pointer to the "Control" object: "m_control".
  // -- The number of variables for which memory has been reserved: "m_variables".
  void inline Core::reset (void)
  {
	std::cout << __func__ << std::endl;
	// Reset the clause database.
	m_ca.reset();
	m_clauseDatabase.clear();


	// Reset the variable order.
	for (uint32_t v = 0; v != m_noOfVarGroups; ++v )
	  { 
		m_varOrder[v]->clear(); 
		m_modeDS[v] = 0;
		m_decVarSign[0] = false;
	  }

	// Reset all variable related data structures.
	for (uint32_t v = 1; v <= m_variables; ++v)
	  {
		uint32_t pLit(v << 1);
		uint32_t nLit((v << 1) ^ 1); 
		m_assignment[pLit] = false;
		m_assignment[nLit] = false;
		m_level[v]         = 0;
		m_dl2ds[v]         = 1; 
		m_activity[v]      = 0.0; 
		m_polarity[v]      = true; 
		m_varGroup[v]      = 0; 
		m_forcing[v].clearReason();
		std::vector<Watcher>().swap(m_watches[pLit]); 
		std::vector<Watcher>().swap(m_watches[nLit]); 
	  }

	// Reset some more status flags.
	m_emptyClause          = false;  
	m_statistics.resetCore();
	m_statistics.resetPrepro();
	m_incVarActivity       = 1.0;
	m_decisionLevel        = 0;
	m_dsEndIndex           = 1;
	m_dsImplIndex          = 1;
	m_lhbrEnable           = false;  
	m_lubyShift            = 8; 
	m_decayFactor          = 1.05;
	m_basicOps             = 0; 
	// reset also "m_variables", the capacity is stored in m_capacity
	m_variables            = 0;
  }
}

#endif
