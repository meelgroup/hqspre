 
/********************************************************************************************
antom.cpp -- Copyright (c) 2016, Tobias Schubert, Sven Reimer

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


// Include antom related headers.
#include "antom.hpp"
#include "solverstate.hpp"
#include "core.hpp"
#include "preprocessor.hpp"
#include "control.hpp"

#include <sys/resource.h>

namespace antom
{
  // Some (hopefully) promising configurations. 
  const uint32_t configs(10); 
  const uint32_t c_decisionStrategy[configs] = {     0,     1,     0,     1,     2,     1,     2,     3,     0,    1 };
  const restartstrategy c_restartStrategy[configs]  = { LUBY, LUBY,  GLUCOSE, GLUCOSE, LUBY, LUBY, GLUCOSE, GLUCOSE, GLUCOSE, LUBY };
  const uint32_t c_unitFactor[configs]       = {     8,     5,     8,     5,     6,     8,     6,    10,    12,    9 }; 
  const double c_decayFactor[configs]            = {  1.05,  1.10,  1.05,  1.10,  1.20,  1.05,  1.50,  1.30,  1.15, 1.03 }; 
  const bool c_lhbr[configs]                     = {  true,  true,  true,  true, false, false,  true, false, false, true };

  // Constructor. 
  Antom::Antom (uint32_t threads) : 
    m_threads(threads),
    m_control(NULL),
    m_core(threads),
    m_preprocessor(threads),
	m_dopreprocessing(false),
	m_softclauses(),
	m_partialTriggerParts(),
	m_currentTriggerParts(),
	m_splittedWidth(32),
	m_maxWidth(0),
	m_maxParts(0),
	m_horizontalwidth(4),
	m_bypassGrid(0),
	m_horizontalbypasses(0),
	m_verticalbypasses(0),
	m_sortsoftclauses(0),
	m_comparator(0),
	m_skipped(0),
	m_setCSC(0),
	m_doskipping(false),
	m_setTrigger(false),
	m_incompleteMode(false),
	m_networktype(0),
	m_triggervar(0),
	m_low(0),
	m_high(0),
	m_sortvarorder(0),
    m_sID(0),
    m_result(threads),
	m_lastIndex(0),
	m_maxInprocess(false),
	m_stacksize(0),
	m_globalPropertyTrigger(),
	m_softstack(),
	m_triggerlists()
  { 
    // Consistency check.
    assert(m_threads != 0); 

    // Set the number of threads to be used in parallel.
#ifdef PARALLEL
    omp_set_num_threads(m_threads);
#endif

    // Initialize "m_control".
    m_control = new Control(m_threads);

	// Initialize the SAT solving cores.
    for (uint32_t i = 0; i < m_threads; ++i)
      { 
		m_core[i] = new Core(i, m_control); 
		m_preprocessor[i] = new Preprocessor( m_core[i] );
		m_core[i]->setPreprocessor(m_preprocessor[i]);
	  }
	m_globalPropertyTrigger.resize(1,0);
	m_softstack.push_back(0);
	m_triggerlists.resize(1);
  }
 
  // Destructor.
  Antom::~Antom (void) 
  {
    for (uint32_t i = 0; i < m_threads; ++i)
      { 
		delete m_core[i];
		delete m_preprocessor[i];
      }

    delete m_control; 
  }

  // Returns the ID of the thread that was able to solve the CNF.
  uint32_t Antom::solvingThread (void) const { return m_sID; } 

  // Returns the number of used variables
  uint32_t Antom::variables (void) const { return m_core[m_sID]->variables(); }

  // Returns the last used index. Does not necessary meet with "variables()"
  uint32_t Antom::lastIndex(void) const { return m_lastIndex; }
								 
  // Returns the current number of clauses within the clause database. 
  uint32_t Antom::clauses (void) const { return m_core[m_sID]->clauses(); }

  // Returns the current number of literals within the clause database. 
  uint32_t Antom::literals (void) const { return m_core[m_sID]->literals(); }

  // Returns the number of decisions made so far.
  uint32_t Antom::decisions (void) const { return m_core[m_sID]->decisions(); }
  
  // Returns the number of BCP operations performed so far.
  uint32_t Antom::bcps (void) const { return m_core[m_sID]->bcps(); }
  
  // Returns the number of implications found so far. 
  unsigned long Antom::implications (void) const { return m_core[m_sID]->implications(); }

  // Returns the number of conflicts encountered so far.
  uint32_t Antom::conflicts (void) const { return m_core[m_sID]->conflicts(); }
  
  // Returns the number of restarts performed so far.
  uint32_t Antom::restarts (void) const { return m_core[m_sID]->restarts(); }
  
  // Returns the number of database simplifications performed so far.
  uint32_t Antom::simplifications (void) const { return m_core[m_sID]->simplifications(); }

  // Returns the number of binary clauses deduced due to "Lazy Hyper Binary Resolution".
  uint32_t Antom::lhbr (void) const { return m_core[m_sID]->lhbr(); }

  // Returns the number of unit clauses deduced due to conflict analysis.
  uint32_t Antom::learntUnitClauses (void) const { return m_core[m_sID]->learntUnitClauses(); }
  
  // Returns the number of binary clauses deduced due to conflict analysis.
  uint32_t Antom::learntBinaryClauses (void) const { return m_core[m_sID]->learntBinaryClauses(); }
  
  // Returns the number of ternary clauses deduced due to conflict analysis.
  uint32_t Antom::learntTernaryClauses (void) const { return m_core[m_sID]->learntTernaryClauses(); }

  // Returns the number of synchronizations performed so far. 
  uint32_t Antom::synchronizations (void) const { return m_core[m_sID]->synchronizations(); }

  // Returns the number of inprocessings steps during solving main routine
  uint32_t Antom::inprocessings( void ) const { return m_core[m_sID]->inprocessings(); }

  // Returns the average "Literals Blocks Distance" of all conflict clauses deduced so far.
  double Antom::avgLBD (void) const { return m_core[m_sID]->avgLBD(); }

  // Returns the average length of all conflict clauses deduced so far.
  double Antom::avgCCLength (void) const { return m_core[m_sID]->avgCCLength(); }

  // Returns the solver's average decision level before backtracking.
  double Antom::avgDL (void) const { return m_core[m_sID]->avgDL(); }

  // Returns the average number of decision levels cleared during conflict analysis. 
  double Antom::avgDLclearedCA (void) const { return m_core[m_sID]->avgDLclearedCA(); }

  // Returns the average number of variables getting unassigned during conflict analysis. 
  double Antom::avgVarsUnassignedCA (void) const { return m_core[m_sID]->avgVarsUnassignedCA(); }

  // Returns a reference to either the satisfying variable assignment (after calling one of the 
  // "solve()" routines) or the set of currently assigned variables (after calling one of the 
  // two "deduceAssumptions()" routines). Example:
  // model[17] =  0 --> x17 = unassigned
  // model[17] = 35 --> x17 = false 
  // model[17] = 34 --> x17 = true
  // In case neither "solve()/maxSolve()" nor "deduceAssumptions()" has been called beforehand, the 
  // vector contains invalid data. 
  const std::vector<uint32_t>& Antom::model (void) const { return m_core[m_sID]->model(); }

  // Returns a fresh variable index not used so far.
  uint32_t Antom::newVariable (void) 
  {
#ifndef NDEBUG

    // If the threads do not handle the same number of variables, we might have a problem.
    for (uint32_t t = 1; t < m_threads; ++t)
      { assert(m_core[t]->variables() == m_core[t - 1]->variables()); }

#endif

    // Get a new variable index.
    uint32_t index(m_core[m_sID]->variables() + 1); 

    // Set the maximum variable index of all threads to "index". 
	
    for (uint32_t t = 0; t < m_threads; ++t)
      { m_core[t]->setMaxIndex(index); }
    
    // Return "index".
    return index; 
  }

  // Sets the maximum variable index to "max". 
  void Antom::setMaxIndex (uint32_t max) 
  { 
	uint32_t maxindex(max);

	for (uint32_t t = 0; t < m_threads; ++t) 
	  {
		m_core[t]->setMaxIndex(maxindex); 
	  } 
  }

  // Sets the group of variable "var" to "grp". See "setDecisionStrategy()" for more details. 
  void Antom::setVarGroup (uint32_t var, uint32_t grp)
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setVarGroup(var, grp); } }

  void Antom::useTernaryClauses (bool val)
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->useTernaryClauses(val); } }

  // Returns whether variable was already deleted in pre-/in-processing
  bool Antom::isDeleted( uint32_t var ) const 
  { return m_core[m_sID]->isDeleted(var); }

  void Antom::setCPULimit ( double t )
  { m_control->setCPULimit(t); }

  void Antom::setIncrementalMode( uint32_t val ) 
  { m_control->setIncrementalMode(val); }

  // Adds a clause to the clause databases of all threads. Returns FALSE if the CNF formula is unsatisfiable, 
  // otherwise TRUE will be returned. Assumes that the solver is on decision level 0 and that "clause" is not 
  // empty. Furthermore, all literals have to be encoded as follows, having variable indices greater 0:
  //  x3 <--> (3 << 1)     = 6
  // -x3 <--> (3 << 1) + 1 = 7
  // All clauses inserted into the clause database using "addClause()" are assumed to belong to 
  // the original CNF formula (having a "Literals Blocks Distance" of 1). 
  // IN THE MULTI-THREADED MODE, "maxSetIndex()" HAS TO BE CALLED BEFOREHAND.
  bool Antom::addClause (std::vector<uint32_t>& clause, uint32_t lbd) 
  {
    // Add the clause to thread with ID 0 to see whether the CNF is already unsatisfiable or not.
    if (!m_core[0]->addClause(clause, lbd))
      { return false; }

    // Clause already satisfied or a tautological one?
    if (clause.empty())
      { return true; }

    // Now, add the (modified) clause to the clause databases of the remaining threads.
#ifdef PARALLEL
#pragma omp parallel for
    for (uint32_t t = 1; t < m_threads; ++t)
      { m_result[t] = m_core[t]->addClause(clause, lbd); /* assert(m_result[t]); */ }

    for (uint32_t t = 1; t < m_threads; ++t)
      { if (!m_result[t]) { return false; } }
#endif

    // Everything went fine. 
    return true; 
  }

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
  // 3) "maxSetIndex()" HAS BEEN CALLED BEFOREHAND.
  bool Antom::addClause (uint32_t* lits, uint32_t num, uint32_t lbd)
  {
    // Add the current clause to all clauses databases.

#ifdef PARALLEL
#pragma omp parallel for 
    for (uint32_t t = 0; t < m_threads; ++t)
      { m_result[t] = m_core[t]->addClause(lits, num, lbd); }

#ifndef NDEBUG

    // If the results are not all the same, we might have a problem.
    for (uint32_t t = 1; t < m_threads; ++t)
      { assert(m_result[t] == m_result[t - 1]); }

    // Return "m_result[0]".
    return m_result[0]; 
#endif
#else
    // Add the clause to thread with ID 0 to see whether the CNF is already unsatisfiable or not.
    m_result[0] = m_core[0]->addClause(lits, num, lbd);

    return m_result[0]; 
#endif
  }

  // Add unit clause, using literal encoding as in "addClause()"
  bool Antom::addUnit( uint32_t lit )
  {
	std::vector<uint32_t > unitclause;
	unitclause.push_back(lit);
	return addClause(unitclause);
  }

  // Collects data for performing a regression analysis afterwards (--> SATzilla-like SAT solving). 
  // NOTE, THAT "getDataRegressionAnalysis()" CAN BE USED IN SINGLE-THREADED MODE ONLY.
  void Antom::getDataRegressionAnalysis (void)
  {
    // Check the number of threads. 
    assert(m_threads == 1);

    // Initialization.
    std::vector<uint32_t> assumptions; 

    // Save antom's current status.
    m_core[0]->saveStatus();

    // Now, analyse all configurations.
    for (uint32_t c = 0; c < configs; ++c)
      {
		// Output.
		std::cout << "c checking configuration " << c << "..." << std::endl;

		// Initialize current configuration.	
		m_core[0]->setDecisionStrategy(c_decisionStrategy[c], 0); 
		m_core[0]->setRestartStrategy(c_restartStrategy[c]); 
		m_core[0]->setLuby(c_unitFactor[c]); 
		m_core[0]->setDecayFactor(c_decayFactor[c]); 
		m_core[0]->setLHBR(c_lhbr[c]); 

		// Start some SAT solving.
		uint32_t result(m_core[0]->solve(assumptions, 10)); 
	
		// CNF formula not already solved?
		if (result == ANTOM_UNKNOWN)
		  {
			// Get some stats. 
			uint32_t x0(m_core[0]->variables());
			uint32_t x1(m_core[0]->decisions()); 
			uint32_t x2(m_core[0]->bcps()); 
			uint32_t x3(m_core[0]->conflicts());
			uint32_t x4(m_core[0]->restarts()); 
			double x5(m_core[0]->avgLBD()); 
			double x6(m_core[0]->avgCCLength()); 
			double x7(m_core[0]->avgDL()); 
			uint32_t x8(m_core[0]->learntUnitClauses()); 
			uint32_t x9(m_core[0]->learntBinaryClauses()); 
			uint32_t x10(m_core[0]->learntTernaryClauses()); 
			double x11(m_core[0]->avgDLclearedCA()); 
			double x12(m_core[0]->avgVarsUnassignedCA()); 
			uint32_t x13(m_core[0]->clauses()); 
			unsigned long x14(m_core[0]->implications());
			double x15((double) x0 / x13);
			double x16((double) x13 / x0);
			double x17((double) x1 / x3);
			double x18((double) x14 / x1);
			double x19((double) x14 / x3);
			uint32_t x20(m_core[0]->literals()); 
			double x21(m_core[0]->progress()); 
	    
			// Restore status.
			m_core[0]->restoreStatus();

			// Re-initialize the configuration under consideration.
			m_core[0]->setDecisionStrategy(c_decisionStrategy[c], 0); 
			m_core[0]->setRestartStrategy(c_restartStrategy[c]); 
			m_core[0]->setLuby(c_unitFactor[c]); 
			m_core[0]->setDecayFactor(c_decayFactor[c]); 
			m_core[0]->setLHBR(c_lhbr[c]); 

			//Solve the CNF with a higher limit wrt. synchronizations.
			result = m_core[0]->solve(assumptions, 12000); 

			// Output.
			if (result != ANTOM_UNKNOWN)
			  {
				std::cout << "c stats, config " << c << ": " << x0 << " " << x1 << " " << x2 << " " << x3 << " " << x4 
						  << " " << x5 << " " << x6 << " " << x7 << " " << x8 << " " << x9 << " " << x10 << " " << x11 
						  << " " << x12  << " " << x13 << " " << x14 << " " << x15 << " " << x16 << " " << x17 << " "
						  << x18 << " " << x19 << " " << x20 << " " << x21 << " " << m_core[0]->synchronizations() << std::endl; 
			  }

			// Reset "m_control".
			m_control->resetDone();	    

		  }

		// Restore status. 
		m_core[0]->restoreStatus();
      }
  }

  // Dumps cnf into std::cout
  void Antom::dumpCNF( bool printAssignment ) const
  {
	std::cout << "p cnf " << m_core[m_sID]->variables() << " " << m_core[m_sID]->clauses() << std::endl;
	m_core[m_sID]->dumpCNF(printAssignment);
  }

  /* antom core interface */

  void Antom::trivialAssignment (void) const { m_core[m_sID]->trivialAssignment(); }

  // Activates or deactivates "Lazy Hyper Binary Resolution".
  // val = TRUE  --> LHBR enabled (default).
  // val = FALSE --> LHBR disabled.
  void Antom::setLHBR (bool val) { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setLHBR(val); } }

  // Sets the unit factor of both restart strategies -- Luby & glucose-like -- to "val" (default: 8). 
  // The unit factor directly corresponds to the interval between two restart operations. 
  void Antom::setLuby (uint32_t val) { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setLuby(val); } }

  // Sets the decision strategy of group "group" to mode "val". 
  // Currently, there are four modes that differ wrt. the polarity of a decision variable:
  // 0 (default) --> Use the variable's cached polarity together with antom's "polarity toggling scheme". 
  // 1           --> Use the variable's cached polarity only.
  // 2           --> The polarity will be set to FALSE regardless of the cached value. 
  // 3           --> The polarity will be set to TRUE regardless of the cached value.
  // Furthermore, antom maintains two variable orderings: "group 0" and "group 1". As long as "group 0" is 
  // non-empty, variables from that group will be preferred to serve as decision variables. By default, all 
  // variables belong to "group 1".
  void Antom::setDecisionStrategy (uint32_t val, uint32_t group)
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setDecisionStrategy(val, group); } }

  // Like "setDecisionStrategy()" for a specific variable instead of a group
  void Antom::setDecisionStrategyForVariable (uint32_t val, uint32_t var)
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setDecisionStrategyForVariable(val, var); } }

  // Sets the restart strategy to model "val":
  // 0 --> Luby (default).
  // 1 --> Glucose-like.       
  void Antom::setRestartStrategy (restartstrategy val)
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setRestartStrategy(val); } }

  void Antom::setSimplifyStrategy (simplifystrategy val)
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setSimplifyStrategy(val); } }

  // Sets the decay factor to "val" (default: 1.05). The decay factor is responsible 
  // for controlling how the variable activities evolve during the search process. 
  void Antom::setDecayFactor (double val) 
  { for (uint32_t t = 0; t < m_threads; ++t) { m_core[t]->setDecayFactor(val); } }

  // Performs unit propagation, taking the current CNF and the specified assumptions into account. Returns 
  // FALSE if a conflict occurs, otherwise the return value is TRUE. NOTE, THAT "deduceAssumptions()" CAN BE 
  // USED IN SINGLE-THREADED MODE ONLY.
  bool Antom::deduceAssumptions (void) { std::vector<uint32_t> assumptions; return deduceAssumptions(assumptions); } 
  bool Antom::deduceAssumptions (const std::vector<uint32_t>& assumptions)
  { assert(m_threads == 1); m_sID = 0; return m_core[0]->deduceAssumptions(assumptions); }

  // Solves the current CNF formula using the most promising configuration of antom. The return values are SAT/UNSAT.
  // NOTE, THAT "solveSATzilla()" CAN BE USED IN SINGLE-THREADED MODE ONLY.
  uint32_t Antom::solveSATzilla ( void )
  {
    // Check the number of threads. 
    assert(m_threads == 1);

    // Initialization.
    std::vector<uint32_t> assumptions; 
    uint32_t result(ANTOM_UNKNOWN); 
    double estimatedSync(0.0); 
    double bestSync(0.0);
    uint32_t bestConfig(1);
    const double intercept[configs] = {  1.331e+03, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p0[configs]        = {  5.751e-03, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p1[configs]        = {  1.513e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p2[configs]        = { -1.443e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p3[configs]        = {  6.215e-03, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p4[configs]        = { -2.212e+00, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p5[configs]        = {  6.837e+01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p6[configs]        = { -5.974e+00, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p7[configs]        = {  6.625e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p8[configs]        = { -3.101e+00, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p9[configs]        = {  2.448e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p10[configs]       = {  4.939e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p11[configs]       = {  2.017e+02, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p12[configs]       = {  3.228e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 }; 
    const double p13[configs]       = { -6.741e-04, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p14[configs]       = { -2.868e-04, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p15[configs]       = {  7.254e+03, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p16[configs]       = {  8.786e+01, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p17[configs]       = { -2.389e+02, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p18[configs]       = {  3.342e+00, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p19[configs]       = { -1.866e-01, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p20[configs]       = {          0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
    const double p21[configs]       = {          0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
 
    // Save antom's current status.
    m_core[0]->saveStatus();

    // Now, analyse all configurations.
    for (uint32_t c = 0; c < configs; ++c)
      {
		// Initialize current configuration.	
		m_core[0]->setDecisionStrategy(c_decisionStrategy[c], 0); 
		m_core[0]->setRestartStrategy(c_restartStrategy[c]); 
		m_core[0]->setLuby(c_unitFactor[c]); 
		m_core[0]->setDecayFactor(c_decayFactor[c]); 
		m_core[0]->setLHBR(c_lhbr[c]); 

		// Start some SAT solving.
		result = m_core[0]->solve(assumptions, 10); 
	
		// CNF formula already solved?
		if (result != ANTOM_UNKNOWN)
		  { return result; }
		else
		  {
			// Get some stats. 
			uint32_t x0(m_core[0]->variables());
			uint32_t x1(m_core[0]->decisions()); 
			uint32_t x2(m_core[0]->bcps()); 
			uint32_t x3(m_core[0]->conflicts());
			uint32_t x4(m_core[0]->restarts()); 
			double x5(m_core[0]->avgLBD()); 
			double x6(m_core[0]->avgCCLength()); 
			double x7(m_core[0]->avgDL()); 
			uint32_t x8(m_core[0]->learntUnitClauses()); 
			uint32_t x9(m_core[0]->learntBinaryClauses()); 
			uint32_t x10(m_core[0]->learntTernaryClauses()); 
			double x11(m_core[0]->avgDLclearedCA()); 
			double x12(m_core[0]->avgVarsUnassignedCA()); 
			uint32_t x13(m_core[0]->clauses()); 
			unsigned long x14(m_core[0]->implications());
			double x15((double) x0 / x13);
			double x16((double) x13 / x0);
			double x17((double) x1 / x3);
			double x18((double) x14 / x1);
			double x19((double) x14 / x3);
			uint32_t x20(m_core[0]->literals()); 
			double x21(m_core[0]->progress()); 

			// Estimate the number of synchronizations required to solve the CNF.
			estimatedSync = intercept[0]; 
			estimatedSync += p0[0] * (double) x0; 
			estimatedSync += p1[0] * (double) x1; 
			estimatedSync += p2[0] * (double) x2; 
			estimatedSync += p3[0] * (double) x3; 
			estimatedSync += p4[0] * (double) x4; 
			estimatedSync += p5[0] * x5; 
			estimatedSync += p6[0] * x6; 
			estimatedSync += p7[0] * x7; 
			estimatedSync += p8[0] * (double) x8; 
			estimatedSync += p9[0] * (double) x9; 
			estimatedSync += p10[0] * (double) x10; 
			estimatedSync += p11[0] * x11; 
			estimatedSync += p12[0] * x12; 
			estimatedSync += p13[0] * (double) x13; 
			estimatedSync += p14[0] * (double) x14; 
			estimatedSync += p15[0] * x15; 
			estimatedSync += p16[0] * x16; 
			estimatedSync += p17[0] * x17; 
			estimatedSync += p18[0] * x18; 
			estimatedSync += p19[0] * x19; 
			estimatedSync += p20[0] * x20; 
			estimatedSync += p21[0] * x21; 

			if (estimatedSync < (double) m_core[0]->synchronizations())
			  { estimatedSync = (double) m_core[0]->synchronizations(); }

			// Output. 
			if (m_control->getVerbosity() > 0)
			  { std::cout << "c estimated #synchronizations required by configuration " << c << ": " << estimatedSync << std::endl; }

			// Have we found a more promising configuration?
			if (c == 0 || estimatedSync < bestSync)
			  { bestConfig = c; bestSync = estimatedSync; }	       

			// Restore antom's status saved at the beginning.
			m_core[0]->restoreStatus();
		  }
      }

    // Output.
    if (m_control->getVerbosity() > 0)
      { std::cout << "c most promising configuration: " << bestConfig << std::endl; }

    // Configure antom, using the most promising configuration found before.
    m_core[0]->setDecisionStrategy(c_decisionStrategy[bestConfig], 0); 
    m_core[0]->setRestartStrategy(c_restartStrategy[bestConfig]); 
    m_core[0]->setLuby(c_unitFactor[bestConfig]); 
    m_core[0]->setDecayFactor(c_decayFactor[bestConfig]); 
    m_core[0]->setLHBR(c_lhbr[bestConfig]);     

    // Solve the CNF formula.
    result = m_core[0]->solve(assumptions); 

    // Output.
    if (m_control->getVerbosity() > 0)
      {
		double error((double) m_core[0]->synchronizations() / bestSync);
		std::cout << "c estimated / real #synchronizations: " << error << std::endl;
      }

    // Return "result".
    return result;
  }
  
  // Simplify Database
  void Antom::simplify( void ) 
  {
	for (uint32_t t = 0; t < m_threads; ++t)
      { m_core[t]->simplify(false); }
  }

  // Solves the current CNF formula, taking assumptions (if specified) into account. The assumptions have to be encoded in the 
  // same way as the literals of a clause (see "addClause()"). The return values are SAT/UNSAT. In the multi-threaded mode, the 
  // CNF formula gets solved by "m_threads" threads running in parallel, according to the well-known algorithm portfolio scheme. 
  uint32_t Antom::solve (void) 
  { std::vector<uint32_t> assumptions; return solve(assumptions); } 

  uint32_t Antom::solve (const std::vector<uint32_t>& assumptions) 
  {
    // Initialization.
    for (uint32_t t = 0; t < m_threads; ++t)
      { m_result[t] = ANTOM_UNKNOWN; }
    m_sID = 0; 

    // (Re-)initialize the "Control" object.
    m_control->resetDone();

#ifdef PARALLEL
#pragma omp parallel 
    {
      // Every thread has its own unique ID.
      uint32_t id(omp_get_thread_num());
	  
      // Solve the CNF formula.
      m_result[id] = m_core[id]->solve(assumptions); 
    }

    // Have we solved the CNF formula?
    uint32_t t(0); 
    for (t = 0; t < m_threads; ++t)
      { 
		if (m_result[t] != ANTOM_UNKNOWN)
		  { m_sID = t; return m_result[t]; }
      }
#else
	// Solve the CNF formula.
	m_result[0] = m_core[0]->solve(assumptions); 

	if (m_result[0] != ANTOM_UNKNOWN)
	  { m_sID = 0; return m_result[0]; }
#endif

    // If we reach this point, we've got a problem.
	// Sven: not in "basic operation timeout mode" :)
    //assert(t < m_threads); 

    // Return UNKNOWN.
    return ANTOM_UNKNOWN;
  }

  uint32_t Antom::getExtendedResult( void ) const { return m_core[m_sID]->getExtendedResult(); }

  // Stores the current status of all SAT solving cores.
  void Antom::saveStatus (void)
  {
#ifdef PARALLEL
#pragma omp parallel for 
    for (uint32_t t = 0; t < m_threads; ++t)
      { m_core[t]->saveStatus(); }
#else
	m_core[0]->saveStatus();
#endif
  }

  // Restores the status of all SAT solving cores saved before by "saveStatus()".
  void Antom::restoreStatus (void)
  {
#ifdef PARALLEL
#pragma omp parallel for 
    for (uint32_t t = 0; t < m_threads; ++t)
      { m_core[t]->restoreStatus(); }
#else
	m_core[0]->restoreStatus();
#endif
  }

  // Deletes the status of all SAT solving cores saved before by "saveStatus()". 
  void Antom::deleteStatus (void)
  {
#ifdef PARALLEL
#pragma omp parallel for 
    for (uint32_t t = 0; t < m_threads; ++t)
      { m_core[t]->deleteStatus(); }
#else
	m_core[0]->deleteStatus();
#endif
  } 

  // Resets antom and all SAT solving cores
  void Antom::reset (void)
  {
#ifdef PARALLEL
#pragma omp parallel for 
    for (uint32_t t = 0; t < m_threads; ++t)
      { 
		m_core[t]->reset(); 
		m_result[t] = ANTOM_UNKNOWN;
	  }
#else
	m_core[0]->reset(); 
	m_result[0] = ANTOM_UNKNOWN;
#endif

	m_softclauses.clear();
	m_partialTriggerParts.clear();
	m_currentTriggerParts.clear();

	m_low = 0;
	m_high= 0;
	m_lastIndex = 0;
	m_stacksize = 0;
	m_horizontalbypasses = 0;
	m_verticalbypasses = 0;
	m_comparator = 0;
	m_skipped = 0 ;
	m_triggervar = 0;

	m_globalPropertyTrigger.resize(1,0);
	m_softstack.clear();
	m_softstack.push_back(0);
	m_triggerlists.clear();
	m_triggerlists.resize(1);

	m_control->setTimeSetted( false );
	m_control->setSumTime( false );
  }

  // Writes current clauses into "db"
  void Antom::getClauseDatabase( std::vector< std::vector< uint32_t > >& db ) 
  { m_core[m_sID]->getClauseDatabase( db ); }

  // Clears all datastructures by deleting every related clause, etc. 
  // with variable indices between "begin" and "end"
  void Antom::clearVariables( uint32_t begin, uint32_t end )
  { 
	for (uint32_t t = 0; t < m_threads; ++t)
	  { m_core[t]->clearVariables(begin, end); }
  }

  std::vector< std::pair<std::vector< uint32_t >, uint32_t > > Antom::getConflictClauses( void ) const
  {
	return m_core[m_sID]->getConflictClauses();
  }

  /* antom preprocessor interface */ 

  /* Interface preprocessor */

  // De-/activates UPLA in preprocessing
  void Antom::setUPLA ( bool val )
  { 
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_preprocessor[t]->setUPLA(val); } 
  }

  // De-/activates full subsumption check in preprocessing
  void Antom::setSubsumption ( bool val )
  { 
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_preprocessor[t]->setSubsumption(val); } 
  }

  // De-/activates variable elimination in preprocessing
  void Antom::setVarElim( bool val )
  { 
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_preprocessor[t]->setVarElim(val); } 
  }

  // Set thresholds for cost (default: 10) and increase (default: 0 )
  // Only variables with equal or less "cost" occurences will be considered
  // Variable elimination is only performed if formula is maximum increased by "increase"
  void Antom::setVarIncrease( uint32_t costs, int increase )
  { 
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_preprocessor[t]->setVarIncrease(costs, increase); } 
  }

  // Sets maximum number of preprocessing loops
  void Antom::setMaxLoops ( uint32_t val )
  {
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_preprocessor[t]->setMaxLoops(val); } 
  }

  // Should variable "var" be a "Don't Touch" variable?
  void Antom::setDontTouch ( uint32_t var, bool dt )
  { 

	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_preprocessor[t]->setDontTouch(var, dt); } 
  }

  // Return true if "var" is a "Don't Touch" variable
  bool Antom::isDontTouch ( uint32_t var )
  {
	return m_preprocessor[0]->isDontTouch(var); 
  }

  // De-/active preprocessing
  void Antom::setPreprocessing ( bool val )
  { 
	m_dopreprocessing = val;  
	// Set preprocessing flag for each core in order to activate model extension
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_core[t]->setPreprocessing(val); } 
  }

  // De-/active inprocessing during solving
  void Antom::setInprocessing ( bool val )
  { 
	for (uint32_t t = 0; t < m_threads; ++t) 
	  { m_core[t]->setInprocessing(val); } 
  }

  // De-/active inprocessing during max-antom
  void Antom::setMaxInprocessing ( bool val )
  { m_maxInprocess = val; }

  // Be verbose
  void Antom::setVerbosity ( uint32_t val )
  { m_control->setVerbosity(val); }

  // Simplifies the current CNF formula by performing some preprocessing steps.
  // Returns FALSE if the formula is unsatisfiable, otherwise TRUE
  bool Antom::preprocess ( preprotype type )
  {
	// Initialization.
	for (uint32_t t = 0; t < m_threads; ++t)
	  {
		m_result[t] = ANTOM_UNKNOWN;
		m_core[t]->setPreprocessing(true);
	  }
	m_sID = 0;

	// (Re-)initialize the "Control" object.
	m_control->resetDone();

#ifdef PARALLEL
#pragma omp parallel 
	{
	  // Every thread has its own unique ID.
	  uint32_t id(omp_get_thread_num());

	  // Solve the CNF formula.
	  m_result[id] = m_preprocessor[id]->preprocess(type); 

    // Have we solved the CNF formula?
    uint32_t t(0); 
    for (t = 0; t < m_threads; ++t)
      {
		if (m_result[t] != ANTOM_UNKNOWN)
		  { m_sID = t; return m_result[t]; } 
	  }
	}
#else
	m_result[0] = m_preprocessor[0]->preprocess(type); 

	if (m_result[0] != ANTOM_UNKNOWN)
	  { m_sID = 0; return m_result[0]; } 
#endif

    // Return UNKNOWN.
    return ANTOM_UNKNOWN;
  }
}
