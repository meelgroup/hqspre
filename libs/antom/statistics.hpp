#ifndef STATISTICS_HPP
#define STATISTICS_HPP

/********************************************************************************************
statistiscs.hpp -- Copyright (c) 2016, Tobias Schubert, Sven Reimer

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


namespace antom {

  // Container for all solver statistics
  struct Statistics {
	uint32_t decisions; // The number of decisions made so far.
	uint32_t bcps; // The number of BCP operations performed so far. 
	unsigned long long implications; // The number of implications found so far.
	uint32_t usedVariables; // The number of acutual used Variables (not assigend on level 0)
	uint32_t totalConflicts; // The number of conflicts encountered so far.
	uint32_t totalLearntUnitClauses; // The number of unit clauses deduced due to conflict analysis.
	uint32_t totalLearntBinaryClauses;  // The number of binary clauses deduced due to conflict analysis.
	uint32_t totalLearntTernaryClauses; // The number of ternary clauses deduced due to conflict analysis.
	uint32_t staticClauses; // current number of static clauses in the database (including binary)
	uint32_t learnedClauses; // current number of learnt clauses in the database (including binary)
	uint32_t restarts; // The number of restarts performed so far.
	uint32_t simplifications; // The number of database simplifications performed so far.
	uint32_t lhbr; // The number of binary clauses deduced due to "Lazy Hyper Binary Resolution".

	uint32_t inprocessings; // The number of inprocessings performed so far.

	uint32_t synchronizations; // The number of synchronizations performed so far.
	double progress; // The progress after the search process has been stopped due to reaching the limit wrt. synchronizations.

	// Divided by "m_conflicts", "m_globalAvgLBD" represents the average 
	// "Literals Block Distance" of all conflict clauses deduced so far. 
	unsigned long long globalLBD; 

	unsigned long long localLBD; 

	// Divided by "m_conflicts", "m_avgCCLength" represents the average length 
	// of all conflict clauses deduced so far.
	unsigned long long staticLength;
	unsigned long long learnedLength;
	unsigned long long totalLearnedLength; 

	// Divided by "m_conflicts + m_restarts + 1", "m_avgDL" represents 
	// the solver's average decision level before backtracking.
	unsigned long long DL; 

	// Divided by "m_conflicts", "m_avgDLclearedCA" represents the 
	// average number of decision levels cleared during conflict analysis. 
	unsigned long long DLclearedCA;
	  
	// Divided by "m_conflicts", "m_avgVarsUnassignedCA" represents the 
	// average number of variables getting unassigned during conflict analysis. 
	unsigned long long VarsUnassignedCA; 

	// Some preprocessor statistics
	uint32_t constantVariables;
	uint32_t equivalentVariables;
	uint32_t uplaConstantVariables;
	uint32_t uplaEuivalentVariables;	
	uint32_t resolvedVariables;
	uint32_t monotoneVariables;
	uint32_t dontcareVariables;
	uint32_t subsumptions;
	uint32_t selfSubsumptions;
	uint32_t unitPropagations;
	uint32_t binaryClauses;
	uint32_t ternaryClauses;
	uint32_t naryClauses;

	void clearClauseStatistics (void)
	{
	  usedVariables = 0;
	  staticClauses = 0;
	  learnedClauses = 0;
	  learnedLength = 0;
	  staticLength = 0;
	  learnedLength = 0;
	  staticLength = 0;
	}
	void resetCore (void)
	{
	  decisions = 0;
	  implications = 0;
	  bcps = 0;
	  usedVariables = 0;
	  totalConflicts = 0;
	  totalLearntUnitClauses = 0;
	  totalLearntBinaryClauses = 0;
	  totalLearntTernaryClauses = 0;
	  staticClauses = 0;
	  learnedClauses = 0;
	  restarts = 0;
	  simplifications = 0;
	  lhbr = 0;
	  inprocessings = 0;
	  synchronizations = 0;
	  progress = 0.0;
	  globalLBD = 0;
	  localLBD = 0;
	  staticLength = 0;
	  learnedLength = 0;
	  totalLearnedLength = 0;
	  DL = 0;
	  DLclearedCA = 0;
	  VarsUnassignedCA = 0;
	}

	void resetPrepro (void)
	{
	  constantVariables = 0;
	  equivalentVariables = 0;
	  uplaConstantVariables = 0;
	  uplaEuivalentVariables = 0;	
	  resolvedVariables = 0;
	  monotoneVariables = 0;
	  dontcareVariables = 0;
	  subsumptions = 0;
	  selfSubsumptions = 0;
	  unitPropagations = 0;
	  binaryClauses = 0;
	}

	double inline litPerStaticClauses ( void ) const
	{
	  if (staticClauses == 0)
		{ return 0.0; }
	  return ((double)staticLength/staticClauses);
	}

	double inline litPerConflicts ( void ) const
	{
	  if (totalConflicts == 0)
		{ return 0.0; }
	  return ((double)learnedLength/totalConflicts);
	}
	  
	double inline currentLitPerConflicts ( void ) const
	{ 
	  if (learnedClauses == 0)
		{ return 0.0; }
	  return ((double)learnedLength/learnedClauses); 
	}

	double inline avgLBD (void) const 
	{
	  if (totalConflicts == 0)
		{ return 0.0; }
		
	  return ((double) globalLBD / totalConflicts); 
	}

	double inline avgCCLength( void ) const
	{
	  if (totalConflicts == 0)
		{ return 0.0; }
	  return ((double) totalLearnedLength / totalConflicts); 
	}

	double inline currentCCLength( void ) const
	{
	  if (learnedClauses == 0)
		{ return 0.0; }
	  return ((double) learnedLength / learnedClauses); 
	}

	double inline avgDL (void) const 
	{ return ((double) DL / (totalConflicts + restarts + 1)); }

	double inline avgDLclearedCA (void) const
	{
	  if (totalConflicts == 0)
		{ return 0.0; }
	  return ((double) DLclearedCA / totalConflicts); 
	}

	// Returns the average number of variables getting unassigned during conflict analysis. 
	double inline avgVarsUnassignedCA (void) const
	{
	  if (totalConflicts == 0)
		{ return 0.0; }
	  return ((double) VarsUnassignedCA / totalConflicts); 
	}
	  
  };
}

#endif
