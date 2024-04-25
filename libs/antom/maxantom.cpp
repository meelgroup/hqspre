 
/********************************************************************************************
maxantom.cpp -- Copyright (c) 2016, Sven Reimer

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
#include "control.hpp"
#include "preprocessor.hpp"

namespace antom
{

  // Helper function for sorter network generation
  uint32_t greatestPowerOfTwoLessThan (uint32_t n)
  {
    uint32_t k(1);
    while (k < n)
      { k <<= 1; }
    return (k >> 1);
  }

  // Helper function for sorter network generation
  uint32_t smallestPowerOfTwoLargerThan (uint32_t n)
  {
    uint32_t k(1);
    while (k < n)
      { k <<= 1; }
    return k;
  }

  bool compareSoftclauses ( Antom::softclause s1, Antom::softclause s2) 
  { return s1.s_contra > s2.s_contra; }

  void Antom::setMaxBounds( uint32_t low, uint32_t high )
  {
	assert( low <= high );
	m_low = low;
	m_high = high;
  }

  void Antom::setLowerBound( uint32_t low )
  {
	m_low = low;
  }

  void Antom::setHigherBound( uint32_t high )
  {
	m_high = high;
  }

  void Antom::setSortVarorder( uint32_t val ) 
  { m_sortvarorder = val; }
	  
  // Add a clause to the soft clause database
  bool Antom::addSoftClause( std::vector<uint32_t>& clause )
  {
	std::vector < uint32_t > sclause( clause.size() );
	uint32_t i = 0;
	for( ; i < clause.size(); ++i )
	  { 
        sclause[i] = clause[i]; 
        setDontTouch(clause[i]>>1); 
}

	if( m_control->getIncrementalMode() > 0 )
	  {
		// In incremental mode every softclause is triggered by a global assumption
		if ( m_globalPropertyTrigger[m_stacksize] == 0 )
		  { 
			m_globalPropertyTrigger[m_stacksize] = newVariable(); 
			setDontTouch(m_globalPropertyTrigger[m_stacksize]);
		  }
		clause.push_back(m_globalPropertyTrigger[m_stacksize]<<1);
	  }

	uint32_t trigger( newVariable() );
	setDontTouch(trigger);
	clause.push_back(trigger<<1);

	// Associate soft clause to current context 
	assert( m_stacksize < m_softstack.size() );
	
	// Create a new variable which is added to each clause in sorter network
	// Used in incremental mode where the sorter network and all conflict clauses resulting
	// from the network has to be deleted after every step
	m_softclauses.push_back( softclause(trigger<<1, sclause) );

	if( m_softstack[m_stacksize] == 0 )
	  { m_softstack[m_stacksize] = (uint32_t)m_softclauses.size(); }

	return addClause(clause);
  }

  // push-pop mechanism for soft clauses
  void Antom::softclause_push ( void ) 
  {
	std::cout << __func__ << " " << variables() << std::endl;
	++m_stacksize;
	if( m_stacksize >= m_globalPropertyTrigger.size() )
	  { 
		m_globalPropertyTrigger.resize( m_stacksize+1, 0 ); 
		m_softstack.push_back(0);
		m_triggerlists.resize( m_stacksize+1 ); 
		assert( m_softstack.size() == (m_stacksize+1) );
	  }

	assert( m_softstack[m_stacksize] == 0 );
	assert( m_globalPropertyTrigger[m_stacksize] == 0 );
  }

  void Antom::softclause_pop ( void ) 
  {
	std::cout << __func__ << std::endl;
	if( m_stacksize == 0 )
	  { 
		std::cout << "ERROR: try to pop non-existing context" << std::endl;
		exit(0);
	  }
	
#ifndef NDEBUG
	// Assume an ascending list of variables
	for( uint32_t i = 1; i < m_softstack.size(); ++i )
	  {
		assert( m_softstack[i] > m_softstack[i-1] );
	  }
#endif

	// Deactive property
	addUnit( (m_globalPropertyTrigger[m_stacksize]<<1) );
	// Deactive trigger
	assert( m_softstack[m_stacksize] > 0 );
	while( m_softclauses.size() >= m_softstack[m_stacksize] )
	  {
#ifndef NDEBUG
		bool rst = addUnit( m_softclauses.back().s_triggerlit );
		assert( rst );
#else
		addUnit( m_softclauses.back().s_triggerlit );
#endif
		m_softclauses.pop_back();
	  }

	if( !m_currentTriggerParts.empty() )
	  {
		assert( m_currentTriggerParts.size() == 1 );
		trivialAssignment();
		// clear trigger data structure
		Trigger& current(m_currentTriggerParts.front());
		size_t clausesize(current.softclauses.size());
		for( uint32_t i = 0 ; i < clausesize; ++i )
		  {
			uint32_t triggervar( current.softclauses[i].s_triggerlit>>1 );

			if( model()[triggervar] == (triggervar<<1) )
			  {
				std::cout << "delete softclause with triggervar " << triggervar << std::endl;
				current.softclauses[i--] = current.softclauses[--clausesize];
				current.softclauses.pop_back();
				continue;
			  }
		  }

		assert( !m_triggerlists[m_stacksize].empty() );
		current.currenttrigger = m_triggerlists[m_stacksize-1];
		
		m_core[m_sID]->simplify(false);
	  }

	m_globalPropertyTrigger[m_stacksize] = 0;
	m_softstack[m_stacksize] = 0;
	m_triggerlists[m_stacksize].clear();

	--m_stacksize;
  }

  // Checks whether soft clauses are satisfied "by chance" by the model "model", i.e. the trigger
  // literal in a soft clause is set to TRUE, but the clause is satisfied without the trigger literal
  // Returns the number of overall satisfied soft clauses
  uint32_t Antom::countSatisfiedSoftClauses( const std::vector<uint32_t>& model, Antom::Trigger& triggerPart, bool unproceeded )
  {
	uint32_t result(0);
	// Proceed all soft clauses
	for( uint32_t i = 0; i != triggerPart.softclauses.size(); ++i )
	  {
		uint32_t triggerlit = triggerPart.softclauses[i].s_triggerlit;
		
		if( !unproceeded )
		  { 
			triggerPart.softclauses[i].s_lastAssignment = model[triggerlit>>1]; 
		  }

		// Just proceed satisfied triggers
		if( model[triggerlit>>1] == triggerlit )
		  {
			std::vector< uint32_t> clause( triggerPart.softclauses[i].s_clause );
			for( uint32_t pos = 0; pos != clause.size(); ++pos )
			  {
				// clause satisfied without trigger?
				if( model[clause[pos]>>1] == clause[pos] )
				  {
					if( !unproceeded )
					  { 
						triggerPart.softclauses[i].s_lastAssignment = (triggerlit^1); 
					  }
					++result;
					break;
				  }
			  }
		  }
		else if ( !(unproceeded && m_setTrigger) && model[triggerlit>>1] != 0 )
		  { 
			assert( model[triggerlit>>1] == (triggerlit^1));
			++result; 
		  }
	  }
	return result;
  }

  // Try to flip variables in soft clauses such that new soft clauses are satisfied
  // Returns number of overall satisfied soft clauses
  uint32_t Antom::flipVariables( std::vector< uint32_t >& model )
  {
	// Assumes that first element of triggervars is the smallest
	std::vector< std::pair<bool, uint32_t> > softliterals( (m_softclauses.back().s_triggerlit>>1) , std::make_pair( true, 0 ) );
  
  std::vector< std::pair< uint32_t, uint32_t > > softvariables;

  std::vector< uint32_t > assumptions( m_softclauses.back().s_triggerlit>>1, 0 );

	for( uint32_t i = 0 ; i != assumptions.size(); ++i ) 
	  {
		// Put some fake model into assumptions, if variable does not exists in original problem
		if( model[i+1] == 0 )
		  { assumptions[i] = (i+1)<<1; }
		else
		  { assumptions[i] = model[i+1]; }
	  }

	// all literals we want to proceed
	for( uint32_t s = 0; s != m_softclauses.size(); ++s )
	  {
		uint32_t triggerlit = m_softclauses[s].s_triggerlit;
		std::vector<uint32_t> lits( m_softclauses[s].s_clause );
		bool satisfied = ( (model[triggerlit>>1]&1) == 0);

		for ( uint32_t pos = 0; pos != lits.size(); ++pos )
		  {
			++softliterals[lits[pos]>>1].second;
			// Just add variables whose trigger variable is "true"
			if( !satisfied && ( model[lits[pos]>>1] == lits[pos] ) )
			  {	
				softliterals[lits[pos]>>1].first = false;
			  }
		  } 
	  }

	for( uint32_t s = 1; s <= softliterals.size(); ++s )
	  { 
		if( softliterals[s].first && ( softliterals[s].second > 0 ) )
		  { 
			softvariables.push_back( std::make_pair( s, softliterals[s].second) ); 
		  }
	  }

	std::sort(softvariables.begin(), softvariables.end(), sortPairBySecond<uint32_t, uint32_t>);

	// Now add the models of all variables of the softclauses as assumption
	// Flip exact one value of a trigger and check, if a conflict occurs
	for( std::vector< std::pair< uint32_t, uint32_t > >::iterator i = softvariables.begin();  i != softvariables.end(); ++i )
	  {

		// flip sign
		assumptions[ i->first -1 ] ^= 1;
		
		// Now deduce this assumptions
		if( deduceAssumptions( assumptions ) )
		  {
			// No conflict occurs... switch sign of literal in model
			model[ i->first ] ^=1;
		  }
		// Flip back
		else
		  {	assumptions[i->first-1] ^= 1; }
	  }

	return countSatisfiedSoftClauses( model, m_currentTriggerParts.front() );
  }

  // Proceed all soft clauses
  // Count positive and negative occurences of all variables in soft clauses
  // Set decision strategy for the variables such that the polarity with more occurences is prefered
  // If there is no larger occurence value for a polarity, set the decision strategy to "0"
  // If "pos" is false the polarity with less occurences is prefered
  void Antom::setStrategyforSoftVariables( bool pos )
  {
	std::vector< uint32_t > occur( ((m_lastIndex<<1)+2), 0 );

	for( uint32_t i = 0; i != m_softclauses.size(); ++i )
	  {

		std::vector <uint32_t > lits( m_softclauses[i].s_clause);
		for ( uint32_t pos = 0; pos != lits.size(); ++pos )
		  { ++occur[lits[pos]]; }
	  }

	for( uint32_t v = 1; v <= m_lastIndex; ++v )
	  {
		uint32_t poslit( v<<1 );
		uint32_t neglit( (v<<1)^1 );
		if( occur[poslit] > occur[neglit] ) 
		  {
			if( pos )
			  { setDecisionStrategyForVariable(3,v); }
			else
			  { setDecisionStrategyForVariable(2,v); }
		  }
		else if ( occur[poslit] > occur[neglit] )
		  {
			if( pos )
			  { setDecisionStrategyForVariable(2,v); }
			else
			  { setDecisionStrategyForVariable(3,v); }
		  }
		else 
		  {
			setDecisionStrategyForVariable(0,v);
		  }
	  }
  }

  uint32_t Antom::maxSolve (uint32_t& optimum, uint32_t mode )
  {
	std::vector< uint32_t > externalAssumptions;
	return maxSolve( externalAssumptions, optimum, mode ); 
  }
  
  // Solves the current (partial) MaxSAT formula. Returns SAT/UNSAT and modifies "optimum", representing the minimum number of 
  // unsatisfied clauses. The modes of operation are:
  // mode = 0 --> unsatisfiability-based (multi-threaded: internal portfolio),
  // mode = 1 --> satisfiability-based (multi-threaded: internal portfolio).
  // mode = 2 --> binary search (multi-threaded: internal portfolio).
  uint32_t Antom::maxSolve (const std::vector< uint32_t >& externalAssumptions, uint32_t& optimum, uint32_t mode )
  {
	// Consistency checks.
    assert(mode < 6); 

	if( mode == 3 )
	  { std::cout << "mode 3 currently not supported" << std::endl; return ANTOM_UNKNOWN; }

	if( m_core[m_sID]->emptyClause() )
	  { return ANTOM_UNSAT; }

	bool partialmode(false);

	if( m_triggervar == 0 )
	  {
		m_triggervar = newVariable();
		addUnit(m_triggervar<<1);
	  }

	struct rusage resources;
	getrusage(RUSAGE_SELF, &resources); 
	double timeS  = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
	m_control->setStartTime(timeS);
	m_control->setSumTime(true);

	// There should be no additional assumption in non-incremental mode
	// exception: incomplete solving mode (mode > 2)
	assert( externalAssumptions.empty() || ( m_control->getIncrementalMode() != 0 ) || mode > 2 );

	if( m_control->getIncrementalMode() > 0 )
	  {
		for( uint32_t i = 0; i != externalAssumptions.size(); ++i )
		  { 
			setDontTouch(externalAssumptions[i]>>1); 
		  }
	  }

	uint32_t size((uint32_t)m_softclauses.size());

	if( size == 0 )
	  { 
		std::vector< uint32_t > tmpassumption = externalAssumptions;
		uint32_t res = solve(tmpassumption); 
		m_control->setSumTime(false);
		return res;
	  }

	if ( !partialmode && m_control->getVerbosity() > 1 )
	  { 
		std::cout << "c softclauses: " << size << std::endl
				  << "c hardclauses: " << (clauses()-size) << std::endl;
	  }

	if( m_dopreprocessing )
	  {
		// (Incrementally) preprocess formula without sorter
		if ( !preprocess( e_incremental ))
		  { 
			if( m_control->getIncrementalMode() > 0 )
			  { 
				invalidateSoftClauses(); 
			  }
			m_control->setSumTime(false);
			return ANTOM_UNSAT; 
		  }
	  }

	if( mode < 3 )
	  {
		// Add the "Bitonic Sorting Network" to the clause database. 
		// Collect trigger clauses of soft variables
		assert( m_softstack[m_stacksize] > 0 );

		// only build maxizimer if new soft clauses are added since last call
		if( m_currentTriggerParts.empty() || ( m_currentTriggerParts.front().softclauses.size() < m_softclauses.size() ) )
		  { 
		  
			Antom::Trigger trigger( (uint32_t)m_softclauses.size() - m_softstack[m_stacksize] - 1 );
			
			for( uint32_t i = m_softstack[m_stacksize]-1; i != m_softclauses.size(); ++i )
			  { 
				trigger.currenttrigger.push_back(m_softclauses[i].s_triggerlit>>1);
				trigger.softclauses.push_back(m_softclauses[i]);
			  }
		
			m_partialTriggerParts.push_back(trigger);
		
			createNextPartialMaximizer();
		  }


		if( m_currentTriggerParts.size() > 1 )
		  {
			assert( m_currentTriggerParts.size() == 2 );
			
			Antom::Trigger tempVariables1 = m_currentTriggerParts.front();
			m_currentTriggerParts.pop_front();
			Antom::Trigger tempVariables2 = m_currentTriggerParts.front();
			m_currentTriggerParts.pop_front();
			
			mergePartTrigger( tempVariables1, tempVariables2 );

			m_currentTriggerParts.push_front(tempVariables2);
		  }
		
		if( m_control->getVerbosity() > 1 )
		  {
			std::cout << "c comparator: " << m_comparator << " skipped: " << m_skipped << std::endl;
			std::cout << "c horizontal bypasses: " << m_horizontalbypasses << " vertical bypasses: " << m_verticalbypasses << std::endl;
		  }
	  }
	else 
	  { 
		if ( mode == 4 ) 
		  { partialmode = true; }
		mode = 1; 
	  }

	setDecisionStrategy(0,0);
	setDecisionStrategy(0,1);

	// Lower decision priority for original variables
	if( m_sortvarorder == 1)
	  {
		for( uint32_t v = 1; v <= m_lastIndex; ++v )
		  { setVarGroup(v,1); }
	  }
	// Random decision priority for all variables
	else if ( m_sortvarorder == 2 )
	  {
		for( uint32_t v = 1; v <= variables(); ++v )
		  {	setVarGroup(v,rand()%2); }
	  }
	// Lower decision priority for variables occuring in sorter network
	else if ( m_sortvarorder == 3 )
	  {
		for( uint32_t v = m_lastIndex+1; v <= variables(); ++v )
		  {	setVarGroup(v,1);  }
	  }

	// Mark all soft clause trigger as "Don't Touch"
	for( uint32_t i = 0; i != size; ++i )
	  { 
		setDontTouch(m_softclauses[i].s_triggerlit>>1); 
	  	if( mode == 0 )
	  	  { setDecisionStrategyForVariable(2, m_softclauses[i].s_triggerlit>>1); }
	  	else
	  	  { setDecisionStrategyForVariable(3, m_softclauses[i].s_triggerlit>>1); }
	  }

	Antom::Trigger& trigger = m_currentTriggerParts.front();
	uint32_t triggersize = trigger.size();
	
    // Initialization.
    const std::vector<uint32_t>& tmodel(model());
    uint32_t currentBestResult(0);
    uint32_t result(ANTOM_UNKNOWN);
	uint32_t currentresult(ANTOM_UNKNOWN);
    uint32_t pos(0); 
	// for incremental mode we may need to collect all assumptions...
	std::vector<uint32_t> collectedAssumptions = externalAssumptions;

	uint32_t nxtInprocess(0);
	// Perform inprocessing if we have obtained a 5% improvement
	uint32_t inprocessFactor( (triggersize*0.05) );

	if( m_dopreprocessing )
	  {
		// (Incrementally) preprocess formula including sorter
		if (!preprocess( e_incremental ))
		  { 
			if( m_control->getIncrementalMode() > 0 )
			  { 
				invalidateSoftClauses(); 
			  }
			m_control->setSumTime(false);
			return ANTOM_UNSAT; 
		  }
	  }

	// Initialize the 4 threads of our portfolio. 
	if (m_threads == 4)
	  {
	    m_core[0]->setLHBR(true); 
	    m_core[1]->setLHBR(false); 
	    m_core[2]->setLHBR(true); 
	    m_core[3]->setLHBR(true); 

	    m_core[0]->setLuby(8); 
	    m_core[1]->setLuby(12); 
	    m_core[2]->setLuby(6); 
	    m_core[3]->setLuby(6); 

	    m_core[0]->setDecisionStrategy(2, 1); 
	    m_core[1]->setDecisionStrategy(0, 1);
	    m_core[2]->setDecisionStrategy(0, 1); 
	    m_core[3]->setDecisionStrategy(2, 1); 

	    m_core[0]->setRestartStrategy(LUBY); 
	    m_core[1]->setRestartStrategy(LUBY); 
	    m_core[2]->setRestartStrategy(GLUCOSE); 
	    m_core[3]->setRestartStrategy(GLUCOSE); 
 
	    m_core[0]->setDecayFactor(1.05);
	    m_core[1]->setDecayFactor(1.10);
	    m_core[2]->setDecayFactor(1.05);
	    m_core[3]->setDecayFactor(1.20);
	  }

	// Handle user given bounds
	if( ( m_low > 0 ) && m_low <= triggersize )
	  {
		uint32_t lowerlit = (trigger.currenttrigger[m_low-1]<<1)^1;
		if( ( m_control->getIncrementalMode() > 0 ) || ( partialmode && !m_incompleteMode) )
		  {
			collectedAssumptions.push_back( lowerlit ); 
		  }
		else
		  {
			if( !addUnit( lowerlit ) )
			  {
				m_control->setSumTime(false);
				return ANTOM_UNSAT;
			  }
		  }
	  }
	if( ( m_high > 0 ) && ( m_high <= triggersize ) )
	  {
		uint32_t higherlit = (trigger.currenttrigger[triggersize-m_high]<<1);

		if( ( m_control->getIncrementalMode() > 0 ) || ( partialmode && !m_incompleteMode ) )
		  {
			collectedAssumptions.push_back( higherlit ); 
		  }
		else
		  {
#ifndef NDEBUG
			bool rst(false); rst = addUnit(higherlit); assert( rst );
#else
			addUnit(higherlit);
#endif
		  }
	  }

	if( m_control->getVerbosity() > 3 )
	  {
		std::cout << "current trigger: " << std::endl;
		trivialAssignment();
		for( uint32_t i = 0; i != triggersize; ++i )
		  {
			if( i < trigger.softclauses.size() )
			  {
				std::cout << " " << i << " " << trigger.currenttrigger[i] << " [" << Lit(model()[trigger.currenttrigger[i]]) << "] ";
				std::cout << " clause: ";
				for( uint32_t j = 0 ; j != trigger.softclauses[i].s_clause.size(); ++j )
				  { 
					std::cout << Lit( trigger.softclauses[i].s_clause[j]) << " "; 
				  }
				std::cout << " trigger: " << Lit(trigger.softclauses[i].s_triggerlit) << std::endl;
			  }
			else if ( m_control->getVerbosity() > 4 )
			  {
				std::cout << " " << i << " " << trigger.currenttrigger[i] << " [" << Lit(model()[trigger.currenttrigger[i]]) << "] " << std::endl;
			  }
		  }
	  }

	// Activate property in incremental mode
	if( ( m_control->getIncrementalMode() > 0 ) )
	  { 
		for( uint32_t i = 0; i <= m_stacksize; ++ i )
		  {
			assert( m_globalPropertyTrigger[i] != 0 );
			collectedAssumptions.push_back( (m_globalPropertyTrigger[i]<<1)^1 ); 
		  }
	  }

	// What about "mode"?
    switch (mode)
      {
	
		// UNSAT based
      case 0: 

		// Initialization. 
		pos = triggersize;
		currentresult = ANTOM_UNSAT; 
		currentBestResult = triggersize;

		if( m_high > 0 )
		  { 
			currentBestResult = triggersize-m_high-1; 
		  }

		nxtInprocess = pos-inprocessFactor;

		if( m_low > 0 )
		  { pos = size-m_low-1;  }

		// Now, solve the MaxSAT problem, using a unsatisfiability-based approach.  
		while (true)
		  {
			// Decrement "pos".
			--pos; 

			if( m_maxInprocess && !partialmode && ( pos <= nxtInprocess ) )
			  {
				currentresult = preprocess(e_in);
		    
				// Have we found the optimum?
				if (currentresult == ANTOM_UNSAT)
				  { break; }
				nxtInprocess = pos - inprocessFactor;
			  }

			// Output.
			if (m_control->getVerbosity() > 0) 
			  { std::cout << "c checking o = " << (size - pos - 1) << "..." << std::endl; }

			collectedAssumptions.push_back( (trigger.currenttrigger[pos]<<1)^1 );
			
			// Solve the CNF, taking our assumption into account. 
			currentresult = solve(collectedAssumptions); 
		
			// Have we found the optimum?
			if (currentresult == ANTOM_SAT)
			  { 
				result = ANTOM_SAT;
				// Update "optimum".				
				optimum  = triggersize - pos - 1;
				break; 
			  }
			// Reached timeout?
			else if ( currentresult == ANTOM_UNKNOWN )
			  {
				assert( m_control->getCPULimit() > 0.0 );
				if( m_control->getIncrementalMode() > 0 )
				  { 
					invalidateSoftClauses(); 
				  }
				m_control->setSumTime(false);
				return ANTOM_UNKNOWN;
			  }

			if( ( m_control->getIncrementalMode() > 0 ) || ( partialmode && !m_incompleteMode ) )
			  {
				assert( !collectedAssumptions.empty() );
				collectedAssumptions[collectedAssumptions.size()-1] ^= 1;
			  }
			else 
			  {
				uint32_t assumption( collectedAssumptions.back() );
				// Remove from collected assumption
				collectedAssumptions.pop_back();
				// Flip the current assumption and add it as a unit clause to the clause database.
				if (!addUnit(assumption^1) )
				  { assert(currentresult == ANTOM_UNSAT); break; }

			  }
		
			// Did we reached the last element?
			if( pos == 0 )
			  { 
				optimum = currentBestResult;
				currentresult = solve(collectedAssumptions);
				// Reached timeout?
				if ( currentresult == ANTOM_UNKNOWN )
				  {
					assert( m_control->getCPULimit() > 0.0 );
				  }
				break; 
			  }
		  }

		if( m_control->getIncrementalMode() == 1 )
		  { 
			invalidateSoftClauses(); 
		  }

		// Return "result".
		m_control->setSumTime(false);
		return result; 
	
		// SAT-based 
      case 1:

		nxtInprocess = pos + inprocessFactor;

		// Initialization.
		result = ANTOM_UNSAT;

		// Solve the MaxSAT problem, using a satisfiability-based approach.  
		while (true)
		  {
			if( m_maxInprocess && !partialmode && pos >= nxtInprocess )
			  {
				// Do inprocessing
				currentresult = preprocess(e_in);
		
				// Have we found the optimum?
				if (currentresult != ANTOM_UNKNOWN)
				  { break; }
				nxtInprocess = pos + inprocessFactor;
			  }

			// Solve the CNF. 
			currentresult = solve(collectedAssumptions); 

			// Have we found the optimum?
			if (currentresult == ANTOM_UNSAT)
			  { break; }
			// Reached timeout?
			else if ( currentresult == ANTOM_UNKNOWN )
			  {
#ifndef NDEBUG
				getrusage(RUSAGE_SELF, &resources); 
				double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
				assert( timeC - m_control->getCPULimit() > 0.0 );
#endif
				assert( m_control->getCPULimit() > 0.0 );

				if( m_control->getIncrementalMode() > 0 )
				  { 
					invalidateSoftClauses(); 
				  }
				m_control->setSumTime(false);
				return ANTOM_UNKNOWN;
			  }
			else
			  { 
				result = currentresult; 
			  }

			// Try to satisfy more soft clauses by chance.	    
			const std::vector<uint32_t>& newModel(model());
			pos = countSatisfiedSoftClauses( newModel, trigger );
			currentBestResult = pos;

			assert(pos <= size);


			// Output our current best result. 
			if ((m_control->getVerbosity() > 0) && !partialmode)
			  { 
				std::cout << "o " << (size - pos) << std::endl; 
				if( m_control->getVerbosity()>1)
				  {
					getrusage(RUSAGE_SELF, &resources); 
					double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
					std::cout << "c " << (timeC-m_control->getStartTime()) << "s" <<std::endl;
				  }
			  }

			// Have we found the very special case with all trigger variables set to FALSE?
			if (triggersize == pos)
			  { break; }

			uint32_t litbound( (trigger.currenttrigger[pos] << 1) ^ 1 ); 

			if( (m_control->getIncrementalMode() > 0 ) || partialmode )
			  {
				collectedAssumptions.push_back(litbound); 
			  }
			else 
			  {
				// Flip the first trigger variable currently set to TRUE and add it to the database.
				if (!addUnit( litbound ) )
				  { break; }
			  }
		  }
	
		// Update "optimum".
		optimum = size - pos;

		if( m_control->getIncrementalMode() == 1 )
		  { 
			invalidateSoftClauses(); 
		  }

		// Return "result".
		return result; 

		// Binary search
	  case 2:
		
		uint32_t min = 0;
		uint32_t max = size;

		// Initialization.
		currentresult = solve(collectedAssumptions);
	    // Have we found the optimum?
	    if (currentresult == ANTOM_UNSAT)
	      { min=max; m_control->setSumTime(false); return ANTOM_UNSAT; }
		// Reached timeout?
		else if ( currentresult == ANTOM_UNKNOWN )
		  {
			assert( m_control->getCPULimit() > 0.0 );
			if( m_control->getIncrementalMode() == 1 )
			  { 
				invalidateSoftClauses(); 
			  }
			m_control->setSumTime(false);
			return ANTOM_UNKNOWN;
		  }

		// a lazy quick and dirty way to preserve the best model
		// TODO
		std::vector< uint32_t > bestmodel = model();

		min = countSatisfiedSoftClauses( tmodel, trigger );

		uint32_t t = triggersize;
		bool res = true;
		// search for upper bound
		collectedAssumptions.push_back( (trigger.currenttrigger[triggersize-1]<<1)^1 );
		do {
		  --t;
		  collectedAssumptions.pop_back();
		  collectedAssumptions.push_back( (trigger.currenttrigger[t]<<1)^1 );
		  res = deduceAssumptions(collectedAssumptions);
		} while ( !res );

		collectedAssumptions.pop_back();
		max = t+1;

		pos = (min+max-1) >> 1;	

		currentBestResult = size-min;
		// Output our current best result. 
		if ( m_control->getVerbosity() > 0 )
		  {
			std::cout << "o " << currentBestResult << std::endl; 
			if ( m_control->getVerbosity() > 1 )
			  { 
				getrusage(RUSAGE_SELF, &resources); 
				double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
				std::cout << "c " << (timeC-m_control->getStartTime()) << "s" <<std::endl;
				std::cout << "c known bounds: (" << (triggersize-max) << " / " << (triggersize-min) << ")" << std::endl;
			  }
		  }
		
		if ( min > 0 )
		  { 
			if( ( m_control->getIncrementalMode() > 0 ) || ( partialmode && !m_incompleteMode ) )
			  {
				collectedAssumptions.push_back( (trigger.currenttrigger[min-1]<<1)^1 ); 
			  }
			else 
			  {
				// if the resulting problem is unsatisfied, we have found our optimum!
				if (!addUnit( (trigger.currenttrigger[min-1]<<1)^1) )
				  { max=min; }
			  }
		  }
		if ( max < triggersize )
		  { 
			if( ( m_control->getIncrementalMode() > 0 ) || ( partialmode && !m_incompleteMode ) )
			  {
				collectedAssumptions.push_back( trigger.currenttrigger[max]<<1 ); 
			  }
			else
			  {
#ifndef NDEBUG
				bool rst(false); rst = addUnit(trigger.currenttrigger[max] << 1); assert(rst);
#else
				addUnit(trigger.currenttrigger[max] << 1);
#endif
			  }
		  }

		if( m_maxInprocess && !partialmode  && ( (max < triggersize) || (min > 0) ) )
		  {
			// Do inprocessing
			currentresult = preprocess(e_in);

			if( currentresult == ANTOM_UNSAT )
			  { break; }
		  }

		while ( min < max )
		  {
			if ( m_control->getVerbosity() > 1 )
			  { std::cout << "c TRY with " << (triggersize-pos-1) << std::endl; }

			collectedAssumptions.push_back( (trigger.currenttrigger[pos]<<1)^1);

			currentresult = solve(collectedAssumptions);

			if ( currentresult == ANTOM_SAT) // SAT
			  {
				result = ANTOM_SAT;
				bestmodel = model();
				if ( m_control->getVerbosity() > 1 )
				  { std::cout << "c Found with " << (triggersize-pos-1) << std::endl; }
				
				uint32_t nxtmin = countSatisfiedSoftClauses(tmodel, trigger);
				assert( nxtmin > min );
				min = nxtmin;
				
				currentBestResult = size-min;

				// Output our current best result. 
				if ( m_control->getVerbosity() > 0 )
				  { 
					std::cout << "o " << currentBestResult << std::endl; 
					if ( m_control->getVerbosity() > 1)
					  {
						getrusage(RUSAGE_SELF, &resources); 
						double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
						std::cout << "c " << (timeC-m_control->getStartTime()) << "s" <<std::endl;
					  }
				  }
			  }
			else if ( currentresult == ANTOM_UNSAT ) // UNSAT
			  {
				if ( m_control->getVerbosity() > 1 )
				  { std::cout << "c Failed with " << (triggersize-pos-1) << std::endl; }
				
				max = pos;

				assert( !collectedAssumptions.empty() );				
				collectedAssumptions[collectedAssumptions.size()-1] ^= 1;

			  }
			else if ( currentresult == ANTOM_UNKNOWN ) // Reached timeout?
			  {
				assert( m_control->getCPULimit() > 0.0 );
				if( m_control->getIncrementalMode() > 0 )
				  { 
					invalidateSoftClauses(); 
					for( uint32_t i = 0; i != externalAssumptions.size(); ++i )
					  { setDontTouch((externalAssumptions[i]>>1),false); }
				  }
				m_control->setSumTime(false);
				return ANTOM_UNKNOWN;
			  }
			else
			  { assert(false); }
			
			if ( ( m_control->getIncrementalMode() == 0 ) && ( !partialmode || m_incompleteMode ) )
			  {
#ifndef NDEBUG
				bool rst(false); rst = addUnit( collectedAssumptions.back() ); assert( rst );
#else
				addUnit( collectedAssumptions.back() );
#endif
				collectedAssumptions.pop_back();
			  }

			// Do inprocessing
			if( m_maxInprocess && !partialmode  )
			  {
				currentresult = preprocess(e_in);
				
				// instance unsatisfiable with added assumption?
				// then the currentoptimum is the best result
				if( currentresult != ANTOM_UNKNOWN )
				  { break; }
			  }
		
			pos = (min+max-1) >> 1;
		  
			if ( m_control->getVerbosity() > 1 )
			  { std::cout << "c known bounds: (" << (triggersize-max) << " / " << (triggersize-min) << ")" << std::endl; }

		  }

		if ( currentBestResult > 0 )
		  { 
			std::vector< uint32_t > model_assumption;
			model_assumption.reserve(m_lastIndex+1);
			// solve with the best found model, so that the antom-model is set correctly 
			// just add the model for the original clauses. 
			// Due to our "by chance" method the virtual best model is not complete
			for ( uint32_t m = 1; m <= m_lastIndex; ++m )
			  {
				if( bestmodel[m] != 0 )
				  { model_assumption.push_back(bestmodel[m]);}
			  }

			// this is the quick and dirty way! TODO
			currentresult = solve(model_assumption);

			assert( currentresult == ANTOM_SAT && result == ANTOM_SAT);
			optimum = currentBestResult;
		  }

		if( m_control->getIncrementalMode() == 1 )
		  { 
			invalidateSoftClauses(); 
		  }

		m_control->setSumTime(false);
		return result;

	  }

    // If we reach this point, something went wrong.
    assert(false);
    return ANTOM_UNKNOWN;
  }


  uint32_t Antom::calcFirstDepth( uint32_t& result, uint32_t& optimum, uint32_t& overalloptimum, std::vector< uint32_t>& externalAssumptions, uint32_t maxmode )
  {
	uint32_t size((uint32_t)m_softclauses.size());
	uint32_t currentresult(ANTOM_UNKNOWN);

	struct rusage resources;

	while( !m_partialTriggerParts.empty() )
	  {
		// Create sorter for part "part" 
		createNextPartialMaximizer();

		if( m_control->getVerbosity() > 1 )
		  {
			std::cout << "c comparator: " << m_comparator << " skipped: " << m_skipped << std::endl;
			std::cout << "c horizontal bypasses: " << m_horizontalbypasses << " vertical bypasses: " << m_verticalbypasses << std::endl;
		  }

		uint32_t partialoptimum = size;

		std::vector< uint32_t > localAssumptions = externalAssumptions;

		Antom::Trigger& trigger = m_currentTriggerParts.front();

		setSoftTrigger( localAssumptions );

		if( m_control->getVerbosity() > 1 )
		  {
			uint32_t sum(0);
			std::cout << "c ";
			for( uint32_t i = 0; i != m_currentTriggerParts.size(); ++i )
			  {
				std::cout << m_currentTriggerParts[i].softclauses.size() << " (" << m_currentTriggerParts[i].depth << "), ";
				sum += (uint32_t)m_currentTriggerParts[i].softclauses.size();
			  }
			std::cout << " (" << sum << "," << m_softclauses.size() << ")" << std::endl;
			assert( sum <= m_softclauses.size() );
		  }

		// All soft clauses already in one part?
		if( trigger.softclauses.size() >= m_softclauses.size() )
		  { maxmode = 5; }

		// Maximize partial sorter
		// Assumes that current partial result is in front of list

		if( m_maxInprocess )
		  { currentresult = preprocess(e_in); }
		else
		  { currentresult = ANTOM_UNKNOWN; }

		currentresult = maxSolve( localAssumptions, partialoptimum, maxmode );
		m_control->setSumTime(true);

		trigger.optimum = partialoptimum;
		++trigger.depth;

		if( currentresult == ANTOM_SAT )
		  {
			result = ANTOM_SAT;

			optimum = partialoptimum - updateTriggerOptimum();

			if( size != partialoptimum )
			  {
				uint32_t lit = (trigger.currenttrigger[size-partialoptimum-1]<<1)^1;

				// if( m_incompleteMode )
				//   { addUnit( lit ); }
				// else
				//   { externalAssumptions.push_back( lit ); }

				externalAssumptions.push_back( lit );
			
				if( optimum < overalloptimum )
				  {
					overalloptimum = optimum; 
					
					if ( m_control->getVerbosity() > 0 )
					  { 
						std::cout << "o " << optimum << std::endl; 
						
						if ( m_control->getVerbosity() > 1 )
						  {
							getrusage(RUSAGE_SELF, &resources); 
							double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
							std::cout << "c " << (timeC-m_control->getStartTime()) << "s" << std::endl;
						  }
					  }
				  }
			  }

			// "unit" bounds for the first element
			if( ( m_currentTriggerParts.size() == 1 ) && ( ( size-partialoptimum ) < trigger.size() ) && ( maxmode != 5 ) )
			  {
				uint32_t lit = (trigger.currenttrigger[size-partialoptimum]<<1);
#ifndef NDEBUG
				bool rst = addUnit(lit); assert(rst);
#else
				addUnit(lit);
#endif
			  }
		  }
		else if( currentresult == ANTOM_UNSAT )
		  {
			m_control->setSumTime(false);
			return ANTOM_UNSAT;
		  }
		// Timeout
		else if( currentresult == ANTOM_UNKNOWN )
		  {
			assert( m_control->getCPULimit() > 0.0 );
			if( m_control->getIncrementalMode() == 1 )
			  { 
				invalidateSoftClauses(); 
			  }
			m_control->setSumTime(false);
			return ANTOM_UNKNOWN;				
		  }
	  }

	return ANTOM_SAT;
  }

  // Merge to trigger parts. The merged trigger will be "trigger2" after merging
  void Antom::mergePartTrigger( Antom::Trigger& trigger1, Antom::Trigger& trigger2 )
  {
	uint32_t size((uint32_t)m_softclauses.size());

	assert( m_triggervar != 0 );
	// Fill the two parts in order to get two balanced part
	while( trigger1.size() < trigger2.size() )
	  {
		uint32_t dummyvar = m_triggervar;
		trigger1.currenttrigger.push_back( dummyvar );
	  }
	while( trigger2.size() < trigger1.size() )
	  {
		uint32_t dummyvar = m_triggervar;
		trigger2.currenttrigger.push_back( dummyvar );
	  }
				
	assert( trigger1.size() == trigger2.size() );

	std::vector< uint32_t > inputA(trigger1.currenttrigger);
	std::vector< uint32_t > inputB(trigger2.currenttrigger);

	// Merge current triggers
	trigger2.currenttrigger.insert( trigger2.currenttrigger.end(), trigger1.currenttrigger.begin(), trigger1.currenttrigger.end());
				
	// Reverse "left half": bitonic sorter needs one half in decreasing and the other in increasing order
	if( m_networktype == 0 )
	  {
		uint32_t middle = trigger2.size()>>1;
		uint32_t start = 0;
		while ((start != middle) && (start != --middle)) 
		  { std::swap(trigger2.currenttrigger[start++], trigger2.currenttrigger[middle]); }
	  }

	// Merge original trigger indices
	trigger2.softclauses.insert( trigger2.softclauses.end(), trigger1.softclauses.begin(), trigger1.softclauses.end() );

	findSorterCSC( trigger2 );

	trigger2.optimum = trigger2.optimum + trigger1.optimum - size;
	
	uint32_t partopt = trigger2.optimum;
	for( uint32_t i = 0; i != m_partialTriggerParts.size(); ++i )
	  {
		partopt = partopt - (int)m_softclauses.size() + m_partialTriggerParts[i].optimum;
	  }
	int maxsim = (int)trigger2.softclauses.size() - partopt;

	// Can we ensure a minimum of satisfied soft clauses?
	if( ( maxsim > 0 ) && ( (int)trigger2.maxsimultan < maxsim ) )
	  { trigger2.maxsimultan = maxsim; }
	
	// "Re-don't touch" current trigger vars
	if( trigger2.depth > 0 )
	  {
		for( uint32_t i = 0; i != trigger2.size(); ++i )
		  {
			setDontTouch(trigger2.currenttrigger[i], false);
		  }
	  }

	//clear model
	trivialAssignment();
	uint32_t n = antom::smallestPowerOfTwoLargerThan(trigger2.size());

	// Merge two partial sets
	switch( m_networktype )
	  {
	  case 0:
		bitonicMerge( trigger2, 0, trigger2.size(), false );
		break;
	  case 1: 
		
		for( uint32_t i = trigger2.size(); i < n; ++i )
		  {
			uint32_t dummyvar = m_triggervar;
			trigger2.currenttrigger.push_back( dummyvar );
		  }

		oddEvenMerge( trigger2, 0, trigger2.size(), 1 );
		break;
	  case 2:
		// TODO
		assert(false);
		break;
	  default:
		assert(false);
		break;
	  }

	// Store partial optimum
	setSorterCSC( trigger2 );

	setHorizontalBypasses( inputA, inputB, trigger2);

	// increase depth
	++trigger2.depth;

	setVerticalBypasses( trigger2 );

	if ( m_control->getVerbosity() > 1)
	  {
		std::cout << "c comparator: " << m_comparator << " skipped: " << m_skipped << std::endl;
		std::cout << "c horizontal bypasses: " << m_horizontalbypasses << " vertical bypasses: " << m_verticalbypasses << std::endl;
	  }

	assert( m_triggerlists.size() > m_stacksize );
	m_triggerlists[m_stacksize] = trigger2.currenttrigger;
  }

  uint32_t Antom::maxSolvePartial ( uint32_t& optimum, uint32_t mode )
  {
	std::vector< uint32_t > externalAssumptions;
	return maxSolvePartial( externalAssumptions, optimum, mode );
  }

  uint32_t Antom::maxSolvePartial ( const std::vector< uint32_t >& externalAssumptions, uint32_t& optimum, uint32_t mode )
  {
	// Consistency checks.
    assert(mode < 2); 
	assert( !m_incompleteMode || ( mode == 1 ) );

	if( m_core[m_sID]->emptyClause() )
	  { 
		if( m_control->getIncrementalMode() > 0 )
		  { 
			invalidateSoftClauses(); 
		  }
		return ANTOM_UNSAT; 
	  }

	// Set incrementalmode to "incremental + partial"
	if( m_control->getIncrementalMode() == 1 )
	  { m_control->setIncrementalMode(2); }

	struct rusage resources;
	getrusage(RUSAGE_SELF, &resources); 
	double timeS  = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
	m_control->setStartTime(timeS);
	m_control->setSumTime(true);

	for( uint32_t i = 0; i != externalAssumptions.size(); ++i )
	  { setDontTouch(externalAssumptions[i]>>1); }

	uint32_t size((uint32_t)m_softclauses.size());
	uint32_t currentresult(ANTOM_UNKNOWN);
	uint32_t result(ANTOM_UNKNOWN);
	uint32_t depth(0);
	uint32_t maxmode(4);
	uint32_t currentoptimum(size+1);
	optimum = size+1;

	bool firstsolve(false);

	if( m_triggervar == 0 )
	  {
		m_triggervar = newVariable();
		addUnit(m_triggervar<<1);
	  }

	if ( m_control->getVerbosity() > 1 )
	  { 
		std::cout << "c softclauses: " << size << std::endl
				  << "c hardclauses: " << (clauses()-m_softclauses.size()) << std::endl;
	  }

	// calc and set all trivially conflicting softclauses
	checkAllConflictingSoftclauses();
	calcSplitWidth();

	uint32_t prepart(0);
	// build datastructure for parts
	while( prepart*m_splittedWidth < size )
	  {
		uint32_t s ( prepart*m_splittedWidth );
		uint32_t maxsize = s+m_splittedWidth;

		if( size < maxsize )
		  { maxsize = size; }
		
		Antom::Trigger trigger(m_splittedWidth);

		for( ; s < maxsize; ++s )
		  { 
			trigger.currenttrigger.push_back(m_softclauses[s].s_triggerlit>>1);
			trigger.softclauses.push_back(m_softclauses[s]);
		  }
		m_partialTriggerParts.push_back(trigger);
		++prepart;

	  }

	// Reverse 
	size_t end(m_partialTriggerParts.size());
	size_t start(0);
	while ((start != end) && (start != --end)) 
	  { std::swap(m_partialTriggerParts[start++], m_partialTriggerParts[end]); }

	if( size == 0 )
	  { 
		uint32_t res = solve(externalAssumptions);
		m_control->setSumTime(false);
		if( m_control->getIncrementalMode() > 0 )
		  { 
			invalidateSoftClauses(); 
		  }
		return res;
	  }

	currentoptimum = size;
	std::vector< uint32_t > collectedAssumptions;

	if ( m_control->getVerbosity() > 1 )
	  { std::cout << "c start solving depth " << depth << " width: " << m_splittedWidth << std::endl; }
	
	std::vector< uint32_t > tempassumptions;

	switch ( mode )
	  {
	  case 0: 
		// Depth-first-seach mode
		do
		  {
			uint32_t partsize((uint32_t)m_currentTriggerParts.size());
			
			// create partial sorter as base case
			// Either there is only one candidate on stack or just one candidate with the correct depth
			if( ( partsize < 2 || m_currentTriggerParts[0].depth < m_currentTriggerParts[1].depth ) && ( !m_partialTriggerParts.empty() ) )
			  {
				// Create sorter for part "part" 
				createNextPartialMaximizer();

				if( m_control->getVerbosity() > 1 )
				  {
					std::cout << "c comparator: " << m_comparator << " skipped: " << m_skipped << std::endl;
					std::cout << "c horizontal bypasses: " << m_horizontalbypasses << " vertical bypasses: " << m_verticalbypasses << std::endl;
				  }
			  }
			// In non base case take first two part and merge
			else
			  {
				assert( partsize > 1 );

				// Now merge sorters

				Antom::Trigger tempVariables1 = m_currentTriggerParts[0];
				m_currentTriggerParts.pop_front();
				Antom::Trigger tempVariables2 = m_currentTriggerParts[0];
				m_currentTriggerParts.pop_front();

				mergePartTrigger( tempVariables1, tempVariables2 );

				currentoptimum = currentoptimum + (size-tempVariables2.optimum);

				if( size != tempVariables2.optimum )
				  {
					uint32_t lit = (tempVariables2.currenttrigger[size-tempVariables2.optimum-1]<<1)^1;
					tempVariables2.assumption = lit;
				  }

				// Pushed merged list in front
				m_currentTriggerParts.push_front(tempVariables2);
			  }

			// Add assumptions
			collectedAssumptions.clear(); 
			// Add partial bounds to assumptions
			for( uint32_t i = 0 ; i != m_currentTriggerParts.size(); ++i )
			  {
				if( m_currentTriggerParts[i].assumption != 0 )
				  { 
					collectedAssumptions.push_back(m_currentTriggerParts[i].assumption);
				  }
			  }

			setSoftTrigger( collectedAssumptions );

			// solve (merged) instance 
			uint32_t partialoptimum = size;

			if( m_control->getVerbosity() > 1 )
			  {
				uint32_t sum(0);
				std::cout << "c ";
				for( uint32_t i = 0; i != m_currentTriggerParts.size(); ++i )
				  {
					std::cout << m_currentTriggerParts[i].softclauses.size() << " (" << m_currentTriggerParts[i].depth << "), ";
					sum += (uint32_t)m_currentTriggerParts[i].softclauses.size();
				  }
				std::cout << " (" << sum << "," << m_softclauses.size() << ")" << std::endl;
				assert( sum <= m_softclauses.size() );
			  }

			// We solve the last part -> we can "unit" the bounds 
			if( m_currentTriggerParts.front().softclauses.size() >= m_softclauses.size() )
			  { maxmode = 5; }

			if( m_maxInprocess )
			  { currentresult = preprocess(e_in); }
			else
			  { currentresult = ANTOM_UNKNOWN; }

			// The part to solve is always in front of "m_partialTriggerParts"
			tempassumptions = collectedAssumptions;
			for( uint32_t i = 0; i != externalAssumptions.size(); ++i )
			  { tempassumptions.push_back(externalAssumptions[i]); }

			currentresult = maxSolve( tempassumptions, partialoptimum, maxmode );
			m_control->setSumTime(true);

			m_currentTriggerParts.front().optimum = partialoptimum;

			if( currentresult == ANTOM_SAT )
			  {
				result = ANTOM_SAT;

				uint32_t alloptimum = updateTriggerOptimum();
				currentoptimum = partialoptimum - alloptimum;
				
				if( currentoptimum < optimum )
				  { 
					optimum = currentoptimum;
					if ( m_control->getVerbosity() > 0 )
					  { 
						if ( m_control->getVerbosity() > 0 )
						  { 
							std::cout << "o " << currentoptimum << std::endl; 
							if( m_control->getVerbosity() > 1 )
							  {
								getrusage(RUSAGE_SELF, &resources); 
								double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
								std::cout << "c " << (timeC-timeS) << "s" << std::endl;
							  }
						  }
					  }
				  }

				if( partialoptimum < size )
				  {
					uint32_t lit = (m_currentTriggerParts.front().currenttrigger[size-partialoptimum-1]<<1)^1;
					m_currentTriggerParts.front().assumption = lit;
				  }

				if ( m_control->getVerbosity() > 1 )
				  { std::cout << "c partial optimum: " << currentoptimum << std::endl; } 
			  }
			else if( currentresult == ANTOM_UNSAT )
			  {
				m_control->setSumTime(false);
				if( m_control->getIncrementalMode() > 0 )
				  { 
					invalidateSoftClauses(); 
				  }
				return ANTOM_UNSAT;
			  }
			// Timeout
			else if( currentresult == ANTOM_UNKNOWN )
			  {
				assert( m_control->getCPULimit() > 0.0 );
				if( m_control->getIncrementalMode() > 0 )
				  { 
					invalidateSoftClauses(); 
				  }
				m_control->setSumTime(false);
				return ANTOM_UNKNOWN;				
			  }

			// We have only one current part left (not the last one)
			// Then we can "unit" the upper bound
			if( ( m_currentTriggerParts.size() == 1 ) && ( m_currentTriggerParts.front().softclauses.size() < m_softclauses.size() ) && ( ( size-partialoptimum ) < m_currentTriggerParts.front().size() ) )
			  {
					
				uint32_t lit = (m_currentTriggerParts.front().currenttrigger[size-partialoptimum]<<1);
#ifndef NDEBUG
				bool rst = addUnit(lit); assert(rst);
#else
				addUnit(lit);
#endif
			  }
		  	// Do until one part is left and all parts are considered
		  } while ( m_currentTriggerParts.front().softclauses.size() < size );

		assert( (m_currentTriggerParts.size() == 1 ) && m_partialTriggerParts.empty() );
		
		
		break;	
	  case 1:
		// Breadth-first mode

		// get first depth
		tempassumptions = collectedAssumptions;
		for( uint32_t i = 0; i != externalAssumptions.size(); ++i )
		  { tempassumptions.push_back(externalAssumptions[i]); }

		currentresult = calcFirstDepth( result, currentoptimum, optimum, tempassumptions, maxmode );

		if( currentresult == ANTOM_UNSAT )
		  {
			m_control->setSumTime(false);
			if( m_control->getIncrementalMode() > 0 )
			  { 
				invalidateSoftClauses(); 
			  }
			return ANTOM_UNSAT;
		  }
		// Timeout
		else if( currentresult == ANTOM_UNKNOWN )
		  {
			assert( m_control->getCPULimit() > 0.0 );
			if( m_control->getIncrementalMode() > 0 )
			  { 
				invalidateSoftClauses(); 
			  }
			m_control->setSumTime(false);
			return ANTOM_UNKNOWN;				
		  }
		
		// All soft clauses in one part -> we can stop here
		// We also stop in incomplete mode
		if( m_currentTriggerParts.size() == 1 || m_incompleteMode )
		  { break; }

		// Now start merging sorters
		do
		  {
			// Now merge sorters together
			Antom::Trigger tempVariables = m_currentTriggerParts.back();
			m_currentTriggerParts.pop_back();

			// Get next element to merge
			if( !m_currentTriggerParts.empty() && tempVariables.depth == m_currentTriggerParts.back().depth )
			  {
				// next trigger
				Antom::Trigger tempVariables2 = m_currentTriggerParts.back();

				// Reset optimum for next depth if we have computed last element of current depth
				if( tempVariables.depth > depth )
				  {
					if ( m_control->getVerbosity() > 1 )
					  { std::cout << "c overall optimum for depth " << (depth+1) << ": " << currentoptimum << std::endl; }
					++depth;
					collectedAssumptions.clear();
					currentoptimum = size;
					firstsolve = true;
					
					// Clear last trigger values on new level
					// Otherwise we are not able to unit the first element of this depth
					for( uint32_t i = 0; i != m_currentTriggerParts.size(); ++i )
					  {
						for( uint32_t j = 0; j != m_currentTriggerParts[i].softclauses.size(); ++j )
						  {
							m_currentTriggerParts[i].softclauses[j].s_lastAssignment = 0;
						  }
					  }

				  }

				m_currentTriggerParts.pop_back();
				mergePartTrigger( tempVariables, tempVariables2 );

				if( tempVariables2.optimum < size)
				  {
					uint32_t lit = (tempVariables2.currenttrigger[size-tempVariables2.optimum-1]<<1)^1;
					collectedAssumptions.push_back(lit);
				  }

				// Pushed merged list at the end
				m_currentTriggerParts.push_front(tempVariables2);
			  }
			// reached last element of current depth
			else
			  { 
				++tempVariables.depth;
				// Just push the current last element to last position in order to solve it as next instance
				m_currentTriggerParts.push_front(tempVariables);
			  }

			assert( !m_currentTriggerParts.empty() );
			// At this point the current part to solve is at the end of the dequeue

			std::vector< uint32_t > localAssumptions = collectedAssumptions;

			setSoftTrigger( localAssumptions );

			uint32_t partialoptimum = size;

			if( m_control->getVerbosity() > 1 )
			  {
				uint32_t sum(0);
				std::cout << "c ";
				for( uint32_t i = 0; i != m_currentTriggerParts.size(); ++i )
				  {
					std::cout << m_currentTriggerParts[i].softclauses.size() << " (" << m_currentTriggerParts[i].depth << "), ";
					sum += (uint32_t)m_currentTriggerParts[i].softclauses.size();
				  }
				std::cout << " (" << sum << "," << m_softclauses.size() << ")" << std::endl;
				assert( sum <= m_softclauses.size() );
			  }

			// Last element -> we can "unit" bounds
			if( m_currentTriggerParts.front().softclauses.size() >= m_softclauses.size() )
			  { maxmode = 5; }

			if( m_maxInprocess )
			  { currentresult = preprocess(e_in); }
			else
			  { currentresult = ANTOM_UNKNOWN; }

			// Maximize partial sorter

			for( uint32_t i = 0; i != externalAssumptions.size(); ++i )
			  { localAssumptions.push_back(externalAssumptions[i]); }

			currentresult = maxSolve( localAssumptions, partialoptimum, maxmode );
			m_control->setSumTime(true);

			assert( currentresult == ANTOM_UNSAT || partialoptimum <= size );
			m_currentTriggerParts.front().optimum = partialoptimum;

			assert(currentresult != ANTOM_UNSAT );

			if( currentresult == ANTOM_SAT )
			  {
				result = ANTOM_SAT;
			
				currentoptimum = partialoptimum - updateTriggerOptimum();

				if ( m_control->getVerbosity() > 1 )
				  { std::cout << "c current optimum: " << currentoptimum << std::endl; } 

				if ( maxmode != 5 && ( m_control->getVerbosity() > 0 ) && ( currentoptimum < optimum ) )
				  { 
					optimum = currentoptimum;
					std::cout << "o " << optimum << std::endl; 
					if( m_control->getVerbosity() > 1 )
					  {
						getrusage(RUSAGE_SELF, &resources); 
						double timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
						std::cout << "c " << (timeC-m_control->getStartTime()) << "s" << std::endl;
					  }
				  }
				
				if( size != partialoptimum )
				  {
					uint32_t pos(size-partialoptimum-1);
					uint32_t lit((m_currentTriggerParts.front().currenttrigger[pos]<<1)^1);

					// if( m_incompleteMode )
					//   { addUnit(lit); }
					// else
					//   {	collectedAssumptions.push_back( lit ); }

					collectedAssumptions.push_back( lit );
				  }

				// "unit" bounds for the first element
				// Except for very last unit. This unit is already added in opposite polarty in "maxSolve"
				if( firstsolve && (maxmode != 5 ) && ((size-partialoptimum)<m_currentTriggerParts.front().size() ))
				  {
					uint32_t lit = (m_currentTriggerParts.front().currenttrigger[size-partialoptimum]<<1);
#ifndef NDEBUG
					bool rst = addUnit(lit); assert(rst);
#else
					addUnit(lit);
#endif
				  }
				firstsolve = false;
			  }
			// Timeout
			else if( currentresult == ANTOM_UNKNOWN )
			  {
				assert( m_control->getCPULimit() > 0.0 );
				if( m_control->getIncrementalMode() > 0 )
				  { invalidateSoftClauses(); }
				m_control->setSumTime(false);
				return ANTOM_UNKNOWN;				
			  }

		  } while( m_currentTriggerParts.size() > 1 );

		break;
	  default:
		std::cout << "Error: unknown mode " << mode << std::endl;
		assert( false );
		break;
	  }

	optimum = currentoptimum;
	if ( m_control->getVerbosity() > 1 )
	  {
		std::cout << "c comparator: " << m_comparator << " skipped: " << m_skipped << std::endl;
	  }

	m_control->setSumTime(false);
	if( m_control->getIncrementalMode() > 0 )
	  { invalidateSoftClauses(); }
	return result;
  }
  
  uint32_t Antom::updateTriggerOptimum( void )
  {
	uint32_t result(0);
	// proceed current considered trigger parts
	// Skip result of current first element
	size_t size(m_currentTriggerParts.size());
	for( size_t i = 1; i < size; ++i )
	  {
		bool unproceeded = false;
		// is "m_currentTriggerParts[i]" already solved at current depth?
		if( m_currentTriggerParts[i].depth < m_currentTriggerParts[0].depth )
		  { unproceeded = true; }
		uint32_t pos = countSatisfiedSoftClauses( model(), m_currentTriggerParts[i], unproceeded );
		m_currentTriggerParts[i].optimum = (uint32_t)m_softclauses.size() - pos;
		result += pos;
	  }

	// proceed non builded trigger parts
	size = m_partialTriggerParts.size();
	for( size_t i = 0; i < size; ++i )
	  {
		uint32_t pos(countSatisfiedSoftClauses( model(), m_partialTriggerParts[i], true ));
		m_partialTriggerParts[i].optimum = (uint32_t)m_softclauses.size() - pos;
		result += pos;
	  }
	return result;
  }

  void Antom::calcSplitWidth( void )
  {
	uint32_t parts(1);
	uint32_t splitwidth((uint32_t)m_softclauses.size());

	if( m_maxWidth != 0 )
	  {
		// First get largest power of 2 number below "m_maxWidth"
		uint32_t factor( 1 );
		while ( ( factor * m_maxWidth ) < splitwidth )
		  { factor <<= 1; }

		// If there is any left over split into "(largest power of 2 number) - 1 + rest" parts
		m_splittedWidth = splitwidth/factor;

		if( (splitwidth%factor) != 0 )
		  { ++m_splittedWidth; }
	  }

	if ( m_maxParts != 0 )
	  {
		while ( parts > m_maxParts )
		  { splitwidth = splitwidth<<1; parts = parts>>1; }
		m_splittedWidth = splitwidth;
	  }
  }
  
  void Antom::setSplittedWidth( uint32_t width )
  { assert( width > 0 ); m_splittedWidth = width; }

  void Antom::setMaxWidth( uint32_t width )
  { m_maxWidth = width; }

  void Antom::setMaxParts( uint32_t parts )
  { m_maxParts = parts; }

  void Antom::setSortSoftClauses( uint32_t val )
  { assert( val < 4 ); m_sortsoftclauses = val; }

  void Antom::setSkip( bool val ) { m_doskipping = val; }
  void Antom::setCSC( uint32_t val ) { m_setCSC = val; }
  void Antom::setTrigger( bool val ) { m_setTrigger = val; }
  void Antom::setIncompleteMode( bool val ) { m_incompleteMode = val; }

  void Antom::setGridMode( uint32_t val ) { assert( val < 4 ); m_bypassGrid = val; }
  void Antom::setHorizontalWidth( uint32_t val ) { assert( val > 0 ); m_horizontalwidth = val; }

  void Antom::setNetworktype( uint32_t val ) { assert( val < 3 ); m_networktype = val; }

  void Antom::checkAllConflictingSoftclauses( void )
  {
	if( m_setCSC != 2 )
	  { return; }

	size_t size = m_softclauses.size();

	if( m_control->getVerbosity() > 1 )
	  { std::cout << "c " << __func__ << " " << size << std::endl; }

	uint32_t bypasses(0);
	uint32_t unsats(0);

	for( size_t i = 0; i != size; ++i )
	  {
		std::vector< uint32_t > assumptions;
		uint32_t lit( m_softclauses[i].s_triggerlit );
		assumptions.push_back( lit^1 );

		// Deduce activation of current soft clause
		bool rst = deduceAssumptions(assumptions);
		m_softclauses[i].s_contra = 0;
		m_softclauses[i].s_simultan = 0;

		// Instance is not solveable if current soft clause is activated
		if( !rst )
		  {
			rst = addUnit( lit ); assert( rst );
			++unsats;
		  }			
		else
		  {
			std::vector< uint32_t > solvermodel = model();

			// Check model
			for( uint32_t j = 0; j < size; ++j )
			  {
				uint32_t checklit( m_softclauses[j].s_triggerlit );
				assert( (checklit>>1) < solvermodel.size() );
				// Contradiction... j'th soft clause is deactivated if i'th soft clause is activated
				if( solvermodel[checklit>>1] == checklit )
				  {
					++bypasses;
					++m_softclauses[i].s_contra;
					std::vector < uint32_t > clause( 2, 0 );
					clause[0] = lit;
					clause[1] = checklit;
					rst = addClause(clause); assert(rst);
				  }
				// The i'th and j'th soft clause can be activated at once
				else if( ( i != j ) && ( solvermodel[checklit>>1] == (checklit^1) ) )
				  {
					++bypasses;
					++m_softclauses[i].s_simultan;
					std::vector < uint32_t > clause( 2, 0 );
					clause[0] = lit;
					clause[1] = (checklit)^1;
					rst = addClause(clause); assert(rst);
				  }
			  }
		  }
	  }

	if( m_control->getVerbosity() > 1 )
	  { 
		std::cout << "c find overall " << bypasses << " bypasses and " << unsats << " unsats" << std::endl; }
	
	if( m_sortsoftclauses == 1 )
	  { std::sort( m_softclauses.begin(), m_softclauses.end(), compareSoftclauses ); }
	else if( m_sortsoftclauses == 2 )
	  {	std::sort( m_softclauses.rbegin(), m_softclauses.rend(), compareSoftclauses ); }
	else if ( m_sortsoftclauses == 3 )
	  {	std::random_shuffle(m_softclauses.begin(),m_softclauses.end());  }
  }

  // Search in soft clauses for sorter bypasses by "deduceAssumption"
  void Antom::findSorterCSC( Antom::Trigger& trigger )
  {
	if( m_setCSC == 0 )
	  { return; }

	uint32_t size = trigger.size();
	size_t softclausessize = trigger.softclauses.size();

	if( m_control->getVerbosity() > 1 )
	  { std::cout << "c " << __func__ << " " << size << std::endl; }

	trigger.mincontra = size;
	trigger.maxsimultan = 0;
	uint32_t unsats(0);
	uint32_t bypasses(0);

	for ( size_t i = 0; i != softclausessize; ++i )
	  {
		std::vector< uint32_t > assumptions;
		uint32_t lit( trigger.softclauses[i].s_triggerlit );

		trigger.softclauses[i].s_contra = 0;
		trigger.softclauses[i].s_simultan = 0;

		assumptions.push_back( lit^1 );

		// Deduce activation of current soft clause
		bool rst = deduceAssumptions(assumptions);

		// Instance is not satisfied if current soft clause is activated
		if( !rst )
		  {
			rst = addUnit( lit ); assert( rst );
			++unsats;
		  }
		else
		  {
			std::vector< uint32_t > solvermodel = model();

			// Check model
			for( uint32_t j = 0; j != softclausessize; ++j )
			  {
				uint32_t checklit( trigger.softclauses[j].s_triggerlit );
				assert( (checklit>>1) < solvermodel.size() );
				// Contradiction... j'th soft clause is deactivated if i'th soft clause is activated
				if( solvermodel[checklit>>1] == checklit )
				  {
					++trigger.softclauses[i].s_contra;
					++bypasses;

					std::vector < uint32_t > clause( 2, 0 );
					clause[0] = lit;
					clause[1] = checklit;
					rst = addClause(clause); assert(rst);
				  }
				// The i'th and j'th soft clause can be activated at once
				else if( ( i != j ) && ( solvermodel[checklit>>1] == (checklit^1) ) )
				  {
					++trigger.softclauses[i].s_simultan;
					++bypasses;

					std::vector < uint32_t > clause( 2, 0 );
					clause[0] = lit;
					clause[1] = checklit^1;
					rst = addClause(clause); assert(rst);
				  }
			  }

			if( trigger.mincontra > trigger.softclauses[i].s_contra )
			  { 
				trigger.mincontra = trigger.softclauses[i].s_contra; 
			  }
			if( trigger.maxsimultan < trigger.softclauses[i].s_simultan )
			  { trigger.maxsimultan = trigger.softclauses[i].s_simultan; }
		  }
	  }

	if( m_control->getVerbosity() > 1 )
	  { 
		std::cout << "c find overall " << bypasses << " bypasses and " << unsats << " unsats" << std::endl; 
	  }
	trivialAssignment();
	return;
  }

  // Set clause bypasses in sorter, given by found trivial cases in "findSorterBypasses()"
  // Assumes that the triggervariables in "m_currentTriggerParts" are up to date
  void Antom::setSorterCSC( Antom::Trigger& trigger )
  {
	if( m_setCSC == 0 )
	  { return; }

	// No of soft clauses in this part
	uint32_t noofsoftclauses((uint32_t)trigger.size());
	uint32_t softclausessize((uint32_t)trigger.softclauses.size());
	uint32_t diff(noofsoftclauses - softclausessize);
	
	if ( trigger.maxsimultan > 0 )
	  {
		uint32_t var( trigger.currenttrigger[trigger.maxsimultan-1] );
#ifndef NDEBUG
		bool rst = addUnit( (var<<1)^1 ); assert( rst );
#else
		addUnit( (var<<1)^1 );
#endif
	  }

	if ( trigger.mincontra < noofsoftclauses && trigger.mincontra > 0 )
	  {
		uint32_t var( trigger.currenttrigger[noofsoftclauses-trigger.mincontra-diff] );
#ifndef NDEBUG
		bool rst = addUnit( var<<1 ); assert( rst );
#else
		addUnit( var<<1 );
#endif
	  }

	for( uint32_t i = 0; i != softclausessize; ++i )
	  {
		uint32_t varcontra = trigger.softclauses[i].s_contra;
		if( varcontra > 0 && varcontra < noofsoftclauses )
		  {
			uint32_t triggerlit( trigger.softclauses[i].s_triggerlit );
			uint32_t lit( trigger.currenttrigger[noofsoftclauses-varcontra-diff]<<1 );
				
			std::vector < uint32_t > clause( 2, 0 );
			clause[0] = triggerlit;
			clause[1] = lit;
#ifndef NDEBUG
			bool rst = addClause(clause); assert(rst);
#else
			addClause(clause);
#endif
		  }

	  }
  }

  // Adds last assignment of soft triggers to "assumptions"
  void Antom::setSoftTrigger( std::vector< uint32_t >& assumptions )
  {
	if( !m_setTrigger )
	  { return; }

	Antom::Trigger& trigger = m_currentTriggerParts.front();
	// Deactive current trigger
	for( uint32_t i = 0; i != trigger.softclauses.size(); ++i )
	  {	
		trigger.softclauses[i].s_lastAssignment = -1; 
	  }

	// Add last assignment of soft triggers to assumptions

	// proceed proceeded parts
	for( uint32_t i = 1; i < m_currentTriggerParts.size(); ++i )
	  {
		const Antom::Trigger& trig = m_currentTriggerParts[i];
		for( uint32_t j = 0; j != trig.softclauses.size(); ++j )
		  {
			const Antom::softclause& sclause = trig.softclauses[j];
			if( sclause.s_lastAssignment == 0 )
			  {	assumptions.push_back( sclause.s_triggerlit ); }
			else
			  {
				assert( sclause.s_lastAssignment > 0 );
				assumptions.push_back( sclause.s_lastAssignment );
			  }
		  }
	  }

	// proceed unproceeded parts
	for( uint32_t i = 0; i != m_partialTriggerParts.size(); ++i )
	  {
		const Antom::Trigger& trig = m_partialTriggerParts[i];
		for( uint32_t j = 0; j != trig.softclauses.size(); ++j )
		  {
			const Antom::softclause& sclause = trig.softclauses[j];
			// If there is no last assignemt, deactive soft clause
			assert( sclause.s_lastAssignment == 0 );
			assumptions.push_back( sclause.s_triggerlit );
		  }
	  }
  }

  void Antom::setVerticalBypasses( const Antom::Trigger& trigger )
  {
	std::vector< uint32_t > newclause;
	std::vector< uint32_t > input( trigger.currenttrigger );
  	setDontTouch(input[0]);
				
	// Add additional contraints to the sorter network interface
	for (uint32_t i = 1 ; i < input.size(); ++i)
	  {
		if( ( input[i] != input[i-1] ) && (m_bypassGrid == 2 || m_bypassGrid == 3 ) )
		  {
			newclause.clear();
			// temp[i-1] == 1 -> temp[i]==1
			// temp[i] == 0 -> temp[i-1]==0
			newclause.push_back( (input[i-1]<<1)^1 );
			newclause.push_back( input[i]<<1 );

			++m_verticalbypasses;

			if( m_control->getIncrementalMode() > 0 )
			  {
				// Add trigger literal
				newclause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 );
			  }

#ifndef NDEBUG
			bool rst = addClause(newclause); assert(rst);
#else
			addClause(newclause);
#endif
		  }
		setDontTouch(input[i]);
	  }
  }

  void Antom::setHorizontalBypasses( const std::vector< uint32_t >& inputA, const std::vector< uint32_t >& inputB, const Trigger& trigger )
  {
	if( m_bypassGrid != 1 && m_bypassGrid != 3 )
	  { return; }

	std::vector< uint32_t > newclause;
	newclause.reserve(2);

	size_t sizeA = inputA.size();
#ifndef NDEBUG
	size_t sizeB = inputB.size();
	assert( sizeA == sizeB );
	bool rst(false);
#endif

	for( size_t i = 0; i != sizeA; ++i )
	  {
		if ( ( i != 0 ) && ( (i&3) != 3 ) )
		  { continue; }

		// skip trivial parts
		if( model()[inputA[i]] == 0 )
		  { 
			if( model()[trigger.currenttrigger[i+sizeA]] == 0 )
			  {
				// "Forward bypass"
				// A[i] == 1 => trigger[i+size] == 1
				newclause.clear();
				newclause.push_back((inputA[i]<<1)^1);
				newclause.push_back(trigger.currenttrigger[i+sizeA]<<1);

				if( m_control->getIncrementalMode() > 0 )
				  {
					// Add trigger literal
					newclause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 );
				  }

#ifndef NDEBUG
				rst = addClause(newclause); assert(rst);			
#else
				addClause(newclause);
#endif
				++m_horizontalbypasses;
			  }

			if( model()[trigger.currenttrigger[i]] == 0 )
			  {
				// "Backward bypass"
				// A[i] == 0 => trigger[i] == 0
				newclause.clear();
				newclause.push_back(inputA[i]<<1);
				newclause.push_back( (trigger.currenttrigger[i]<<1)^1);

				if( m_control->getIncrementalMode() > 0 )
				  {
					// Add trigger literal
					newclause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 );
				  }

#ifndef NDEBUG
				rst = addClause(newclause); assert(rst);			
#else
				addClause(newclause);
#endif
				++m_horizontalbypasses;
			  }
		  }

		if( model()[inputB[i]] == 0 )
		  { 
			if( model()[trigger.currenttrigger[i+sizeA]] == 0 )
			  {
				// "Forward bypass"
				// B[i] == 1 => trigger[i+size] == 1
				newclause.clear();
				newclause.push_back((inputB[i]<<1)^1);
				newclause.push_back(trigger.currenttrigger[i+sizeA]<<1);

				if( m_control->getIncrementalMode() > 0 )
				  {
					// Add trigger literal
					newclause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 );
				  }

#ifndef NDEBUG
				rst = addClause(newclause); assert(rst);			
#else
				addClause(newclause);
#endif
				++m_horizontalbypasses;
			  }
			if( model()[trigger.currenttrigger[i]] == 0 )
			  {
				// "Backward bypass"
				// B[i] == 0 => trigger[i] == 0
				newclause.clear();
				newclause.push_back(inputB[i]<<1);
				newclause.push_back( (trigger.currenttrigger[i]<<1)^1);

				if( m_control->getIncrementalMode() > 0 )
				  {
					// Add trigger literal
					newclause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 );
				  }

#ifndef NDEBUG
				rst = addClause(newclause); assert(rst);			
#else
				addClause(newclause);
#endif
				++m_horizontalbypasses;
			  }
		  }
	  }
  }

  // Deletes the soft clause datastructure and all clauses containing these clauses
  void Antom::invalidateSoftClauses ( void )
  {
	assert( m_control->getIncrementalMode() > 0 );

	// Set triggers to true, i.e. invalid softclauses
	for ( uint32_t i = 0; i != m_softclauses.size(); ++i )
	  {
		assert( m_lastIndex < (m_softclauses[i].s_triggerlit>>1) );

		// Remove "don't touch" status for soft clause variables
		for( uint32_t pos = 0; pos != m_softclauses[i].s_clause.size(); ++pos )
		  { setDontTouch(m_softclauses[i].s_clause[pos]>>1, false); }
	  }

	// clear soft clause data structure
	m_softclauses.clear();
	m_partialTriggerParts.clear();
	m_currentTriggerParts.clear();

	assert( m_lastIndex < m_globalPropertyTrigger[m_stacksize] );
	// reset trigger
	m_globalPropertyTrigger[m_stacksize] = 0;

	// Delete variables and clauses from last time step
	clearVariables(m_lastIndex+1, m_core[m_sID]->variables());

	// Reset max variable index to "m_lastIndex", the datastructure capacity is conserved
	setMaxIndex(m_lastIndex);

	for (uint32_t t = 0; t < m_threads; ++t) 
	  { 
		m_preprocessor[t]->setPreVarIndex(m_lastIndex+1); 
		m_preprocessor[t]->setPreClauseIndex(); 
	  }

	// Checks, whether all clauses with variable index > "m_lastIndex" are deleted
	assert( m_core[m_sID]->checkMaxIndex(m_lastIndex) );
  }

  void Antom::createNextPartialMaximizer( void )
  {
  	assert( !m_partialTriggerParts.empty() );
  	// clear model
  	trivialAssignment();

  	Antom::Trigger trigger = m_partialTriggerParts.back();
  	m_partialTriggerParts.pop_back();

	findSorterCSC(trigger);

  	createMaximizer(trigger);

  	setSorterCSC(trigger);
  }

  // Pushes new part in front of "currentTriggerParts"
  void Antom::createMaximizer ( Antom::Trigger& trigger )
  {
	uint32_t size = trigger.size();

	if( size == 0 )
	  { return; }

	assert( ( m_triggervar != 0 ) || ( m_control->getIncrementalMode() == 0 ) );

	// if( m_triggervar == 0 )
	//   { 
	// 	m_triggervar = newVariable();
	// 	addUnit(m_triggervar<<1);
	//   }

	if( m_control->getIncrementalMode() > 0 )
	  { 
		// Last original variable index is the one before the global property
		// Assumes that new softclauses were added
		assert( m_globalPropertyTrigger[m_stacksize] != 0 );
		m_lastIndex = m_globalPropertyTrigger[m_stacksize]-1;
	  }

	// clear model
	trivialAssignment();

	uint32_t n = antom::smallestPowerOfTwoLargerThan(size);
	// Creates and adds sorter network clauses
	switch( m_networktype )
	  {
	  case 0:
		bitonicSort( trigger, 0, size, false );
		break;
	  case 1:
		for( uint32_t i = size; i < n; ++i )
		  {
			uint32_t dummyvar = m_triggervar;
			trigger.currenttrigger.push_back( dummyvar );
		  }
		size = trigger.size();

		oddEvenSort( trigger, 0, size );
		break;
	  case 2:
		assert(false);
		// TODO
		break;
	  default:
		assert(false);
		break;
	  }

	setVerticalBypasses(trigger);

	m_currentTriggerParts.push_front( trigger );

	assert( m_triggerlists.size() > m_stacksize );
	m_triggerlists[m_stacksize] = trigger.currenttrigger;
  }  

  // Create multiple maximizer for all soft clauses of size "k"
  void Antom::createPartialMaximizer( uint32_t part )
  {

	uint32_t softsize((uint32_t)m_softclauses.size());
	Antom::Trigger trigger(m_splittedWidth);

	uint32_t s( part*m_splittedWidth );
	uint32_t maxsize(s+m_splittedWidth);

	if( softsize < maxsize )
	  { 
		maxsize = softsize;
	  }

	for( ; s < maxsize; ++s )
	  { 
		trigger.currenttrigger.push_back(m_softclauses[s].s_triggerlit>>1);
		trigger.softclauses.push_back(m_softclauses[s]);
	  }

	findSorterCSC(trigger);

	createMaximizer(trigger);

	setSorterCSC(trigger);
  }

  // Helper functions to generate the "Bitonic Sorting Network" used for (partial) MaxSAT solving.
  // See "http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/bitonic/oddn.htm" for more details. 
  void Antom::bitonicSort( Antom::Trigger& trigger, uint32_t lo, uint32_t n, bool dir )
  {
	assert( m_control->getIncrementalMode() == 0 || m_globalPropertyTrigger[m_stacksize] != 0 );

    if (n > 1)
      {
		uint32_t m(n >> 1);
		bitonicSort(trigger, lo, m, !dir);
		bitonicSort(trigger, lo + m, n - m, dir);
		bitonicMerge(trigger, lo, n, dir);
      }
  }

  void Antom::bitonicMerge( Antom::Trigger& trigger, uint32_t lo, uint32_t n, bool dir )
  {
    if (n > 1)
      {
		uint32_t m(antom::greatestPowerOfTwoLessThan(n));
		for (uint32_t i = lo; i < (lo + n - m); ++i)
		  { bitonicCompare(trigger, i, i + m, dir); }
		bitonicMerge(trigger, lo, m, dir);
		bitonicMerge(trigger, lo + m, n - m, dir);
      }
  }

  void Antom::bitonicCompare( Antom::Trigger& trigger, uint32_t i, uint32_t j, bool dir )
  {
	// Don't do anything if current trigger is trivally true/false
	// If the "left" trigger is true or the "right" trigger is false -> swap (shift true to "left")
	if( m_doskipping && ( model()[trigger.currenttrigger[i]] != 0 || model()[trigger.currenttrigger[j]] != 0 ) )
	 { 
		++m_skipped;

		if( dir && ( model()[trigger.currenttrigger[j]] == (trigger.currenttrigger[j]<<1) ||
					 model()[trigger.currenttrigger[i]] == ( (trigger.currenttrigger[i]<<1)^1 ) ) )
		  { 
			std::swap( trigger.currenttrigger[i], trigger.currenttrigger[j] ); 
		  }
		else if ( !dir && ( model()[trigger.currenttrigger[i]] == (trigger.currenttrigger[i]<<1) ||
							model()[trigger.currenttrigger[j]] == ( (trigger.currenttrigger[j]<<1)^1 ) ) )
		  { 
			std::swap( trigger.currenttrigger[i], trigger.currenttrigger[j] ); 
		  }

		// If the "left" trigger is false or the "right" trigger is true -> do nothing (shift false to "right")
		return;
	  }

	++m_comparator;
	  
	// Get two fresh variables not used by solver so far.
    uint32_t v1(newVariable());
    uint32_t v2(newVariable()); 

    // Initialization.
    std::vector<uint32_t> clause; 
#ifndef NDEBUG
    bool result(false); 
#endif

    // Encode "v1 = trigger[i] OR trigger[j]".
	clause.push_back(v1 << 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1)^1); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
    clause.push_back(v1 << 1); 
	clause.push_back( (trigger.currenttrigger[j]<<1)^1); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
    clause.push_back((v1 << 1) ^ 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1) ); 
	clause.push_back( (trigger.currenttrigger[j]<<1) ); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    // Encode "v2 = trigger[i] AND trigger[j]".
    clause.clear(); 
    clause.push_back((v2 << 1) ^ 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1) ); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
	clause.push_back((v2 << 1) ^ 1); 
	clause.push_back( (trigger.currenttrigger[j]<<1) ); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }
	
#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
    clause.push_back(v2 << 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1)^1); 
    clause.push_back( (trigger.currenttrigger[j]<<1)^1); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif
      
    // Finally, update "trigger".
    if (dir)
      { trigger.currenttrigger[i] = v1; trigger.currenttrigger[j] = v2; } 
    else
      { trigger.currenttrigger[i] = v2; trigger.currenttrigger[j] = v1; } 
  }

    /** sorts a piece of length n of the array
     *  starting at position lo
     */
  void Antom::oddEvenSort( Antom::Trigger& trigger, uint32_t lo, uint32_t n)
  {
	if (n>1)
	  {
		//uint32_t m = n>>1;
		uint32_t m(antom::greatestPowerOfTwoLessThan(n));
		oddEvenSort( trigger, lo, m);
		oddEvenSort( trigger, lo+m, m);
		oddEvenMerge( trigger, lo, n, 1);
	  }
    }
  
    /** lo is the starting position and
     *  n is the length of the piece to be merged,
     *  r is the distance of the elements to be compared
     */
	void Antom::oddEvenMerge( Antom::Trigger& trigger, uint32_t lo, uint32_t n, uint32_t r)
    {
	  uint32_t m = r<<1;

	  if ( m < n )
        {
		  oddEvenMerge(trigger, lo, n, m);      // even subsequence
		  oddEvenMerge(trigger, lo+r, n, m);    // odd subsequence

		  for (int i=lo+r; i+r<lo+n; i+=m)
			{ oddEvenCompare(trigger, i, i+r); }
        }
	  else
		{
		  oddEvenCompare(trigger, lo, lo+r);
		}
    }

  void Antom::oddEvenCompare( Antom::Trigger& trigger, uint32_t i, uint32_t j )
  {
	// Don't do anything if current trigger is trivally true/false
	// If the "left" trigger is true or the "right" trigger is false -> swap (shift true to "left")
	if( model()[trigger.currenttrigger[i]] != 0 || model()[trigger.currenttrigger[j]] != 0 )
	 { 
		++m_skipped;

		if( ( model()[trigger.currenttrigger[i]] == (trigger.currenttrigger[i]<<1) ||
			  model()[trigger.currenttrigger[j]] == ( (trigger.currenttrigger[j]<<1)^1 ) ) )
		  { 
			std::swap( trigger.currenttrigger[i], trigger.currenttrigger[j] ); 
		  }

		// If the "left" trigger is false or the "right" trigger is true -> do nothing (shift false to "right")
		return;
	  }

	++m_comparator;

	// Get two fresh variables not used by solver so far.
    uint32_t v1(newVariable());
    uint32_t v2(newVariable()); 

    // Initialization.
    std::vector<uint32_t> clause; 
#ifndef NDEBUG
    bool result(false); 
#endif

    // Encode "v1 = trigger[i] OR trigger[j]".

	clause.push_back(v1 << 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1)^1); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
    clause.push_back(v1 << 1); 
	clause.push_back( (trigger.currenttrigger[j]<<1)^1); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
    clause.push_back((v1 << 1) ^ 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1) ); 
	clause.push_back( (trigger.currenttrigger[j]<<1) ); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    // Encode "v2 = trigger[i] AND trigger[j]".

    clause.clear(); 
    clause.push_back((v2 << 1) ^ 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1) ); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
	clause.push_back((v2 << 1) ^ 1); 
	clause.push_back( (trigger.currenttrigger[j]<<1) ); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }
	
#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif

    clause.clear(); 
    clause.push_back(v2 << 1); 
	clause.push_back( (trigger.currenttrigger[i]<<1)^1); 
    clause.push_back( (trigger.currenttrigger[j]<<1)^1); 

	if( m_control->getIncrementalMode() > 0 )
	  { clause.push_back( m_globalPropertyTrigger[m_stacksize]<<1 ); }

#ifndef NDEBUG
    result = addClause(clause); assert(result); 
#else
	addClause(clause);
#endif
      
    // Finally, update "trigger".
	trigger.currenttrigger[i] = v2; trigger.currenttrigger[j] = v1;
  }
}
