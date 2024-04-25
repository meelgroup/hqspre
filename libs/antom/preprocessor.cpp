
/********************************************************************************************
preprocessor.cpp -- Copyright (c) 2014, Sven Reimer

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

#include "preprocessor.hpp"
#include "solverstate.hpp"

/* For all routines:
   Add an extra loop, if something changes after unitPropagation, consider the subroutine again
   
   So far:
   At the end of every subroutine unitPropagation is performend, the subroutine does not take the result of the propagation into account
 */

namespace antom {

  // Constructor
  Preprocessor::Preprocessor ( Core* core ) :
	p_core( core ),	 
	p_control(core->m_control),
	p_emptyClause(core->m_emptyClause),
	p_variables(core->m_variables),
	p_dsImplIndex(core->m_dsImplIndex),
	p_dsEndIndex(core->m_dsEndIndex),
	p_decisionLevel(core->m_decisionLevel),
	p_assignment(core->m_assignment),
	p_level(core->m_level),
	p_decisionStack(core->m_decisionStack),
	p_model(core->m_model),
	p_forcing(core->m_forcing),
	p_deleted(core->m_deleted),
	p_clauseDatabase(core->m_clauseDatabase),
	p_binaries(core->m_watches),
	p_ca(core->m_ca),
	// initialize data structures
	p_occur(),
	p_replacedby(),
	p_donttouch(),
	p_uplaactivity(),
	p_uplaheap(p_uplaactivity),
	p_replaces(),
	p_elimclauses(),
	p_firstPreVarIndex(1),
	p_firstPreClauseIndex(1),
	p_maxloops(1000000),
	p_lastImplIndex(1),
	p_dosubsumption(true),
	p_doupla(true),
	p_dovarelimination(true),
	p_costVal(10),
	p_increaseVal(0),
	p_statistics(core->m_statistics)
  {
	assert(p_control != NULL );
  }

  // Simplifies the current CNF formula by performing some preprocessing steps.
  // Returns ANTOM_UNSAT if the formula is unsatisfiable, otherwise ANTOM_UNKNOWN
  uint32_t Preprocessor::preprocess (  preprotype type  )
  {
	// If the solver is not on decision level 0, we might have a problem.
	assert(p_decisionLevel == 0);

	if( p_emptyClause )
	  { return ANTOM_UNSAT; }

	if( type == e_in )
	  { 
		++p_statistics.inprocessings; 
		if( p_control->getVerbosity() > 1 )
		  { std::cout << "c Inprocessing No. " << p_statistics.inprocessings << std::endl; }
	  }

	double timeC(0.0);
	struct rusage resources;
	getrusage(RUSAGE_SELF, &resources);
	double timeS = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
	p_core->m_control->setStartTime(timeS);

	uint32_t loops(0);
	uint32_t result(ANTOM_UNKNOWN);

	// Some statistics
	uint32_t t_cons(p_statistics.constantVariables);
	uint32_t t_equiv(p_statistics.equivalentVariables);
	uint32_t t_uplacons(p_statistics.uplaConstantVariables);
	uint32_t t_uplaequiv(p_statistics.uplaEuivalentVariables);
	uint32_t t_resvars(p_statistics.resolvedVariables);
	uint32_t t_monolits(p_statistics.monotoneVariables);
	uint32_t t_dclits(p_statistics.dontcareVariables);
	uint32_t t_subsumptions(p_statistics.subsumptions);
	uint32_t t_selfsubsumptions(p_statistics.selfSubsumptions);
	uint32_t t_unitprop(p_statistics.unitPropagations);

	bool doitagain( true );
	// indicates whether something changes since last call of a sub method
	// didsomething &  0x1 (00000001) = did something in fastprocess
	// didsomething &  0x2 (00000010) = did something in subsumption
	// didsomething &  0x4 (00000100) = did something in upla
	// didsomething &  0x8 (00001000) = did something in variable elimination
	// didsomething & 0x10 (00010000) = flag for marking the first prepro loop
	uint32_t didsomething( 0x1f );

	// Extract binaries, build occurence lists
	preparePreprocessing(type);

	// Always start over in incremental mode
	if( p_control->getIncrementalMode() )
	  { p_lastImplIndex = 1; }

	p_dsImplIndex = p_lastImplIndex;

	bool fast(p_dsImplIndex != p_dsEndIndex);
	if( !propagateUnits() ) { p_control->setDone(); result = ANTOM_UNSAT; goto STATS; }
	if( !fastPreprocess(fast, type==e_incremental) ) { p_control->setDone(); result = ANTOM_UNSAT; goto STATS; }
	doitagain = fast;

	// clear fastpreprocess part
	didsomething &= 0x1e;

	// main preprocessing loop
	do {
	  ++loops;
	  
	  // clear upla part; 0x1b = 00011011
	  didsomething &= 0x1b;
	  doitagain = false;

	  // Perform UPLA?
	  // Skip UPLA in some inprocessings, since it's rather expensive
	  if( p_doupla && ( type != e_in || ( ( p_statistics.inprocessings & 0xf ) == 8 ) ) )
		{
		  // no changes since last upla? -> end loop
		  if( didsomething == 0 )
			{ break; }

		  if( !upla(didsomething, type==e_incremental) ) 
			{ p_control->setDone(); result = ANTOM_UNSAT; break; }

		  bool fast = (didsomething&0x4);
		  if( !fastPreprocess(fast, type==e_incremental) ) 
			{ p_control->setDone(); result = ANTOM_UNSAT; break; }
		  doitagain |= fast;

		  getrusage(RUSAGE_SELF, &resources); 
		  timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
		  if ( ( p_core->m_control->getCPULimit() > 0.0 ) && ( p_core->m_control->reachedTimeout(timeC) ) )
			{ 
			  return ANTOM_UNKNOWN;
			}
		}

	  // clear variable elimination part; 0x17 = 00010111
	  didsomething &= 0x17;

	  // Perform variable elimination?
	  if( p_dovarelimination )
		{
		  // no changes since last variable elimination? -> end loop
		  if( didsomething == 0 )
			{ break; }

		  if( !varElimination(didsomething, type==e_incremental) ) 
			{ p_control->setDone(); result = ANTOM_UNSAT; break; }
		  bool fast = (didsomething&0x8);
		  if( !fastPreprocess(fast, type==e_incremental) ) 
			{ p_control->setDone(); result = ANTOM_UNSAT; break; }
		  doitagain |= fast;

		  getrusage(RUSAGE_SELF, &resources); 
		  timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
		  if ( ( p_core->m_control->getCPULimit() > 0.0 ) && ( p_core->m_control->reachedTimeout(timeC) ) )
			{ 
			  return ANTOM_UNKNOWN;
			}
		}

	  // clear subsumption part; 0x1d = 00011101
	  didsomething &= 0x1d;

	  // Perform full subsumption check?
	  // Skip subsumption in some inprocessings, since it's rather expensive
	  if( p_dosubsumption && ( type != e_in || ( p_statistics.inprocessings & 0x7 ) == 4 ) )
		{
		  // no changes since last subsumption? -> end loop
		  if( didsomething == 0 )
			{ break; }

		  if( !fullSubsumptionCheck(didsomething, type==e_incremental) ) 
			{ p_control->setDone(); result = ANTOM_UNSAT; break;}
		  bool fast = (didsomething&0x2);
		  if( !fastPreprocess(fast, type==e_incremental) ) 
			{ p_control->setDone(); result = ANTOM_UNSAT; break;}
		  doitagain |= fast;

		  getrusage(RUSAGE_SELF, &resources); 
		  timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;
		  if ( ( p_core->m_control->getCPULimit() > 0.0 ) && ( p_core->m_control->reachedTimeout(timeC) ) )
			{ 
			  return ANTOM_UNKNOWN;
			}
		}

	  // clear "first loop" flag
	  didsomething &= 0x0f;

	} while( doitagain && loops <= p_maxloops && !p_core->m_control->done() );

	if( type==e_incremental )
	  {
		p_firstPreVarIndex = p_variables+1;
		p_firstPreClauseIndex = p_clauseDatabase.size()+1;
	  }

  STATS:
	if( p_control->getVerbosity() > 1 )
	  {
		std::cout << "c -----------------------------" << std::endl;
		switch( type )
		  {
		  case e_pre:
			std::cout << "c After Preprocessing " << std::endl
					  << "c prepro loops           : " << loops << std::endl;
			break;
		  case e_in:
			std::cout << "c After Inprocessing " << std::endl
					  << "c inpro loops            : " << loops << std::endl;
			break;
		  case e_incremental:
			std::cout << "c After Incremental Preprocessing " << std::endl
					  << "c prepro loops           : " << loops << std::endl;
			break;
		  default:
			assert(false);
			break;
		  }

		getrusage(RUSAGE_SELF, &resources); 
		timeC = (double) resources.ru_utime.tv_sec + 1.e-6 * (double) resources.ru_utime.tv_usec;

		std::cout << "c binary constants       : " << (p_statistics.constantVariables - t_cons) << " (" << p_statistics.constantVariables << ")" <<std::endl
				  << "c binary equivalances    : " << (p_statistics.equivalentVariables - t_equiv) << " (" << p_statistics.equivalentVariables << ")" << std::endl
				  << "c upla constants         : " << (p_statistics.uplaConstantVariables - t_uplacons) << " (" << p_statistics.uplaConstantVariables << ")" <<  std::endl
				  << "c upla equivalances      : " << (p_statistics.uplaEuivalentVariables - t_uplaequiv) << " (" << p_statistics.uplaEuivalentVariables << ")" <<  std::endl
				  << "c variable eliminations  : " << (p_statistics.resolvedVariables - t_resvars) << " (" << p_statistics.resolvedVariables << ")" <<  std::endl
				  << "c monotone variables     : " << (p_statistics.monotoneVariables - t_monolits) << " (" << p_statistics.monotoneVariables << ")" <<  std::endl
				  << "c dc variables           : " << (p_statistics.dontcareVariables - t_dclits) << " (" << p_statistics.dontcareVariables << ")" <<  std::endl
				  << "c subsumed clauses       : " << (p_statistics.subsumptions - t_subsumptions) << " (" << p_statistics.subsumptions << ")" <<  std::endl
				  << "c selfsubsumed literals  : " << (p_statistics.selfSubsumptions - t_selfsubsumptions) << " (" << p_statistics.selfSubsumptions << ")" <<  std::endl
				  << "c unit propagations      : " << (p_statistics.unitPropagations - t_unitprop) << " (" << p_statistics.unitPropagations << ")" <<  std::endl
				  << "c pre/inpro time         : " << (timeC-timeS) << "s" << std::endl;
		
	  }

	if( result == ANTOM_UNKNOWN )
	  { 
		// Rebuild watches
		updateWatches();

		// garbage collect after watchupdates, so that watches are allocated together
		p_core->checkGarbage();

		// Update implication index for next inprocessing
		p_lastImplIndex = p_dsEndIndex;
	  }

	// Everything went fine.
	return result;
  }

  // Some fast preprocessing routines, which can be called often
  bool Preprocessor::fastPreprocess( bool& didsomething, bool incremental )
  {
	assert( p_dsImplIndex == p_dsEndIndex );

	if( !detectMonotone(didsomething, incremental) ) { return false; }
	if( !findBinaryConsAndEquiv(didsomething, incremental) ) { return false; }

	return true;
  }
	
  // Resets the Preprocessor. The following status flags/variables remain untouched:
  // * The references of the core
  // * Information about replaced variables and clauses 
  // * Don't touch variables
  // * Overall statistics 
  // * DoPreprocessing and DoInprocessing flags
  void Preprocessor::reset (void)
  {
	// Reset all variable related data structures.
	for (uint32_t v = 1; v <= p_variables; ++v)
	  {
		uint32_t pLit(v << 1);
		uint32_t nLit((v << 1) ^ 1); 

		std::vector< CRef >().swap( p_occur[pLit] );
		std::vector< CRef >().swap( p_occur[nLit] );
	  }

	p_maxloops = 1000000;
	p_lastImplIndex = 1;
	p_dosubsumption = true;
	p_doupla = true;
	p_dovarelimination = true;
	p_statistics.resetPrepro();
  }

  /* Begin: some helper functions */

  // Updates all data structures depending on the number of variables to be able to handle "p_variables" variables.

  void Preprocessor::updateDataStructures( void )
  {
	p_replacedby.resize(p_variables+1, 0);
	p_donttouch.resize(p_variables+1, false);
	p_replaces.resize(p_variables+1);

	p_uplaactivity.resize(p_variables+1, 0);
	p_uplaheap.resize(p_variables);

	// Initialization.
	uint32_t max((p_variables << 1) + 2);	
	  
	p_occur.resize(max);
  }

  // Adds (lit1 + lit2) to binaries. 
  // If (lit1 + lit2) already exists, do nothing#
  // Returns false, if binary already exists
  bool Preprocessor::addBinary( uint32_t lit1, uint32_t lit2, bool learned )
  {
	// Check if new binary is already in watch list
	uint32_t firstlit(lit1);
	uint32_t seclit(lit2);
	  
	if( p_binaries[seclit].size() < p_binaries[firstlit].size() )
	  {
		firstlit = lit2;
		seclit = lit1;
	  }

	size_t f( 0 );
	size_t fsize( (uint32_t)p_binaries[firstlit].size() );
	 
	for( ; f != fsize; ++f )
	  {
		if( p_binaries[firstlit][f].getSecondLit() == seclit )
		  { break; }
	  }
	// Add new binary
	if( f == fsize )
	  {
		p_binaries[lit1].push_back(Watcher(lit2,learned));
		p_binaries[lit2].push_back(Watcher(lit1,learned));
		++p_statistics.binaryClauses += 2;

		return true;
	  }

	return false;
  }

  // Remove the "pos"th binary entry in the binary list of "lit"
  // "pos" and "size" will be updated
  void Preprocessor::removeBinary( uint32_t lit, uint32_t& pos, uint32_t& size )
  {
	p_binaries[lit][pos--] = p_binaries[lit][--size];
	p_binaries[lit].pop_back();
	--p_statistics.binaryClauses;
  }

  // Remove the binary (lit1 + lit2) from binary list of "lit1"
  void Preprocessor::removeBinary( uint32_t lit1, uint32_t lit2 )
  {
	size_t i( 0 );
	size_t size( p_binaries[lit1].size() );

	for( ; i != size; ++i )
	  {
		if( p_binaries[lit1][i].getSecondLit() == lit2 )
		  {
			p_binaries[lit1][i--] = p_binaries[lit1][--size];
			p_binaries[lit1].pop_back();
			--p_statistics.binaryClauses;
			break;
		  }
	  }

	assert( i != size );
  }

  // Removes "clause" from occurence list of "lit"
  void Preprocessor::removeFromOccurenceList ( uint32_t lit, CRef cr )
  {
	size_t osize( p_occur[ lit ].size() );
	size_t f( 0 );
	for( ; f != osize; ++f )
	  {
		if( cr == p_occur[lit][f] )
		  {
			p_occur[lit][f--] = p_occur[lit][--osize];
			p_occur[lit].pop_back();
			break;
		  }
	  }

	assert( f != osize );
  }

  // Removes every occurence of "clause"
  // Mark "clause" as "to deleted"
  void Preprocessor::clearAllOccurences( CRef cr )
  {
	Clause& clause( p_ca[cr] );
	// In case length was equal to "2", we have deleted the third literal in advance
	if( clause.length() <= 3 )
	  { --p_statistics.ternaryClauses; }
	else
	  { --p_statistics.naryClauses; }
	uint32_t size(clause.length());
	for( uint32_t pos = 0; pos != size; ++pos)
	  {
		removeFromOccurenceList( clause[pos], cr );
	  }
	
	// Mark clause as to be deleted
	clause.markForDeletion();
  }

  // Removes "literal" from clause
  // Eventually introduces new binary and mark old n-nary for deletion
  // Returns "true" if n-nary clause is deleted, "false" otherwisse
  bool Preprocessor::strengthenClause ( CRef cr, uint32_t literal, bool keepoccurence )
  {
	Clause& clause( p_ca[cr] );
	bool result(false);
	uint32_t pos( 0 );
	uint32_t qos( 0 );
	unsigned long long sign( 0 );
	uint32_t size( clause.length() );

	// Remove "literal" from clause
	for( ; pos != size; ++pos )
	  {
		if( clause[ pos ] != literal )
		  {
			clause[ qos ] = clause[ pos ];
			sign |= 1ULL << (clause[qos] % 64);
			++qos;
		  }
	  }

	assert( pos != qos );

	// Is "clause" before deletion of "literal" a ternary clause?
	// Then we got a binary
	if( clause.length() == 3 )
	  {
		assert(qos == 2 );
		// Add the new binary
		addBinary(clause[0], clause[1], clause.isLearned());

		clause.setLength( 2 );
		clearAllOccurences(cr);
		result = true;
	  }
	else
	  {
		p_ca.freeLiterals(pos-qos);
		clause.setSign(sign);
		assert( qos == (size-1) );
		clause.setLength( qos );
		if ( qos == 3 )
		  { ++p_statistics.ternaryClauses; --p_statistics.naryClauses; }
	  }

	if( !keepoccurence )
	  { removeFromOccurenceList( literal, cr ); }

	return result;
  }

  // 1. Extract all binaries of watchlist and push them in extra data structure
  // (this can also be done during "addClause", if preprocessing is enabled)
  // 2. Creates occurence lists
  // Assumes that there are no duplicated binaries in "m_watches"
  void Preprocessor::preparePreprocessing( preprotype type )
  {
	// Allocate memory for preprocessing
	updateDataStructures();

	p_statistics.usedVariables = 0;
	p_statistics.binaryClauses = 0;
	p_statistics.ternaryClauses = 0;
	p_statistics.naryClauses = 0;

	// Clear binary and n-nary occurence lists
	// Remove n-nary and ternary from watch list
	for( uint32_t v = 1; v <= p_variables; ++v )
	  {

		std::vector<CRef>().swap(p_occur[v<<1]);
		std::vector<CRef>().swap(p_occur[(v<<1)^1]);

		if( p_binaries[v<<1].empty() && p_binaries[(v<<1)^1].empty() )
		  {	continue; }

		++p_statistics.usedVariables;
		p_deleted[v] = false;

		for( uint32_t literal = (v<<1); literal < ((v<<1)+2); ++literal )
		  {	
			std::vector<Watcher>& watches( p_binaries[literal] );

			size_t size( watches.size() );

			for( size_t i = 0; i != size; ++i )
			  {
				if( !watches[i].isBinary() )
				  {
					// Add new binary
					watches[i--] = watches[--size];
					watches.pop_back();
				  }
				else
				  {
					++p_statistics.binaryClauses;
				  }
			  }

			std::sort( watches.begin(), watches.end(), WatchedSorter() );
		  }
	  }

	// Build occurence lists
	size_t size(p_clauseDatabase.size());
	for( size_t c = 0; c != size; ++c )
	  {
		// Get a pointer to the next clause.
		CRef cr( p_clauseDatabase[c] );
		Clause& clause( p_ca[cr] );

		if( clause.length() == 3 )
		  { ++p_statistics.ternaryClauses; }
		else
		  { ++p_statistics.naryClauses; }

		assert( !clause.toDelete() );

		// sort clause... needed for subsumption checks
		clause.sort();

		uint32_t size( clause.length());
		for( uint32_t pos = 0; pos != size; ++pos ) 
		  {
			p_occur[clause[pos]].push_back(cr);
		  }
	  }

	if( p_control->getVerbosity() > 1 )
	  {
		std::cout << "c ----------------------------" << std::endl;

		switch( type )
		  {
		  case e_pre:
			std::cout << "c Before Preprocessing " << std::endl;
			break;
		  case e_in:
			std::cout << "c Before Inprocessing " << std::endl;
			break;
		  case e_incremental:
			std::cout << "c Before Incremental Preprocessing " << std::endl;
			break;
		  default:
			assert(false);
			break;
		  }

		std::cout << "c #Used variables        : " << p_statistics.usedVariables << std::endl
				  << "c #Bin clauses           : " << (p_statistics.binaryClauses>>1) << std::endl
				  << "c #Ternary clauses       : " << p_statistics.ternaryClauses << std::endl
				  << "c #N-nary clauses        : " << p_statistics.naryClauses << std::endl
				  << "c #Total clauses         : " << ((p_statistics.binaryClauses>>1) + p_statistics.ternaryClauses + p_statistics.naryClauses ) << std::endl
				  << "c ----------------------------" << std::endl;
	  }
  }

  // 1. Update all watchlists
  void Preprocessor::updateWatches( bool showstats )
  {
	// Now update watches for n-nary clauses
	size_t size = p_clauseDatabase.size();
	for( size_t c = 0; c != size; ++c )
	  {
		CRef cr = p_clauseDatabase[c];
		assert( !p_ca[cr].toDelete() );

		p_core->attachClause(cr, false);
	  }

	if( showstats && p_control->getVerbosity() > 1 )
	  {
		std::cout << "c #Used variables        : " << p_statistics.usedVariables << std::endl
				  << "c #Bin clauses           : " << (p_statistics.binaryClauses>>1) << std::endl
				  << "c #Ternary clauses       : " << p_statistics.ternaryClauses << std::endl
				  << "c #N-nary clauses        : " << p_statistics.naryClauses << std::endl
				  << "c #Total clauses         : " << ((p_statistics.binaryClauses>>1) + p_statistics.ternaryClauses + p_statistics.naryClauses ) << std::endl
				  << "c ----------------------------" << std::endl;
	  }
  }

  bool Preprocessor::copyBinaryList( uint32_t toReplace, uint32_t replace )
  {
	// Proceed positive occurences of binaries first
	size_t bsize( p_binaries[toReplace].size() );

	for( size_t i = 0; i != bsize; ++i )
	  {
		uint32_t seclit( p_binaries[toReplace][i].getSecondLit() );
		
		// Find constant...
		if( replace == seclit )
		  {
			++p_statistics.constantVariables;

			// Variable already assigned in opposite polarity?
			if( p_assignment[seclit^1] )
			  { return false; }
			
			if( !p_assignment[seclit] )
			  { p_core->addImplication( seclit ); }

			// Remove the dual binary clause of seclit
			removeBinary( seclit, toReplace );
		  }
		// Skip the responsible clause for the equivalence
		else if ( (replace^1) != seclit )
		  { 
			// Add new binary
			addBinary( replace, seclit, p_binaries[toReplace][i].isLearnedBinary() );

			// Remove the dual binary clause of seclit
			removeBinary( seclit, toReplace );
		  }
	  }

	// Clear binary list of "toReplace"
	p_binaries[toReplace].clear();
	return true;
  }

  void Preprocessor::copyOccurenceList( uint32_t toReplace, uint32_t replace )
  {
	// Consider the positive occurences of the n-nary clauses
	size_t osize( p_occur[toReplace].size() );

	for( size_t i = 0; i != osize; ++i )
	  {
		CRef cr = p_occur[toReplace][i];
		Clause& clause = p_ca[cr];

		// clause already marked as deleted?
		if( clause.toDelete() )
		  { continue; }

		int occ = clause.hasLitPolarity( replace );

		// After replacement clause would consists of ( l1 + ... + replace + ~replace ) 
		// Clause is satisfied after replacement -> delete occurences of clause and mark for deletion
		if( occ == -1 )
		  {

			clearAllOccurences(cr);
			// Clause is also deleted in current vector -> update values
			--i; --osize;
		  }
		// Replaced literal is already in clause -> remove "toReplace" from clause
		else if( occ == +1 )
		  {
			// Keep occurence of clause, since it will be deleted anyway afterwards
			strengthenClause( cr, toReplace, true );
		  }
		// just replace
		else
		  {
			uint32_t size( clause.length() );
			
			for( uint32_t pos = 0; pos != size; ++pos )
			  {
				if( clause[pos] == toReplace )
				  {
					clause[pos] = replace;
					break;
				  }
			  }

			clause.sort();
			// Recalc the signature
			clause.calcSign();

			// Update occurence list of "replace"
			p_occur[replace].push_back(cr);			
		  }
	  }

	// Delete the old occurence list
	p_occur[toReplace].clear();
  }

  // Replace every occurence of "toReplace" with "replace"
  // Refresh occurence lists
  // Preserves model for replaced variable
  bool Preprocessor::replaceVariable( uint32_t toReplace, uint32_t replace )
  {
	assert( !p_donttouch[toReplace>>1] );
	// If "toReplace" and "replace" are the same varible, we'll run into trouble
	assert( (toReplace>>1) != (replace>>1) );

	p_statistics.binaryClauses -= ( p_binaries[toReplace].size() + p_binaries[toReplace^1].size() );

	// Copy Binaries and occurences
	if (!copyBinaryList(toReplace,replace) )
	  { return false; }
	if (!copyBinaryList(toReplace^1,replace^1) )
	  { return false; }
	copyOccurenceList(toReplace,replace);
	copyOccurenceList(toReplace^1,replace^1);

	// Preserve model for replaced variable
	bool pol = !( (replace^toReplace) & 1);
	uint32_t replacedLit( (toReplace|1)^pol);

	uint32_t toReplaceVar( toReplace>>1 );
	uint32_t replaceVar( replace>>1 );

	p_replacedby[toReplaceVar] = (replace|1)^pol;
	p_replaces[replaceVar].push_back(replacedLit);

	while( !p_replaces[toReplaceVar].empty() )
	  {
		// Change replaced variables of currently replaced variable
		uint32_t furtherlit( p_replaces[toReplaceVar].back() );
		p_replaces[toReplaceVar].pop_back();

		assert( p_replaces[furtherlit>>1].empty() );

		pol = !( (toReplace^furtherlit^replace) & 1);
		p_replaces[replaceVar].push_back((furtherlit|1)^pol);
		p_replacedby[furtherlit>>1] = (replace|1)^pol;

	  }

	uint32_t clausesize(0);

	// Finally replace all occurences of "toReplace" with "replace" in "p_elimclauses"
	for( int i = (int)p_elimclauses.size()-1; i > 0; --i )
	  {
		// Did we have a clause size argument?
		if( clausesize == 0 )
		  { clausesize = p_elimclauses[i]; --i;}

		// Found "toReplace" in "p_elimclauses"
		if( (p_elimclauses[i]>>1) == toReplaceVar )
		  {
			// Get correct polarity
			bool polar = (replacedLit^p_elimclauses[i])&1;
			p_elimclauses[i] = ((replaceVar<<1)|(uint32_t)polar);
		  }

		--clausesize;
	  }

	// Mark "toReplace" as deleted
	p_deleted[toReplaceVar] = true;

	return propagateUnits();
  }

  // Delete all occurences and clauses of "var" in database
  void Preprocessor::deleteVariable( uint32_t var )
  {
	assert( !p_donttouch[var] );

	// Delete binaries
	uint32_t poslit(var<<1);
	uint32_t neglit((var<<1)^1);

	for( size_t i = 0; i != p_binaries[poslit].size(); ++i )
	  {
		removeBinary( p_binaries[poslit][i].getSecondLit(), poslit );
	  }
	for( size_t i = 0; i != p_binaries[neglit].size(); ++i )
	  {
		removeBinary( p_binaries[neglit][i].getSecondLit(), neglit );
	  }

	p_statistics.binaryClauses -= ( p_binaries[poslit].size() + p_binaries[neglit].size() );
	p_binaries[poslit].clear();
	p_binaries[neglit].clear();
	
	while( !p_occur[poslit].empty() )
	  { 
		clearAllOccurences( *p_occur[poslit].begin() ); 
	  }

	while( !p_occur[neglit].empty() )
	  { 
		clearAllOccurences( *p_occur[neglit].begin() ); 
	  }

	// Mark "var" as deleted
	p_deleted[var] = true;
	--p_statistics.usedVariables;

	// Push fake assignment on stack
	if( !p_assignment[var<<1] && !p_assignment[(var<<1)^1])
	  { 
		p_core->addImplication(var<<1); 
		++p_dsImplIndex;
	  }
  }

  // Merges two n-nary clauses with common literal "reslit"
  // Store new clause in "newClause"
  void Preprocessor::mergeClauses( Clause& clause1, Clause& clause2, uint32_t reslit, std::vector< uint32_t >& newClause ) const
  {
	newClause.clear();
	newClause.reserve( clause1.length() + clause2.length() - 2 );
  
	uint32_t negreslit( reslit^1 );

	uint32_t clause1size( clause1.length() );
	uint32_t clause2size( clause2.length() );

	for (uint32_t i = 0; i != clause1size; ++i )
	  {
		assert( !p_assignment[clause1[i]] && !p_assignment[clause1[i]^1] );

		if( clause1[i] != reslit )
		  { newClause.push_back(clause1[i]); }
	  }

	for (uint32_t i = 0; i != clause2size; ++i )
	  {
		assert( !p_assignment[clause2[i]] && !p_assignment[clause2[i]^1] );
		
		if( clause2[i] != negreslit )
		  { newClause.push_back(clause2[i]); }
	  }
	
	std::sort( newClause.begin(), newClause.end() );

	uint32_t target( 0 );
	
	for( size_t i = 1; i != newClause.size(); ++i )
	  {
		if( newClause[i] == (newClause[target]^1) )
		  {
			/* tautologic clause */
			newClause.clear();
			return;
		  }
		/* skip duplicate literals */
		else if( newClause[i] != newClause[target] )
		  {
			++target;
			if( target != i )
			  { newClause[target] = newClause[i]; }
		  }
	  }

	// Cut off last literals
	if( target + 1 < newClause.size() )
	  { newClause.resize( target + 1 ); }    
  }

  // Merges a n-nary clauses "clause" with a binary (reslit + otherlit) and common literal "reslit"
  // Store new clause in "newClause"
  void Preprocessor::mergeClauses( Clause& clause, uint32_t reslit, uint32_t otherlit, std::vector< uint32_t >& newClause ) const
  {
	newClause.clear();
	newClause.reserve( clause.length() );
  
	assert( !p_assignment[otherlit] && !p_assignment[otherlit^1] );

	bool pushed( false );

	uint32_t size( clause.length() );

	for( uint32_t i = 0; i != size; ++i )
	  {
		assert( !p_assignment[clause[i]] && !p_assignment[clause[i]^1] );

		// Tautological clause?
		if( clause[i] == (otherlit^1) )
		  { newClause.clear(); return; }
		// Put "otherlit" into new clause?
		else if ( !pushed && ( clause[i] > otherlit ) )
		  { 
			newClause.push_back(otherlit); 
			pushed = true;
		  }

		// Skip resolvent
		if ( clause[i] != (reslit^1) ) 
		  { 
			if( clause[i] != otherlit )
			  { newClause.push_back(clause[i]); }
		  }
	  }

	// Reached last element without adding "otherlit"? 
	// Then push "otherlit" add end of new clause
	if( !pushed )
	  { newClause.push_back(otherlit); }
  }

  // Counts the literals of merge of clause "clause1" and "clause2"
  // Return 0, if result is a tautology
  uint32_t Preprocessor::countMergeClauses( Clause& clause1, Clause& clause2, uint32_t reslit ) const
  {
	uint32_t negreslit( reslit^1 );

	uint32_t i( 0 );
	uint32_t j( 0 );
	uint32_t resultsize( 0 );
	  
	uint32_t c1size(clause1.length());
	uint32_t c2size(clause2.length());

	while( i < c1size && j < c2size )
	  {
		// skip resolvent literal
		if( (clause1[i] == reslit) )
		  { ++i; }
		if ( (clause2[j] == negreslit) )
		  {++j; }

		// tautological clause
		if( clause1[i] == (clause2[j]^1) )
		  { return 0; } 
		else if( clause1[i] < clause2[j] )
		  { ++i; ++resultsize; }
		else if( clause1[i] > clause2[j] )
		  { ++j; ++resultsize; }
		// skip duplicated literal
		else
		  { ++i; ++j; }
	  }
	  
	resultsize += (c1size-i) + (c2size-j);

	return resultsize;
  }

  // Counts the literals of merge of clause "clause" and "(reslit + otherlit)"
  // Return 0, if result is a tautology
  uint32_t Preprocessor::countMergeClauses( Clause& clause, uint32_t reslit, uint32_t otherlit ) const
  {
	uint32_t i(0);
	// Count from "1" for "otherlit"
	int resultsize(1);

	assert( !clause.toDelete() );

	uint32_t csize(clause.length());

	while( i < csize )
	  {
		// skip resolvent literal
		if( (clause[i] == reslit) )
		  { ++i; }
		// tautological clause
		if( clause[i] == (otherlit^1) )
		  { return 0; } 
		else if( clause[i] < otherlit )
		  { ++i; ++resultsize; }
		else if( clause[i] > otherlit )
		  { break; }
		// Skip duplicated literal
		else
		  { ++i; }
	  }

	resultsize += (csize-i);

	return resultsize;
  }

  // Estimates costs for variable elimination of "var"
  int Preprocessor::estimateCosts( uint32_t var ) 
  {
	int opv = (int)p_binaries[var<<1].size() + (int)p_occur[var<<1].size();
	int onv = (int)p_binaries[(var<<1)^1].size() + (int)p_occur[(var<<1)^1].size();

	if( opv == 0 && onv == 0 ) 
	  {
		// Unused variable

		// Return some incredibly high cost 
		return 1000000000;
	  }
    
	int spv = ( (int)p_binaries[var<<1].size() )<<1;

	for( uint32_t i = 0; i != p_occur[var<<1].size(); ++i )
	  { spv += p_ca[p_occur[var<<1][i]].length(); }

	int snv = ( (int)p_binaries[(var<<1)^1].size() )<<1;

	for( uint32_t i = 0; i != p_occur[(var<<1)^1].size(); ++i )
	  { snv += p_ca[p_occur[(var<<1)^1][i]].length(); }

	assert( opv + onv > 0 );  
	assert( spv >= (opv<<1) );
	assert( snv >= (onv<<1) );
      
	int cost = onv * (spv - opv ) + opv * ( snv - onv ) - spv - snv;
    
	return cost;
  }

  // Estimate costs for variable elimination of "var" with more accurate "countMergeClauses"
  int Preprocessor::estimateCosts2 ( uint32_t var ) const 
  {
	assert( var <= p_variables );
	uint32_t poslit(var<<1);
	uint32_t neglit((var<<1)^1);
	uint32_t posbinsize(p_binaries[poslit].size());
	uint32_t negbinsize(p_binaries[neglit].size());
	uint32_t posoccursize(p_occur[poslit].size());
	uint32_t negoccursize(p_occur[neglit].size());

	// Return ridiculously high cost if variable occurs more than 20 times 
	// I.e. do not take this variable into account
	if ( (posbinsize + negbinsize + posoccursize + negoccursize) > 20 )
	  { return 10000000; }

	// decrement binary lits 
	int totalliterals = -(( p_binaries[poslit].size() + p_binaries[neglit].size() )<<1);
	
	for( uint32_t i = 0; i != posoccursize; ++i )
	  { 
		Clause& clausepos( p_ca[p_occur[poslit][i]] );
		assert( !clausepos.toDelete()); 

		// decrement pos n-nary lits
		totalliterals -= clausepos.length(); 

		if( clausepos.lbd() == 1 )
		  { 
			// increment neg binary, pos n-nary lits
			for( uint32_t j = 0; j != negbinsize; ++j )
			  {
				uint32_t tmpcount = countMergeClauses( clausepos, poslit, p_binaries[neglit][j].getSecondLit() );
				totalliterals += (int)tmpcount;
			  }

			// increment pos n-nary, neg n-nary lits
			for( uint32_t k = 0; k != negoccursize; ++k )
			  {
				Clause& clauseneg( p_ca[p_occur[neglit][k]] );
				if( clauseneg.lbd() == 1 )
				  {
					uint32_t tmpcount = countMergeClauses( clausepos, clauseneg, poslit );
					totalliterals += (int)tmpcount;
				  }
			  }

		  }
	  }

	for( uint32_t i = 0; i != negoccursize; ++i )
	  { 
		Clause& clause( p_ca[p_occur[neglit][i]] );
		assert( !clause.toDelete() ); 

		// decrement neg n-nary lits
		totalliterals -= clause.length();

		if( clause.lbd() == 1 )
		  { 
			// increment pos binary, neg n-nary lits
			for( uint32_t j = 0; j != posbinsize; ++j )
			  {
				uint32_t tmpcount = countMergeClauses( clause, neglit, p_binaries[poslit][j].getSecondLit() );
				totalliterals += (int)tmpcount;
			  }
		  }
	  }

	for( uint32_t i = 0; i != posbinsize; ++i )
	  {
		for( uint32_t j = 0; j != negbinsize; ++j )
		  {
			// increment pos+neg binary lits
			if ( p_binaries[poslit][i].getSecondLit() != (p_binaries[neglit][j].getSecondLit()^1) )
			  { totalliterals += 2;  } 
		  }
	  }

	return totalliterals;
  }

  // Adds a clause to database
  // Do _not_ update watch lists
  // A binary clause is put into the binary datastructure of preprocessor
  // Updates occurence lists for n-nary clauses
  // This method is only used in the preprocessor 
  bool Preprocessor::addClausePrepro (std::vector<uint32_t>& clause)
  {
	assert( !p_emptyClause );

	// Are we really on decision level 0?
	assert(p_decisionLevel == 0); 

	// If "clause" is empty, we might have a problem.
	assert(!clause.empty()); 

	// Sort "clause" to speedup the checks below.
	std::sort(clause.begin(),clause.end());

	// "Shifted" variable indices are assumed to be greater 1.
	assert(clause.front() > 1); 

	assert( (clause.back() >> 1) <= p_variables );

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

		// "clause" satisfied by "l"? Do we have a tautological clause?
		if (p_assignment[l] || (l ^ 1) == lit)
		  { clause.resize(0); return true; }

		// Do we have to take the current literal into account?
		if (!p_assignment[l ^ 1] && l != lit)
		  { clause[size++] = l; lit = l; }
	  }

	// Do we have an empty clause? CNF formula unsatisfiable?
	if (size == 0)
	  { p_emptyClause = true; return false; }
      
	// Resize "clause" (necessary for the multi-threaded mode to work correctly).
	clause.resize(size); 

	// Do we have a unit clause?
	if (size == 1)
	  {
		// Push the unit literal as a "fake" implication onto the decision stack.
		p_core->addImplication(clause[0]);

		// Everything went fine.
		return true; 
	  }

	// Do we have a binary clause?
	if (size == 2)
	  {	 
		uint32_t wl0(clause[0]);
		uint32_t wl1(clause[1]); 

		addBinary( wl0, wl1, false );

		// Everything went fine.
		return true; 
	  }
	else if ( size == 3 )
	  {
		++p_statistics.ternaryClauses;
	  }
	else
	  {
		++p_statistics.naryClauses;
	  }

	// Initialization.
	CRef cr(p_ca.alloc(clause, 1, size));
      
	// update occurence lists
	for (uint32_t l = 0; l < size; ++l)
	  { p_occur[clause[l]].push_back(cr); }

	// Finally, add the new clause to the clause database.
	p_clauseDatabase.push_back(cr);

	// Everything went fine.
	return true;
  }

  /* End: some helper functions */

  // Propagate new units
  // Delete all satisfied clauses and their occurence	
  // Strengthen Clauses
  // Returns "false" if a contradiction occurs (formula is UNSAT), otherwise true
  bool Preprocessor::propagateUnits( void )
  {
	assert( p_decisionLevel == 0 );

	uint32_t units(0);

	// first deduce all collected implications
	while( p_dsImplIndex != p_dsEndIndex )
	  {
		// Remove every clause with "poslit" and strengthen every clause with "neglit"
		uint32_t poslit( p_decisionStack[p_dsImplIndex] );
		uint32_t neglit( p_decisionStack[p_dsImplIndex]^1 );

		p_statistics.binaryClauses -= ( p_binaries[poslit].size() + p_binaries[neglit].size() );

		++p_dsImplIndex;
		
		// Has to be assigned, since it's part of the decision stack.
		assert( p_assignment[poslit] || p_assignment[neglit] ); 

		if( p_binaries[poslit].empty() && p_binaries[neglit].empty() && p_occur[poslit].empty() && p_occur[neglit].empty() )
		  {
			// Mark variable as deleted
			p_deleted[poslit>>1] = true;
			p_level[poslit>>1] = 0;
			continue; 
		  }

		++units;
		++p_statistics.unitPropagations;
		--p_statistics.usedVariables;

		// Proceed positive binary occurences
		for( size_t i = 0; i != p_binaries[poslit].size(); ++i)
		  {
			uint32_t seclit( p_binaries[poslit][i].getSecondLit() );
			removeBinary( seclit, poslit );
		  }

		// Clear binary list
		p_binaries[poslit].clear();

		// Proceed positive n-nary clauses
		while( !p_occur[poslit].empty() ) 
		  {
			CRef cr = *p_occur[poslit].rbegin();
			Clause& clause( p_ca[cr] );
			p_occur[poslit].pop_back();
				
			uint32_t csize(clause.length());

			if( csize == 3 )
			  {
				--p_statistics.ternaryClauses;
			  }
			else
			  {
				--p_statistics.naryClauses;
			  }
			
			// Update all other occurence lists
			for( uint32_t pos = 0; pos != csize; ++pos )
			  {
				if( clause[pos] != poslit )
				  { removeFromOccurenceList( clause[pos], cr ); }
			  }
			// Mark clause as to deleted
			clause.markForDeletion();
		  }		
		
		// Now strengthen the clauses with negative occurences


		// First consider binary clauses
		size_t binsize(p_binaries[neglit].size()); 
		for( size_t i = 0; i != binsize; ++i)
		  {
			uint32_t seclit( p_binaries[neglit][i].getSecondLit() );

			if( p_assignment[seclit^1] )
			  { 
				if( p_control->getVerbosity() > 1 )
				  {
					std::cout << "c contradiction in unit propagation with " << Lit(seclit) << " -> UNSAT" << std::endl;
				  }
				return false; 
			  }
		
			if( !p_assignment[seclit] )
			  { 
				p_core->addImplication(seclit); 
			  }

			removeBinary( seclit, neglit );
		  }
		
		// Clear binary list
		p_binaries[neglit].clear();

		// Now consider n-nary clauses with negative occurences
		while( !p_occur[neglit].empty() ) 
		  {
			CRef cr = *p_occur[neglit].rbegin();
			Clause& clause( p_ca[cr] );
			p_occur[neglit].pop_back();

			// Clause already deleted
			if( clause.toDelete() )
			  { continue; }

			strengthenClause( cr, neglit, true );
		  }

		// Mark variable as deleted
		p_deleted[poslit>>1] = true;
		p_level[poslit>>1] = 0;
	  }
	
	// At this point all implications are performed 
	// And all occurence lists are up to date
	// Now, delete marked clauses from clausedatabase

	size_t csize(p_clauseDatabase.size());
	for( size_t c = 0; c != csize; ++c )
	  {
		// delete marked clauses permanatly
		if( p_ca[p_clauseDatabase[c]].toDelete() )
		  {
			p_ca.free(p_clauseDatabase[c]);
			p_clauseDatabase[c--] = p_clauseDatabase[--csize];
			p_clauseDatabase.pop_back();
		  }
	  }

	if( (p_control->getVerbosity() > 1) && ( units != 0 ) )
	  { 
		std::cout << "c unit propagations      : " << units << std::endl; 
	  } 

	return true;
  }

  // Detect trivial monotone/pure literals
  bool Preprocessor::detectMonotone( bool& didsomething, bool incremental )
  {
	uint32_t monolits( p_statistics.monotoneVariables );
	uint32_t dclits( p_statistics.dontcareVariables );

	bool doitagain( false );

	uint32_t low(1);
	if( incremental )
	  { low = p_firstPreVarIndex; }

	do { 
	  doitagain = false;
	  for(uint32_t v = low; v <= p_variables; ++v )
		{
		  // Skip deleted variables and variables which are already assigned
		  if( p_deleted[v] || p_donttouch[v] || p_assignment[v<<1] || p_assignment[(v<<1)^1] )
			{ continue; }

		  bool dc( false );
		  uint32_t lit( 0 );

		  // Positive occurences of "v"?
		  if( p_binaries[v<<1].empty() && p_occur[v<<1].empty() )
			{
			  lit = (v<<1)^1;
			  didsomething = true;
			  doitagain = true;
			  dc = true;
			} 

		  // Negative occurences of "v"?
		  if( p_binaries[(v<<1)^1].empty() && p_occur[(v<<1)^1].empty() )
			{
			  lit = v<<1;
			
			  // Neither positive nor negative occurence of "v"? 
			  // => "v" is not used anymore
			  if( dc && !p_donttouch[v] )
				{
				  p_deleted[v] = true;
				  //lit = 0;
				  ++p_statistics.dontcareVariables;
				}
			  didsomething = true;
			  doitagain = true;
			}
 
		  // "v" is monotone with polarity of "lit"
		  if( lit != 0 )
			{ 
			  p_core->addImplication( lit ); 
			  ++p_statistics.monotoneVariables;
			}
		}
	  if ( !propagateUnits() )
		{ return false; }
	} while( doitagain );

	if( p_control->getVerbosity() > 1 && (p_statistics.monotoneVariables != monolits) )
	  {
		std::cout << "c monotone lits          : " << ( p_statistics.monotoneVariables - monolits ) << std::endl 
				  << "c dc lits                : " << ( p_statistics.dontcareVariables - dclits ) << std::endl;
	  }
	return propagateUnits();
  }

  // Search within binaries for two cases:
  //  1. [(a + b) * (a + ~b)] => a is constant, imply a
  // 2a. [(a + ~b) * (~a + b )] => a and b are equivalent, replace all occurences of a with b (or b with a)
  // 2b. [(a + b) * (~a + ~b )] => a and ~b are equivalent, replace all occurences of a with ~b (or b with ~a)
  bool Preprocessor::findBinaryConsAndEquiv( bool& didsomething, bool incremental )
  {
	// Skip, if there are to many binary clauses in the database
	if( p_statistics.binaryClauses > 200000 )
	  { return true; }

	uint32_t cons( p_statistics.constantVariables );
	uint32_t equiv( p_statistics.equivalentVariables );

	uint32_t low(1);
	if( incremental )
	  { low = p_firstPreVarIndex; }

	for( uint32_t v = low; v <= p_variables; ++v )
	  {
		if( p_deleted[v] ) 
		  { continue; }

		uint32_t plit( v<<1 );
		uint32_t nlit( plit^1 );

	  STARTOVER_VAR:

		size_t psize(p_binaries[plit].size());
		size_t nsize(p_binaries[nlit].size());

		for( size_t p = 0; p < psize; ++p )
		  {
			uint32_t seclit( p_binaries[plit][p].getSecondLit() );

			for( size_t n = 0; n < nsize; ++n)
			  {

				// Do we have a constant?
				if( p_binaries[nlit][n].getSecondLit() == seclit )
				  {
					didsomething = true;
					++p_statistics.constantVariables;

					// Variable should be unassigned, since we delete immediatly the clauses of implications
					assert( !p_assignment[seclit] && !p_assignment[seclit^1] );

					// Add constant to decisionstack
					p_core->addImplication(seclit);

					// Propagate the new implication for the constant variable
					// Eliminates automatically the defining binaries for the constant
					if( !propagateUnits() )
					  { return false; }

					// Start over with this variable
					goto STARTOVER_VAR;
				  }
				// Do we have an equivalence?
				else if ( p_binaries[nlit][n].getSecondLit() == (seclit^1) )
				  {
					uint32_t replacelit( nlit );

					// If "seclit" is don't touch, swap with "replacelit" so that the don't touch variable will not be removed

					if( p_donttouch[seclit>>1] )
					  { 
						if( !p_donttouch[replacelit>>1] )
						  { 
							replacelit = seclit;
							seclit = nlit;
						  }
						// Both variables don't touch? Do nothing...
						else
						  { continue; }
					  }

					didsomething = true;
					++p_statistics.equivalentVariables;

					// Remove binary clauses defining the equivalence
					removeBinary(replacelit, seclit^1);
					removeBinary(replacelit^1, seclit);

					// Replace the occurence of "seclit" with "replacelit"
					if ( !replaceVariable(seclit, replacelit ) )
					  { 
						if( p_control->getVerbosity() > 1 )
						  { std::cout << "c contradiction after replacement of " << Lit(seclit) << " with " << Lit( nlit ) << " -> UNSAT" << std::endl; }
						return false; 
					  }

					// Update "psize" and "nsize"
					psize = p_binaries[plit].size();
					nsize = p_binaries[nlit].size();
					  
					// Start over with this variable
					goto STARTOVER_VAR;
				  }
			  }
		  }
	  }

	if( p_control->getVerbosity() > 1 && ( ( p_statistics.constantVariables != cons ) || (p_statistics.equivalentVariables != equiv ) ) )
	  {
		std::cout << "c binary cons            : " << (p_statistics.constantVariables - cons) << std::endl
				  << "c binary equiv           : " << (p_statistics.equivalentVariables - equiv) << std::endl;
	  }
	
	return propagateUnits();
  }


  bool Preprocessor::fullSubsumptionCheck( uint32_t& didsomething, bool incremental )
  {
	if( p_control->getVerbosity() > 2 )
	  { std::cout << "c Performing subsumption checks..." << std::endl; }

	uint32_t tmpsub(p_statistics.subsumptions);
	uint32_t tmpselfsub(p_statistics.selfSubsumptions);
	
	uint32_t low(1);
	if( incremental )
	  { low = p_firstPreVarIndex; }

	for( uint32_t i = low; i <= p_variables; ++i )
	  {
		if( p_deleted[i] )
		  { continue; }

		uint32_t poslit = i<<1;
		uint32_t neglit = (i<<1)^1;

		// First check if the binaries subsume n-nary clauses
		size_t bsize( p_binaries[poslit].size() );
		for( size_t j = 0; j != bsize; ++j )
		  {
			checkBinSub( poslit, p_binaries[poslit][j].getSecondLit() );
		  }

		bsize = p_binaries[neglit].size();
		for( size_t j = 0; j != bsize; ++j )
		  {
			checkBinSub( neglit, p_binaries[neglit][j].getSecondLit() );
		  }
	  }

	uint32_t startindex = 0;
	if( incremental )
	  { startindex = p_firstPreVarIndex; }

	if( (p_clauseDatabase.size()-startindex) <= 1000000 )
	  {
		// Now check for every n-nary, if the clause is self-subsuming or subsumed by another n-nary clause
		for( uint32_t c = startindex; c != p_clauseDatabase.size(); ++c )
		  {
			CRef cr = p_clauseDatabase[c];
			Clause& clause = p_ca[cr];

			// Already marked as deleted?
			if( clause.toDelete() )
			  { continue; }
		
			// Subsumption Check
			if( isSubsumed( clause ) )
			  { 
				++p_statistics.subsumptions;
				clearAllOccurences( cr ); 
			  }
		  }
	  }

	if( ( (p_statistics.subsumptions - tmpsub) > 0 ) || ( (p_statistics.selfSubsumptions - tmpselfsub) > 0 ) )
	  { 
		didsomething |= 0x02; 
		
		if( p_control->getVerbosity() > 1 )
		  {
			std::cout << "c subsumptions           : " << (p_statistics.subsumptions - tmpsub) << std::endl
					  << "c selfsubsumptions       : " << (p_statistics.selfSubsumptions - tmpselfsub) << std::endl;
		  }
	  }

	return propagateUnits();
  }

  // Mark all n-nary clauses which are subsumed by the binary (i1 + i2)
  // Perform self-subsumption, with one binary clause
  void Preprocessor::checkBinSub( uint32_t i1, uint32_t i2 )
  {
	// Get Signature of binary clause
	unsigned long long sign( 0 );
	sign |= 1ULL << (i1 % 64);
	sign |= 1ULL << (i2 % 64);
	
	uint32_t checklit( i1 );
	uint32_t seclit( i2 );

	size_t size( p_occur[checklit].size() );

	for( size_t i = 0; i != size; ++i)
	  {
		CRef cr(p_occur[checklit][i]);
		Clause& clause(p_ca[cr]);

		if( ( ( sign & ~clause.sign() ) != 0 ) || clause.toDelete() )
		  { continue; }

		uint32_t csize(clause.length());

		for(uint32_t pos = 0; pos != csize; ++pos )
		  {
			// "clause" is self-subsuming with ( i1 + i2 )
			if( ( clause[pos] == (seclit^1) ) && !p_donttouch[seclit>>1] )
			  { 
				// If we have  deleted the n-nary clause, we have to update the status variables
				if ( strengthenClause( cr, seclit^1, false ) )
				  { --size; --i; }

				++p_statistics.selfSubsumptions;
			  }
			// "clause" is subsumed by ( i1 + i2 )
			else if( clause[pos] == seclit )
			  { 
				++p_statistics.subsumptions;

				for( uint32_t p = 0; p != clause.length(); ++p)
				  {
					if( clause[p] != checklit )
					  { removeFromOccurenceList( clause[p], cr ); }
				  }

				if( clause.length() == 3 )
				  { --p_statistics.ternaryClauses; }
				else
				  { --p_statistics.naryClauses; }
					
				clause.markForDeletion();
				
				assert( size == p_occur[checklit].size() );
				p_occur[checklit][i--] = p_occur[checklit][--size];
				p_occur[checklit].pop_back();
				break;
			  }
		  }
	  }
  }

  // Checks if "clause" is subsumed by another n-nary clause
  // Assumes that the binary subsumption check was already performed
  bool Preprocessor::isSubsumed( Clause& clause ) const
  {
	uint32_t sign( clause.sign() );
	uint32_t csize( clause.length() );
	// check if another nary clause subsumes "clause"
	
	for( uint32_t pos = 0; pos != csize; ++pos )
	  {
		const std::vector< CRef >& occur( p_occur[clause[pos]] );

		size_t osize( occur.size() );

		for( size_t j = 0; j != osize; ++j )
		  {
			Clause& checkClause(p_ca[occur[j]]);

			uint32_t ccsize( checkClause.length() );
			unsigned long long csign( checkClause.sign() );

			/* skip if:
			   clause has same or larger size
			   clause has been marked as deleted
			   clause's signature doesn't fit
			*/
			if(
			   ( checkClause == clause ) ||
			   ( ccsize > csize ) ||
			   ( checkClause.lbd() == 0 ) ||
			   ( ( csign & ~sign ) != 0 )
			   )
			  { continue; }


			uint32_t c(0);
			uint32_t s(0);

			// Check if "checkClause" subsumes "clause"
			while( ( c != ccsize ) && 
				   ( s != csize ) && 
				   ( ( ccsize - c ) <= ( csize - s ) ) )
			  {
				if( checkClause[c] == clause[s] )
				  {
					++c;
					++s;
				  }
				else if( checkClause[c] > clause[s] )
				  {
					++s;
				  }
				else
				  {
					return false;
				  }
			  }

			if( c != ccsize )
			  {
				return false;
			  }

			return true;
		  }
	  }
	return false;
  }

  // Checks if "clause" is subsumed by another n-nary clause
  // Assumes that the binary subsumption check was already performed
  // This method assumes that "clause" is not added in the clause database so far
  bool Preprocessor::isSubsumed( const std::vector< uint32_t >& clause, uint32_t sign ) const
  {
	size_t csize = clause.size();
	// check if another nary clause subsumes "clause"
	for( size_t pos = 0; pos != csize; ++pos )
	  {
		const std::vector< CRef >& occur( p_occur[clause[pos]] );

		size_t osize( occur.size() );

		for( size_t j = 0; j != osize; ++j )
		  {
			Clause& checkClause(p_ca[occur[j]]);

			uint32_t ccsize( checkClause.length() );
			unsigned long long csign( checkClause.sign() );

			/* skip if:
			   clause has same or larger size
			   clause has been marked as deleted
			   clause's signature doesn't fit
			*/
			if( ( ccsize > csize ) ||
				( checkClause.lbd() == 0 ) ||
				( ( csign & ~sign ) != 0 )
				)
			  { continue; }

			uint32_t c = 0;
			uint32_t s = 0;

			// Check if "checkClause" subsumes "clause"
			while( ( c != ccsize ) && 
				   ( s != csize ) && 
				   ( ( ccsize - c ) <= ( csize - s ) ) )
			  {
				if( checkClause[c] == clause[s] )
				  {
					++c;
					++s;
				  }
				else if( checkClause[c] > clause[s] )
				  {
					++s;
				  }
				else
				  {
					return false;
				  }
			  }

			if( c != ccsize )
			  {
				return false;
			  }
			return true;
		  }
	  }
	return false;
  }

  // Is "clause" subsumed by some clause in database?
  // Assumes that "clause" is sorted
  bool Preprocessor::isForwardSubsumed( const std::vector< uint32_t >& clause, unsigned long long sign ) const
  {
	size_t csize( clause.size() );
	// Check binaries first
	for( size_t i = 0; i != csize; ++i )
	  {
		size_t bsize( p_binaries[clause[i]].size() );
		for( size_t j = 0; j != bsize; ++j )
		  {
			uint32_t seclit( p_binaries[clause[i]][j].getSecondLit());
			unsigned long long binsign( ( 1ULL << (seclit % 64) ) | ( 1ULL << ( clause[i] % 64) ) );

			// subsumption candidate!
			if( ( binsign & ~sign ) == 0 )
			  {
				uint32_t k( 0 );
				while( ( k < csize ) && ( clause[k] < seclit ) )
				  { ++k; }
				// Subsumption found!
				if( ( k < csize ) && ( clause[k] == seclit ) )
				  { 
					return true; 
				  }
			  }
		  }
	  }

	// Check n-naries
	return isSubsumed(clause, sign);
  }

  void Preprocessor::preserveModel( uint32_t resvar )
  {
	uint32_t poslit(resvar<<1);
	uint32_t neglit(poslit^1);

	size_t possize( p_binaries[poslit].size() + p_occur[poslit].size() );
	size_t negsize( p_binaries[neglit].size() + p_occur[neglit].size() );

	assert( !p_assignment[poslit] && !p_assignment[neglit] );

	// Preserve model
	uint32_t firstsize( possize );
	uint32_t secondsize( negsize );
	uint32_t firstlit( poslit );
	uint32_t secondlit( neglit );

	// Determine the polarity with less occurences
	if( secondsize < firstsize )
	  {
		firstsize = negsize;
		secondsize = possize;
		firstlit = neglit;
		secondlit = poslit;
	  }
		  
	// Store binary clauses of one polarity (the one with less occurences)
	for( size_t n = 0; n != p_binaries[firstlit].size(); ++n )
	  {
		p_elimclauses.push_back(firstlit);
		p_elimclauses.push_back(p_binaries[firstlit][n].getSecondLit());
		// Size of the clause
		p_elimclauses.push_back(2);
	  }

	// Store n-nary clauses of one polarity (the one with less occurences)
	size_t osize( p_occur[firstlit].size() );
	for( size_t n = 0; n != osize; ++n )
	  {
		Clause& clause = p_ca[p_occur[firstlit][n]];

		if( clause.lbd() > 1 )
		  { continue; }

		uint32_t first(p_elimclauses.size());
		uint32_t csize(clause.length());

		for( uint32_t pos = 0; pos != csize; ++pos )
		  {
			p_elimclauses.push_back(clause[pos]);
			// Store "firstlit" on first position;
			if( clause[pos] == firstlit )
			  { 
				p_elimclauses[first+pos] = p_elimclauses[first];
				p_elimclauses[first] = firstlit;
			  }
		  }
		// Size of the clause 
		p_elimclauses.push_back(csize);
	  }

	// Store opposite polarity of the literal
	p_elimclauses.push_back(secondlit);
	p_elimclauses.push_back(1);
  }

  // Performs variable elimination
  bool Preprocessor::varElimination( uint32_t& didsomething, bool incremental )
  {
	if( p_control->getVerbosity() > 2 )
	  { std::cout << "c Performing variable elimination..." << std::endl; }

	uint32_t resvars(p_statistics.resolvedVariables);
	uint32_t nxtRecalc(resvars+1023);
	bool recalc( false );

	std::list< std::pair<uint32_t, int> > varcost;

	uint32_t low(1);
	if( incremental )
	  { low = p_firstPreVarIndex; }

	for( uint32_t v = low; v <= p_variables; ++v )
	  {
		// Skip deleted and don't touch variables
		if( !p_deleted[v] && !p_donttouch[v] )
		  {
			int cost = estimateCosts2( v );
			  
			varcost.push_back( std::pair< uint32_t, int >(v,cost));
		  }
	  }

	varcost.sort(sortPairBySecond<uint32_t,int>);

	bool restart( false );

	while( true )
	  {

		uint32_t resvar(0);
		int cost(0);

		if( varcost.empty() )
		  { break; }
	
		// Recalculate costs:
		// - Every 1024 variable eliminations or
		// - If new unit was created
		if( recalc || ( nxtRecalc < p_statistics.resolvedVariables ) )
		  {
			recalc = false;
			nxtRecalc = p_statistics.resolvedVariables + 1023;
			for( std::list<std::pair< uint32_t, int> >::iterator s = varcost.begin(); s != varcost.end(); )
			  {
				uint32_t var = s->first;
				if( p_deleted[var] )
				  { 
					s = varcost.erase(s);
					continue; 
				  }

				cost = estimateCosts2(var);
				s->second = cost;

				++s;
			  }
			varcost.sort(sortPairBySecond<uint32_t,int>);
		  }

		for( std::list<std::pair< uint32_t, int> >::iterator s = varcost.begin(); s != varcost.end(); ++s )
		  {
			// found a candidate for var Elimination!
			uint32_t var = s->first;
			uint32_t costs = ( p_binaries[var<<1].size() + p_binaries[(var<<1)^1].size() + p_occur[var<<1].size() + p_occur[(var<<1)^1].size());
			
			if( !p_deleted[var] && ( s->second <= p_increaseVal ) && costs <= p_costVal )
			  { 
				cost = s->second;
				resvar = var; 
				varcost.erase(s);
				break;
			  }
		  }
		  		
		// No candidate found, end loop
		if (resvar == 0) 
		  { 
			if( restart )
			  { 
				restart = false; 
				recalc = true; 
				continue; 
			  }
			break;
		  }

		++p_statistics.resolvedVariables;
		
		didsomething |= 0x8;
		restart = true;

		std::vector< std::vector< uint32_t > > resolvents;

		// Store some original clauses for model preservation
		preserveModel(resvar);

		uint32_t poslit = resvar<<1;
		uint32_t neglit = (resvar<<1)^1;

		std::vector<uint32_t> newClause( 2 );

		/* Now start resolution steps */
		for( size_t i1 = 0; i1 != p_binaries[poslit].size(); ++i1 )
		  {

			// Skip learned
			if( p_binaries[poslit][i1].isLearnedBinary())
			  { continue; }

			uint32_t posseclit( p_binaries[poslit][i1].getSecondLit() );

			assert( !p_assignment[posseclit] && !p_assignment[posseclit^1] );

			// Resolve binary clauses of "poslit" and "neglit"
			for( size_t i2 = 0; i2 != p_binaries[neglit].size(); ++i2 )
			  {
				// Skip learned
				if( p_binaries[neglit][i2].isLearnedBinary())
				  { continue; }

				uint32_t negseclit( p_binaries[neglit][i2].getSecondLit() );
				
				assert( !p_assignment[negseclit] && !p_assignment[negseclit^1] );

				// Resolved tautology? => Skip!
				if( posseclit == (negseclit^1) )
				  { continue; }
				// Resolved (a+b) and (~a+b)? => b is constant
				else if( posseclit == negseclit )
				  {
					newClause.resize( 1 );
					newClause[0] = posseclit;
					
					resolvents.push_back(newClause);
					newClause.resize( 2 );
				  }
				// Ordinary resolution step
				else
				  {
					newClause[0] = posseclit;
					newClause[1] = negseclit;

					resolvents.push_back(newClause);
					newClause.resize( 2 );
				  }
			  }

			// Resolve binary clauses of "poslit" and n-nary clauses of "neglit"
			for( size_t i2 = 0; i2 != p_occur[neglit].size(); ++i2 )
			  {
				Clause& c2( p_ca[p_occur[neglit][i2]] );
				assert( !c2.toDelete() );

				if( c2.isLearned() )
				  { continue; }

				mergeClauses( c2, poslit, posseclit, newClause );
				
				if( !newClause.empty() )
				  { resolvents.push_back(newClause); }
			  }
			newClause.resize( 2 );
		  }

		for( size_t i1 = 0; i1 != p_occur[poslit].size(); ++i1 )
		  {

			Clause& c1( p_ca[p_occur[poslit][i1]] );
			assert( c1.lbd() != 0 );

			// Skip learned
			if( c1.isLearned() )
			  { continue; }

			// Resolve binary clauses of "neglit" and n-nary clauses of "poslit"
			size_t binsize(p_binaries[neglit].size());
			for( size_t i2 = 0; i2 != binsize; ++i2 )
			  {
				// Skip learned
				if( p_binaries[neglit][i2].isLearnedBinary())
				  { continue; }

				uint32_t negseclit( p_binaries[neglit][i2].getSecondLit() );
				assert( !p_assignment[negseclit] && !p_assignment[negseclit^1] );

				mergeClauses( c1, neglit, negseclit, newClause );

				if( !newClause.empty() )
				  { resolvents.push_back(newClause); }
				newClause.resize( 2 );
			  }

			// Resolve n-nary clauses of "neglit" and "poslit"
			binsize = p_occur[neglit].size();
			for( size_t i2 = 0; i2 != binsize; ++i2 )
			  {
				Clause& c2(p_ca[p_occur[neglit][i2]]);
				assert( c2.lbd() != 0 );

				if( c2.lbd() > 1 )
				  { continue; }

				mergeClauses( c1, c2, poslit, newClause );

				if( !newClause.empty() )
				  { resolvents.push_back(newClause); }
			  }
		  }

		// First delete resolved variables from database
		deleteVariable(resvar);

		// Now add temporary saved clauses
		for( size_t c = 0; c != resolvents.size(); ++c )
		  { 
			if( resolvents[c].size() > 2 )
			  {
				// Calc signature
			    unsigned long long sign( 0 );
				for( uint32_t s = 0; s != resolvents[c].size(); ++s )
				  { 
					sign |= 1ULL << (resolvents[c][s] % 64); 
				  }

				std::sort(resolvents[c].begin(), resolvents[c].end());
					 
				// Clause is subsumed by existing clause?
				if( !isForwardSubsumed( resolvents[c], sign ) )
				  {
					// Add clause without initilizing watchlists
					if ( !addClausePrepro(resolvents[c]) )
					  { 
						if( p_control->getVerbosity() > 1 )
						  { 
							std::cout << "c contradiction with resolved clause -> UNSAT" << std::endl; 
						  }
						return false; 
					  }
				  }
			  }
			else if ( !addClausePrepro(resolvents[c]) )
			  { 
				if( p_control->getVerbosity() > 1 )
				  { 
					std::cout << "c contradiction with resolved unit or binary clause -> UNSAT" << std::endl; 
				  }
				return false; 
			  }
		  }

		// Did we add new unit(s)?
		// First propagate these units before next resolution step
		if( p_dsImplIndex != p_dsEndIndex )
		  { 
			recalc = true;
			if( !propagateUnits() )
			  { return false; }
		  }
	  }

	if( p_control->getVerbosity() > 1 && (p_statistics.resolvedVariables != resvars) )
	  {
		std::cout << "c variable eliminations  : " << (p_statistics.resolvedVariables-resvars) << std::endl;
	  }
	return propagateUnits();
  }
  
  // Restore model for deleted variables
  // This method should be called before model is returned
  // Assumes that model of the solver core is already set to "p_model"
  // First restore replaced, then resolved variables
  // Then update replaced variables
  void Preprocessor::extendModel( void )
  {
	/* Restore eliminated variables during equivalance checking */
	restoreReplacedVariables(); 

	do {
	  /* Restore eliminated variables */
	  restoreVariableEliminations();
	} while (restoreReplacedVariables() );
  }

  bool Preprocessor::restoreReplacedVariables( void )
  {
	bool didsomething(false);
	/* Restore replaced variables */
	for( uint32_t v = 1; v <= p_variables; ++v )
	  {
		assert( p_deleted[v] || p_assignment[ v<<1 ] || p_assignment[ (v<<1)^1 ] );

		for( size_t p = 0; p != p_replaces[v].size(); ++p )
		  {
			// Set assignements of replaces variables
			uint32_t pro = p_replaces[v][p] ^ ( (p_model[v]&1) != 0 );
			
			if( pro != p_model[pro>>1] )
			  { 
				didsomething = true; 
			  }

			p_model[pro>>1] = pro;
			assert( p_replaces[pro>>1].empty() );
		  }
	  }
  
	// Consistency Check 
	for ( uint32_t v = 1; v <= p_variables; ++v )
	  { 
		assert( p_deleted[v] || (p_model[v] != 0 ) ); 
	  }
	return didsomething;
  }

  // Adapted (and translated in readable code) from minisat/SATelite
  // Proceed deleted clauses during resolution and reset model assignments if necessary
  // Clauses are stored in "p_elimclauses" in following manner:
  // 1. If "var" is eliminated, the complete occurence list of one polarity is stored
  // 2. The occurence of "var" is stored in front of the clause
  // 3. After each clause the size of the clause is stored
  // Ex.: clause "( v_1 + v_2 + var )" => "var v_2 v_1 3"
  // The vector is proceeded backwards, checking if all clauses are satisfied without "var"
  // If one clause is not satisfied, the assignment of var is flipped to the opposite polarity
  bool Preprocessor::restoreVariableEliminations( void )
  {
	uint32_t clausesize( 0 );
	bool didsomething(false);

	for( std::vector< uint32_t >::reverse_iterator rit = p_elimclauses.rbegin(); rit != p_elimclauses.rend(); ++rit )
	  {
		// Did we have a clause size argument?
		if( clausesize == 0 )
		  { clausesize = *rit; ++rit;}

		uint32_t pos = *rit;

		// Model of literal correctly setted? Skip clause
		if ( p_model[pos>>1] == pos )
		  {
			// Goto next clause
			rit += (clausesize-1);
			clausesize = 0;
		  }
		// Model of literal incorrectly setted? Go to next literal
		else if ( p_model[pos>>1] != pos )
		  { 
			// Reached last element in clause and clause is not satisfied? Change the assignment!
			if( --clausesize == 0 ) 
			  { 
				didsomething = true;
				p_model[pos>>1] = pos;
			  }
		  }
		// variable was eliminated before setting
		// Set model for variable to true and skip clause
		else if ( p_model[pos>>1] == 0 )
		  {
			didsomething = true;
			p_model[pos>>1] = pos;
		  }
	  }
	return didsomething;
  }

  void Preprocessor::clearRestoreData(uint32_t begin, uint32_t end)
  {
	// First clear replacelist
	for( uint32_t v = 0; v <= end; ++v )
	  {
		if( (v >= begin) && (v <= end) )
		  {
			p_replaces[v].clear();
			p_replacedby[v] = 0;
		  }
		else 
		  {
			// Consistency checks
			assert( p_replacedby[v] == 0 || (p_replacedby[v]>>1) < begin || (p_replacedby[v]>>1) > end );

#ifndef NDEBUG
			size_t size = p_replaces[v].size();
			for( uint32_t i = 0; i != size; ++i )
			  {
				assert( ((p_replaces[v][i]>>1) < begin) || ((p_replaces[v][i]>>1) > end) );
			  }
#endif
		  }
	  }

	// Now clear "p_elimclauses"

	uint32_t clausesize(0);
	uint32_t clausebegin(0);
	bool unit(false);
	bool deleteclauses(false);
	for( int i = (int)p_elimclauses.size()-1; i >= 0; --i )
	  {
		// Did we have a clause size argument?
		if( clausesize == 0 )
		  { 
			clausesize = p_elimclauses[i];
			clausebegin = i;
			--i; 

			unit = (clausesize==1);

			if( deleteclauses )
			  { 
				// reached a new unit, clear deleteclauses status
				if( unit )
				  { deleteclauses = false; }
				// Otherwise delete clausesize entry
				else
				  { p_elimclauses[i+1] = 0; }
			  }
			
		  }

		if( deleteclauses )
		  { 
			p_elimclauses[i] = 0; --clausesize; continue;
		  }

		uint32_t var( p_elimclauses[i] >> 1);
		// reached deleted var?
		if( (var>=begin) && (var<=end) )
		  {
			if( unit )
			  {
				// We have reached a clause from a deleted var
				// Delete all these clauses
				deleteclauses = true;
				p_elimclauses[i] = 0;
				p_elimclauses[i+1] = 0;
			  }
			else
			  {
				// We found a deleted var in list of a clause from another deleted var
				// Just delete this clause
				for( int j = clausebegin; j > i; --j )
				  { 
					p_elimclauses[j] = 0; 
				  }
				for( ; clausesize == 0 ; --clausesize )
				  { 
					p_elimclauses[i] = 0; --i;
				  }
			  }
		  }

		--clausesize;
	  }

	// Now delete all the "0" from "p_elimclauses"

	uint32_t p = 0;
	uint32_t q = 0;
	for( ; p != p_elimclauses.size(); ++p )
	  {
		if( p_elimclauses[p] == 0 )
		  { continue;}

		p_elimclauses[q] = p_elimclauses[p];
		++q;
	  }
	p_elimclauses.resize(q);
 }

  /* UPLA */

  /* Begin: some helper functions */

  // Backtracks to decision literal "declit". 
  void Preprocessor::backtrackUPLA (uint32_t declit)
  {
	// Initialization.
	uint32_t lit(p_decisionStack[--p_dsEndIndex]);
	
	// This loop assumes that we have a dummy assignment at the first 
	// position of the decision stack, which has been assigned on decision level 0. 
	while( lit != declit )
	  {
		// Undo the current assignment.
		p_assignment[lit] = false;

		p_forcing[lit>>1].clearReason();
		  
		// Get the next assignment to be undone.
		lit = p_decisionStack[--p_dsEndIndex];
	  } 

	// Undo the assignment of "declit"
	p_assignment[lit] = false;

	assert(p_forcing[lit>>1].noReason());
  
	// Update "p_dsImplIndex".
	p_dsImplIndex = p_dsEndIndex;
	return;
  } 


  // Adds a decision/implication to the temp upla decision stack.
  void Preprocessor::addUnit (uint32_t lit)
  {    
	// The variable corresponding to "lit" has to be undefined.
	assert(!p_assignment[lit] && !p_assignment[lit ^ 1]); 
	assert( lit > 1 );

	// Update "p_assignment".
	p_assignment[lit] = true;

	p_forcing[lit>>1] = Reason();
    
	// Push "lit" onto the decision stack.    
	p_decisionStack[p_dsEndIndex++] = lit; 
  }

  /* End: some helper fucntions */

  // Performs "Unit Propagation Lookahead". 
  // Returns FALSE if the formula is unsatisfiable, otherwise TRUE will be returned.
  bool Preprocessor::upla ( uint32_t& didsomething, bool incremental )
  {
	// Skipif there are to many clauses in the database
	if( ( (p_statistics.binaryClauses>>1) + p_clauseDatabase.size() ) > 300000 )
	  { return true; }

	if( p_control->getVerbosity() > 2 )
	  { std::cout << "c Performing UPLA..." << std::endl; }

	updateWatches(false);

	// Initialization.
	std::vector<uint32_t> posimplications;
	std::vector<uint32_t> negimplications; 

	std::vector<uint32_t> remtmp;
	std::vector<bool> nextcandidates( p_variables+1,false );

	std::vector< std::pair< uint32_t, uint32_t > > newequivalences;

	uint32_t constants( p_statistics.uplaConstantVariables );
	uint32_t uplaequivs( p_statistics.uplaEuivalentVariables );

	bool bcpres1(true);
	bool bcpres2(true);

	p_uplaheap.clear();
	
	uint32_t low(1);
	if( incremental )
	  { low = p_firstPreVarIndex; }

	for(uint32_t v = low; v <= p_variables; ++v )
	  {
		if( p_deleted[v] )
		  { continue; }

		p_uplaactivity[v] = p_binaries[v<<1].size() + p_binaries[(v<<1)^1].size() + p_occur[v<<1].size() + p_occur[(v<<1)^1].size();

		if( p_uplaactivity[v] == 0 )
		  { 
			continue; 
		  }

		p_uplaheap.insert(v);
	  } 

	uint32_t tmpimplindex(p_dsImplIndex);
	
	// Perform UPLA as long as mandatory implications can be found. 
	while( !p_uplaheap.empty() )
	  {
		// Check all unassigned variables.
		uint32_t tmppos = p_dsEndIndex;

		while( !p_uplaheap.empty() )
		  {
			// Initialization.
			uint32_t lit(p_uplaheap.top()<<1);

			nextcandidates[lit>>1] = false;
			posimplications.clear();
			negimplications.clear();

			// Current variable still unassigned?
			if (p_assignment[lit] || p_assignment[lit ^ 1])
			  { continue; }

			// Add "lit^1" as a decision to the decision stack.
			addUnit( lit^1 );
		  
			// Initialization.
			uint32_t pos(p_dsEndIndex);

			// What about the effects of this decision?	
			bcpres1 = p_core->deduce();

			// store all implications, triggered by decision of "lit^1"
			for(uint32_t i = pos; i < p_dsEndIndex; ++i)
			  {
				negimplications.push_back( p_decisionStack[i] ); 
			  }

			// Backtrack.
			backtrackUPLA(lit^1);

			// If there are no conflict and no implications for "lit^1", we don't have to consider "lit"
			if( bcpres1 && negimplications.empty() )
			  { continue;}

			// Add "lit" as a decision to the decision stack.
			addUnit( lit );

			// What about the effects of this decision?		  
			bcpres2 = p_core->deduce();
				
			// store all implications, triggered by decision of "lit"
			for(uint32_t i = pos; i < p_dsEndIndex; ++i)
			  { 
				posimplications.push_back( p_decisionStack[i] ); 
			  }

			// Backtrack.
			backtrackUPLA(lit);

			// Both assumption leads to a conflict => formula UNSAT
			if( !bcpres1 && !bcpres2 )
			  { 
				if( p_control->getVerbosity() > 1 )
				  { std::cout << "c UPLA: both polarities of " << (lit>>1) << " are conflicting!" << std::endl; }
				return false; 
			  }

			// Assumption "lit" leads to a conflict => imply "lit^1"
			if( bcpres1 && !bcpres2 )
			  { 	
				// Add "real" implication and perform "real" deduction
			    p_core->addImplication( lit^1 );

				++p_statistics.uplaConstantVariables;

			    if ( !p_core->deduce() )
				  { 
					return false; 
				  }

			    didsomething |= 0x4;
			  }
			// Assumption "lit^1" leads to a conflict => imply "lit"
			else if( !bcpres1 && bcpres2 )
			  { 
				// Add "real" implication and perform "real" deduction
			    p_core->addImplication( lit );

				++p_statistics.uplaConstantVariables;

			    if ( !p_core->deduce() )
				  { 
					return false; 
				  }

			    didsomething |= 0x4;
			  }
			// No conflict, but maybe we have learnt some constants or equivalences
			else
			  {
				size_t possize (posimplications.size());
			    for( size_t i = 0; i != possize; ++i )
			      {
					uint32_t posimpl(posimplications[i]);

					if( p_assignment[posimpl] || p_assignment[posimpl^1] || p_donttouch[posimpl>>1] ) 
					  { continue; }

					size_t negsize(negimplications.size());
					for( size_t j = 0; j != negsize; ++j )
					  {
						uint32_t negimpl(negimplications[j]);

						// New Constant
						if( posimpl == negimpl )
						  {
							didsomething |= 0x4;

							++p_statistics.uplaConstantVariables;

							// Constant already assigned to opposite polarity? => problem UNSAT
							if( p_assignment[(posimpl)^1] )
							  { return false; }

							p_core->addImplication( posimpl );
						  }
						// New Equivalence
						else if( posimpl == (negimpl^1) )
						  {
							// Add the binaries, which are responsible for the equivalence

							uint32_t firstlit(lit);
							uint32_t secondlit(posimpl);

							if( p_donttouch[secondlit>>1] )
							  { 
								if( !p_donttouch[firstlit>>1] )
								  { 
									secondlit = lit;
									firstlit = posimpl;
								  }
								// Both variables don't touch? Do nothing...
								else
								  { continue; }
							  }

							bool firstbin = addBinary(firstlit, secondlit^1, false);
							bool secondbin = addBinary(firstlit^1, secondlit, false);

							// if both binaries already exists, we have to do nothing...
							if( firstbin || secondbin )
							  {
								didsomething |= 0x04;

								// Remove equivalence anyway... even if it's not new
								newequivalences.push_back(std::make_pair(lit, posimpl));
							  }
						  }
					  }
			      }

			    if ( !p_core->deduce() )
				  { 
					return false; 
				  }
			  }
		  }
		// Every candidate is proceeded, calculate candidates for next round

		// Proceed occurence list of assigned literals for next upla round
		for( uint32_t j = tmppos; j < p_dsEndIndex; ++j )
		  {
			uint32_t litOnStack(p_decisionStack[j]);

			// clear reasons for newly introduced implications on level 0 since corresponding reason clauses will be removed

			p_forcing[litOnStack>>1].clearReason();
			const std::vector< CRef >& occur( p_occur[ litOnStack^1 ] );

			size_t osize( occur.size() );

			for( size_t c = 0; c != osize; ++c )
			  {
				Clause& clause = p_ca[occur[c]];
				uint32_t csize( clause.length() );
					
				for( uint32_t opos = 0; opos != csize; ++opos )
				  {
					uint32_t clit = clause[opos];

					if( !nextcandidates[ clit>>1 ] && !p_assignment[clit] && !p_assignment[clit^1] )
					  {
						p_uplaheap.insert(clit>>1);
						nextcandidates[clit>>1] = true;
					  }
				  }
			  }
		  }
	  }

 
	// Set Implication Pointer for next Simplification
	p_dsImplIndex = tmpimplindex;

	// Order of variables changes during UPLA => reorder
	for( size_t c = 0 ; c != p_clauseDatabase.size(); ++c )
	  {	p_ca[p_clauseDatabase[c]].sort(); }

	// Remove n-nary and ternary from watch list
	for( uint32_t v = 1; v <= p_variables; ++v )
	  {
		if( p_binaries[v<<1].empty() && p_binaries[(v<<1)^1].empty() )
		  {	continue; }

		for( uint32_t literal = (v<<1); literal < ((v<<1)+2); ++literal )
		  {	
			std::vector<Watcher>& watches( p_binaries[literal] );

			size_t size( watches.size() );
			for( size_t i = 0; i != size; ++i )
			  {
				if( !watches[i].isBinary() )
				  {
					watches[i--] = watches[--size];
					watches.pop_back();
				  }
			  }
			std::sort( watches.begin(), watches.end(), WatchedSorter() );
		  }
	  }

	// Propagate units
	if( !propagateUnits() )
	  { return false; }


	// Now add the new equivalences
	for( size_t i = 0; i != newequivalences.size(); ++i )
	  {
		uint32_t firstlit = newequivalences[i].first; 
		uint32_t secondlit = newequivalences[i].second;

		if( p_deleted[firstlit>>1] )
		  { 			
			// Both variables already deleted? Or deleted variable already replaced by "secondlit"?
			// Do nothing...
			if( p_deleted[secondlit>>1] || ( p_replacedby[firstlit>>1] = secondlit ) )
			  { 
				continue; 
			  }
			
			// Change replace lit
			firstlit = p_replacedby[firstlit>>1]; 
			assert( !p_deleted[firstlit>>1]); 
		  }
		else if( p_deleted[secondlit>>1] )
		  {
			// "secondlit" already replaced by "firstlit"?
			if ( ( p_replacedby[secondlit>>1] = firstlit ) )
			  { 
				continue; 
			  }
			// Change replace lit
			secondlit = p_replacedby[secondlit>>1]; 
		  }

		removeBinary( firstlit^1, secondlit );
		removeBinary( firstlit, secondlit^1 );

		if( p_donttouch[secondlit>>1] )
		  { 
			removeBinary( secondlit, firstlit^1 );
			removeBinary( secondlit^1, firstlit );
			continue; 
		  }

		++p_statistics.uplaEuivalentVariables;

		if ( !replaceVariable( secondlit, firstlit ) )
		  { return false; }
	  }

	if( p_control->getVerbosity() > 1 && ( (p_statistics.uplaConstantVariables - constants) || (p_statistics.uplaEuivalentVariables - uplaequivs) ) )
	  {
		std::cout << "c upla constants         : " << (p_statistics.uplaConstantVariables - constants) << std::endl;
		std::cout << "c upla equivalences      : " << (p_statistics.uplaEuivalentVariables - uplaequivs) << std::endl;
	  }

	return propagateUnits();      
  }

}
