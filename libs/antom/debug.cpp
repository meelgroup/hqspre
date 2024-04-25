
#ifndef DEBUG_HPP
#define DEBUG_HPP

/********************************************************************************************
debug.cpp -- Copyright (c) 2016, Sven Reimer

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

#include <algorithm>
#include <iostream>
#include <cassert>
#include <vector>

#include "antom.hpp"
#include "solverstate.hpp"
#include "core.hpp"
#include "preprocessor.hpp"

namespace antom {
  
  // prints literals of clause
  void Clause::printLits( void ) const
  {
	const uint32_t* literals = getLiterals();
	assert( literals != NULL );
	
	for( uint32_t pos = 0; pos != m_header.length; ++pos)
	  {
		std::cout << Lit(literals[pos]) << " "; 
	  }
	
	std::cout << std::endl;
  }

  void Clause::print (void) const
  {
	printLits();
	std::cout << "lbd: " << lbd() << " length: " << length();
	std::cout << " reloced: " << reloced() << std::endl;
  }

  void Core::printClause( Clause* clause, bool assignment ) const
  {
	assert( clause != NULL );
	uint32_t size = clause->length();
	for( uint32_t pos = 0; pos != size; ++pos)
	  {
		std::cout << Lit( (*clause)[pos]) << " "; 
		if( assignment )
		  { std::cout << "[" << isAssigned((*clause)[pos]) << "] "; }
	  }
	std::cout << std::endl;
  }

  // Returns:
  // "-1" if literal is assigned to false
  // " 1" if literal is assigned to true
  // " 0" if literal is unassigned
  int Core::isAssigned( uint32_t lit ) const 
  {
  if( m_assignment[lit] )
	  {
		assert( !m_assignment[lit^1] );
		return 1;
	  }
	else if ( m_assignment[lit^1] )
	  {
		return -1;
	  }
	return 0;
  }

  int Preprocessor::isAssigned( uint32_t lit ) const
  {
	if( p_assignment[lit] )
	  {
		assert( !p_assignment[lit^1] );
		return 1;
	  }
	else if ( p_assignment[lit^1] )
	  { 
		return -1;
	  }

	return 0;
  }

  void Preprocessor::printOccurenceList( uint32_t lit ) const
  {
	for( uint32_t o = 0; o != p_occur[lit].size(); ++o )
	  {
		p_ca[p_occur[lit][o]].print();
	  }
	std::cout << std::endl;
  }

  void Core::dumpCNF( bool printAssignment ) const
  {
	// print binary
	for( uint32_t i = 2; i < m_watches.size(); ++i )
	  {
		bool unsatisfied( m_assignment[i^1] );
		for( uint32_t b = 0; b != m_watches[i].size(); ++ b )
		  {
			if( m_watches[i][b].isBinary() && ( m_watches[i][b].getSecondLit() > i) )
			  {
				std::cout << Lit(i) << " ";
				if( printAssignment )
				  { 
					std::cout << "[" << isAssigned(i) << "] "; 
				  }
				std::cout << Lit(m_watches[i][b].getSecondLit());
				if( printAssignment )
				  { 
					uint32_t seclit = m_watches[i][b].getSecondLit();
					unsatisfied &= m_assignment[(seclit)^1];

					std::cout << " [" << isAssigned(seclit) << "] "; 
				  }

				std::cout << " 0";
				if( printAssignment && unsatisfied )
				  { std::cout << " UNSAT"; }
				std::cout << std::endl;
			  }
		  }
	  }

	// print n-nary
	for( uint32_t i = 0; i != m_clauseDatabase.size(); ++i )
	  {
		uint32_t pos(0);
		bool unsatisfied(true);
		const Clause& lits = m_ca[m_clauseDatabase[i]];
		for( ; pos != lits.length(); ++pos )
		  {
			std::cout << Lit( lits[pos] ) << " "; 
			if( printAssignment )
			  { 
				std::cout << "[" << isAssigned(lits[pos]) << "] "; 
				unsatisfied &= m_assignment[lits[pos]^1];
			  }
		  }
		std::cout << "0";
		if( printAssignment && unsatisfied )
		  { std::cout << " UNSAT"; }
		std::cout << std::endl;
	  }
	std::cout << std::endl;
  }

  void Core::printDatabase( bool printOccur, bool printWatches ) const
  {
	m_preprocessor->printDatabase( printOccur, printWatches );
  }

  void Preprocessor::printDatabase( bool printOccur, bool printWatches ) const
  {
	std::cout << "vars: " << std::endl;
	for( uint32_t v = 1; v <= p_variables; ++v )
	  {
		std::cout << v << " del: " << (p_deleted[v]?"T":"F") << " dt: " << (p_donttouch[v]?"T":"F") << std::endl;
	  }

	if( printOccur )
	  {
		std::cout << std::endl << "occurence lists: " << std::endl;
		for( uint32_t v = 1; v <= p_variables; ++v )
		  {
			std::cout << v << ":  (" << p_binaries[(v<<1)].size() << ")"  << std::endl;
			for( uint32_t b = 0; b != p_binaries[v<<1].size(); ++b )
			  {
				assert( p_binaries[(v<<1)][b].isBinary() );
				std::cout << v << " " << Lit(p_binaries[v<<1][b].getSecondLit()) << std::endl;
			  }
			std::cout << "occur: " << p_occur[v<<1].size() << std::endl;
			printOccurenceList(v<<1);

			std::cout << "-" << v << ": (" << p_binaries[(v<<1)^1].size() << ")" << std::endl;
			for( uint32_t b = 0; b != p_binaries[(v<<1)^1].size(); ++b )
			  {
				assert( p_binaries[(v<<1)^1][b].isBinary() );
				std::cout << "-" << v << " " << Lit(p_binaries[(v<<1)^1][b].getSecondLit()) << std::endl;
			  }

			std::cout << "occur: " << p_occur[(v<<1)^1].size() << std::endl;
			printOccurenceList((v<<1)^1);
			std::cout << std::endl;
		  }
	  }

	if( printWatches )
	  {
		std::cout << std::endl << "watch lists: " << std::endl;
		for( uint32_t v = 1; v <= p_variables; ++v )
		  {
			for( uint32_t literal = (v<<1); literal < ((v<<1)+2); ++literal )
			  {
				std::cout << Lit(literal) << ": (" << p_binaries[literal].size() << ")"  << std::endl;

				for( size_t b = 0; b != p_binaries[literal].size(); ++b )
				  {
					bool satisfied(false);
					if( p_binaries[literal][b].isBinary() )
					  {
						uint32_t secondlit(p_binaries[literal][b].getSecondLit());
						if( p_assignment[literal] || p_assignment[secondlit] )
						  { satisfied = true; }
						std::cout << Lit(literal) << " [" << isAssigned(literal) << "] " 
								  << Lit(secondlit) << " [" << isAssigned(secondlit) << "] ";
					  }
					else if ( p_binaries[literal][b].isTernary() )
					  {
						uint32_t secondlit(p_binaries[literal][b].getSecondLit());
						uint32_t thirdlit(p_binaries[literal][b].getThirdLit());
						
						std::cout << Lit(literal) << " [" << isAssigned(literal) << "] " 
								  << Lit(secondlit) << " [" << isAssigned(secondlit) << "] "
								  << Lit(thirdlit) << " [" << isAssigned(thirdlit) << "] ";
					  }
					else
					  {
						assert( p_binaries[literal][b].isClause() );
						Clause& clause(p_ca[p_binaries[literal][b].getClause()]);
						uint32_t csize(clause.length());
						for( uint32_t pos = 0; pos != csize; ++pos )
						  {
							if( p_assignment[clause[pos]] )
							  { satisfied = true; }
							std::cout << Lit(clause[pos]) << " [" << isAssigned(clause[pos]) << "] ";
						  }
					  }
					if( satisfied )
					  { std::cout << "SAT"; }
					std::cout << std::endl;
				  }
			  }
		  }
	  }

	std::cout << "clausedatabase: " << std::endl;

	for( uint32_t c = 0; c != p_clauseDatabase.size(); ++c )
	  {
		std::cout << c << ": ";
		p_ca[p_clauseDatabase[c]].print();
	  }
	std::cout << std::endl;
	std::cout << "decisionstack: " << std::endl;
	for( uint32_t i = 1; i < p_dsEndIndex; ++i )
	  {
		std::cout << i << " " << Lit(p_decisionStack[i]) << std::endl;
	  }

	std::cout << std::endl;
  }

  // Consistency check whether all clauses with index > lastIndex >= m_variables are not used
  // Return false if this property does not hold
  bool Core::checkMaxIndex( uint32_t lastIndex )
	{
	  // Check whether a clause with index > lastIndex is in a watchlist of allow indices
	  uint32_t i(0);
	  for( ; i <= lastIndex; ++i )
		{
		  for( uint32_t literal = (i<<1); literal < ((i<<1)+2); ++literal )
			{
			  
			  for( uint32_t j = 0; j != m_watches[literal].size(); ++j )
				{
				  // Binary clause
				  if( m_watches[literal][j].isBinary())
					{

					  if( (m_watches[literal][j].getSecondLit()>>1) > lastIndex )
						{
						  std::cout << "forbidden binary index: " << (m_watches[literal][j].getSecondLit()>>1) << std::endl;
						  return false;
						}

					}
				  // N-nary claue
				  else
					{
					  const Clause& clause = m_ca[m_watches[literal][j].getClause()];
					  uint32_t size = m_ca[m_watches[literal][j].getClause()].length();
					  for ( uint32_t pos = 0; pos != size; ++pos )
						{
						  if( (clause[pos]>>1) > lastIndex )
							{
							  std::cout << "forbidden n-nary index: " << (clause[pos]>>1) << std::endl;
							  return false;
							}
						}
					}
				}	  
			}
		}

	  // Check whether all watch lists with index > lastIndex is empty
	  for( ; i <= m_variables; ++i )
		{
		  if( !m_watches[i<<1].empty() || !m_watches[(i<<1)^1].empty() )
			{ 
			  std::cout << "index not empty: " << i << std::endl;
			  
			  return false; 
			}
		}
	  return true;
	}

}

#endif
