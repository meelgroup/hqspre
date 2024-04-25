#ifndef REASON_HPP
#define REASON_HPP

/********************************************************************************************
reason.hpp -- Copyright (c) 2016, Sven Reimer

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

  // Reason handler
  // Stores the reason for the implication of a variable
  // Handles binary, ternary and n-nary clauses 
  // Adapted from Cryptominisat
  class Reason {
  public:

	//TODO: introduce Lit class

	// Constructor for binary and n-nary clauses:
	// Stores the second literal or clause position in data1
	Reason(uint32_t lit, bool isBinary)
	{
	  clauseType = isBinary?BINARY:NNARY;

	  data1 = lit;
	  data2 = 0;
	}

	// Constructor for ternary clause:
	// Stores the second literal in data1
	// Stores the third literal in data2
	Reason(uint32_t lit1, uint32_t lit2)
	{
	  clauseType = TERNARY;
	  data1 = lit1;
	  data2 = lit2;
	}


	// No Reason
	Reason(void)
	{
	  clauseType = NOTYPE;
	  data1 = 0;
	  data2 = 0;
	}

	bool isBinary(void) const
	{
	  return (clauseType == BINARY);
	}

	bool isTernary(void) const
	{
	  return (clauseType == TERNARY);
	}

	bool isClause(void) const
	{
	  return (clauseType == NNARY);
	}

	void setClause(CRef& ref) 
	{
	  assert(isClause());
	  data1 = ref;
	}

	CRef getClause(void) const
	{
	  assert(isClause());
	  return (CRef)data1;
	}

	uint32_t getSecondLit(void) const
	{
	  assert( isBinary() || isTernary() );
	  return data1;
	}

	uint32_t getThirdLit(void) const
	{ 
	  assert( isTernary() );
	  return data2;
	}

	// Returns true if no reason is set
	bool noReason(void) const
	{
	  return (clauseType == NOTYPE);
	}

	// Returns true if reason is set
	bool hasReason(void) const
	{
	  return (clauseType != NOTYPE);
	}

	// check whether the clause "cref" forces this reason
	bool forcedby( const CRef& cref ) const 
	{
	  if( isBinary() || isTernary() )
		{
		  // To be safe, return "true"
		  return true;
		}
	  if( noReason() )
		{ 
		  return false; 
		}
	  return (cref == (CRef)data1);
	}
	
	void clearReason(void) 
	{
	  clauseType = NOTYPE;
	  data1 = 0;
	  data2 = 0;
	}

	void print( ClauseAllocator& ca ) const
	{
	  std::cout << "reason of type ";
	  switch(clauseType)
		{
		case NOTYPE: std::cout << "no reason"; break;
		case BINARY: std::cout << "binary"; break;
		case TERNARY: std::cout << "ternary"; break;
		case NNARY: std::cout << "n-nary"; break;
		default: std::cout << "unvalid reason type"; assert(false); break;
		}
	  std::cout << std::endl;

	  std::cout << "clause: " << std::endl;
	  if( isBinary() || isTernary() )
		{
		  std::cout << Lit(getSecondLit());
		  if( isTernary() )
			{
			  std::cout << " " << Lit(getThirdLit());
			}
		  std::cout << std::endl;
		}
	  else if (isClause() )
		{
		  ca[getClause()].print(); 
		  assert(!ca[getClause()].toDelete() );
		}
	  else
		{
		  std::cout << "no forced Reason" << std::endl;
		}
	}

  private:

	uint32_t data1:32;
	uint32_t data2:30;
	clausetype clauseType:2;
  };

  // Complete Reason for "analyze
  class ReasonComplete {

  public:

	// Constructor 
	ReasonComplete(const Reason& original, uint32_t conflictLit, const ClauseAllocator& ca)
	{
	  if(original.isBinary() || original.isTernary() )
		{
		  lits[0] = conflictLit;
		  lits[1] = original.getSecondLit();
		  if( original.isTernary() )
			{
			  lits[2] = original.getThirdLit();
			  clauseType = TERNARY;
			  clauseSize = 3;
			}
		  else
			{
			  lits[2] = 0;
			  clauseType = BINARY;
			  clauseSize = 2;
			}
		  clause = NULL;
		}
	  else if( original.isClause() )
		{
		  lits[0] = 0; lits[1] = 0; lits[2] = 0;
		  clause = ca.getClause(original.getClause());
		  clauseType = NNARY;
		  clauseSize = clause->length();
		}
	  else
		{
		  lits[0] = 0; lits[1] = 0; lits[2] = 0;
		  clause = NULL;
		  clauseType = NOTYPE;
		  clauseSize = 0;
		}
	}

	uint32_t size(void) const
	{
	  return clauseSize;
	}

	bool isBinary(void) const
	{
	  return (clauseType == BINARY);
	}

	bool isTernary(void) const
	{
	  return (clauseType == TERNARY);
	}

	bool isClause(void) const
	{
	  return (clauseType == NNARY);
	}

	uint32_t operator[](const uint32_t i) const
	{
	  if ( clauseType == NNARY )
		{
		  assert(clause != NULL);
		  assert( i < clause->length() );
		  return (*clause)[i];
		}
	  else 
		{
		  assert( clauseType == BINARY || clauseType == TERNARY );
		  assert( i <= clauseType );
		  return lits[i];
		}
	}

	void print( void ) const
	{
	  std::cout << "reason of type ";
	  switch(clauseType)
		{
		case NOTYPE: std::cout << "no reason"; break;
		case BINARY: std::cout << "binary"; break;
		case TERNARY: std::cout << "ternary"; break;
		case NNARY: std::cout << "n-nary"; break;
		default: std::cout << "unvalid reason type"; assert(false); break;
		}
	  std::cout << std::endl;

	  std::cout << "clause: " << std::endl;
	  if( isBinary() || isTernary() )
		{
		  std::cout << Lit(lits[0]) << " " << Lit(lits[1]);
		  if( isTernary() )
			{
			  std::cout << " " << Lit(lits[2]);
			}
		  std::cout << std::endl;
		}
	  else if (isClause() )
		{
		  clause->printLits(); 
		}
	  else
		{
		  std::cout << "no forced Reason" << std::endl;
		}
	}
	

  private:

	clausetype clauseType;
	Clause* clause;
	uint32_t clauseSize;
	uint32_t lits[3];

  };
}

#endif
