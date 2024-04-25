#ifndef WATCHER_HPP
#define WATCHER_HPP

/********************************************************************************************
watcher.hpp -- Copyright (c) 2016, Sven Reimer

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

  // Watcher class
  // Handles binary and ternary clauses 
  // Adapted from Cryptominisat
  class Watcher {
  public:

	// Constructor for binary clause:
	// Stores the second literal in data1
	// Stores the information whether the clause was learnt in data2
	Watcher(uint32_t lit, bool learnt)
	{
	  clauseType = BINARY;
	  data1 = lit;
	  data2 = learnt;
	}


	// Constructor for ternary and n-nary clause:
	// Stores a second/blocking literal in data1
	// Stores the third literal/clauses position in data2
	Watcher(uint32_t lit1, uint32_t lit2, clausetype type)
	{
	  assert( type == TERNARY || type == NNARY );
	  clauseType = type;
	  data1 = lit2;
	  // data2 is used for clause position in case of n-nary clause
	  data2 = lit1;
	}

	Watcher(void)
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

	clausetype getType(void) const
	{ 
	  return clauseType;
	}

	void setBlockingLiteral( uint32_t blit )
	{
	  assert(isClause());
	  data1 = blit;
	}

	uint32_t getBlockingLiteral(void) const 
	{
	  assert(isClause() || isTernary() );
	  return data1;
	}

	uint32_t getSecondLit(void) const
	{
	  return data1;
	}

	void setSecondLit(uint32_t lit)
	{
	  assert( isBinary() || isTernary() );
	  data1 = lit;
	}

	uint32_t getThirdLit(void) const
	{ 
	  assert( isTernary() );
	  return data2;
	}

	void setThirdLit(uint32_t lit)
	{
	  assert( isTernary() );
	  data2 = lit;
	}

	void setClause(CRef cr)
	{
	  assert(isClause());
	  data2 = (uint32_t)cr;
	}

	CRef getClause(void) const
	{
	  assert(isClause());
	  return (CRef)data2;
	}

	bool isLearnedBinary(void) const
	{
	  assert(isBinary());
	  return (bool)(data2 != 0 );
	}

	void setLearnedBinary(bool learnt)
	{
	  assert(isBinary());
	  // Updated learning status should always be "false"
	  assert(learnt == false);
	  data2 = (uint32_t)learnt;
	}

	void print(ClauseAllocator& ca) const
	{
	  std::cout << "type: ";
	  switch(clauseType)
		{
		case BINARY: std::cout << "binary"; break;
		case TERNARY: std::cout << "ternary"; break;
		case NNARY: std::cout << "n-nary"; break;
		default: assert(false); break;
		}
	  std::cout << std::endl;
	  
	  if( isBinary() || isTernary() )
		{
		  std::cout << "secondlit: " << Lit(data1);
		  if( isBinary() )
			{
			  std::cout << " isLearned: " << data2 << std::endl;;
			}
		  if( isTernary() )
			{
			  std::cout << " thirdlit: " << Lit(data2) << std::endl;
			}
		}
	  else
		{
		  std::cout << "blockinglit: " << Lit(data1) << " cr: " << data2 << std::endl;
		  std::cout << "the clause: " << std::endl;
		  ca[data2].print();
		}
	  
	}

  private:

	uint32_t data1:32;
	uint32_t data2:30;
	clausetype clauseType:2;
  };

  // Sorter structure, sorts watchlist in binary, ternary, n-nary
  struct WatchedSorter
  {
    bool operator() (const Watcher& x, const Watcher& y) const;
  };

  inline bool WatchedSorter::operator() (const Watcher& w1, const Watcher& w2) const
  {
	assert( w2.isBinary() || w2.isTernary() || w2.isClause() );
	assert( w1.isBinary() || w1.isTernary() || w1.isClause() );
    if (w2.isBinary()) 
	  {
		// Sort binaries by index for duplicate checks
		if( w1.isBinary() && (w1.getSecondLit() < w2.getSecondLit() ) )
		  {
			return true;
		  }
		else
		  { 
			return false;
		  }
	  }
    //w2 is not binary, but w1 is, so w1 must be first
    if (w1.isBinary()) 
	  { return true; }

    //from now on, none is binary.
    if (w2.isTernary()) 
	  { return false; }
    if (w1.isTernary()) 
	  { return true; }

    //from now on, none is binary or ternary
    //don't bother sorting these
    return false;
  }

}

#endif
