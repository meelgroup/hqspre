
#ifndef CLAUSE_HPP
#define CLAUSE_HPP

/********************************************************************************************
clause.hpp -- Copyright (c) 2016, Tobias Schubert, Sven Reimer

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
#include <cassert>
#include <algorithm>
#include "allocator.hpp"
//#include "literal.hpp"

namespace antom
{

  typedef RegionAllocator<uint32_t>::Ref CRef;

  // The "Clause" class.
  class Clause
  {
  private:

	struct {
	  unsigned reloced : 1;
	  unsigned length  : 31;
	  unsigned lbd     : 32; } m_header;

	friend class ClauseAllocator;

	// The signature of the clause.
	unsigned long long m_sign;

  public:

	// Constructor.
	// Attentention! The memory for the clause has to be allocated in advance, otherwise we run into errors
	Clause (uint32_t* lits, uint32_t lbd, uint32_t length) :
	  m_sign(0)
	{
	  assert(lbd > 0);
	  assert(length > 0); 
	  m_header.reloced = 0;
	  m_header.lbd = lbd;
	  m_header.length = length;

	  // Copy clause
	  for (uint32_t i = 0; i < length; ++i) 
		{
		  getLiterals()[i] = lits[i];
		}
	}

	// Constructor.
	// Attentention! The memory for the clause has to be allocated in advance, otherwise we run into errors
	Clause (const std::vector<uint32_t>& lits, uint32_t& lbd, uint32_t& length) :
	  m_sign(0)
	{
	  // Consistency check.
	  //assert(m_literals != NULL); 
	  assert(lbd > 0);
	  assert(length > 0); 
	  m_header.reloced = 0;
	  m_header.lbd = lbd;
	  m_header.length = length;

	  // Copy clause
	  for (uint32_t i = 0; i < length; ++i) 
		{
		  getLiterals()[i] = lits[i];
		}
	}
    
	~Clause (void) {}

	uint32_t* getLiterals()
	{ return (uint32_t*)((char*)this + sizeof(Clause)); }

	const uint32_t* getLiterals() const
	{ return (uint32_t*)((char*)this + sizeof(Clause)); }

	uint32_t operator[] (uint32_t i) const
	{ return *(getLiterals()+i); }
	uint32_t& operator[] (uint32_t i)
	{ return *(getLiterals()+i); }

	bool operator==(const Clause& other ) const 
	{ return getLiterals() == other.getLiterals();}



	// Clause will be reallocated from time to time
	bool reloced (void) const { return (m_header.reloced == 1); }
	CRef relocation (void) const { assert(m_header.reloced == 1); return getLiterals()[0]; }
	void relocate (CRef c) { m_header.reloced = 1; getLiterals()[0] = (uint32_t)c; }

	// Returns the "Literals Blocks Distance".
	uint32_t lbd (void) const 
	{ 
	  return m_header.lbd;
	}

	// Returns whether the clause was learned
	bool isLearned (void) const 
	{ 
	  return (m_header.lbd>1);
	}

	void markForDeletion(void)
	{
	  m_header.lbd = 0;
	}

	// Returns whether clause is marked as to delete
	bool toDelete(void) const 
	{ 
	  return (bool)(m_header.lbd == 0);
	}


	// Returns the clause length.
	uint32_t length (void) const 
	{
	  return m_header.length;
	}

	// Returns signature of clause.
	unsigned long long sign (void) const { return m_sign; }

	// Sets the "Literals Block Distance" to "lbd".
	void setLBD (uint32_t lbd) 
	{ 
	  assert(lbd < (1 << 16));
	  m_header.lbd = lbd;
	}

	// Sets the clause length to "l".
	void setLength (uint32_t l) 
	{
	  assert(l > 0); 
	  m_header.length = l;
	}

	// Sets the signature of clause to "s".
	//void setSign (uint32_t s) { assert(s > 0); m_sign = s; }
	void setSign (unsigned long long s) 
	{ 
	  assert(s > 0); 
	  m_sign = s; 
	}

	int hasLitPolarity( uint32_t lit ) const

	{
	  const uint32_t* lits = getLiterals();
	  for( unsigned int pos = 0; pos != m_header.length; ++pos )
		{
		  if( lits[ pos ] == lit )
			{
			  return +1;
			}
		  else if( lits[ pos ] == (lit^1) )
			{
			  return -1;
			}
		}
	  return 0;
	}   

	void calcSign (void)
	{
	  m_sign = 0;

	  uint32_t* lits = getLiterals();
	  for(uint32_t pos = 0; pos != m_header.length; ++pos)
		{
		  m_sign |= 1ULL << (lits[pos] % 64);
		}
	} 

	void sort (void)
	{
	  uint32_t* literals = getLiterals();
	  std::sort(literals, literals + m_header.length );
	}

	// prints literals of clause
	void printLits( void ) const;
	void print (void) const;
  };

  // Adopted from minisat

  // Undefined reference for dummy references in case a clause was deleted
  const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;	
  // ClauseAllocator -- a simple class for allocating memory for clauses:
  class ClauseAllocator : public RegionAllocator<uint32_t>
  {
  private:
	static uint32_t clauseWord32Size(uint32_t size)
	{
	  return (sizeof(Clause) + (sizeof(uint32_t) * size )) / sizeof(uint32_t); 
	}
	
  public:

	ClauseAllocator(uint32_t initialCap) : 
	  RegionAllocator<uint32_t>(initialCap)
	{}


	void copyTo(ClauseAllocator& to)
	{
	  RegionAllocator<uint32_t>::copyTo(to); 
	}

	void moveTo(ClauseAllocator& to)
	{
	  RegionAllocator<uint32_t>::moveTo(to); 
	}

	CRef alloc (Clause& c)
	{
	  assert(sizeof(uint32_t) == 4);

	  CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(c.length()));
	  new (getAdress(cid)) Clause(c.getLiterals(), c.lbd(), c.length());

	  return cid;
	}

	CRef alloc (uint32_t* lits, uint32_t lbd, uint32_t length)
	{
	  assert(sizeof(uint32_t) == 4);

	  CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(length));
	  new (getAdress(cid)) Clause(lits, lbd, length);

	  return cid;
	}

	CRef alloc (const std::vector<uint32_t>& lits, uint32_t lbd, uint32_t length)
	{
	  assert(sizeof(uint32_t) == 4);

	  CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(length));
	  new (getAdress(cid)) Clause(lits, lbd, length);

	  return cid;
	}

	void allocRegion( uint32_t size )
	{ RegionAllocator<uint32_t>::allocRegion(size); }

	Clause& operator[](Ref r) 
	{ return (Clause&)RegionAllocator<uint32_t>::operator[](r); }

	const Clause& operator[](Ref r) const 
	{ return (Clause&)RegionAllocator<uint32_t>::operator[](r); }

	inline Clause* getClause (Ref r)
	{ return (Clause*)RegionAllocator<uint32_t>::getAdress(r); }

	inline Clause* getClause (Ref r) const
	{ return (Clause*)RegionAllocator<uint32_t>::getAdress(r); }

	uint32_t getReference (const Clause* t) 
	{ return RegionAllocator<uint32_t>::getReference((uint32_t*)t); }

	void free(CRef cid)
	{
	  Clause& c = operator[](cid);
	  RegionAllocator<uint32_t>::free(clauseWord32Size(c.length()));
	}

	void freeLiterals( uint32_t numberOfLits ) 
	{ RegionAllocator<uint32_t>::free(numberOfLits); }

	uint32_t getSize( void ) const
	{ return RegionAllocator<uint32_t>::getSize(); }

	uint32_t getCapacity( void ) const
	{ return RegionAllocator<uint32_t>::getCapacity(); }
  
	void reloc (CRef& cr, ClauseAllocator& to)
	{
	  Clause& c = operator[](cr);
	  if (c.reloced()) 
		{
		  cr = c.relocation(); 
		  return; 
		}
        
	  cr = to.alloc(c);
	  c.relocate(cr);
	}

	void reset( void )
	{ RegionAllocator<uint32_t>::reset(); }
	
  };
}

#endif
