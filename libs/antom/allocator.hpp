#ifndef ALLOCATOR_HPP
#define ALLOCATOR_HPP

/********************************************************************************************
allocator.hpp -- Copyright (c) 2016, Sven Reimer

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


  // Adopted from minisat
  // RegionAllocator -- a simple class for allocating memory for clauses:
  
  template<class T>
  class RegionAllocator
  {
  private:
	T* r_memory;
	uint32_t r_size;
	uint32_t r_capacity;
	uint32_t r_wasted;

	void setCapacity(uint32_t min_cap)
	{
	  //std::cout << __func__ << " " << min_cap << " current: " << r_capacity << std::endl;
	  if (r_capacity >= min_cap) return;

	  uint32_t prev_cap = r_capacity;
	  while (r_capacity < min_cap)
		{
		  // See minisat Region allocator:
		  // NOTE: Multiply by a factor (13/8) without causing overflow, then add 2 and make the
		  // result even by clearing the least significant bit. The resulting sequence of capacities
		  // is carefully chosen to hit a maximum capacity that is close to the '2^32-1' limit when
		  // using 'uint32_t' as indices so that as much as possible of this space can be used.
		  uint32_t delta = ((r_capacity >> 1) + (r_capacity >> 3) + 2) & ~1;
		  r_capacity += delta;

		  // Overflow
		  if (r_capacity <= prev_cap)
			{
			  exit(0);
			}
		}

	  //std::cout << "capacity: " << r_capacity << " alloc: " << sizeof(T)*r_capacity << std::endl;
	  assert(r_capacity > 0);
	  r_memory = (T*)realloc(r_memory, sizeof(T)*r_capacity);
	}

  public:

	typedef uint32_t Ref;
	// Undefined reference for dummy references in case memory was freed
    enum { Ref_Undef = UINT32_MAX };
	// Reference size for statistics
    enum { Unit_Size = sizeof(uint32_t) };

	explicit RegionAllocator(uint32_t initialCap = 1024*1024) :
	  r_memory(NULL), 
	  r_size(0),
	  r_capacity(0), 
	  r_wasted(0)
	{
	  //std::cout << "init: " << __func__ << " with " << initialCap << std::endl;
	  setCapacity(initialCap);
	}

	~RegionAllocator()
	{
	  if (r_memory != NULL)
		{
		  ::free(r_memory);
		}
	}

	uint32_t size() const { return r_size; }
	uint32_t wasted() const { return r_wasted; }
	void free (uint32_t size) { r_wasted += size; }

	Ref alloc (uint32_t size)
	{ 
	  assert(size > 0);
	  setCapacity(r_size+size);

	  uint32_t prevSize = r_size;
	  r_size += size;
    
	  // Overflow
	  if (r_size < prevSize)
		{
		  exit(0);
		}

	  return prevSize;
	}

	void allocRegion( uint32_t size )
	{
	  r_capacity = size;
	  r_wasted = 0;
	  r_size = 0;
	  r_memory = (T*)realloc(r_memory, sizeof(T)*r_capacity);
	}


	T& operator[](Ref r) 
	{ assert(r < r_size); return r_memory[r]; }
	const T& operator[](Ref r) const 
	{ assert(r < r_size); return r_memory[r]; }

	T* getAdress (Ref r) 
	{ 
	  assert(r < r_size ); 
	  return &r_memory[r]; 
	}
	T* getAdress (Ref r) const
	{ 
	  assert(r < r_size); 
	  return &r_memory[r]; 
	}

	Ref getReference (const T* t)  
	{
	  assert((void*)t >= (void*)&r_memory[0] && (void*)t < (void*)&r_memory[r_size-1]);
	  return  (Ref)(t - &r_memory[0]); 
	}

	void copyTo(RegionAllocator& to) 
	{
	  if (to.r_memory != NULL) 
		{
		  ::free(to.r_memory);
		}

	  to.r_memory = r_memory;
	  to.r_size = r_size;
	  to.r_capacity = r_capacity;
	  to.r_wasted = r_wasted;
	}

	void moveTo(RegionAllocator& to) 
	{
	  copyTo(to);

	  r_memory = NULL;
	  r_capacity = 0;
	  r_size = 0;
	  r_wasted = 0;
	}

	void reset( void )
	{
	  r_size = 0;
	  r_wasted = 0;
	}

  uint32_t getSize( void ) const
  {
	return r_size;
  }

  uint32_t getCapacity( void ) const
  {
	return r_capacity;
  }

  };
}

#endif
