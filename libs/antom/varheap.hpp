
#ifndef VARHEAP_HPP
#define VARHEAP_HPP

/********************************************************************************************
varheap.hpp -- Copyright (c) 2016, Tobias Schubert

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
#include <vector>

namespace antom
{
  // The "VarHeap" class.
  template <typename T>
  class VarHeap
  {

  public:

    // Constructor.
    VarHeap (const std::vector<T>& act) : 
      m_heap(),
      m_position(),
      m_size(0),
      m_variables(0),
      m_activity(act),
      m_status()
    { } 

	~VarHeap ( void ) {}

    // Updates all data structures to be able to handle "var" variables.
    void resize (uint32_t var) 
    {
      // Resize "m_position".
      m_position.resize(var + 1, -1);

      // Resize "m_heap".
      m_heap.resize(var, 0); 

      // Update "m_variables".
      m_variables = var;
    }

    // Clears the entire heap.
    void clear (void)
    {
      for (uint32_t m = 0; m < m_size; ++m)
	{ m_position[m_heap[m]] = -1; }
      m_size = 0; 
    }

    // Saves the current status.
    void saveStatus (void)
    {
      // Store all status variables/flags.
      m_status.size = m_size;
      m_status.variables = m_variables; 

      // Resize all vectors.
      m_status.position.resize(m_variables + 1, -1); 
      m_status.heap.resize(m_variables, 0); 

      // Store all vectors. 
      for (uint32_t v = 1; v <= m_variables; ++v)
		{ m_status.position[v] = m_position[v]; }
      for (uint32_t p = 0; p < m_size; ++p)
		{ m_status.heap[p] = m_heap[p]; assert(m_position[m_heap[p]] != -1); }
    }

    // Restores the status saved before by "saveStatus()". 
    void restoreStatus (void)
    {
      // Restore all status variables/flags.
      m_size = m_status.size;
      m_variables = m_status.variables; 

      // Resize all vectors.
      m_position.resize(m_variables + 1, -1); 
      m_heap.resize(m_variables, 0); 

      // Restore all vectors. 
      for (uint32_t v = 1; v <= m_variables; ++v)
	{ m_position[v] = m_status.position[v]; }
      for (uint32_t p = 0; p < m_size; ++p)
	{ m_heap[p] = m_status.heap[p]; }
    }

    // Deletes the status saved before by "saveStatus()". 
    void deleteStatus (void)
    {
      std::vector<uint32_t>().swap(m_status.heap);
      std::vector<int>().swap(m_status.position);
    }

    // Returns whether the heap is empty or not.
    bool empty (void) const { return (m_size == 0); }

    // Returns the current size of "m_heap".
    uint32_t size (void) const { return m_size; }

    // Returns whether "var" is an element of "m_heap".
    bool inHeap (uint32_t var) const 
    {
      // "var" has to be less or equal "m_variables".
      assert(var <= m_variables);

      // Return whether "var" is part of the heap.
      return (m_position[var] > -1); 
    }

    // Updates the position of "var" within the heap.
    void update (uint32_t var)
    {
      // "var" has to be less or equal "m_variables".
      assert(var <= m_variables);

      // "var" has to be an element of "m_heap".
      assert(m_position[var] > -1);

      // Ensure that the heap property holds. Assumes, that "var's" 
      // activity has been incremented by the SAT solving core. 
      shiftUpwards(m_position[var]); 
    }

    // Inserts variable "var" into "m_heap". 
    void insert (uint32_t var) 
    {
      // "var" has to be less or equal "m_variables".
      assert(var <= m_variables);

      // If "var" is an element of "m_heap", we've got a problem.
      assert(m_position[var] == -1); 

      // Update "m_position".
      m_position[var] = m_size;  
      
      // Add "var" to "m_heap".
      m_heap[m_size] = var;
      
      // Increment "m_size".
      ++m_size; 
	
      // Ensure that the heap property holds.
      shiftUpwards(m_position[var]);
    }

    // Returns the root variable.
    uint32_t top (void)
    {
      // If "m_heap" is empty, we've got a problem.
      assert(m_size > 0); 
      
      // Get the root variable.
      uint32_t var = m_heap[0]; 

      // Decrement "m_size".
      --m_size;
      
      // Overwrite "m_heap[0]" with the last element of "m_heap".
      m_heap[0] = m_heap[m_size];

      // Update "m_position".
      m_position[var] = -1;
   
      // If we removed the last element from the heap, we can skip the following operations.
      if (m_size > 0)
	{
	  // Update "m_position".
	  m_position[m_heap[0]] = 0; 
	  
	  // Ensure that the heap property holds. 
	  shiftDownwards(0);
	}
	  
      // Return "var".
      return var;
    }

    // Removes "var" from the heap.
    void remove (uint32_t var)
    {
      // If "m_heap" is empty, we've got a problem.
      assert(m_size > 0); 
      
      // Initialization.
      int pos(m_position[var]); 

      // If "var" is not part of the heap, we've got a problem.
      assert(pos > -1); 

      // Decrement "m_size".
      --m_size;
      
      // Overwrite "m_heap[pos]" with the last element of "m_heap".
      m_heap[pos] = m_heap[m_size];

      // Update "m_position".
      m_position[var] = -1;
   
      // If we removed the right-most element from the heap, we can skip the following operations.
      if ((uint32_t) pos != m_size)
	{
	  // Update "m_position".
	  m_position[m_heap[pos]] = pos; 
	  
	  // Ensure that the heap property holds. 
	  shiftDownwards(pos);
	}

      // Consistency check.
      assert(m_position[var] == -1);
    }

  private:

    // Returns the position of the "father" of the element stored on position "pos".
    uint32_t father (uint32_t pos) const { return ((pos - 1) >> 1); }

    // Returns the position of the left "son" of the element stored on position "pos".
    uint32_t left (uint32_t pos) const { return ((pos << 1) + 1); }

    // Returns the position of the right "son" of the element stored on position "pos".
    uint32_t right (uint32_t pos) const { return ((pos + 1) << 1); }

    // Ensures the heap property by shifting the element on position "pos" of "m_heap" upwards.
    void shiftUpwards (uint32_t pos)
    {
      // Get the variable stored on position "pos".
      uint32_t var = m_heap[pos]; 
      
      // Determine the correct position of "var" within "m_heap".
      while (pos > 0 && m_activity[var] > m_activity[m_heap[father(pos)]])
	{
	  m_heap[pos]             = m_heap[father(pos)];
	  m_position[m_heap[pos]] = pos;
	  pos                     = father(pos);
	}
      
      // Store "var" at position "pos".
      m_heap[pos]     = var;
      m_position[var] = pos;
    }

    // Ensures the heap property by shifting the element on position "pos" of "m_heap" downwards.
    void shiftDownwards (uint32_t pos)
    {      
      // Get the variable stored on position "pos".
      uint32_t var = m_heap[pos]; 

      // Determine the correct position of "var" within "m_heap".
      while (left(pos) < m_size)
	{
	  uint32_t r = right(pos);
	  uint32_t child = r < m_size && m_activity[m_heap[r]] > m_activity[m_heap[left(pos)]] ? r : left(pos);
	  	
	  if (m_activity[m_heap[child]] <= m_activity[var])
	    { break; }
	  
	  m_heap[pos]             = m_heap[child];
	  m_position[m_heap[pos]] = pos;
	  pos                     = child; 
	}
      
      // Store "var" at position "pos".
      m_heap[pos]     = var;
      m_position[var] = pos;
    }

    // The heap.
    std::vector<uint32_t> m_heap;

    // The position of a particular variable within "m_heap".
    std::vector<int> m_position;

    // The current size of "m_heap".
    uint32_t m_size; 

    // The maximum number of variables for which memory has been reserved.
    uint32_t m_variables;

    // The variables' activities.
    const std::vector<T>& m_activity;

    // A struct to be able to store the current state of the variable ordering.
    struct 
    {
      std::vector<uint32_t> heap;
      std::vector<int> position;
      uint32_t size; 
      uint32_t variables;
    } m_status; 

  };
}

#endif
