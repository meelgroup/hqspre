
#ifndef CONTROL_HPP
#define CONTROL_HPP

/********************************************************************************************
control.hpp -- Copyright (c) 2016, Tobias Schubert

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
#include <cstddef>
#include <vector>
#include <sys/resource.h>

namespace antom
{
  // The "ThreadData" class.
  class ThreadData
  {

  public:

    // Constructor.
    ThreadData (void) : 
      decisionStack(NULL),
      dsStart(0),
      dsEnd(0)
    { }

    // Decision stack related data.
    uint32_t* decisionStack;
    uint32_t dsStart; 
    uint32_t dsEnd; 

  private: 
    
    // Copy constructor.
    ThreadData (const ThreadData&);

    // Assignment operator.
    ThreadData& operator = (const ThreadData&);

  };

  // The "Control" class.
  class Control
  {

  public:

    // Constructor.
    Control (uint32_t threads = 1) : 
      m_done(false), 
      m_threads(threads),
      m_threadData(threads),
      m_unitClauses(threads),
	  m_cpulimit(0.0),
	  m_timeS(0.0),
	  m_verbosity(0),
	  m_incrementalMode(0),
	  m_sumTime(false),
	  m_timeSetted(false)
    {
      // Consistency check.
      assert(m_threads != 0);   

      // Initialize "m_threadData".
      for (uint32_t t = 0; t < m_threads; ++t)
		{ m_threadData[t] = new ThreadData; }
    }

    // Destructor.
    ~Control (void)
    {
      // Delete "m_threadData".
      for (uint32_t t = 0; t < m_threads; ++t)
	{ delete m_threadData[t]; }
    }

    // Returns whether the search process can be stopped or not.
    bool done (void) const { return m_done; }

    // Sets "m_done" to TRUE.
    void setDone (void) 
	{ m_done = true; }

    // Sets "m_done" to FALSE.
    void resetDone (void) { m_done = false; }

	// Sets global CPU limit
	void setCPULimit( double t ) { m_cpulimit = t; }

	double getCPULimit( void ) const { return m_cpulimit; }

	void setStartTime( double startTime )
	{ if( !m_sumTime && !m_timeSetted ) { m_timeS = startTime; m_timeSetted = true; } }

	double getStartTime( void ) const { return m_timeS; }

	void setSumTime( bool val ) { m_sumTime = val; }

	bool getSumTime( void ) const { return m_sumTime; }

	void setTimeSetted( bool val ) { m_timeSetted = val; }

	bool getTimeSetted( void ) const { return m_timeSetted; }

	bool reachedTimeout( double currentTime ) const
	{ 
	  return ( (currentTime - m_timeS ) > m_cpulimit ); 
	}

	// Sets verbosity
	void setVerbosity ( uint32_t val ) { m_verbosity = val; }

	uint32_t getVerbosity ( void ) const { return m_verbosity; }

	void setIncrementalMode( uint32_t val ) { m_incrementalMode = val; }
	
	uint32_t getIncrementalMode( void ) const { return m_incrementalMode; }
 
    // Used by the threads to import unit clauses found by other threads.

    // Used by the threads to export all of their assignments made on decision level 0.
    void exportUnitClauses (uint32_t* decisionStack, uint32_t start, uint32_t end, uint32_t id)
    { 
      assert(id < m_threads);
      m_threadData[id]->decisionStack = decisionStack; 
      m_threadData[id]->dsStart = start;
      m_threadData[id]->dsEnd = end; 
    }

    uint32_t* importUnitClauses (uint32_t id)
    {
      assert(id < m_threads); 
      m_unitClauses[id].clear(); 
      for (uint32_t t = 0; t < m_threads; ++t)
		{
		  if (t != id)
			{
			  for (uint32_t l = m_threadData[t]->dsStart; l < m_threadData[t]->dsEnd;  ++l)
				{ m_unitClauses[id].push_back(m_threadData[t]->decisionStack[l]); }
			}
		}
      m_unitClauses[id].push_back(0); 
      return &m_unitClauses[id][0]; 
    }

  private:

    // A flag indicating whether the search process can be stopped or not.
    bool m_done;
 
    // The number of threads running in parallel. 
    uint32_t m_threads; 
  
    // For each thread we store a pointer to some decision stack related data.
    std::vector<ThreadData*> m_threadData; 

    // For each thread we maintain a vector, storing all unit clauses found by other threads. 
    std::vector<std::vector<uint32_t> > m_unitClauses; 

	// User given CPU-limit
	double m_cpulimit;

	// Start time of the SAT core
	double m_timeS;

	// Be verbose
	uint32_t m_verbosity;

	// Incremental MaxSAT mode
	// 0 - no incremental mode (default)
	// 1 - "BMC"ish: soft clauses are deleted after each call
	// 2 - soft clauses are kept after each call
	uint32_t m_incrementalMode;

	// Do we have to accumulate run time?
	bool m_sumTime;

	// Starttime already set?
	bool m_timeSetted;
  };
}

#endif
