
/********************************************************************************************
main.cpp -- Copyright (c) 2016, Tobias Schubert, Sven Reimer

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
#include <sys/resource.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <cassert>
#include <csignal>
#include <string>
#include <vector>
#include <omp.h>
#include <unistd.h>

// Include antom related headers.
#include "antom.hpp"

//#define COMPETITION

// Some more headers. 
void SIGSEGV_handler(int signum);
bool loadCNF (const std::string& file, uint32_t& maxIndexOrigVars, antom::Antom& solver, uint32_t type);
void printUsage( void );


void processMemUsage(double& vm_usage, double& resident_set)
{
  using std::ios_base;
  using std::ifstream;
  using std::string;

  vm_usage     = 0.0;
  resident_set = 0.0;

  // 'file' stat seems to give the most reliable results
  //
  ifstream stat_stream("/proc/self/stat",ios_base::in);

  // dummy vars for leading entries in stat that we don't care about
  //
  string pid, comm, state, ppid, pgrp, session, tty_nr;
  string tpgid, flags, minflt, cminflt, majflt, cmajflt;
  string utime, stime, cutime, cstime, priority, nice;
  string O, itrealvalue, starttime;

  // the two fields we want
  //
  unsigned long vsize;
  long rss;

  stat_stream >> pid >> comm >> state >> ppid >> pgrp >> session >> tty_nr
			  >> tpgid >> flags >> minflt >> cminflt >> majflt >> cmajflt
			  >> utime >> stime >> cutime >> cstime >> priority >> nice
			  >> O >> itrealvalue >> starttime >> vsize >> rss; // don't care about the rest

  stat_stream.close();

  long page_size_kb = sysconf(_SC_PAGE_SIZE) / 1024; // in case x86-64 is configured to use 2MB pages
  vm_usage     = (double)vsize / 1024.0;
  resident_set = (double)(rss * page_size_kb);
}


// An example demonstrating how to use antom.
int main (int argc, char** argv)
{ 
  // Define signal handling functions.
  signal(SIGSEGV,SIGSEGV_handler);

  // Initialization.
  std::cout.precision(2);
  std::cout.setf(std::ios::unitbuf);
  std::cout.setf(std::ios::fixed);
  
  // Output.
  std::cout << "c =================================================================" << std::endl
			<< "c antom; Tobias Schubert, Sven Reimer; University of Freiburg, 2016" << std::endl
			<< "c =================================================================" << std::endl;


#ifndef COMPETITION
  // Wrong number of command line parameters?
  if (argc < 3)
    {

	  printUsage();
      // Return UNKNOWN.
      return ANTOM_UNKNOWN;
    }
#endif

  // Initialization.
  //uint32_t mode(0);
  //uint32_t mode(21);
  uint32_t mode(24);
  uint32_t threads(1); 
  
  restartstrategy restartStrategy(LUBY); 
  simplifystrategy simplifyStrategy(ANTOM);
  uint32_t decisionStrategy(0); 
  uint32_t unitFactor(8); 
  double decayFactor(1.05); 
  double cpuLimit(0.0);
  std::string resultFile("");
  bool storeResult(false); 
  bool lhbr(false); 
  bool ternary(false);

  uint32_t maxLoops( 1000000 );
  uint32_t verbose( 1 );
  bool upla( true );
  bool subsumption( true );
  bool varElim( true );
  bool preprocess( false );
  bool inprocess( false );
  bool maxinprocess( false );


#ifndef COMPETITION
  bool skip(false);
  bool trigger(false);
  uint32_t maxWidth(0);
  uint32_t gridmode(0);
  uint32_t csc(0);
#else
  bool skip(true);
  bool trigger(true);
  uint32_t maxWidth(64);
  uint32_t gridmode(3);
  uint32_t csc(1);
#endif

  bool incomplete(false);
  uint32_t width(32);
  uint32_t maxParts(0);
  uint32_t sortsoftclauses(0);
  uint32_t verticalWidth(4);
  uint32_t networktype(0);

  uint32_t sortvarorder(0);
  bool verify(false);

#ifndef COMPETITION
  // Get the additional command line parameters.
  for (uint32_t c = 1; c < ((uint32_t) argc - 1); ++c)
    {
      // Initialization.
      std::string argument(argv[c]); 
      bool matched(false);      

      // What about the operating mode?
      if (argument == "--mode=0")
		{ mode = 0; matched = true; continue;}
      else if (argument == "--mode=1")
		{ mode = 1; matched = true; continue; }
	  else if (argument == "--mode=10")
		{ mode = 10; matched = true; continue; }
      else if (argument == "--mode=11")
		{ mode = 11; matched = true; continue; }
      else if (argument == "--mode=12")
		{ mode = 12; matched = true; continue; }
      else if (argument == "--mode=13")
		{ mode = 13; matched = true; continue; }
      else if (argument == "--mode=14")
		{ mode = 14; matched = true; continue; }
      else if (argument == "--mode=15")
		{ mode = 15; matched = true; continue; }
      else if (argument == "--mode=20")
		{ mode = 20; matched = true; continue; }
      else if (argument == "--mode=21")
		{ mode = 21; matched = true; continue; }
      else if (argument == "--mode=22")
		{ mode = 22; matched = true; continue; }
      else if (argument == "--mode=23")
		{ mode = 23; matched = true; continue; }
      else if (argument == "--mode=24")
		{ mode = 24; matched = true; continue; }
      else if (argument == "--mode=25")
		{ mode = 25; matched = true; continue; }
      else if (argument == "--mode=26")
		{ mode = 26; matched = true; continue; }
      else if (argument == "--mode=99")
		{ mode = 99; matched = true; continue; }
	  // What about the number of threads?
      else if (argument == "--threads=1")
		{ threads = 1; matched = true; continue; }
      else if (argument == "--threads=2")
		{ threads = 2; matched = true; continue; }
      else if (argument == "--threads=3")
		{ threads = 3; matched = true; continue; }
      else if (argument == "--threads=4")
		{ threads = 4; matched = true; continue; }
      else if (argument == "--threads=5")
		{ threads = 5; matched = true; continue; }
      else if (argument == "--threads=6")
		{ threads = 6; matched = true; continue; }
      else if (argument == "--threads=7")
		{ threads = 7; matched = true; continue; }
      else if (argument == "--threads=8")
		{ threads = 8; matched = true; continue; }
      else if (argument == "--verbose" || argument == "--v")
		{ ++verbose; matched = true; continue; }
      else if (argument == "--verbose=0")
		{ verbose = 0; matched = true; continue; }
	  // What about "Lazy Hyper Binary Resolution"?
      else if (argument == "--lhbr=true")
		{ lhbr = true; matched = true; continue; }
      else if (argument == "--lhbr=false")
		{ lhbr = false; matched = true; continue; }
      // What about the restart strategy?
      else if (argument == "--restart=luby")
		{ restartStrategy = LUBY; matched = true; continue; }
      else if (argument == "--restart=glucose")
		{ restartStrategy = GLUCOSE; matched = true; continue; }
      // What about the simplifaction strategy?
      else if (argument == "--simplify=antom")
		{ simplifyStrategy = ANTOM; matched = true; continue; }
      else if (argument == "--simplify=minisat")
		{ simplifyStrategy = MINISAT; matched = true; continue; }
      // What about the decision strategy?
      else if (argument == "--decision=0")
		{ decisionStrategy = 0; matched = true; continue; }
      else if (argument == "--decision=1")
		{ decisionStrategy = 1; matched = true; continue; }
      else if (argument == "--decision=2")
		{ decisionStrategy = 2; matched = true; continue; }
      else if (argument == "--decision=3")
		{ decisionStrategy = 3; matched = true; continue; }
	  else if (argument.compare(0,11,"--cpuLimit=") == 0)
		{ std::stringstream sCPU(argument.substr(11,argument.length())); sCPU >> cpuLimit; matched = true; continue; }
	  // What about special treatment for ternary clauses?
      else if (argument == "--ternary=true")
		{ ternary = true; matched = true; continue; }
      else if (argument == "--ternary=false")
		{ ternary = false; matched = true; continue; }
      // What about the unit factor?
      else if (argument.compare(0, 13, "--unitFactor=") == 0)
		{ std::stringstream ss(argument.substr(13, argument.length())); ss >> unitFactor; matched = true; continue; }      // What about the decay factor?
      else if (argument.compare(0, 14, "--decayFactor=") == 0)
		{ std::stringstream ss(argument.substr(14, argument.length())); ss >> decayFactor; matched = true; continue; }
      // What about the result file?
      else if (argument.compare(0, 14, "--result-file=") == 0)
		{ std::stringstream ss(argument.substr(14, argument.length())); ss >> resultFile; storeResult = true; matched = true; continue; }
	  else if (argument.compare(0,13,"--splitWidth=") == 0)
		{ std::stringstream sWidth(argument.substr(13,argument.length())); sWidth >> width; matched = true; continue; }
	  else if (argument.compare(0,11,"--maxWidth=") == 0)
		{ std::stringstream sWidth(argument.substr(11,argument.length())); sWidth >> maxWidth; matched = true; continue; }
	  else if (argument.compare(0,11,"--maxParts=") == 0)
		{ std::stringstream sParts(argument.substr(11,argument.length())); sParts >> maxParts; matched = true; continue; }
	  else if (argument.compare(0,12,"--vertWidth=") == 0)
		{ std::stringstream sWidth(argument.substr(12,argument.length())); sWidth >> verticalWidth; matched = true; continue; }
	  // What about performing UPLA?
      else if (argument == "--upla=true")
		{ upla = true; matched = true; continue; }
      else if (argument == "--upla=false")
		{ upla = false; matched = true; continue; }
	  // What about full subsumption checks?
	  else if (argument == "--subsumption=true")
		{ subsumption = true; matched = true; continue; }
      else if (argument == "--subsumption=false")
		{ subsumption = false; matched = true; continue; }
	  // What about variable elimination?
	  else if (argument == "--varElim=true")
		{ varElim = true; matched = true; continue; }
      else if (argument == "--varElim=false")
		{ varElim = false; matched = true; continue; }
	  // What about perfoming preprocessing?
	  else if (argument == "--prepro=true")
		{ preprocess = true; matched = true; continue; }
      else if (argument == "--prepro=false")
		{ preprocess = false; matched = true; continue; }
	  // What about perfoming inprocessing during solve?
	  else if (argument == "--inpro=true")
		{ inprocess = true; matched = true; continue; }
      else if (argument == "--inpro=false")
		{ inprocess = false; matched = true; continue; }
	  // What about perfoming inprocessing during maxsolve?
	  else if (argument == "--maxInpro=true")
		{ maxinprocess = true; matched = true; continue; }
      else if (argument == "--maxInpro=false")
		{ maxinprocess = false; matched = true; continue; }
	  // Verify the model with another antom-instance?
	  else if (argument == "--verify=true")
		{ verify = true; matched = true; continue; }
      else if (argument == "--verify=false")
		{ verify = false; matched = true; continue; }
      // What about the maximum preprocessor loops?
      else if (argument.compare(0, 11, "--maxLoops=") == 0)
		{ std::stringstream ss(argument.substr(11, argument.length())); ss >> maxLoops; matched = true; continue; }
	  // Sort decision variables for (partial) MaxSAT?
	  else if (argument == "--sortvar=true")
		{ sortvarorder = 1; matched = true; continue; }
      else if (argument == "--sortvar=false")
		{ sortvarorder = 0; matched = true; continue; }
      else if (argument == "--sortvar=random")
		{ sortvarorder = 2; matched = true; continue; }
      else if (argument == "--sortvar=reverse")
		{ sortvarorder = 3; matched = true; continue; }
	  else if (argument == "--sortsoft=0")
		{ sortsoftclauses = 0; matched = true; continue; }
	  else if (argument == "--sortsoft=1")
		{ sortsoftclauses = 1; matched = true; continue; }
	  else if (argument == "--sortsoft=2")
		{ sortsoftclauses = 2; matched = true; continue; }
	  else if (argument == "--sortsoft=3")
		{ sortsoftclauses = 3; matched = true; continue; }
	  else if (argument == "--skip=true")
		{ skip = true; matched = true; continue; }
	  else if (argument == "--skip=false")
		{ skip = false; matched = true; continue; }
	  else if (argument == "--csc=false")
		{ csc = 0; matched = true; continue; }
	  else if (argument == "--csc=true")
		{ csc = 1; matched = true; continue; }
	  else if (argument == "--csc=all")
		{ csc = 2; matched = true; continue; }
	  else if (argument == "--trigger=true")
		{ trigger = true; matched = true; continue; }
	  else if (argument == "--trigger=false")
		{ trigger = false; matched = true; continue; }
	  else if (argument == "--gridMode=0")
		{ gridmode = 0; matched = true; continue; }
	  else if (argument == "--gridMode=1")
		{ gridmode = 1; matched = true; continue; }
	  else if (argument == "--gridMode=2")
		{ gridmode = 2; matched = true; continue; }
	  else if (argument == "--gridMode=3")
		{ gridmode = 3; matched = true; continue; }
	  else if (argument == "--incomplete=false")
		{ incomplete = false; matched = true; continue; }
	  else if (argument == "--incomplete=true")
		{ incomplete = 1; matched = true; continue; }
      else if (argument == "--network=0")
		{ networktype = 0; matched = true; continue; }
      else if (argument == "--network=1")
		{ networktype = 1; matched = true; continue; }
      else if (argument == "--network=2")
		{ networktype = 2; matched = true; continue; }
  
      // Unknown option?
      if (!matched)
		{
		  // Output. 
		  std::cout << "c Unknown option: " << argv[c] << std::endl;
		  printUsage();
		  return ANTOM_UNKNOWN;
		}
    }

  if( incomplete && (mode != 14 && mode != 24 ) )
	{
	  std::cout << "Incomplete mode only supported for mode 14 and 24" << std::endl;
	  printUsage();
	  return ANTOM_UNKNOWN;
	}

  // Output.
  switch (mode)
    {
    case  0: std::cout << "c operating mode.........: SAT (multi-threaded: portfolio)"                                                                    << std::endl; break; 
    case  1: std::cout << "c operating mode.........: single-threaded, SATzilla-like"                                                                     << std::endl; break; 
    case 10: std::cout << "c operating mode.........: MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio)"                                << std::endl; break; 
    case 11: std::cout << "c operating mode.........: MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"                                  << std::endl; break; 
    case 12: std::cout << "c operating mode.........: MaxSAT, binary search-based (multi-threaded: internal portfolio)"                                   << std::endl; break;
    case 13: std::cout << "c operating mode.........: partialMode MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio"                      << std::endl; break; 
    case 14: std::cout << "c operating mode.........: partialMode MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"                       << std::endl; break;
    case 15: std::cout << "c operating mode.........: partialMode MaxSAT, binary search-based (multi-threaded: internal portfolio)"                        << std::endl; break; 
    case 20: std::cout << "c operating mode.........: partial MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio)"                        << std::endl; break; 
    case 21: std::cout << "c operating mode.........: partial MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"                          << std::endl; break; 
    case 22: std::cout << "c operating mode.........: partial MaxSAT, binary search-based (multi-threaded: internal portfolio)"                           << std::endl; break;
    case 23: std::cout << "c operating mode.........: partialMode partial MaxSAT, satisfiability-based, dfs (multi-threaded: internal portfolio)"          << std::endl; break;
    case 24: std::cout << "c operating mode.........: partialMode partial MaxSAT, satisfiability-based, bfs (multi-threaded: internal portfolio)"          << std::endl; break;
    case 25: std::cout << "c operating mode.........: partialMode partial MaxSAT, satisfiability-based, bfs, one depth (multi-threaded: internal portfolio)"          << std::endl; break;
    case 99: std::cout << "c operating mode.........: collecting data for regression analysis (--> SATzilla-like SAT solving)"                            << std::endl; break; 
    }
  std::cout << "c benchmark file.........: " << argv[(uint32_t) argc - 1] << std::endl;
  if (storeResult)
    { std::cout << "c result file............: " << resultFile << std::endl; }

  std::cout << "c #threads...............: " << threads << std::endl; 

  std::cout << "c lhbr...................: ";
  if (lhbr)
    { std::cout << "true" << std::endl; }
  else
    { std::cout << "false " << std::endl; }

  std::cout << "c restart strategy.......: ";
  if (restartStrategy == LUBY)
    { std::cout << "luby" << std::endl; }
  else if (restartStrategy == GLUCOSE)
    { std::cout << "glucose" << std::endl; }
  else
	{ std::cout << "undefined" << std::endl; }

  std::cout << "c simplify strategy......: ";
  if (simplifyStrategy == ANTOM)
    { std::cout << "antom" << std::endl; }
  else if (simplifyStrategy == MINISAT)
    { std::cout << "minisat" << std::endl; }
  else
	{ std::cout << "undefined" << std::endl; }

  std::cout << "c decision strategy......: ";
  switch (decisionStrategy)
    {
    case 0: std::cout << "using cached polarity together with antom's 'polarity toggling scheme'" << std::endl; break;
    case 1: std::cout << "using cached polarity only" << std::endl; break;
    case 2: std::cout << "setting polarity to FALSE regardless of the cached value" << std::endl; break;
    case 3: std::cout << "setting polarity to TRUE regardless of the cached value" << std::endl; break;
    }

  std::cout << "c network type...........: ";
  switch ( networktype )
	{
	case 0: std::cout << "Bitonic sorter" << std::endl; break;
	case 1: std::cout << "Odd-Even sorter" << std::endl; break;
	case 2: std::cout << "Pairwise sorter" << std::endl; break;
	}
  std::cout << "c restart unit factor....: " << unitFactor << std::endl
			<< "c decay factor...........: " << decayFactor << std::endl; 

#endif

  // Get a first timestamp.
  double start(omp_get_wtime()); 

  // Initialize an "antom" object.
  antom::Antom myAntom(threads); 

  // Set antom's various parameters.
  myAntom.setLHBR(lhbr); 
  myAntom.setRestartStrategy(restartStrategy); 
  myAntom.setSimplifyStrategy(simplifyStrategy);
  myAntom.setDecisionStrategy(decisionStrategy, 0); 
  myAntom.setLuby(unitFactor); 
  myAntom.setDecayFactor(decayFactor); 

  myAntom.setUPLA( upla );
  myAntom.setSubsumption( subsumption );
  myAntom.setVarElim( varElim );
  myAntom.setMaxLoops( maxLoops );
  myAntom.setPreprocessing( preprocess );
  myAntom.setInprocessing( inprocess );
  myAntom.setMaxInprocessing( maxinprocess );
  myAntom.setVerbosity( verbose );
  myAntom.setCPULimit( cpuLimit );
  myAntom.setSortVarorder( sortvarorder );
  myAntom.useTernaryClauses( ternary );
  myAntom.setSkip(skip);
  myAntom.setCSC(csc);
  myAntom.setTrigger(trigger);
  myAntom.setSplittedWidth(width);
  myAntom.setMaxWidth(maxWidth);
  myAntom.setMaxParts(maxParts);
  myAntom.setSortSoftClauses(sortsoftclauses);
  myAntom.setHorizontalWidth(verticalWidth);
  myAntom.setGridMode(gridmode);
  myAntom.setIncompleteMode(incomplete);
  myAntom.setNetworktype(networktype);

  // Initialization.
  uint32_t maxIndexOrigVars(0); 

  // Load the benchmark file specified by the user.
  uint32_t type(0); 
  if (mode >= 10 && mode < 20) { type = 1; }
  if (mode >= 20 && mode < 30 ) { type = 2; }
  if (!loadCNF(argv[(uint32_t) argc - 1], maxIndexOrigVars, myAntom, type))
    {
      // Output.
      std::cout << "s UNSATISFIABLE" << std::endl; 
      
      // Return UNSAT.
      return ANTOM_UNSAT;
    }
  
  // Solve the benchmark specified by the user.
  uint32_t result(ANTOM_UNKNOWN); 

  uint32_t optimum(0);

  // First preprocess the formula
  // Do not apply Preprocessing with max-antom, since it's performed within "maxSolve()" incrementally
  if( mode < 10 && preprocess )
	{ result = myAntom.preprocess(); }

  //std::vector< uint32_t > assumptions;

  if( result == ANTOM_UNKNOWN )
	{
	  switch(mode)
		{ 
		case  0: result = myAntom.solve(/*assumptions*/); break; 
		case  1: myAntom.setVerbosity(1); result = myAntom.solveSATzilla(); break; 
		case 10: result = myAntom.maxSolve(optimum, 0); break;
		case 11: result = myAntom.maxSolve(optimum, 1); break; 
		case 12: result = myAntom.maxSolve(optimum, 2); break;
		case 13: result = myAntom.maxSolvePartial(optimum, 0); break;
		case 14: result = myAntom.maxSolvePartial(optimum, 1); break; 
		case 15: result = myAntom.maxSolvePartial(optimum, 2); break; 
		case 20: result = myAntom.maxSolve(optimum, 0); break; 
		case 21: result = myAntom.maxSolve(optimum, 1); break; 
		case 22: result = myAntom.maxSolve(optimum, 2); break; 
		case 23: result = myAntom.maxSolvePartial(optimum, 0); break;
		case 24: result = myAntom.maxSolvePartial(optimum, 1); break; 
		case 25: result = myAntom.maxSolvePartial(optimum, 2); break; 
		case 99: myAntom.getDataRegressionAnalysis(); break; 
		}
	}

  // Get the CPU time. 
  struct rusage resourcesS;
  getrusage(RUSAGE_SELF, &resourcesS); 
  double timeS((double) resourcesS.ru_utime.tv_sec + 1.e-6 * (double) resourcesS.ru_utime.tv_usec);
  timeS += (double) resourcesS.ru_stime.tv_sec + 1.e-6 * (double) resourcesS.ru_stime.tv_usec;

  // Get the wall clock time.
  double vmusage = 0.0;
  double residentset = 0.0;
  processMemUsage(vmusage, residentset);

  double timeW(omp_get_wtime() - start); 

  // Output.
  std::cout << "c #ID fastest thread.....: " << myAntom.solvingThread()          << std::endl
			<< "c #variables.............: " << myAntom.variables()              << std::endl
			<< "c #clauses...............: " << myAntom.clauses()                << std::endl
			<< "c #literals..............: " << myAntom.literals()               << std::endl
			<< "c #decisions.............: " << myAntom.decisions()              << std::endl
			<< "c #bcp operations........: " << myAntom.bcps()                   << std::endl
			<< "c #implications..........: " << myAntom.implications()           << std::endl
			<< "c #conflicts.............: " << myAntom.conflicts()              << std::endl
			<< "c #restarts..............: " << myAntom.restarts()               << std::endl
			<< "c #simplifications.......: " << myAntom.simplifications()        << std::endl
			<< "c #synchronizations......: " << myAntom.synchronizations()       << std::endl
			<< "c #lhbr clauses..........: " << myAntom.lhbr()                   << std::endl
			<< "c #learnt unit clauses...: " << myAntom.learntUnitClauses()      << std::endl
			<< "c #learnt binary clauses.: " << myAntom.learntBinaryClauses()    << std::endl
			<< "c #learnt ternary clauses: " << myAntom.learntTernaryClauses()   << std::endl
			<< "c average lbd............: " << myAntom.avgLBD()                 << std::endl
			<< "c average cc length......: " << myAntom.avgCCLength()            << std::endl
			<< "c average dec. level.....: " << myAntom.avgDL()                  << std::endl
			<< "c average lev. cleared...: " << myAntom.avgDLclearedCA()         << std::endl
			<< "c average vars unassigned: " << myAntom.avgVarsUnassignedCA()    << std::endl
			<< "c #inprocessings.........: " << myAntom.inprocessings()          << std::endl
			<< "c cpu time...............: " << timeS << "s"                     << std::endl
			<< "c wall clock time........: " << timeW << "s"                     << std::endl
			<< "c cpu utilization........: " << ((timeS / timeW) * 100.0) << "%" << std::endl
			<< "c virtual memory usage...: " << vmusage                          << std::endl
			<< "c resident set memory....: " << residentset                      << std::endl
			<< "c ===================================================="          << std::endl;

  // Wrt. the code below, operating modes 0 and 1 are equivalent.
  if (mode == 1)
    { mode = 0; }

  // Satisfiable formula?
  if (result == ANTOM_SAT) 
    {
      // Output.
      if (mode == 0)
		{ 
		  if (!storeResult)
			{ std::cout << "s SATISFIABLE" << std::endl; }
		}
      else
		{ 
		  assert(mode >= 10 && mode < 30); 
		  std::cout << "o " << optimum << std::endl 
					<< "s OPTIMUM FOUND" << std::endl; 
		}

      // Get the satisfying variable assignment.
      const std::vector<uint32_t>& model(myAntom.model());

      // Consistency check.
      assert(maxIndexOrigVars > 0); 
      assert(maxIndexOrigVars < model.size()); 

      // Should we print or save the model?
      if (!storeResult || mode != 0)
		{
		  // Output.
		  std::cout << "v ";
		  for (uint32_t m = 1; m <= maxIndexOrigVars; ++m)
			{
			  if (model[m] != 0)
				{
				  if ((model[m] & 1) == 1)
					{ std::cout << "-"; }
				  std::cout << (model[m] >> 1) << " "; 
				}
			}
		  if (mode == 0)
			{ std::cout << "0"; } 
		  std::cout << std::endl; 
		}
      else
		{
		  // Store our solution so that SatELite is able to extend the partial model. 
		  assert(mode == 0 && storeResult); 
		  std::ofstream satELite(resultFile);
		  satELite << "SAT\n";
		  for (uint32_t m = 1; m <= maxIndexOrigVars; ++m)
			{ 
			  assert(model[m] != 0);
			  if ((model[m] & 1) == 1)
				{ satELite << "-"; }
			  satELite << (model[m] >> 1) << " "; 
			}
		  satELite << "0\n";
		  satELite.close();
		}


	  // Check model with a new and plain antom core
	  if( verify )
		{
		  antom::Antom verify(threads); 
		  verify.setPreprocessing(false);
		  verify.setInprocessing(false);

		  std::vector<uint32_t> verifytriggerVars;
		  uint32_t maxverifyindex(0);
		  if (!loadCNF(argv[(uint32_t) argc - 1], maxverifyindex, verify, 2))
			{
			  std::cout << "Bad input" << std::endl;
			  assert(false);
			}

		  std::vector< uint32_t > verifyassumptions;
		  for( uint32_t j = 1; j <= maxverifyindex; ++j )
			{
			  if( model[j] != 0 )
				{ 
				  verifyassumptions.push_back(model[j]); 
				}
			}
		  uint32_t verifyresult = verify.solve(verifyassumptions);

		  if( verifyresult == ANTOM_SAT )
			{
			  std::cout << "Everything okay with model!" << std::endl;
			}
		  else
			{
			  assert( verifyresult == ANTOM_UNSAT );
			  std::cout << "WRONG MODEL" << std::endl;
			  assert(false);
			}
		}

      // Return SAT.
      return ANTOM_SAT; 
    }

  if( result == ANTOM_UNKNOWN )
	{
	  std::cout << "s TIMEOUT" << std::endl; 
	  return ANTOM_UNKNOWN; 
	}
  // Output.
  if (mode != 0 || !storeResult)
    { std::cout << "s UNSATISFIABLE" << std::endl; }

  // Return UNSAT.
  return ANTOM_UNSAT; 
}

// Terminate antom in case of a segmentation fault.
void SIGSEGV_handler(int signum) 
{
  // Output.
  std::cout << "c segmentation fault (signal " << signum << ")" << std::endl
			<< "s UNKNOWN" << std::endl; 

  // Terminate with UNKNOWN.
  exit(ANTOM_UNKNOWN); 
} 

// Loads a formula from file, returns FALSE if the formula is unsatisfiable.
// "type" has to be set according to the type of benchmark:
// type = 0 --> SAT 
// type = 1 --> MaxSAT
// type = 2 --> partial MaxSAT
bool loadCNF (const std::string& file, uint32_t& maxIndexOrigVars, antom::Antom& solver, uint32_t type)
{
  // Open the file.
  std::ifstream source;
  source.open(file.c_str());

  // Any problems while opening the file?
  if (!source) 
    {
      // Output. 
      std::cout << "c Unable to open file" << std::endl
				<< "s UNKNOWN" << std::endl; 
      
      // Return UNKNOWN.
      exit(ANTOM_UNKNOWN); 
    }

  // Variables.
  std::vector<uint32_t> clause;
  uint32_t maxVars(0);
  //uint32_t numClauses(0); 
  uint32_t literal(0); 
  uint32_t sign(0); 
  uint32_t threshold(0); 
  bool firstLit(true); 
  char c('0'); 

  // Process the file.
  while (source.good())
    {
      // Get the next character.
      c = (char)source.get();
   
      // No more clauses?
      if (!source.good())
		{ break; }

      // Statistics?
      if (c == 'p')
		{
		  // Get the next char. 
		  c = (char)source.get(); 

		  // Remove whitespaces.
		  while (c == ' ') 
			{ c = (char)source.get(); }

		  // In case of a partial MaxSAT benchmark file, the next character has to be "w".
		  if (type == 2)
			{ assert(c = 'w'); c = (char)source.get(); }

		  // The next three characters have to be "c", "n", and "f".
		  assert(c = 'c');
		  c = (char)source.get();
		  assert(c = 'n');
		  c = (char)source.get(); 
		  assert(c = 'f');
		  c = (char)source.get(); 

		  // Remove whitespaces.
		  while (c == ' ') 
			{ c = (char)source.get(); }

		  // Let's get the number of variables within the current CNF.
		  while (c != ' ' && c != '\n') 
			{ maxVars = (maxVars * 10) + (uint32_t) c - '0'; c = (char)source.get(); }

		  // Update "maxIndexOrigVariables".
		  maxIndexOrigVars = maxVars; 

		  // Remove whitespaces.
		  while (c == ' ') 
			{ c = (char)source.get(); }

		  // Let's get the number of clauses within the current CNF.
		  //while (c != ' ' && c != '\n') 
		  // { numClauses = (numClauses * 10) + (uint32_t) c - '0'; c = source.get(); }

		  // Set the maximum number of variables the solver has to deal
		  solver.setMaxIndex(maxVars);
		}
      else
		{
		  // Clause? 
		  if (c != 'c' && c != '%')
			{
			  // Reset "clause".
			  clause.clear();

			  // Initialize "firstLit".
			  firstLit = true; 
	      
			  // Initialize "threshold".
			  threshold = 0; 

			  // Do we have to solve a MaxSAT benchmark?
			  if (type == 1)
				{
				  // Update "threshold".
				  threshold = 1; 
				}
			  // Get the next clause.
			  while (true)
				{
				  // Initialization.
				  literal = 0;
				  sign    = 0; 
				  // Remove whitespaces.
				  while (c == ' ') 
					{ c = (char)source.get(); }

				  // Have we reached the clause stopper?
				  if (c == '0')
					{
					  // Mark all variables occuring in a softclause in (partial) MAX-SAT as "Don't Touch"
					  if( threshold == 1 )
						{
						  // Add "clause" to the clause database of "solver".	  
						  if (clause.size() >= threshold && !solver.addSoftClause(clause))
							{ source.close(); return false; }		      
						}
					  // Add "clause" to the clause database of "solver".	  
					  else if (clause.size() > threshold && !solver.addClause(clause))
						{ source.close(); return false; }		      
					  break; 
					}
				  // Let's get the next literal.
				  while (c != ' ') 
					{
					  if (c == '-')
						{ sign = 1; }
					  else
						{ literal = (literal * 10) + (uint32_t) c - '0'; }
					  c = (char)source.get();
					}

				  // Consistency check.
				  assert(literal != 0); 

				  // In case we are loading a partial MaxSAT benchmark, the first literal
				  // specifies whether the current clause is a "soft" or "hard" one.
				  if (type == 2 && firstLit)
					{
					  // Reset "firstLit".
					  firstLit = false;
					  // Consistency check.
					  assert(sign == 0);

					  // Soft clause?
					  if (literal == 1)
						{
						  // Update "threshold".
						  threshold = 1; 
						}
					}
				  else
					{
					  // Another consistency check, in this case due to (partial) MaxSAT solving. 
					  assert((type != 1 && type != 2) || literal <= maxVars); 
					  // Add "literal" to "clause".		      
					  clause.push_back((literal << 1) + sign); 
					  // Update "maxVars" if necessary.
					  if (literal > maxVars)
						{ maxVars = literal; solver.setMaxIndex(maxVars); }
					}
				}
			}
		}

	  // Go to the next line of the file. 
	  while (c != '\n') 
		{ c = (char)source.get(); } 	  
	}

  // Close the file.
  source.close();

  // Everything went fine.
  return true;
}

void printUsage( void )
{
  // Ouput. 
  std::cout << "c usage: ./antom --mode=<0..99> [--result-file=<file>] [options] <wcnf/cnf>"                                        << std::endl
			<< "c"                                                                                                                  << std::endl
			<< "c mode = 0 --> SAT (multi-threaded: portfolio)"                                                                     << std::endl
			<< "c mode = 1 --> SAT (single-threaded, SATzilla-like)"                                                                << std::endl
			<< "c mode = 10 --> MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio)"                                << std::endl
			<< "c mode = 11 --> MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"                                  << std::endl
			<< "c mode = 12 --> MaxSAT, binary search-based (multi-threaded: internal portfolio)"                                   << std::endl
			<< "c mode = 13 --> partialMode MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio)"                    << std::endl
			<< "c mode = 14 --> partialMode MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"                       << std::endl
			<< "c mode = 15 --> partialMode MaxSAT, binary search-based (multi-threaded: internal portfolio)"                        << std::endl
			<< "c mode = 20 --> partial MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio)"                        << std::endl
			<< "c mode = 21 --> partial MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"                          << std::endl
			<< "c mode = 22 --> partial MaxSAT, binary search-based (multi-threaded: internal portfolio)"                           << std::endl
			<< "c mode = 23 --> partialMode partial MaxSAT, unsatisfiability-based (multi-threaded: internal portfolio)"             << std::endl
			<< "c mode = 24 --> partialMode partial MaxSAT, satisfiability-based (multi-threaded: internal portfolio)"               << std::endl
			<< "c mode = 25 --> partialMode partial MaxSAT, binary search-based (multi-threaded: internal portfolio)"                << std::endl
			<< "c mode = 99 --> collecting data for regression analysis (--> SATzilla-like SAT solving)"                            << std::endl
			<< "c"                                                                                                                  << std::endl
			<< "c options:"                                                                                                         << std::endl
			<< "c --threads=<1..8>           --> number of threads for multithreaded mode (default 1)"                              << std::endl 
			<< "c --cpuLimit=[>=0.0]         --> CPU limit in seconds"                                                              << std::endl
			<< "c                                0.0: no CPU limit at all (default)"                                                << std::endl
			<< "c --verify=<true/false>      --> verifies model in SAT-case with a second antom-instance"                           << std::endl
			<< "c --v | --verbose            --> increase verbosity"                                                                << std::endl
			<< "c --verbose=0                --> reset verbosity"                                                                   << std::endl
			<< "c solver option:"                                                                                                   << std::endl
			<< "c --lhbr=<true/false>        --> enables/disables 'Lazy Hyper Binary Resolution' (default: true)"                   << std::endl
			<< "c --restart=<luby/glucose>   --> sets the restart strategy to either Luby or Glucose (default: Luby)"               << std::endl
			<< "c --unitFactor=<value>       --> sets the unit factor of both restart strategies to 'value' (default: 8)"           << std::endl
			<< "c --decayFactor=<value>      --> sets the decay factor (variable activities) to 'value' (default: 1.05)"            << std::endl
			<< "c --decision=<value>         --> sets the decision strategy to mode 'value' (default: 0)"                           << std::endl
			<< "c                                mode 0: use the cached polarity together with antom's 'polarity toggling scheme'"  << std::endl
			<< "c                                mode 1: use the cached polarity only"                                              << std::endl
			<< "c                                mode 2: the polarity will be set to FALSE regardless of the cached value"          << std::endl
			<< "c                                mode 3: the polarity will be set to TRUE regardless of the cached value"           << std::endl
			<< "c preprocessor options:"                                                                                            << std::endl
			<< "c --prepro=<true/false>      --> enables/disables preprocessor (default: false)"                                    << std::endl
			<< "c --inpro=<true/false>       --> enables/disables inprocessor during solve (default: false)"                        << std::endl
			<< "c --maxInpro=<true/false>    --> enables/disables inprocessor during maxsolve (default: false)"                      << std::endl
			<< "c --upla=<true/false>        --> enables/disables 'UPLA' during pre/inprocessing (default: true)"                   << std::endl
			<< "c --subsumption=<true/false> --> enables/disables full subsumption check during pre/inprocessing (default: true)"   << std::endl
			<< "c --varElim=<true/false>     --> enables/disables variable elimination during pre/inprocessing (default: true)"     << std::endl
			<< "c --maxloops=<value>         --> sets the maximum number of preprocessing main loops (default: 1000000)"            << std::endl
			<< "c maxSAT options:"                                                                                                  << std::endl
			<< "c --sortvar=<value>          --> sets variable priority of variables involved in maxSAT (default: false)"           << std::endl
			<< "c                                false: priorities unchanged"                                                       << std::endl
			<< "c                                true: prefer variables of sorting network"                                         << std::endl
			<< "c                                reverse: prefer variables of original instance"                                    << std::endl 
			<< "c                                random: some variables are randomly prefered"                                      << std::endl
			<< "c --sortsoft=<value>         --> sort soft clause parts for partialMode (default: 0)"                               << std::endl
			<< "c                                0: no sorting"                                                                     << std::endl
			<< "c                                1: sort soft clauses due to the larger number of conflicting soft clauses"         << std::endl
			<< "c                                2: sort soft clauses due to the smaller number of conflicting soft clauses"        << std::endl 
			<< "c                                3: random sort"                                                                    << std::endl
			<< "c --splitWidth=<value>       --> sets splitting width for partialMode (default: 32)"                                << std::endl 
			<< "c --maxWidth=<value>         --> sets maximum splitting width for partialMode (default: 0 = none)"                  << std::endl 
			<< "c --maxParts=<value>         --> sets maximum number of splitting parts for partialMode (default: 0 = none)"        << std::endl 
			<< "c --skip=<true/false>        --> enables/disables skipping of comperators (default: false)"                         << std::endl 
			<< "c --csc=<true/false/all>     --> enables/disables 'conflicting soft clauses' (default: false)"                      << std::endl 
			<< "c --trigger<t=rue/false>     --> enables/disables 'trigger setting' (default: false)"                               << std::endl 
			<< "c --incomplete=<true/false>  --> enables/disables incomplete mode (default: true)"                                  << std::endl 
			<< "c --gridMode=<value>         --> activates bypass grid (default: 0)"                                                << std::endl 
			<< "c                                0: no grid"                                                                        << std::endl
			<< "c                                1: horizontal bypasses"                                                            << std::endl
			<< "c                                2: vertical bypasses"                                                              << std::endl
			<< "c                                3: bypass grid (horizontla+vertical)"                                              << std::endl
			<< "c --horiWidth=<value>        --> sets width of horizontal grid (default: 4)"                                        << std::endl 
			<< "s UNKNOWN"                                                                                                          << std::endl;
}
