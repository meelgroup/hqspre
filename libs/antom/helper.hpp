#ifndef HELPER_HPP
#define HELPER_HPP

// Some useful helper functions

#include "clause.hpp"

enum clausetype {
  NOTYPE,
  BINARY,
  TERNARY,
  NNARY,
};

int inline Lit (uint32_t lit)
{ return ( (lit>>1) * (((lit&1)!=0)?-1:1)  ); }

namespace antom {
  // A helper function to compare two clauses wrt. their LBD value & clause length.
  bool inline compareLBD (Clause* c1, Clause* c2) 
  { 
    if (c1->lbd() == c2->lbd())
      { return c1->length() > c2->length(); }
    return c1->lbd() > c2->lbd(); 
  }
}

#endif
