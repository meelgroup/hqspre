#include <set>
#include <iostream>
#include "aux.hpp"
#include "literal.hpp"
#include "clause.hpp"
#include "formula.hpp"

namespace hqspre {

bool Formula::pairBlockedClauses()
{
    if (setting.verbosity > 0) {
        std::cout << __FUNCTION__ << std::endl;
    }
    val_assert(unit_stack.empty());

    unsigned int count = 0;

    for (unsigned int c_nr = 0; c_nr < clauses.size(); ++c_nr) {
        if (clauseDeleted(c_nr)) continue;
        std::vector<Literal> current_clause(clauses[c_nr].size());
        for (unsigned int i = 0; i != clauses[c_nr].size(); ++i) {
            current_clause[i] = clauses[c_nr][i];
            val_assert(!_seen[current_clause[i]]);
             _seen[current_clause[i]] = true;
        }
        auto sig = clauses[c_nr].getSignature();
        addHiddenLiteralsBinary(c_nr, current_clause, sig);
        clearSeen(current_clause);
        bool blocked = true;
        bool found1 = false;
        bool found2 = false;

        for (auto lit1_pos = current_clause.cbegin(); lit1_pos != current_clause.cend(); ++lit1_pos) {
            const Literal lit1 = *lit1_pos;
            const Variable var1 = lit2var(lit1);
            if (!isExistential(var1)) continue;
            found1 = true;

            auto lit2_pos = lit1_pos;
            ++lit2_pos;
            for (; lit2_pos != current_clause.cend(); ++lit2_pos) {
                const Literal lit2 = *lit2_pos;
                const Variable var2 = lit2var(lit2);
                if (!isExistential(var2)) continue;
                found2 = true;

                std::set<unsigned int> res_candidates;
                res_candidates.insert(occ_list[negate(lit1)].cbegin(), occ_list[negate(lit1)].cend());
                res_candidates.insert(occ_list[negate(lit2)].cbegin(), occ_list[negate(lit2)].cend());

                for (const unsigned int other_c_nr: res_candidates) {
                    const Clause& other_clause = clauses[other_c_nr];
                    std::set<Literal> resolvent;
                    resolvent.insert(negate(lit1));
                    resolvent.insert(negate(lit2));
                    bool lit1_found = false;
                    bool lit2_found = false;
                    for (unsigned int ell: current_clause) {
                        if (ell == lit1 || ell == lit2) continue;
                        else resolvent.insert(ell);
                    }
                    for (unsigned int ell: other_clause) {
                        if (ell == negate(lit1)) lit1_found = true;
                        else if (ell == negate(lit2)) lit2_found = true;
                        resolvent.insert(ell);
                    }
                    auto it1 = resolvent.cbegin();
                    auto it2 = it1;
                    ++it2;
                    bool tautology = false;
                    while (it2 != resolvent.cend()) {
                        if (lit2var(*it1) == lit2var(*it2) && *it1 != *it2) {
                            // tautology found;
                            const Variable tvar = lit2var(*it1);
                            if ( (!lit1_found || dependenciesSubset(tvar, lit2var(lit1))) || (!lit2_found || dependenciesSubset(tvar, lit2var(lit2))) ) {
                                tautology = true;
                                break;
                            }
                        }
                        ++it1;
                        ++it2;
                    }
                    if (!tautology) { blocked = false; break; }
                }
                if (blocked) break;
            }
            if (blocked) break;
        }

        if (blocked && found1 && found2) {
            ++count;
            removeClause(c_nr);
        }
    }
    if (setting.verbosity > 1) {
        std::cout << "c " << __FUNCTION__ << " () removed " << count << " pair-blocked clauses.\n";
    }


    return count > 0;
}


} // end namespace hqspre
