#include <algorithm>
#include <set>
#include <iostream>
#include "aux.hpp"
#include "clause.hpp"

/**
 * \file clause.cpp
 * \brief Implementation of operations on clauses
 * \author Ralf Wimmer
 * \date 05-06/2016
 */

namespace hqspre {

/**
 * \brief Checks if the given sorted range contains a duplicate element
 */
template<typename Iterator>
static bool is_unique(Iterator first, Iterator last)
{
    return std::adjacent_find(first, last) == last;
}


/**
 * \brief Creates a clause from a vector of literals
 *
 * \param _literals the vector of literals
 * \param needs_check if true the literals get sorted and duplicate literals are removed
 * \param _status status of the clause (mandatory, optional, deleted)
 * \pre If needs_check is false, the user has to guarantee that the clause is
 *      sorted and does not contain duplicate literals.
 */
Clause::Clause(const std::vector<Literal>& _literals, bool needs_check, ClauseStatus _status):
    literals(_literals),
    status(_status)
{
    if (needs_check) {
        std::sort(literals.begin(), literals.end());
        literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    }

    val_assert(std::is_sorted(literals.cbegin(), literals.cend()));
    val_assert(is_unique(literals.cbegin(), literals.cend()));

    computeSignature();
}


/**
 * \brief Creates a clause from a vector of literals
 *
 * \param _literals the vector of literals
 * \param needs_check if true the literals get sorted and duplicate literals are removed
 * \param _status status of the clause (mandatory, optional, deleted)
 * \pre If needs_check is false, the user has to guarantee that the clause is
 *      sorted and does not contain duplicate literals.
 */
Clause::Clause(std::vector<Literal>&& _literals, bool needs_check, ClauseStatus _status) noexcept:
    literals(std::move(_literals)),
    status(_status)
{
    if (needs_check) {
        std::sort(literals.begin(), literals.end());
        literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    }
    val_assert(std::is_sorted(literals.cbegin(), literals.cend()));
    val_assert(is_unique(literals.cbegin(), literals.cend()));

    computeSignature();
}


/**
 * \brief Checks if the clause is a tautology.
 *
 * \return true if the clause contains both a variable and its negation at the same time.
 */
bool Clause::isTautology() const noexcept
{
    if (literals.empty()) return false;

    for (unsigned int pos = 0; pos < literals.size() - 1; ++pos) {
        val_assert(literals[pos] != literals[pos+1]);
        if (lit2var(literals[pos]) == lit2var(literals[pos+1])) {
            return true;
        }
    }
    return false;
}


/**
 * \brief Checks if a clause contains a given literal.
 * \return true if the literal appears in the clause, false otherwise.
 */
bool Clause::containsLiteral(const Literal lit) const
{
    return std::binary_search(literals.cbegin(), literals.cend(), lit);
}

/**
 * \brief Computes a signature of the clause.
 *
 * This signature can be used to make subsumption checking more
 * efficient. For clauses \f$C\f$ and \f$C'\f$, if
 * \f$\mathrm{sig}(C)\land\neg\mathrm{sig}(C') \neq 0\f$, then
 * \f$C\f$ cannot subsume \f$C'\f$, i.e., \f$C\not\subseteq C'\f$.
 *
 * \note If a clause is modified, the signature has to be recomputed.
 * \sa Formula::subsumption()
 * \sa Clause::subsetOf(const Clause&)
 */
void Clause::computeSignature()
{
    signature = 0;

    for (Literal lit: literals) {
        addSignatureLit(signature, lit);
        addSignatureLit(var_signature, lit2var(lit));
    }
}


/**
 * \brief Checks if the current clause is a subset of `other`.
 *
 * Assumes that all involved clauses are sorted
 * \sa Clause::computeSignature()
 * \param other the clause that is checked if it contains the current clause
 * \param other_signature the signature of the clause `other`
 */
template <typename Container>
bool Clause::subsetOf(const Container& other, const uint64_t other_signature) const
{
    if (this->size() > other.size()) return false;
    if ((this->getSignature() & ~(other_signature)) != 0) return false;

    return std::includes(this->begin(), this->end(), other.begin(), other.end());
}

  // Excplicit template initialization
  template bool Clause::subsetOf(const std::set<Literal>& other, const uint64_t other_signature) const;
  template bool Clause::subsetOf(const std::vector<Literal>& other, const uint64_t other_signature) const;
  template bool Clause::subsetOf(const Clause& other, const uint64_t other_signature) const;

/**
 * \brief Computes the resolvent of the two clauses w.r.t. the given variable.
 *
 * \param c_pos clause which contains 'var' positive
 * \param c_neg clause which contains 'var' negative
 * \param var pivot variable
 * \return the resolvent of the two clauses.
 * \note The two clauses must be sorted, non-tautological and may not
 *       contain duplicate literals. The resolvent then has the same properties.
 */
Clause resolve(const Clause& c_pos, const Clause& c_neg, const Variable var)
{
    val_assert(c_pos.size() >= 1 && c_neg.size() >= 1);

    std::vector<Literal> result;
    result.reserve(c_pos.size() + c_neg.size() - 2);

    const Literal lit_pos = var2lit(var, false);
    const Literal lit_neg = var2lit(var, true);

    auto iter_pos = c_pos.cbegin();
    auto iter_neg = c_neg.cbegin();
    while (true) {
        // Have we reached the end of the positive clause?
        if (iter_pos == c_pos.cend()) {
            while (iter_neg != c_neg.cend()) {
                if (*iter_neg != lit_neg) result.push_back(*iter_neg);
                ++iter_neg;
            }
            break;
        }

        // Have we reached the end of the negative clause?
        if (iter_neg == c_neg.cend()) {
            while (iter_pos != c_pos.cend()) {
                if (*iter_pos != lit_pos) result.push_back(*iter_pos);
                ++iter_pos;
            }
            break;
        }

        // We haven't reached the end of any clause
        if      (*iter_pos == lit_pos)   { ++iter_pos; }
        else if (*iter_neg == lit_neg)   { ++iter_neg; }
        else if (*iter_pos == *iter_neg) { result.push_back(*iter_pos); ++iter_pos; ++iter_neg; }
        else if (*iter_pos < *iter_neg)  { result.push_back(*iter_pos); ++iter_pos; }
        else if (*iter_neg < *iter_pos)  { result.push_back(*iter_neg); ++iter_neg; }
        else { val_assert(0);result.push_back(*iter_pos); ++iter_pos; ++iter_neg; }
    }

    return Clause(std::move(result), false);
}


/**
 * \brief Checks if the clause is in a consistent state.
 *
 * Consistent means that it is sorted in ascending order,
 * does not contain duplicate literals and is not a tautology.
 * \return true iff the clause is consistent.
 */
bool Clause::checkConsistency() const
{
    for (const Literal lit: literals) {
        if (lit < 2) {
            std::cerr << "[ERROR] Invalid literal in clause: " << lit << std::endl;
            return false;
        }
    }

    if (!std::is_sorted(literals.cbegin(), literals.cend())) {
        std::cerr << "[ERROR] Clause is not sorted: " << *this << std::endl;
        return false;
    }

    if (!is_unique(literals.cbegin(), literals.cend())) {
        std::cerr << "[ERROR] Clause contains duplicate literals: " << *this << std::endl;
        return false;
    }

    if (isTautology()) {
        std::cerr << "[ERROR] Clause is a tautology: " << *this << std::endl;
        return false;
    }

    return true;
}


/**
 * \brief Constructs a new BinaryClause object.
 * \param lit the implied literal
 * \param id the ID of the corresponding regular clause
 */
BinaryClause::BinaryClause(Literal lit, unsigned int id):
  literal(lit),
  clause_id(id)
{}

/**
 * \brief Constructs a new BinaryClause object.
 * \param lit the implied literal
 */
BinaryClause::BinaryClause(Literal lit):
  literal(lit),
  clause_id(0)
{}


} // end namespace hqspre
