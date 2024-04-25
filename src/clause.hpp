#ifndef HQSPRE_CLAUSE_HPP_
#define HQSPRE_CLAUSE_HPP_

#include <vector>
#include <ostream>
#include <cstdint>
#include <limits.h>
#include "literal.hpp"


/**
 * \file clause.hpp
 * \author Ralf Wimmer
 * \date 05/2016
 * \brief Data structures related to clauses
 */

namespace hqspre {

/**
 * \brief Status of a clause (mandatory/optional/deleted)
 */
enum class ClauseStatus: short
{
    /**
     * \brief Actual problem clause
     *
     * Mandatory clauses may not be deleted.
     */
    MANDATORY, ///< actual problem clause

    /**
     * \brief Redundant clause which may be deleted if not used.
     *
     * Optional clauses must be implications from the mandatory clauses.
     * They can be deleted without changing the set of satisfying assignments
     * of the (mandatory) matrix.
     */
    OPTIONAL,

    /**
     * \brief A clause which has been deleted.
     *
     * Deleted clauses may not be accessed anymore and will
     * be recycled in future.
     */
    DELETED    ///< deleted (invalid) clause
};


/**
 * \brief Add the signature bit of a single literal to signature
 */
template <typename T>
inline void addSignatureLit(T& signature, Literal literal) noexcept
{
    static_assert(std::is_integral<T>::value, "addSignatureLit(&, Literal) only works for integral types T");
    constexpr unsigned int num_bits = sizeof(signature) * CHAR_BIT;
    signature |= 1ul << (literal % num_bits);
}


// Forward declaration
class Formula;


/**
 * \brief Representation of a clause, i.e., a disjunction of literals.
 */
class Clause
{
public:
    ///\brief Type of a forward (read/write) iterator
    typedef std::vector<Literal>::iterator iterator;

    ///\brief Type of a forward read-only iterator
    typedef std::vector<Literal>::const_iterator const_iterator;

    ///\brief Type of a reverse (read/write) iterator
    typedef std::vector<Literal>::reverse_iterator reverse_iterator;

    ///\brief Type of a reverse read-only iterator
    typedef std::vector<Literal>::const_reverse_iterator const_reverse_iterator;

    /**
     * \brief Creates a copy of a given clause.
     */
    Clause(const Clause&) = default;

    /**
     * \brief Moves a given clause into a new one.
     */
    Clause(Clause&&) = default;
    explicit Clause(const std::vector<Literal>& _literals, bool needs_check = true, ClauseStatus _status = ClauseStatus::MANDATORY);
    explicit Clause(std::vector<Literal>&& _literals, bool needs_check = true, ClauseStatus _status = ClauseStatus::MANDATORY) noexcept;

    /// \brief Destructor with default behavior
    ~Clause() noexcept = default;

    /// \brief Assignment operator with default behavior
    Clause& operator=(const Clause&) = default;

    /// \brief Move assignment operator with default behavior
    Clause& operator=(Clause&&)  = default;

    std::size_t size()                const noexcept;
    bool empty()                      const noexcept;
    bool isTautology()                const noexcept;
    bool containsLiteral(Literal lit) const;

    template <typename Container>
    bool subsetOf(const Container& other, const uint64_t signature) const;

    //@{
    /**
     * \name Getting iterators for traversing the clause
     */
    const_iterator cbegin()          const noexcept;
    const_iterator cend()            const noexcept;
    const_iterator begin()           const noexcept;
    const_iterator end()             const noexcept;

    const_reverse_iterator crbegin() const noexcept;
    const_reverse_iterator crend()   const noexcept;
    const_reverse_iterator rbegin()  const noexcept;
    const_reverse_iterator rend()    const noexcept;
    //@}

    Literal front()                           const noexcept;
    Literal back()                            const noexcept;
    Literal operator[](unsigned int pos)      const noexcept;
    const std::vector<Literal>& getLiterals() const noexcept;

    bool operator==(const Clause& other)      const;
    bool operator!=(const Clause& other)      const;

    ClauseStatus getStatus()                  const noexcept;
    void setStatus(ClauseStatus new_status)         noexcept;
    std::uint64_t getSignature()              const noexcept;
    std::uint32_t getVarSignature()           const noexcept;

    bool isMarked()                           const noexcept;
    bool isMarked(unsigned int pos)           const noexcept;
    void mark(unsigned int pos)               const noexcept;
    void unMark()                             const noexcept;
    void unMark(unsigned int pos)             const noexcept;

    bool checkConsistency()                   const;

private:

    // Private methods; all methods which provide write access to the
    // clause are private.

    iterator begin()          noexcept;
    iterator end()            noexcept;
    reverse_iterator rbegin() noexcept;
    reverse_iterator rend()   noexcept;

    ///\brief Gives (read and write) access to the literal at position `pos`.
    Literal& operator[](unsigned int pos) { return literals[pos]; }

    ///\brief Makes the clause empty.
    void clear() { literals.clear(); signature = 0; }

    ///\brief Resizes the underlying vector of literals to the given size.
    void resize(unsigned int new_size) { literals.resize(new_size, 0); }

    ///\brief Reserves memory for (at least) the given number of literals.
    void reserve(unsigned int new_capacity) { literals.reserve(new_capacity); }

    ///\brief Erases a range of literals from the clause.
    iterator erase(iterator begin, iterator end) { return literals.erase(begin, end); }

    void computeSignature();

    // private data
    std::vector<Literal> literals; ///< Vector of literals
    ClauseStatus status;           ///< Status of the clause (mandatory/optional/deleted)

    /**
     * \brief The signature of the clause.
     * signature is the clause signature produced by the IDs of the literals
     * var_signature is produced by the IDs of the variables
     * \sa Clause::computeSignature()
     */
    std::uint64_t signature = 0;
    std::uint32_t var_signature = 0;

    /**
     * \brief Marking for the clause
     * Used by various methods to mark whether a clause was touched/edited during the process
     */
    mutable uint8_t marked = 0;

    // friend declarations
    friend class Formula;
};

Clause resolve(const Clause& c_pos, const Clause& c_neg, const Variable var);
std::ostream& operator<<(std::ostream& stream, const Clause& clause);


/**
 * \brief Representation of a binary clause, i.e. the implied literal and its clause id
 *
 * The BinaryClause objects are used to store the implication graph
 * of the binary clauses. For a binary clause \f$\{a,b\}\f$ with ID 
 * \f$i\f$ we have two BinaryClause objects: One is stored in `implications`
 * at position \f$\neg a\f$ and contains the implied literal \f$b\$f
 * together with the ID \f$i\f$. The other one is stored at \f$\neg b\f$
 * and contains \f$a\f$ and the ID \f$i\f$.
 */
class BinaryClause
{
public:
    BinaryClause(Literal lit, unsigned int id);
    BinaryClause(Literal lit);
    ~BinaryClause() = default;

    bool operator==(const BinaryClause& other) const;
    bool operator!=(const BinaryClause& other) const;
    bool operator<(const BinaryClause& other)  const;

    unsigned int getLiteral() const noexcept;
    unsigned int getClauseID() const noexcept;

private:
    Literal literal;        ///< The implied literal
    unsigned int clause_id; ///< The ID of the corresponding regular clause
};

} // end namespace hqspre

#include "clause.ipp"

#endif
