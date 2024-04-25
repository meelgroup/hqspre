#ifndef HQSPRE_CLAUSE_IPP_
#define HQSPRE_CLAUSE_IPP_

/**
 * \file clause.ipp
 * \brief Inline implementation of operations on clauses
 * \author Ralf Wimmer
 * \date 05-06/2016
 */

namespace hqspre {

/**
 * \brief Returns the number of literals in the clause
 */
inline size_t Clause::size() const noexcept
{
    return literals.size();
}

/**
 * \brief Checks if the clause is empty.
 */
inline bool Clause::empty() const noexcept
{
    return literals.empty();
}


/**
 * \brief Returns a read-only iterator pointing to the first literal and providing read access.
 */
inline Clause::const_iterator Clause::cbegin() const noexcept
{
    return literals.cbegin();
}

/**
 * \brief Returns a read-only iterator pointing to the first literal and providing read access.
 */
inline Clause::const_iterator Clause::begin() const noexcept
{
    return literals.begin();
}

/**
 * \brief Returns a read-only iterator pointing beyond the last literal and providing read access.
 */
inline Clause::const_iterator Clause::cend() const noexcept
{
    return literals.cend();
}

/**
 * \brief Returns a read-only iterator pointing beyond the last literal and providing read access.
 */
inline Clause::const_iterator Clause::end() const noexcept
{
    return literals.end();
}


/**
 * \brief Returns a read-only reverse iterator pointing to the last literal of the clause.
 */
inline Clause::const_reverse_iterator Clause::crbegin() const noexcept
{
    return literals.crbegin();
}


/**
 * \brief Returns a read-only reverse iterator pointing before the first literal of the clause.
 */
inline Clause::const_reverse_iterator Clause::crend() const noexcept
{
    return literals.crend();
}


/**
 * \brief Returns a read-only reverse iterator pointing to the last literal of the clause.
 */
inline Clause::const_reverse_iterator Clause::rbegin() const noexcept
{
    return literals.rbegin();
}


/**
 * \brief Returns a read-only reverse iterator pointing before the first literal of the clause.
 */
inline Clause::const_reverse_iterator Clause::rend() const noexcept
{
    return literals.rend();
}


/**
 * \brief Returns an iterator pointing to the first literal and providing read and write access.
 */
inline Clause::iterator Clause::begin() noexcept
{
    return literals.begin();
}


/**
 * \brief Returns an iterator pointing beyond the last literal and providing read and write access.
 */
inline Clause::iterator Clause::end() noexcept
{
    return literals.end();
}


/**
 * \brief Returns a reverse iterator pointing to the last literal and providing read and write access.
 */
inline Clause::reverse_iterator Clause::rbegin() noexcept
{
    return literals.rbegin();
}


/**
 * \brief Returns a reverse iterator pointing before the first literal and providing read and write access.
 */
inline Clause::reverse_iterator Clause::rend() noexcept
{
    return literals.rend();
}

/**
 * \brief Returns the first literal in the clause.
 * \pre The clause must not be empty.
 */
inline Literal Clause::front() const noexcept
{
    return literals.front();
}


/**
 * \brief Returns the last literal in the clause.
 * \pre The clause must not be empty.
 */
inline Literal Clause::back() const noexcept
{
    return literals.back();
}


inline const std::vector<Literal>& Clause::getLiterals() const noexcept
{
    return literals;
}

/**
 * \brief Provides read access to the literals.
 *
 * The parameter `pos` must be in the right range. Otherwise the behavior
 * is undefined (similar to access to a std::vector).
 * \return the literal at the specified position
 */
inline Literal Clause::operator[](unsigned int pos) const noexcept
{
    return literals[pos];
}

/**
 * \brief Compares two clauses for equality
 *
 * Two clauses are equal if they contain the same literals.
 */
inline bool Clause::operator==(const Clause& other) const
{
    return this->literals == other.literals;
}


/**
 * \brief Compares two clauses for disequality
 *
 * Two clauses are not equal if they contain different sets of literals.
 */
inline bool Clause::operator!=(const Clause& other) const
{
    return this->literals != other.literals;
}


/**
 * \brief Returns the status of a clause -- MANDATORY, OPTIONAL, or DELETED.
 */
inline ClauseStatus Clause::getStatus() const noexcept
{
    return status;
}


/**
 * \brief Sets the status of a clause -- MANDATORY, OPTIONAL, or DELETED.
 */
inline void Clause::setStatus(ClauseStatus new_status) noexcept
{
    status = new_status;
}


/**
 * \brief Returns the signature of a clause.
 *
 * This signature is used for efficiently excluding candidates
 * of subsumption.
 */
inline std::uint64_t Clause::getSignature() const noexcept
{
    return signature;
}

  inline std::uint32_t Clause::getVarSignature() const noexcept
{
    return var_signature;
}

/**
 * \brief Returns whether the clause was marked
 *
 */
inline bool Clause::isMarked() const noexcept
{
    return marked != 0;
}

/**
 * \brief Returns whether a certain position of the clause was marked
 * \note The position of the marker must be in the range from 0 to 7.
 */
inline bool Clause::isMarked(unsigned int pos) const noexcept
{
    val_assert(pos < 8);
    return static_cast<bool>(marked & (1<<pos));
}

/**
 * \brief Mark a position of the clause
 * \note The position of the marker must be in the range from 0 to 7.
 */
inline void Clause::mark(unsigned int pos) const noexcept
{
    val_assert(pos < 8);
    marked |= (1 << pos);
}

/**
 * \brief Unmark a clause as touched
 *
 */
inline void Clause::unMark() const noexcept
{
    marked = 0;
}

/**
 * \brief Unmark a certain position of the clause
 * \note The position of the marker must be in the range from 0 to 7.
 */
inline void Clause::unMark(unsigned int pos) const noexcept
{
    val_assert(pos < 8);
    marked &= ~(1 << pos);
}

/**
 * \brief Prints a clause in DIMACS format.
 */
inline std::ostream& operator<<(std::ostream& stream, const Clause& clause)
{
    for (const Literal lit: clause) {
        stream << lit2dimacs(lit) << " ";
    }
    stream << "0";

    return stream;
}


/**
 * \brief Checks two BinaryClause objects for equality.
 *
 * Two such objects are equal if they contain the same implied literal,
 * independent of the corresponding clause ID.
 */
inline bool BinaryClause::operator==(const BinaryClause& other) const
{
    return this->literal == other.literal;
}

/**
 * \brief Checks two BinaryClause objects for disequality.
 *
 * Two such objects are equal if they contain the same implied literal,
 * independent of the corresponding clause ID.
 */
inline bool BinaryClause::operator!=(const BinaryClause& other) const
{
    return this->literal != other.literal;
}

/**
 * \brief Provides a linear order on BinaryClause objects.
 *
 * Only the implied literals are compared, not the clause IDs.
 */
inline bool BinaryClause::operator<(const BinaryClause& other) const
{
    return this->literal < other.literal;
}


/**
 * \brief Returns the implied literal of the BinaryClause object.
 */
inline Literal BinaryClause::getLiteral() const noexcept
{
    return literal;
}


/**
 * \brief Returns the ID of the corresponding regular clause.
 */
inline unsigned int BinaryClause::getClauseID() const noexcept
{
    return clause_id;
}


} // end namespace hqspre


#endif
