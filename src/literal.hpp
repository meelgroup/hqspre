#ifndef HQSPRE_LITERAL_HPP_
#define HQSPRE_LITERAL_HPP_

/**
 * \file literal.hpp
 * \author Ralf Wimmer
 * \date 05/2016
 * \brief Manipulation of literals
*/


namespace hqspre {


using Literal = unsigned int;
using Variable = unsigned int;


/**
 * \brief Converts a literal to its underlying variable.
 */
inline constexpr Variable lit2var(const Literal lit) noexcept
{
    return (lit >> 1);
}


/**
 * \brief Converts a variable to a literal with the given polarity.
 */
inline constexpr Literal var2lit(const Variable var, const bool negated = false) noexcept
{
    return ((var << 1) | (negated ? 1 : 0));
}


/**
 * \brief Converts a literal to DIMACS format.
 *
 * Positive literals correspond to the variable index,
 * negative literals to the negative variable index.
 */
inline constexpr int lit2dimacs(const Literal lit) noexcept
{
    return ((lit & 1) == 1) ? (-1 * static_cast<int>(lit2var(lit))) : (static_cast<int>(lit2var(lit)));
}

/**
 * \brief Negates a given literal.
 */
inline constexpr Literal negate(const Literal lit) noexcept
{
    return (lit ^ 1);
}


/**
 * \brief Negates a given literal iff 'negate' is true.
 */
inline constexpr Literal negate_if(const Literal lit, const bool negate) noexcept
{
    return (negate ? (lit ^ 1) : lit);
}


/**
 * \brief Checks whether a given literal is positive.
 */
inline constexpr bool isPositive(const Literal lit) noexcept
{
    return ((lit & 1) == 0);
}


/**
 * \brief Checks whether a given literal is negative.
 */
inline constexpr bool isNegative(const Literal lit) noexcept
{
    return ((lit & 1) != 0);
}


} // end namespace hqspre

#endif
