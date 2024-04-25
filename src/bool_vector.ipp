/**************************************************************
 *
 *       LRABS // BoolVector.icc
 *
 *       Copyright (C) 2007 Florian Pigorsch
 *
 *       Author:
 *         Florian Pigorsch
 *         University of Freiburg
 *         pigorsch@informatik.uni-freiburg.de
 *
 *       Last revision:
 *         $Revision: 236 $
 *         $Author: pigorsch $
 *         $Date$
 *
 ***************************************************************/

#ifndef HQSPRE_BOOL_VECTOR_IPP_
#define HQSPRE_BOOL_VECTOR_IPP_

namespace hqspre {

inline std::size_t BoolVector::size() const noexcept
{
    return _size;
}

inline bool BoolVector::uninitialized() const noexcept
{
    return _bins == 0;
}

inline bool BoolVector::get( std::size_t index ) const
{
    return ( _bins[ ( index / BinSize ) ] >> ( index % BinSize ) ) & 1ul;
}

inline void BoolVector::setBin( std::size_t index, BoolVector::BinType b )
{
    _bins[ index ] = b;
}

} // end namespace hqspre

#endif
