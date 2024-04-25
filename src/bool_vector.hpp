/**************************************************************
 *
 *       LRABS // BoolVector.hh
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

#ifndef HQSPRE_BOOL_VECTOR_HPP_
#define HQSPRE_BOOL_VECTOR_HPP_

#include <climits>
#include <iosfwd>

/**
 * \file bool_vector.hpp
 * \brief Header file for BoolVector
 * \author Florian Pigorsch, Ralf Wimmer
 * \date 2007-16
 */

namespace hqspre
{

    /**
     * \brief Data structure for compactly storing bit vectors
     *
     * It stores bools with 1 bit per value on average and provides
     * dedicated operators like bit-wise logical operations.
     */
    class BoolVector
    {
    public:
        typedef unsigned long BinType;

        BoolVector();
        explicit BoolVector( std::size_t size, bool initial = true );
        BoolVector( const BoolVector& v );
        BoolVector( BoolVector&& v ) noexcept;
        ~BoolVector();

        BoolVector& operator=( const BoolVector& v );
        BoolVector& operator=( BoolVector&& v ) noexcept;

        std::size_t size() const noexcept;

        /* count the number of "true" values in the vector */
        std::size_t countTrue() const;

        /* returns the lowest index whose value is "true", -1 if no such index exists */
        long getFirstTrue() const;

        bool uninitialized() const noexcept;
        void initialize( std::size_t size, bool initial = true );

        bool get( std::size_t index ) const;
        void set( std::size_t index, bool value );
        void flip( std::size_t index );

        void setBin( std::size_t index, BinType b );

        void set( bool value );

        bool allTrue() const;
        bool allFalse() const;
        bool operator==( const BoolVector& b ) const;

        BoolVector operator~() const;
        void flip();

        BoolVector& operator &=( const BoolVector& v );
        BoolVector& operator |=( const BoolVector& v );
        BoolVector& operator ^=( const BoolVector& v );

        static bool intersectAndCheckEmpty( BoolVector& v1, const BoolVector& v2 );
    protected:
        /*! 
         * Compile-time constants used in BoolVector.
         */
        enum Constants
        {
            BinSize = CHAR_BIT * sizeof( BinType ) /*!< Bit-size of one bin */
        };

        std::size_t _size;
        std::size_t _binCount;
        BinType _lastBinMask;

        BinType* _bins;

        friend std::ostream& operator<<( std::ostream& os, const BoolVector& b );
    };

    std::ostream& operator<<( std::ostream& os, const BoolVector& b );
}


#include "bool_vector.ipp"

#endif /* LRABS_BOOLVECTOR_HH */
