/********************************************************************************************
varheap.h -- Copyright (c) 2013-2016, Tobias Schubert, Sven Reimer

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

#ifndef HQSPRE_VARHEAP_HPP_
#define HQSPRE_VARHEAP_HPP_

#include <cassert>
#include <vector>


/**
 * \file varheap.hpp
 * \author Tobias Schubert
 * \author Sven Reimer
 * \date 2013-16
 * \brief Heap data structure to be used as a priority queue
 */

namespace hqspre {

/**
 * \brief Used to construct a min-heap which returns the element with the lowest value
 */
template <typename T>
class DescendingOrder
{
public:
    DescendingOrder(const std::vector<T>& a) :
        act(a)
    {}

    bool operator()(const uint32_t& x, const uint32_t& y) const noexcept
    {
        return (act[x] > act[y]);
    }

private:
    const std::vector<T>& act;
};


/**
 * \brief Used to construct a max-heap which returns the element with the highest value.
 */
template <typename T>
class AscendingOrder
{
public:
    AscendingOrder(const std::vector<T>& a) :
        act(a)
    {}

    bool operator()(const uint32_t& x, const uint32_t& y) const noexcept
    {
        return (act[x] < act[y]);
    }

private:
    const std::vector<T>& act;
};



template < template < typename > class Order, typename T>
class VarHeap
{

public:

    /**
     * \brief Constructs an empty heap with a given order.
     */
    VarHeap(const Order<T>& ord):
        _heap(),
        _position(),
        _size(0),
        _variables(0),
        _comp(ord)
    {}

    ~VarHeap() = default;

    /**
     * \brief Updates all data structures to be able to handle "var" variables.
     */
    void resize(uint32_t var)
    {
        _position.resize(var + 1, -1);
        _heap.resize(var, 0);
        _variables = var;
    }

    /**
     * \brief Clears the entire heap.
     */
    void clear() noexcept
    {
        for (uint32_t m = 0; m < _size; ++m)
        {
            _position[_heap[m]] = -1;
        }
        _size = 0;
    }

    /**
     * \brief Returns whether the heap is empty or not.
     */
    bool empty(void) const noexcept
    {
        return (_size == 0);
    }

    /**
     * \brief Returns the current size of `_heap`.
     */
    uint32_t size(void) const noexcept
    {
        return _size;
    }


    /**
     * \brief Returns whether "var" is an element of "_heap".
     */
    bool inHeap(uint32_t var) const noexcept
    {
        // "var" has to be less or equal "_variables".
        assert(var <= _variables);

        // Return whether "var" is part of the heap.
        return (_position[var] > -1);
    }

    /**
     * \brief Updates the position of "var" within the heap.
     */
    void update(uint32_t var) noexcept
    {
        // "var" has to be less or equal "_variables".
        assert(var <= _variables);

        // "var" has to be an element of "_heap".
        assert(_position[var] > -1);

        // Ensure that the heap property holds. Assumes, that "var's"
        // activity has been incremented.
        shiftUpwards(_position[var]);
    }

    /**
     * \brief Inserts variable "var" into "_heap".
     */
    void insert(uint32_t var) noexcept
    {
        // "var" has to be less or equal "_variables".
        assert(var <= _variables);

        // If "var" is an element of "_heap", we've got a problem.
        assert(_position[var] == -1);

        // Update "_position".
        _position[var] = _size;

        // Add "var" to "_heap".
        _heap[_size] = var;

        // Increment "_size".
        ++_size;

        // Ensure that the heap property holds.
        shiftUpwards(_position[var]);
    }

    /**
     * \brief Returns the root variable.
     */
    uint32_t top(void) noexcept
    {
        // If "_heap" is empty, we've got a problem.
        assert(_size > 0);

        // Get the root variable.
        uint32_t var = _heap[0];

        // Decrement "_size".
        --_size;

        // Overwrite "_heap[0]" with the last element of "_heap".
        _heap[0] = _heap[_size];

        // Update "_position".
        _position[var] = -1;

        // If we removed the last element from the heap, we can skip the following operations.
        if (_size > 0)
        {
            // Update "_position".
            _position[_heap[0]] = 0;

            // Ensure that the heap property holds.
            shiftDownwards(0);
        }

        // Return "var".
        return var;
    }

    /**
     * \brief Removes "var" from the heap.
     */
    void remove(uint32_t var) noexcept
    {
        // If "_heap" is empty, we've got a problem.
        assert(_size > 0);

        // Initialization.
        const int pos = _position[var];

        // If "var" is not part of the heap, we've got a problem.
        assert(pos > -1);

        // Decrement "_size".
        --_size;

        // Overwrite "_heap[pos]" with the last element of "_heap".
        _heap[pos] = _heap[_size];

        // Update "_position".
        _position[var] = -1;

        // If we removed the right-most element from the heap, we can skip the following operations.
        if ((uint32_t) pos != _size)
        {
            // Update "_position".
            _position[_heap[pos]] = pos; 

            // Ensure that the heap property holds. 
            shiftDownwards(pos);
        }

        // Consistency check.
        assert(_position[var] == -1);
    }

private:

    /**
     * \brief Returns the position of the "father" of the element stored on position "pos".
     */
    uint32_t father(uint32_t pos) const noexcept
    {
        return ((pos - 1) >> 1);
    }

    /**
     * \brief Returns the position of the left "son" of the element stored on position "pos".
     */
    uint32_t left(uint32_t pos) const noexcept
    {
        return ((pos << 1) + 1);
    }

    /**
     * \brief Returns the position of the right "son" of the element stored on position "pos".
     */
    uint32_t right (uint32_t pos) const noexcept
    {
        return ((pos + 1) << 1);
    }

    /**
     * \brief Ensures the heap property by shifting the element on position "pos" of "_heap" upwards.
     */
    void shiftUpwards(uint32_t pos) noexcept
    {
        // Get the variable stored on position "pos".
        const uint32_t var = _heap[pos];

        // Determine the correct position of "var" within "_heap".
        while (pos > 0 && _comp(var,_heap[father(pos)]))
        {
            _heap[pos]            = _heap[father(pos)];
            _position[_heap[pos]] = pos;
            pos                   = father(pos);
          }

        // Store "var" at position "pos".
        _heap[pos]     = var;
        _position[var] = pos;
    }

    /**
     * \brief Ensures the heap property by shifting the element on position "pos" of "_heap" downwards.
     */
    void shiftDownwards(uint32_t pos)
    {
        // Get the variable stored on position "pos".
        const uint32_t var = _heap[pos];

        // Determine the correct position of "var" within "_heap".
        while (left(pos) < _size)
        {
            const uint32_t r = right(pos);
            const uint32_t child = r < _size && _comp(_heap[r],_heap[left(pos)]) ? r : left(pos);

            if (!_comp(_heap[child], var)) { break; }

            _heap[pos]            = _heap[child];
            _position[_heap[pos]] = pos;
            pos                   = child;
        }

        // Store "var" at position "pos".
        _heap[pos]     = var;
        _position[var] = pos;
    }


    /// The heap.
    std::vector<uint32_t> _heap;

    /// The position of a particular variable within "_heap".
    std::vector<int32_t> _position;

    /// The current size of "_heap".
    uint32_t _size;

    /// The maximum number of variables for which memory has been reserved.
    uint32_t _variables;

    /// Ordering class
    Order<T> _comp;
};


} // end namespace hqspre

#endif
