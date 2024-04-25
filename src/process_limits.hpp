/********************************************************************************************
process_limits.h -- Copyright (c) 2016, Sven Reimer

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

#ifndef HQSPRE_PROCESS_LIMITS_H_
#define HQSPRE_PROCESS_LIMITS_H_

namespace hqspre {

enum class PreproMethod : unsigned int
{
    UNIV_REDUCT = 0,
    UNIV_EXPANSION = 1,
    EQUIV = 2,
    BCE = 3,
    IMPL_CHAINS = 4,
    CONTRA = 5,
    HEC = 6,
    SUBSTIUTION = 7,
    SUBSUMPTION = 8,
    SELF_SUBSUMPTION = 9,
    RESOLUTION = 10,
    UNIT_BY_SAT = 11,
    IMPL_BY_SAT = 12
};


/**
 * \brief Manages the limits of the differents processes.
 * Works like a "deterministic" timeout
 */
class ProcessLimit
{

public:
    ProcessLimit() = default;
    ~ProcessLimit() = default;

    void useLimit(bool value)
    {
        check_limits = value;
    }

    void increaseLimitBy(int value)
    {
        process_limit -= value;
    }

    void decreaseLimitBy(int value)
    {
        process_limit -= value;
    }

    void decreaseLimitBy(int factor, int value)
    {
        process_limit -= factor * value;
    }

    void decrementLimit()
    {
        --process_limit;
    }

    bool reachedLimit() const
    {
        return (check_limits && process_limit < 0);
    }

    void setLimit(PreproMethod method)
    {
        process_limit = limits[static_cast<unsigned int>(method)];
    }

    friend std::ostream& operator<<(std::ostream& stream, const ProcessLimit pl);

private:

    const int64_t limits[13] = {
        1ul<<31 , // universal reduction limit - currently not used
        1ul<<25 , // universal expansion limit
        1ul<<31 , // equivalance checking limit - currently not used
        1ul<<31 , // blocked clause elimination limit
        1ul<<31 , // implication chain limit - currently not used
        1ul<<28 , // contradiction limit
        1ul<<31 , // hidden equivalences and contradiction limit
        1ul<<31 , // substitution limit - currently not used
        1ul<<31 , // subsumption limit - currently not used
        1ul<<26 , // self subsumption limit
        1ul<<25 , // resolution limit
        1ul<<26 , // find units by SAT limit
        1ul<<31   // find implications by SAT limit
    };

    /// The given limit
    int64_t process_limit = 0;

    /// Do we check the limits? This may be obsolete (always active) in future
    bool check_limits = true;

};


inline std::ostream& operator<<(std::ostream& stream, const ProcessLimit pl)
{
    stream << pl.process_limit;
    return stream;
}

} // end namespace hqspre

#endif
