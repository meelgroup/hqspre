// $Id: timer.hpp 1001 2016-07-31 16:57:41Z wimmer $

// Copyright 2010-2011, Ralf Wimmer, Albert-Ludwigs-University Freiburg, Germany
// wimmer@informatik.uni-freiburg.de

#ifndef HQSPRE_TIMER_HPP_
#define HQSPRE_TIMER_HPP_

#include <iosfwd>

namespace hqspre {


/**
 * \class Timer
 * \brief Class to measure elapsed time.
 * \author Ralf Wimmer, Albert-Ludwigs-University Freiburg, Germany
 */
class Timer
{
public:
    Timer();
    void   start();
    void   stop();
    void   reset();
    double read() const;

private:

    double gettime() const;

    double current_time; ///< The amount of time that has already passed
    double start_time;   ///< The point in time when the timer has been started the last time
    bool running;        ///< Is the Timer running?
};


/**
 * \brief Starts a given timer upon creation and stops it upon destruction
 */
class ScopeTimer
{
public:
    ScopeTimer(Timer& _timer): timer(_timer)
    {
        timer.start();
    }

    ~ScopeTimer()
    {
        timer.stop();
    }

private:
    Timer& timer; ///< The timer to be started and stopped automatically
};

std::ostream& operator<<(std::ostream& stream, const Timer& timer);

bool createTimeout(double timeout, void(*timeoutHandler)(int) );

} // end namespace hqspre

#endif
