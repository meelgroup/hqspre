#include <ostream>
#include <signal.h>
#include <time.h>
#include <sys/time.h>
#include "timer.hpp"


namespace hqspre {

/**
 * \file timer.cpp
 * \brief Implementation of the Timer class and related functions
 * \author Ralf Wimmer, Albert-Ludwigs-University Freiburg, Germany
 */



/**
   \brief Creates a new timer object.
*/
Timer::Timer():
    current_time(0.0),
    start_time(0.0),
    running(false)
{
}

/**
   \brief Starts or continues time measurement.
*/
void Timer::start()
{
    if (!running) {
        running = true;
        start_time = gettime();
    }
}

/**
   \brief Stops time measurement if running.
   Otherwise calling this function has no effect.
*/
void Timer::stop()
{
    if (running) {
        running = false;
        current_time += (gettime() - start_time);
    }
}


/**
   \brief Resets the time to 0. The timer is stopped if it is currently running.
*/
void Timer::reset()
{
    running = false;
    current_time = 0.0;
    start_time = 0.0;
}


/**
  \brief Returns the measured time in seconds.
*/
double Timer::read() const
{
    if (running) {
        return (current_time + (gettime() - start_time));
    } else {
        return current_time;
    }
}


/**
   \brief Returns the time used by the current process.
   \note If _user_plus_system_time is set to true, the sum of
     user and system time are returned, otherwise only the user time.
   \return The time used by the current process, measure in CLOCKS_PER_SEC.
*/
double Timer::gettime() const
{
    static timeval start;
    gettimeofday(&start, 0);
    return static_cast<double>(start.tv_sec) + static_cast<double>(start.tv_usec)/1000000.0;
}


/**
   \brief Prints the measured time to the given output stream.
   \param stream the stream the measured time is to be printed to
   \param timer the time measurement object whose values is to be printed.
   \note The value of the object is treated as a double value.
*/
std::ostream& operator<<(std::ostream& stream, const Timer& timer)
{
    stream << timer.read();
    return stream;
}

/**
 * \brief Sets up a timeout after which a signal handler is called
 * 
 * @param[in] timeout amount of time in seconds after which the handler is to be called
 * @param[in] timeoutHandler function pointer pointing to the function called after the timeout
 * @return true iff estabilishing the timeout was successful
 */
bool createTimeout( double timeout, void(*timeoutHandler)(int) )
{
    struct sigaction sigact;
    struct sigevent sigev;
    timer_t timerid;

    sigact.sa_handler = timeoutHandler;
    sigemptyset( &sigact.sa_mask );
    sigact.sa_flags = 0;
    if (sigaction( SIGUSR1, &sigact, 0 ) != 0) {
        // 'sigaction' failed
        return false;
    }

    sigev.sigev_notify = SIGEV_SIGNAL;
    sigev.sigev_signo = SIGUSR1;
    if (timer_create( CLOCK_PROCESS_CPUTIME_ID, &sigev, &timerid )  != 0) {
        // 'timer_create' failed
        return false;
    }

    struct itimerspec interval;
    interval.it_value.tv_sec = (int)timeout;
    interval.it_value.tv_nsec = ( timeout - interval.it_value.tv_sec ) * 1000000000;
    interval.it_interval.tv_sec = 0;
    interval.it_interval.tv_nsec = 0;
    if (timer_settime( timerid, 0, &interval, NULL ) != 0) {
        // 'timer_settime' failed
        return false;
    }

    // everything seems successful
    return true;
}

} // end namespace hqspre
