/*
 * Class exercise from Daniel M. Zimmerman (2013)
 */

class Clock {
  
  // The number of seconds in a minute.
  final int SECS_IN_MIN = 60;
  
  // The number of minutes in an hour.
  final int MINS_IN_HOUR = 60;
  
  // The number of hours in a day.
  final int HOURS_IN_DAY = 24;
  
  // Instance Fields
  
  /**
   * The current hours on the clock.
   */
  private int my_hours; //@ in hours;
  //@ model int hours;
  //@ private represents hours = my_hours;
  
  /**
   * The current minutes on the clock.
   */
  private int my_minutes; //@ in minutes;
  //@ model int minutes;
  //@ private represents minutes = my_minutes;
  
  /**
   * The current seconds on the clock.
   */
  private int my_seconds; //@ in seconds;
  //@ model int seconds;
  //@ private represents seconds = my_seconds;

  // model queries for legal times and total number of seconds on the clock
  
  /*@ ensures \result == 0 <= the_hours && the_hours < HOURS_IN_DAY &&
                         0 <= the_minutes && the_minutes < MINS_IN_HOUR && 
                         0 <= the_seconds && the_seconds < SECS_IN_MIN;
      pure helper model boolean legalTime(int the_hours, int the_minutes, int the_seconds);
   */
  
  /*@ ensures \result == hours * MINS_IN_HOUR * SECS_IN_MIN + 
                         minutes * SECS_IN_MIN + seconds;
      pure helper model int totalSeconds();
   */
  

  //@ invariant legalTime(hours, minutes, seconds);

  // Constructor
  
  /* 
   * the constructor should have appropriate constructs that force
   * the client to validate the data passed in.
   */
  
  /**
   * Constructs a new Clock set to the specified time.
   * 
   * @param the_hours The initial setting for hours.
   * @param the_minutes The initial setting for minutes.
   * @param the_seconds The initial setting for seconds.
   */
  //@ requires legalTime(the_hours, the_minutes, the_seconds);
  //@ ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
  Clock(final int the_hours, final int the_minutes, final int the_seconds) {
    my_hours = the_hours;
    my_minutes = the_minutes;
    my_seconds = the_seconds;
  }
  
  /**
   * @return The current hours on the clock.
   */
  //@ ensures \result == hours;
  /*@ pure helper */ int hours() {
    return my_hours;
  }
  
  /**
   * @return The current minutes on the clock.
   */
  //@ ensures \result == minutes;
  /*@ pure helper */ int minutes() {
    return my_minutes;
  }
  
  /**
   * @return The current seconds on the clock.
   */
  //@ ensures \result == seconds;
  /*@ pure helper */ int seconds() {
    return my_seconds;
  }
  
  /**
   * Checks to see if the time on this clock is later than the time
   * on the specified Clock.
   * 
   * @param the_other_clock The other Clock to check.
   * @return true if this Clock has a later time, false otherwise.
   */
  //@ ensures \result == totalSeconds() > the_other_clock.totalSeconds();
  /*@ pure */ boolean later(final Clock the_other_clock) {
    return my_hours > the_other_clock.my_hours ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes > the_other_clock.my_minutes) ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes == the_other_clock.my_minutes &&
            my_seconds > the_other_clock.my_seconds);
  }
  
  /**
   * Checks to see if the time on this clock is earlier than the time
   * on the specified Clock.
   * 
   * @param the_other_clock The other Clock to check.
   * @return true if this Clock has an earlier time, false otherwise.
   */
  //@ ensures \result == totalSeconds() < the_other_clock.totalSeconds();
  /*@ pure */ boolean earlier(final Clock the_other_clock) {
    return my_hours < the_other_clock.my_hours ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes < the_other_clock.my_minutes) ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes == the_other_clock.my_minutes &&
            my_seconds < the_other_clock.my_seconds);
  }

  // Commands
  
  /**
   * Sets the hours on the clock.
   * 
   * @param the_hours The new value for hours.
   */
  //@ requires 0 <= the_hours && the_hours < HOURS_IN_DAY;
  //@ ensures hours == the_hours;
  void setHours(final int the_hours) {
    my_hours = the_hours;
  }

  /**
   * Sets the minutes on the clock.
   * 
   * @param the_minutes The new value for minutes.
   */
  //@ requires 0 <= the_minutes && the_minutes < MINS_IN_HOUR;
  //@ ensures minutes == the_minutes;
  void setMinutes(final int the_minutes) {
    my_minutes = the_minutes;
  }
  
  /**
   * Sets the seconds on the clock.
   * 
   * @param the_seconds The new value for seconds.
   */
  //@ requires 0 <= the_seconds && the_seconds < SECS_IN_MIN;
  //@ ensures seconds == the_seconds;
  void setSeconds(final int the_seconds) {
    my_seconds = the_seconds;
  }
  
  //@ ensures \old(seconds) + 1 < SECS_IN_MIN ==> seconds == \old(seconds) + 1;
  //@ ensures \old(seconds) + 1 == SECS_IN_MIN ==> seconds == 0;
  //@ ensures \old(minutes) + 1 < MINS_IN_HOUR && seconds == 0 ==> minutes == \old(minutes) + 1;
  //@ ensures \old(minutes) + 1 == MINS_IN_HOUR && seconds == 0 ==> minutes == 0;
  //@ ensures 0 < seconds ==> minutes == \old(minutes);
  //@ ensures \old(hours) + 1 < HOURS_IN_DAY && minutes == 0 && seconds == 0 ==> hours == \old(hours) + 1;
  //@ ensures \old(hours) + 1 == HOURS_IN_DAY && minutes == 0 && seconds == 0 ==> hours == 0;
  //@ ensures 0 < minutes ==> hours == \old(hours);
  /**
   * Ticks the clock forward by one second. If we have reached the
   * end of the day (that is, we tick forward from 23:59:59), the clock 
   * should wrap around to 00:00:00.
   */
  void tick() {
    my_seconds = my_seconds + 1;
    
    if (my_seconds >= SECS_IN_MIN) {
      my_minutes = my_minutes + 1;
      my_seconds = 0;
    }
    
    if (my_minutes >= MINS_IN_HOUR) {
      my_hours = my_hours + 1;
      my_minutes = 0;
    }
    
    if (my_hours >= HOURS_IN_DAY) {
      my_hours = 0;
    }
  }
}