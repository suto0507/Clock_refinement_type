//@ in hours;
//@ model int hours;
//@ private represents hours = my_hours;
//@ in minutes;
//@ model int minutes;
//@ private represents minutes = my_minutes;
//@ in seconds;
//@ model int seconds;
//@ private represents seconds = my_seconds;
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
//@ requires legalTime(the_hours, the_minutes, the_seconds);
//@ ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
//@ ensures \result == hours;
/*@ pure helper */
//@ ensures \result == minutes;
/*@ pure helper */
//@ ensures \result == seconds;
/*@ pure helper */
//@ ensures \result == totalSeconds() > the_other_clock.totalSeconds();
/*@ pure */
//@ ensures \result == totalSeconds() < the_other_clock.totalSeconds();
/*@ pure */
//@ requires 0 <= the_hours && the_hours < HOURS_IN_DAY;
//@ ensures hours == the_hours;
//@ requires 0 <= the_minutes && the_minutes < MINS_IN_HOUR;
//@ ensures minutes == the_minutes;
//@ requires 0 <= the_seconds && the_seconds < SECS_IN_MIN;
//@ ensures seconds == the_seconds;
//@ ensures \old(seconds) + 1 < SECS_IN_MIN ==> seconds == \old(seconds) + 1;
//@ ensures \old(seconds) + 1 == SECS_IN_MIN ==> seconds == 0;
//@ ensures \old(minutes) + 1 < MINS_IN_HOUR && seconds == 0 ==> minutes == \old(minutes) + 1;
//@ ensures \old(minutes) + 1 == MINS_IN_HOUR && seconds == 0 ==> minutes == 0;
//@ ensures 0 < seconds ==> minutes == \old(minutes);
//@ ensures \old(hours) + 1 < HOURS_IN_DAY && minutes == 0 && seconds == 0 ==> hours == \old(hours) + 1;
//@ ensures \old(hours) + 1 == HOURS_IN_DAY && minutes == 0 && seconds == 0 ==> hours == 0;
//@ ensures 0 < minutes ==> hours == \old(hours);