//@def_type Legal_Secs = {int v | 0 <= v && v < SECS_IN_MIN};
//@def_type Legal_Mins = {int v | 0 <= v && v < MINS_IN_HOUR};
//@def_type Legal_Hours = {int v | 0 <= v && v < HOURS_IN_DAY};
//@ in hours;
//@ model int refinement_type Legal_Hours hours;
//@ private represents hours = my_hours;
//@ in minutes;
//@ model int refinement_type Legal_Mins minutes;
//@ private represents minutes = my_minutes;
//@ in seconds;
//@ model int refinement_type Legal_Secs seconds;
//@ private represents seconds = my_seconds;
/*@ ensures \result == hours * MINS_IN_HOUR * SECS_IN_MIN + 
                        minutes * SECS_IN_MIN + seconds;
    pure helper model int totalSeconds();
  */
//@ ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
/*`@refinement_type Legal_Hours*/
/*`@refinement_type Legal_Mins*/
/*`@refinement_type Legal_Secs*/
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
//@ ensures hours == the_hours;
/*`@refinement_type Legal_Hours*/
//@ ensures minutes == the_minutes;
/*`@refinement_type Legal_Mins*/
//@ ensures seconds == the_seconds;
/*`@refinement_type Legal_Secs*/
//@ ensures \old(seconds) + 1 < SECS_IN_MIN ==> seconds == \old(seconds) + 1;
//@ ensures \old(seconds) + 1 == SECS_IN_MIN ==> seconds == 0;
//@ ensures \old(minutes) + 1 < MINS_IN_HOUR && seconds == 0 ==> minutes == \old(minutes) + 1;
//@ ensures \old(minutes) + 1 == MINS_IN_HOUR && seconds == 0 ==> minutes == 0;
//@ ensures 0 < seconds ==> minutes == \old(minutes);
//@ ensures \old(hours) + 1 < HOURS_IN_DAY && minutes == 0 && seconds == 0 ==> hours == \old(hours) + 1;
//@ ensures \old(hours) + 1 == HOURS_IN_DAY && minutes == 0 && seconds == 0 ==> hours == 0;
//@ ensures 0 < minutes ==> hours == \old(hours);
//@no_refinement_type