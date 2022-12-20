class Clock {
  
  final int SECS_IN_MIN = 60;
  
  final int MINS_IN_HOUR = 60;
  
  final int HOURS_IN_DAY = 24;
  
  //@def_type Legal_Secs = {int v | 0 <= v && v < SECS_IN_MIN};
  //@def_type Legal_Mins = {int v | 0 <= v && v < MINS_IN_HOUR};
  //@def_type Legal_Hours = {int v | 0 <= v && v < HOURS_IN_DAY};

  
  private int my_hours; //@ in hours;
  //@ model int refinement_type Legal_Hours hours;
  //@ private represents hours = my_hours;
  
  private int my_minutes; //@ in minutes;
  //@ model int refinement_type Legal_Mins minutes;
  //@ private represents minutes = my_minutes;
  
  private int my_seconds; //@ in seconds;
  //@ model int refinement_type Legal_Secs seconds;
  //@ private represents seconds = my_seconds;

  
  /*@ ensures \result == hours * MINS_IN_HOUR * SECS_IN_MIN + 
                         minutes * SECS_IN_MIN + seconds;
      pure helper model int totalSeconds();
   */
  


  //@ ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
  Clock(
      final int /*`@refinement_type Legal_Hours*/ the_hours,
      final int /*`@refinement_type Legal_Mins*/ the_minutes,
      final int /*`@refinement_type Legal_Secs*/ the_seconds
    ) {
    my_hours = the_hours;
    my_minutes = the_minutes;
    my_seconds = the_seconds;
  }
  
  //@ ensures \result == hours;
  /*@ pure helper */ int hours() {
    return my_hours;
  }
  
  //@ ensures \result == minutes;
  /*@ pure helper */ int minutes() {
    return my_minutes;
  }
  
  //@ ensures \result == seconds;
  /*@ pure helper */ int seconds() {
    return my_seconds;
  }
  
  //@ ensures \result == totalSeconds() > the_other_clock.totalSeconds();
  /*@ pure */ boolean later(final Clock the_other_clock) {
    return my_hours > the_other_clock.my_hours ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes > the_other_clock.my_minutes) ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes == the_other_clock.my_minutes &&
            my_seconds > the_other_clock.my_seconds);
  }
  
  //@ ensures \result == totalSeconds() < the_other_clock.totalSeconds();
  /*@ pure */ boolean earlier(final Clock the_other_clock) {
    return my_hours < the_other_clock.my_hours ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes < the_other_clock.my_minutes) ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes == the_other_clock.my_minutes &&
            my_seconds < the_other_clock.my_seconds);
  }

  //@ ensures hours == the_hours;
  void setHours(final int /*`@refinement_type Legal_Hours*/ the_hours) {
    my_hours = the_hours;
  }

  //@ ensures minutes == the_minutes;
  void setMinutes(final int /*`@refinement_type Legal_Mins*/ the_minutes) {
    my_minutes = the_minutes;
  }
  
  //@ ensures seconds == the_seconds;
  void setSeconds(final int /*`@refinement_type Legal_Secs*/ the_seconds) {
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
  //@helper
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