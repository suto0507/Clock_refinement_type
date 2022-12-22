public class Clock {
  
  public static final int SECS_IN_MIN = 60;
  
  public static final int MINS_IN_HOUR = 60;
  
  public static final int HOURS_IN_DAY = 24;
  
  
  private int my_hours; //@ in hours;
  //@ public model int hours;
  //@ private represents hours = my_hours;
  
  private int my_minutes; //@ in minutes;
  //@ public model int minutes;
  //@ private represents minutes = my_minutes;
  
  private int my_seconds; //@ in seconds;
  //@ public model int seconds;
  //@ private represents seconds = my_seconds;

  
  /*@ ensures \result <==> 0 <= the_hours < HOURS_IN_DAY &&
                           0 <= the_minutes < MINS_IN_HOUR && 
                           0 <= the_seconds < SECS_IN_MIN;
      public static pure heap_free helper model boolean legalTime(int the_hours, int the_minutes, int the_seconds);
   */
  
  /*@ ensures \result == hours * MINS_IN_HOUR * SECS_IN_MIN + 
                         minutes * SECS_IN_MIN + seconds;
      public pure helper model int totalSeconds();
   */
  

  //@ public invariant legalTime(hours, minutes, seconds);

  //@ requires legalTime(the_hours, the_minutes, the_seconds);
  //@ ensures hours == the_hours && minutes == the_minutes && seconds == the_seconds;
  public Clock(final int the_hours, final int the_minutes, final int the_seconds) {
    my_hours = the_hours;
    my_minutes = the_minutes;
    my_seconds = the_seconds;
  }
  
  //@ ensures \result == hours;
  public /*@ pure helper */ int hours() {
    return my_hours;
  }
  
  //@ ensures \result == minutes;
  public /*@ pure helper */ int minutes() {
    return my_minutes;
  }
  
  //@ ensures \result == seconds;
  public /*@ pure helper */ int seconds() {
    return my_seconds;
  }
  
  //@ ensures \result <==> totalSeconds() > the_other_clock.totalSeconds();
  public /*@ pure */ boolean later(final Clock the_other_clock) {
    return my_hours > the_other_clock.my_hours ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes > the_other_clock.my_minutes) ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes == the_other_clock.my_minutes &&
            my_seconds > the_other_clock.my_seconds);
  }
  
  //@ ensures \result <==> totalSeconds() < the_other_clock.totalSeconds();
  public /*@ pure */ boolean earlier(final Clock the_other_clock) {
    return my_hours < the_other_clock.my_hours ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes < the_other_clock.my_minutes) ||
           (my_hours == the_other_clock.my_hours &&
            my_minutes == the_other_clock.my_minutes &&
            my_seconds < the_other_clock.my_seconds);
  }

  //@ requires 0 <= the_hours < HOURS_IN_DAY;
  //@ modifies hours;
  //@ ensures hours == the_hours;
  //@ signals_only \nothing;
  protected void setHours(final int the_hours) {
    my_hours = the_hours;
  }

  //@ requires 0 <= the_minutes < MINS_IN_HOUR;
  //@ modifies minutes;
  //@ ensures minutes == the_minutes;
  //@ signals_only \nothing;
  protected void setMinutes(final int the_minutes) {
    my_minutes = the_minutes;
  }
  
  //@ requires 0 <= the_seconds < SECS_IN_MIN;
  //@ modifies seconds;
  //@ ensures seconds == the_seconds;
  //@ signals_only \nothing;
  protected void setSeconds(final int the_seconds) {
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
  public void tick() {
    my_seconds += 1;
    
    if (my_seconds >= SECS_IN_MIN) {
      my_minutes += 1;
      my_seconds = 0;
    }
    
    if (my_minutes >= MINS_IN_HOUR) {
      my_hours += 1;
      my_minutes = 0;
    }
    
    if (my_hours >= HOURS_IN_DAY) {
      my_hours = 0;
    }
  }
}