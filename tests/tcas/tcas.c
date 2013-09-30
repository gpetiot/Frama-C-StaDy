
int Cur_Vertical_Sep = 16684;
int High_Confidence = 32767;
int Two_of_Three_Reports_Valid;
int Own_Tracked_Alt;
int Own_Tracked_Alt_Rate = 450;
int Other_Tracked_Alt;
int Alt_Layer_Value;		
int Positive_RA_Alt_Thresh[4] = {16434,0,0,0};
int Up_Separation;
int Down_Separation;
int Other_RAC;
int Other_Capability = 0;
int Climb_Inhibit = 1;


int Own_Below_Threat() {
  return (Own_Tracked_Alt < Other_Tracked_Alt);
}

int Own_Above_Threat() {
  return (Other_Tracked_Alt < Own_Tracked_Alt);
}

int ALIM () {
  return Positive_RA_Alt_Thresh[Alt_Layer_Value];
}

int Inhibit_Biased_Climb () {
  return (Climb_Inhibit ? Up_Separation + 100  : Up_Separation);
}

int Non_Crossing_Biased_Climb() {
  int upward_preferred;
  int upward_crossing_situation;
  int result;
  
  upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
  if (upward_preferred) {
    result = !(Own_Below_Threat())
      || ((Own_Below_Threat()) && (!(Down_Separation >= ALIM())));
  }
  else {	
    result = Own_Above_Threat()
      && (Cur_Vertical_Sep >= 300 ) && (Up_Separation >= ALIM());
  }
  return result;
}

int Non_Crossing_Biased_Descend() {
  int upward_preferred;
  int upward_crossing_situation;
  int result;
  
  upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
  if (upward_preferred) {
    result = Own_Below_Threat()
      && (Cur_Vertical_Sep >= 300 ) && (Down_Separation >= ALIM());
  }
  else {
    result = !(Own_Above_Threat())
      || ((Own_Above_Threat()) && (Up_Separation >= ALIM()));
  }
  return result;
}



int alt_sep_test() {
  int enabled, tcas_equipped, intent_not_known;
  int need_upward_RA = 0;
  int need_downward_RA = 0;
  int alt_sep;
  
  enabled = High_Confidence
    && (Own_Tracked_Alt_Rate <= 600 ) && (Cur_Vertical_Sep > 600 );
  tcas_equipped = Other_Capability == 1 ;
  intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == 0;  
  alt_sep = 0;

  if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped)) {
    need_upward_RA = Non_Crossing_Biased_Climb() && Own_Below_Threat() ;
    need_downward_RA = Non_Crossing_Biased_Descend() && Own_Above_Threat();
    
    if(need_upward_RA && need_downward_RA)
      alt_sep = 0 ;
    else    
      if (need_upward_RA)
	alt_sep = 1 ;
      else if (need_downward_RA)
	alt_sep = 2 ;
      else
	alt_sep = 0 ;
  }
  
  return alt_sep;
}




/*@ requires 300 <= other_tracked_alt <= 1000;
  @ requires 300 <= own_tracked_alt <= 1000;
  @ requires 0 <= alt_layer_value < 4;
  @ requires 0 <= other_rac <= 2;
  @ requires 0 <= two_of_three_reports_valid <= 1;
  @
  @ behavior P1a :
  @   assumes up_separation >= Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes down_separation < Positive_RA_Alt_Thresh[alt_layer_value];
  @   ensures \result != 2;
  @ behavior P1b :
  @   assumes up_separation < Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes down_separation >= Positive_RA_Alt_Thresh[alt_layer_value];
  @   ensures \result != 1;
  @ behavior P2a :
  @   assumes up_separation < Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes down_separation < Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes up_separation > down_separation;
  @   ensures \result != 2;
  @ behavior P2b :
  @   assumes up_separation < Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes down_separation < Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes up_separation < down_separation;
  @   ensures \result != 1;
  @ behavior P3a :
  @   assumes up_separation >= Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes down_separation >= Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes own_tracked_alt > other_tracked_alt;
  @   ensures \result != 2;
  @ behavior P3b :
  @   assumes up_separation >= Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes down_separation >= Positive_RA_Alt_Thresh[alt_layer_value];
  @   assumes own_tracked_alt < other_tracked_alt;
  @   ensures \result != 1;
  @ behavior P4a :
  @   assumes own_tracked_alt > other_tracked_alt;
  @   ensures \result != 2;
  @ behavior P4b :
  @   assumes own_tracked_alt < other_tracked_alt;
  @   ensures \result != 1;
  @ behavior P5a :
  @   assumes up_separation > down_separation;
  @   ensures \result != 2;
  @ behavior P5b :
  @   assumes up_separation < down_separation;
  @   ensures \result != 1;
  @*/
int entry_point(int two_of_three_reports_valid,
		int own_tracked_alt,
		int other_tracked_alt,
		int alt_layer_value,
		int up_separation,
		int down_separation,
		int other_rac)
{
  Two_of_Three_Reports_Valid = two_of_three_reports_valid;
  Own_Tracked_Alt = own_tracked_alt;
  Other_Tracked_Alt = other_tracked_alt;
  Alt_Layer_Value = alt_layer_value;
  Up_Separation = up_separation;
  Down_Separation = down_separation;
  Other_RAC = other_rac;

  return alt_sep_test();
}
