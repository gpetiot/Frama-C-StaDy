
/* run.config
STDOPT: +"-main alt_sep_test -stady -stady-msg-key generated-c,generated-pl -then -report"
*/


int Cur_Vertical_Sep;// = 16684;
int High_Confidence;// = 32767;
int Two_of_Three_Reports_Valid;
int Own_Tracked_Alt;
int Own_Tracked_Alt_Rate;// = 450;
int Other_Tracked_Alt;
int Alt_Layer_Value;		
int* Positive_RA_Alt_Thresh;//[4];// = {16434,0,0,0};
int Up_Separation;
int Down_Separation;
int Other_RAC;
int Other_Capability;// = 0;
int Climb_Inhibit;// = 1;


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



/*@ requires 300 <= Other_Tracked_Alt <= 1000;
  @ requires 300 <= Own_Tracked_Alt <= 1000;
  @ requires 0 <= Alt_Layer_Value < 4;
  @ requires 0 <= Other_RAC <= 2;
  @ requires 0 <= Two_of_Three_Reports_Valid <= 1;
  @ requires Other_Capability == 0;
  @ requires Climb_Inhibit == 1;
  @ requires Cur_Vertical_Sep == 16684;
  @ requires High_Confidence == 32464;
  @ requires Own_Tracked_Alt_Rate == 450;
  @ requires \valid(Positive_RA_Alt_Thresh+(0..3));
  @ requires Positive_RA_Alt_Thresh[0] == 16434;
  @ requires Positive_RA_Alt_Thresh[1] == 0;
  @ requires Positive_RA_Alt_Thresh[2] == 0;
  @ requires Positive_RA_Alt_Thresh[3] == 0;
  @
  @ behavior P1a :
  @   assumes Up_Separation >= Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Down_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   ensures \result != 2;
  @ behavior P1b :
  @   assumes Up_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Down_Separation >= Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   ensures \result != 1;
  @ behavior P2a :
  @   assumes Up_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Down_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Up_Separation > Down_Separation;
  @   ensures \result != 2;
  @ behavior P2b :
  @   assumes Up_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Down_Separation < Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Up_Separation < Down_Separation;
  @   ensures \result != 1;
  @ behavior P3a :
  @   assumes Up_Separation >= Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Down_Separation >= Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Own_Tracked_Alt > Other_Tracked_Alt;
  @   ensures \result != 2;
  @ behavior P3b :
  @   assumes Up_Separation >= Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Down_Separation >= Positive_RA_Alt_Thresh[Alt_Layer_Value];
  @   assumes Own_Tracked_Alt < Other_Tracked_Alt;
  @   ensures \result != 1;
  @ behavior P4a :
  @   assumes Own_Tracked_Alt > Other_Tracked_Alt;
  @   ensures \result != 2;
  @ behavior P4b :
  @   assumes Own_Tracked_Alt < Other_Tracked_Alt;
  @   ensures \result != 1;
  @ behavior P5a :
  @   assumes Up_Separation > Down_Separation;
  @   ensures \result != 2;
  @ behavior P5b :
  @   assumes Up_Separation < Down_Separation;
  @   ensures \result != 1;
  @*/
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
