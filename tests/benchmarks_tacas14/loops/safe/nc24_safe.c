
#include <string.h>

int bar(char *x)
{
  return __VERIFIER_nondet_int();
}

int foo(int * x){
  *x = __VERIFIER_nondet_int();
  return *x;
}


/*@ requires \valid(x+(0..999));
  @ requires \valid(nondet_ret+(0..999));
  @ requires \valid(nondet_tmp_cnt+(0.999));
  @*/
int f(char* x, int* nondet_ret, int* nondet_tmp_cnt){
  int i,j,ret,offset, tmp_cnt, tel_data,klen;
  int nondet_ret_cpt = 0;
  int nondet_tmp_cnt_cpt = 0;

   
  for (i= 0; i < 1000; ++i) {

    ret = nondet_ret[nondet_ret_cpt++];
    if (ret != 0)
      return -1;

    tmp_cnt = nondet_tmp_cnt[nondet_tmp_cnt_cpt++];

    if (tmp_cnt < 0)
      return -1;
      
      
    for ( offset = 0; offset < tmp_cnt; offset++ ) {
      ret = foo(&tel_data ) ;
      if ( ( ret == 0 ) || ( ret == 1 ) )
	return 1 ;
      else if ( ret == -1 )
	continue ;

         
      for ( j = 0; x[j] != 0; j++ )
	if ( x[i] == 1)
	  memmove( &x[i], &x[i + 1], (1001) - ( i + 1 ) )  ;

            
      ret = bar( x) ;
         
      if ( ret != -1 )
	continue ;

         
      klen = strlen(x ) ;
         
      if ( klen > 20 )
	x[i]=0;
             
      else if ( klen > 0 )
	x[i] =  -1;
    }
  }
  //@ assert(offset>=0 && offset<=1000);
  return 1;
}

