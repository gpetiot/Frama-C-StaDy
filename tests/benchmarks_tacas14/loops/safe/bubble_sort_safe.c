
/*@ requires 0 <= size <= 4;
  @ requires \valid(item+(0..size-1));
  @ ensures \forall int x; 0 <= x < size-1 ==> item[x] <= item[x+1];
  @ behavior B:
  @  assumes \true;
  @*/
void bubblesort(int size, int item[])
{
  int a, b, t;

  /*@ loop invariant 1 <= a <= size;
    @ loop variant size-a;
    @*/
  for(a = 1; a < size; ++a)
    {
      /*@ loop invariant a-1 <= b <= size-1;
	@ loop invariant \forall int i; b <= i < size ==> item[i] >= item[b];
	@ loop variant b;
	@*/
      for(b = size-1; b >= a; --b)
	{

	  if (b-1 < size && b < size)
	    {
	      //@ ensures item[b-1] <= item[b];
	      if(item[ b - 1] > item[ b ])
		/*@ ensures item[b-1] == \old(item[b]);
		  @ ensures item[b] == \old(item[b-1]);
		  @*/
		{
		  t = item[ b - 1];
		  item[ b - 1] = item[ b ];
		  item[ b ] = t;
		}
	    }
	}
    }
}


