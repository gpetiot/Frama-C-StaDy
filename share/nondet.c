
#define __NONDET(TYPE,TYPENAME) \
TYPE* nondet_##TYPENAME##_val; \
static unsigned nondet_##TYPENAME##_cpt;	\
TYPE nondet_##TYPENAME() { \
  if(pathcrawler_dimension(nondet_##TYPENAME##_val) <= nondet_##TYPENAME##_cpt) { pathcrawler_assume_exception("nondet.c: Need more nondet values",0); } \
  return nondet_##TYPENAME##_val[nondet_##TYPENAME##_cpt++]; \
}

__NONDET(_Bool,bool)
__NONDET(char,char)
__NONDET(signed char,schar)
__NONDET(unsigned char,uchar)
__NONDET(signed short,sshort)
__NONDET(unsigned short,ushort)
__NONDET(signed int,sint)
__NONDET(unsigned int,uint)
__NONDET(signed long,slong)
__NONDET(unsigned long,ulong)
__NONDET(signed long long,slonglong)
__NONDET(unsigned long long,ulonglong)
__NONDET(float,float)
__NONDET(double,double)
//__NONDET(long double,longdouble)
