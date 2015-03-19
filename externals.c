#define mp_bitcnt_t unsigned long long
struct __anonstruct___mpz_struct_1 {
   int _mp_alloc ;
   int _mp_size ;
   unsigned long *_mp_d ;
};
typedef struct __anonstruct___mpz_struct_1 __mpz_struct;
typedef __mpz_struct ( __attribute__((__FC_BUILTIN__)) mpz_t)[1];

unsigned long int __gmpz_get_ui(mpz_t x){return 0;}
signed long int __gmpz_get_si(mpz_t x){return 0;}
int __gmpz_cmp_ui(mpz_t x, unsigned long int y){return 0;}
int __gmpz_cmp_si(mpz_t x, signed long int y){return 0;}
int __gmpz_cmp(mpz_t x, mpz_t y){return 0;}
void __gmpz_clear(mpz_t x){}
void __gmpz_init(mpz_t x){}
void __gmpz_init_set(mpz_t x, mpz_t y){}
void __gmpz_init_set_ui(mpz_t x, unsigned long int y){}
void __gmpz_init_set_si(mpz_t x, signed long int y){}
void __gmpz_init_set_str(mpz_t x, const char* y, int z){}
void __gmpz_set(mpz_t x, mpz_t y){}
void __gmpz_abs(mpz_t x, mpz_t y){}
void __gmpz_add(mpz_t x, const mpz_t y, const mpz_t z){}
void __gmpz_add_ui(mpz_t x, const mpz_t y, unsigned long int z){}
void __gmpz_sub(mpz_t x, const mpz_t y, const mpz_t z){}
void __gmpz_sub_ui(mpz_t x, const mpz_t y, unsigned long int z){}
void __gmpz_ui_sub(mpz_t x, unsigned long int y, const mpz_t z){}
void __gmpz_mul(mpz_t x, const mpz_t y, const mpz_t z){}
void __gmpz_mul_si(mpz_t x, const mpz_t y, long int z){}
void __gmpz_mul_ui(mpz_t x, const mpz_t y, unsigned long int z){}
void __gmpz_tdiv_q(mpz_t x, const mpz_t y, const mpz_t z){}
void __gmpz_tdiv_q_ui(mpz_t x, const mpz_t y, unsigned long int z){}
void __gmpz_tdiv_r(mpz_t x, const mpz_t y, const mpz_t z){}
void __gmpz_tdiv_r_ui(mpz_t x, const mpz_t y, unsigned long int z){}
void __gmpz_mul_2exp(mpz_t rop, const mpz_t op1, mp_bitcnt_t op2){}
void __gmpz_fdiv_q_2exp(mpz_t q, const mpz_t n, mp_bitcnt_t b){}
int pathcrawler_assert_exception(char* x,int y){return 0;}
int pathcrawler_dimension(void* x){return 0;}
void pathcrawler_to_framac(char* x){}
int pathcrawler_assume_exception(char* x,int y){return 0;}
void* malloc(unsigned long x){return 0;}
void free(void* x){}
