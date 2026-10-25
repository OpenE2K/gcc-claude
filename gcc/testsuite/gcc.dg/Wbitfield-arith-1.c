/* -Wbitfield-arith: arithmetic on a bit-field wider than int but narrower
   than its declared type wraps at the field's width in C, where lcc,
   clang and C++ compute it in the declared type; warn where the result
   is widened.  */
/* { dg-do compile } */
/* { dg-options "-Wbitfield-arith -Wno-int-to-pointer-cast" } */

typedef unsigned long long u64;
struct s { u64 : 3; u64 ip : 45; u64 a : 20; u64 b : 32; long long pfn : 36; };

u64 f1 (struct s *p) { return p->ip << 3; }	/* { dg-warning "'<<' on a 45-bit bit-field" } */
u64 f2 (struct s *p) { return ~p->ip; }		/* { dg-warning "'~' on a 45-bit bit-field" } */
u64 f3 (struct s *p) { return p->ip + 1; }	/* { dg-warning "'\\+' on a 45-bit bit-field" } */
int f4 (struct s *p) { return (p->ip << 3) > 0x100000000000ULL; } /* { dg-warning "'<<' on a 45-bit bit-field" } */
void *f5 (struct s *p) { return (void *) (p->pfn << 12); } /* { dg-warning "'<<' on a 36-bit bit-field" } */
double f6 (struct s *p) { return -p->ip; }	/* { dg-warning "'unary -' on a 45-bit bit-field" } */
u64 f7 (struct s *p, u64 q) { return (p->ip << 3) == q; } /* { dg-warning "'<<' on a 45-bit bit-field" } */

/* The same result either way.  */
u64 g1 (struct s *p) { return (u64) p->ip << 3; }
void g2 (struct s *p) { p->ip = p->ip + 1; p->ip <<= 2; }
u64 g3 (struct s *p) { return p->a << 16; }	/* 20 bits: int in lcc too.  */
u64 g4 (struct s *p) { return p->b << 4; }	/* 32 bits: unsigned int.  */
u64 g5 (struct s *p) { return (p->ip << 3) & 0xfff; }
unsigned g6 (struct s *p) { return p->ip << 3; }
u64 g7 (struct s *p) { return p->ip; }
u64 g8 (struct s *p) { return p->ip >> 3; }
int g9 (struct s *p) { return p->ip > 0x100000000000ULL; }
