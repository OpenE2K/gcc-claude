/* Copyright (C) 2009-2025 AO MCST. */

#include <stddef.h>
#include <inttypes.h>
#ifdef __linux__
# include <asm/e2k_syswork.h>
# include <asm/mas.h>
#else /* __linux__ */
# define MAS_DCACHE_LINE_FLUSH 0xf
#endif /* __linux__ */

void
__e2k_clear_cache (const void *base, const void *end)
{
#if __iset__ <= 2
  if (__builtin_cpu_is ("elbrus-v1") || __builtin_cpu_is ("elbrus-v2"))
    {
      /* На этих процессорах можно выполнить только через ядро
       * Подробности см. mcstbug #67069. Ядро воспринимает FLUSH_CMD_CACHES
       * только на процессорах elbrus-v1 и elbrus-v2. Из-за этого
       * нужно обязательно определять тип процессора в runtime, чтобы код,
       * собранный на elbrus-v2, смог работать на elbrus-v3 и выше */

# ifdef __linux__
#  ifdef __ptr128__
      /* Пока без защищённого режима (см. mcstbug #163928.3) */
      __builtin_abort ();
#  else /* __ptr128__ */
      icache_range_t s;
      long r;

      s.start = (size_t) base;
      s.end = (size_t) end;

      r = e2k_syswork (FLUSH_CMD_CACHES, &s, 1);
      if (r != 0)
        __builtin_abort ();
#  endif /* __ptr128__ */
# else /* __linux__ */
      /* Из "других" операционных систем у нас только QNX, а там поддержки
       * elbrus-v2 нет */
      __builtin_abort ();
# endif /* __linux__ */
    }
  else
#endif /* __iset__ */
    {
      /* На остальных процессорах вариант НЕ через ядро, а потому нужно всё делать
       * ручками. См. bug #622.2. Здесь мы не будем разбираться, запускаемся
       * мы с affinity, или нет, поэтому пойдём по варианту "flush во всех кэшах
       * во всех процессорах", т.к. он гарантированно нам сделает flush
       * кэша инструкций на всех процессорах */

      /* Инженеры обещают, что на новых процессорах значение уменьшаться не будет */
#define E2K_ICACHE_SET_SIZE 256
#define E2K_ICACHE_SET_MASK (E2K_ICACHE_SET_SIZE - 1)

      size_t addr;

#pragma no_asm_inline
      asm volatile ("wait st_c = 1" : : : "memory");

      for (addr = ((size_t)base) & ~E2K_ICACHE_SET_MASK;
           addr < (((size_t)end + E2K_ICACHE_SET_MASK) & ~E2K_ICACHE_SET_MASK);
           addr += E2K_ICACHE_SET_SIZE)
        {
#pragma no_asm_inline
          asm volatile ("std,2 [%1 + 0], mas=%2, %0"
                        :
                        : "r" ((uint64_t)0),
                          "r" ((uint64_t)addr),
                          "i" (MAS_DCACHE_LINE_FLUSH)
                        : "memory");
        }

#pragma no_asm_inline
      asm volatile ("wait fl_c = 1" : : : "memory");
    }
}
