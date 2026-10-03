/* Copyright (C) 2009-2025 AO MCST. */

.section ".init", "ax", @progbits
    /* Flag for prohibiting unaligned memory accesses */
    rrs %upsr, %r0
    ors %r0, (1<<2), %r0
    {
    rws %r0, %upsr
    nop 4
    }
