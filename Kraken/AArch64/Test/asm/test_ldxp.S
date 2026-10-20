# Undefined flags: n, z, c, v

// LDXP/LDAXP of a pair stored by STP (no STXP: a store exclusive may fail
// spuriously, which Kraken models as an undefined Bool, so its status is not
// comparable with native execution)
stp x1, x2, [sp, #-32]!
ldxp x3, x4, [sp]
ldaxp x5, x6, [sp]

// W pair: one 8-byte block, low word to the first register
stp w7, w8, [sp, #16]
add x9, sp, #16
ldxp w10, w11, [x9]
ldaxp w12, w13, [x9]
add sp, sp, #32
