# Undefined flags: n, z, c, v

// CASP on a stack pair: a failing compare (registers get memory), then a
// succeeding one (memory gets the new pair), in every kind and both widths
stp x1, x2, [sp, #-32]!
mov x4, x1
mov x5, x2
add x4, x4, #1
casp x4, x5, x6, x7, [sp]
caspa x4, x5, x8, x9, [sp]
ldp x10, x11, [sp]
caspl x10, x11, x12, x13, [sp]
ldp x14, x15, [sp]
stp w3, w3, [sp, #16]
mov w16, w3
mov w17, w3
add x22, sp, #16
caspal w16, w17, w18, w19, [x22]
ldp w20, w21, [sp, #16]
add sp, sp, #32
// x22 held a stack address, which differs between QEMU and Kraken
mov x22, xzr
