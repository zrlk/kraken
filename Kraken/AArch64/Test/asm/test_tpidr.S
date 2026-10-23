# Undefined flags: n, z, c, v
// TPIDR_EL0 (the thread pointer) is a private register: MSR writes it, MRS
// reads it back; XZR as either operand writes 0 / discards the value.
msr tpidr_el0, x1
mrs x2, tpidr_el0
add x3, x2, #1
msr tpidr_el0, x3
mrs x4, tpidr_el0
mrs xzr, tpidr_el0
msr tpidr_el0, xzr
mrs x5, tpidr_el0
