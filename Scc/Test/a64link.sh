# Sourced by Scc/Test/run.sh, Scc/Test/certify.sh and Scc/Test/elf.sh: the AArch64 link, in one place.
#
# Every arm executable is built from its assembler text with clang and lld (`A64_CC`). The proofs of
# the programs that take their thread id or spawn (wake, hello: `Spike/Test/WakeLinkedA64*.lean`,
# `Spike/Test/HelloLinkedA64*.lean`) are stated with `.text` at `0x210550` (their `hlo`,
# `Spike.Lib.A64.WakePh.lo`), so their executables are linked with the code base pinned there
# (`A64_PIN`). `.text` alone is not enough: lld then moves `.rodata` and the build-id note above the
# code. So the note and `.rodata` are pinned at the bases of lld's default script too. With the three
# pins, lld writes the default script's three segments (note and `.rodata`, then `.text`, then the
# data); for a program whose default `.text` is already at `0x210550` (wake) the executable is the
# default link, byte for byte. `.text` at `0x210550` leaves `0x210550 - 0x2001b8` bytes (about
# 66 KiB) for `.rodata`; a larger `.rodata` makes the pinned link fail.
#
# The programs that are not wake or hello have theorems at every layout passing the placement check
# (`Scc.Lower.Accepted1`, hello1), and are linked at lld's default (`A64_PIN_ALL=0`). With
# `A64_PIN_ALL=1` every arm executable is pinned.
#
# x86-64 needs no pin: GNU ld puts .text at 0x401000 whatever the size of .rodata.

A64_CC="clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static -fuse-ld=lld"
A64_PIN="-Wl,--section-start=.note.gnu.build-id=0x200190"
A64_PIN="$A64_PIN,--section-start=.rodata=0x2001b8,--section-start=.text=0x210550"
A64_PIN_ALL=0

# a64_flags PINNED: the link flags beyond `A64_CC`, for a program whose proof pins the code base
# (PINNED = 1: wake, hello) or not (0).
a64_flags() {
  if [ "$1" = 1 ] || [ "$A64_PIN_ALL" = 1 ]; then echo "$A64_PIN"; fi
}
