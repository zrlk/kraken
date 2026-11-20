/* Link script of `--host raw` units (`Scc/Test/elf.sh`): the text at
   address 0, so it starts on a 64 KiB granule; `.rodata`, then `.data` and
   `.bss`, each from the next granule; no `.comment` or `.note.*` sections
   (no build id). Entry `scc_rt_main`. The unit's own routine table
   (section `.scc_kabi`, 4 KiB) comes first in the writable segment, before
   `.data`. */
ENTRY(scc_rt_main)
SECTIONS
{
  . = 0;
  .text : { *(.text) *(.text.*) }
  . = ALIGN(65536);
  .rodata : { *(.rodata) *(.rodata.*) }
  . = ALIGN(65536);
  .scc_kabi : { *(.scc_kabi) }
  .data : { *(.data) }
  .bss : { *(.bss) }
  /DISCARD/ : { *(.comment) *(.note.*) }
}
