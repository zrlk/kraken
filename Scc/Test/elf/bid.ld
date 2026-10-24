/* As ins.ld, with the build-id note before .text, which is 16-aligned (Link.wfB). */
SECTIONS {
  .text : ALIGN(16) { *(.text .text.*) }
  .rodata : { *(.rodata .rodata.*) }
} INSERT AFTER .note.gnu.build-id;
