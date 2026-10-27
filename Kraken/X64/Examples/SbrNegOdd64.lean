module

public import Kraken.StateCfg
public import Kraken.SeparationMem
import Kraken.X64.Parser

/-!
# `ff_sbr_neg_odd_64_sse`: an SSE loop that reads a constant

FFmpeg's `sbr_neg_odd_64` flips the sign of the odd-indexed floats of a
64-float array `z` (`libavcodec/sbrdsp.c`). Its SSE version
(`libavcodec/x86/sbrdsp.asm`) walks the 256 bytes in steps of 64: it loads
four 16-byte chunks, xors each with the constant `ps_mask2`, which has the
sign bit set in lanes 1 and 3, and stores them back.

The program below is the routine's machine code, disassembled from the object
file, in the parser's AT&T syntax. There are two changes. The final `ret` is
left off. The 16 bytes of `ps_mask2`, which the object file keeps in
`.rodata`, sit in the program behind a `jmp` that skips them and an
`.align 16`, so that the label `ps_mask2` names their address.

We prove that the loop terminates without faulting, and that on exit the
array and the mask are still in place, separated from each other and from the
frame `R`. The machine keeps code and data in separate memories, so the
precondition owns the 16 bytes at `ps_mask2` in data memory. The proof never
needs their contents, which need not match the `.byte` line.

`xorps` requires its memory operand 16-byte aligned. `Host` does not promise
that an `.align 16` directive ends at a multiple of 16, so the alignment of
`ps_mask2` is a hypothesis (`h_mask_aligned`); the old layout model proved it
from the layout's validity.
-/

open Kraken.X64.Parser
open Std.WP
open Lean.Order
open scoped Program.WP

set_option experimental.vcgen true

namespace Kraken.Examples.SbrNegOdd64

/-- The program: `ff_sbr_neg_odd_64_sse` from the object file, without its
`ret`, with the mask it reads placed behind a `jmp` and aligned to 16 bytes. -/
def sbr_neg_odd_64_prog : Program := parse("
start:
    jmp ff_sbr_neg_odd_64_sse
    .align 16
ps_mask2:
    .byte 0, 0, 0, 0, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0, 0x80
ff_sbr_neg_odd_64_sse:
    lea 0x100(%rdi),%rsi
.loop:
    movaps (%rdi),%xmm0
    movaps 0x10(%rdi),%xmm1
    movaps 0x20(%rdi),%xmm2
    movaps 0x30(%rdi),%xmm3
    xorps ps_mask2(%rip),%xmm0
    xorps ps_mask2(%rip),%xmm1
    xorps ps_mask2(%rip),%xmm2
    xorps ps_mask2(%rip),%xmm3
    movaps %xmm0,(%rdi)
    movaps %xmm1,0x10(%rdi)
    movaps %xmm2,0x20(%rdi)
    movaps %xmm3,0x30(%rdi)
    add $0x40,%rdi
    cmp %rsi,%rdi
    jne .loop
")

/-- The address of the mask. -/
abbrev ps_mask2 [Host] : BitVec 64 := (label "ps_mask2").toBitVec

theorem sbr_neg_odd_64_spec [Host] [FunDecls] (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_mask_aligned : isAligned 16 ps_mask2 = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R) :
    WP.wp sbr_neg_odd_64_prog
      (fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R)
      (fun _ _ => False) d := by
  refine Program.WP.cfg
    (fun b s =>
      match b with
      | .entry | .label "start" | .label "ff_sbr_neg_odd_64_sse" => s = d
      | .label ".loop" =>
        let j := (s.regs.get64 .rdi - d.regs.get64 .rdi).toNat
        s.regs.get64 .rsi = d.regs.get64 .rdi + 256#64 ∧ j < 256 ∧ j % 64 = 0
          ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
          ∧ s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R
      | .exit => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R
      | _ => False)
    (fun l s => match l with
      | ".loop" => (s.regs.get64 .rsi - s.regs.get64 .rdi).toNat
      | _ => 2 ^ 64) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- `sbr_neg_odd_64_spec`, read at the machine: from the program's first
directive, the run reaches the program's end with the array and the mask in
place. The mask's alignment is assumed (`h_mask_aligned`) until `Host` gets an
alignment field for `.align`. -/
theorem sbr_neg_odd_64_terminates_and_safe [Host] [FunDecls] [he : Embeds sbr_neg_odd_64_prog]
    (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_mask_aligned : isAligned 16 ps_mask2 = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R) :
    Eventually (step1 Host.exe)
      (fun u => u.data.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R)
      ⟨d, he.embedding.startAddr⟩ :=
  Program.step1_of_wp (sbr_neg_odd_64_spec d h_z_aligned h_mask_aligned R h_mem)
    (fun _ _ h => h) (fun _ h => h.elim)

end Kraken.Examples.SbrNegOdd64
