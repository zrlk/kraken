module

public import Kraken.StateCfg
public import Kraken.SeparationMem
public import Kraken.X64.WP.Image
public import Kraken.X64.WP.HostWitness
import Kraken.X64.Parser
import all Kraken.SeparationMem

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
array and the program's image are still in place, separated from each other and
from the frame `R`. The machine keeps code and data in separate memories; the
precondition says that the image is loaded into data memory (`Host.Image`),
and the proof carves the mask's cell out of it (`Host.Image.split`), so the
bytes the loop reads are the ones on the `.byte` line.
`sbr_neg_odd_64_spec_blocks` is the earlier form, which owns the 16 bytes at
`ps_mask2` as a block with untracked contents.

`xorps` requires its memory operand 16-byte aligned. The label `ps_mask2`
follows an `.align 16`, so `Host.label_aligned` gives its alignment
(`ps_mask2_aligned`).
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

/-- `ps_mask2` is 16-byte aligned wherever the program is embedded: it follows the
`.align 16` at index 2. -/
theorem ps_mask2_aligned [Host] [he : Embeds sbr_neg_odd_64_prog] : isAligned 16 ps_mask2 = true :=
  Host.label_aligned he.embedding.isInfixAt (i := 2) rfl rfl

theorem sbr_neg_odd_64_spec_of_aligned [Host] [FunDecls] (d : MachineData)
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

/-- The mask with the array's blocks, as an owned 16-byte block whose contents are not
tracked. -/
theorem sbr_neg_odd_64_spec_blocks [Host] [FunDecls] (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R) :
    WP.wp sbr_neg_odd_64_prog
      (fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R)
      (fun _ _ => False) d := by
  -- `Program.wp` quantifies over the embeddings; under one, the mask is aligned.
  show Program.wp _ _ _ d
  rw [Program.wp_eq]
  intro he
  exact Program.wp_eq.mp (sbr_neg_odd_64_spec_of_aligned d h_z_aligned ps_mask2_aligned R h_mem)

/-- The bytes of the mask, as written in the program. -/
def mask_bytes : List UInt8 := [0, 0, 0, 0, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0, 0x80]

theorem mask_bytes_length : mask_bytes.length = 16 := rfl

attribute [local grind =] mask_bytes_length

/-- The loop with the mask's bytes owned, ahead of the array's block. -/
theorem sbr_neg_odd_64_spec_of_bytes [Host] [FunDecls] (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_mask_aligned : isAligned 16 ps_mask2 = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Bytes ps_mask2 mask_bytes ⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ R) :
    WP.wp sbr_neg_odd_64_prog
      (fun _ s => s.dmem =⋆ Mem.Bytes ps_mask2 mask_bytes ⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ R)
      (fun _ _ => False) d := by
  refine Program.WP.cfg
    (fun b s =>
      match b with
      | .entry | .label "start" | .label "ff_sbr_neg_odd_64_sse" => s = d
      | .label ".loop" =>
        let j := (s.regs.get64 .rdi - d.regs.get64 .rdi).toNat
        s.regs.get64 .rsi = d.regs.get64 .rdi + 256#64 ∧ j < 256 ∧ j % 64 = 0
          ∧ s.regs.get64 .rsp = d.regs.get64 .rsp
          ∧ s.dmem =⋆ Mem.Bytes ps_mask2 mask_bytes ⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ R
      | .exit => s.dmem =⋆ Mem.Bytes ps_mask2 mask_bytes ⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ R
      | _ => False)
    (fun l s => match l with
      | ".loop" => (s.regs.get64 .rsi - s.regs.get64 .rdi).toNat
      | _ => 2 ^ 64) ?_ rfl
  cfg_cases
  all_goals kvcgen64 with finish

/-- The image, with the mask carved out. -/
theorem image_split [Host] [he : Embeds sbr_neg_odd_64_prog] (B R : DataMem → Prop) (m : DataMem) :
    (m =⋆ B ⋆ Host.Image ⋆ R) ↔
      (m =⋆ Mem.Bytes ps_mask2 mask_bytes ⋆ B ⋆ (Host.ImageExcept "ps_mask2" mask_bytes ⋆ R)) := by
  rw [Std.ExtHashMap.sep_assoc, Host.Image.split he.embedding.isInfixAt (i := 3) rfl rfl,
    Std.ExtHashMap.sep_comm_l, ← Std.ExtHashMap.sep_assoc]
  exact Iff.rfl

theorem sbr_neg_odd_64_spec [Host] [FunDecls] (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ Host.Image ⋆ R) :
    WP.wp sbr_neg_odd_64_prog
      (fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ Host.Image ⋆ R)
      (fun _ _ => False) d := by
  -- `Program.wp` quantifies over the embeddings; under one, the mask is aligned and is a
  -- cell of the image.
  show Program.wp _ _ _ d
  rw [Program.wp_eq]
  intro he
  have h := sbr_neg_odd_64_spec_of_bytes d h_z_aligned ps_mask2_aligned _
    ((image_split _ R _).mp h_mem)
  exact Program.wp_eq.mp (Program.wp_mono (fun _ h => (image_split _ R _).mpr h) (fun _ h => h) h)

/-- `sbr_neg_odd_64_spec`, read at the machine: from the program's first
directive, the run reaches the program's end with the array and the image in
place. -/
theorem sbr_neg_odd_64_terminates_and_safe [Host] [FunDecls] [he : Embeds sbr_neg_odd_64_prog]
    (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ Host.Image ⋆ R) :
    Eventually (step1 Host.exe)
      (fun u => u.data.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ Host.Image ⋆ R)
      ⟨d, he.embedding.startAddr⟩ :=
  Program.step1_of_wp (sbr_neg_odd_64_spec d h_z_aligned R h_mem)
    (fun _ _ h => h) (fun _ h => h.elim)

/-! ## The hypotheses can hold at once

The theorems above assume a `Host`. `witnessHost` is one: it places the program at
`0x1000` with sizes the encodings could have, so the mask lands at `0x1010`.
`Host.ofChecks` checks the host's conditions by evaluation. -/

/-- Sizes for the 23 directives of `sbr_neg_odd_64_prog`. -/
def witnessSizes : List Nat := [0, 2, 14, 0, 16, 0, 7, 0, 3, 4, 4, 4, 7, 7, 7, 7, 3, 4, 4, 4, 4, 3, 2]

/-- The program at `0x1000`, laid out by `witnessSizes`. -/
@[instance_reducible] def witnessLayout : _root_.Layout := {start := 0x1000, size := fun i => witnessSizes.getD i 0}

/-- A host for `sbr_neg_odd_64_prog`. -/
@[instance_reducible] def witnessHost : Host :=
  Host.ofChecks sbr_neg_odd_64_prog witnessLayout (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- Under `witnessHost`, the image is the mask at `0x1010`. -/
theorem witness_dataCells : @Host.dataCells witnessHost = [(0x1010#64, mask_bytes)] := by
  decide +kernel

/-- There are a host, an embedding, and a machine that meet every hypothesis of
`sbr_neg_odd_64_spec`: the mask at `0x1010`, the array right after it, nothing else. -/
theorem sbr_neg_odd_64_hyps_satisfiable :
    ∃ (_ : Host), ∃ (_ : Embeds sbr_neg_odd_64_prog), ∃ (d : MachineData) (R : DataMem → Prop),
      isAligned 16 (d.regs.get64 .rdi) = true ∧
      d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256)] ⋆ Host.Image ⋆ R := by
  have hsplit := Mem.At_append_sep mask_bytes (List.replicate 256 (0 : UInt8)) 0x1010#64
    (by rw [List.length_replicate, mask_bytes_length]; omega)
  rw [mask_bytes_length, show (0x1010#64 + BitVec.ofNat 64 16 : BitVec 64) = 0x1020#64 from rfl]
    at hsplit
  have h : ((mask_bytes ++ List.replicate 256 (0 : UInt8)).At 0x1010#64) =⋆
      Eq (mask_bytes.At 0x1010#64) ⋆ Eq ((List.replicate 256 (0 : UInt8)).At 0x1020#64) := by
    rw [← hsplit]
  rw [Std.ExtHashMap.sep_comm] at h
  have h1 := Mem.Block.sep_intro (len := 256) List.length_replicate (by decide) h
  generalize (mask_bytes ++ List.replicate 256 (0 : UInt8)).At 0x1010#64 = m at h1
  refine ⟨witnessHost, @Embeds.mk witnessHost _ (@Embedding.mk witnessHost _ 0 (List.prefix_refl _)),
    { dmem := m, regs := { rdi := 0x1020 } }, Std.ExtHashMap.emp,
    by change isAligned 16 (0x1020#64) = true; decide, ?_⟩
  rw [Std.ExtHashMap.sep_emp]
  show m =⋆ Mem.Block 0x1020#64 256 ⋆ Mem.Cells (@Host.dataCells witnessHost)
  rw [witness_dataCells]
  exact h1

end Kraken.Examples.SbrNegOdd64
