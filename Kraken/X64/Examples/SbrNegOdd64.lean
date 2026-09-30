import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.SeparationMem

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
`.rodata`, sit in the program behind a `jmp` that skips them, so that the label
`ps_mask2` names their address.

We prove that the loop terminates without faulting, and that on exit the
array and the mask are still in place, separated from each other and from the
frame `R`. The machine keeps code and data in separate memories, so the
precondition owns the 16 bytes at `ps_mask2` in data memory, aligned as `xorps`
requires. The proof never needs their contents, which need not match the
`.byte` line.

The layout is a parameter. `ValidLayout` fixes only that labels take no bytes
and every other directive at least one, so the `jmp` can take any size and
`ps_mask2` can land at any address. `h_mask_aligned` restricts the theorem to
the layouts that align it to 16 bytes, as the assembler source does by putting
the constant in `SECTION_RODATA`, which `x86inc.asm` aligns to 16. For the
other layouts the theorem says nothing. The hypothesis is needed only at the
four `xorps`: without it the proof fails there and nowhere else.
`sbr_neg_odd_64_hyps_satisfiable`, at the end of the file, gives a layout, a
machine and a frame that meet every hypothesis at once, so the theorem is not
vacuous.

The proof has the shape of `ButterfliesBlocks.lean`: `sbr_table` gives the
assertion at each label (at `.loop`, the loop invariant), `sbr_var` is the
variant, and `MachineWP.cfg` with `cfg_cases` leaves one `vcgen` obligation per
block, each closed by `finish`.
-/

open Kraken.X64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option experimental.vcgen true

/-- The program: `ff_sbr_neg_odd_64_sse` from the object file without its
`ret`, with the mask it reads placed behind a `jmp`. -/
def sbr_neg_odd_64_prog : Program := parse("
start:
    jmp ff_sbr_neg_odd_64_sse
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

/-! ## The proof -/

/-- The spec table: the machine at each label, for a run that started on `d`
with the mask at `mask`. At `.loop` it is the loop invariant: `rsi` is the end
of the array, `rdi` is a multiple of 64 bytes into it, and the array and the
mask are in place. Control never reaches the mask's cell. -/
private abbrev sbr_table (d : MachineData) (mask : BitVec 64) (R : DataMem → Prop) :
    Label → MachineData → Prop
  | "start", s => s = d
  | "ff_sbr_neg_odd_64_sse", s => s = d
  | ".loop", s =>
      let j := (s.regs.get64 .rdi - d.regs.get64 .rdi).toNat
      s.regs.get64 .rsi = d.regs.get64 .rdi + 256#64 ∧ j < 256 ∧ j % 64 = 0 ∧
      s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (mask, 16)] ⋆ R
  | _, _ => False

/-- The variant: the bytes still to process at `.loop`; the entry runs once. -/
private abbrev sbr_var : Label → MachineData → Nat
  | ".loop", s => (s.regs.get64 .rsi - s.regs.get64 .rdi).toNat
  | _, _ => 2 ^ 64

variable [layout : _root_.Layout] [Executable.ValidLayout (layout sbr_neg_odd_64_prog)]

/-- The ambient code of the example: `sbr_neg_odd_64_prog`, laid out. -/
local instance sbr.env : CodeEnv := ⟨layout sbr_neg_odd_64_prog⟩

/-- The address of the mask: where the layout puts the label `ps_mask2`. -/
abbrev ps_mask2 : BitVec 64 := ((_root_.Executable.labels cenv).label "ps_mask2").toBitVec

theorem sbr_neg_odd_64_correct (d : MachineData)
    (h_z_aligned : isAligned 16 (d.regs.get64 .rdi) = true)
    (h_mask_aligned : isAligned 16 ps_mask2 = true)
    (R : DataMem → Prop)
    (h_mem : d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R) :
    ⦃ fun s => s = d ⦄
      sbr_neg_odd_64_prog
    ⦃ fun _ s => s.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (ps_mask2, 16)] ⋆ R ⦄ := by
  apply MachineWP.cfg (sbr_table d ps_mask2 R) sbr_var
  cfg_cases [sbr_neg_odd_64_prog]
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish

/-- `sbr_neg_odd_64_correct`, read at the machine as the baseline judgment. -/
theorem sbr_neg_odd_64_terminates_and_safe
    (s₀ : MachineData)
    (h_z_aligned : isAligned 16 s₀.regs.rdi.toBitVec)
    (h_mask_aligned : isAligned 16 ps_mask2)
    (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec, 256), (ps_mask2, 16)] ⋆ R) :
    Eventually (straightlineStep (layout sbr_neg_odd_64_prog))
      (fun s' => s'.1.dmem =⋆ Mem.Blocks [(s₀.regs.rdi.toBitVec, 256), (ps_mask2, 16)] ⋆ R)
      (s₀, Kraken.Layout.start Directive) :=
  Program.run_of_triple (sbr_neg_odd_64_correct s₀ h_z_aligned h_mask_aligned R h_mem) rfl

/-! ## The hypotheses can hold

`h_mask_aligned` holds only for some layouts. Here is one: the text starts at
0, labels take no bytes and every other directive takes 16, so `ps_mask2` is
16. With the array right behind the mask, all the hypotheses of
`sbr_neg_odd_64_correct` hold at once, so the theorem is not vacuous. -/

/-- A layout that puts `ps_mask2` at 16. -/
@[reducible] def sbr_wit_layout : _root_.Layout where
  start := 0
  size i := if (sbr_neg_odd_64_prog[i]?.map Directive.isLabel).getD false then 0 else 16

omit layout [Executable.ValidLayout (layout sbr_neg_odd_64_prog)] in
theorem sbr_wit_layout_valid : Executable.ValidLayout (sbr_wit_layout sbr_neg_odd_64_prog) where
  label_size i l z h := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    show (if (sbr_neg_odd_64_prog[i]?.map Directive.isLabel).getD false then 0 else 16) = 0
    simp [hd, Directive.isLabel]
  instr_size i d z h hnl := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d', hd, rfl, rfl⟩ := h
    have : d'.isLabel = false := by
      cases d' <;> simp_all [Directive.isLabel]
    show 0 < (if (sbr_neg_odd_64_prog[i]?.map Directive.isLabel).getD false then 0 else 16)
    simp [hd, this]
  no_wrap := by decide +kernel

omit layout [Executable.ValidLayout (layout sbr_neg_odd_64_prog)] in
/-- `ps_mask2` is 16 under `sbr_wit_layout`: it follows the label `start`
and the 16-byte `jmp`. -/
theorem sbr_wit_mask : @ps_mask2 sbr_wit_layout = 16#64 := by
  have h := Executable.label_addrOf (sbr_wit_layout sbr_neg_odd_64_prog) "ps_mask2" 2
    (by decide +kernel) (by decide +kernel)
  simp only [ps_mask2, h]
  decide +kernel

omit layout [Executable.ValidLayout (layout sbr_neg_odd_64_prog)] in
/-- Under `sbr_wit_layout`, a machine with the mask's 16 bytes at 16 and the
array's 256 bytes at 32 meets every hypothesis of `sbr_neg_odd_64_correct`. -/
theorem sbr_neg_odd_64_hyps_satisfiable :
    ∃ (d : MachineData) (R : DataMem → Prop),
      isAligned 16 (d.regs.get64 .rdi) = true ∧
      isAligned 16 (@ps_mask2 sbr_wit_layout) = true ∧
      d.dmem =⋆ Mem.Blocks [(d.regs.get64 .rdi, 256), (@ps_mask2 sbr_wit_layout, 16)] ⋆ R := by
  have hsplit := Mem.At_append_sep (List.replicate 16 (0 : UInt8)) (List.replicate 256 0) 16#64
    (by rw [List.length_replicate, List.length_replicate]; omega)
  simp only [List.length_replicate] at hsplit
  rw [show (16#64 + BitVec.ofNat 64 16 : BitVec 64) = 32#64 from rfl] at hsplit
  have h : ((List.replicate 16 (0 : UInt8) ++ List.replicate 256 0).At 16#64) =⋆
      Eq ((List.replicate 16 (0 : UInt8)).At 16#64) ⋆ Eq ((List.replicate 256 (0 : UInt8)).At 32#64) := by
    rw [← hsplit]
  have h1 := Mem.Block.sep_intro (len := 16) List.length_replicate (by decide) h
  rw [Std.ExtHashMap.sep_comm] at h1
  have h2 := Mem.Block.sep_intro (len := 256) List.length_replicate (by decide) h1
  generalize (List.replicate 16 (0 : UInt8) ++ List.replicate 256 0).At 16#64 = m at h2
  refine ⟨{ dmem := m, regs := { rdi := 32 } }, Std.ExtHashMap.emp, by dsimp only; decide,
    by rw [sbr_wit_mask]; rfl, ?_⟩
  rw [Std.ExtHashMap.sep_emp, sbr_wit_mask]
  exact h2

