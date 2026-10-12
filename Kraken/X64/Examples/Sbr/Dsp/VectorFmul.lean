import Kraken.X64.Examples.Sbr.Dsp.FloatDspCommon

/-!
# `ff_vector_fmul_sse` / `ff_vector_fmul_avx` as `ProcSpec`s

`vector_fmul(dst, src0, src1, len)` (`libavutil/x86/float_dsp.asm`) sets
`dst[i] = src0[i] * src1[i]` for `i < len`, 64 bytes per iteration, from the end
down: `rcx = 4 len - 64` (`lea -0x40(,%ecx,4),%rcx`, a 32-bit address computation
zero-extended), then `sub $0x40,%rcx; jge`.

The texts are those of the object (`float_dsp.o`), the alignment padding after the
`lea` written as a sized `nop`, the final `rep ret` of the SSE variant written
`ret`. The SSE loop body is cut by a free label between its two store pairs, so
that no load follows a store within a block (see `FloatDspCommon.lean`).
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open Kraken.Examples.Sbr.FloatDsp
open scoped Kraken.LeafLemmas.Offset
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.VectorFmul

/-- `ff_vector_fmul_sse` from the object. -/
def bodySse : Program := parse("
ff_vector_fmul_sse:
    lea -0x40(,%ecx,4),%rcx
    nop 7
ff_vector_fmul_sse.loop:
    movaps (%rsi,%rcx),%xmm0
    movaps 0x10(%rcx,%rsi),%xmm1
    mulps (%rdx,%rcx),%xmm0
    mulps 0x10(%rcx,%rdx),%xmm1
    movaps %xmm0,(%rdi,%rcx)
    movaps %xmm1,0x10(%rcx,%rdi)
ff_vector_fmul_sse.loop2:
    movaps 0x20(%rcx,%rsi),%xmm0
    movaps 0x30(%rcx,%rsi),%xmm1
    mulps 0x20(%rcx,%rdx),%xmm0
    mulps 0x30(%rcx,%rdx),%xmm1
    movaps %xmm0,0x20(%rcx,%rdi)
    movaps %xmm1,0x30(%rcx,%rdi)
    sub $0x40,%rcx
    jge ff_vector_fmul_sse.loop
ff_vector_fmul_sse.done:
    ret
")

/-- `ff_vector_fmul_avx` from the object. -/
def bodyAvx : Program := parse("
ff_vector_fmul_avx:
    lea -0x40(,%ecx,4),%rcx
    nop 7
ff_vector_fmul_avx.loop:
    vmovaps (%rsi,%rcx),%ymm0
    vmovaps 0x20(%rcx,%rsi),%ymm1
    vmulps (%rdx,%rcx),%ymm0,%ymm0
    vmulps 0x20(%rcx,%rdx),%ymm1,%ymm1
    vmovaps %ymm0,(%rdi,%rcx)
    vmovaps %ymm1,0x20(%rcx,%rdi)
    sub $0x40,%rcx
    jge ff_vector_fmul_avx.loop
ff_vector_fmul_avx.done:
    vzeroupper
    ret
")

variable [CodeEnv]

/-- The loop invariant, at the head of every work block: `rcx` the byte offset
of the current 64-byte chunk, the pointers unchanged. -/
abbrev Inv (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let j := (s.regs.get64 .rcx).toNat
  VectorFmulC t₀ ∧ j % 64 = 0 ∧ j + 64 ≤ 4 * fmulN t₀
  ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
  ∧ s.regs.get64 .rdx = arg2 t₀
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ VectorFmulF t₀ ⋆ Rest need R ra t₀)

/-- At the exit: the frame and the footprint. -/
abbrev Done (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ VectorFmulF t₀ ⋆ Rest need R ra t₀)

/-- At the entry. -/
abbrev Entry (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s = t₀ ∧ VectorFmulC t₀ ∧ (t₀.dmem =⋆ VectorFmulF t₀ ⋆ Rest need R ra t₀)

abbrev tableSse (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_sse", s => Entry need R ra t₀ s
  | "ff_vector_fmul_sse.loop", s => Inv need R ra t₀ s
  | "ff_vector_fmul_sse.loop2", s => Inv need R ra t₀ s
  | "ff_vector_fmul_sse.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varSse : Label → MachineData → Nat
  | "ff_vector_fmul_sse.loop", s => (s.regs.get64 .rcx).toNat + 1
  | "ff_vector_fmul_sse.loop2", s => (s.regs.get64 .rcx).toNat + 1
  | "ff_vector_fmul_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev tableAvx (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_avx", s => Entry need R ra t₀ s
  | "ff_vector_fmul_avx.loop", s => Inv need R ra t₀ s
  | "ff_vector_fmul_avx.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varAvx : Label → MachineData → Nat
  | "ff_vector_fmul_avx.loop", s => (s.regs.get64 .rcx).toNat + 1
  | "ff_vector_fmul_avx.done", _ => 0
  | _, _ => 2 ^ 64

/-- The entry block: the `lea` and the first entry into the loop. -/
macro "fmul_entry" : tactic =>
  `(tactic| (
    vcgen
    rename_i n s h
    obtain ⟨⟨hst, hc, hm⟩, hv⟩ := h
    subst hst
    simp only [Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at *
    rw [lea_len_toNat _ (BitVec.setWidth 32 (-64 : Int64).toBitVec) 64 (by rfl) (by decide)
      (by decide) hc.1 hc.2.1 hc.2.2.1]
    simp at hv
    subst hv
    refine ⟨⟨hc, ?_, ?_, by simp only [true_and]; exact hm⟩, ?_⟩ <;> omega))

/-- The exit block. -/
macro "fmul_exit" : tactic =>
  `(tactic| (
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells))

/-- The `CallPre`/`CallPost` bridges. -/
macro "fmul_pre" : tactic =>
  `(tactic| (
    rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h))

macro "fmul_post" : tactic =>
  `(tactic| (
    rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (VectorFmulF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (8 ?@ _)]
    exact hm))

-- measured 178k heartbeats
set_option maxHeartbeats 270000 in
theorem specSse (hpl : Program.PlacedIn bodySse) (need : Nat) :
    VectorFmulSpec need (entry "ff_vector_fmul_sse") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodySse) (tableSse need)
    (Post' VectorFmulF need) varSse (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodySse]
    · fmul_entry
    · fdsp_block
    · fdsp_block
    · fmul_exit
  · fmul_pre
  · fmul_post

theorem specAvx (hpl : Program.PlacedIn bodyAvx) (need : Nat) :
    VectorFmulSpec need (entry "ff_vector_fmul_avx") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodyAvx) (tableAvx need)
    (Post' VectorFmulF need) varAvx (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodyAvx]
    · fmul_entry
    · fdsp_block
    · fmul_exit
  · fmul_pre
  · fmul_post

end Kraken.Examples.Sbr.VectorFmul
