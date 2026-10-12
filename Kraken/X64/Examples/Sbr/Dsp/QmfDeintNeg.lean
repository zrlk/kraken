import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.PackedSse
import Kraken.Rules.IntMisc
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas

/-!
# `ff_sbr_qmf_deint_neg_sse` as a `ProcSpec`

`sbr_qmf_deint_neg(v, src)` (`libavcodec/x86/sbrdsp.asm`) writes `v[64]`
from `src[64]`: the even floats of `src`, reversed, go to `v[0..31]`, the odd
ones, negated (`xorps` with the constant `ff_ps_neg`), to `v[32..63]`
(`libavcodec/sbrdsp_template.c`). `spec` proves `QmfDeintNegSpec`: a call
with `v`, `src` and `ff_ps_neg` 16-byte aligned, the 256 bytes of `v`, the
256 of `src` and the 16 of `ff_ps_neg` owned, returns with the SysV
convention restored and only those bytes changed.

## Notes

* The contract matches `tests/checkasm/sbrdsp.c` (`src[64]`, `dst[64]`,
  both `LOCAL_ALIGNED_16`) and the one call site, `sbr_qmf_synthesis` in
  `libavcodec/aacsbr_template.c` (`qmf_deint_neg(v, mdct_buf[0])`, two
  distinct buffers). The footprint owns `v` and `src` as separate blocks, so
  the spec assumes they do not overlap; it holds at that call site. No
  condition beyond checkasm: alignment of `v` (two `movaps` stores per
  iteration), of `src` (two `movaps` loads) and of `ff_ps_neg` (one `movaps`
  load, the constant's alignment, discharged from the layout at linking).
* Dropping the alignment of `src` from `C` makes the loop block fail on the
  alignment of both loads (negative check, scratch).
* No stack, no callee-saved register touched: the reservation is 0.
* The loop counts `rcx` from `-128` up to `0` by 16 (`jl`, a signed exit);
  the invariant tracks `m = (-rcx).toNat` (a positive multiple of 16, at most
  128), with `rdi = v + (m - 16)` moving down and `rsi`, `rdx` fixed at the
  ends of `src` and `v`. The `jl` exit needs `BitVec.signed_eq` as a local
  `grind` rule, as in `ButterfliesBlocks.lean`.
* The loads `(%rsi,%rcx,2)` and `0x10(%rsi,%rcx,2)` with `rsi = src + 256`
  have the address shape `a + c + x + d`, which no `Blocks.Inside` rule
  matched; `Mem.Blocks.Inside.base_add_add_add`
  (`Kraken/Rules/LeafLemmas.lean`) covers it.
* Rule-file `grind` scopes opened (see `Kraken/Rules/*.lean`):
  `Kraken.Rules.GenericMem.Norm`, `Kraken.Rules.IntMisc.SubReg`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.LeafLemmas.BaseAdd
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.QmfDeintNeg

/-- The routine from the object file, labels prefixed with the symbol, the
final `ret` kept behind a label of its own (`….done`). -/
def body : Program := parse("
ff_sbr_qmf_deint_neg_sse:
    mov $0xffffffffffffff80,%rcx
    lea 0x100(%rdi),%rdx
    add $0x70,%rdi
    add $0x100,%rsi
    movaps ff_ps_neg(%rip),%xmm3
ff_sbr_qmf_deint_neg_sse.loop:
    movaps (%rsi,%rcx,2),%xmm0
    movaps 0x10(%rsi,%rcx,2),%xmm1
    movaps %xmm0,%xmm2
    shufps $0x88,%xmm1,%xmm2
    shufps $0x77,%xmm0,%xmm1
    xorps %xmm3,%xmm2
    movaps %xmm1,(%rdi)
    movaps %xmm2,(%rdx,%rcx,1)
    sub $0x10,%rdi
    add $0x10,%rcx
    jl ff_sbr_qmf_deint_neg_sse.loop
ff_sbr_qmf_deint_neg_sse.done:
    ret
")

variable [CodeEnv]

/-- The caller's side of memory behind the footprint. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- At the loop: `rcx = -m` with `m` the bytes of `v` still to write from the
middle, a positive multiple of 16 at most 128; `rsi = src + 256`,
`rdx = v + 256`, `rdi = v + m - 16`. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_qmf_deint_neg_sse", s => s = t₀ ∧ QmfDeintNegC t₀
      ∧ (t₀.dmem =⋆ QmfDeintNegF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_deint_neg_sse.loop", s =>
      let v := arg0 t₀
      let m := (-s.regs.get64 .rcx).toNat
      QmfDeintNegC t₀ ∧ s.regs.get64 .rsi = arg1 t₀ + 256#64
      ∧ s.regs.get64 .rdx = v + 256#64
      ∧ s.regs.get64 .rdi = v + (-s.regs.get64 .rcx - 16#64)
      ∧ 0 < m ∧ m ≤ 128 ∧ m % 16 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfDeintNegF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_deint_neg_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfDeintNegF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: `-rcx` at the loop (128 down to 16); 0 at `.done`. -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_qmf_deint_neg_sse.loop", s => (-s.regs.get64 .rcx).toNat
  | "ff_sbr_qmf_deint_neg_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev Post' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ QmfDeintNegF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

/- The `jl` exit reads the overflow flag, which compares signed values. -/
attribute [local grind =] BitVec.signed_eq

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : QmfDeintNegSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen with finish
    · vcgen with finish
    · vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (QmfDeintNegF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.QmfDeintNeg
