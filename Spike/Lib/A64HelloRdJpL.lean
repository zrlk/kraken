/-
**`wc_rodata`'s `.sp0` invariant `JpL` at rodata's allocation** (AArch64,
`Level1I`'s `hP`): at a landing image `Level1.JpL` whose allocator call is below `rdCN` (`hJ1`, the
root's `mRdJ0 (rdJH …)`), `.sp0`'s `x0` is the landing's base `b`, the place of `l` at `upd L0 l b`, its two words
below `2 ^ 64` (the call's `room` and `cells`), and the source is at `rdCA l ini` (`allocCtl` at rodata's `newBuf`,
`HelloRodataSrc.rdCN_newBuf`). This is `RdSrcL1.hr0_rd`'s `hJp`.

- `jpL_rb`: `JpL … → RB (upd L0 l b) l σ ∧ ∃ ini, c = rdCA l ini`.
- `jpT_rb`: the same at `JpT (JpL …) t`.
- `rdJH_rdCN`: `hJ1` at the root's `mRdJ0 (rdJH lab J) σC`.
-/
import Spike.Lib.A64HelloLevel1T
import Spike.Lib.A64HelloRdSrcL1
import Spike.Lib.A64SegInstA

namespace Spike.Lib.A64.HelloPh.RdJpL

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Ctl MemSide Region)
open Spike.Lib.A64.Flow (enter leave)
open Spike.Lib.A64.Flow.Hello1 (mRdJ0)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.RdSrcL1 (RB)
open Spike.Lib.HelloRodataSrc (rdCN rdCA)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **`JpL` below `rdCN`** (module doc): `.sp0`'s `x0` is `l`'s place `b` at `upd L0 l b`, two words below
`2 ^ 64`, and the source is at `rdCA l ini`. -/
theorem jpL_rb {R : Region} {ms₀ : MemSide isaLSE2} {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop}
    {L0 : Spike.Lib.A64Consumer.Lbl} {l : WeakMem.AllocLabel} {b w : Nat} {σ : FAS} {c : Ctl}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) (h : JpL (R := R) ms₀ lab J0 J1 l b w σ c) :
    RB (Spike.Lib.A64ConsumerA.upd L0 l b) l σ ∧ ∃ ini, c = rdCA l ini := by
  obtain ⟨q, σx, σ', c0, ⟨ini, old, hc, hx0, hb, hle, -, -, -, -⟩, ⟨⟨σe, hJe, -, -⟩, h257, -⟩,
    ⟨hc0, -, -, hh, -⟩, rfl⟩ := h
  have hq : q.1.c0 = rdCN := hc0.symm.trans (hJ1 _ _ hJe)
  have hqh : q.1.h = 257#64 := hh.symm.trans h257
  obtain ⟨h1, h2, h3, -, -⟩ := Spike.Lib.HelloRodataSrc.rdCN_newBuf
  have ht := q.2.term
  have hv := q.2.ev
  have hn := q.2.num
  rw [hq, h1] at ht
  simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
  obtain ⟨hx, ⟨ha, hτ⟩, he⟩ := ht
  rw [hq, ← ha, h2] at hv
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  rw [← hv.2, h3] at hn
  simp only [Option.some.injEq] at hn
  have hoff := q.2.off
  rw [hqh, show (Spike.Lib.A64.Alloc.mOf 257#64).toNat = 0 by decide] at hoff
  have hroom := q.2.room
  have hcells := q.2.cells
  have hx0' : σx.regs.X0.toBitVec.toNat = b := hx0
  refine ⟨⟨?_, ?_⟩, ini, ?_⟩
  · show Spike.Lib.A64ConsumerA.upd L0 l b l = some σx.regs.X0.toBitVec.toNat
    simp [Spike.Lib.A64ConsumerA.upd, hx0']
  · show σx.regs.X0.toBitVec.toNat + 16 ≤ 2 ^ 64
    omega
  · rw [hc, hq, ← hx, ← hτ, ← he, ← hn]; rfl

/-- **`jpL_rb` at `JpT`** (`RdSrcL1.hr0_rd`'s `hJp` at `Level1I`'s `.sp0` invariant). -/
theorem jpT_rb {R : Region} {ms₀ : MemSide isaLSE2} {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop}
    {L0 : Spike.Lib.A64Consumer.Lbl} {l : WeakMem.AllocLabel} {b w : Nat} {t : UInt64}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) :
    ∀ σ c, JpT (JpL (R := R) ms₀ lab J0 J1 l b w) t σ c →
      RB (Spike.Lib.A64ConsumerA.upd L0 l b) l σ ∧ ∃ ini, c = rdCA l ini :=
  fun _ _ h => jpL_rb hJ1 h.1

/-- **The root's call invariant is below `rdCN`**: `mRdJ0 (rdJH lab J) σC`'s controls are `rdCN`. -/
theorem rdJH_rdCN {lab : Label → Int64} {J : FAS → Ctl → Prop} {σC : FAS} :
    ∀ σ c, mRdJ0 (rdJH lab J) σC σ c → c = rdCN :=
  fun _ _ h => h.2.1

end Spike.Lib.A64.HelloPh.RdJpL

/-- info: 'Spike.Lib.A64.HelloPh.RdJpL.jpL_rb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdJpL.jpL_rb

/-- info: 'Spike.Lib.A64.HelloPh.RdJpL.jpT_rb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdJpL.jpT_rb

/-- info: 'Spike.Lib.A64.HelloPh.RdJpL.rdJH_rdCN' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdJpL.rdJH_rdCN
