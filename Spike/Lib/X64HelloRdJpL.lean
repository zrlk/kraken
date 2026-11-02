/-
**`wc_rodata`'s `.x15` invariant `JpL` at rodata's allocation** (x86-64; the twin of
`Spike/Lib/A64HelloRdJpL.lean`): at a landing image `Level1.JpL` whose allocator call is below `rdCN` (`hJ1`, the
root's `mRdJ0 (rdJH …)`), `.x15`'s `%rax` is the landing's base `b`, the place of `l` at `upd L0 l b`, its two
words below `2 ^ 64` (the call's `room` and `cells`), and the source is at `rdCA l ini` (`allocCtl` at rodata's
`newBuf`, `X64HelloRodataSrc.rdCN_newBuf`). This is `RdSrcL1.hr0_rd`'s `hJp`.

- `jpL_rb`: `JpL … → RB (upd L0 l b) l σ ∧ ∃ ini, c = rdCA l ini`.
- `jpT_rb`: the same at `JpT (JpL …) t`.
- `rdJH_rdCN`: `hJ1` at the root's `mRdJ0 (rdJH lab R J) σC`.

## Differences from the AArch64 version

- The landing's base is `%rax` (AArch64: `x0`), and `RB` is `X64.HelloPh.RdSrcL1`'s.
- `HelloRd.rN`'s call node also records `%rbp` (`mR R`'s saved-`%rbp` slot), skipped here, and `rdJH` takes the
  region `R` (its `mNC` records `%rbp`).
-/
import Spike.Lib.X64HelloLevel1T
import Spike.Lib.X64HelloLevel1
import Spike.Lib.X64HelloRdSrcL1
import Spike.Lib.X64SegInstA

namespace Spike.Lib.X64.HelloPh.RdJpL

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Ctl MemSide Region)
open Spike.Lib.X64 (enter leave)
open Spike.Lib.X64.Flow.Hello1 (mRdJ0)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.RdSrcL1 (RB)
open Spike.Lib.X64HelloRodataSrc (rdCN rdCA)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-- **`JpL` below `rdCN`** (module doc): `.x15`'s `%rax` is `l`'s place `b` at `upd L0 l b`, two words below
`2 ^ 64`, and the source is at `rdCA l ini`. -/
theorem jpL_rb {R : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop}
    {L0 : Spike.Lib.X64Consumer.Lbl} {l : WeakMem.AllocLabel} {b w : Nat} {σ : FAS} {c : Ctl}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) (h : JpL (R := R) ms₀ lab J0 J1 l b w σ c) :
    RB (Spike.Lib.X64ConsumerA.upd L0 l b) l σ ∧ ∃ ini, c = rdCA l ini := by
  obtain ⟨q, σx, σ', c0, ⟨ini, old, hc, hx0, hb, hle, -⟩, ⟨⟨σe, hJe, -⟩, -, h257, -⟩,
    ⟨hc0, -, -, hh, -⟩, rfl⟩ := h
  have hq : q.1.c0 = rdCN := hc0.symm.trans (hJ1 _ _ hJe)
  have hqh : q.1.h = 257#64 := hh.symm.trans h257
  obtain ⟨h1, h2, h3, -, -⟩ := Spike.Lib.X64HelloRodataSrc.rdCN_newBuf
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
  rw [hqh, show (Spike.Lib.X64.Alloc.mOf 257#64).toNat = 0 by decide] at hoff
  have hroom := q.2.room
  have hcells := q.2.cells
  have hx0' : σx.regs.rax.toBitVec.toNat = b := hx0
  refine ⟨⟨?_, ?_⟩, ini, ?_⟩
  · show Spike.Lib.X64ConsumerA.upd L0 l b l = some σx.regs.rax.toBitVec.toNat
    simp [Spike.Lib.X64ConsumerA.upd, hx0']
  · show σx.regs.rax.toBitVec.toNat + 16 ≤ 2 ^ 64
    omega
  · rw [hc, hq, ← hx, ← hτ, ← he, ← hn]; rfl

/-- **`jpL_rb` at `JpT`** (`RdSrcL1.hr0_rd`'s `hJp` at `Level1I`'s `.x15` invariant). -/
theorem jpT_rb {R : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop}
    {L0 : Spike.Lib.X64Consumer.Lbl} {l : WeakMem.AllocLabel} {b w : Nat} {t : UInt64}
    (hJ1 : ∀ σ c, J1 σ c → c = rdCN) :
    ∀ σ c, JpT (JpL (R := R) ms₀ lab J0 J1 l b w) t σ c →
      RB (Spike.Lib.X64ConsumerA.upd L0 l b) l σ ∧ ∃ ini, c = rdCA l ini :=
  fun _ _ h => jpL_rb hJ1 h.1

/-- **The root's call invariant is below `rdCN`**: `mRdJ0 (rdJH lab R J) σC`'s controls are `rdCN`. -/
theorem rdJH_rdCN {lab : Label → Int64} {R : Region} {J : FAS → Ctl → Prop} {σC : FAS} :
    ∀ σ c, mRdJ0 (rdJH lab R J) σC σ c → c = rdCN :=
  fun _ _ h => h.2.1

end Spike.Lib.X64.HelloPh.RdJpL

/-- info: 'Spike.Lib.X64.HelloPh.RdJpL.jpL_rb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdJpL.jpL_rb

/-- info: 'Spike.Lib.X64.HelloPh.RdJpL.jpT_rb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdJpL.jpT_rb

/-- info: 'Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN
