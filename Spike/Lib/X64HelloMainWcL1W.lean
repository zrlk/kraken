/-
**The controls of `MainWcPS.hW.rd` and `hra` at rodata's own label** (x86-64; the twin of
`Spike/Lib/A64HelloMainWcL1W.lean`'s live part): `wc_rodata` from the allocator's return at `RdSrcL1`'s invariants
(`jP'` … `jX3` at the labels `lbl` and rodata's label `l`), for any `.x15` invariant `Jp` below `rdCA l ini` at
`RB lbl l` (`hJp`; `RdJpL.jpT_rb` at `Level1I`'s), and any last-block invariant `J4` whose controls are rodata's
from the publication on (`hJ4`).

- `rd_ctl`: every control of the seven invariants is one of rodata's past the allocation (`RdPlS.RdCH`), with its
  term among `helloTerms`, and `.x15`'s base is `l`'s place.
- `hra_jpL`, `hra_jpLW`: `hra` (`MainWcPS`'s and `rdPostW_WSHX`'s forms) at a landing image `JpL` below the root's
  call invariant `mRdJ0 (rdJH lab R' J) σC` (`RdRa.hra_land`, `mNC`'s return address).

## Differences from the AArch64 version

- `.x15` has seven invariants (AArch64 `.sp0`, eight): there is no fence node, and `MainWcPS.hW`'s last one is
  `HelloRd.J4P p J4 J5` (the publication a source stutter). `rd_ctl` takes that last invariant
  as a parameter `J4` with `hJ4`: its controls are `rdC4`, `rdC5` or `rdRet` (AArch64: `jC4`, `jRet` fixed).
- `hra` is the return address `.Lscc_rt_main.x0` at `σ0.slot 0` (AArch64 `.L1_scc_rt_main.sp0` at `-8`).
- `rdJH` takes `scc_rt_main`'s region `R'` (x86-64's `mNC` pins `%rbp` in it).
- No `RdBuf` import: its only use is `cellX0_jpL`'s.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `cellX0_jpL`. AArch64's
  `rdPostW_L1` (at `WSHF`, `ownGH`) is restated at `ownGHXW` inside `X64HelloMainWcL1RX.hW_L1X`.
-/
import Spike.Lib.X64HelloRdPostWfSF
import Spike.Lib.X64HelloRdPlS
import Spike.Lib.X64HelloRdJpL
import Spike.Lib.X64HelloRdRa

namespace Spike.Lib.X64.HelloPh.MainWcL1W

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64Consumer (Lbl)
open Spike.Lib.X64 (leave)
open Spike.Lib.X64.Flow.HelloRd (rN)
open Spike.Lib.X64.Flow.Hello1 (aR mRdJ0)
open Spike.Lib.X64.HelloPh.Level1 (JpL)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.RdSrcL1 (RB jP' jX1 jC2 jC2' jX3)
open Spike.Lib.X64.HelloPh.RdPlS (RdCH)
open Spike.Lib.X64HelloRodataSrc (rdCA rdC4 rdC5 rdRet)
open Spike.Lib (Ctl Region MemSide)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## The controls -/

section Ctl

variable {lbl : Lbl} {l : WeakMem.AllocLabel} {Jp J4 : FAS → Ctl → Prop}

/-- **The seven invariants' controls** (module doc): `.x15`'s base is `l`'s place, and the control is one of
rodata's past the allocation, its term among `helloTerms`. -/
theorem rd_ctl (hJp : ∀ σ0 c, Jp σ0 c → RB lbl l σ0 ∧ ∃ ini, c = rdCA l ini)
    (hJ4 : ∀ σ0 c, J4 σ0 c → RB lbl l σ0 ∧ ∃ ini wo0 wo1,
      c = rdC4 l ini wo0 wo1 ∨ c = rdC5 l ini wo0 wo1 ∨ c = rdRet l ini wo0 wo1) :
    ∀ σ0 c, (Jp σ0 c ∨ jP' lbl l σ0 c ∨ jX1 lbl l σ0 c ∨ jC2 lbl l σ0 c ∨ jC2' lbl l σ0 c ∨ jX3 lbl l σ0 c ∨
      J4 σ0 c) →
      RB lbl l σ0 ∧ ∃ ini, RdCH l ini c ∧ c.term ∈ Spike.Lib.X64HelloRdCf.helloTerms := by
  intro σ0 c h
  have T := fun ini => Spike.Lib.X64HelloRdCf.rd_terms l ini default default
  rcases h with h | ⟨hB, ini, rfl⟩ | ⟨hB, ini, w, rfl⟩ | ⟨hB, ini, wo0, rfl⟩ | ⟨hB, ini, wo0, rfl⟩ |
    ⟨hB, ini, wo0, w, rfl⟩ | h
  · obtain ⟨hB, ini, rfl⟩ := hJp σ0 c h
    exact ⟨hB, ini, .inl ⟨rfl, rfl⟩, (T ini).2.2.1⟩
  · exact ⟨hB, ini, .inr (.inl ⟨rfl, rfl⟩), (T ini).2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inl ⟨rfl, rfl⟩), (T ini).2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inl ⟨rfl, rfl⟩⟩),
      (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inl ⟨rfl, rfl⟩)⟩),
      (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.2.1⟩
  · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inl ⟨rfl, rfl⟩)⟩),
      (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 default).2.2.2.2.2.1⟩
  · obtain ⟨hB, ini, wo0, wo1, rfl | rfl | rfl⟩ := hJ4 σ0 c h
    · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inl ⟨rfl, rfl⟩⟩)⟩),
        (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.1⟩
    · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inr (.inl ⟨rfl, rfl⟩)⟩)⟩),
        (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.2.1⟩
    · exact ⟨hB, ini, .inr (.inr ⟨wo0, .inr (.inr ⟨wo1, .inr (.inr ⟨rfl, rfl⟩)⟩)⟩),
        (Spike.Lib.X64HelloRdCf.rd_terms l ini wo0 wo1).2.2.2.2.2.2.2.2⟩

end Ctl

/-! ## `.x15`'s facts at a landing image -/

section Land

variable {R R' : Region} {ms₀ : MemSide isa} {lab : Label → Int64} {J : FAS → Ctl → Prop} {σC : FAS}
  {J0 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}

/-- **`MainWcPS.hra` at a landing image** below the root's call invariant: `.x15`'s return address is
`scc_rt_main`'s `.x2` (`mNC`'s, kept by the entry and the allocator, `RdRa.hra_land`). -/
theorem hra_jpL {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab R' J) σC) l b w σ c) :
    lab ".Lscc_rt_main.x0" = Int64.ofBitVec (σ.slot 0) := by
  obtain ⟨_, σx, σ', c0, _, hN, _, rfl⟩ := h
  exact Spike.Lib.X64.HelloPh.RdRa.hra_land (R := R) (σx := σx)
    (fun σe c h => let ⟨c', hc'⟩ := h.2.2; Spike.Lib.X64.HelloPh.RdRa.x30_mRdJ0 (c := c') ⟨h.1, hc'⟩) hN

/-- **`RdWfSFX.rdPostW_WSHX`'s `hra` at a landing image** (`hra_jpL`, the bit-vector form). -/
theorem hra_jpLW {σ : FAS} {c : Ctl}
    (h : JpL (R := R) ms₀ lab J0 (mRdJ0 (rdJH lab R' J) σC) l b w σ c) :
    σ.slot 0 = (lab ".Lscc_rt_main.x0").toBitVec := by
  rw [hra_jpL h, Int64.toBitVec_ofBitVec]

end Land

end Spike.Lib.X64.HelloPh.MainWcL1W

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.rd_ctl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.rd_ctl

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpL

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpLW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpLW
