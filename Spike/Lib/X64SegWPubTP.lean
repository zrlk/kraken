/-
**A segment with rows after a publication keeps the `%fs` base** (x86-64; no AArch64 twin): `SegW.keepTPN`
(`Spike/Lib/X64Hello1RodataTP.lean`) for `SegWP` (`Spike/Lib/X64SegWPub.lean`). The source's publication is a
source step, so the state it is taken at is the row's, and `tpXa` keeps `MemSide.pub`.

- `SegWP.keepTPN`: a `SegWP` inside `NoSetFsW W K` under `tpXa ms t` is one inside `W` under `ms`, with `TP t`
  kept from the entry to the exit.
-/
import Spike.Lib.X64SegWPub
import Spike.Lib.X64Hello1RodataTP

namespace Spike.Lib.X64SegWPub

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Frag Out KOut MemSide)
open Spike.Lib.X64.KeepTP (TP tpXa out_tp)
open Spike.Lib.X64.Flow (NoSetFsW)

/-- **A `SegWP` inside `NoSetFsW W K` keeps the `%fs` base** (`SegW.keepTPN` for `SegWP`): under `ms` (whose
kernel is x86-64's), from the entry's pairs at `fsBase = t` to the exit's at `fsBase = t`, inside `W`. -/
theorem SegWP.keepTPN {W : Frag isa} {K : State → State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {P Q : Frag isa} {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : SegWP (NoSetFsW W K) K p lbl (tpXa ms t) P Q) :
    SegWP W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨fun s c => inv s c ∧ TP t s, fun s c hp => ⟨hP s c hp.1, hp.2⟩, fun s c h => (hiW s c h.1).1,
    fun s c hi => ?_⟩
  obtain ⟨hout, hk⟩ := hcl s c hi.1
  have hw := hiW s c hi.1
  have mX : ∀ s c, ((inv s c ∨ Q s c) ∧ TP t s) → (inv s c ∧ TP t s) ∨ (Q s c ∧ TP t s) :=
    fun _ _ hx => hx.1.elim (fun h => .inl ⟨h, hx.2⟩) fun h => .inr ⟨h, hx.2⟩
  refine ⟨fun hK' => ?_, fun s' hks => (hw.2.2 s' hks).elim⟩
  rcases hout hK' with ho | ⟨hns, hpub, c₁, hps, hy, ho⟩
  · exact .inl ((out_tp hK hw.2.1 hi.2 ho).mono mX)
  · exact .inr ⟨hns, hpub, c₁, hps, ⟨hy, hi.2⟩, (out_tp hK hw.2.1 hi.2 ho).mono mX⟩

/-- info: 'Spike.Lib.X64SegWPub.SegWP.keepTPN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64SegWPub.SegWP.keepTPN

end Spike.Lib.X64SegWPub
