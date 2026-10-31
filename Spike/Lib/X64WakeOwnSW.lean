/-
**Main's TCB word off `ownG`'s words at wake's placed layout** (x86-64):
`X64WakeOwnS.ownS_disj`'s premises at `RuntimeLayout.ofPlaceWX h i`, the
layout of an output with wake's placement facts (`PlaceWX`), the nthreads
word `a` at its label (`Rt.Reserve.ntA`):

- `tcbSep_W`: `PhRec.TcbSep`, from A8 (`wordsOk`, `tcbSep_of_wordsOk`).
- `ntA_W`: `ntA` is the symbol A13's data part reads (`rtA … "scc_rt_nthreads"`).
- `tcbM_ne_ntA_W`: `tcbM ≠ ntA`: `tcbM = pinA + 8` is a runtime word
  (`fld_mem`) and A13's data part keeps `ntA` clear of all of them (`hA13`,
  a check of the concrete layout, `Spike.Test.WakeLinkedX64.hA13_e`:
  `PlaceWX` has no A13).
- `ownS_disj_W`: `ownS`'s words are off `ownG L (ntA L.lab)`'s.
-/
import Spike.Lib.X64WakeOwnS
import Spike.Lib.X64PlaceWRt
import Spike.Lib.Rt.X64RtReserve

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

private theorem ne_of_sep {a b : BitVec 64} (hs : Scc.Cert.Rt.X64.WordSep a b) : a ≠ b := fun he => by
  subst he; unfold Scc.Cert.Rt.X64.WordSep at hs; omega

/-- **`PhRec.TcbSep` at `ofPlaceWX`** (A8). -/
theorem tcbSep_W : PhRec.TcbSep (Ly) :=
  Scc.Cert.Rt.X64.tcbSep_of_wordsOk
    (Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (PlaceWX.rtWordsOk_link_of_placeWX i h))

/-- **`ntA` is A13's `scc_rt_nthreads`**, given A13's data part. -/
theorem ntA_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ntA (Ly).lab = Scc.Cert.Rt.X64.rtA (Ly).Λ o.prog o.secs "scc_rt_nthreads" := by
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true] at hA13
  obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp hA13.1.1.1.1.1
  have hs := Scc.Cert.Link.X64.symsAround_of_loadOk (PlaceWX.loadOk_link_of_placeWX i h)
  refine (congrArg Int64.toBitVec
    (Scc.Cert.Rt.X64.label_threadAt_of_symLab (E := Scc.Sem.Entry.linux) hs ha0)).trans ?_
  simp only [Scc.Cert.Rt.X64.rtA, ha0, Option.getD_some]
  rfl

/-- **Main's TCB word is not `scc_rt_nthreads`**: a runtime word, which
A13's data part keeps clear of the counter. -/
theorem tcbM_ne_ntA_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    tcbM (Ly) ≠ ntA (Ly).lab := by
  have hnt := ntA_W h i hA13
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq] at hA13
  have hm : tcbM (Ly) ∈ (Ly).rtWords := (Ly).fld_mem (i := 0) (by decide)
  rw [hnt]
  exact (ne_of_sep (hA13.1.1.1.2.1 _ hm)).symm

/-- **`ownS`'s words are off `ownG`'s** at `ofPlaceWX`, `a` the nthreads
word. -/
theorem ownS_disj_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {s : State} :
    ∀ l w w', (l, w) ∈ ownS (Ly) s → (l, w') ∉ ownG (Ly) (ntA (Ly).lab) s :=
  ownS_disj (tcbSep_W h i) (tcbM_ne_ntA_W h i hA13)

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.tcbSep_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbSep_W

/-- info: 'Spike.Lib.X64.WakePh.tcbM_ne_ntA_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbM_ne_ntA_W

/-- info: 'Spike.Lib.X64.WakePh.ownS_disj_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownS_disj_W
