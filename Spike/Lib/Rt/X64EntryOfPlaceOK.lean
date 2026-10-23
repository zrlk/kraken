/-
**`_start` at an output passing `placeOK`** (x86-64): `entry_segW'`'s
obligations (`EntryW`) and then `_start`'s segment, with no premise left
but the source's facts at `c0` and the callee's segment. The code check is
A11's (`rtCodeOk_bare_of_placeOKAt`, `RtCodeIn.start0`); the phase facts are
A6's (`rtPh_of_placeOKAt`, `startPhTab`): `_start`'s steps off the sites and
in their phase, the call's block's phase check, and the phase index `13`
at its three pcs, which is not the take's (`Tk`: `13 / 8 % 2 = 1`).

- `entryW_ofPlaceOK`: `EntryW` inside `SFacts … Dt` at the record
  (`Spike/Lib/X64PhRec.lean`), any write tail `Dt` and taken range `rS`.
- `entry_segW_ofPlaceOK`: `entry_segW_take` with it, at the entry stack,
  `rtF`, the take of `rS0` its outside move: the form of
  `x64_lower_correct`'s `hEntryX`.
-/
import Spike.Lib.Rt.X64EntryW
import Spike.Lib.Rt.X64RtCode
import Spike.Lib.Rt.X64RtPhOfTab
import Spike.Lib.X64PhRec
import Spike.Lib.X64StubFacts

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (pcOf codeLabel)
open Spike.Lib.X64Consumer
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.PhRec (μ own Tk K okPc ph)
open Spike.Lib.X64.Rt.PhOfTab

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The record's labels are the code labels** of an output passing
`placeOK`. -/
theorem lab_ofPlaceOK : ∀ l a, codeLabel (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog l = some a →
    (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a := by
  intro _ _ ha
  exact @Scc.Cert.Rt.X64.label_threadAt_of_codeLabel Scc.Sem.Entry.linux _ _ _ (RuntimeLayout.ofPlaceOK h i).valid
    _ _ (by exact Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK_above h i) ha

/-- A fact of `startPhTab` passes its check at the record. -/
theorem startFact_ofPlaceOK {f : Scc.Cert.Rt.X64.PhFact} (hf : f ∈ startPhTab) :
    Scc.Cert.Rt.X64.factOk (codeLabel (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog)
      (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i)) f = true :=
  Scc.Cert.Rt.X64.factOk_of_rtPhOk (rtPh_of_placeOKAt h) (by simp only [rtPhTab, List.mem_append]; simp [hf])

/-- A pc of phase `13` is not in the take's phase. -/
theorem not_tk_13 {L : RuntimeLayout} {p : Int64} (hp : ph L p.toBitVec.toNat = 13) :
    ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk L s := fun s hs => by
  unfold Tk; rw [hs, hp]; decide

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **`_start`'s nodes inside `SFacts … Dt`** at the record of an output
passing `placeOK`, in any region with room for the call's return address,
the source at `c0` (`hC0`). -/
theorem entryW_ofPlaceOK {rS : Range} {lbl : Lbl} {Dt : State → Prop} {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 0 ≤ R.hi) {c0 : Ctl} (hC0 : CFacts (Ly).Λ lbl c0) :
    EntryW (fun s c => SFacts (Ly).Λ (μ (Ly)) (own (Ly)) rS (Tk (Ly)) lbl s c Dt) (K (Ly) rS) (Ly).exe (Ly).endPc R F
      (Ly).lab c0 := by
  have hl := lab_ofPlaceOK h i
  have hs0 := step_of_factOk hl (startFact_ofPlaceOK h i (f := .step "_start" 0 2)
    (by simp only [startPhTab, List.mem_cons, true_or]))
  have hs2 := step_of_factOk hl (startFact_ofPlaceOK h i (f := .step "_start" 2 4)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hf6 := startFact_ofPlaceOK h i (f := .blk "_start" 6 Code.Start.entryCall none none)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true])
  have hb := blkPh_of_factOk hl (l := "_start") (o := 6) (b := Code.Start.entryCall) (ra := none) (dead := none)
    (rapc := 0) (dset := fun _ => false) (fun _ _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h) hf6
  have hp0 := ph_of_factOk hl (startFact_ofPlaceOK h i (f := .ph "_start" 0 13)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp2 := ph_of_factOk hl (startFact_ofPlaceOK h i (f := .ph "_start" 2 13)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  have hp6 := ph_of_factOk hl (startFact_ofPlaceOK h i (f := .ph "_start" 6 13)
    (by simp only [startPhTab, List.mem_cons, true_or, or_true]))
  exact (entryW_of_instOk (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i)
    (rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h)).start0 hR hlo hhi hC0 hs0.1 hs0.2 hs2.1 hs2.2 hb
    (not_tk_13 hp0) (not_tk_13 hp2) (not_tk_13 hp6)).mono fun _ _ hS => hS.dt_mono fun _ h => h.elim

/-- **`_start` as one segment at an output passing `placeOK`**: from
`_start` at the entry stack under `rtF`, the take of `rS0` the outside
move, inside `SFacts … Dt`, given the source's facts at `c0` and the
callee's segment `hS` (`x64_start_segW`'s conclusion). -/
theorem entry_segW_ofPlaceOK {p : Prog} {lbl : Lbl} {ms : MemSide isa} {Dt : State → Prop} {c0 : Ctl}
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ) (hC0 : CFacts (Ly).Λ lbl c0) {Q : Frag isa}
    (hS : ∀ F' : MachineData → Prop, FStable ((entryR E).callee (-8) (-296) 8) F' → KStable (K (Ly) (rS0 (Ly))) F' →
      (∀ m, F' m → rtF (Ly) m) → ∀ Q' : Frag isa,
      SegW (fun s c => SFacts (Ly).Λ (μ (Ly)) (own (Ly)) (rS0 (Ly)) (Tk (Ly)) lbl s c Dt) (K (Ly) (rS0 (Ly))) p lbl ms
        (At (Ly).exe (Ly).endPc ((entryR E).callee (-8) (-296) 8) F' (Ret0.startN0 (Ly).lab c0)) Q') :
    SegW (fun s c => SFacts (Ly).Λ (μ (Ly)) (own (Ly)) (rS0 (Ly)) (Tk (Ly)) lbl s c Dt) (K (Ly) (rS0 (Ly))) p lbl ms
      (At (Ly).exe (Ly).endPc (entryR E) (rtF (Ly)) (entryN0 (Ly).lab c0)) Q :=
  entry_segW_take (Ly) hE (rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h)).start0 (rS0_sub (Ly)) c0
    (entryW_ofPlaceOK h i (entryR_ok hE) (by show (-65536 : Int) ≤ -8; decide) (by show (0 : Int) ≤ 0; decide) hC0) hS

end Place

end Spike.Lib.X64.Rt
