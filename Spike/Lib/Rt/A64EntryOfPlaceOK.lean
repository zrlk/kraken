/-
**`_start` at an output passing `placeOK`** (AArch64, the twin of
`Spike/Lib/Rt/X64EntryOfPlaceOK.lean`): `_start`'s block (`b scc_rt_start`)
inside `SFacts … Dt` at the record, with no premise but the source's facts
at `c0`. The code check is A11's (`rtCodeOk_bare_of_placeOKAt`,
`RtCodeIn.entry`); the phase facts are A6's (`rtPh_of_placeOKAt`,
`startPhTab`): the block's phase check and the phase index `13` at its pc,
which is not the take's (`Tk`: `13 / 8 % 2 = 1`).

- `entryW_ofPlaceOK`: the block inside `SFacts … Dt` (`blkW_pre`), any
  write tail `Dt` and taken range `rS`: the form of `a64_lower_correct`'s
  `hEntry`.
-/
import Spike.Lib.Rt.A64RtW
import Spike.Lib.Rt.A64RtCode
import Spike.Lib.Rt.A64RtPhRec
import Spike.Lib.A64StubFacts

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.PhRec (μ own Tk K okPc ph)
open Spike.Lib.A64.Rt.PhOfTab

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- A fact of `startPhTab` passes its check at the record. -/
theorem startFact_ofPlaceOK {f : Scc.Cert.Rt.A64.PhFact} (hf : f ∈ startPhTab) :
    Scc.Cert.Rt.A64.factOk (Scc.Cert.Link.A64.codeOf (Ly).Λ.code.lo o.prog) (okPc (Ly)) (ph (Ly)) f = true :=
  Scc.Cert.Rt.A64.factOk_of_rtPhOk (rtPh_of_placeOKAt h) (by simp only [rtPhTab, List.mem_append]; simp [hf])

/-- **`_start`'s block inside `SFacts … Dt`** at the record of an output
passing `placeOK`, in any 16-aligned region around the entry's offsets, the
source at `c0` (`hC0`). -/
theorem entryW_ofPlaceOK {rS : Range} {lbl : Lbl} {Dt : State → Prop} {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 0 ≤ R.hi) {c0 : Ctl}
    (hC0 : CFacts (Ly).Λ lbl c0) :
    BlkW (fun s c => SFacts (Ly).Λ (μ (Ly)) (own (Ly)) rS (Tk (Ly)) lbl s c Dt) (K (Ly) rS) (Ly).exe (Ly).endPc
      R F (Ret0.entryN (Ly).lab c0) Ret0.entryB := by
  have hl := PhRecOf.hlab_ofPlaceOK h i
  have hb := blkPh_of_factOk hl (l := "_start") (k := 0) (b := Code.Start.entryB) (ra := none) (dead := none)
    (rapc := 0) (dset := fun _ => false) (fun _ h => by cases h)
    (fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h)
    (startFact_ofPlaceOK h i (f := .blk "_start" 0 Code.Start.entryB none none) (by simp [startPhTab]))
  have hp0 := ph_of_factOk hl (startFact_ofPlaceOK h i (f := .ph "_start" 0 13) (by simp [startPhTab]))
  have hW := blkW_pre (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS)) (lbl := lbl)
    (F := F) (rS := rS) (n := Ret0.entryN (Ly).lab c0) (l := "_start") (k := 0) (dead := fun _ => false) (ra := 0)
    (rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h)).entry (ofNat4_zero _) Ret0.entryB_ok hR hal hlo hhi
    (fun _ _ hJ => hJ ▸ hC0) hb (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    (fun _ _ _ => rfl) (fun s hs => by unfold Tk; rw [hs, hp0]; decide)
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨h1, h2⟩ := hW s σ c he hn hd hp hA hF hJn k hk m hA' hD
  exact ⟨h1.dt_mono fun _ h => h.elim, h2⟩

end Place

end Spike.Lib.A64.Rt
