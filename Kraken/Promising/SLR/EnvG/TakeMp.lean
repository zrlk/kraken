/-
**Part 5: message passing with a writing
reader — the program, its predicates and its VCs** (on `EnvGT`,
`EnvG/TakeEnv.lean`).

The writer is MP's (`SLR/MpTrees.lean`, `mpWriter`: `str` data `:= 1`, then
`stlr` flag `:= 1`, releasing all of `Dt` to the slot of the reader's
acquire id, `flagPred`). The reader **takes** the data at its acquire load,
then writes it and reads its own write back:
```
 takeReader:
 0 spin:
 1   ldar w3, [x0]
 2   cbz  w3, spin
 3   mov  w5, #43
 4   str  w5, [x1]
 5   ldr  w4, [x1]
 6 done_t:
```
No existing route proves a final-state fact about this program that needs the
data's ownership after the hand-off (the reader's plain store needs a
positive share of `Dt`, the final value needs all of it).

**The VCs** (on `ET tid = EnvGT isa Arch.armv8 tid rdPlan`, the empty plan):
- `vc_k1` (`ldar w3, [x0]`): from `K1` (the loop invariant), an outcome with
  a zero low word re-establishes `K1`, one with a non-zero low word gives
  `K2`: **all of `Dt`**, with every write at or below `vwNew`
  (`takeAll_wr_full`, from the slot's `flagPred` and validity).
  The loop invariant must survive *spurious* takes: an acquire load of a zero
  flag message takes that message's slot too (if any), swapping the
  reader's id for a fresh one whose predicate is relaxed at that message
  (`takeAll_held`). So `K1` asks only that the held id's predicate give
  `Good` at a non-zero value *or* be at a timestamp whose flag message is
  zero (`OkPred`), which the relaxation keeps.
- `vc_k2` (`str w5, [x1]`, value `43`): permitted (a positive share, `Dt`
  pure), and afterwards `K3`: all of `Dt` with maximal write `(43, tw)`,
  `tw` at or below the coherence view of `Dt`.
- `vc_k3` (`ldr w4, [x1]`): the reader keeps `Own43` (all of `Dt`, maximal
  write `(43, tw)`), and under the clean flag the load returns `43`
  (`read_max` on the reader's own resource; the read bound covers `tw`).
- `K1.fence`, `K2.fence`, `K3.fence`: monotone under fences (`FenceLe`).

Phase-1 limits (single-access trees, releases are stores, takes only at
non-forwarded acquire loads) apply; none is binding here.
-/
import Kraken.Promising.SLR.EnvG.TakeAllWr
import Kraken.Promising.SLR.EnvG.TakeVCGen
import Kraken.Promising.SLR.EnvG.TakeSmoke

namespace Kraken.Promising.SLR.EnvG.TakeMp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.EnvG.TakeSmoke

/-! ## The program -/

/-- **The writing reader**: spin on an acquire load of the flag until it is
non-zero, then store `43` to the data and load it back into `W4`. -/
def takeReader : Program := parseAArch64("
spin:
    ldar w3, [x0]
    cbz w3, spin
    mov w5, #43
    str w5, [x1]
    ldr w4, [x1]
done_t:
")

/-- info: 7 -/
#guard_msgs in
#eval takeReader.length

theorem rdPlan_valid : rdPlan.Valid := by decide

/-! ## The predicates -/

/-- **A usable acquire predicate**: at a non-zero flag value it gives `Good`
(all of `Dt`), unless its timestamp is that of a zero flag message (where a
spurious take relaxed it). -/
def OkPred (P : Params) (c : Config isa) (ψ : Pred) : Prop :=
  ∀ v m V R, ψ.P v m V R → BitVec.setWidth 32 v ≠ 0 →
    Good P.Dt V R ∨ ∃ v0, c.mem.read? P.Fl V = some v0 ∧ BitVec.setWidth 32 v0 = 0

theorem OkPred.snap {P : Params} {tid : Nat} {c c' : Config isa} {ψ : Pred} (h : OkPred P c ψ)
    (hs : SnapLe tid c c') : OkPred P c' ψ := fun v m V R hP hv =>
  (h v m V R hP hv).imp id fun ⟨v0, hr, h0⟩ => ⟨v0, hs.read? hr, h0⟩

theorem OkPred.flag {P : Params} {c : Config isa} : OkPred P c P.φ := fun _ _ _ _ hP hv => .inl (hP hv)

/-- Before `ldar w3, [x0]` (the loop invariant): the world (the flag's
release predicate `φ`, `Dt` pure), no forwarding item for `Fl`, and an
acquire id of `Fl` with a usable predicate. -/
def K1 (P : Params) (σ : State isa) : Prop :=
  σ.g.rel P.Fl = P.φ ∧ (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ σ.vs.getFwd P.Fl = none ∧
    ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq P.Fl ι ∧ OkPred P σ.snap (σ.g.acqPred ι)

/-- After the take (before `mov`/`str`): `Dt` pure, all of `Dt`, every write
of `Dt` at or below `vwNew`. -/
def K2 (P : Params) (σ : State isa) : Prop :=
  (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ (σ.r.wr P.Dt).q = 1 ∧ ∀ p, (σ.r.wr P.Dt).X p → p.2 ≤ σ.vs.vwNew

/-- All of `Dt`, with maximal write `(43, tw)`. -/
def Own43 (P : Params) (r : Res) : Prop :=
  (r.wr P.Dt).q = 1 ∧ ∃ tw, (r.wr P.Dt).X (43#128, tw) ∧ ∀ p, (r.wr P.Dt).X p → p.2 ≤ tw

/-- After the store (before `ldr`): `Own43`, with `tw` at or below the
coherence view of `Dt`. -/
def K3 (P : Params) (σ : State isa) : Prop :=
  (σ.r.wr P.Dt).q = 1 ∧ ∃ tw, (σ.r.wr P.Dt).X (43#128, tw) ∧ (∀ p, (σ.r.wr P.Dt).X p → p.2 ≤ tw) ∧
    tw ≤ σ.vs.getCoh P.Dt

theorem K3.own43 {P : Params} {σ : State isa} (h : K3 P σ) : Own43 P σ.r :=
  ⟨h.1, h.2.elim fun tw h => ⟨tw, h.1, h.2.1⟩⟩

/-! ## Fences -/

theorem K1.fence {P : Params} {σ σ' : State isa} (h : K1 P σ) (hf : FenceLe σ σ') : K1 P σ' := by
  unfold K1; rw [hf.g, hf.r, hf.getFwd, hf.snap]; exact h

theorem K2.fence {P : Params} {σ σ' : State isa} (h : K2 P σ) (hf : FenceLe σ σ') : K2 P σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hf.g]; exact h1, by rw [hf.r]; exact h2,
    fun p hp => Nat.le_trans (h3 p (by rw [← hf.r]; exact hp)) hf.vwNew⟩

theorem K3.fence {P : Params} {σ σ' : State isa} (h : K3 P σ) (hf : FenceLe σ σ') : K3 P σ' := by
  unfold K3; rw [hf.r, hf.getCoh]; exact h

/-! ## The VCs -/

/-- **VC K1** (`ldar w3, [x0]` on `EnvGT`): a zero flag keeps the loop
invariant, a non-zero flag takes all of `Dt`. -/
theorem vc_k1 {P : Params} (tid : Nat) (σ : State isa) (h : K1 P σ) :
    ∀ v (σ' : State isa), (ET tid).step (.load .acq false P.f 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → K1 P σ') ∧ (BitVec.setWidth 32 v ≠ 0 → K2 P σ') := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsT hs
  obtain ⟨hrel, hpure, hfw, ι, hlt, hacq1, hok⟩ := h
  have hn := hanc.lt
  have hacq : σ.r.acq P.Fl ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hc : TakeCond Arch.armv8 .acq σ.vs P.Fl tr := ⟨by decide, not_fwded_of_none hfw⟩
  have ha' : a = takeAll P.Fl tr σ.r ga := ha.1 hc
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  have hok' : OkPred P σ'.snap (ga.acqPred ι) := by rw [hanc.acqPred hlt]; exact hok.snap hanc.snap
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨ι', h1, h2, hp⟩ := takeAll_held (l := P.Fl) (tr := tr) (r := σ.r) (g := ga) hacq1 (hanc.acqLen hlt)
    refine ⟨by rw [hrel']; exact hrel, fun w => by rw [hrel']; exact hpure w, by rw [hlv.getFwd]; exact hfw, ι',
      by rw [hg, ha']; exact h2, by rw [hr, ha']; exact h1, ?_⟩
    rw [hg, ha']
    rcases hp with hp | hp
    · rw [hp]; exact hok'
    · rw [hp]
      intro v' m V R hP hv'
      rcases hP with ⟨rfl, -⟩ | hP
      · exact .inr ⟨v, hrd.val, hv⟩
      · exact hok' v' m V R hP hv'
  · obtain ⟨s, hs, hkey, hid, hP⟩ := slot_of_seen (k := (P.Fl, tr)) E hn hacq hrd.val
      (by rw [hanc.rel, hrel]; exact flagPred_impure hv)
    obtain ⟨hq, ts, -, hmax, hts⟩ : Good P.Dt tr s.res := by
      rcases hok' v _ tr s.res hP hv with hG | ⟨v0, hr0, h0⟩
      · exact hG
      · rw [hrd.val] at hr0; cases hr0; exact absurd h0 hv
    obtain ⟨hq', hX'⟩ := takeAll_wr_full hn E hs hkey (by rw [hid]; exact hacq) hq
    have hvw : tr ≤ σ'.vs.vwNew := (hlv.acq (by decide) (not_fwded_of_none hfw)).2
    refine ⟨fun w => by rw [hrel']; exact hpure w, by rw [hr, ha']; exact hq', fun p hp => ?_⟩
    rw [hr, ha'] at hp
    exact Nat.le_trans (hmax p ((hX' p).mp hp)) (Nat.le_trans hts hvw)

/-- **VC K2** (`str w5, [x1]`, `w5 = 43`): the plain store is permitted and
gives `K3`. -/
theorem vc_k2 {P : Params} (tid : Nat) (σ : State isa) (h : K2 P σ) :
    (ET tid).ok (.store .plain false P.d 4 43#128) σ ∧
      ∀ b (σ' : State isa), (ET tid).step (.store .plain false P.d 4 43#128) σ b σ' → K3 P σ' := by
  obtain ⟨hpure, hq, hmax⟩ := h
  refine ⟨⟨rfl, by rw [hq]; decide, fun _ => hpure _, fun hr => by simp [rdPlan, Plan.rel, Plan.find?] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, -, -, hwb, hwv, -, ⟨Q, -, hr⟩, -⟩ := step_storeFactsT hs
  have hr' : σ'.r = σ.r.addW P.Dt (43#128, tw) := by simpa [Plan.after, rdPlan, Plan.rel, Plan.find?] using hr
  refine ⟨by rw [hr', Res.addW_q]; exact hq, tw, ?_, fun p hp => ?_, hwv.coh⟩
  · rw [hr', Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr', Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax p hp) hwb.vwNew)
    · exact Nat.le_refl _

/-- **VC K3** (`ldr w4, [x1]`): the reader keeps `Own43`, and under the
clean flag the load returns its own `43`. -/
theorem vc_k3 {P : Params} (tid : Nat) (σ : State isa) (h : K3 P σ) :
    ∀ v (σ' : State isa), (ET tid).step (.load .plain false P.d 4) σ v σ' →
      Own43 P σ'.r ∧ (σ'.cl → v = 43#128) := by
  intro v σ' hs
  obtain ⟨ga, hanc, -, hcl, tr, hrd, -, a, ha, hr, -⟩ := step_loadFactsT hs
  obtain rfl := takeEff_of_not_acq ha (by decide)
  simp only at hr
  refine ⟨by rw [hr]; exact h.own43, fun hc => ?_⟩
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  obtain ⟨hq, tw, hX, hmax, hcoh⟩ := h
  obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
    ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  exact (read_max E' ht hq hX hmax hrd.val hp hrd.window (Nat.le_trans hcoh (Nat.le_max_right _ _))).2

#print axioms vc_k1
#print axioms vc_k2
#print axioms vc_k3

end Kraken.Promising.SLR.EnvG.TakeMp
