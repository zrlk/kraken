/-
**Part 7: smoke test — a reader that skips a
release still collects its slot** (on `EnvGTU`, `EnvG/TakeUEnv.lean`).

The writer (not proved here) stores the data, then releases the flag twice:
`stlr f := 1` hands all of `Dt` to the reader's acquire id (the slot of the
`f = 1` message), `stlr f := 2` hands over nothing. The reader reads the flag
**once**:
```
 skipReader:
 0 start:
 1   ldar w3, [x0]
 2   sub  w6, w3, #2
 3   cbnz w6, done_s
 4   mov  w5, #43
 5   str  w5, [x1]
 6   ldr  w4, [x1]
 7 done_s:
```
If it reads `2` it has skipped the `f = 1` message, whose slot holds `Dt`.
The original take (`takeAll`, `EnvGT`) takes only the slots of the message
read, so `Dt` stays stranded in the skipped slot and the reader's plain
store has no permission. The cumulative take (`takeUpTo`) collects it.

**The flag's predicate** `skipPred` is memory-dependent (`Pred.P` takes the
memory): at a low word `1` it gives `Good` (all of `Dt`, maximal write
`(1, ts)`, `ts ≤ V`); at a low word `2` it gives nothing but the knowledge
that an `f = 1` message exists below `V`. That message is impure, so it
carries a slot for the reader's id (`slot_of_seen`), whose `skipPred` gives
all of `Dt`; `loadFactsTU_wr_full` (the slot's timestamp is below the
message read) makes `Dt` the reader's.

- `vc_s1` (`ldar w3, [x0]`): a low word `2` takes all of `Dt` (`K2`).
- `vc_s2` (`str w5, [x1]`), `vc_s3` (`ldr w4, [x1]`): as `TakeMp`'s `vc_k2`,
  `vc_k3`, on `EnvGTU`.
- `skipReader_envGTU`: the whole reader by `vcgen` (`cfgEnv_partial`): at
  `done_s`, if `W3 = 2` then `Own43` (all of `Dt`, maximal write `(43, tw)`)
  and, under the clean flag, `W4 = 43`.
- The rule: `skipRuleR` (`ThreadRuleRXGS.ofSafelyEnvGTU`), its no-fault rule
  `skipRuleR_noFault`, and **`skipReader_npSafeP`**: `NPSafeP … G₀
  (K2Scope AllocIds)` from any initial resource and ghost giving the reader
  an acquire id of `Fl` with `skipPred` (the input of `final_of_relWritesJS`).

Not done here: the two-release writer and the
end-to-end `final_of_relPureSafelyS` assembly (a new initial ghost with
`skipPred`).
-/
import Kraken.Promising.SLR.EnvG.TakeUA64
import Kraken.Promising.SLR.EnvG.TakeMp
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.EnvG.SpscCommon

namespace Kraken.Promising.SLR.EnvG.TakeUSkip

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp

/-! ## The program -/

/-- **The skipping reader**: one acquire load of the flag; if it is `2`,
store `43` to the data and load it back into `W4`. -/
def skipReader : Program := parseAArch64("
start:
    ldar w3, [x0]
    sub w6, w3, #2
    cbnz w6, done_s
    mov w5, #43
    str w5, [x1]
    ldr w4, [x1]
done_s:
")

/-- info: 8 -/
#guard_msgs in
#eval skipReader.length

/-- The reader's environment, with cumulatively taking loads. -/
abbrev EU (tid : Nat) : SharedEnv := EnvGTU isa Arch.armv8 tid rdPlan

/-! ## The flag's predicate -/

-- A message read at a memory is read at every extension of it (neutral).
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.read?_prefix ↦ Kraken.Promising.SLR.EnvG.TakeUSkip.read?_prefix]

/-- **The flag's release and acquire predicate**: `Good` at a low word `1`;
at a low word `2`, an `f = 1` message below the view (memory-dependent). -/
def skipPred (P : Params) : Pred where
  P v m V r := (BitVec.setWidth 32 v = 1 → Good P.Dt V r) ∧
    (BitVec.setWidth 32 v = 2 → ∃ t < V, ∃ v1, m.read? P.Fl t = some v1 ∧ BitVec.setWidth 32 v1 = 1)
  mono _ _ _ _ _ hm h := ⟨h.1, fun hv => (h.2 hv).imp fun _ ⟨ht, v1, hr, h1⟩ => ⟨ht, v1, read?_prefix hm hr, h1⟩⟩

theorem skipPred_impure1 {P : Params} {v : Val} (hv : BitVec.setWidth 32 v = 1) : ¬ Pred.Pure (skipPred P) v :=
  fun h => by
    have := ((h default 0).1 hv).1
    simp [Res.unit, Perm.unit] at this

theorem skipPred_impure2 {P : Params} {v : Val} (hv : BitVec.setWidth 32 v = 2) : ¬ Pred.Pure (skipPred P) v :=
  fun h => by
    obtain ⟨t, ht, -⟩ := (h default 0).2 hv
    exact Nat.not_lt_zero _ ht

/-! ## The reader's states -/

/-- Before `ldar w3, [x0]`: the flag's release predicate is `skipPred`, `Dt`
is pure, no forwarding item for `Fl`, and an acquire id of `Fl` with
`skipPred`. -/
def K1 (P : Params) (σ : State isa) : Prop :=
  σ.g.rel P.Fl = skipPred P ∧ (∀ v, Pred.Pure (σ.g.rel P.Dt) v) ∧ σ.vs.getFwd P.Fl = none ∧
    ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq P.Fl ι ∧ σ.g.acqPred ι = skipPred P

theorem K1.fence {P : Params} {σ σ' : State isa} (h : K1 P σ) (hf : FenceLe σ σ') : K1 P σ' := by
  unfold K1; rw [hf.g, hf.r, hf.getFwd]; exact h

/-! ## The VCs -/

/-- **VC S1** (`ldar w3, [x0]` on `EnvGTU`): a low word `2` takes **all of
`Dt`**, from the slot of the skipped `f = 1` message. -/
theorem vc_s1 {P : Params} (tid : Nat) (σ : State isa) (h : K1 P σ) :
    ∀ v (σ' : State isa), (EU tid).step (.load .acq false P.f 4) σ v σ' → BitVec.setWidth 32 v = 2 → K2 P σ' := by
  intro v σ' hs hv
  obtain ⟨ga, hanc, hown, -, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsTU hs
  obtain ⟨rF, E⟩ := hown
  obtain ⟨hrel, hpure, hfw, ι, hlt, hacq1, hι⟩ := h
  have hn := hanc.lt
  have hacq : σ.r.acq P.Fl ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hc : TakeCond Arch.armv8 .acq σ.vs P.Fl tr := ⟨by decide, not_fwded_of_none hfw⟩
  have hrel' : σ'.g.rel = σ.g.rel := by rw [hg, (ha.ghost_le).rel, hanc.rel]
  have hpred : ga.acqPred ι = skipPred P := by rw [hanc.acqPred hlt, hι]
  -- the message read (`f = 2`) knows of an `f = 1` message below it
  obtain ⟨s2, -, -, -, hP2⟩ := slot_of_seen (k := (P.Fl, tr)) E hn hacq hrd.val
    (by rw [hanc.rel, hrel]; exact skipPred_impure2 hv)
  rw [hpred] at hP2
  obtain ⟨t, htlt, v1, hr1, hv1⟩ := hP2.2 hv
  -- whose slot for the reader's id holds all of `Dt`
  obtain ⟨s1, hs1, hk1, hid1, hP1⟩ := slot_of_seen (k := (P.Fl, t)) E hn hacq hr1
    (by rw [hanc.rel, hrel]; exact skipPred_impure1 hv1)
  rw [hpred] at hP1
  obtain ⟨hq, ts, -, hmax, hts⟩ := hP1.1 hv1
  -- and the cumulative take collects it
  obtain ⟨hq', hX'⟩ := loadFactsTU_wr_full ⟨rF, E⟩ hn ha hr hc hs1 hk1 (Nat.le_of_lt htlt)
    (by rw [hid1]; exact hacq) hq
  have hvw : tr ≤ σ'.vs.vwNew := (hlv.acq (by decide) (not_fwded_of_none hfw)).2
  refine ⟨fun w => by rw [hrel']; exact hpure w, hq', fun p hp => ?_⟩
  have := hmax p ((hX' p).mp hp)
  simp only [Time, View] at *
  omega

/-- **VC S2** (`str w5, [x1]`, `w5 = 43`): `TakeMp.vc_k2` (stores of
`EnvGTU` are `EnvGT`'s). -/
theorem vc_s2 {P : Params} (tid : Nat) (σ : State isa) (h : K2 P σ) :
    (EU tid).ok (.store .plain false P.d 4 43#128) σ ∧
      ∀ b (σ' : State isa), (EU tid).step (.store .plain false P.d 4 43#128) σ b σ' → K3 P σ' :=
  vc_k2 tid σ h

/-- **VC S3** (`ldr w4, [x1]`): the reader keeps `Own43`, and under the
clean flag the load returns its own `43` (`TakeMp.vc_k3` on `EnvGTU`). -/
theorem vc_s3 {P : Params} (tid : Nat) (σ : State isa) (h : K3 P σ) :
    ∀ v (σ' : State isa), (EU tid).step (.load .plain false P.d 4) σ v σ' →
      Own43 P σ'.r ∧ (σ'.cl → v = 43#128) := by
  intro v σ' hs
  obtain ⟨ga, hanc, -, hcl, tr, hrd, -, a, ha, hr, -⟩ := step_loadFactsTU hs
  obtain rfl := takeEffU_of_not_acq ha (by decide)
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

#print axioms vc_s1
#print axioms vc_s3

end Kraken.Promising.SLR.EnvG.TakeUSkip
