import WeakCore.TermPoolResplit

/-! # TermHbiPOf (r8 route (A)): the stepper's credits `crS` and its `bufInit` pool premise

Before a thread step of `i` with result `r`, the stepper runs at `crS := crR cr pl i (QS …) i`: the
credits `cr i` plus the pool credit `pl i` at the promises the step discharges below every footprint
message of their label (`QS`).  Here:
* `crS_split`/`stepCrQ_of`: `crS = cr i + plQ` with `plQ` a part of `pl i` off the post promises
  (`StepCrQ`, the members' form);
* `crS_le`/`crS_ge`: the stepper's `hle` (at `cr₁ := cr i + pl i`) and `cr i ≤ crS`;
* `hbiP_of`: the stepper's `HbiP` at the split `cr₀ := cr i`, `plb := plQ`, `plf := pl i`, from the
  pool cover (`PoolCovUL`, `PoolTag`'s second part), `cr i`'s `PromCrK`, the `bufInit` target's
  ownership (`bufInit_ownNP`) and the slot payment (`bufInitHeld`).
-/

namespace TermHbiPOf
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermPool TermPoolStaging TermPoolResplit TermOverCrBII
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The promises whose pool credit moves into the stepper's credits. -/
def QS (Eg : GEnv) (c : Cfg) (i : Nat) (S : AllocLabel → Prop) (th : TTh) (r : Memory × List Ts × TTh) :
    Ts → Prop :=
  fun t => t ∈ th.promises ∧ t ∉ r.2.2.promises ∧ FrGuard (Cut Eg i S) c.mem t

/-- The moved part of `i`'s pool. -/
noncomputable def plQ (pl : Nat → Ts → Res) (i : Nat) (Q : Ts → Prop) : Ts → Res := by
  classical
  exact fun t => if Q t then pl i t else .zero

theorem crS_split (cr pl : Nat → Ts → Res) (i : Nat) (Q : Ts → Prop) (t : Ts) :
    crR cr pl i Q i t = cr i t + plQ pl i Q t := by
  classical
  by_cases hq : Q t
  · rw [crR_pos ⟨rfl, hq⟩]; simp only [plQ, hq, ↓reduceIte]
  · rw [crR_neg fun h => hq h.2]; simp only [plQ, hq, ↓reduceIte]; exact (Res.add_zero _).symm

/-- `crS` in the members' form. -/
theorem stepCrQ_of (Eg : GEnv) (c : Cfg) (cr pl : Nat → Ts → Res) (i : Nat) (S : AllocLabel → Prop) (th : TTh)
    (r : Memory × List Ts × TTh) :
    StepCrQ cr pl i r.2.2.promises (crR cr pl i (QS Eg c i S th r) i) := by
  classical
  refine ⟨plQ pl i (QS Eg c i S th r), crS_split cr pl i _, fun t => ?_, fun t h => ?_⟩
  · by_cases hq : QS Eg c i S th r t
    · right; simp only [plQ, hq, ↓reduceIte]
    · left; simp only [plQ, hq, ↓reduceIte]
  · by_cases hq : QS Eg c i S th r t
    · exact hq.2.1
    · simp only [plQ, hq, ↓reduceIte] at h; exact absurd rfl h

theorem crS_ge (cr pl : Nat → Ts → Res) (i : Nat) (Q : Ts → Prop) (t : Ts) : cr i t ≤ crR cr pl i Q i t := by
  rw [crS_split]; exact Res.le_add_right _ _

/-- The stepper's `hle`: at a discharged, guarded promise the moved credit is the whole pool credit. -/
theorem crS_le {Eg : GEnv} {c : Cfg} {cr pl : Nat → Ts → Res} {i : Nat} {S : AllocLabel → Prop} {th : TTh}
    {r : Memory × List Ts × TTh} {η : TEnv} (hCE : CE η = Cut Eg i S) (t : Ts) (m : Msg)
    (ht : t ∈ th.promises) (ht' : t ∉ r.2.2.promises) (hm : c.mem[t]? = some m)
    (hg : ∀ f mf, f ∈ FpAt (CE η) ⟨m.loc.label, 0⟩ → c.mem[f]? = some mf → mf.loc.label = m.loc.label → t < f) :
    cr i t + pl i t ≤ crR cr pl i (QS Eg c i S th r) i t := by
  have hq : QS Eg c i S th r t := ⟨ht, ht', fun m' hm' => by
    rw [hm] at hm'; cases hm'; rw [← hCE]; exact hg⟩
  rw [crR_pos ⟨rfl, hq⟩]; exact Res.le_refl _

/-- **The stepper's `bufInit` pool premise** at `crS`, `cr₀ := cr i`, `plb := plQ`, `plf := pl i`, `Ok := (· = r)`. -/
theorem hbiP_of {g : G} {Eg : GEnv} {c : Cfg} {cr db pl : Nat → Ts → Res} {i : Nat} {S : AllocLabel → Prop}
    {th : TTh} {r : Memory × List Ts × TTh} {η : TEnv} {H : Res}
    (hth : c.ths[i]? = some th) (hCE : CE η = Cut Eg i S) (htag : PoolTag Eg c pl)
    (hC : TermPlant.PromCrK (CE η) (stOf c.mem c.pairs th) (cr i) (db i))
    (hown : ∀ x b ia v e, th.term = .let_ x (.bufInit b ia v) e → ∀ rt w ad,
      evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
      (∃ cl, Eg.sto ad.label = some cl ∧ cl.owner = some i) ∧ ¬ Eg.pubd ad.label)
    (hheld : ∀ x b ia v e, th.term = .let_ x (.bufInit b ia v) e → ∀ rt w ad,
      evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
      ∃ Sp, MemHeldL (CE η) (stOf c.mem c.pairs th) H Sp ∧
        TermPlant.SlotPayS (CE η) (stOf c.mem c.pairs th) Sp (cr i) (db i) ad.label) :
    TermPlant.HbiP g c.mem c.pairs th η H (crR cr pl i (QS Eg c i S th r) i) (cr i)
      (plQ pl i (QS Eg c i S th r)) (pl i) (db i) (fun r' => r' = r) := by
  classical
  intro x b ia v e hterm rt w ad rti wi he hw _ _ hpf
  obtain ⟨Sp, hHL, hpay⟩ := hheld x b ia v e hterm rt w ad he hw hpf
  obtain ⟨⟨cl, hcl, hcown⟩, hnp⟩ := hown x b ia v e hterm rt w ad he hw
  have hcov := (poolTag_iff.1 htag).2
  have hGs : ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
      (∀ t, Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤ pl i t) ∧
      ∀ c0, (CE η).sto ad.label = some c0 →
        (∀ x ∈ Gs, TermPlant.CrItemQP (CE η) (stOf c.mem c.pairs th) (pl i) ad.label c0 x) ∧
        ∀ o tw, PredU (CE η) ⟨ad.label, o⟩ → ¬ VisU (CE η) ⟨ad.label, o⟩ →
          TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨ad.label, o⟩ tw → FirstW c.mem ⟨ad.label, o⟩ tw →
          TermPlant.OverT (CE η) (stOf c.mem c.pairs th) ⟨ad.label, o⟩ tw →
          ∃ x ∈ Gs, ∃ usS j, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS j (o - x.2.1) ∧
            x.2.2.2.2.2 j = true := by
    cases hs : (CE η).sto ad.label with
    | none => exact ⟨[], fun _ _ => Nat.zero_le _, fun c0 h => by cases h⟩
    | some c1 =>
      have hs' : (Cut Eg i S).sto ad.label = some c1 := by rw [← hCE]; exact hs
      have e1 : c1 = cl := Option.some.inj ((cutSto_sub hs').symm.trans hcl)
      subst e1
      have hpf' : Eg.pfr ad.label ≠ none := by rw [hCE] at hpf; exact hpf
      obtain ⟨Gs, hsum, hit, hcv⟩ := hcov i th S hth ad.label c1 hs' hcown hpf' hnp
      refine ⟨Gs, hsum, fun c0 h0 => ?_⟩
      cases h0
      rw [hCE]
      exact ⟨hit, hcv⟩
  obtain ⟨Gs, hsum, hcell⟩ := hGs
  refine ⟨Sp, Gs, crS_split cr pl i _, hC, fun t h0 => ?_, fun r' _ hr' t m ht ht' hm hg => ?_, hHL, hpay,
    hsum, hcell⟩
  · by_cases hq : QS Eg c i S th r t
    · exact ⟨hq.1, fun r' _ hr' => by rw [hr']; exact hq.2.1⟩
    · simp only [plQ, hq, ↓reduceIte] at h0; exact absurd rfl h0
  · subst hr'
    have hq : QS Eg c i S th r' t := ⟨ht, ht', fun m' hm' => by
      rw [hm] at hm'; cases hm'; rw [← hCE]; exact hg⟩
    simp only [plQ, hq, ↓reduceIte]; exact Res.le_refl _

end TermHbiPOf

#print axioms TermHbiPOf.stepCrQ_of
#print axioms TermHbiPOf.crS_le
#print axioms TermHbiPOf.hbiP_of
