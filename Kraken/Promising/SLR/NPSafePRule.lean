/-
**Prototype.** The rule interface with a generic
prepay guard: `ThreadRuleRXG G` is `ThreadRuleRX` (`SLR/ThreadRuleX.lean`)
whose `prepay` field is guarded by `G` instead of `Thread.RelFulfilsLive`,
and `NPSafeP.of_ruleRXG` is a verbatim copy of `NPSafe.of_ruleRX` (only
names changed). Every existing rule is a `ThreadRuleRXG G₀` with the same
fields (`ThreadRuleRX.toG₀`), so it gives `NPSafeP G₀ K` for every frame
`K ⊇ K2₀`; a rule for the fence-aware guard `GF` must discharge `prepay`
for every `GF` promise (the real per-program work).

Nothing imports this file.
-/
import Kraken.Promising.SLR.ThreadRuleX
import Kraken.Promising.SLR.NPSafeP

namespace Kraken.Promising.SLR

variable {I : ISA}

structure ThreadRuleRXG (G : PrepayGuard I) (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    G A tid (c.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
      (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **`NPSafe` from a `ThreadRuleRX`.** The induction of `NPSafe.of_inv`,
with the step from `Erase.npStepRD` (its `c'.WfProm tid` is the step's). -/
theorem NPSafeP.of_ruleRXG {G : PrepayGuard I} {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRXG G A B tid) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R) (g : (model I).Ghost), R.Inv cl c r g →
      NPSafeP (model I) A B tid G (K2₀ (model I)) n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafeP]
    exact fun m => NPSafeP.of_ruleRXG R n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafeP]
    intro c₁ g₁ he hg
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E', hR⟩ := Erase.npStepRD
        (Post := fun t => WpPostR R.Inv (cl ∧ Erase (setRes rF tid r) g₁ (fun _ => False) c₁) c₁ tid r g₁ t)
        hinv E hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E hinv hwf (hnp t ht))
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' := hfin t' hth hdead
      refine ⟨r', g', E', hg', ?_, hnew, NPSafeP.of_ruleRXG R (n + 1) m _ _ r' g' hinv', hacq,
        fun w hw => hown w (written_cx ht (finishInstr_relKey hth).1 hw), hR.1, ?_⟩
      · rintro ts hts ⟨i, ti, hi, htsi⟩
        refine hkeep ts hts ?_
        rw [Config.withThread_get? c₁ t' cx'.mem hn] at hi
        split at hi
        · next he' =>
          subst he'
          cases hi
          exact .inl ((finishInstr_relKey hth).1 ▸ htsi)
        · next he' => exact .inr ⟨i, ti, Ne.symm he', hi, htsi⟩
      · intro b hb hv x hx
        exact hR.finish hth b hb (hv t' ht') x hx
    · obtain ⟨r', g', E', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        R.prepay rF t₁ w h he hg ht₁ E hinv hnp hrel
      exact ⟨r', g', E', hg', hpend, hkeep, hnew, NPSafeP.of_ruleRXG R (n + 1) m _ _ r' g' h', hacq, hk1, hk2⟩
termination_by n m => (n, m)

/-- Every existing rule is a `ThreadRuleRXG G₀`, field for field. -/
def ThreadRuleRX.toG₀ {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) : ThreadRuleRXG G₀ A B tid where
  Inv := R.Inv
  done := R.done
  wp := R.wp
  prepay := R.prepay

/-- `NPSafe.of_ruleRX` recovered from the generic copy. -/
example {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat} (R : ThreadRuleRX A B tid)
    (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R) (g : (model I).Ghost) (h : R.Inv cl c r g) :
    NPSafe (model I) A B tid n m cl c r g := by
  have := NPSafeP.of_ruleRXG R.toG₀ n m cl c r g h
  rwa [NPSafeP_G₀_K₀] at this

#print axioms NPSafeP.of_ruleRXG

end Kraken.Promising.SLR
