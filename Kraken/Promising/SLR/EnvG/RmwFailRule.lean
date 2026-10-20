/-
The failing-RMW route, part 1: **`NPSafe` with a fulfilling step
guard**, and the rule interface whose `wp` may leave the in-flight promise
alive. ISA-neutral. Nothing imports it.

## Why

release-RMW limit 1 (`KNOWN_GAPS.md`, "Release RMWs"): a release-kind RMW that
fulfils a prepaid (pending) promise must never fail. The root cause is in
`NPSafe`'s step conjunct (`Promising/PromiseSafe.lean`, `NPSafe`): after a
prepay, the thread's next step may be *any* outcome of the in-flight
instruction that leaves no promise dead (`c'.WfProm tid`). A failing CAS
(`casal`, x64 `lock cmpxchg`) that read an *older* message `tr < ts` leaves
the pending promise `ts` outstanding and not dead (`coh l`, `vwNew` stay
below `ts`), and the thread's resource has already paid the release. Such a
path can reach a final configuration (the retry loop's next CAS reads a later
message and fulfils `ts`), so no deadness or certification argument removes
it. Phase 1's link (`LinkS`/`LinkR`, `PostS`: "no own pending promise after
the instruction") and `ThreadRuleRX.wp` (`WpPostR`: `Inv` after every live
outcome) cannot carry an instruction boundary with a paid, unfulfilled
release.

Theorem 1′ never needs that outcome. In its annotated run a thread with a
pending promise is *advanced*: it stands just before the fulfilling
instruction `F`, and its next `np` micro-step is `F` itself with the real
outcome, which removes every pending promise of the thread
(`SLR/Theorem1Proof.lean`, `caseNow'`, the status field `hful` used for
`hnopend`; the failing CAS of the example is *replayed before* the prepay,
at `pf = none`). So `NPSafe`'s step conjunct may assume:

- **`StepFul`**: every own promise pending at `g₁` is gone from the thread
  after the step.

## Contents

- `StepFul`, `NPSafeF` (`NPSafe` whose step conjunct also assumes `StepFul`),
  `NPSafe.toF` (every `NPSafe` proof is an `NPSafeF` proof: the old notion is
  the stronger one).
- `WpPostRF` (`WpPostR`, or the in-flight promise is still outstanding),
  `ThreadRuleRXF` (`ThreadRuleRX` with `WpPostRF`), `ThreadRuleRX.toF`,
  `NPSafeF.of_ruleRXF`.
- `Theorem1FChain`: the Theorem 1′ chain for `NPSafeF` (the generic chain
  with the step guard supplied at its two `stepAt` sites), as a `Prop`.
  **Closed**: `theorem1FChain` (`EnvG/RmwFailChain.lean`).
-/
import Kraken.Promising.SLR.ThreadRuleX
import Kraken.Promising.SLR.Theorem1Proof

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## `NPSafe` with the fulfilling step guard -/

/-- **The fulfilling step guard**: every promise of `tid` pending at `g₁`
before the step is no longer a promise of `tid` after it. -/
def StepFul (M : ResModel I) (tid : Nat) (c₁ : Config I) (g₁ : M.Ghost) (c' : Config I) : Prop :=
  ∀ t t', c₁.threads[tid]? = some t → c'.threads[tid]? = some t' → ∀ ts ∈ t.prom, M.pendingAt g₁ ts →
    ts ∉ t'.prom

section Safety

variable (M : ResModel I) (A : Arch) (B : Config I → M.R → M.Ghost → Prop) (tid : Nat)

/-- **`NPSafe` with the fulfilling step guard**: `NPSafe`
(`Promising/PromiseSafe.lean`) whose step conjunct also assumes `StepFul`
(a prepaid promise of `tid` is fulfilled by `tid`'s next step). The body is
otherwise a verbatim copy. -/
def NPSafeF : Nat → Nat → Prop → Config I → M.R → M.Ghost → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, 0, cl, c, r, g => ∀ m, NPSafeF n m cl c r g
  | n + 1, m + 1, cl, c, r, g =>
    ∀ c₁ g₁, EnvExt tid c c₁ → M.ghostLe g g₁ →
    (cl → c₁.Done tid → B c₁ r g₁) ∧
    (∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → NPStepBy A tid c₁ c' →
      c₁.MachInv → c₁.WfProm tid → c'.WfProm tid →
      (∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      StepFul M tid c₁ g₁ c' →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
        (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
        NPSafeF (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧ M.acqLe r' g' r g₁ ∧
        (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
        (∀ b, b ≤ c₁.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b) ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b)) ∧
    (∀ (rF : Nat → M.R) (t₁ : Thread I) (w : Msg), c₁.threads[tid]? = some t₁ →
      M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁ → c₁.MachInv →
      (∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts) →
      { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }.RelFulfilsLive A tid
        (c₁.mem.append { w with tid }).2 (c₁.mem.append { w with tid }).1 →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafeF (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        (∀ b, b ≤ c₁.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b) ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b))
termination_by n m => (n, m)

end Safety

/-- **Every `NPSafe` proof is an `NPSafeF` proof**: the step guard is an
extra hypothesis. (So `NPSafeF` is the weaker per-thread notion; the existing
rules, which produce `NPSafe`, produce it too.) -/
theorem NPSafe.toF {M : ResModel I} {A : Arch} {B : Config I → M.R → M.Ghost → Prop} {tid : Nat} :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : M.R) (g : M.Ghost), NPSafe M A B tid n m cl c r g →
      NPSafeF M A B tid n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeF]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafe] at h
    rw [NPSafeF]
    exact fun m => NPSafe.toF n m cl c r g (h m)
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafe] at h
    rw [NPSafeF]
    intro c₁ g₁ he hg
    obtain ⟨hd, hs, hp⟩ := h c₁ g₁ he hg
    refine ⟨hd, fun rF c' E hst hinv hwf hwf' hnp _ => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨r', g', E', hg', hkeep, hnew, hs', hacq, hown, hK2, hK1⟩ := hs rF c' E hst hinv hwf hwf' hnp
      exact ⟨r', g', E', hg', hkeep, hnew, NPSafe.toF (n + 1) m _ c' r' g' hs', hacq, hown, hK2, hK1⟩
    · obtain ⟨r', g', E', hg', hpend, hkeep, hnew, hs', hacq, hK2, hK1⟩ := hp rF t₁ w ht₁ E hinv hnp hrel
      exact ⟨r', g', E', hg', hpend, hkeep, hnew, NPSafe.toF (n + 1) m _ _ r' g' hs', hacq, hK2, hK1⟩
termination_by n m => (n, m)

/-! ## The rule interface with a live in-flight escape -/

/-- **`WpPostR` with the in-flight escape**: either an own promise pending at
the instruction's start is still outstanding at the outcome (the in-flight
release RMW failed; `StepFul` excludes the outcome), or `WpPostR`. -/
def WpPostRF (Inv : Prop → Config I → Res → Ghost → Prop) (cl : Prop) (c : Config I) (tid : Nat) (r : Res)
    (g : Ghost) (t : Thread I) : I.State → Res → Ghost → Ctx → Prop :=
  fun st r' g' cx' => (∃ ts ∈ t.prom, ts ∈ g.pend ∧ ts ∈ cx'.prom) ∨ WpPostR Inv cl c tid r g t st r' g' cx'

/-- **A per-thread rule whose `wp` may leave the in-flight promise alive**:
`ThreadRuleRX` with `WpPostRF` in place of `WpPostR`. It gives `NPSafeF`
(`NPSafeF.of_ruleRXF`), not `NPSafe`. -/
structure ThreadRuleRXF (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostRF Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **Every `ThreadRuleRX` is a `ThreadRuleRXF`** (the right disjunct of
`WpPostRF`). -/
def ThreadRuleRX.toF {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) : ThreadRuleRXF A B tid where
  Inv := R.Inv
  done := R.done
  wp rF t tree h he hg ht hex E hm hwf hnp :=
    EvTree.EraseWPRD.mono (fun _ _ _ _ h => .inr h) tree _ _ _ (R.wp rF t tree h he hg ht hex E hm hwf hnp)
  prepay := R.prepay

/-- **`NPSafeF` from a `ThreadRuleRXF`** (`NPSafe.of_ruleRX`; the escape
outcome contradicts `StepFul`). -/
theorem NPSafeF.of_ruleRXF {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRXF A B tid) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R) (g : (model I).Ghost), R.Inv cl c r g →
      NPSafeF (model I) A B tid n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeF]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafeF]
    exact fun m => NPSafeF.of_ruleRXF R n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafeF]
    intro c₁ g₁ he hg
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp hful => ?_,
      fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E', hR⟩ := Erase.npStepRD
        (Post := fun t => WpPostRF R.Inv (cl ∧ Erase (setRes rF tid r) g₁ (fun _ => False) c₁) c₁ tid r g₁ t)
        hinv E hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E hinv hwf (hnp t ht))
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      rcases hpost with ⟨ts, hts, hpd, hts'⟩ | hpost
      · exact absurd ((finishInstr_relKey hth).1 ▸ hts') (hful t t' ht ht' ts hts hpd)
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' := hfin t' hth hdead
      refine ⟨r', g', E', hg', ?_, hnew, NPSafeF.of_ruleRXF R (n + 1) m _ _ r' g' hinv', hacq,
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
      exact ⟨r', g', E', hg', hpend, hkeep, hnew, NPSafeF.of_ruleRXF R (n + 1) m _ _ r' g' h', hacq, hk1, hk2⟩
termination_by n m => (n, m)

/-! ## The open part: Theorem 1′ for `NPSafeF` -/

/-- **Theorem 1′ (pure-promise form) for `NPSafeF`** (`Prop`; proved as
`theorem1FChain`, `EnvG/RmwFailChain.lean`):
`Theorem1IIPure` (`SLR/Theorem1Proof.lean`) with the per-thread hypothesis
`NPSafeF` in place of `NPSafe`. Expected proof: the generic chain
(`NPSafeP`, `SLR/NPSafeP.lean` ff.) with one more parameter, the step guard,
supplied at its two `stepAt` sites — `caseNow'` (`Theorem1Proof.lean`, from
the thread's status: not advanced, so no own pending promise, `hnp0`; or
advanced, and the real step is `F`, which fulfils every pending promise,
`hful`; exactly the argument of `hnopend` there) and the replay steps of
`caseD1'` (`Theorem1D1.lean`, same status argument). That edits existing
chain files, which this prototype could not do; did (`StepGuard`,
`NPSafePS` in `SLR/NPSafeP.lean`). -/
def Theorem1FChain (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    PromisePure A fuel states initMem g.rel →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafeF (model I) A B tid n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', (VirtualRel.ii A).rel c v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- **The open chain implies the existing Theorem 1′** (`NPSafe.toF`): proving
`Theorem1FChain` loses nothing. -/
theorem theorem1IIPure_of_F [I.LawfulState] {A : Arch} {fuel : Nat} (h : Theorem1FChain (I := I) A fuel) :
    Theorem1IIPure (I := I) A fuel :=
  fun B states initMem rF g hNT E hp hpure hs =>
    h B states initMem rF g hNT E hp hpure fun tid htid n m => NPSafe.toF n m _ _ _ _ (hs tid htid n m)

end Kraken.Promising.SLR.EnvG
