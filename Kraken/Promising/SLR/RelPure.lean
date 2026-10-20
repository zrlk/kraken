/-
Conjunct (i) of option (A): **release mode only by release
writes**. No
existing definition is changed; everything here is a new, separate predicate.
Everything in this file is proved (no `sorry`).

## Two forms of (i)

- **Witness form** (`RelMark`, `EvTree.EraseWPRDK`, `ThreadRuleRXK`): every
  key the ghost adds to `relMsgs` at a write event is added by a write of
  effective kind `.rel`. This is the B1 note's (i). It is a statement about
  the *existential witness* `g'` of the erasure WP, so it is **not a
  consequence of `ThreadRuleRX`**: the interface admits rules whose `wp`
  marks a plain store's message release (B1's counterexample is a
  `ThreadRuleR`, hence a `ThreadRuleRX` by `ThreadRuleR.toRX`). It must be a
  new rule obligation (`ThreadRuleRXK.wpK`). For a rule whose trees have no
  non-release write at all (TSO, NT-free; or no writes) it follows from the
  existing `wp` (`EvTree.EraseWPRD.toK`, `ThreadRuleRX.toK`). For a rule with
  plain stores (MP's writer, the SWP worker) the witness is hidden inside the
  cell proofs, so `wpK` needs every write cell re-proved through `K`
  variants of the store/RMW shapes (`SLR/ReachRules.lean`, `RuleShapes`,
  `RmwPend*`).
- **Witness-free form** (`RelPure`): at every state the rule's
  `wp` is asked about, the next instruction's non-release writes write values
  that are pure for the current release predicates. This is what (A)
  consumes (`pure_of_relMark` shows the witness form implies it at every
  executable fresh non-release write), it is cheap, and it is proved for all
  four rules in `RelPureA64.lean` / `RelPureX64.lean`.

## Contents

- `RelMark`, `pure_of_relMark` (the consumption: a fresh non-release write
  under `RelMark` writes a pure value).
- `EvTree.EraseWPRDK`, `EvTree.EraseWPRDK.toD`, `EvTree.EraseWPRD.toK`.
- `ThreadRuleRXK`, `NoNonRel`, `ThreadRuleRX.toK`.
- `RelPure`, `relPure_of_noNonRel`, `relFulfilsLive_of_relPure` (the consumption: at an
  invariant state, an instruction removing a promise with an impure message,
  leaving no promise dead, is a live release fulfilment).
- `ReplayConcl`, `fulfilCell_of_replay`, `promisePure_of_replay`: the proved
  reduction of (A) to a replay lemma (`ReplayConcl`) and `RelPure`, through
  `FulfilCell` (`PromisePureGeneral.lean`). The replay lemma itself is open
  (`KNOWN_GAPS.md`, "General `PromisePure` (option (A))").
-/
import Kraken.Promising.SLR.PromisePureGeneral
import Kraken.Promising.SLR.ThreadRuleX

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## (i), witness form -/

/-- **(i) for one write event** of effective kind `k`, ghost `g ↦ g'`: every
key added to `relMsgs` is added by a release write. -/
def RelMark (k : StoreKind) (g g' : Ghost) : Prop :=
  ∀ key ∈ g'.relMsgs, key ∉ g.relMsgs → k = .rel

theorem relMark_of_rel {g g' : Ghost} : RelMark .rel g g' := fun _ _ _ => rfl

/-- A key at a timestamp beyond the memory is in no erased ghost's
`relMsgs` (`Erase.relExists`). -/
theorem not_relMsgs_fresh {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {l : Loc} {ts : Time} (hts : c.mem.last < ts) : (l, ts) ∉ g.relMsgs := by
  intro h
  obtain ⟨v, hv⟩ := E.relExists _ h
  unfold Memory.read? at hv
  split at hv
  · omega_t
  · split at hv
    · next w hw => have := c.mem.last_le_of_get?_eq_some hw; omega_t
    · cases hv

/-- **The consumption of (i)**: a non-release write of `v` to `l` at a
timestamp beyond the pre-state memory (a fresh write, e.g. the target's
write at the break event of `Sim.SimInvP.brk`), whose ghost change satisfies
`RelMark`, leaves its message out of release mode, so erasure after it makes
`v` pure. -/
theorem pure_of_relMark {rF rF' : Nat → Res} {g g' : Ghost} {T T' : Nat → Prop} {c c' : Config I}
    (E : Erase rF g T c) (E' : Erase rF' g' T' c') {k : StoreKind} (hm : RelMark k g g') (hk : k ≠ .rel)
    {l : Loc} {ts : Time} {v : Val} (hts : c.mem.last < ts) (hv : c'.mem.read? l ts = some v) :
    Pred.Pure (g'.rel l) v :=
  E'.pure l ts v hv fun h => hk (hm _ h (not_relMsgs_fresh E hts))

/-- **Erasure WP with dead branches and (i)**: `EvTree.EraseWPRD` whose
write nodes also establish `RelMark` for the write's effective kind. -/
def _root_.Kraken.Promising.EvTree.EraseWPRDK (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res)
    (T : Nat → Prop) (c : Config I) (t : Thread I) {σ : Type} (Post : σ → Res → Ghost → Ctx → Prop) :
    EvTree σ → Res → Ghost → Ctx → Prop
  | .done s, r, g, cx => Post s r g cx
  | .fault _, _, _, _ => True
  | .choose _ k, r, g, cx => ∀ i, EvTree.EraseWPRDK A tid iv rF T c t Post (k i) r g cx
  | .load k xcl l ret, r, g, cx => ∀ x ∈ readSuccs A iv cx k xcl l,
      EvTree.EraseWPRDK A tid iv rF T c t Post (ret x.2.1) r g x.2.2
  | .store k xcl l v ret, r, g, cx =>
      (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl l v (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
        ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
        cx'.Overtaken ∨ ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
          RelMark (A.storeKind k) g g' ∧ EvTree.EraseWPRDK A tid iv rF T c t Post (ret true) r' g' cx') ∧
      (xcl = true → EvTree.EraseWPRDK A tid iv rF T c t Post (ret false) r g (xclFailCtx cx l))
  | .fence k ret, r, g, cx => EvTree.EraseWPRDK A tid iv rF T c t Post (ret ()) r g (fenceStep cx k)
  | .rmw k noRet l op ret, r, g, cx =>
      ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
        (op x.2.1 = none → EvTree.EraseWPRDK A tid iv rF T c t Post (ret x.2.1) r g (fenceOptCtx A x.2.2)) ∧
        ∀ new, op x.2.1 = some new →
          ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
            ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
            cx'.Overtaken ∨ ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' (rmwAfter A k noRet l cx') ∧
              RelMark (A.storeKind (A.rmwKind k).storeKind) g g' ∧
              EvTree.EraseWPRDK A tid iv rF T c t Post (ret x.2.1) r' g' (rmwAfter A k noRet l cx')

section WPRDK

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type}

/-- `EraseWPRDK` is a strengthening of `EraseWPRD`. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRDK.toD {Post : σ → Res → Ghost → Ctx → Prop} (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPRDK A tid iv rF T c t Post r g cx → tree.EraseWPRD A tid iv rF T c t Post r g cx := by
  induction tree with
  | done s => exact fun r g cx h => h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih => exact fun r g cx h x hx => ih x.2.1 r g x.2.2 (h x hx)
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    rcases h.1 cx' hc E hi hm with ho | ⟨r', g', E', hR, -, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    rcases (h x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', E', hR, -, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih x.2.1 r' g' _ hw⟩

/-- **(i) for free when the tree has no non-release write** (every store and
RMW write of effective kind `.rel`: `EvTree.RelWrites A (fun _ _ => False)`;
e.g. TSO and NT-free, `EvTree.NoNT.relWrites`, or no writes at all): every
`EraseWPRD` proof is an `EraseWPRDK` proof. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRD.toK {Post : σ → Res → Ghost → Ctx → Prop} (tree : EvTree σ) :
    ∀ r g cx, tree.RelWrites A (fun _ _ => False) →
      tree.EraseWPRD A tid iv rF T c t Post r g cx → tree.EraseWPRDK A tid iv rF T c t Post r g cx := by
  induction tree with
  | done s => exact fun r g cx _ h => h
  | fault _ => exact fun _ _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx hR h i => ih i r g cx (hR i) (h i)
  | load k xcl l ret ih => exact fun r g cx hR h x hx => ih x.2.1 r g x.2.2 (hR _) (h x hx)
  | store k xcl l v ret ih =>
    intro r g cx hR h
    have hk : A.storeKind k = .rel := Classical.byContradiction fun hne => hR.1 hne
    refine ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (hR.2 false) (h.2 hx)⟩
    rcases h.1 cx' hc E hi hm with ho | ⟨r', g', E', hRs, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hRs, fun _ _ _ => hk, ih true r' g' cx' (hR.2 true) hw⟩
  | fence k ret ih => exact fun r g cx hR h => ih () r g _ (hR ()) h
  | rmw k noRet l op ret ih =>
    intro r g cx hR h x hx
    refine ⟨fun hop => ih x.2.1 r g _ (hR.2 _) ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    have hk : A.storeKind (A.rmwKind k).storeKind = .rel :=
      Classical.byContradiction fun hne => hR.1 hne x.2.1 new hop
    rcases (h x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', E', hRs, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hRs, fun _ _ _ => hk, ih x.2.1 r' g' _ (hR.2 _) hw⟩

end WPRDK

/-- **A rule with (i)**: `ThreadRuleRX` whose `wp` also establishes
`RelMark` at every write (`EvTree.EraseWPRDK`). The prepay conjunct needs no
change for (A): a prepaid promise is fulfilled by a release
(`Thread.RelFulfilsLive`). -/
structure ThreadRuleRXK (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat)
    extends ThreadRuleRX A B tid where
  wpK : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRDK A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)

/-- The trees a rule's `wp` is asked about have no non-release write. -/
def NoNonRel {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) : Prop :=
  ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (t : Thread I) (tree : EvTree I.State),
    R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t → I.exec t.st = some tree →
    tree.RelWrites A (fun _ _ => False)

/-- **(i) for a rule without non-release writes** (TSO NT-free, or no
writes): its existing `wp` already satisfies `RelMark`. -/
def ThreadRuleRX.toK {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) (h : NoNonRel R) : ThreadRuleRXK A B tid :=
  { R with
    wpK := fun rF t tree hI he hg ht hex E hinv hwf hnp =>
      EvTree.EraseWPRD.toK tree _ _ _ (h t tree hI he hg ht hex) (R.wp rF t tree hI he hg ht hex E hinv hwf hnp) }

/-! ## (i), witness-free form -/

/-- **(i‴), witness-free**: at every state the rule's `wp` is asked about,
the next instruction's non-release writes write values pure for the current
release predicates. No ghost witness is involved. -/
def RelPure {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) : Prop :=
  ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (t : Thread I) (tree : EvTree I.State),
    R.Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t → I.exec t.st = some tree →
    tree.RelWrites A (fun l v => Pred.Pure (g.rel l) v)

theorem relPure_of_noNonRel {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop}
    {tid : Nat} (R : ThreadRuleRX A B tid) (h : NoNonRel R) : RelPure R :=
  fun t tree hI he hg ht hex => (h t tree hI he hg ht hex).mono fun _ _ hf => hf.elim

/-- **The consumption of (i‴)**: at a state the rule's `wp` is asked about,
an instruction step that removes the promise `ts`, whose message is impure,
and leaves no promise dead, is a live release fulfilment of `ts`. (This is
exactly what (A) needs at the fulfilling step `f`, *if* the replay reaches
`f` in an invariant state.) -/
theorem relFulfilsLive_of_relPure [I.LawfulState] {A : Arch}
    {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat} (R : ThreadRuleRX A B tid) (hR : RelPure R)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (hI : R.Inv cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) {t : Thread I} (ht : c.threads[tid]? = some t)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {ts : Time} (hin : ts ∈ t.prom) (hout : ts ∉ o.thread.prom) {w : Msg}
    (hw : c.mem.get? ts = some w) (hb : ¬ Pred.Pure (g.rel w.loc) w.val)
    (hlive : o.thread.hasDeadPromise o.mem = false) : t.RelFulfilsLive A tid ts c.mem := by
  cases hex : I.exec t.st with
  | none => unfold stepOne at hstep; rw [hex] at hstep; cases hstep
  | some tree =>
    exact stepOne_relFulfilsLive_of_relWrites A hstep ho hex (hR t tree hI he hg ht hex) hin hout hw hb hlive

/-! ## (A) reduced to a replay lemma -/

variable {A : Arch} {fuel : Nat} in
/-- **The conclusion of the replay**: at every held step `f`, `j`'s source
state is the state of an invariant instance of `j`'s rule, in some
configuration (the hybrid at `f`), for a ghost with release predicates
`rel`. -/
def ReplayConcl (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val))
    (rel : Loc → Pred) {B : Nat → Config I → (model I).R → (model I).Ghost → Prop}
    (R : (j : Nat) → ThreadRuleRX A (B j) j) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J f j t pw, J < f → f < π.len → PromStep π J j t pw → HeldOn π J f j ((π.cfg J).mem.last + 1) →
    ∀ tf, (π.cfg f).threads[j]? = some tf →
      ∃ (cl : Prop) (c₀ c' : Config I) (r : Res) (g₀ g : Ghost) (t' : Thread I),
        (R j).Inv cl c₀ r g₀ ∧ EnvExt j c₀ c' ∧ g₀.Le g ∧ g₀.rel = rel ∧ c'.threads[j]? = some t' ∧
          t'.st = tf.st

variable {A : Arch} {fuel : Nat} in
/-- **`ReplayConcl` and `RelPure` give `FulfilCell`.** -/
theorem fulfilCell_of_replay [I.LawfulState] {states : List I.State} {initMem : List (Loc × Val)}
    {rel : Loc → Pred} {B : Nat → Config I → (model I).R → (model I).Ghost → Prop}
    (R : (j : Nat) → ThreadRuleRX A (B j) j) (hR : ∀ j, RelPure (R j))
    (hrep : ReplayConcl A fuel states initMem rel R) : FulfilCell A fuel states initMem rel := by
  intro π h0 hfin J f j t pw hJf hf hps hheld tf tree htf hex
  obtain ⟨cl, c₀, c', r, g₀, g, t', hI, he, hle, hrel, ht', hst⟩ := hrep π h0 hfin J f j t pw hJf hf hps hheld tf htf
  have h := hR j t' tree hI he hle ht' (by rw [hst]; exact hex)
  rw [hle.rel, hrel] at h
  exact h

variable {A : Arch} {fuel : Nat} in
/-- **(A), conditional on `ReplayConcl`**: `PromisePure` from the rules'
`RelPure` and the replay. -/
theorem promisePure_of_replay [I.LawfulState] {states : List I.State} {initMem : List (Loc × Val)}
    {rel : Loc → Pred} {B : Nat → Config I → (model I).R → (model I).Ghost → Prop}
    (R : (j : Nat) → ThreadRuleRX A (B j) j) (hR : ∀ j, RelPure (R j))
    (hrep : ReplayConcl A fuel states initMem rel R) : PromisePure A fuel states initMem rel :=
  promisePure_of_fulfilCell (fulfilCell_of_replay R hR hrep)

end Kraken.Promising.SLR
