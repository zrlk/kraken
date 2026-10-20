/-
**The `GHyb` transfer.** Every existing rule with a
witness-free (i‴) (`RelPure`, `SLR/RelPure.lean`) is a rule for the hybrid
prepay guard `GHyb rel` (`SLR/NPSafePFence.lean`), with no new prepayment.

`GHyb rel` asks for a prepayment of a promise `ts` when the next instruction
can fulfil it with a live release (`Thread.RelFulfilsLive`, the current
guard), *or* with a live fence-released store (`Thread.RelFulfilsLiveF`)
while the message at `ts` is impure for `rel`. The second disjunct collapses
into the first for a rule whose non-release writes are pure: the fulfilling
write writes the promised message (`writeSuccs_unpromise`), so a non-release
fulfilling write would write an impure value, contradicting `RelWrites`.
Hence the fulfilling write is a release, i.e. the first disjunct
(`EvTree.RelFulfilsLiveF.toLive_of_relWrites`), and the rule's existing
`prepay` field applies.

- `EvTree.RelFulfilsLiveF.toLive_of_relWrites`,
  `Thread.RelFulfilsLiveF.toLive_of_relWrites`: the collapse.
- `GHyb.toG₀`: `GHyb rel` is `G₀` at a thread whose next instruction's
  non-release writes are pure for `rel`.
- `ThreadRuleRX.toHyb`: a `ThreadRuleRX` with `RelPure` is a
  `ThreadRuleRXG (GHyb rel)`, with invariant `R.Inv ∧ g.rel = rel`
  (`Ghost.Le` keeps `rel`).
- `NPSafeP.of_relPure`: hence `NPSafeP (GHyb g.rel) K2₀` at every invariant
  state.
- The four rules: `Mp.mpW_npSafeP_hyb`, `Mp.mpR_npSafeP_hyb`,
  `SwpInv.swp_npSafeP_hyb` (`SLR/NPSafePHybA64.lean`) and
  `X64SpinInv.spin_npSafeP_hyb` (`SLR/NPSafePHybX64.lean`).
-/
import Kraken.Promising.SLR.NPSafePRule
import Kraken.Promising.SLR.NPSafePFence
import Kraken.Promising.SLR.RelPure
import Kraken.Promising.SLR.NPSafePInst

namespace Kraken.Promising

variable {I : ISA}

/-- **A fence-aware live fulfilment of an impure message, by a tree whose
non-release writes are pure, is a live release fulfilment**: the fulfilling
write writes the message at `ts` (`writeSuccs_unpromise`), so it is not a
non-release write. -/
theorem EvTree.RelFulfilsLiveF.toLive_of_relWrites {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time}
    {Q : Loc → Val → Prop} {w : Msg} {σ : Type} :
    ∀ (tree : EvTree σ) (c : Ctx), tree.RelFulfilsLiveF A tid iv ts c → tree.RelWrites A Q →
      c.mem.get? ts = some w → ¬ Q w.loc w.val → tree.RelFulfilsLive A tid iv ts c
  | .done _, _, h, _, _, _ => h
  | .fault _, _, h, _, _, _ => h
  | .choose _ k, c, ⟨i, h⟩, hQ, hw, hb => ⟨i, toLive_of_relWrites (k i) c h (hQ i) hw hb⟩
  | .load _ _ _ ret, _, ⟨x, hx, h⟩, hQ, hw, hb =>
    ⟨x, hx, toLive_of_relWrites (ret x.2.1) _ h (hQ _) (by rw [(readSuccs_memProm A iv hx).1]; exact hw) hb⟩
  | .store _ _ _ _ ret, _, h, hQ, hw, hb => by
    rcases h with ⟨c', hc', ⟨⟨-, hin, hout⟩, hd⟩ | h⟩ | h
    · refine .inl ⟨c', hc', .inl ⟨⟨?_, hin, hout⟩, hd⟩⟩
      obtain ⟨w', hw', hl, hv⟩ := SLR.writeSuccs_unpromise hc' hin hout
      rw [hw] at hw'
      cases hw'
      exact Classical.byContradiction fun hne => hb (hl ▸ hv ▸ hQ.1 hne)
    · exact .inl ⟨c', hc', .inr (toLive_of_relWrites (ret true) c' h (hQ.2 true) (SLR.writeSuccs_get? hc' hw) hb)⟩
    · exact .inr (toLive_of_relWrites (ret false) _ h (hQ.2 false) hw hb)
  | .fence k ret, c, h, hQ, hw, hb =>
    toLive_of_relWrites (ret ()) _ h (hQ ()) (by rw [(SLR.fenceStep_mem_prom c k).1]; exact hw) hb
  | .rmw k noRet l op ret, c, ⟨x, hx, h⟩, hQ, hw, hb => by
    have hfm : ∀ c0 : Ctx, (if A.rmwFence then fenceStep c0 .sy else c0).mem = c0.mem := fun c0 => by
      split
      · exact (SLR.fenceStep_mem_prom c0 .sy).1
      · rfl
    have hw' : x.2.2.mem.get? ts = some w := by rw [(readSuccs_memProm A iv hx).1, hfm]; exact hw
    refine ⟨x, hx, ?_⟩
    rcases h with h | ⟨new, hop, c', hc', ⟨⟨-, hin, hout⟩, hd⟩ | h⟩
    · exact .inl (toLive_of_relWrites (ret x.2.1) _ h (hQ.2 _) (by rw [hfm]; exact hw') hb)
    · refine .inr ⟨new, hop, c', hc', .inl ⟨⟨?_, hin, hout⟩, hd⟩⟩
      obtain ⟨w', hw'', hl, hv⟩ := SLR.writeSuccs_unpromise hc' hin hout
      rw [hw'] at hw''
      cases hw''
      exact Classical.byContradiction fun hne => hb (hl ▸ hv ▸ hQ.1 hne _ _ hop)
    · refine .inr ⟨new, hop, c', hc', .inr (toLive_of_relWrites (ret x.2.1) _ h (hQ.2 _) ?_ hb)⟩
      rw [hfm, rmwPost_mem]
      exact SLR.writeSuccs_get? hc' hw'

/-- The thread form of `EvTree.RelFulfilsLiveF.toLive_of_relWrites`. -/
theorem Thread.RelFulfilsLiveF.toLive_of_relWrites {A : Arch} {tid : Nat} {ts : Time} {t : Thread I}
    {mem : Memory} {Q : Loc → Val → Prop} {w : Msg} (h : t.RelFulfilsLiveF A tid ts mem)
    (hQ : ∀ tree, I.exec t.st = some tree → tree.RelWrites A Q) (hw : mem.get? ts = some w)
    (hb : ¬ Q w.loc w.val) : t.RelFulfilsLive A tid ts mem := by
  obtain ⟨tree, hex, h⟩ := h
  exact ⟨tree, hex, EvTree.RelFulfilsLiveF.toLive_of_relWrites tree _ h (hQ tree hex) hw hb⟩

/-- **`GHyb rel` collapses to `G₀`** at a thread whose next instruction's
non-release writes are pure for `rel`. -/
theorem GHyb.toG₀ {rel : Loc → SLR.Pred} {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : GHyb rel A tid ts t mem)
    (hQ : ∀ tree, I.exec t.st = some tree → tree.RelWrites A fun l v => SLR.Pred.Pure (rel l) v) :
    G₀ A tid ts t mem :=
  h.elim id fun ⟨hF, _, hw, hb⟩ => Thread.RelFulfilsLiveF.toLive_of_relWrites hF hQ hw hb

end Kraken.Promising

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- **A rule with (i‴) is a rule for `GHyb rel`**, for the ghosts whose
release predicates are `rel`: the `GHyb` guard of a prepaid promise collapses
to the current one (`GHyb.toG₀`, from `RelPure` at the promising state), so
the existing `prepay` applies; `wp` and `done` are the rule's, with
`g.rel = rel` carried along (`Ghost.Le.rel`). -/
def ThreadRuleRX.toHyb {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) (hR : RelPure R) (rel : Loc → Pred) : ThreadRuleRXG (GHyb rel) A B tid where
  Inv cl c r g := R.Inv cl c r g ∧ g.rel = rel
  done h he hg hcl hd := R.done h.1 he hg hcl hd
  wp rF t tree h he hg ht hex E hinv hwf hnp :=
    EvTree.EraseWPRD.mono (fun _ _ _ _ hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
        fun t' h1 h2 => ⟨hp.2.2.2.2.2 t' h1 h2, hp.1.rel.trans (hg.rel.trans h.2)⟩⟩) tree _ _ _
      (R.wp rF t tree h.1 he hg ht hex E hinv hwf hnp)
  prepay rF t₁ w h he hg ht₁ E hinv hnp hG := by
    have hG₀ := GHyb.toG₀ hG fun tree hex => by
      have := hR t₁ tree h.1 he hg ht₁ hex
      rwa [hg.rel, h.2] at this
    obtain ⟨r', g', E', hg', hpend, hkeep, hnew, h', rest⟩ := R.prepay rF t₁ w h.1 he hg ht₁ E hinv hnp hG₀
    exact ⟨r', g', E', hg', hpend, hkeep, hnew, ⟨h', hg'.rel.trans (hg.rel.trans h.2)⟩, rest⟩

/-- **`NPSafeP (GHyb g.rel)` from a rule with (i‴)**, at every invariant
state, in the current frame `K2₀`. -/
theorem NPSafeP.of_relPure {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) (hR : RelPure R) (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R)
    (g : (model I).Ghost) (h : R.Inv cl c r g) :
    NPSafeP (model I) A B tid (GHyb g.rel) (K2₀ (model I)) n m cl c r g :=
  NPSafeP.of_ruleRXG (R.toHyb hR g.rel) n m cl c r g ⟨h, rfl⟩

/-- **Lift to option (S)'s frame** `K2Scope AllocIds`, for any guard: the
frame is only weakened (`K2₀.toScope`). Generalises `NPSafe.toAllocIds`
(`SLR/NPSafePInst.lean`) from `G₀` to every `G`. -/
theorem _root_.Kraken.Promising.NPSafeP.toAllocIds {A : Arch} {B : Config I → Res → Ghost → Prop} {tid n m : Nat} {cl : Prop}
    {G : PrepayGuard I} {c : Config I} {r : Res} {g : Ghost}
    (h : NPSafeP (model I) A B tid G (K2₀ (model I)) n m cl c r g) :
    NPSafeP (model I) A B tid G (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.mono (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h) h

/-- `NPSafeP.of_relPure` in option (S)'s frame `K2Scope AllocIds`, the frame
of `theorem1IIPure_Hyb_S` (`SLR/Theorem1FinalP.lean`). -/
theorem NPSafeP.of_relPure_S {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat}
    (R : ThreadRuleRX A B tid) (hR : RelPure R) (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R)
    (g : (model I).Ghost) (h : R.Inv cl c r g) :
    NPSafeP (model I) A B tid (GHyb g.rel) (K2Scope (model I) AllocIds) n m cl c r g :=
  (NPSafeP.of_relPure R hR n m cl c r g h).toAllocIds

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.NPSafeP.of_relPure
#print axioms Kraken.Promising.NPSafeP.toAllocIds
#print axioms Kraken.Promising.SLR.NPSafeP.of_relPure_S
