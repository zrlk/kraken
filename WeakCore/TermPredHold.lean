import WeakCore.TermCut

/-!
# TermPredHold: the predicted-holder clause `PredHoldG` (draft)

At a predicted unit (`PredU`: frontier, below `ini`, not below the real count) of an unpublished
(`¬ pubd`) cell of thread `j`, the first write (`FirstW`) is an outstanding promise of `j`
(H1 + H2).  H3 (the holder is at most every own promise there) is free: an outstanding promise is
never `undef` (`PromNotUndef`), and everything below the first write is (`holder_min`).

The guard is `¬ pubd` (monotone; a `publish` of a partly initialised private buffer keeps `ini`
and sets `pubd`), not the own key (which the owner may park and reload).

Consumer: BH2′ of `bufInitHeld` (`TermPredHoldP.bh2_of`; `bufInit` holds the own key, so by
`ownPub` its target is unpublished).
-/

namespace TermPredHold

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (PredHold) **Predicted units have an own holder**: at a predicted unit of thread `j`'s
unpublished own cell, the first write is an outstanding promise of `j`. -/
def PredHoldG (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (j : Nat) (th : TTh) (S : AllocLabel → Prop) (a : Address), c.ths[j]? = some th →
    (∃ cl, Eg.sto a.label = some cl ∧ cl.owner = some j) → ¬ Eg.pubd a.label →
    PredU (Cut Eg j S) a → ∃ h, FirstW c.mem a h ∧ h ∈ th.promises ∧ ∀ F, Eg.pfr a.label = some F → h ≤ F

/-- (H3) The first write at `a` is at most every non-`undef` message there. -/
theorem holder_min {mem : Memory} {a : Address} {h : Ts} (hf : FirstW mem a h) {t : Ts} {m : Msg}
    (hm : mem[t]? = some m) (hl : m.loc = a) (hv : m.val ≠ .undef) : h ≤ t :=
  Nat.le_of_not_lt fun hlt => hv (hf.2 t m hlt hm hl)

/-- `PredU` does not read the cut's `seen` set. -/
theorem predU_cut_seen {Eg : GEnv} {j : Nat} {S S' : AllocLabel → Prop} {a : Address}
    (h : PredU (Cut Eg j S) a) : PredU (Cut Eg j S') a := h

/-- (init) Without frontiers there is no predicted unit. -/
theorem predHold_none {Eg : GEnv} {c : Cfg} (h : ∀ l, Eg.pfr l = none) : PredHoldG Eg c :=
  fun _ _ _ a _ _ _ hq => absurd (h a.label) hq.1

/-- A first write exists at any address carrying a non-`undef` message. -/
theorem firstW_ex {mem : Memory} {a : Address} :
    ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc = a → m.val ≠ .undef → ∃ h, FirstW mem a h ∧ h ≤ t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro m hm hl hv
    by_cases hb : ∃ (t' : Nat) (m' : Msg), t' < t ∧ mem[t']? = some m' ∧ m'.loc = a ∧ m'.val ≠ .undef
    · obtain ⟨t', m', hlt, h1, h2, h3⟩ := hb
      obtain ⟨h, hf, hle⟩ := ih t' hlt m' h1 h2 h3
      exact ⟨h, hf, Nat.le_trans hle (Nat.le_of_lt hlt)⟩
    · refine ⟨t, ⟨⟨m, hm, hl, hv⟩, fun t' m' hlt h1 h2 => ?_⟩, Nat.le_refl _⟩
      exact Classical.byContradiction fun h3 => hb ⟨t', m', hlt, h1, h2, h3⟩

/-- **A predicted unit of an own cell, unfolded**: a frontier, below `ini` slots, and (for some
buffer layout of the cell) at or above the real count `min ini rini`. -/
theorem predU_own {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {a : Address} {cl : Cell}
    (hcl : Eg.sto a.label = some cl) (ho : cl.owner = some j) (h : PredU (Cut Eg j S) a) :
    Eg.pfr a.label ≠ none ∧
      (∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → a.offset < Eg.ini a.label * nWords us) ∧
      ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us ∧
        min (Eg.ini a.label) (Eg.rini a.label) * nWords us ≤ a.offset := by
  have hc : (Cut Eg j S).sto a.label = some cl := cutSto_own hcl ho
  obtain ⟨hp, hi, hr⟩ := h
  refine ⟨hp, fun N e us hT hu => hi cl N e us hc hT hu, ?_⟩
  refine Classical.byContradiction fun hne => hr fun c N e us hc' hT hu => ?_
  rw [hc] at hc'; cases hc'
  exact Nat.lt_of_not_le fun hle => hne ⟨N, e, us, hT, hu, hle⟩

/-- **Folding a predicted unit of an own cell.** -/
theorem predU_of {Eg : GEnv} {j : Nat} {S : AllocLabel → Prop} {a : Address} {cl : Cell}
    (hcl : Eg.sto a.label = some cl) (ho : cl.owner = some j) (hp : Eg.pfr a.label ≠ none)
    (hi : ∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → a.offset < Eg.ini a.label * nWords us)
    (hr : ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us ∧
        min (Eg.ini a.label) (Eg.rini a.label) * nWords us ≤ a.offset) :
    PredU (Cut Eg j S) a := by
  have hc : (Cut Eg j S).sto a.label = some cl := cutSto_own hcl ho
  refine ⟨hp, fun c N e us hc' hT hu => ?_, fun hw => ?_⟩
  · rw [hc] at hc'; cases hc'; exact hi N e us hT hu
  · obtain ⟨N, e, us, hT, hu, hle⟩ := hr
    have := hw cl N e us hc hT hu
    exact absurd this (Nat.not_lt.2 hle)

#print axioms holder_min
#print axioms predU_cut_seen
#print axioms predHold_none
#print axioms firstW_ex
#print axioms predU_own
#print axioms predU_of

end TermPredHold
