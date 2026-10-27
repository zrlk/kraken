import WeakCore.TermLiveCert
/-! # TermLiveCertKey — `cfgKey` is exact up to `canon`

`cfgKey` records every field of `Cfg`, `TTh`, `Frame` and `VState` except the coherence views off the memory's
addresses (`TermRun.thKey`). So equal keys give equal `canon` forms (`cfgKey_canon`), and a `CfgCoh` configuration
is its own `canon` form (`canon_self`: `CohAt` makes those views `0`). A future field that `cfgKey` omits breaks
`cfgKey_canon`. -/

namespace TermLiveCert
open CoreLang CoreTerm TermRun TermLiveMach TermLiveProps
open WeakMem (Arch Address Val Msg)

/-- One thread's `canon` form at addresses `A`. -/
def canonTh (A : List Address) (th : TTh) : TTh :=
  { th with vs := { th.vs with coh := fun b => if b ∈ A then th.vs.coh b else 0 } }

theorem canon_eq (c : Cfg) : canon c = { c with ths := c.ths.map (canonTh (locs c)) } := rfl

theorem map_congr_of {α β γ : Type} {f : α → β} {g : α → γ} (hfg : ∀ x y, f x = f y → g x = g y) :
    ∀ {l l' : List α}, l.map f = l'.map f → l.map g = l'.map g
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, y :: l', h => by
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨hfg x y h.1, map_congr_of hfg h.2⟩

theorem frame_map_inj :
    ∀ {s s' : List Frame}, s.map (fun f => (f.x, f.body, f.env, f.σs, f.ty)) =
      s'.map (fun f => (f.x, f.body, f.env, f.σs, f.ty)) → s = s' := by
  intro s s' h
  have : s.map id = s'.map id := map_congr_of (f := fun f : Frame => (f.x, f.body, f.env, f.σs, f.ty))
    (fun x y hxy => by
      cases x; cases y
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3, h4, h5⟩ := hxy
      subst h1 h2 h3 h4 h5; rfl) h
  simpa using this

theorem thKey_canonTh {A : List Address} {th th' : TTh} (h : thKey A th = thKey A th') :
    canonTh A th = canonTh A th' := by
  obtain ⟨term, env, σs, stack, ⟨coh, vRd, vWr, vCtrl, vPreBase, vRelSt, mine, fwd⟩, promises, nalloc, undefs,
    tidLbl, permit⟩ := th
  obtain ⟨term', env', σs', stack', ⟨coh', vRd', vWr', vCtrl', vPreBase', vRelSt', mine', fwd'⟩, promises',
    nalloc', undefs', tidLbl', permit'⟩ := th'
  simp only [thKey, ThKey.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8, h9, h10⟩, h11, h12, h13, h14, h15, h16, h17⟩ := h
  subst h1 h2 h3 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  have hs := frame_map_inj h4
  subst hs
  have hc : ∀ b ∈ A, coh b = coh' b := List.map_inj_left.1 h5
  simp only [canonTh, TTh.mk.injEq, WeakMem.VState.mk.injEq, and_true, true_and]
  funext b
  split
  · exact hc b (by assumption)
  · rfl

/-- **Key exactness.** Equal keys, equal `canon` forms. -/
theorem cfgKey_canon {c d : Cfg} (h : cfgKey c = cfgKey d) : canon c = canon d := by
  obtain ⟨mem, pairs, ths, lbase, boxFence, cap, trace⟩ := c
  obtain ⟨mem', pairs', ths', lbase', boxFence', cap', trace'⟩ := d
  simp only [cfgKey, CfgKey.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hm : mem = mem' := Array.toList_inj.1 h1
  subst hm h2 h4 h5 h6 h7
  simp only [canon_eq, locs, Cfg.mk.injEq, true_and, and_true]
  apply Array.toList_inj.1
  simp only [Array.toList_map]
  exact map_congr_of (fun x y hxy => thKey_canonTh hxy) h3

/-- **A coherent configuration is its own `canon` form.** -/
theorem canon_self {c : Cfg} (hc : CfgCoh c) : canon c = c := by
  rw [canon_eq]
  have hths : c.ths.map (canonTh (locs c)) = c.ths := by
    apply Array.ext
    · simp
    · intro i h1 h2
      simp only [Array.getElem_map]
      have hth := hc i c.ths[i] (Array.getElem?_eq_getElem h2)
      rcases hq : c.ths[i] with ⟨term, env, σs, stack, ⟨coh, vRd, vWr, vCtrl, vPreBase, vRelSt, mine, fwd⟩,
        promises, nalloc, undefs, tidLbl⟩
      rw [hq] at hth
      simp only [canonTh, TTh.mk.injEq, WeakMem.VState.mk.injEq, and_true, true_and]
      funext b
      split
      · rfl
      · rename_i hb
        rcases hth b with h0 | ⟨m, hm, hl⟩
        · exact h0.symm
        · exfalso
          apply hb
          simp only [locs, List.mem_eraseDups, List.mem_map]
          exact ⟨m, Array.mem_toList_iff.2 (Array.mem_of_getElem? hm), hl⟩
  simp only [hths]

/-- `canon` keeps the key. -/
theorem cfgKey_canon_self (c : Cfg) : cfgKey (canon c) = cfgKey c := by
  simp only [canon_eq, cfgKey, locs, Array.toList_map, List.map_map, CfgKey.mk.injEq, true_and, and_true]
  apply List.map_congr_left
  intro th hth
  simp only [Function.comp, thKey, canonTh, ThKey.mk.injEq, true_and, and_true]
  apply List.map_congr_left
  intro b hb
  simp [hb]

/-- `progB` sees every `Progress` move into a coherent configuration. -/
theorem progB_complete {c c' : Cfg} {i : Nat} (hc' : CfgCoh c') (h : Progress c c' i) : progB c c' i = true := by
  unfold progB
  rcases h with h | ⟨b, hb⟩
  · simp [h]
  · obtain ⟨m, hm, hl⟩ := cohOf_loc hc' (Nat.lt_of_le_of_lt (Nat.zero_le _) hb)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine Or.inr ⟨b, ?_, hb⟩
    simp only [locs, List.mem_eraseDups, List.mem_map]
    exact ⟨m, Array.mem_toList_iff.2 (Array.mem_of_getElem? hm), hl⟩

end TermLiveCert

#print axioms TermLiveCert.cfgKey_canon
#print axioms TermLiveCert.canon_self
#print axioms TermLiveCert.cfgKey_canon_self
#print axioms TermLiveCert.progB_complete
