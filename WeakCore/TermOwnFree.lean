import WeakCore.TermFreeQW
import WeakCore.TermOverCrX

/-! # TermOwnFree: adding free items to a credited cover (own-load wiring)

The own-load flip (a unit newly meeting the window guard) is covered by the post-state's free items
`freeWL`.  `overCrL_addFree` adds any zero-resource item list to a cover proved under a narrower
guard, deduplicating the holders (`crItems_dedup`); `overCrL_addFreeWL` instantiates `freeWL`.
-/

namespace TermOwnFree
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- **Adding free items**: a cover under guard `G1` and zero-resource items `Fz` answering for the
rest of guard `G` give a cover under `G`. -/
theorem overCrL_addFree {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {G1 G : Nat → Ts → Prop} {Gs Fz : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrL E s cr l c G1 Gs) (hH : TermOverCr.HolderLow s l Gs)
    (hFi : ∀ x ∈ Fz, TermOverCr.CrItemQ E s cr l c x) (hFz : ∀ x ∈ Fz, x.2.2.2.2.1 = .zero)
    (hFH : TermOverCr.HolderLow s l Fz)
    (hFw : ∀ x ∈ Fz, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hG : ∀ o tw, TermOverCr.CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G o tw →
      TermPlant.OverT E s ⟨l, o⟩ tw → G1 o tw ∨ ∃ x ∈ Fz, TermOverCrX.CrCovI x o) :
    ∃ Gs', TermOverCr.OverCrL E s cr l c G Gs' ∧ TermOverCr.HolderLow s l Gs' := by
  obtain ⟨hnd, hit, hcov, hwa, hz⟩ := h
  have hit2 : ∀ x ∈ Gs ++ Fz, TermOverCr.CrItemQ E s cr l c x := fun x hx =>
    (List.mem_append.1 hx).elim (hit x) (hFi x)
  have hsum : ∀ t, TermOverCrW.sumH (Gs ++ Fz) t ≤ cr t := by
    intro t
    rw [TermOverCrW.sumH_append, TermOverCrW.sumH_zero hFz t, Res.add_zero]
    exact TermOverCrW.sumH_le_of_nodup hnd (fun x hx => TermOverCrW.crItemQ_R (hit x hx)) t
  obtain ⟨L', hnd', hit', hK', hsrc', htgt', -⟩ := TermOverCrW.crItems_dedup hcpl hni (Gs ++ Fz) hit2 hsum
  have hHL : TermOverCr.HolderLow s l (Gs ++ Fz) := TermOverCr.holderLow_append hH hFH
  -- an item of `Gs ++ Fz` covering `o` has a covering image in `L'`
  have himg : ∀ o0 : Nat, ∀ x ∈ Gs ++ Fz, TermOverCrX.CrCovI x o0 →
      ∃ x' ∈ L', ∃ usS i, accs x'.2.2.1 = some usS ∧ x'.2.1 ≤ o0 ∧ InAcc usS i (o0 - x'.2.1) ∧
        x'.2.2.2.2.2 i = true := by
    intro o0 x hx hc
    obtain ⟨usS, i, hus, hb, hi, hk⟩ := hc
    obtain ⟨x', hx', -, eb, eS, hsup⟩ := htgt' x hx
    exact ⟨x', hx', usS, i, by rw [eS]; exact hus, by rw [eb]; exact hb, by rw [eb]; exact hi, hsup i hk⟩
  refine ⟨L', ⟨hnd', hit', fun o tw hcu hv hlo hg hov => ?_, fun x' hx' usS i o hus hk hio => ?_,
    fun t m ht hm hl hnw hnz => ?_⟩, fun x' hx' usS hus t m ht hm hl h1 h2 => ?_⟩
  · rcases hG o tw hcu hv hlo hg hov with h1 | ⟨x, hx, hc⟩
    · obtain ⟨x, hx, usS, i, hus, hb, hi, hk⟩ := hcov o tw hcu hv hlo h1 hov
      exact himg o x (List.mem_append_left _ hx) ⟨usS, i, hus, hb, hi, hk⟩
    · exact himg o x (List.mem_append_right _ hx) hc
  · obtain ⟨x, hx, -, eb, eS, hkx⟩ := hK' x' hx' i hk
    rw [← eb]
    rcases List.mem_append.1 hx with hx | hx
    · exact hwa x hx usS i o (by rw [eS]; exact hus) hkx hio
    · exact hFw x hx usS i o (by rw [eS]; exact hus) hkx hio
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hz t m ht hm hl hnw hnz)
    obtain ⟨x', hx', e1, -, -, -⟩ := htgt' x (List.mem_append_left _ hx)
    exact List.mem_map.2 ⟨x', hx', e1⟩
  · obtain ⟨x, hx, e1, eb, eS⟩ := hsrc' x' hx'
    rw [← e1]
    rw [← eb] at h1 h2
    exact hHL x hx usS (by rw [eS]; exact hus) t m ht hm hl h1 h2

#print axioms overCrL_addFree

/-- **With the post-state's `freeWL`**: units of the guard `G` outside `G1` covered by a free item. -/
theorem overCrL_addFreeWL {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    {G1 G : Nat → Ts → Prop} {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (h : TermOverCr.OverCrL E s cr l c G1 Gs) (hH : TermOverCr.HolderLow s l Gs)
    (hG : ∀ o tw, TermOverCr.CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → G o tw →
      TermPlant.OverT E s ⟨l, o⟩ tw → G1 o tw ∨ ∃ x, TermFreeQW.FreeQW E s l c tw x) :
    ∃ Gs', TermOverCr.OverCrL E s cr l c G Gs' ∧ TermOverCr.HolderLow s l Gs' := by
  refine overCrL_addFree hcpl hni h hH TermFreeQW.freeWL_item TermFreeQW.freeWL_zero
    TermFreeQW.freeWL_holder TermFreeQW.freeWL_wa (fun o tw hcu hv hlo hg hov => ?_)
  rcases hG o tw hcu hv hlo hg hov with h1 | ⟨x, hx⟩
  · exact .inl h1
  · obtain ⟨y, hy, usS, i, hus, hb, hi, hk⟩ := TermFreeQW.freeWL_cover hx hlo
    exact .inr ⟨y, hy, usS, i, hus, hb, hi, hk⟩

#print axioms overCrL_addFreeWL

end TermOwnFree
