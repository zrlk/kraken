import WeakCore.TermOwnCF

/-! # TermOwnCP: assembling the owner's cover from an item list (ownC)

`overCr_assemble`: any list of credited items (holders may repeat; per-holder resources within
the credits) whose units carry a lowest own promise, held at the lowest own promise of their
piece, covering every unit the cover asks for and holding every credited non-word promise of the
label, gives `OverCrE` (merged per holder by `TermOverCrW.crItems_dedup`).
-/

namespace TermOwnCP
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The owner's cover from an item list.** -/
theorem overCr_assemble {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {c : Cell}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)))
    (hit : ∀ x ∈ L, TermOverCr.CrItemQ E s f l c x) (hsum : ∀ t, TermOverCrW.sumH L t ≤ f t)
    (hwa : ∀ x ∈ L, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0)
    (hHL : TermOverCr.HolderLow s l L)
    (hcov : ∀ o tw, TermOverCr.CovU E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E s l o tw → TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ x ∈ L, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hz : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      f t ≠ .zero → t ∈ L.map (·.1)) :
    TermOverCr.OverCrE E s f l c := by
  obtain ⟨L', hnd, hit', hK', hsrc', htgt', -⟩ := TermOverCrW.crItems_dedup hcpl hni L hit hsum
  refine ⟨L', ⟨hnd, hit', fun o tw hc hv hlo hg hov => ?_, fun x' hx' usS i o h1 h2 h3 => ?_,
    fun t m ht hm hl hw hnz => ?_⟩, fun x' hx' usS hus t m ht hm hl h1 h2 => ?_⟩
  · obtain ⟨x, hx, usS, i, h1, h2, h3, h4⟩ := hcov o tw hc hv hlo hg hov
    obtain ⟨x', hx', -, f2, f3, f4⟩ := htgt' x hx
    exact ⟨x', hx', usS, i, by rw [f3]; exact h1, by rw [f2]; exact h2, by rw [f2]; exact h3, f4 i h4⟩
  · obtain ⟨x, hx, -, f2, f3, f4⟩ := hK' x' hx' i h2
    rw [← f3] at h1
    rw [← f2]
    exact hwa x hx usS i o h1 f4 h3
  · obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hz t m ht hm hl hw hnz)
    obtain ⟨x', hx', f1, -⟩ := htgt' x hx
    exact List.mem_map.2 ⟨x', hx', by rw [f1, hx1]⟩
  · obtain ⟨x, hx, f1, f2, f3⟩ := hsrc' x' hx'
    rw [← f1]
    rw [← f3] at hus
    rw [← f2] at h1 h2
    exact hHL x hx usS hus t m ht hm hl h1 h2

#print axioms overCr_assemble

/-- A first write below a non-`undef` message. -/
theorem firstW_ex {mem : Memory} {a : Address} {t : Ts} {m : Msg} (hm : mem[t]? = some m) (hl : m.loc = a)
    (hu : m.val ≠ .undef) : ∃ h, FirstW mem a h ∧ h ≤ t := by
  classical
  obtain ⟨k, ⟨mk, hk, hlk, huk⟩, hmin⟩ := TermOverCrW.exists_min_nat
    (P := fun n => ∃ m, mem[n]? = some m ∧ m.loc = a ∧ m.val ≠ .undef) t ⟨m, hm, hl, hu⟩
  refine ⟨k, ⟨⟨mk, hk, hlk, huk⟩, fun t' m' ht' hm' hl' => ?_⟩, hmin t ⟨m, hm, hl, hu⟩⟩
  by_cases hne : m'.val = .undef
  · exact hne
  · exact absurd (hmin t' ⟨m', hm', hl', hne⟩) (Nat.not_le.2 ht')

#print axioms firstW_ex

/-- **No overtaking above the lowest own promise at a unit whose coherence tail is own promises**
(`TailP`, the owner's invariant at a cell without a frontier) under `PromAbove`. -/
theorem noOver_tail {E : TEnv} {s : St} {a : Address} {tw : Ts}
    (hT : TailP s a) (hPA : PromAbove s) (hlo : TermPlant.LowOwn s a tw)
    (hnu : ∀ m, s.mem[tw]? = some m → m.val ≠ .undef) (hnv : ¬ VisU E a) :
    ¬ TermPlant.OverT E s a tw := by
  rintro ⟨t, m, h1, h2, h3, h4⟩
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := hlo
  have hc := hPA tw htw mw hmw
  rw [hml] at hc
  have htp : t ∈ s.promises := hT t m (Nat.lt_trans hc h1) h2 h3
  apply h4
  simp only [PromAt, hnv, ↓reduceIte]
  split
  · obtain ⟨h0, hf, hle⟩ := firstW_ex hmw hml (hnu mw hmw)
    refine List.mem_filter.2 ⟨List.mem_append_left _ htp, ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨h0, hf, Nat.lt_of_le_of_lt hle h1⟩
  · exact List.mem_append_left _ htp

#print axioms noOver_tail

end TermOwnCP
