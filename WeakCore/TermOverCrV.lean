import WeakCore.TermOverCrU

/-!
# TermOverCrV: re-pin items into the owner's cover (OvW3 R3)

At an own store fulfil, the `RepinQ` hands the owner re-pin items `Dn` (credited at
`cr' = cr0 + rpSum RS`; holders may repeat, on one piece each).  With the kept old items `Gk`
(lifted by `crItem_keep`) and the 2a re-key items `Gn`, the items are merged per holder
(`crItems_dedup`, by `crItem_mergeR`) into one list carrying the owner's cover after the op
(`overCr_ownopD`).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)


#print axioms crItem_mergeR

/-- The resources of the items of `L` held by `t`. -/
def sumH (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) (t : Ts) : Res :=
  Res.sum ((L.filter fun x => decide (x.1 = t)).map fun x => x.2.2.2.2.1)

theorem sumH_cons (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool))
    (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) (t : Ts) :
    sumH (x :: L) t = (if x.1 = t then x.2.2.2.2.1 else .zero) + sumH L t := by
  unfold sumH
  by_cases h : x.1 = t
  · simp [h]
  · simp [h]

theorem sumH_append (L1 L2 : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) (t : Ts) :
    sumH (L1 ++ L2) t = sumH L1 t + sumH L2 t := by
  unfold sumH
  rw [List.filter_append, List.map_append, Res.sum_append]

theorem le_add_leftR (a b : Res) : b ≤ a + b := fun k => by simp only [Res.add_apply]; omega

theorem sumH_le_cons (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool))
    (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) (t : Ts) : sumH L t ≤ sumH (x :: L) t := by
  rw [sumH_cons]; exact le_add_leftR _ _

theorem sumH_cons_self (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool))
    (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) :
    sumH (x :: L) x.1 = x.2.2.2.2.1 + sumH L x.1 := by
  rw [sumH_cons]; simp

theorem sumH_cons_ne (x : Ts × Nat × Ty × List Word × Res × (Nat → Bool))
    (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) {t : Ts} (h : x.1 ≠ t) :
    sumH (x :: L) t = sumH L t := by
  rw [sumH_cons]; simp [h]

/-- With distinct holders, a holder's sum is its item's resources. -/
theorem sumH_le_of_nodup {f : Ts → Res} :
    ∀ {L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}, (L.map (·.1)).Nodup →
      (∀ x ∈ L, x.2.2.2.2.1 ≤ f x.1) → ∀ t, sumH L t ≤ f t
  | [], _, _, t => Res.zero_le _
  | x :: L, hnd, h, t => by
      rw [List.map_cons] at hnd
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.1 hnd
      by_cases e : x.1 = t
      · subst e
        rw [sumH_cons_self]
        have hz : sumH L x.1 = .zero := by
          unfold sumH
          rw [List.filter_eq_nil_iff.2 (fun y hy => by
            simp only [decide_eq_true_eq]
            exact fun e' => hx (by rw [← e']; exact List.mem_map_of_mem hy))]
          rfl
        rw [hz, Res.add_zero]
        exact h x List.mem_cons_self
      · rw [sumH_cons_ne x L e]
        exact sumH_le_of_nodup hnd' (fun y hy => h y (List.mem_cons_of_mem _ hy)) t

#print axioms sumH_le_of_nodup

/-- **Merging credited items per holder**: items whose per-holder resources fit the credit
become one item per holder, each at the piece and holder of an input item, covering every unit
an input item covered, and covering only units some input item at its piece covered. -/
theorem crItems_dedup {E : TEnv} {s : St} {cr : Ts → Res} {l : AllocLabel} {c : Cell}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true) :
    ∀ (L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))),
      (∀ x ∈ L, TermOverCr.CrItemQ E s cr l c x) → (∀ t, sumH L t ≤ cr t) →
      ∃ L' : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)), (L'.map (·.1)).Nodup ∧
        (∀ x' ∈ L', TermOverCr.CrItemQ E s cr l c x') ∧
        (∀ x' ∈ L', ∀ i, x'.2.2.2.2.2 i = true →
          ∃ x ∈ L, x.1 = x'.1 ∧ x.2.1 = x'.2.1 ∧ x.2.2.1 = x'.2.2.1 ∧ x.2.2.2.2.2 i = true) ∧
        (∀ x' ∈ L', ∃ x ∈ L, x.1 = x'.1 ∧ x.2.1 = x'.2.1 ∧ x.2.2.1 = x'.2.2.1) ∧
        (∀ x ∈ L, ∃ x' ∈ L', x'.1 = x.1 ∧ x'.2.1 = x.2.1 ∧ x'.2.2.1 = x.2.2.1 ∧
          ∀ i, x.2.2.2.2.2 i = true → x'.2.2.2.2.2 i = true) ∧
        (∀ x' ∈ L', x'.2.2.2.2.1 ≤ sumH L x'.1)
  | [], _, _ => ⟨[], List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, hit, hs => by
    have hsL : ∀ t, sumH L t ≤ cr t := fun t => Res.le_trans (sumH_le_cons x L t) (hs t)
    obtain ⟨L', hnd, hit', hK', hsrc', htgt', hR'⟩ :=
      crItems_dedup hcpl hni L (fun y hy => hit y (List.mem_cons_of_mem _ hy)) hsL
    by_cases hex : ∃ z ∈ L', z.1 = x.1
    · obtain ⟨z, hz, hzx⟩ := hex
      have hsum : z.2.2.2.2.1 + x.2.2.2.2.1 ≤ cr z.1 := by
        have h1 := hR' z hz
        have h2 := hs x.1
        rw [sumH_cons_self] at h2
        rw [hzx] at h1 ⊢
        intro k
        have a1 := h1 k; have a2 := h2 k
        simp only [Res.add_apply] at a1 a2 ⊢; omega
      obtain ⟨eb, eS, z', e1, e2, e3, eK, eR, hz'⟩ :=
        crItem_mergeR hcpl hni (hit' z hz) (hit x List.mem_cons_self) hzx.symm hsum
      let f : (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) → (Ts × Nat × Ty × List Word × Res × (Nat → Bool)) :=
        fun w => if w.1 = x.1 then z' else w
      have hfz : f z = z' := by simp [f, hzx]
      have hfn : ∀ w, w.1 ≠ x.1 → f w = w := fun w h => by simp [f, h]
      have hzw : ∀ w ∈ L', w.1 = x.1 → w = z :=
        fun w hw e => eq_of_nodup_map (·.1) hnd hw hz (by rw [e, hzx])
      -- members of the new list
      have hmem : ∀ w'' ∈ L'.map f, w'' = z' ∨ (w'' ∈ L' ∧ w''.1 ≠ x.1) := by
        intro w'' hw''
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw''
        by_cases e : w.1 = x.1
        · left; rw [hzw w hw e, hfz]
        · right; rw [hfn w e]; exact ⟨hw, e⟩
      have hzpm : z' ∈ L'.map f := by rw [← hfz]; exact List.mem_map_of_mem hz
      have hwm : ∀ w ∈ L', w.1 ≠ x.1 → w ∈ L'.map f := fun w hw e => by
        rw [← hfn w e]; exact List.mem_map_of_mem hw
      refine ⟨L'.map f, ?_, fun w'' hw'' => ?_, fun w'' hw'' i hi => ?_, fun w'' hw'' => ?_,
        fun y hy => ?_, fun w'' hw'' => ?_⟩
      · have e : (L'.map f).map (·.1) = L'.map (·.1) := by
          rw [List.map_map]
          refine List.map_congr_left (fun w hw => ?_)
          by_cases e : w.1 = x.1
          · show (f w).1 = w.1
            rw [hzw w hw e, hfz, e1]
          · show (f w).1 = w.1
            rw [hfn w e]
        rw [e]; exact hnd
      · rcases hmem w'' hw'' with rfl | ⟨hw, -⟩
        · exact hz'
        · exact hit' w'' hw
      · rcases hmem w'' hw'' with rfl | ⟨hw, -⟩
        · rw [eK] at hi
          rcases Bool.or_eq_true_iff.1 hi with hi | hi
          · obtain ⟨y, hy, f1, f2, f3, f4⟩ := hK' z hz i hi
            exact ⟨y, List.mem_cons_of_mem _ hy, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], f4⟩
          · exact ⟨x, List.mem_cons_self, by rw [e1, hzx], by rw [e2, eb], by rw [e3, eS], hi⟩
        · obtain ⟨y, hy, f1, f2, f3, f4⟩ := hK' w'' hw i hi
          exact ⟨y, List.mem_cons_of_mem _ hy, f1, f2, f3, f4⟩
      · rcases hmem w'' hw'' with rfl | ⟨hw, -⟩
        · exact ⟨x, List.mem_cons_self, by rw [e1, hzx], by rw [e2, eb], by rw [e3, eS]⟩
        · obtain ⟨y, hy, f1, f2, f3⟩ := hsrc' w'' hw
          exact ⟨y, List.mem_cons_of_mem _ hy, f1, f2, f3⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨z', hzpm, by rw [e1, hzx], by rw [e2, eb], by rw [e3, eS],
            fun i hi => by rw [eK, hi, Bool.or_true]⟩
        · obtain ⟨w, hw, f1, f2, f3, f4⟩ := htgt' y hy
          by_cases e : w.1 = x.1
          · obtain rfl := hzw w hw e
            exact ⟨z', hzpm, by rw [e1, f1], by rw [e2, f2], by rw [e3, f3],
              fun i hi => by rw [eK, f4 i hi, Bool.true_or]⟩
          · exact ⟨w, hwm w hw e, f1, f2, f3, f4⟩
      · rcases hmem w'' hw'' with rfl | ⟨hw, hne⟩
        · rw [e1, hzx, sumH_cons_self]
          have h1 := hR' z hz
          rw [hzx] at h1
          intro k
          have a1 := eR k; have a2 := h1 k
          simp only [Res.add_apply] at a1 a2 ⊢; omega
        · rw [sumH_cons_ne x L (fun e => hne e.symm)]
          exact hR' w'' hw
    · have hnot : x.1 ∉ L'.map (·.1) := fun h => by
        obtain ⟨z, hz, e⟩ := List.mem_map.1 h
        exact hex ⟨z, hz, e⟩
      refine ⟨x :: L', by rw [List.map_cons]; exact List.nodup_cons.2 ⟨hnot, hnd⟩, fun w hw => ?_,
        fun w hw i hi => ?_, fun w hw => ?_, fun y hy => ?_, fun w hw => ?_⟩
      · rcases List.mem_cons.1 hw with rfl | hw
        · exact hit w List.mem_cons_self
        · exact hit' w hw
      · rcases List.mem_cons.1 hw with rfl | hw
        · exact ⟨w, List.mem_cons_self, rfl, rfl, rfl, hi⟩
        · obtain ⟨y, hy, f1, f2, f3, f4⟩ := hK' w hw i hi
          exact ⟨y, List.mem_cons_of_mem _ hy, f1, f2, f3, f4⟩
      · rcases List.mem_cons.1 hw with rfl | hw
        · exact ⟨w, List.mem_cons_self, rfl, rfl, rfl⟩
        · obtain ⟨y, hy, f1, f2, f3⟩ := hsrc' w hw
          exact ⟨y, List.mem_cons_of_mem _ hy, f1, f2, f3⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨y, List.mem_cons_self, rfl, rfl, rfl, fun _ h => h⟩
        · obtain ⟨w, hw, f1, f2, f3, f4⟩ := htgt' y hy
          exact ⟨w, List.mem_cons_of_mem _ hw, f1, f2, f3, f4⟩
      · rcases List.mem_cons.1 hw with rfl | hw
        · rw [sumH_cons_self]; exact Res.le_add_right _ _
        · exact Res.le_trans (hR' w hw) (sumH_le_cons x L w.1)

#print axioms crItems_dedup

end TermOverCrW

namespace TermOverCr5
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section ownD
variable {s s' : St} (hmem : s'.mem = s.mem) (hsub : ∀ t, t ∈ s'.promises → t ∈ s.promises)
include hmem hsub

/-- **(OvW3 R3) The owner's cover at its own op, with re-pin items.**  As `overCr_ownopR`, plus
re-pin items `Dn` (the `RepinQ` at the label; holders may repeat): a unit the op newly
needs may be covered by a re-pin item (`hcovN0`'s third case, from `RepinCov`), and a credit
at the holder may come from a re-pin item (`hzN`).  The kept, re-key and re-pin items are merged
per holder (`crItems_dedup`); the per-holder resources fit `cr'` (`hsumL`). -/
theorem overCr_ownopD {E E' : TEnv} {cr cr' : Ts → Res} {l : AllocLabel} {c : Cell} {G G' : Nat → Ts → Prop}
    {Gs Gk Gn Dn : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (hcpl : Ty.coupledOKIn [] c.ty = true) (hni : noIallV c.ty = true)
    (hsto0 : E.sto l = some c) (hpf : E.pfr l ≠ none)
    (hpi : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → ∀ cl, E.sto m.loc.label = some cl →
      E.pfr m.loc.label ≠ none → InitR E cl m.loc.label m.loc.offset)
    (hsto : E'.sto l = E.sto l) (hV : ∀ S ws R0, ValOfR E S ws R0 → ValOfR E' S ws R0)
    (hPU : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      PredU E ⟨l, x.2.1 + o⟩ → PredU E' ⟨l, x.2.1 + o⟩)
    (h : TermOverCr.OverCrL E s cr l c G Gs)
    (hGk : Gk.Sublist Gs)
    (hcrK : ∀ x ∈ Gk, cr x.1 ≤ cr' x.1)
    (hnfH : ∀ x ∈ Gk, ∀ mh, s.mem[x.1]? = some mh → ∀ t m, t ∈ s.promises → t ∉ s'.promises →
      s.mem[t]? = some m → m.loc ≠ mh.loc)
    (hnfK : ∀ x ∈ Gk, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, x.2.1 + o⟩)
    (hGn : ∀ x ∈ Gn, TermOverCr.CrItemQ E' s' cr' l c x)
    (hwaN : ∀ x ∈ Gn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0)
    (hDn : ∀ x ∈ Dn, TermOverCr.CrItemQ E' s' cr' l c x)
    (hwaD : ∀ x ∈ Dn, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn s' ⟨l, x.2.1 + o⟩ t0)
    (hsumL : ∀ t, TermOverCrW.sumH (Gk ++ Gn ++ Dn) t ≤ cr' t)
    (hHL : TermOverCr.HolderLow s' l (Gk ++ Gn ++ Dn))
    (hcovN0 : ∀ o tw, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o → ¬ VisU E' ⟨l, o⟩ →
      TermPlant.LowOwn s' ⟨l, o⟩ tw → G' o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw →
      ((∀ t m, t ∈ s.promises → t ∉ s'.promises → s.mem[t]? = some m → m.loc ≠ ⟨l, o⟩) ∧
        ¬ VisU E ⟨l, o⟩ ∧ G o tw ∧ TermPlant.OverT E s ⟨l, o⟩ tw ∧
        ∀ x ∈ Gs, (∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true) → x ∈ Gk) ∨
      ∃ x ∈ Gn ++ Dn, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true)
    (hzN : ∀ t m, t ∈ s'.promises → s'.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E' m.loc →
      cr' t ≠ .zero → (cr t ≠ .zero ∧ ∀ x ∈ Gs, x.1 = t → x ∈ Gk) ∨ t ∈ (Gn ++ Dn).map (·.1)) :
    ∃ Gs', TermOverCr.OverCrL E' s' cr' l c G' Gs' ∧ TermOverCr.HolderLow s' l Gs' := by
  have hit0 := h.2.1
  have hcov0 := h.2.2.1
  have hwa0 := h.2.2.2.1
  have hz0 := h.2.2.2.2
  -- the merged list
  have hitL : ∀ x ∈ Gk ++ Gn ++ Dn, TermOverCr.CrItemQ E' s' cr' l c x := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact crItem_keep hmem hsub hsto hV (hcrK x hx) (hnfH x hx) (hnfK x hx) (hPU x hx) (hit0 x (hGk.subset hx))
      · exact hGn x hx
    · exact hDn x hx
  obtain ⟨L', hnd, hit', hK', hsrc', htgt', -⟩ :=
    TermOverCrW.crItems_dedup hcpl hni (Gk ++ Gn ++ Dn) hitL hsumL
  -- a source item covering a unit gives a merged item covering it
  have hcovT : ∀ o x, x ∈ Gk ++ Gn ++ Dn → (∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧
      InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true) →
      ∃ x' ∈ L', ∃ usS i, accs x'.2.2.1 = some usS ∧ x'.2.1 ≤ o ∧ InAcc usS i (o - x'.2.1) ∧
        x'.2.2.2.2.2 i = true := by
    intro o x hx ⟨usS, i, h1, h2, h3, h4⟩
    obtain ⟨x', hx', -, f2, f3, f4⟩ := htgt' x hx
    exact ⟨x', hx', usS, i, by rw [f3]; exact h1, by rw [f2]; exact h2, by rw [f2]; exact h3, f4 i h4⟩
  refine ⟨[] ++ L', overCr_ownopR hmem hsub hsto0 hpf hpi hsto hV (Gk := []) (Gn := L')
    (fun _ h => absurd h List.not_mem_nil) h (List.nil_sublist _)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) hit' hnd (fun _ h => absurd h List.not_mem_nil)
    (fun x' hx' usS i o h1 h2 h3 => ?_) (fun o tw hi hi0 hv hl hg hov => ?_) (fun t m ht hm hl hw hnz => ?_),
    fun x' hx' usS hus t m ht hm hl h1 h2 => ?_⟩
  · -- every merged `K` unit has a lowest own promise
    obtain ⟨x, hx, -, f2, f3, f4⟩ := hK' x' hx' i h2
    rw [← f3] at h1
    rw [← f2]
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨t0, h0⟩ := hwa0 x (hGk.subset hx) usS i o h1 f4 h3
        exact ⟨t0, lowOwn_keep hmem hsub (hnfK x hx usS i o h1 f4 h3) h0⟩
      · exact hwaN x hx usS i o h1 f4 h3
    · exact hwaD x hx usS i o h1 f4 h3
  · right
    rcases hcovN0 o tw hi hi0 hv hl hg hov with ⟨hnf, hv0, hg0, hov0, hin⟩ | ⟨x, hx, hr⟩
    · obtain ⟨x, hx, hr⟩ := hcov0 o tw hi0 hv0 (lowOwn_keep_back hmem hsub hnf hl) hg0 hov0
      exact hcovT o x (List.mem_append_left _ (List.mem_append_left _ (hin x hx hr))) hr
    · rw [List.append_assoc] at hcovT
      exact hcovT o x (List.mem_append_right _ hx) hr
  · right
    rcases hzN t m ht hm hl hw hnz with ⟨hnz0, hk⟩ | hn
    · have hw0 : ¬ WordUnit E m.loc := fun hw0 => hw (by
        obtain ⟨c1, hc1, hor⟩ := hw0
        exact ⟨c1, by rw [hl, hsto, ← hl]; exact hc1, hor⟩)
      have hm0 : s.mem[t]? = some m := by rw [← hmem]; exact hm
      obtain ⟨x, hx, hx1⟩ := List.mem_map.1 (hz0 t m (hsub t ht) hm0 hl hw0 hnz0)
      obtain ⟨x', hx', f1, -⟩ := htgt' x (List.mem_append_left _ (List.mem_append_left _ (hk x hx hx1)))
      exact List.mem_map.2 ⟨x', hx', by rw [f1, hx1]⟩
    · obtain ⟨x, hx, hx1⟩ := List.mem_map.1 hn
      have hx2 : x ∈ Gk ++ Gn ++ Dn := by rw [List.append_assoc]; exact List.mem_append_right _ hx
      obtain ⟨x', hx', f1, -⟩ := htgt' x hx2
      exact List.mem_map.2 ⟨x', hx', by rw [f1, hx1]⟩
  · -- holder lowness of the merged items
    have hx'' : x' ∈ L' := by simpa using hx'
    obtain ⟨x, hx, f1, f2, f3⟩ := hsrc' x' hx''
    rw [← f1]
    rw [← f3] at hus
    rw [← f2] at h1 h2
    exact hHL x hx usS hus t m ht hm hl h1 h2

#print axioms overCr_ownopD

end ownD

end TermOverCr5
