import WeakCore.TermOwnCP

/-! # TermOwnCT: the owner's cover at a cell whose coherence tails are own promises (ownC)

`overCr_tail`: when every unit of the label holding an own promise has its coherence tail made of
own promises (`TailP`), no unit is overtaken above its lowest own promise (`noOver_tail`), so the
cover clause is vacuous; the cover is then any nodup list of per-promise items, one for each
credited non-word promise of the label.
-/

namespace TermOwnCT
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- One item per qualifying element of a list, holders nodup. -/
theorem items_of_list {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {c : Cell} (Q : Ts → Prop)
    (hitem : ∀ t, Q t → ∃ x : Ts × Nat × Ty × List Word × Res × (Nat → Bool), x.1 = t ∧
      TermOverCr.CrItemQ E s f l c x ∧
      (∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
        ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0) ∧ TermOverCr.HolderLow s l [x]) :
    ∀ P : List Ts, ∃ L : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)), (L.map (·.1)).Nodup ∧
      (∀ x ∈ L, TermOverCr.CrItemQ E s f l c x) ∧
      (∀ x ∈ L, ∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
        ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0) ∧ TermOverCr.HolderLow s l L ∧
      ∀ t ∈ P, Q t → t ∈ L.map (·.1)
  | [] => ⟨[], by simp, by simp, by simp, fun x hx => absurd hx List.not_mem_nil, by simp⟩
  | t :: P => by
      classical
      obtain ⟨L, hnd, hit, hwa, hHL, hcov⟩ := items_of_list Q hitem P
      by_cases hq : Q t ∧ t ∉ L.map (·.1)
      · obtain ⟨x, hx1, hxi, hxw, hxH⟩ := hitem t hq.1
        refine ⟨x :: L, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun t' ht' hq' => ?_⟩
        · rw [List.map_cons, List.nodup_cons, hx1]; exact ⟨hq.2, hnd⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact hxi
          · exact hit y hy
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact hxw
          · exact hwa y hy
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact hxH y List.mem_cons_self
          · exact hHL y hy
        · rcases List.mem_cons.1 ht' with rfl | ht'
          · rw [List.map_cons, hx1]; exact List.mem_cons_self
          · rw [List.map_cons]; exact List.mem_cons_of_mem _ (hcov t' ht' hq')
      · refine ⟨L, hnd, hit, hwa, hHL, fun t' ht' hq' => ?_⟩
        rcases List.mem_cons.1 ht' with rfl | ht'
        · by_cases hin : t' ∈ L.map (·.1)
          · exact hin
          · exact absurd ⟨hq', hin⟩ hq
        · exact hcov t' ht' hq'

#print axioms items_of_list

/-- **The owner's cover at a label whose own-promise units have own-promise coherence tails.** -/
theorem overCr_tail {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {c : Cell}
    (hT : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → TailP s m.loc)
    (hPA : PromAbove s)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hitem : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc.label = l → ¬ WordUnit E m.loc →
      f t ≠ .zero → ∃ x : Ts × Nat × Ty × List Word × Res × (Nat → Bool), x.1 = t ∧
      TermOverCr.CrItemQ E s f l c x ∧
      (∀ usS i o, accs x.2.2.1 = some usS → x.2.2.2.2.2 i = true → InAcc usS i o →
        ∃ t0, TermPlant.LowOwn s ⟨l, x.2.1 + o⟩ t0) ∧ TermOverCr.HolderLow s l [x]) :
    TermOverCr.OverCrE E s f l c := by
  obtain ⟨L, hnd, hit, hwa, hHL, hcov⟩ := items_of_list (E := E) (s := s) (f := f) (l := l) (c := c)
    (fun t => t ∈ s.promises ∧ ∃ m, s.mem[t]? = some m ∧ m.loc.label = l ∧ ¬ WordUnit E m.loc ∧ f t ≠ .zero)
    (fun t ⟨ht, m, hm, hl, hw, hnz⟩ => hitem t m ht hm hl hw hnz) s.promises
  refine ⟨L, ⟨hnd, hit, fun o tw _ hv hlo _ hov => ?_, hwa,
    fun t m ht hm hl hw hnz => hcov t ht ⟨ht, m, hm, hl, hw, hnz⟩⟩, hHL⟩
  obtain ⟨m, hm, hml⟩ := hlo.2.1
  have hT' : TailP s ⟨l, o⟩ := by
    have := hT tw m hlo.1 hm (by rw [hml])
    rwa [hml] at this
  exact absurd hov (TermOwnCP.noOver_tail hT' hPA hlo (fun m' hm' => hnu tw m' hlo.1 hm') hv)

#print axioms overCr_tail

end TermOwnCT
