import WeakCore.TermOverCrP
import WeakCore.TermStepper
import WeakCore.TermPromAtFW

/-! # TermOverCrQ: adding a plant credit to a promise's credit (H7)

Under H7 a `δ`-point may already carry credit.  A plant credit adds to an existing
key-free credit (a plant credit, or nothing): `plantCr_add`, `crKeys_add`, and the
`PromCrK` form `plantCrK_add` (the old credit at a non-word unit is a plant credit or zero).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Plant credits add**: a plant credit `R` plus a plant credit `R'` (same promise) is one. -/
theorem plantCr_add {E : TEnv} {s : St} {m : Msg} {t : Ts} {R R' : Res}
    (h : PlantCr E s m t R) (h' : PlantCr E s m t R') : PlantCr E s m t (R + R') := by
  obtain ⟨c, sb, S0, b0, S, us, wb, hsto, hown, hpf, hseg, hat, hS, hnw, hus, hn, h1, h2, htw, hwb, hfp, hlow,
    hR⟩ := h
  rcases hR with ⟨K, ws, R0, hwl, hv, hle, hpin⟩ | hz
  · exact ⟨c, sb, S0, b0, S, us, wb, hsto, hown, hpf, hseg, hat, hS, hnw, hus, hn, h1, h2, htw, hwb, hfp, hlow,
      Or.inl ⟨K, ws, R0, hwl, hv, Res.le_trans hle (Res.le_add_right _ _), hpin⟩⟩
  · rw [hz, Res.zero_add]
    exact h'

#print axioms plantCr_add

/-- Key-freedom adds. -/
theorem crKeys_add {R R' : Res} (h : TermPlant.CrKeys R) (h' : TermPlant.CrKeys R') :
    TermPlant.CrKeys (R + R') := fun l => by
  simp only [Res.add_apply, h l, h' l]

#print axioms crKeys_add

/-- **(H7) A key-free plant credit adds to a `PromCrK` credit** at a non-word unit. -/
theorem plantCrK_add {E : TEnv} {s : St} {cr db : Ts → Res} {t : Ts} {m : Msg} {R' : Res}
    (hC : TermPlant.PromCrK E s cr db) (ht : t ∈ s.promises) (hm : s.mem[t]? = some m)
    (hw : ¬ WordUnit E m.loc) (hP : PlantCr E s m t R') (hK : TermPlant.CrKeys R') :
    PlantCr E s m t (cr t + R') ∧ TermPlant.CrKeys (cr t + R') := by
  obtain ⟨m', hm', -, hc⟩ := hC t ht
  rw [hm] at hm'
  cases hm'
  rcases hc with h | ⟨h, hk⟩
  · rw [TermOverCr4.oldCr_nword_zero hw h, Res.zero_add]
    exact ⟨hP, hK⟩
  · exact ⟨plantCr_add h hP, crKeys_add hk hK⟩

#print axioms plantCrK_add

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain

/-- **A solid component lies in a segment**: `AtOff` into a laid-out cell type splits at the
segment (`SegOf`: the whole type, or a buffer slot). -/
theorem seg_of_atOff {T S : Ty} {b : Nat} (hlay : LayT T) (h : AtOff T b S) (hS : Solid S) :
    ∃ sb S0 b0, SegOf T sb S0 ∧ AtOff S0 b0 S ∧ sb + b0 = b := by
  by_cases harr : ∃ N e, T = .array (.lit N) e
  · obtain ⟨N, e, rfl⟩ := harr
    cases h with
    | here _ => exact absurd rfl (hS.2.1 _ _)
    | @elem _ _ _ j o us hus hj hat =>
        exact ⟨j * nWords us, e, o, Or.inr ⟨N, us, j, rfl, hus, hj, rfl⟩, hat, rfl⟩
    | fold _ _ _ _ => exact absurd (cl_mu_eq _ _ _) (hS.2.2 _)
  · rcases hlay with hacc | ⟨N, e, hTe, -⟩
    · exact ⟨0, T, b, Or.inl ⟨rfl, rfl, hacc⟩, h, Nat.zero_add _⟩
    · exact absurd ⟨N, e, hTe⟩ harr

#print axioms seg_of_atOff

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **(O2) The plant-credit target of a piece**: below a window bound `wb` clearing the foreign
promises at the cell, the lowest own promise `t` of a non-word piece holding an own promise `tw`
is a plant credit for any credit covering a value of the piece. -/
theorem piece_target {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {b : Nat} {S : Ty} {us : List Acc}
    {tw wb : Ts} {mw : Msg} {ws : List Word} {R0 R : Res}
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l ≠ none) (hlay : LayT c.ty)
    (hP : TermPiece.Piece c.ty b S) (hus : accs S = some us)
    (hnw : ∀ o', b ≤ o' → o' < b + nWords us → ¬ WordUnit E ⟨l, o'⟩)
    (htw : tw ∈ s.promises) (hmw : s.mem[tw]? = some mw) (hlw : mw.loc.label = l)
    (h1 : b ≤ mw.loc.offset) (h2 : mw.loc.offset < b + nWords us) (hwbt : tw ≤ wb) (hwb : wb < s.mem.size)
    (hfp : ∀ tf mf, tf ∈ FpAt E ⟨l, 0⟩ → s.mem[tf]? = some mf → mf.loc.label = l → wb < tf)
    (hwl : ws.length = nWords us) (hv : ValOfR E S ws R0) (hR : R0 ≤ R) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧ b ≤ m.loc.offset ∧
      m.loc.offset < b + nWords us ∧ t ≤ tw ∧
      (∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = l → b ≤ m'.loc.offset →
        m'.loc.offset < b + nWords us → t ≤ t') ∧ PlantCr E s m t R := by
  obtain ⟨t, m, ht, hm, hl, hb1, hb2, hle, hmin⟩ := lowest_in_piece htw hmw hlw h1 h2
  obtain ⟨sb, S0, b0, hseg, hat, e⟩ := seg_of_atOff hlay hP.1 hP.2.1
  subst e
  have hsto' : E.sto m.loc.label = some c := by rw [hl]; exact hsto
  have hpf' : E.pfr m.loc.label ≠ none := by rw [hl]; exact hpf
  have hnw' : ¬ WordUnit E m.loc := by
    have := hnw m.loc.offset hb1 hb2
    rw [← hl] at this
    exact this
  refine ⟨t, m, ht, hm, hl, hb1, hb2, hle, hmin, ?_⟩
  refine plantCr_mk hsto' hown hpf' hseg hat hP.2.1 hnw' hus (TermPiece.Piece_pos hP hus) hb1 hb2
    (Nat.le_trans hle hwbt) hwb (fun tf mf h0 h3 h4 => ?_) (fun t' m' h3 h4 h5 h6 h7 _ => ?_) hwl hv hR
  · rw [hl] at h0 h4
    exact hfp tf mf h0 h3 h4
  · rw [hl] at h5
    exact hmin t' m' h3 h4 h5 h6 h7

#print axioms piece_target

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A unit initialised at the real count is not predicted. -/
theorem not_predU_of_initRr {E : TEnv} {c : Cell} {l : AllocLabel} {o : Nat} (hsto : E.sto l = some c)
    (hI : InitRr E c l o) : ¬ PredU E ⟨l, o⟩ := fun h =>
  h.2.2 fun c1 N e us h1 h2 h3 => by
    have e1 : c1 = c := Option.some.inj (h1.symm.trans hsto)
    subst e1
    exact hI N e us h2 h3

#print axioms not_predU_of_initRr

/-- (PredCov) `hI` of `overCr_foreign`: at a step keeping the cell, its frontier, and not raising
`ini` nor `rc` at `l`, a covered unit after was covered before. -/
theorem covU_back {E E' : TEnv} {c : Cell} {l : AllocLabel} (hsto0 : E.sto l = some c)
    (hsto : E'.sto l = E.sto l) (hpf : E.pfr l ≠ none) (hini : E'.ini l ≤ E.ini l) (hrc : E'.rc l ≤ E.rc l) :
    ∀ o, TermOverCr.CovU E' c l o → TermOverCr.CovU E c l o := by
  intro o h
  rcases h with hI | ⟨-, hW, hWr⟩
  · exact .inl (initRr_back hrc o hI)
  · by_cases hI0 : InitRr E c l o
    · exact .inl hI0
    · refine .inr ⟨hpf, fun c1 N e us h1 h2 h3 => ?_, fun hw => hI0 fun N e us h2 h3 => ?_⟩
      · exact Nat.lt_of_lt_of_le (hW c1 N e us (by rw [hsto]; exact h1) h2 h3) (Nat.mul_le_mul_right _ hini)
      · exact hw c N e us hsto0 h2 h3

#print axioms covU_back

/-- **(O5, PredCov)** `hcovD_core` under the cover's guard `CovU`: an own (non-`undef`) lowest
promise is skipped, or is the first write of a predicted unit (`promAt_or_firstW`). -/
theorem hcovD_coreQ {E E' : TEnv} {s s' : St} {l : AllocLabel} {c : Cell} {tg : TermPiece.GdE → Option Ts}
    {Gd : List TermPiece.GdE}
    (hVU : ∀ o, ¬ VisU E' ⟨l, o⟩ → ¬ VisU E ⟨l, o⟩)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.val ≠ .undef)
    (hWb : ∀ o tw, TermOverCr.WinG E' s' l o tw → TermOverCr.WinG E s l o tw)
    (hent : ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ g ∈ Gd, g.l = l ∧ (∃ t, tg g = some t) ∧ ∃ us i, accs g.S = some us ∧ g.b ≤ o ∧
        InAcc us i (o - g.b) ∧ (∀ o', InAcc us i o' → o' = o - g.b) ∧ g.L (o - g.b) = true) :
    ∀ o tw, TermOverCr.CovU E' c l o → ¬ VisU E' ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw →
      TermOverCr.WinG E' s' l o tw → TermPlant.OverT E' s' ⟨l, o⟩ tw → TermPlant.OverT E s ⟨l, o⟩ tw ∨
      ∃ y ∈ dnOf l tg (kfOf E s l) Gd, ∃ usS i, accs y.2.2.1 = some usS ∧ y.2.1 ≤ o ∧
        InAcc usS i (o - y.2.1) ∧ y.2.2.2.2.2 i = true := by
  intro o tw hI hv hl hw hov
  classical
  by_cases hold : TermPlant.OverT E s ⟨l, o⟩ tw
  · exact .inl hold
  · right
    obtain ⟨g, hg, hgl, ⟨t, ht⟩, us, i, hus, hb, hio, hsing, hL⟩ := hent o tw hI hv hl hw hov hold
    have heq : g.b + (o - g.b) = o := Nat.add_sub_cancel' hb
    have hk : KOk E s l g (o - g.b) := by
      unfold KOk
      rw [heq]
      refine ⟨⟨tw, hl⟩, fun tw' hl' => ?_⟩
      rw [TermPlant.LowOwn_uniq hl' hl]
      obtain ⟨h1, ⟨m, hm, hml⟩, -⟩ := id hl
      refine ⟨hL, TermPromAtFW.promAt_or_firstW h1 hm hml (hnu tw m h1 hm) (hVU o hv),
        fun t1 m1 h1 h2 h3 => ?_, hWb o tw hw⟩
      exact (Classical.em _).elim id fun hn => False.elim <| by
        unfold TermPlant.OverT at hold
        exact hold ⟨t1, m1, h1, h2, h3, hn⟩
    exact ⟨(t, g.b, g.S, g.ws, g.R, kfOf E s l g), mem_dnOf.2 ⟨g, hg, hgl, t, ht, rfl⟩, us, i, hus, hb, hio,
      kfOf_single hus hsing hk⟩

#print axioms hcovD_coreQ

end TermOverCrW

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **(O-cov, owner → storer)** An outstanding promise of thread `j` is a foreign promise of
every other thread `k` (`PromsOK` with disjoint promise sets). -/
theorem mem_fpOf_of_prom {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {t : Ts}
    (hP : PromsOK Eg c) (hD : PromsDisj c) (hjk : j ≠ k) (hj : c.ths[j]? = some thj)
    (hk : c.ths[k]? = some thk) (ht : t ∈ thj.promises) : t ∈ Eg.fpOf k := by
  have hall : t ∈ allProms c := TermStepper.mem_allProms.2 ⟨j, thj, hj, ht⟩
  rcases List.mem_append.1 ((hP k thk hk t).2 hall) with h | h
  · exact absurd h (hD j k thj thk t hjk hj hk ht)
  · exact h

#print axioms mem_fpOf_of_prom

/-- The same at the storer's cut. -/
theorem mem_cut_fp_of_prom {Eg : GEnv} {c : Cfg} {j k : Nat} {thj thk : TTh} {t : Ts} {Sk : AllocLabel → Prop}
    (hP : PromsOK Eg c) (hD : PromsDisj c) (hjk : j ≠ k) (hj : c.ths[j]? = some thj)
    (hk : c.ths[k]? = some thk) (ht : t ∈ thj.promises) : t ∈ (Cut Eg k Sk).fp :=
  mem_fpOf_of_prom hP hD hjk hj hk ht

#print axioms mem_cut_fp_of_prom

end TermOverCrW
