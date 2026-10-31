import WeakCore.GenLayer
import WeakCore.TermCut
import WeakCore.TermTyped
import WeakCore.TermBlkZ
import WeakCore.TermInterf
import WeakCore.TermPubW
import WeakCore.TermOwnX2
import WeakCore.TermOwnHeldQ
import WeakCore.TermOwnK1
import WeakCore.TermOwnK2
import WeakCore.TermOwnK3
import WeakCore.TermOwnK4
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
set_option autoImplicit false
set_option maxErrors 100000
namespace TermSound.Flat
def anchorK_TermSound : Unit := ()
end TermSound.Flat
namespace TermMem.Flat
def anchorK_TermMem : Unit := ()
end TermMem.Flat
namespace TermTear.Flat
def anchorK_TermTear : Unit := ()
end TermTear.Flat
namespace TermStep.Flat
def anchorK_TermStep : Unit := ()
end TermStep.Flat
namespace TermCut.Flat
def anchorK_TermCut : Unit := ()
end TermCut.Flat
namespace TermTyped.Flat
def anchorK_TermTyped : Unit := ()
end TermTyped.Flat
namespace TermBlkZ.Flat
def anchorK_TermBlkZ : Unit := ()
end TermBlkZ.Flat
namespace TermInterf.Flat
def anchorK_TermInterf : Unit := ()
end TermInterf.Flat
namespace TermPubW.Flat
def anchorK_TermPubW : Unit := ()
end TermPubW.Flat
namespace TermOwnX2.Flat
def anchorK_TermOwnX2 : Unit := ()
end TermOwnX2.Flat
namespace TermOwnHeldQ.Flat
def anchorK_TermOwnHeldQ : Unit := ()
end TermOwnHeldQ.Flat
namespace TermOwnK1.Flat
def anchorK_TermOwnK1 : Unit := ()
end TermOwnK1.Flat
namespace TermOwnK2.Flat
def anchorK_TermOwnK2 : Unit := ()
end TermOwnK2.Flat
namespace TermOwnK3.Flat
def anchorK_TermOwnK3 : Unit := ()
end TermOwnK3.Flat
namespace TermOwnK4.Flat
def anchorK_TermOwnK4 : Unit := ()
end TermOwnK4.Flat
-- PORTB TermSound.lean:10096 TEnv.ownTop_substTs
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem _root_.TermSound.TEnv.ownTop_substTsBcw1 (σs : List Ty) (η : TEnv) (ρ₀ : Nat → Nat) (P : List Ty) (d : Nat) (t : Ty) :
    (TEnv.pre P η).ownTop (substTs σs P.length d t) = (TEnv.pre P (subEB ρ₀ η σs)).ownTop t := by
  rw [TEnv.ownTop_substTs σs η ρ₀ P d t]
  have hw := pre_subEB_wit (ρ₀ := ρ₀) (η := η) (σs := σs) P
  cases t <;> simp only [TEnv.ownTop, hw]
end
end TermSound.Flat

-- K10 (D-TV): witness-arm coherence.  At an inhabited variable, a value of
-- the witness (at CE) is a value of the variable.  Vacuous at CE envs; stable
-- under push0 / unsee.
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
def Z1 (η : TEnv) : Prop :=
  ∀ k S ws, (∃ S0 w0, η.rels k S0 w0) → VRz (fun _ => 0) (CE η) False (η.wit k) S ws → η.rels k S ws
def RInvZ (η : TEnv) : Prop := RInv η ∧ Z1 η ∧ Z1 η.unsee
theorem RInvZ_unsee {η : TEnv} (h : RInvZ η) : RInvZ η.unsee := ⟨RInv_unsee h.1, h.2.2, h.2.2⟩
theorem Z1_push0 {η : TEnv} (h : Z1 η) (s : Ty) : Z1 (η.push0 s) := by
  intro k S ws hne hz
  cases k with
  | zero => obtain ⟨S0, w0, h0⟩ := hne; simp [TEnv.push0, TEnv.ins, TEnv.insR] at h0
  | succ k =>
      have e1 : (η.push0 s).rels (k + 1) = η.rels k := by simp [TEnv.push0, TEnv.ins, TEnv.insR]
      have e2 : (η.push0 s).wit (k + 1) = η.wit k := by simp [TEnv.push0, TEnv.ins, TEnv.insR]
      have e3 : CE (η.push0 s) = CE η := rfl
      rw [e1] at hne ⊢; rw [e2, e3] at hz; exact h k S ws hne hz
theorem RInvZ_push0 {η : TEnv} (h : RInvZ η) (s : Ty) : RInvZ (η.push0 s) :=
  ⟨RInv_push0 h.1 s, Z1_push0 h.2.1 s, Z1_push0 h.2.2 s⟩
theorem RInvZ_CE (η : TEnv) : RInvZ (CE η) :=
  ⟨RInv_CE η, fun _ _ _ ⟨_, _, h⟩ _ => (h : False).elim, fun _ _ _ ⟨_, _, h⟩ _ => (h : False).elim⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11331 VR_VRR
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_VRRB : ∀ (t : Ty) {ρ : Nat → Nat} {η : TEnv} {rt : Shp} {ws : List Word},
    noIallV t = true → RInvZ η → (VRF False) ρ η t rt ws → ∃ R, VRRB ρ η t rt ws R := by
  intro t
  induction t with
  | iall b _ => intro ρ η rt ws hn; simp [noIallV] at hn
  | refine t ψ ih =>
      intro ρ η rt ws hn hr h; simp only [VRF, VRb2] at h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) hr h.1
      exact ⟨R, by simp only [VRRB]; exact ⟨hR, h.2⟩⟩
  | iex b ih =>
      intro ρ η rt ws hn hr h; simp only [VRF, VRb2] at h
      obtain ⟨n, rb, w, e, h⟩ := h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) hr h
      exact ⟨R, by simp only [VRRB]; exact ⟨n, rb, w, e, hR⟩⟩
  | prod a b iha ihb =>
      intro ρ η rt ws hn hr h; simp only [VRF, VRb2] at h
      simp only [noIallV, Bool.and_eq_true] at hn
      obtain ⟨ra, rb, e, h⟩ := h
      cases hw : ra.wc with
      | none =>
          refine ⟨.zero, ?_⟩
          simp only [VRRB]
          refine ⟨ra, rb, e, .zero, .zero, ?_, ?_, ?_⟩
          · exact (Res.zero_add _).symm
          · intro _; trivial
          · intro n hn'; rw [hw] at hn'; cases hn'
      | some n =>
          obtain ⟨hl, h1, h2⟩ := h n hw
          obtain ⟨Ra, hRa⟩ := iha hn.1 hr h1
          obtain ⟨Rb, hRb⟩ := ihb hn.2 hr h2
          refine ⟨Ra + Rb, ?_⟩
          simp only [VRRB]
          refine ⟨ra, rb, e, Ra, Rb, rfl, ?_, ?_⟩
          · intro h0; rw [hw] at h0; cases h0
          · intro n' hn'; rw [hw] at hn'; cases hn'; exact ⟨hl, hRa, hRb⟩
  | sum a b iha ihb =>
      intro ρ η rt ws hn hr h; simp only [VRF, VRb2] at h
      simp only [noIallV, Bool.and_eq_true] at hn
      obtain ⟨n, Ra, Rb, e, h | ⟨j, p, hd, h1, h2⟩⟩ := h
      · obtain ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6, hL, hR⟩ := h
        by_cases hj : B.tag - s < (armsOf Ra).length
        · obtain ⟨q1, q2⟩ := hL hj
          cases hb : isBoxed Ra with
          | true =>
              obtain ⟨R, hR'⟩ := iha hn.1 hr (q1 hb)
              refine ⟨R, ?_⟩
              simp only [VRRB]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun _ => ⟨fun _ => hR', fun hb' => (by rw [hb] at hb'; cases hb')⟩,
                fun hj' => absurd hj (Nat.not_lt.2 hj')⟩⟩
          | false =>
              obtain ⟨q, d1, d2, d3, d4, d5⟩ := q2 hb
              obtain ⟨R, hR'⟩ := iha hn.1 (RInvZ_unsee hr) d5
              refine ⟨R, ?_⟩
              simp only [VRRB]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun _ => ⟨fun hb' => (by rw [hb] at hb'; cases hb'), fun _ => ⟨q, d1, d2, d3, d4, hR'⟩⟩,
                fun hj' => absurd hj (Nat.not_lt.2 hj')⟩⟩
        · have hj2 : (armsOf Ra).length ≤ B.tag - s := Nat.not_lt.1 hj
          obtain ⟨q1, q2⟩ := hR hj2
          cases hb : isBoxed Rb with
          | true =>
              obtain ⟨R, hR'⟩ := ihb hn.2 hr (q1 hb)
              refine ⟨R, ?_⟩
              simp only [VRRB]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun hj' => absurd hj' hj,
                fun _ => ⟨fun _ => hR', fun hb' => (by rw [hb] at hb'; cases hb')⟩⟩⟩
          | false =>
              obtain ⟨q, d1, d2, d3, d4, d5⟩ := q2 hb
              obtain ⟨R, hR'⟩ := ihb hn.2 (RInvZ_unsee hr) d5
              refine ⟨R, ?_⟩
              simp only [VRRB]
              exact ⟨n, Ra, Rb, e, Or.inl ⟨ht, x, s, B, c1, c2, c3, c4, c5, c6,
                fun hj' => absurd hj' hj,
                fun _ => ⟨fun hb' => (by rw [hb] at hb'; cases hb'), fun _ => ⟨q, d1, d2, d3, d4, hR'⟩⟩⟩⟩
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, d1, d2⟩ := h1 hj
          obtain ⟨R, hR'⟩ := iha hn.1 hr d2
          refine ⟨R, ?_⟩
          simp only [VRRB]
          exact ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun _ => ⟨q, d1, hR'⟩,
            fun hj' => absurd hj (Nat.not_lt.2 hj')⟩⟩
        · obtain ⟨q, d1, d2⟩ := h2 (Nat.not_lt.1 hj)
          obtain ⟨R, hR'⟩ := ihb hn.2 hr d2
          refine ⟨R, ?_⟩
          simp only [VRRB]
          exact ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun hj' => absurd hj' hj, fun _ => ⟨q, d1, hR'⟩⟩⟩
  | tvar k =>
      intro ρ η rt ws _ hr h; simp only [VRF, VRb2] at h
      obtain ⟨ws', hw, h | ⟨hz, hne⟩⟩ := h
      · obtain ⟨R, hR⟩ := hr.1.1 k rt ws' h
        exact ⟨R, by simp only [VRRB]; exact ⟨ws', hw, Or.inl hR⟩⟩
      · obtain ⟨R, hR⟩ := hr.1.1 k rt ws' (hr.2.1 k rt ws' hne hz)
        exact ⟨R, by simp only [VRRB]; exact ⟨ws', hw, Or.inl hR⟩⟩
  | tex κ b ih =>
      intro ρ η rt ws hn hr h; simp only [VRF, VRb2] at h
      obtain ⟨n, rb, s, e, hc, hk, h⟩ := h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) (RInvZ_push0 hr s) h
      exact ⟨R, by simp only [VRRB]; exact ⟨n, rb, s, e, hc, hk, hR⟩⟩
  | mu b ih =>
      intro ρ η rt ws hn hr h; simp only [VRF, VRb2] at h
      obtain ⟨R, hR⟩ := ih (by simpa [noIallV] using hn) (RInvZ_push0 hr _) h
      exact ⟨R, by simp only [VRRB]; exact hR⟩
  | void => intro ρ η rt ws _ _ h; simp only [VRF, VRb2] at h
  | word r P =>
      intro ρ η rt ws _ _ h; simp only [VRF, VRb2] at h
      by_cases hw : WordHolds P (ws.map (·.val))
      · exact ⟨_, by simp only [VRRB]; exact ⟨h, Or.inl ⟨hw, rfl⟩⟩⟩
      · exact ⟨_, by simp only [VRRB]; exact ⟨h, Or.inr ⟨hw, rfl⟩⟩⟩
  | word2 r P =>
      intro ρ η rt ws _ _ h; simp only [VRF, VRb2] at h
      by_cases hw : Word2Holds P (ws.map (·.val))
      · exact ⟨_, by simp only [VRRB]; exact ⟨h, Or.inl ⟨hw, rfl⟩⟩⟩
      · exact ⟨_, by simp only [VRRB]; exact ⟨h, Or.inr ⟨hw, rfl⟩⟩⟩
  | intS | int | opq _ | tid | fix | lanes | code | epair =>
      intro ρ η rt ws _ _ h; simp only [VRF, VRb2] at h; exact ⟨_, by simp only [VRRB]; exact ⟨h, rfl⟩⟩
  | ptr | loc | ptrOpt =>
      intro ρ η rt ws _ _ h; simp only [VRF, VRb2] at h; exact ⟨_, by simp only [VRRB]; exact ⟨h, rfl⟩⟩
  | unit | cap | tok | tok2 | tokE | share | array =>
      intro ρ η rt ws _ _ _; exact ⟨_, by simp only [VRRB]; exact rfl⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11453 RInv_of
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem RInv_ofB {η : TEnv} (hc : CohBW η) (hr : CohRB η) (hw : WitAF η) : RInv η := by
  refine ⟨fun k S ws h => ?_, fun k S ws h => ?_⟩
  · obtain ⟨R, hR⟩ := VR_VRRB (η.wit k) (hw k).2.1 (RInvZ_CE η) (((hc k).2.1 (fun _ => 0) S ws).1 h)
    exact ⟨R, ((hr k).1 (fun _ => 0) S ws R).2 hR⟩
  · obtain ⟨R, hR⟩ := VR_VRRB (η.wit k) (hw k).2.1 (RInvZ_CE η.unsee) (((hc k).2.2 (fun _ => 0) S ws).1 h)
    exact ⟨R, ((hr k).2 (fun _ => 0) S ws R).2 hR⟩
theorem RInvZ_ofB {η : TEnv} (hc : CohBW η) (hr : CohRB η) (hw : WitAF η) : RInvZ η :=
  ⟨RInv_ofB hc hr hw, fun k S ws _ hz => ((hc k).2.1 (fun _ => 0) S ws).2 (VRz_VRb2 _ _ _ _ _ _ hz),
    fun k S ws _ hz => ((hc k).2.2 (fun _ => 0) S ws).2 (VRz_VRb2 _ _ _ _ _ _ hz)⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11462 RetOKR_RetOK
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem RetOKR_RetOKB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {ret : Ty}
    {KR : TEnv → Nat → List Word → Res → Prop} {K : TEnv → List Word → Prop}
    (hn : noIallV ret = true) (hw : WitAF η) (hK : ∀ E rd ws R, KR E rd ws R → K E ws)
    (h : RetOKRB glb gnum gi ρ η σs ret KR) : RetOKB glb gnum gi ρ η σs ret K := by
  intro η' he hS ws hv hl
  have hw' : WitAF η' := fun k => by rw [he.2.1]; exact hw k
  obtain ⟨R, hR⟩ := VR_VRRB ret hn (RInvZ_ofB he.1 he.2.2.2.2.2.2.2.2.2.2.1 hw') hv
  exact hK _ _ _ _ (h η' he hS ws R hR hl)
end
end TermSound.Flat

-- PORTB TermSound.lean:11472 FInvR_FInv
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem FInvR_FInvB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {KR : TEnv → Nat → List Word → Res → Prop}
    {K : TEnv → List Word → Prop} {cx : Cx} {env : Env} {Rf : Res}
    (hn : noIallV cx.ret = true) (hK : ∀ E rd ws R, KR E rd ws R → K E ws)
    (h : FInvRB glb gnum gi ρ η σs KR cx env Rf) : FInvB glb gnum gi ρ η σs K cx env :=
  ⟨h.1.1, h.1.2.1, RetOKR_RetOKB hn h.1.2.2.2.2.2.2.1 hK h.2.1, h.1.2.2.2⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:11480 ResumeR_Resume
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem ResumeR_ResumeB {p : Prog} (hT : ∀ c : Cx, TvOK c → noIallV c.ret = true) :
    ∀ (st : List Frame) (Rs : Res) (E : TEnv) (rd : Nat) (ws : List Word) (R : Res),
      ResumeRB glb gnum gi p st Rs E rd ws R → ResumeB glb gnum gi p st E ws
  | [], _, _, _, _, _, _ => trivial
  | _ :: rest, _, _, _, _, _, h => by
      obtain ⟨Rc, Rrest, -, ρ, η, c, hCE, -, hEO, hTy, hTv, hF, hpw, hDF⟩ := h
      exact ⟨ρ, η, c, hCE, hEO, hTy.1, hTv,
        FInvR_FInvB (hT c hTv) (fun E rd ws R h => ResumeR_ResumeB hT rest Rrest E rd ws R h) hF, hpw, hDF⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:14493 WitL_call
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem WitL_callB {σs ts : List Ty} {η : TEnv} {ρ : Nat → Nat} {cx : Cx} (hW : WitL σs η.wit cx.opq)
    (hK : cx.ke.length ≤ σs.length) (hC : ∀ k, Clo (η.wit k))
    (hts : ∀ σ ∈ ts, cx.opaqueOK σ = true ∧ σ.wf cx.ke.length cx.inames.length = true) :
    WitL (ts.map (close σs)).reverse (subEB ρ η ts.reverse).wit [] := by
  have hr : ∀ σ ∈ ts, ∀ j, σ.guardT j = false → j < σs.length := fun σ hm j hj =>
    Nat.lt_of_not_le (fun hc => by
      have := guardT_of_wf σ _ _ j (hts σ hm).2 (Nat.le_trans hK hc)
      rw [hj] at this; cases this)
  refine ⟨fun k _ hk => ?_, fun k σ' hσ' => ⟨fun _ => ?_, fun h => by cases h⟩, fun k _ hk => ?_⟩
  rotate_left
  · rw [← List.map_reverse, List.getElem?_map] at hσ'
    cases hσ : ts.reverse[k]? with
    | none => simp [hσ] at hσ'
    | some σ =>
        simp only [hσ, Option.map_some, Option.some.injEq] at hσ'
        subst hσ'
        rw [subEB_wit_lt hσ]
        have hmem : σ ∈ ts := List.mem_reverse.1 (List.mem_of_getElem? hσ)
        exact zrel_WitL hW hC ρ (hts σ hmem).1 (hr σ hmem)
  · have hk' : k < ts.reverse.length := by simpa using hk
    have hσ : ts.reverse[k]? = some (ts.reverse[k]'hk') := List.getElem?_eq_getElem hk'
    generalize ts.reverse[k]'hk' = σ at hσ
    have hmem : σ ∈ ts := List.mem_reverse.1 (List.mem_of_getElem? hσ)
    obtain ⟨ho, hwf⟩ := hts σ hmem
    have e1 : ((ts.map (close σs)).reverse)[k]? = some (close σs σ) := by
      rw [← List.map_reverse, List.getElem?_map, hσ]; rfl
    have e2 : accs (close (ts.map (close σs)).reverse (.tvar k)) = accs (close σs σ) := by
      show accs (substTs _ 0 0 (.tvar k)) = _
      simp only [substTs, Nat.not_lt_zero, if_false, ite_false, Nat.sub_zero, e1, accs_shiftIN, accs_shiftTN]
    rw [e2, subEB_wit_lt hσ]
    refine accs_WitL hW hC ρ ho (fun j hj => Nat.lt_of_not_le (fun hc => ?_))
    have := guardT_of_wf σ _ _ j hwf (Nat.le_trans hK hc)
    rw [hj] at this; cases this
  have hk' : k < ts.reverse.length := by simpa using hk
  have hσ : ts.reverse[k]? = some (ts.reverse[k]'hk') := List.getElem?_eq_getElem hk'
  generalize ts.reverse[k]'hk' = σ at hσ
  have hmem : σ ∈ ts := List.mem_reverse.1 (List.mem_of_getElem? hσ)
  obtain ⟨ho, hwf⟩ := hts σ hmem
  have e1 : ((ts.map (close σs)).reverse)[k]? = some (close σs σ) := by
    rw [← List.map_reverse, List.getElem?_map, hσ]; rfl
  have e2 : sig (close (ts.map (close σs)).reverse (.tvar k)) = sig (close σs σ) := by
    show sig (substTs _ 0 0 (.tvar k)) = _
    simp only [substTs, Nat.not_lt_zero, if_false, ite_false, Nat.sub_zero, e1, sig_shiftIN, sig_shiftTN]
  rw [e2, subEB_wit_lt hσ]
  refine sig_WitL hW ρ ho (fun j hj => Nat.lt_of_not_le (fun hc => ?_))
  have := guardT_of_wf σ _ _ j hwf (Nat.le_trans hK hc)
  rw [hj] at this; cases this
end
end TermSound.Flat

-- PORTB TermSound.lean:14549 WitAF_subE
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem WitAF_subEB {ρ₀ : Nat → Nat} {η : TEnv} {σs : List Ty} (hw : WitAF η)
    (hs : ∀ σ ∈ σs, σ.arrFree = true) (hn : ∀ σ ∈ σs, noIallV σ = true)
    (hC : ∀ k, Clo (η.wit k)) (hm : ∀ σ ∈ σs, TermTv.mg σ = true) : WitAF (subEB ρ₀ η σs) := by
  intro k
  show (match σs[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - σs.length)).arrFree = true ∧
    noIallV (match σs[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - σs.length)) = true ∧
    TermTv.mg (match σs[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - σs.length)) = true
  split
  · rename_i σ h
    exact ⟨arrFree_cl hw.af σ 0 0 (hs σ (List.mem_of_getElem? h)), noIallV_cl hw.ni σ 0 0 (hn σ (List.mem_of_getElem? h)),
      TermTv.mg_cl (fun k => (hC k).1) hw.mg σ 0 0 (hm σ (List.mem_of_getElem? h))⟩
  · exact hw _
end
end TermSound.Flat

-- PORTB TermSound.lean:14562 WitSh_call
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem WitSh_callB {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hC : ∀ k, Clo (η.wit k)) (hS : WitSh cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    WitSh (d.tparams.reverse.map some) (subEB ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hsh : κ.share = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show Ty.coupledOK (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = true
    rw [e]
    exact coupledOK_cl0 ρ₀ η.wit cx.ke hC (fun k _ hk => hS k hk) (admitsIn_share had hsh)
      (tb_of_wf σ (admitsIn_wf had))
end
end TermSound.Flat

-- PORTB TermSound.lean:14589 WitC_call
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem WitC_callB {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hC : ∀ k, Clo (η.wit k)) (hS : WitC cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    WitC (d.tparams.reverse.map some) (subEB ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hcp : κ.copy = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show Ty.affine (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = false
    rw [e]
    exact AffineCl.affine_cl0 ρ₀ η.wit cx.ke hC (fun k _ hk => hS k hk) σ ((admitsIn_word had).2 hcp)
      (tb_of_wf σ (admitsIn_wf had))
end
end TermSound.Flat

-- PORTB TermSound.lean:14616 WitN_call
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem WitN_callB {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hC : ∀ k, Clo (η.wit k)) (hS : WitN cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt)) :
    WitN (d.tparams.reverse.map some) (subEB ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hno : κ.noOwn = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show Ty.noOwn (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = true
    rw [e]
    exact NoOwnCl.noOwn_cl0 ρ₀ η.wit cx.ke hC (fun k _ hk => hS k hk) σ (admitsIn_noOwn had hno)
      (tb_of_wf σ (admitsIn_wf had))
end
end TermSound.Flat

-- PORTB TermSound.lean:14646 WitR_call
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem WitR_callB {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hS : WitR cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt))
    (hrt : ∀ σ ∈ ts, rgnFree σ = true) :
    WitR (d.tparams.reverse.map some) (subEB ρ₀ η ts.reverse) := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  intro k hk
  have e0 : (d.tparams.reverse.map some : KEnv)[k]? = d.tparams.reverse[k]?.map some := List.getElem?_map ..
  unfold KEnv.ask at hk
  rw [e0] at hk
  cases hκ : d.tparams.reverse[k]? with
  | none => rw [hκ] at hk; simp at hk
  | some κ =>
    have hsh : κ.share = true := by rw [hκ] at hk; simpa using hk
    have hkl : k < d.tparams.length := by
      have := (List.getElem?_eq_some_iff.mp hκ).1; simpa using this
    rw [List.getElem?_reverse hkl] at hκ
    have hj : d.tparams.length - 1 - k < ts.length := by omega
    have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
      List.getElem?_eq_getElem hj
    generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
    have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
    have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
    have had := ha κ σ hm
    show rgnFree (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = true
    rw [e]
    exact rgnFree_cl0 ρ₀ η.wit cx.ke hS (admitsIn_share had hsh) (hrt σ (List.mem_of_getElem? hσ))
end
end TermSound.Flat

-- PORTB TermStep.lean:3540 MemInv_noOwnT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem MemInv_noOwnTB {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} {f : Ts}
    (hm : MemInvB g E s) (hsto : E.sto l = some c) (hf : E.pfr l = some f) : Ty.noOwnIn [] c.ty = true :=
  (hm.2.2.2.2.2.2.2.2.1.2.2.1 l c f hsto hf).2.2.2.1
end
end TermStep.Flat

-- PORTB TermStep.lean:14488 MemInv_plantF
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
theorem MemInv_plantFB {g : G} {E E' : TEnv} {s : St} {l : AllocLabel} {c : Cell} {F : Ts}
    (hm : MemInvB g E s) (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hnone : E.pfr l = none)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto) (hi : E'.ini = E.ini)
    (hP : E'.pfr = fun l' => if l' = l then some F else E.pfr l') (hS : E'.seen = E.seen) (hR : E'.rini = E.rini)
    (hF : F ≤ s.vs.vWr ∨ HoldW E s l F)
    (hcpl : ∀ b S, SegOf c.ty b S → accs S ≠ none → TearOKB S) (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true)
    (hbx : ∀ l B, E.box l = some B → E'.box l = some B := by first | exact fun _ _ h => h | simp_all | (intro _ _ h; simpa [CE, TEnv.withStoB] using h))
    (hbe : E'.box = E.box := by first | rfl | simp_all)
    (hri : ∀ l, E.rini l ≤ E'.rini l := by rini_le) :
    MemInvB g E' s := by
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  have hsub : ∀ l c, E.sto l = some c → E'.sto l = some c := fun l c h => by rw [hs]; exact h
  have hile : ∀ l, E.ini l ≤ E'.ini l := fun l => by rw [hi]; exact Nat.le_refl _
  have hPne : ∀ l', l' ≠ l → E'.pfr l' = E.pfr l' := fun l' he => by rw [hP]; simp only [he, ↓reduceIte]
  have hPm : ∀ l' f, E.pfr l' = some f → E'.pfr l' = some f := fun l' f h => by
    by_cases he : l' = l
    · rw [he, hnone] at h; cases h
    · rw [hPne l' he]; exact h
  have hSm : ∀ l', E.seen l' → E'.seen l' := fun l' h => by rw [hS]; exact h
  have hmono : ∀ {U : Ty} {vs : List Word}, ValOfB E U vs → ValOfB E' U vs :=
    fun h => ValOf_monoB hp ht hsub hile h hPm hSm hbx
  have hwE : ∀ T o w, WordOKB E T o w → WordOKB E' T o w := fun T o w h =>
    WordOK_monoB hp ht hsub hile hPm hSm h hbx
  have hiniR : ∀ c' l' o, InitR E' c' l' o → InitR E c' l' o := fun c' l' o h N e us h1 h2 => by
    have := h N e us h1 h2; rw [hi] at this; exact this
  have hrcE : ∀ l', E'.rc l' = E.rc l' := fun l' => TEnv.rc_congr (by rw [hi]) (by rw [hR])
  have hnew0 : ∀ (l' : AllocLabel) (o : Nat) (t : Nat) (m : Msg), s.mem.size ≤ t → s.mem[t]? = some m →
      m.loc = ⟨l', o⟩ → ∀ T, WordOKB E' T o (mw m) := fun _ _ t m ht hm _ _ =>
    (Nat.not_le.2 (lt_of_get hm) ht).elim
  refine ⟨MemOKP_monoB hmo hp ht hsub hile (fun t m c h hc => by rw [hs] at hc; exact hc) hPm hSm hbx,
    ?_, hpl, ?_, ?_, ?_, ?_, ?_, ?_, BoxInv_tr hbi hbe (fun _ _ _ h => by rw [hS] at h; exact h)
      (fun l _ _ => by rw [hs]) (fun l _ _ => by rw [hi])
      (Nat.le_refl _) (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h), hpo⟩
  · 
    intro l' c' hc ho
    rw [hs] at hc
    refine OwnCellF_pubB (hoo l' c' hc (by rw [ht]; exact ho)) hmono (by rw [hi]) ?_ hmo.2.2 (by rw [hR])
    by_cases he : l' = l
    · subst he; exact Or.inl hnone
    · exact Or.inr (hPne l' he)
  · 
    refine ⟨fun j hj => ?_, PrivCoh_env (s := s) hfr.2 hs ht hPm fun l' => Nat.le_of_eq (hrcE l').symm⟩

    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj
    have hne : freshLabel g.lbase g.n g.i j ≠ l := fun he => by rw [he, hsto] at f1; cases f1
    exact ⟨by rw [hs]; exact f1, f2, by rw [hi]; exact f4, by rw [hR]; exact f5.1, by rw [hPne _ hne]; exact f5.2⟩
  · 
    intro l' hl'
    rw [hS] at hl'
    obtain ⟨f, h1, h2⟩ := hsn l' hl'
    exact ⟨f, hPm l' f h1, h2⟩
  · 
    refine ⟨fun l' c' hc ho o hio => ?_, fun l' c' hc ho hlt => ?_⟩
    · rw [hs] at hc
      exact HiddenP_growB (hoh.1 l' c' hc (by rw [ht]; exact ho) o (fun N e us h1 h2 => by
          have := hio N e us h1 h2; rw [hrcE] at this; exact this)) (hwE _ _)
        (Nat.le_refl _) (fun _ _ => rfl) (fun t m ht' hm hl => hnew0 l' o t m ht' hm hl _)
        (fun _ _ h1 h2 => absurd h1 h2)
    · rw [hs] at hc
      rw [hrcE, hi] at hlt
      obtain ⟨f, hf, hns, hH⟩ := hoh.2 l' c' hc (by rw [ht]; exact ho) hlt
      have he : l' ≠ l := fun he => by rw [he, hnone] at hf; cases hf
      refine ⟨f, by rw [hPne _ he]; exact hf,
        by rw [hS]; exact fun hz => hns (fun hz0 => hz ((ZW.stoAt (congrFun hs l')).2 hz0)), fun o hio => ?_⟩
      exact HiddenP_growB (hH o (hiniR c' l' o hio)) (hwE _ _)
        (Nat.le_refl _) (fun _ _ => rfl) (fun t m ht' hm hl => hnew0 l' o t m ht' hm hl _)
        (fun _ _ h1 h2 => absurd h1 h2)
  · 
    intro l' c' f hc hown' hf o hio
    rw [hs] at hc
    by_cases he : l' = l
    · rw [he, hsto] at hc
      cases hc
      exact (hown' (by rw [← ht]; exact hown)).elim
    · rw [hPne _ he] at hf
      exact HiddenP_growB (hpd l' c' f hc (by rw [ht]; exact hown') hf o (hiniR c' l' o hio)) (hwE _ _)
        (Nat.le_refl _) (fun _ _ => rfl) (fun t m ht' hm hl => hnew0 l' o t m ht' hm hl _)
        (fun _ _ h1 h2 => absurd h1 h2)
  · 
    intro l' c' f hc ho hf
    rw [hS]
    rw [hs] at hc
    by_cases he : l' = l
    · subst he
      rw [hP] at hf
      simp at hf
      subst hf
      rcases hF with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (h.congrE fun _ _ h => IniWr.ofEq hs hi hR h))
    · rw [hPne _ he] at hf
      exact (hopub l' c' f hc (by rw [ht]; exact ho) hf).imp id
        (Or.imp id fun h => h.congrE fun _ _ h => IniWr.ofEq hs hi hR h)
  · 
    obtain ⟨hS0, hI0, hC0, hPP0, hLV0⟩ := hpi
    refine ⟨fun l' hl' => ?_, fun l' c' b S us hc hseg hu hini => ?_, fun l' c' f hc hf => ?_, ?_, ?_⟩
    · rw [hS] at hl'
      rcases hS0 l' hl' with ⟨c', h1, h2⟩ | ⟨h1, h2⟩
      · exact .inl ⟨c', by rw [hs]; exact h1, by rw [← ht]; exact h2⟩
      · exact .inr ⟨by rw [hs]; exact h1, by rw [hbe]; exact h2⟩
    · rw [hs] at hc
      obtain ⟨ws, h1, h2⟩ := hI0 l' c' b S us hc hseg hu (fun N e h1 => by
        have := hini N e h1; rw [hi] at this; exact this)
      exact ⟨ws, hmono h1, h2⟩
    · rw [hs] at hc
      by_cases he : l' = l
      · rw [he, hsto] at hc
        rw [← Option.some.inj hc]
        obtain ⟨vals, hcell, -⟩ := hoo l c hsto hown
        exact ⟨LayT_of_CellOKB hcell, hcpl, hcT, hnT, hrT⟩
      · rw [hPne _ he] at hf; exact hC0 l' c' f hc hf
    · intro l' c' f o hc hown' hf htw t0 t1 m0 m1 hn0 hn1 hm0 hm1 hl0 hl1 hh0 hh1 hst
      rw [hs] at hc
      have he : l' ≠ l := fun he => by
        rw [he, hsto] at hc
        rw [← Option.some.inj hc] at hown'
        rcases hown' with ⟨h, -⟩ | ⟨h, -⟩
        · exact h (by rw [← ht]; exact hown)
        · rw [he, hrcE, hi] at h
          obtain ⟨f', hf', -⟩ := hoh.2 l c hsto hown h
          rw [hnone] at hf'; cases hf'
      rw [hPne _ he] at hf
      exact PairOK_monoB hp ht hsub hile hPm hSm
        (hPP0 l' c' f o hc (PubG_tr ht (Nat.le_of_eq (hrcE l').symm) (fun h => ⟨by rw [hrcE, hi] at h; exact h, Nat.le_of_eq (by rw [hi])⟩)
          (fun _ => Nat.le_of_eq (by rw [hi])) hown') hf htw t0 t1 m0 m1 hn0 hn1 hm0 hm1 hl0 hl1 hh0 hh1 hst) hbx
    · intro l' c' f b S us o hc hown' hf hseg hu ho
      rw [hs] at hc
      have he : l' ≠ l := fun he => by
        rw [he, hsto] at hc
        rw [← Option.some.inj hc] at hown'
        exact hown' (by rw [← ht]; exact hown)
      rw [hPne _ he] at hf
      exact hLV0 l' c' f b S us o hc (by rw [ht]; exact hown') hf hseg hu ho
end
end TermStep.Flat

-- PORTB TermStep.lean:15390 InhZ
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
set_option hygiene false in
set_option hygiene false in
def InhZB (P : Prog) (e : Ty) : Prop := ∃ ws, ValOfB ({ prog := P } : TEnv) e ws ∧ ws.length = 0
end
end TermStep.Flat

-- PORTB TermStep.lean:44350 PlantCr
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def PlantCrB (E : TEnv) (s : St) (m : Msg) (tw : Ts) (R : Res) : Prop :=
  ∃ c sb S0 b0 S us wb, E.sto m.loc.label = some c ∧ c.owner = some E.tid ∧ E.pfr m.loc.label ≠ none ∧
    SegOf c.ty sb S0 ∧ AtOff S0 b0 S ∧ Solid S ∧ ¬ WordUnit E m.loc ∧ accs S = some us ∧ 0 < nWords us ∧
    sb + b0 ≤ m.loc.offset ∧ m.loc.offset < sb + b0 + nWords us ∧ tw ≤ wb ∧ wb < s.mem.size ∧
    (∀ tf mf, tf ∈ FpAt E ⟨m.loc.label, 0⟩ → s.mem[tf]? = some mf → mf.loc.label = m.loc.label → wb < tf) ∧
    (∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = m.loc.label →
      sb + b0 ≤ m'.loc.offset → m'.loc.offset < sb + b0 + nWords us → t' ≤ wb → tw ≤ t') ∧
    ((∃ K ws R0, ws.length = nWords us ∧ ValOfRB E S ws R0 ∧ R0 ≤ R ∧
        PinW s.mem (winL wb s.promises) m.loc.label (sb + b0) us K ws) ∨
      R = .zero)
end
end TermStep.Flat

-- PORTB TermCut.lean:1329 MemHeldOn
namespace TermCut.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
def MemHeldOnB (Q : AllocLabel → Prop) (E : TEnv) (s : St) (H : Res) : Prop :=
  ∃ (L : List AllocLabel) (Rl : AllocLabel → Res), L.Nodup ∧ (∀ l c, Q l → E.sto l = some c → l ∈ L) ∧
    (∀ l, l ∈ L → Q l) ∧ H = Res.sum (L.map Rl) ∧ ∀ l, l ∈ L → HeldEntryB E s l (Rl l)
end
end TermCut.Flat

-- PORTB TermCut.lean:1334 MemHeldP
namespace TermCut.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
def MemHeldPB (E : TEnv) (s : St) (H : Res) : Prop := MemHeldOnB (Priv E) E s H
end
end TermCut.Flat

-- PORTB TermCut.lean:1337 MemHeldS
namespace TermCut.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
def MemHeldSB (E : TEnv) (s : St) (H : Res) : Prop := MemHeldOnB (fun l => ∃ f, E.pfr l = some f) E s H
end
end TermCut.Flat

-- PORTB TermCut.lean:1340 MemHeld_splitOn
namespace TermCut.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
theorem MemHeld_splitOnB (Q : AllocLabel → Prop) {E : TEnv} {s : St} {H : Res} (h : MemHeldB E s H) :
    ∃ H₁ H₂, H = H₁ + H₂ ∧ MemHeldOnB Q E s H₁ ∧ MemHeldOnB (fun l => ¬ Q l) E s H₂ := by
  classical
  obtain ⟨L, Rl, hn, hc, rfl, he⟩ := h
  refine ⟨Res.sum ((L.filter (fun l => decide (Q l))).map Rl),
    Res.sum ((L.filter (fun l => !decide (Q l))).map Rl), ?_,
    ⟨_, Rl, hn.filter _, fun l c hq hs => List.mem_filter.2 ⟨hc l c hs, by simpa using hq⟩,
      fun l hl => by simpa using (List.mem_filter.1 hl).2, rfl, fun l hl => he l (List.mem_filter.1 hl).1⟩,
    ⟨_, Rl, hn.filter _, fun l c hq hs => List.mem_filter.2 ⟨hc l c hs, by simpa using hq⟩,
      fun l hl => by simpa using (List.mem_filter.1 hl).2, rfl, fun l hl => he l (List.mem_filter.1 hl).1⟩⟩
  rw [← Res.sum_append, ← List.map_append]
  exact Res.sum_perm (List.filter_append_perm _ L).symm
end
end TermCut.Flat

-- PORTB TermTyped.lean:115 extArg_one
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
private theorem extArg_oneB {bkG : Prop} {ρ : Nat → Nat} {η : TEnv} {o : Opq} {sh : Shp} {ws : List Word}
    (h : (VRF bkG) ρ η (.opq o) sh ws) : ∃ w, ws = [w] := by
  obtain ⟨m, hm⟩ := h
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩ <;> simp at hm
  exact ⟨w, rfl⟩
end
end TermTyped.Flat

-- PORTB TermTyped.lean:121 extArg_pair
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
private theorem extArg_pairB {bkG : Prop} {ρ : Nat → Nat} {η : TEnv} {o : Opq} {sg : Bool} {wd : Wd} {sh : Shp} {ws : List Word}
    (h : (VRF bkG) ρ η (.prod (.opq o) (.fix sg wd)) sh ws) (hwc : sh.wc ≠ none) : ∃ w1 w2, ws = [w1, w2] := by
  obtain ⟨ra, rb, rfl, h⟩ := h
  cases hra : ra.wc with
  | none => simp [Shp.wc, hra] at hwc
  | some k =>
    obtain ⟨-, ⟨m, hm⟩, -, m2, hm2, -⟩ := h k hra
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> rcases k with _ | _ | _ | k <;> simp at hm hm2
    exact ⟨w1, w2, rfl⟩
end
end TermTyped.Flat

-- PORTB TermTyped.lean:137 mod_pw2
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
private theorem mod_pw2B (m : Nat) (w : Wd) : m % 2 ^ Wd.bits w < pw2 w := by
  rw [pw2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
end
end TermTyped.Flat

-- PORTB TermTyped.lean:142 ext_res
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ext_resB {bkG : Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {n : ExtName} {i : Nat} {ws : List Word} {tr : List Event}
    {rs : List Word} {rt : Ty} (hn : n ≠ .current) (hvr : (VRF bkG) ρ η n.sig.1 (shp rt) ws) (hwc : wc rt ≠ none)
    (hrs : rs ∈ n.resultsL i ws tr) :
    VRRB ρ η n.sig.2 (shp n.sig.2) rs .zero ∧ Lay σs n.sig.2 n.sig.2 rs := by
  rw [mem_resultsL] at hrs
  rw [← shp_wc] at hwc
  cases n with
  | current => exact absurd rfl hn
  | mmioR w acc o =>
    obtain ⟨r, rfl⟩ := extArg_oneB (bkG := bkG) hvr
    simp only [ExtName.Admits] at hrs; subst hrs
    refine ⟨⟨_, _, rfl, .zero, .zero, rfl, by simp [shp, Shp.wc, wc, accs], fun k hk => ?_⟩,
      Lay_pair (ws := [_]) (us := [_]) (Lay_opq σs _ _) (Lay_fix σs _ _ _)⟩
    simp [shp, Shp.wc, wc, accs, nWords, Acc.size] at hk; subst hk
    exact ⟨by simp, ⟨⟨_, rfl⟩, rfl⟩, ⟨rfl, _, rfl, mod_pw2B _ _⟩, rfl⟩
  | mmioW w acc o =>
    obtain ⟨r, v, rfl⟩ := extArg_pairB (bkG := bkG) hvr hwc
    simp only [ExtName.Admits] at hrs; subst hrs
    exact ⟨⟨⟨_, rfl⟩, rfl⟩, Lay_opq σs _ _⟩
  | regAt nb w acc st tk k =>
    obtain ⟨b, rfl⟩ := extArg_oneB (bkG := bkG) hvr
    simp only [ExtName.Admits] at hrs; subst hrs
    refine ⟨⟨_, _, rfl, .zero, .zero, rfl, by simp [shp, Shp.wc, wc, accs], fun k hk => ?_⟩,
      Lay_pair (ws := [_]) (us := [_]) (Lay_opq σs _ _) (Lay_opq σs _ _)⟩
    simp [shp, Shp.wc, wc, accs, nWords, Acc.size] at hk; subst hk
    exact ⟨by simp, ⟨⟨_, rfl⟩, rfl⟩, ⟨_, rfl⟩, rfl⟩
  | devRecv w =>
    obtain ⟨r, rfl⟩ := extArg_oneB (bkG := bkG) hvr
    simp only [ExtName.Admits] at hrs; subst hrs
    exact ⟨⟨⟨rfl, _, rfl, mod_pw2B _ _⟩, rfl⟩, Lay_fix σs _ _ _⟩
  | devChoice w =>
    simp only [ExtName.Admits] at hrs
    obtain ⟨v, hv, rfl⟩ := hrs
    exact ⟨⟨⟨rfl, _, rfl, by rw [pw2]; exact hv⟩, rfl⟩, Lay_fix σs _ _ _⟩
  | _ =>
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;>
      simp only [ExtName.Admits] at hrs <;> subst hrs <;>
      exact ⟨by simp [ExtName.sig, VRRB], Lay_unitT _⟩
end
end TermTyped.Flat

-- PORTB TermTyped.lean:230 ThInvRE_ext
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ThInvRE_extB {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} {x : String} {n : ExtName} {a : At} {e : Expr}
    {rt : Ty} {ws rs : List Word} {i : Nat} {tr : List Event} {vv : VState} {pm : Option Ts} (hn : n ≠ .current)
    (hterm : th.term = .let_ x (.ext n a) e) (hev : evalAt th.env a = some (rt, ws)) (hrs : rs ∈ n.resultsL i ws tr)
    (hR : ThInvREB glb gnum gi p E th Tot) :
    ThInvREB glb gnum gi p E { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := vv, permit := pm } Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw, hDy⟩ := hR
  have hT2 := hT.2
  rw [hterm] at hT2
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (TermTv.extSig_tb _ _) (TermTv.extSig_mg _)).1
    obtain ⟨rt1, ws1, R, Rr, hev1, hvr1, hl1, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    rw [hev] at hev1; cases hev1
    obtain ⟨hz, hl⟩ := ext_resB (bkG := False) (σs := th.σs) hn (VR_subB (bkG := False) hi1.1.1 hsub _ _ hvr1) hl1.2.2.1 hrs
    have hf := bindRZB hb (FInvR_monoB hi1 (le_of_add_le hle)) (RLink_ofB hE.2.1 hE.2.2) hz hl
    refine ⟨ρ, η, c', Rf, Rs, hCE, hE, ⟨he, hck⟩, htv', hf, hsum, ?_, hDy.letW hterm rfl⟩
    intro fr rest hst ws1
    rw [hret]; exact hpw fr rest hst ws1
end
end TermTyped.Flat

-- PORTB TermTyped.lean:266 lay_tidT
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
private theorem lay_tidTB (σs : List Ty) (L : AllocLabel) : Lay σs .tid .tid [cst (.loc ⟨L, 0⟩ 0)] :=
  ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
    by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩
end
end TermTyped.Flat

-- PORTB TermTyped.lean:270 vr_tidT
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
private theorem vr_tidTB {bkG : Prop} {ρ : Nat → Nat} {η : TEnv} {L : AllocLabel} (hs : η.sto L = some ⟨.unit, none⟩)
    (hp : η.pfr L = some 0) :
    (VRF bkG) ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] ∧ VRRB ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] .zero :=
  ⟨⟨L, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr (.inl fun _ _ => Nat.zero_le _)⟩,
    ⟨L, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr (.inl fun _ _ => Nat.zero_le _)⟩, rfl⟩
end
end TermTyped.Flat

-- PORTB TermTyped.lean:299 ThInvRE_cur
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ThInvRE_curB {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} {x : String} {a : At} {e : Expr}
    {l : AllocLabel} (hterm : th.term = .let_ x (.ext .current a) e) (hs : E.sto l = some ⟨.unit, none⟩)
    (hp : E.pfr l = some 0) (hR : ThInvREB glb gnum gi p E th Tot) :
    ThInvREB glb gnum gi p E { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw, hDy⟩ := hR
  subst hCE
  have hT2 := hT.2
  rw [hterm] at hT2
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
    obtain ⟨rt, ws0, R, Rr, -, -, -, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    have hf := bindRZB hb (FInvR_monoB hi1 (le_of_add_le hle)) (RLink_ofB hE.2.1 hE.2.2) (vr_tidTB (bkG := False) (ρ := ρ) hs hp).2
      (lay_tidTB _ _)
    refine ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hf, hsum, ?_, hDy.letW hterm rfl⟩
    intro fr rest hst ws1
    rw [hret]; exact hpw fr rest hst ws1
end
end TermTyped.Flat

-- PORTB TermTyped.lean:407 ScopeOK
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ScopeOKB (lb n i : Nat) (p : Prog) (th : TTh) : Prop :=
  ∀ ρ η cx, EnvOKB p η → Typed p cx th.term → TvOK cx → FInvB lb n i ρ η th.σs (ResumeB lb n i p th.stack) cx th.env →
    ScopeD th.σs cx th.term
end
end TermTyped.Flat

-- PORTB TermTyped.lean:489 tidBox_ext
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tidBox_extB {E0 E : TEnv} {l : AllocLabel} (hx : ExtB E0 E)
    (h : E0.sto l = some ⟨.unit, none⟩ ∧ E0.pfr l = some 0) : E.sto l = some ⟨.unit, none⟩ ∧ E.pfr l = some 0 :=
  ⟨hx.2.2.2.2.1 l _ h.1, hx.2.2.2.2.2.2.1 l 0 h.2⟩
end
end TermTyped.Flat

-- PORTB TermTyped.lean:512 ScopeAt
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ScopeAtB (p : Prog) (i : Nat) (c : Cfg) : Prop := ∀ th, c.ths[i]? = some th → ¬ SpawnT th.term → ScopeOKB c.lbase c.n i p th
end
end TermTyped.Flat

-- PORTB TermTyped.lean:598 WrIniC
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
class WrIniCB : Prop where
  wr : ∀ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh}, EnvOKB p η → Typed p cx th.term → TvOK cx →
    FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env → MemInvB g (CE η) (stOf mem pairs th) →
    ScopeD th.σs cx th.term → r ∈ tstep g mem pairs th → WrSite g (CE η) mem pairs th r
  
  wrA : ∀ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh}, EnvOKB p η → Typed p cx th.term → TvOK cx →
    FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env → MemInvB g (CE η) (stOf mem pairs th) →
    ScopeD th.σs cx th.term → (∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts) →
    r ∈ tstep g mem pairs th → WrSiteA g (CE η) mem pairs th r
end
end TermTyped.Flat

-- PORTB TermTyped.lean:661 iniLe_of_hid
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem iniLe_of_hidB {E : TEnv} {mem : Memory} {vs : VState} {P : List Ts} (h : OwnHidPB E mem vs P)
    {l : AllocLabel} {c : Cell} (hc : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l = none) :
    E.ini l ≤ E.rini l := by
  apply Nat.le_of_not_lt
  intro hlt
  have hrc : E.rc l < E.ini l := by unfold TEnv.rc; omega
  obtain ⟨f, hf, -⟩ := h.2 l c hc hown hrc
  rw [hpf] at hf; cases hf
end
end TermTyped.Flat

-- PORTB TermTyped.lean:723 memPos_of_own
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem memPos_of_ownB {g : G} {E : TEnv} {s : St} (hm : MemInvB g E s) {l : AllocLabel} {c : Cell} {N : Nat}
    {e : Ty} {us : List Acc} (hc : E.sto l = some c) (hown : c.owner = some E.tid)
    (hty : c.ty = .array (.lit N) e) (hus : accs e = some us) (hw : 0 < nWords us) (hN : 0 < N) :
    0 < s.mem.size := by
  obtain ⟨vals, hC, hL, -⟩ := hm.2.1 l c hc hown
  have hlen : 0 < vals.length := by
    rcases hC with ⟨hwc, -⟩ | ⟨N', e', us', hT, hus', -, hl, -⟩
    · rw [hty] at hwc; cases hwc
    · rw [hty] at hT; cases hT; rw [hus] at hus'; cases hus'; rw [hl]; exact Nat.mul_pos hN hw
  obtain ⟨⟨m, hm', -⟩, -⟩ := hL 0 vals[0] (List.getElem?_eq_getElem hlen)
  refine Classical.byContradiction fun hn => ?_
  rw [Array.getElem?_eq_none (Nat.le_trans (Nat.le_of_not_lt hn) (Nat.zero_le _))] at hm'; cases hm'
end
end TermTyped.Flat

-- PORTB TermTyped.lean:4514 DbRes_own_zero
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem DbRes_own_zeroB {E : TEnv} {mem : Memory} {m : Msg} {tw : Ts} {R : Res}
    (h : DbResB E mem m tw R) (l : Nat) : R (.own l) = 0 := by
  rcases h with ⟨hV, hI, h3, h4⟩ | ⟨-, rfl⟩
  · by_cases hi : InitAt mem m.loc tw
    · obtain ⟨R₁, Z, hF, hS, hZ, rfl⟩ := h3 hi
      have hZo : Z (.own l) = 0 := by
        by_cases hd : DesigAt E mem m.loc tw
        · obtain ⟨Zb, Zz, -, -, rfl⟩ := hS hd
          exact noOwnR_own _ l
        · rw [hZ hd]; rfl
      have hR1 : R₁ (.own l) = 0 := by
        rcases hF with ⟨n, P, -, rfl⟩ | ⟨-, rfl⟩
        · simp only [Res.add_apply, wr, wdW]
          split <;> split <;> simp
        · rfl
      simp only [Res.add_apply, hZo, hR1]
    · exact VRes_own_zero (Or.inl ⟨hV, hI, h4 hi⟩) l
  · rfl
end
end TermTyped.Flat

-- PORTB TermTyped.lean:4718 use_own_ne
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem use_own_neB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {cx c₁ : Cx} {env : Env} {a : At} {t : Ty} {Rf : Res}
    {x : AllocLabel} (hu : cx.use a = .ok (t, c₁)) (hi : FInvRB glb gnum gi ρ η σs K cx env Rf) (hE : EnvOKB p η)
    (ht : (∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k))
    (h0 : Rf (.own x) = 0) {rt : Ty} {ws : List Word} {ad : Address} {g : Nat}
    (hea : evalAt env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g]) : ad.label ≠ x := by
  obtain ⟨rt', ws', R, Rr, hea', -, -, hvR, -, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  rw [hea] at hea'
  cases hea'
  have hR : R = ownW .own ws := by
    rcases ht with ⟨u, hc⟩ | ⟨n, u, k, hc⟩
    · exact VRR_cell_RB hc hvR
    · exact VRR_buf_RB hc hvR
  rw [hR, ownW_own_loc hws] at hle
  rintro rfl
  have h1 := Res.le_def.1 hle (.own ad.label)
  simp only [Res.add_apply, Res.one, ite_true] at h1
  omega
end
end TermTyped.Flat

-- PORTB TermBlkZ.lean:265 VRR_own_zero
namespace TermBlkZ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address Ts AllocLabel)
theorem VRR_own_zeroB (l : Nat) : ∀ (t : Ty) (ke : KEnv) (η : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word)
    (X : Res), Ty.noOwnIn ke t = true →
    (∀ k S vs Y, η.rrs k S vs Y → Y (.own l) = 0) → (∀ k S vs Y, η.urrs k S vs Y → Y (.own l) = 0) →
    VRRB ρ η t rt ws X → X (.own l) = 0
  | .tvar k, _, η, ρ, rt, ws, X, _, hr, _, hv => by
      simp only [VRRB] at hv
      obtain ⟨w0, -, h1 | ⟨-, rfl, -⟩⟩ := hv
      · exact hr k rt _ X h1
      · rfl
  | .refine t ψ, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRRB] at hv
      exact VRR_own_zeroB l t ke η ρ rt ws X hn hr hur hv.1
  | .iex b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRRB] at hv
      obtain ⟨n, rb, w, -, h2⟩ := hv
      exact VRR_own_zeroB l b ke η (vcons w ρ) rb ws X hn hr hur h2
  | .prod a b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn, Bool.and_eq_true] at hn
      simp only [VRRB] at hv
      obtain ⟨ra, rb, -, Ra, Rb, hR, hz, hf⟩ := hv
      cases hw : ra.wc with
      | none => rw [hz hw]; rfl
      | some n =>
        obtain ⟨-, e2, e3⟩ := hf n hw
        rw [hR, Res.add_apply, VRR_own_zeroB l a ke η ρ _ _ _ hn.1 hr hur e2,
          VRR_own_zeroB l b ke η ρ _ _ _ hn.2 hr hur e3]
  | .sum a b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn, Bool.and_eq_true] at hn
      simp only [VRRB] at hv
      obtain ⟨n, Ra, Rb, -, ⟨-, x, s, B, -, -, -, -, -, -, hA, hA'⟩ | ⟨j, p, -, h2, h3⟩⟩ := hv
      · by_cases hj : B.tag - s < (armsOf Ra).length
        · cases hb : isBoxed Ra with
          | true => exact VRR_own_zeroB l a ke η ρ _ _ _ hn.1 hr hur ((hA hj).1 hb)
          | false =>
            obtain ⟨q, -, -, -, -, hv⟩ := (hA hj).2 hb
            exact VRR_own_zeroB l a ke η.unsee ρ _ _ _ hn.1 hur hur hv
        · have hj' : (armsOf Ra).length ≤ B.tag - s := Nat.le_of_not_lt hj
          cases hb : isBoxed Rb with
          | true => exact VRR_own_zeroB l b ke η ρ _ _ _ hn.2 hr hur ((hA' hj').1 hb)
          | false =>
            obtain ⟨q, -, -, -, -, hv⟩ := (hA' hj').2 hb
            exact VRR_own_zeroB l b ke η.unsee ρ _ _ _ hn.2 hur hur hv
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, -, hv⟩ := h2 hj
          exact VRR_own_zeroB l a ke η ρ _ _ _ hn.1 hr hur hv
        · obtain ⟨q, -, hv⟩ := h3 (Nat.le_of_not_lt hj)
          exact VRR_own_zeroB l b ke η ρ _ _ _ hn.2 hr hur hv
  | .code a b _, _, η, ρ, rt, ws, X, _, _, _, hv => by
      simp only [VRRB] at hv; rw [hv.2]; rfl
  | .tex κ b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn, Bool.and_eq_true] at hn
      simp only [VRRB] at hv
      obtain ⟨n, rb, s, -, -, -, h3⟩ := hv
      exact VRR_own_zeroB l b (some κ :: ke) (η.push0 s) ρ rb ws X hn.2 (push0_rrs_own hr) (push0_urrs_own hur) h3
  | .ptr μ u, ke, η, ρ, rt, ws, X, hn, _, _, hv => by
      have hμ := noOwnIn_ptr_mode hn
      simp only [VRRB] at hv
      rw [hv.2]
      cases μ with
      | own => exact absurd rfl hμ
      | _ => rfl
  | .ptrOpt μ u, ke, η, ρ, rt, ws, X, hn, _, _, hv => by
      have hμ := noOwnIn_ptrOpt_mode hn
      simp only [VRRB] at hv
      rw [hv.2]
      cases μ with
      | own => exact absurd rfl hμ
      | _ => rfl
  | .loc μ u, ke, η, ρ, rt, ws, X, hn, _, _, hv => by
      have hμ := noOwnIn_loc_mode hn
      simp only [VRRB] at hv
      rw [hv.2]
      cases μ with
      | own => exact absurd rfl hμ
      | _ => rfl
  | .mu b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRRB] at hv
      exact VRR_own_zeroB l b (none :: ke) _ ρ rt ws X hn (push0_rrs_own hr) (push0_urrs_own hur) hv
  | .iall b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRRB] at hv
      exact VRR_own_zeroB l b ke η (vcons 0 ρ) rt ws X hn hr hur (hv 0)
  | .intS _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .opq _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .int, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .tid, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .fix _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .lanes _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .unit, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv]; rfl
  | .void, _, _, _, _, _, _, _, _, _, hv => by simp [VRRB] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv]; rfl
  | .share _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv]; rfl
  | .cap _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv]; rfl
  | .word _ _, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRRB] at hv
      rcases hv.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [wdW] <;> split <;> rfl
  | .tok _ st, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRRB] at hv; rw [hv]; cases st <;> simp
  | .word2 _ _, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRRB] at hv
      rcases hv.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv]; rfl
  | .epair _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv.2]; rfl
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRRB] at hv; rw [hv]; rfl
end
end TermBlkZ.Flat

-- PORTB TermInterf.lean:176 CellOKR_mono
namespace TermInterf.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem CellOKR_monoB {η₁ η₂ : TEnv} (hp : η₁.prog = η₂.prog) (ht : η₁.tid = η₂.tid) (hI : Incl η₁ η₂)
    {n nr : Nat} {T : Ty} {vals : List Word} {R : Res} (h : CellOKRB η₁ n nr T vals R) : CellOKRB η₂ n nr T vals R := by
  rcases h with ⟨h1, h2⟩ | ⟨N, e, us, Rs, hTe, hu, hn, hl, hRs, hR, hj⟩
  · exact Or.inl ⟨h1, ValOfR_monoB hp ht hI.sto hI.ini h2 hI.pfr hI.box hI.rini⟩
  · exact Or.inr ⟨N, e, us, Rs, hTe, hu, hn, hl, hRs, hR,
      fun j Rj h1 h2 => slotR_imp (hj j Rj h1 h2) rfl
        (fun h => ValOfR_monoB hp ht hI.sto hI.ini h hI.pfr hI.box hI.rini)⟩
end
end TermInterf.Flat

-- PORTB TermInterf.lean:186 HeldEntry_priv_move
namespace TermInterf.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem HeldEntry_priv_moveB {E E' : TEnv} {s s' : St} {l : AllocLabel} {R : Res}
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hI : Incl E E') (hpv : Priv E l) (hpv' : Priv E' l)
    (hsto : E'.sto l = E.sto l) (hini : E'.ini l = E.ini l) (hri : E'.rini l = E.rini l) (hpr : s'.promises = s.promises)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → m.loc.label ≠ l)
    (h : HeldEntryB E s l R) : HeldEntryB E' s' l R := by
  refine ⟨fun h0 => h.1 (hsto ▸ h0), fun c hc => ?_⟩
  obtain ⟨vals, hv, hk⟩ := h.2 c (hsto ▸ hc)
  refine ⟨vals, fun o w hw => ?_, by rw [hini, TEnv.rc_congr hini hri]; exact CellOKR_monoB hp ht hI hk⟩
  have h1 := hv o w hw
  rw [PromAt_own (a := ⟨l, o⟩) hpv] at h1
  rw [PromAt_own (a := ⟨l, o⟩) hpv', hpr]
  exact LatestNP_grow hpre (fun t m h1 h2 => hnew t m h1 h2) h1
end
end TermInterf.Flat

-- PORTB TermPubW.lean:195 EFootW
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def EFootWB (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  E'.prog = E.prog ∧ E'.tid = E.tid ∧
  (∀ l, E'.sto l = E.sto l ∨
    (FreshIn g s.nalloc s'.nalloc l ∧ ∃ T, E'.sto l = some ⟨T, some E.tid⟩ ∧ (Clo T ∧ mg T = true ∧ noIallV T = true) ∧ UndefAtT s'.mem l T ∧
      NewAtT s.mem.size s'.mem l T)) ∧
  (∀ l, E'.box l = E.box l ∨
    (FreshIn g s.nalloc s'.nalloc l ∧ ∃ B, E'.box l = some B ∧ B.own = E.tid ∧ s.mem.size ≤ B.fr + 1 ∧
      B.fr ≤ s'.vs.vWr ∧ s.mem.size + B.pay.length ≤ B.fr)) ∧
  (∀ l, E.ini l ≤ E'.ini l ∧ (E'.ini l = E.ini l ∨ FreshIn g s.nalloc s'.nalloc l ∨
    (OwnAt E l ∧ E'.ini l ≤ max (E.ini l) (E'.rini l) ∧
      (E.pfr l ≠ none → E'.ini l = E.ini l ∨ E.ini l ≤ E.rini l)))) ∧
  (∀ l, E'.pfr l = E.pfr l ∨
    (E.pfr l = none ∧ ∃ F, E'.pfr l = some F ∧ s.vs.vWr ≤ F ∧ F ≤ max s.vs.vWr s.mem.size ∧ OwnAt E l ∧
      s'.vs.vWr ≤ F ∧
      (¬ E'.seen l → ∀ cl N e us, E'.sto l = some cl → cl.ty = .array (.lit N) e → accs e = some us →
        nWords us = 0 → (∃ ws, ValOfB ({ prog := E.prog } : TEnv) e ws ∧ ws.length = 0) → N ≤ E'.ini l)) ∨
    (FreshIn g s.nalloc s'.nalloc l ∧ E.pfr l = none ∧ E'.sto l = none)) ∧
  (∀ l, E.seen l → E'.seen l) ∧ (∀ l, E'.seen l → E.seen l ∨ OwnAt E l ∨ FreshIn g s.nalloc s'.nalloc l) ∧
  E'.fp = E.fp ∧ (∀ l, E.rini l ≤ E'.rini l) ∧
  ((∀ l, E.rini l ≤ E.ini l) → ∀ l, E'.rini l ≤ E'.ini l) ∧ RiniW E E' s s'.vs.vWr ∧
  (∀ l, E'.rini l = E.rini l ∨ FreshIn g s.nalloc s'.nalloc l ∨ OwnAt E l)
end
end TermStep.Flat

-- PORTB TermPubW.lean:778 FootW
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def FootWB (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  EFootWB g E E' s s' ∧ ∀ l, FreshIn g s.nalloc s'.nalloc l →
    E.sto l = none ∧ E.box l = none ∧ E.ini l = 0 ∧ E.pfr l = none
end
end TermStep.Flat

-- PORTB TermOwnX2.lean:83 stoNIE_efoot
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stoNIE_efootB {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (hf : EFootBB W g E E' s s') (h : StoNIE E) : StoNIE E' := by
  intro l cl hl
  rcases hf.2.2.1 l with he | ⟨-, T, hT, ⟨-, -, hn, -⟩, -⟩
  · exact h l cl (he ▸ hl)
  · rw [hT] at hl; cases hl; exact hn
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:97 finv_of
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem finv_ofB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {cx : Cx} {Rf Rs : Res} (htv : TvOK cx)
    (hF : FInvRB glb gnum gi ρ η th.σs (ResumeRB glb gnum gi p th.stack Rs) cx th.env Rf) :
    FInvB glb gnum gi ρ η th.σs (ResumeB glb gnum gi p th.stack) cx th.env :=
  FInvR_FInvB htv.2.2.2.2.2.2.2
    (fun E rd ws R h => ResumeR_ResumeB (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:110 anchR_gen
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchR_genB {g : G} {E0 E E' : TEnv} {s s' : St} (h : AnchR E0 E0 E s) (hfr : FreshLP g E s)
    (hm' : MemInvB g E' s') (hwl : WrLocG g E E' s s') (hsub : ∀ l c, E0.sto l = some c → E.sto l = some c)
    (hsto : ∀ l c, E'.sto l = some c → E'.pfr l ≠ none → E.sto l = some c)
    (hpk : ∀ l f, E.pfr l = some f → E'.pfr l = some f) (htid : E'.tid = E.tid)
    (hsn : ∀ l, E.seen l → E'.seen l) (hri : ∀ l, E.rini l ≤ E'.rini l)
    (hini : ∀ l, E.sto l ≠ none → E'.ini l ≤ max (E.ini l) (E'.rini l))
    (hnew : ∀ l, E.sto l = none → E'.sto l ≠ none → (∃ c, E'.sto l = some c ∧ c.owner = some E'.tid) ∧ E'.pfr l = none) : AnchR E0 E0 E' s' := by
  obtain ⟨hA, hL, hR, hP, hK⟩ := h
  refine ⟨?_, ?_, ?_, fun l c N e us f hc' ho hty hus hw hN hf => Nat.lt_of_lt_of_le
      (hP l c N e us f (hsto l c hc' (by rw [hpk l f (hK l f hf)]; exact fun h => by cases h))
        (by rw [← htid]; exact ho) hty hus hw hN hf) hwl.1,
    fun l f hf => hpk l f (hK l f hf)⟩
  · intro l hl
    have h3 := hri l
    by_cases hEs : E.sto l = none
    · 
      obtain ⟨⟨c, hc, ho⟩, hp⟩ := hnew l hEs hl
      have := iniLe_of_hidB hm'.2.2.2.2.2.1 hc ho hp
      omega
    · have h1 := hini l hEs
      have h2 := hA l hEs
      omega
  · intro l h0 ⟨c, hc', hown'⟩
    by_cases hpf' : E'.pfr l = none
    · exact iniLe_of_hidB hm'.2.2.2.2.2.1 hc' hown' hpf'
    · have hc := hsto l c hc' hpf'
      have h1 := hL l h0 ⟨c, hc, by rw [← htid]; exact hown'⟩
      have h2 := hini l (by rw [hc]; exact fun h => by cases h)
      have h3 := hri l
      omega
  · intro l c N e us j hc' hown' hns' hty hus hw hjN hall
    by_cases hpf' : E'.pfr l = none
    · refine riniMem_priv hm'.2.2.2.1.2 hpf' hc' hown' hty hus hw hjN fun o h1 h2 => ?_
      obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
      exact ⟨t, m, ht, hm, hl, hv⟩
    · exact riniMemA_old hL hR hP hK hfr (hwl.2 (noPfr E0)) rfl (hri l) hpf' (hsto l c hc' hpf')
        (by rw [← htid]; exact hown') (fun h => hns' (hsn l h)) hty hus hw hjN hall
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:149 anchR_same
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchR_sameB {g : G} {E0 E : TEnv} {s s' : St} (h : AnchR E0 E0 E s) (hfr : FreshLP g E s)
    (hm' : MemInvB g E s') (hwl : WrLocG g E E s s') : AnchR E0 E0 E s' :=
  by
  obtain ⟨hA, hL, hR, hP, hK⟩ := h
  refine ⟨hA, hL, ?_, fun l c N e us f h1 h2 h3 h4 h5 h6 h7 => Nat.lt_of_lt_of_le (hP l c N e us f h1 h2 h3 h4 h5 h6 h7) hwl.1, hK⟩
  intro l c N e us j hc hown hns hty hus hw hjN hall
  by_cases hpf : E.pfr l = none
  · refine riniMem_priv hm'.2.2.2.1.2 hpf hc hown hty hus hw hjN fun o h1 h2 => ?_
    obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
    exact ⟨t, m, ht, hm, hl, hv⟩
  · exact riniMemA_old hL hR hP hK hfr (hwl.2 (noPfr E0)) rfl (Nat.le_refl _) hpf hc hown hns hty hus hw hjN hall
end
end TermOwnX2.Flat

-- K17 (B7): the rini frame of a step.
namespace TermOwnX2.Flat
open TermSound.Flat TermStep.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
def BufInitL (th : TTh) (l : WeakMem.AllocLabel) : Prop :=
  ∃ x bb ib v e rt ws, ∃ ad : WeakMem.Address, th.term = .let_ x (.bufInit bb ib v) e ∧ evalAt th.env bb = some (rt, ws) ∧
    ws.map (·.val) = [.loc ad 0] ∧ ad.label = l
def RiniFr (th : TTh) (E E' : TEnv) : Prop := ∀ l, E.sto l ≠ none → E'.rini l ≤ E.rini l ∨ BufInitL th l
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:164 AnchStep
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def AnchStepB (g : G) (th : TTh) (E E' : TEnv) (s s' : St) : Prop :=
  (∀ E0, ExtB E0 E → AnchR E0 E0 E s → FreshLP g E s → MemInvB g E' s' → (BumpIf th E' → WrLocG g E E' s s') →
    ExtB E0 E' ∧ AnchR E0 E0 E' s') ∧ RiniFr th E E' ∧
    ((∀ l, E.rini l ≤ E.ini l) → ∀ l, E'.rini l ≤ E'.ini l)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:169 anchStep_gen
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchStep_genB {g : G} {th : TTh} {E E' : TEnv} {s s' : St} (hX : ExtB E E') (hb : BumpIf th E') (hsto : ∀ l c, E'.sto l = some c → E'.pfr l ≠ none → E.sto l = some c)
    (hini : ∀ l, E.sto l ≠ none → E'.ini l ≤ max (E.ini l) (E'.rini l))
    (hnew : ∀ l, E.sto l = none → E'.sto l ≠ none → (∃ c, E'.sto l = some c ∧ c.owner = some E'.tid) ∧ E'.pfr l = none) (hri : RiniFr th E E') (hrl : ((∀ l, E.rini l ≤ E.ini l) → ∀ l, E'.rini l ≤ E'.ini l)) : AnchStepB g th E E' s s' :=
  ⟨fun _ hx0 hA hfr hm' hw => ⟨Ext_transB hx0 hX, anchR_genB hA hfr hm' (hw hb) (fun l c h => hx0.2.2.2.2.1 l c h) hsto
    hX.2.2.2.2.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2.2.2.1 hX.rini hini hnew⟩,
    hri, hrl⟩

end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:176 anchStep_fresh
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchStep_freshB {g : G} {th : TTh} {E E' : TEnv} {s s' : St} {lbl : AllocLabel} (hX : ExtB E E')
    (hb : BumpIf th E') (hsto : ∀ l, l ≠ lbl → E'.sto l = E.sto l) (hpf : E'.pfr lbl = none)
    (hini : ∀ l, l ≠ lbl → E'.ini l = E.ini l) (h0 : E.sto lbl = none)
    (hpv : (∃ c, E'.sto lbl = some c ∧ c.owner = some E'.tid) ∧ E'.pfr lbl = none) (hri : ∀ l, l ≠ lbl → E'.rini l = E.rini l)
    (hrl0 : (∀ l, E.rini l ≤ E.ini l) → E'.rini lbl ≤ E'.ini lbl) : AnchStepB g th E E' s s' :=
  anchStep_genB hX hb
    (fun l c h hp => by
      by_cases hl : l = lbl
      · subst hl; exact absurd hpf hp
      · rw [← hsto l hl]; exact h)
    (fun l hl => by
      have hne : l ≠ lbl := fun e => hl (by rw [e]; exact h0)
      rw [hini l hne]; exact Nat.le_max_left _ _)
    (fun l hs hl => by
      by_cases e : l = lbl
      · subst e; exact hpv
      · exact absurd ((hsto l e).trans hs) hl)
    (fun l hl => Or.inl (Nat.le_of_eq (hri l (fun e => hl (by rw [e]; exact h0)))))
    (fun h l => by
      by_cases hl : l = lbl
      · subst hl; exact hrl0 h
      · rw [hri l hl, hini l hl]; exact h l)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:194 anchStep_same
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchStep_sameB {g : G} {th : TTh} {E : TEnv} {s s' : St} (hnb : ∀ E1, BumpIf th E1) :
    AnchStepB g th E E s s' :=
  ⟨fun _ hx0 hA hfr hm' hw => ⟨hx0, anchR_sameB hA hfr hm' (hw (hnb E))⟩,
    fun _ _ => Or.inl (Nat.le_refl _), fun h => h⟩

end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:199 anchStep_keep
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchStep_keepB {g : G} {th : TTh} {E : TEnv} {s s' : St}
    (hmem : ∀ (t : Nat) (m : Msg), t ∉ s'.promises → s'.mem[t]? = some m → t ∉ s.promises ∧ s.mem[t]? = some m)
    (hsz : s.mem.size ≤ s'.mem.size) : AnchStepB g th E E s s' :=
  ⟨fun _ hx0 hA _ _ _ => ⟨hx0, anchR_keep hA hmem hsz⟩,
    fun _ _ => Or.inl (Nat.le_refl _), fun h => h⟩

end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:210 anchStep_eqs
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchStep_eqsB {g : G} {th : TTh} {E : TEnv} {s s' : St} (e1 : s'.mem = s.mem)
    (e2 : s'.promises = s.promises) : AnchStepB g th E E s s' :=
  ⟨fun _ hx0 hA _ _ _ => ⟨hx0, anchR_eqs hA e1 e2⟩,
    fun _ _ => Or.inl (Nat.le_refl _), fun h => h⟩

end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:215 anchStep_shrink
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem anchStep_shrinkB {g : G} {th : TTh} {E E1 : TEnv} {s s' : St} (hX : ExtB E E1) (hsto : E1.sto = E.sto)
    (hini : E1.ini = E.ini) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (hri : E1.rini = E.rini) : AnchStepB g th E E1 s s' :=
  ⟨fun _ hx0 hA hfr hm' _ => ⟨Ext_transB hx0 hX, anchR_genB hA hfr hm'
    ⟨by rw [e1]; exact Nat.le_refl _, fun _ _ _ ht hm => .inl ⟨by rw [← e2]; exact ht, by rw [← e1]; exact hm⟩⟩
    (fun l c h => hx0.2.2.2.2.1 l c h) (fun _ _ h _ => by rw [← hsto]; exact h)
    hX.2.2.2.2.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2.2.2.1 hX.rini (fun _ _ => by rw [hini]; exact Nat.le_max_left _ _)
    (fun l h0 hl => absurd (by rw [hsto]; exact h0) hl)⟩,
    fun _ _ => Or.inl (by rw [hri]; exact Nat.le_refl _),
    fun h l => by rw [hri, hini]; exact h l⟩

end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:261 ext_CE
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ext_CEB {η η' : TEnv} (hx : ExtB η η') : ExtB (CE η) (CE η') :=
  ⟨Coh_CEB η', rfl, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.2.2.1, Nat.le_refl _, CohR_CEB η', hx.rini⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:266 ext_RE
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ext_REB {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} (h : ThInvREB glb gnum gi p E th Tot) : ExtB E E := by
  obtain ⟨ρ, η, cx, Rf, Rs, rfl, -⟩ := h
  exact Ext_reflB (Coh_CEB η) (CohR_CEB η)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:271 wrHyp
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrHypB [WrIniCB] {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {r : Memory × List Ts × TTh} {E' : TEnv} (hE : EnvOKB p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts)
    (hr : r ∈ tstep g mem pairs th) :
    BumpIf th E' → WrLocG g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) :=
  fun hb => ⟨(TermLiveProps.tstep_ext g mem pairs th r hr).mem.size, wrLocA2_of (WrIniCB.wrA hE hT htv hi hm hsc hvr hr) hb⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:281 publish_own_cell
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem publish_own_cellB {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {x : String} {a : At}
    {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hT : Typed p cx th.term) (hi : FInvB glb gnum gi ρ η th.σs (ResumeB glb gnum gi p th.stack) cx th.env)
    (hterm : th.term = .let_ x (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ∃ c, η.sto ad.label = some c ∧ c.owner = some η.tid := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, -, -⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok _ := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨-, rt', ws', hea', hv, -⟩ := use_FInvB (bkG := False) hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VRF, VRb2] at hv
    obtain ⟨ad', c, hws', -, hsto, -, hmode, -⟩ := hv
    rw [hws] at hws'
    simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
    subst hws'
    exact ⟨c, hsto, hmode⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, -, -⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok _ := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨-, rb, wsb, hea', hvb, -⟩ := use_FInvB (bkG := False) hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad', c, U, hws', hsto, -, -, hmode, -⟩
    · rw [hws] at hnull; simp at hnull
    · rw [hws] at hws'
      simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
      subst hws'
      exact ⟨c, hsto, hmode⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:319 OwnXLe
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXLeB (p : Prog) (k : Promises.Knobs) (arch : Arch) (E0 : TEnv) (i : Nat) (x : AllocLabel) (n : Nat)
    (c : Cfg) :
    Prop :=
  ∃ th E Tot HP, c.ths[i]? = some th ∧ ThInvREB c.lbase c.n i p E th Tot ∧
    MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ MemHeldPB E (stOf c.mem c.pairs th) HP ∧
    (gOf p k arch c i).boxFence = true ∧ StoNIE E ∧ E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ n ∧
    ExtB E0 E ∧ AnchR E0 E0 E (stOf c.mem c.pairs th) ∧
    TyOKE (gOf p k arch c i) E ∧ RecFresh (gOf p k arch c i) i th.nalloc ∧ (n = 0 → E.rini x ≤ E0.rini x) ∧
    ((∀ l, E0.rini l ≤ E0.ini l) → ∀ l, E.rini l ≤ E.ini l)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:327 OwnXLe.mono
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem OwnXLeB.mono {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n m : Nat}
    {c : Cfg} (h : OwnXLeB p k arch E0 i x n c) (hnm : n ≤ m) : OwnXLeB p k arch E0 i x m c :=
  let ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hs, hle, hx, hA, hTy, hRc, hZ, hR⟩ := h
  ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hs, Nat.le_trans hle hnm, hx, hA, hTy, hRc, fun h0 => hZ (by omega), hR⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:333 ownXLe_ext
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXLe_extB {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat}
    {c c' : Cfg} (h : OwnXLeB p k arch E0 i x n c) (hs : c' ∈ extSteps c i) (hTA : TermTyped.TidAt i c E0) :
    OwnXLeB p k arch E0 i x n c' := by
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hsx, hle, hx, hA, hTy, hRc, hZ, hR⟩ := h
  rcases TermTyped.extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ | ⟨x1, a1, e1, lb, hterm, htl, rfl⟩
  · exact ⟨_, E, Tot, HP, set_self hth, (by rw [extSteps_n hs]; exact TermTyped.Flat.ThInvRE_extB hn1 hterm hev1 hrs1 hT), by rw [gOf_ext hs]; exact hm, hP,
      by rw [gOf_ext hs]; exact hb, hn, hsx, hle, hx, hA, by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc, hZ, hR⟩
  · obtain ⟨hbs, hbp⟩ := TermTyped.Flat.tidBox_extB hx (hTA th hth lb htl)
    exact ⟨_, E, Tot, HP, set_self (tr := c.trace) hth, (by rw [extSteps_n hs]; exact TermTyped.Flat.ThInvRE_curB hterm hbs hbp hT),
      by rw [gOf_ext hs]; exact hm, hP, by rw [gOf_ext hs]; exact hb, hn, hsx, hle, hx, hA,
      by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc, hZ, hR⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:345 OwnXLe.rf_zero
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem OwnXLeB.rf_zero {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c : Cfg}
    (h : OwnXLeB p k arch E0 i x 0 c) :
    ∃ th, c.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOKB p η ∧ Typed p cx th.term ∧
      FInvRB c.lbase c.n i ρ η th.σs (ResumeRB c.lbase c.n i p th.stack Rs) cx th.env Rf ∧ Rf (.own x) = 0 := by
  obtain ⟨th, E, Tot, HP, hth, ⟨ρ, η, cx, Rf, Rs, -, hE, hTy, -, hFI, hsum, -⟩, -, -, -, -, -, hle, -, -, -⟩ := h
  have h3 := congrArg (fun R : Res => R (.own x)) hsum
  simp only [Res.add_apply] at h3
  exact ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy.1, hFI, by omega⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:355 OwnXLe.use_ne
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem OwnXLeB.use_ne {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c : Cfg}
    (h : OwnXLeB p k arch E0 i x 0 c) :
    ∃ th, c.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOKB p η ∧ Typed p cx th.term ∧
      FInvRB c.lbase c.n i ρ η th.σs (ResumeRB c.lbase c.n i p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x := by
  obtain ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy, hFI, h0⟩ := h.rf_zero
  exact ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy, hFI, fun a t c₁ rt ws ad g hu ht hea hws =>
    use_own_neB hu hFI hE ht h0 hea hws⟩
end
end TermOwnX2.Flat

-- K17: at own-count 0, rini is bounded by the anchor env and ini by max (E0.ini) (E0.rini).
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem OwnXLeB.fz_bounds {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c : Cfg}
    (h : OwnXLeB p k arch E0 i x 0 c) :
    ∃ th E, c.ths[i]? = some th ∧ MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ ExtB E0 E ∧ E.sto x ≠ none ∧
      E.rini x ≤ E0.rini x ∧ E.ini x ≤ max (E0.ini x) (E0.rini x) := by
  obtain ⟨th, E, Tot, HP, hth, -, hm, -, -, -, hs, -, hx, hA, -, -, hZ, -⟩ := h
  have h1 := hA.1 x hs
  have h2 := hZ rfl
  exact ⟨th, E, hth, hm, hx, hs, h2, by omega⟩
end
end TermOwnX2.Flat

-- K17: a thread with no own-count at x is not about to bufInit a slot of x.
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem bumpIni_rle {ini rini : AllocLabel → Nat} {l0 : AllocLabel} {m : Nat} (h : ∀ l, rini l ≤ ini l) (l : AllocLabel) :
    bumpIni rini l0 m l ≤ bumpIni ini l0 m l := by
  unfold bumpIni
  split
  · exact Nat.max_le.2 ⟨Nat.le_trans (h l) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
  · exact h l
theorem not_bufInitL_ofB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {th : TTh} {x : AllocLabel}
    (hE : EnvOKB p η) (hTy : Typed p cx th.term) (hFI : FInvRB glb gnum gi ρ η th.σs (ResumeRB glb gnum gi p th.stack Rs) cx th.env Rf)
    (h0 : Rf (.own x) = 0) : ¬ BufInitL th x := by
  rintro ⟨x1, bb, ib, v, e, rt, ws, ad, hterm, hev, hws, hl⟩
  rw [hterm] at hTy
  cases hTy with
  | let_ hop he =>
    cases hop with
    | bufInit hu hbuf _ _ _ _ _ _ => exact use_own_neB hu hFI hE (Or.inr ⟨_, _, _, hbuf⟩) h0 hev hws hl
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:424 valOfR_own_zero
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem valOfR_own_zeroB {E : TEnv} {T : Ty} {ws : List Word} {R : Res} (hT : Ty.noOwnIn [] T = true)
    (h : ValOfRB E T ws R) (l : Nat) : R (.own l) = 0 :=
  TermBlkZ.Flat.VRR_own_zeroB l T [] (CE E.unsee) (fun _ => 0) (shp T) ws R hT (fun _ _ _ _ h => False.elim h)
    (fun _ _ _ _ h => False.elim h) h.1
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:430 cellOKR_own_zero
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem cellOKR_own_zeroB {E : TEnv} {n nr : Nat} {T : Ty} {vals : List Word} {R : Res}
    (hT : Ty.noOwnIn [] T = true) (h : CellOKRB E n nr T vals R) (l : Nat) : R (.own l) = 0 := by
  rcases h with ⟨-, h⟩ | ⟨N, e, us, Rs, hTe, -, -, -, hlen, rfl, hj⟩
  · exact valOfR_own_zeroB hT h l
  · subst hTe
    have he := noOwn_array hT
    refine Classical.byContradiction fun h0 => ?_
    obtain ⟨Rj, hm, h1⟩ := TermOwnKey.sum_ne h0
    obtain ⟨j, hjl, hjv⟩ := List.getElem_of_mem hm
    have hj' := hj j Rj (by omega) (by rw [List.getElem?_eq_getElem hjl, hjv])
    by_cases hz : nr ≤ j ∧ nWords us = 0
    · rw [hj'.1 hz.1 hz.2] at h1; exact h1 rfl
    · have hor : j < nr ∨ 0 < nWords us := by
        rcases Nat.lt_or_ge j nr with h | h
        · exact .inl h
        · right; rcases Nat.eq_zero_or_pos (nWords us) with h' | h'
          · exact absurd ⟨h, h'⟩ hz
          · exact h'
      exact h1 (valOfR_own_zeroB he (hj'.2 hor) l)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:451 heldEntry_pfr_own_zero
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem heldEntry_pfr_own_zeroB {g : G} {E : TEnv} {s : St} {l : AllocLabel} {f : Ts} {R : Res}
    (hm : MemInvB g E s) (hf : E.pfr l = some f) (h : HeldEntryB E s l R) (x : Nat) : R (.own x) = 0 := by
  obtain ⟨hn, hs⟩ := h
  cases hc : E.sto l with
  | none => rw [hn hc]; rfl
  | some cl =>
    obtain ⟨vals, -, hok⟩ := hs cl hc
    exact cellOKR_own_zeroB (MemInv_noOwnTB hm hc hf) hok x
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:461 memHeldOn_pfr_own_zero
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_pfr_own_zeroB {g : G} {Q : AllocLabel → Prop} {E : TEnv} {s : St} {H : Res}
    (hm : MemInvB g E s) (hQ : ∀ l, Q l → ∃ f, E.pfr l = some f) (h : MemHeldOnB Q E s H) (x : Nat) :
    H (.own x) = 0 := by
  obtain ⟨L, Rl, -, -, hq, rfl, hR⟩ := h
  refine Classical.byContradiction fun h0 => ?_
  obtain ⟨R, hmR, h1⟩ := TermOwnKey.sum_ne h0
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hmR
  obtain ⟨f, hf⟩ := hQ l (hq l hl)
  exact h1 (heldEntry_pfr_own_zeroB hm hf (hR l hl) x)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:472 memHeldS_own_zero
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldS_own_zeroB {g : G} {E : TEnv} {s : St} {H : Res} (hm : MemInvB g E s) (h : MemHeldSB E s H)
    (x : Nat) : H (.own x) = 0 :=
  memHeldOn_pfr_own_zeroB hm (fun _ h => h) h x
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:478 memHeld_own_priv
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeld_own_privB {g : G} {E : TEnv} {s : St} {H : Res} (hm : MemInvB g E s) (h : MemHeldB E s H)
    (x : Nat) : ∃ HP, MemHeldOnB (fun l => E.pfr l = none) E s HP ∧ H (.own x) = HP (.own x) := by
  obtain ⟨H1, H2, rfl, h1, h2⟩ := MemHeld_splitOnB (fun l => E.pfr l = none) h
  have z := memHeldOn_pfr_own_zeroB hm (fun l hl => Option.ne_none_iff_exists'.1 hl) h2 x
  refine ⟨H1, h1, ?_⟩
  simp only [Res.add_apply, z, Nat.add_zero]
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:502 memHeld_priv_le
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeld_priv_leB {E : TEnv} {s : St} {H : Res} (h : MemHeldB E s H) :
    ∃ HP, MemHeldPB E s HP ∧ ∀ key, HP key ≤ H key := by
  obtain ⟨H1, H2, rfl, h1, -⟩ := MemHeld_splitOnB (Priv E) h
  exact ⟨H1, h1, fun key => by simp only [Res.add_apply]; omega⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:512 thInvRE_ext
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem thInvRE_extB {p : Prog} {E E' : TEnv} {th : TTh} {Tot : Res} (h : ThInvREB glb gnum gi p E th Tot) (hx : ExtB E E')
    (hE' : CE E' = E') : ThInvREB glb gnum gi p E' th Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, rfl, hE, hTy, htv, hFI, hsum⟩ := h
  have hext : ExtB η (η.withStoB E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini) :=
    Ext_withStoB hE.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1
      (Nat.le_refl _) E'.fp E'.rini hx.rini
  refine ⟨ρ, η.withStoB E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini, cx, Rf, Rs, ?_,
    ⟨hE.1, Coh_withStoB hE.2.1 _ _ _ _ _ _ _ _, CohR_withStoB hE.2.1 _ _ _ _ _ _ _ _⟩, hTy, htv,
    FInvR_extB hE.2.1 hE.2.2 hext hFI, hsum⟩
  have e1 : E'.prog = η.prog := hx.2.2.1
  have e2 : E'.tid = η.tid := hx.2.2.2.1
  rw [← hE']
  simp only [CE, TEnv.withStoB, e1, e2]
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:544 OwnXStepT
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepTB (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 c0', ScopeAtB p i c0 → TermViewInv.ViewInv c0 → OwnXLeB p k arch E0 i x n c0 →
    c0' ∈ threadSteps p k arch c0 i → Certified p k arch c0' i → OwnXLeB p k arch E0 i x n c0'
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:549 OwnXStepP
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepPB (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 a v w, OwnXLeB p k arch E0 i x n c0 → w < c0.mem.size → Certified p k arch (promise c0 i a v w) i →
    OwnXLeB p k arch E0 i x n (promise c0 i a v w)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:591 OwnXStepPkg
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepPkgB (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n q : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 c0' th, c0.ths[i]? = some th → exprPkg th.term = q →
    ScopeAtB p i c0 → TermViewInv.ViewInv c0 → OwnXLeB p k arch E0 i x n c0 →
    c0' ∈ threadSteps p k arch c0 i → Certified p k arch c0' i → OwnXLeB p k arch E0 i x n c0'
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:604 ownXStepT_of_pkgs
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepT_of_pkgsB {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepPkgB p k arch i x n 1) (h2 : OwnXStepPkgB p k arch i x n 2)
    (h3 : OwnXStepPkgB p k arch i x n 3) (h4 : OwnXStepPkgB p k arch i x n 4) : OwnXStepTB p k arch i x n := by
  intro E0 c0 c0' hsc hvI hI hs hc
  obtain ⟨th, hth⟩ := mem_threadSteps_th hs
  rcases exprPkg_cases th.term with e | e | e | e
  · exact h1 E0 c0 c0' th hth e hsc hvI hI hs hc
  · exact h2 E0 c0 c0' th hth e hsc hvI hI hs hc
  · exact h3 E0 c0 c0' th hth e hsc hvI hI hs hc
  · exact h4 E0 c0 c0' th hth e hsc hvI hI hs hc
end
end TermOwnX2.Flat

-- PORTB TermOwnHeldQ.lean:21 heldEntry_eqs
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem heldEntry_eqsB {E : TEnv} {s s' : St} {l : AllocLabel} {R : Res} (h : HeldEntryB E s l R)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) : HeldEntryB E s' l R := by
  refine ⟨h.1, fun c hc => ?_⟩
  obtain ⟨vals, hL, hC⟩ := h.2 c hc
  refine ⟨vals, fun o w hw => ?_, hC⟩
  rw [PromAt_eqp e2 e1, e1]
  exact hL o w hw
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:30 memHeldOn_eqs
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_eqsB {Q : AllocLabel → Prop} {E : TEnv} {s s' : St} {H : Res} (h : MemHeldOnB Q E s H)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) : MemHeldOnB Q E s' H := by
  obtain ⟨L, Rl, hn, hc, hq, hH, he⟩ := h
  exact ⟨L, Rl, hn, hc, hq, hH, fun l hl => heldEntry_eqsB (he l hl) e1 e2⟩
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:36 memHeldOn_split
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_splitB {Q : AllocLabel → Prop} (Q' : AllocLabel → Prop) {E : TEnv} {s : St} {H : Res}
    (h : MemHeldOnB Q E s H) :
    ∃ H₁ H₂, H = H₁ + H₂ ∧ MemHeldOnB (fun l => Q l ∧ Q' l) E s H₁ ∧ MemHeldOnB (fun l => Q l ∧ ¬ Q' l) E s H₂ := by
  classical
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := h
  refine ⟨Res.sum ((L.filter (fun l => decide (Q' l))).map Rl),
    Res.sum ((L.filter (fun l => !decide (Q' l))).map Rl), ?_,
    ⟨_, Rl, hn.filter _, fun l c hq' hs => List.mem_filter.2 ⟨hc l c hq'.1 hs, by simpa using hq'.2⟩,
      fun l hl => ⟨hq l (List.mem_filter.1 hl).1, by simpa using (List.mem_filter.1 hl).2⟩, rfl,
      fun l hl => he l (List.mem_filter.1 hl).1⟩,
    ⟨_, Rl, hn.filter _, fun l c hq' hs => List.mem_filter.2 ⟨hc l c hq'.1 hs, by simpa using hq'.2⟩,
      fun l hl => ⟨hq l (List.mem_filter.1 hl).1, by simpa using (List.mem_filter.1 hl).2⟩, rfl,
      fun l hl => he l (List.mem_filter.1 hl).1⟩⟩
  rw [← Res.sum_append, ← List.map_append]
  exact Res.sum_perm (List.filter_append_perm _ L).symm
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:54 memHeldOn_move
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_moveB {Q Q' : AllocLabel → Prop} {E E' : TEnv} {s s' : St} {H : Res} (h : MemHeldOnB Q E s H)
    (hcov : ∀ l c, Q' l → E'.sto l = some c → Q l ∧ ∃ c', E.sto l = some c')
    (hent : ∀ l R, Q l → Q' l → HeldEntryB E s l R → HeldEntryB E' s' l R) :
    ∃ H', MemHeldOnB Q' E' s' H' ∧ ∀ key, H' key ≤ H key := by
  obtain ⟨H₁, H₂, rfl, ⟨L, Rl, hn, hc, hq, rfl, he⟩, -⟩ := memHeldOn_splitB Q' h
  refine ⟨_, ⟨L, Rl, hn, fun l c hq' hs => ?_, fun l hl => (hq l hl).2, rfl,
    fun l hl => hent l _ (hq l hl).1 (hq l hl).2 (he l hl)⟩, fun key => by simp only [Res.add_apply]; omega⟩
  obtain ⟨hql, c', hc'⟩ := hcov l c hq' hs
  exact hc l c' ⟨hql, hq'⟩ hc'
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:65 memHeldOn_focus
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_focusB {Q : AllocLabel → Prop} {E : TEnv} {s : St} {H : Res} (h : MemHeldOnB Q E s H)
    {l : AllocLabel} (hql : Q l) :
    ∃ R0 H0, H = R0 + H0 ∧ HeldEntryB E s l R0 ∧ MemHeldOnB (fun l' => Q l' ∧ l' ≠ l) E s H0 := by
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := h
  by_cases hl : l ∈ L
  · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hl
    have hnd' : (L1 ++ L2).Nodup := List.Nodup.sublist (by simp) hnd
    have hnl : l ∉ L1 ++ L2 := by
      intro hm
      rw [List.nodup_append] at hnd
      rcases List.mem_append.1 hm with h1 | h2
      · exact hnd.2.2 l h1 l (by simp) rfl
      · exact (List.nodup_cons.1 hnd.2.1).1 h2
    have hsub : ∀ l', l' ∈ L1 ++ L2 → l' ∈ L1 ++ l :: L2 := fun l' hl' => by
      simp only [List.mem_append, List.mem_cons] at hl' ⊢
      rcases hl' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    refine ⟨Rl l, Res.sum ((L1 ++ L2).map Rl), Res.sum_map_cons_mid Rl l L1 L2, hent l hl,
      L1 ++ L2, Rl, hnd', fun l' c hq' hc => ?_, fun l' hl' => ⟨hq l' (hsub l' hl'), fun e => hnl (e ▸ hl')⟩,
      rfl, fun l' hl' => hent l' (hsub l' hl')⟩
    have := hcov l' c hq'.1 hc
    simp only [List.mem_append, List.mem_cons] at this ⊢
    rcases this with h | h | h
    · exact Or.inl h
    · exact absurd h hq'.2
    · exact Or.inr h
  · have hnone : E.sto l = none := by
      cases hc : E.sto l with
      | none => rfl
      | some c => exact absurd (hcov l c hql hc) hl
    refine ⟨.zero, Res.sum (L.map Rl), (Res.zero_add _).symm, ⟨fun _ => rfl, fun c hc => ?_⟩,
      L, Rl, hnd, fun l' c hq' hc => hcov l' c hq'.1 hc, fun l' hl' => ⟨hq l' hl', fun e => hl (e ▸ hl')⟩,
      rfl, hent⟩
    rw [hnone] at hc; cases hc
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:102 memHeldOn_unfocus
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_unfocusB {Q : AllocLabel → Prop} {E : TEnv} {s : St} {l : AllocLabel} {R H0 : Res}
    (hX : MemHeldOnB (fun l' => Q l' ∧ l' ≠ l) E s H0) (he : HeldEntryB E s l R) (hql : Q l) :
    MemHeldOnB Q E s (R + H0) := by
  classical
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := hX
  have hnl : l ∉ L := fun h => (hq l h).2 rfl
  have hmap : L.map (fun l' => if l' = l then R else Rl l') = L.map Rl :=
    List.map_congr_left fun l' hl' => by simp only [(hq l' hl').2, ↓reduceIte]
  refine ⟨l :: L, fun l' => if l' = l then R else Rl l', List.nodup_cons.2 ⟨hnl, hnd⟩,
    fun l' c hq' hc => ?_, fun l' hl' => ?_, ?_, fun l' hl' => ?_⟩
  · by_cases e : l' = l
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hcov l' c ⟨hq', e⟩ hc)
  · rcases List.mem_cons.1 hl' with e | h
    · exact e ▸ hql
    · exact (hq l' h).1
  · rw [List.map_cons, Res.sum_cons, hmap]; simp only [↓reduceIte]
  · by_cases e : l' = l
    · simp only [e, ↓reduceIte]; exact e ▸ he
    · simp only [e, ↓reduceIte]
      exact hent l' ((List.mem_cons.1 hl').resolve_left e)
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:125 memHeldOn_off
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_offB {Q : AllocLabel → Prop} {E : TEnv} {s : St} {l : AllocLabel} {H : Res}
    (h : MemHeldOnB Q E s H) (hql : ¬ Q l) : MemHeldOnB (fun l' => Q l' ∧ l' ≠ l) E s H := by
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := h
  exact ⟨L, Rl, hnd, fun l' c hq' hc => hcov l' c hq'.1 hc,
    fun l' hl' => ⟨hq l' hl', fun e => hql (e ▸ hq l' hl')⟩, rfl, hent⟩
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:132 heldEntry_tr
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem heldEntry_trB {E E' : TEnv} {s s' : St} {l : AllocLabel} {R : Res} (h : HeldEntryB E s l R)
    (hsto : E'.sto l = E.sto l) (hini : E'.ini l = E.ini l) (hri : E'.rini l = E.rini l)
    (hlat : ∀ o w, LatestNP s.mem (PromAt E s ⟨l, o⟩) ⟨l, o⟩ w → LatestNP s'.mem (PromAt E' s' ⟨l, o⟩) ⟨l, o⟩ w)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfRB E T vs R → ValOfRB E' T vs R) :
    HeldEntryB E' s' l R := by
  obtain ⟨Rs, hL, rfl⟩ := h.toS
  exact (HeldEntryL_trB hL hsto hini hri hlat hv).entry
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:142 memHeldOn_tr
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_trB {Q Q' : AllocLabel → Prop} {E E' : TEnv} {s s' : St} {H : Res} (h : MemHeldOnB Q E s H)
    (hQ : ∀ l, Q' l ↔ Q l)
    (hsto : ∀ l, Q l → E'.sto l = E.sto l) (hini : ∀ l, Q l → E'.ini l = E.ini l)
    (hri : ∀ l, Q l → E'.rini l = E.rini l) (hpf : ∀ l, Q l → E'.pfr l = E.pfr l)
    (htid : E'.tid = E.tid) (hfp : E'.fp = E.fp)
    (hlat : ∀ l, Q l → ∀ o w, LatestNP s.mem (PromAt E s ⟨l, o⟩) ⟨l, o⟩ w →
      LatestNP s'.mem (PromAt E s' ⟨l, o⟩) ⟨l, o⟩ w)
    (hv : ∀ {T : Ty} {vs : List Word} {R : Res}, ValOfRB E T vs R → ValOfRB E' T vs R) :
    MemHeldOnB Q' E' s' H := by
  obtain ⟨L, Rl, hnd, hcov, hq, rfl, hent⟩ := h
  refine ⟨L, Rl, hnd, fun l c hq' hc => hcov l c ((hQ l).1 hq') (by rw [← hsto l ((hQ l).1 hq')]; exact hc),
    fun l hl => (hQ l).2 (hq l hl), rfl, fun l hl => heldEntry_trB (hent l hl) (hsto l (hq l hl))
      (hini l (hq l hl)) (hri l (hq l hl)) (fun o w hw => ?_) hv⟩
  rw [PromAt_congr (a := ⟨l, o⟩) (hsto l (hq l hl)) htid (hpf l (hq l hl)) hfp (hini l (hq l hl))
    (TEnv.rc_congr (hini l (hq l hl)) (hri l (hq l hl)))]
  exact hlat l (hq l hl) o w hw
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:160 memHeldOn_store
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldOn_storeB {Q : AllocLabel → Prop} {E : TEnv} {s s' : St} {H : Res} {k : Promises.Knobs}
    {arch : Arch} {pw : Word} {a : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (h : MemHeldOnB Q E s H) (hoff : ∀ l, Q l → l ≠ a.label) (hpl : PromLt s)
    (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s) : MemHeldOnB Q E s' H :=
  memHeldOn_trB h (fun _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
    (fun l hq _ _ hl => LatestNP_growsAtF (storeUnits_growsF us ws 0 s s' hs).1
      (storeUnits_growsF us ws 0 s s' hs).2.1 (storeUnits_fulL hpl hs) (hoff l hq) hl) id
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:169 heldStoreAtP
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem heldStoreAtPB {Q : AllocLabel → Prop} {g : G} {E : TEnv} {s : St} {H : Res} {a : Address} {c : Cell} {us : List Acc}
    {ws : List Word} {U : Ty} {Rv : Res} (hm : MemInvB g E s) (hH : MemHeldOnB Q E s H) (hq : Q a.label)
    (hsto : E.sto a.label = some c) (hown : c.owner = some E.tid)
    (hnv : NVP E s a.label)
    (hcP : ∃ vals, CellOKB E (E.rc a.label) c.ty vals ∧
      ∀ o v, vals[o]? = some v → LatestP s.mem s.promises s.vs.coh ⟨a.label, o⟩ v)
    (hat : AtOff c.ty a.offset U)
    (hini : IniAt E.rc c a U) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hU : EnvValRB E U ws Rv) (hwU : wc U = some (nWords us)) (hlen : ws.length = nWords us) :
    ∃ vq Rq R2 H0, R2 + Rq + H0 = Rv + H ∧ vq.length = nWords us ∧
      (∀ j v, vq[j]? = some v → LatestP s.mem s.promises s.vs.coh (offs a (0 + j)) v) ∧
      VRRB (fun _ => 0) (CE E.unsee) U (shp U) vq Rq ∧
      ∀ (k : Promises.Knobs) (arch : Arch) (pw : Word) (rel : Bool) (s1 : St), s1.mem = s.mem →
        s1.promises = s.promises → LoadCohB E s s1 → (∀ b, s.vs.coh b ≤ s1.vs.coh b) →
        SeenLE E s1.vs.vRelSt →
        ∀ s', s' ∈ storeUnits k arch pw a rel us ws 0 s1 → MemHeldOnB Q E s' (R2 + H0) := by
  obtain ⟨vals, hcell, hlat⟩ := hcP
  obtain ⟨valsm, hW, hP⟩ := own_msgWordsN (E := E) hnv vals hlat
  obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focusB hH hq
  have hcR : CellOKRB E (E.ini a.label) (E.rc a.label) c.ty valsm R0 :=
    HeldEntry_cellB hent0 hsto hcell hW.length.symm (fun o w h => (hP o w h).2)
  rcases own_segRB hcR hat (IniAt_mono E.rc_le_ini hini) hna with
    ⟨b, oS, S, wS, Rs, Rr, -, hbo, hatS, hwS, hbw, hR0, ⟨hvs, hVs⟩, hput⟩ | ⟨N0, e0, -, hT0, -, -, hr0, -⟩
  rotate_left
  · rcases hini N0 e0 hT0 with ⟨hUc, -⟩ | ⟨-, j0, -, -, hj0, -, -⟩
    · exact absurd (hUc.trans hT0) (hna N0 e0)
    · have hj1 : j0 < E.rc a.label := hj0
      omega
  have hsl : ((valsm.drop b).take wS).length = wS := by
    simp only [List.length_take, List.length_drop]; omega
  obtain ⟨n, Rq, Rr2, hwn, hle, hRs, hvq, hput2⟩ := VRR_atB E.unsee hatS hvs (by rw [hsl]; exact hwS)
  rw [hwU] at hwn
  obtain rfl : nWords us = n := Option.some.inj hwn
  rw [hsl] at hle
  have hlenv : a.offset + nWords us ≤ valsm.length := by
    rw [← hbo, Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hle b) hbw
  have hvqe : (((valsm.drop b).take wS).drop oS).take (nWords us) = (valsm.drop a.offset).take (nWords us) := by
    rw [take_drop_take hle, drop_drop', hbo]
  rw [hvqe] at hvq
  refine ⟨(valsm.drop a.offset).take (nWords us), Rq, Rv + Rr2 + Rr, H0, ?_, by simp; omega,
    fun j v hj => ?_, hvq, fun k arch pw rel s1 e1 e2 e3 hmono hsn1 s' hs' => ?_⟩
  · subst hR0; subst hRs; exact Res.ext fun k => by simp only [Res.add_apply]; omega
  · have hj' : valsm[a.offset + j]? = some v := by
      by_cases hjn : j < nWords us
      · rw [List.getElem?_take_of_lt hjn, List.getElem?_drop] at hj; exact hj
      · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
    have e : offs a (0 + j) = ⟨a.label, a.offset + j⟩ := by simp [offs]
    rw [e]; exact (hP _ v hj').1
  
  have hpl1 : PromLt s1 := fun t ht => by
    rw [e1]; rw [e2] at ht; exact hm.2.2.1 t ht
  have hnd1 : s1.promises.Nodup := by rw [e2]; exact hm.2.2.2.2.2.2.2.2.2.2.1
  have e3' : ∀ o, o < vals.length → s1.vs.coh ⟨a.label, o⟩ = s.vs.coh ⟨a.label, o⟩ := by
    obtain ⟨valsB, hcB, hlatB, -⟩ := e3.1 a.label c hsto hown
    have hlB : valsB.length = vals.length := (CellOKR_lenB hcR hcB).symm.trans hW.length.symm
    intro o ho
    have hA := hlat o (vals[o]'ho) (List.getElem?_eq_getElem ho)
    obtain ⟨⟨m1, hm1, hl1, -⟩, hn1, -⟩ := hlatB o (valsB[o]'(hlB ▸ ho)) (List.getElem?_eq_getElem _)
    rcases Nat.lt_or_ge (s.vs.coh ⟨a.label, o⟩) (s1.vs.coh ⟨a.label, o⟩) with hlt | hge
    · exact absurd (hA.2.2 _ m1 hlt hm1 hl1) hn1
    · exact Nat.le_antisymm hge (hmono _)
  have htail : ∀ j : Nat, j < nWords us → TailP s1 (offs a (0 + j)) := fun j hj => by
    have hlt : a.offset + j < vals.length := by
      have h1 : vals.length = valsm.length := hW.length
      rw [h1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hlenv
    have hv := hlat (a.offset + j) (vals[a.offset + j]'hlt) (List.getElem?_eq_getElem hlt)
    have e : offs a (0 + j) = ⟨a.label, a.offset + j⟩ := by simp [offs]
    unfold TailP; rw [e1, e2, e, e3' _ hlt]
    exact fun t m ht hm hl => hv.2.2 t m ht hm hl
  obtain ⟨g2, g3⟩ := storeUnits_latP (a := a) us ws 0 s1 s1.vs.vRelSt hpl1 hnd1 (Nat.le_refl _) s' hs'
  replace g2 := g2 htail
  have hst := hU.store hsn1
  generalize hws' : ws.map (bumpW s1.vs.vRelSt) = ws' at hst
  have hlen' : ws'.length = nWords us := by rw [← hws', List.length_map]; exact hlen
  have hget : ∀ j w, ws[j]? = some w → ws'[j]? = some (bumpW s1.vs.vRelSt w) := fun j w hw => by
    rw [← hws', List.getElem?_map, hw]; rfl
  have hQ := hput2 ws' Rv hst.1 hlen'
  have hQV := (VR_putB (bkG := False) E.unsee hatS (VRR_VRB (bkG := False) S (RLink_ofB (Coh_CEB _) (CohR_CEB _)) hvs) hVs (by rw [hsl]; exact hwS)
    (VRR_VRB (bkG := False) U (RLink_ofB (Coh_CEB _) (CohR_CEB _)) hst.1) hst.2 (by rw [hlen']; exact hwU)).2.2
  rw [hlen'] at hQV
  have hQl : (((valsm.drop b).take wS).take oS ++ ws' ++ ((valsm.drop b).take wS).drop (oS + nWords us)).length = wS := by
    simp only [List.length_append, List.length_take, List.length_drop, hlen']; omega
  have hcell' := hput _ _ ⟨hQ, hQV⟩ hQl
  have hsp := splice_seg valsm ws' b wS oS (by rw [hlen']; exact hle)
  rw [hlen'] at hsp
  rw [hsp, hbo] at hcell'
  have hlat' : ∀ o v, (valsm.take a.offset ++ ws' ++ valsm.drop (a.offset + nWords us))[o]? = some v →
      LatestP s'.mem s'.promises s'.vs.coh ⟨a.label, o⟩ v := by
    intro o v hov
    rw [splice_get valsm ws' a.offset (nWords us) o hlen' hlenv] at hov
    by_cases hr : a.offset ≤ o ∧ o < a.offset + nWords us
    · rw [iteT hr] at hov
      obtain ⟨hr1, hr2⟩ := hr
      have hj : o - a.offset < ws.length := by rw [hlen]; exact Nat.sub_lt_left_of_lt_add hr1 hr2
      obtain ⟨w, hw⟩ : ∃ w, ws[o - a.offset]? = some w := ⟨ws[o - a.offset], List.getElem?_eq_getElem hj⟩
      rw [hget _ _ hw] at hov
      cases hov
      have := g2 (o - a.offset) w (by rw [← hlen]; exact hj) hw
      have e2 : offs a (0 + (o - a.offset)) = ⟨a.label, o⟩ := by
        simp only [offs, Nat.zero_add]; congr 1; exact Nat.add_sub_of_le hr1
      rw [e2] at this; exact this
    · rw [iteF hr] at hov
      have hold := (hP o v hov).1
      have hov' : o < vals.length := by rw [hW.length]; exact (List.getElem?_eq_some_iff.1 hov).1
      rw [← e1, ← e2] at hold
      replace hold := LatestS_coh_congr (e3' o hov') hold
      refine g3 _ _ (fun j hj e => ?_) hold
      have h' : o = a.offset + j := by simpa [offs] using congrArg WeakMem.Address.offset e
      subst h'
      exact hr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩
  have hent : HeldEntryB E s' a.label (Rv + Rr2 + Rr) :=
    HeldEntry_ownNB hsto (NVP_store (NVP_eqs hnv e1 e2) hpl1 hs') hlat' hcell'
  exact memHeldOn_unfocusB (memHeldOn_storeB (memHeldOn_eqsB hX e1 e2) (fun _ h => h.2) hpl1 hs') hent hq
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:286 OwnXLeS
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXLeSB (p : Prog) (g : G) (E0 : TEnv) (x : AllocLabel) (n : Nat) (mem : Memory) (pairs : List Ts)
    (th : TTh) : Prop :=
  ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E th Tot ∧ MemInvB g E (stOf mem pairs th) ∧ MemHeldPB E (stOf mem pairs th) HP ∧
    g.boxFence = true ∧ StoNIE E ∧ E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ n ∧
    ExtB E0 E ∧ AnchR E0 E0 E (stOf mem pairs th) ∧ TyOKE g E ∧ RecFresh g g.i th.nalloc ∧ (n = 0 → E.rini x ≤ E0.rini x) ∧
    ((∀ l, E0.rini l ≤ E0.ini l) → ∀ l, E.rini l ≤ E.ini l)
end
end TermOwnHeldQ.Flat

-- ♭ MemInv_tys.
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem MemInvB_tys (g : G) (t : AllocLabel → Option (Ty × Bool)) (E : TEnv) (s : St) :
    MemInvB { g with tys := t } E s ↔ MemInvB g E s := by
  unfold MemInvB; rw [BoxInv_tys]; exact Iff.rfl
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:294 OwnXStepL
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepLB (p : Prog) (x : AllocLabel) (n : Nat) (T : Expr → Prop) : Prop :=
  ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh), g.p = p → 0 < g.n →
    T th.term → ∀ E0 : TEnv, ScopeOKB g.lbase g.n g.i p th →
    (∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts) → OwnXLeSB p g E0 x n mem pairs th →
    r ∈ tstep g mem pairs th → PromAbove (stOf r.1 r.2.1 r.2.2) → PAx g mem pairs th →
    OwnXLeSB p { g with tys := tysUpd g.tys th r.2.2 } E0 x n r.1 r.2.1 r.2.2
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:302 ownXStepPkg_of_local
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepPkg_of_localB {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n q : Nat}
    (h : OwnXStepLB p x n (fun t => exprPkg t = q)) : OwnXStepPkgB p k arch i x n q := by
  intro E0 c0 c0' th hth hq hsc hvI hI hs hc
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨th1, E, Tot, HP, hth1, hT, hm, hP, hb, hni, hsx, hle, hx0, hA, hTy, hRc, hZ, hR⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hS := h (gOf p k arch c0 i) c0.mem c0.pairs th r rfl
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))) hq E0 (hsc th hth (TermTyped.not_spawnT_of_steps hth hs)) (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth)
    ⟨E, Tot, HP, hT, hm, hP, hb, hni, hsx, hle, hx0, hA, hTy, hRc, hZ, hR⟩ hr hpa (PAx_of_step hs hc hth)
  obtain ⟨E', Tot', HP', hT', hm', hP', hb', hni', hsx', hle', hx', hA', hTy', hRc', hZ', hR'⟩ := hS
  have hsub := TermTyped.tysOf_thread hs hth e3 hRc
  refine ⟨r.2.2, E', Tot', HP', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, ?_, hni', hsx', hle', hx', ?_, ?_, ?_, hZ', hR'⟩
  · rw [gOf_thread hs, e1, e2, MemInvB_tys]; exact (MemInvB_tys _ _ _ _).1 hm'
  · rw [e1, e2]; exact hP'
  · rw [gOf_thread hs]; exact hb'
  · rw [e1, e2]; exact hA'
  · rw [gOf_thread hs]; exact TyOKE_mono hsub hTy'
  · rw [gOf_thread hs]
    exact RecFresh_sub (g := { gOf p k arch c0 i with tys := tysUpd (gOf p k arch c0 i).tys th r.2.2 })
      (g' := { gOf p k arch c0 i with tys := tysOf c0' }) hsub rfl rfl hRc'
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:323 StepC
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def StepCB (p : Prog) (g : G) (x : AllocLabel) (E : TEnv) (s : St) (th : TTh) (Tot0 HP0 : Res)
    (r : Memory × List Ts × TTh) : Prop :=
  ∃ E' Tot' HP', ThInvREB g.lbase g.n g.i p E' r.2.2 Tot' ∧ MemInvB g E' (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldPB E' (stOf r.1 r.2.1 r.2.2) HP' ∧ StoNIE E' ∧ E'.sto x ≠ none ∧
    Tot' (.own x) + HP' (.own x) ≤ Tot0 (.own x) + HP0 (.own x) ∧
    AnchStepB g th E E' s (stOf r.1 r.2.1 r.2.2) ∧
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E' ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc
end
end TermOwnHeldQ.Flat

-- ♭ mirrors of W TermOwnHeldQ StepCK / stepC_ofK.
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def StepCKB (p : Prog) (g : G) (x : AllocLabel) (E : TEnv) (s : St) (th : TTh) (Tot0 HP0 : Res)
    (r : Memory × List Ts × TTh) : Prop :=
  ∃ Tot' HP', ThInvREB g.lbase g.n g.i p E r.2.2 Tot' ∧ MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP' ∧ StoNIE E ∧ E.sto x ≠ none ∧
    Tot' (.own x) + HP' (.own x) ≤ Tot0 (.own x) + HP0 (.own x) ∧
    AnchStepB g th E E s (stOf r.1 r.2.1 r.2.2)
theorem stepC_ofKB {p : Prog} {g : G} {x : AllocLabel} {E : TEnv} {s : St} {th : TTh} {Tot0 HP0 : Res}
    {r : Memory × List Ts × TTh} (h : StepCKB p g x E s th Tot0 HP0 r)
    (hk : TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc) :
    StepCB p g x E s th Tot0 HP0 r :=
  let ⟨T', H', h1, h2, h3, h4, h5, h6, h7⟩ := h
  ⟨E, T', H', h1, h2, h3, h4, h5, h6, h7, hk.1, hk.2⟩
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:331 ownXStepL_of
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_ofB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} {T : Expr → Prop}
    (h : ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh) (ρ : Nat → Nat)
      (η : TEnv) (cx : Cx) (Rf Rs HP : Res), g.p = p → 0 < g.n → T th.term → ScopeOKB g.lbase g.n g.i p th →
      EnvOKB p η → TypedK p η cx th.term → TvOK cx →
      FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf → RetPw th.σs th.stack cx.ret →
      DyFr p annNew (progTgts p) η th.σs th.term → MemInvB g (CE η) (stOf mem pairs th) →
      MemHeldPB (CE η) (stOf mem pairs th) HP → g.boxFence = true → StoNIE (CE η) → (CE η).sto x ≠ none →
      TyOKE g (CE η) → RecFresh g g.i th.nalloc →
      r ∈ tstep g mem pairs th → PromAbove (stOf r.1 r.2.1 r.2.2) → PAx g mem pairs th →
      StepCB p g x (CE η) (stOf mem pairs th) th (Rf + Rs) HP r) :
    OwnXStepLB p x n T := by
  intro g mem pairs th r hp hn ht E0 hsc hvr hS hr hpa hpx
  obtain ⟨E, Tot, HP, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hi, rfl, hRP, hDy⟩, hm, hP, hb, hni, hx, hle, hx0, hA, hTy, hRc, hZ, hR⟩ := hS
  obtain ⟨E', Tot', HP', h1, h2, h3, h0, h4, h5, h6, h7, h8⟩ :=
    h g mem pairs th r ρ η cx Rf Rs HP hp hn ht hsc hE hT htv hi hRP hDy hm hP hb hni hx hTy hRc hr hpa hpx
  have hFp := finv_ofB htv hi
  obtain ⟨hx', hA'⟩ := h6.1 E0 hx0 hA hm.2.2.2.1.old h2 (wrHypB hE hT.1 htv hFp hm (hsc ρ η cx hE hT.1 htv hFp) hvr hr)
  refine ⟨E', Tot', HP', h1, (MemInvB_tys _ _ _ _).2 h2, h3, hb, h0, h4, by omega, hx', hA', h7, h8, fun hn0 => ?_, fun h => h6.2.2 (hR h)⟩
  subst hn0
  have hR0 : Rf (.own x) = 0 := by simp only [Res.add_apply] at hle; omega
  rcases h6.2.1 x hx with h7 | h7
  · exact Nat.le_trans h7 (hZ rfl)
  · exact absurd h7 (not_bufInitL_ofB hE hT.1 hi hR0)
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnK1.lean:43 memHeldP_promSt
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldP_promStB {E : TEnv} {s : St} {H : Res} {a : Address} {v : WeakMem.Val} {w : Ts}
    (h : MemHeldPB E s H) : MemHeldPB E (promSt s a v w) H := by
  obtain ⟨L, Rl, hnd, hc, hq, hH, hR⟩ := h
  refine ⟨L, Rl, hnd, hc, hq, hH, fun l hl => ⟨(hR l hl).1, fun c hc' => ?_⟩⟩
  obtain ⟨vals, hv, hok⟩ := (hR l hl).2 c hc'
  have hP : Priv E l := hq l hl
  refine ⟨vals, fun o y hy => ?_, hok⟩
  have hnV : ¬ VisU E ⟨l, o⟩ := fun h => h.2 hP
  have hnQ : ¬ PredU E ⟨l, o⟩ := fun h => h.1 hP.2
  have h0 := hv o y hy
  rw [PromAt_nword hnV hnQ] at h0
  rw [PromAt_nword hnV hnQ, promSt_mem, promSt_promises]
  refine LatestNP_congrP (fun t _ _ _ => ?_) (LatestNP_push_prom _ h0)
  simp only [List.mem_append]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
end
end TermOwnK1.Flat

-- PORTB TermOwnK1.lean:79 stoNIE_efootW
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stoNIE_efootWB {g : G} {E E' : TEnv} {s s' : St} (hf : EFootWB g E E' s s') (h : StoNIE E) :
    StoNIE E' := by
  intro l cl hl
  rcases hf.2.2.1 l with he | ⟨-, T, hT, ⟨-, -, hn⟩, -⟩
  · exact h l cl (he ▸ hl)
  · rw [hT] at hl; cases hl; exact hn
end
end TermOwnK1.Flat

-- PORTB TermOwnK1.lean:86 stoNIE_footW
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stoNIE_footWB {g : G} {E E' : TEnv} {s s' : St} (hf : FootWB g E E' s s') (h : StoNIE E) : StoNIE E' :=
  stoNIE_efootWB hf.1 h
end
end TermOwnK1.Flat

-- PORTB TermOwnK1.lean:90 ownXStep_k1
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k1B {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : ∀ n, OwnXStepPkgB p k arch i x n 1 := by
  intro n E0 c0 c0' th hth hq hsc _ hI hs _
  obtain ⟨th0, E, Tot, HP, hth0, hT, hm, hHP, hb, hni, hsx, hle, hx0, hA, hTyE, hRc, hZ, hRl⟩ := hI
  obtain rfl : th0 = th := Option.some.inj (hth0.symm.trans hth)
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hTy, htv, hFI, hsum, hRP, hDy⟩ := hT
  subst hCE
  have hFI0 : FInvB c0.lbase c0.n i ρ η th0.σs (ResumeB c0.lbase c0.n i p th0.stack) cx th0.env :=
    FInvR_FInvB htv.2.2.2.2.2.2.2
      (fun E rd ws R h => ResumeR_ResumeB (fun _ h => h.2.2.2.2.2.2.2) th0.stack Rs E rd ws R h) hFI
  have hR := scopeR_of_pkg1 hTy.1 hq (hsc th0 hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hTy.1 htv hFI0)
  obtain ⟨th1, r, hth1, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  obtain rfl : th1 = th0 := Option.some.inj (hth1.symm.trans hth)
  obtain ⟨Tot', hT', hts⟩ := (tstepR_stepB (hDy := hDy) hP rfl (tstep_notDone hr) hR hTy.1 hTy.2 hFI hE
    (supI_of_memInvB hm (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (TermCert.arr_lt hth)))) htv hRP hPS hSub hSig).2 r hr
  obtain ⟨em, ep, hm'⟩ := frame_keepB hR hTy.1 hTy.2 hFI hE htv hm r hr
  have hg := gOf_thread hs
  have h0 := totStep_own_le hts x
  rw [hsum] at h0
  have hkeep := TermNallocF.tstep_tys_keep hr (fun x a T e h => by rw [h] at hq; simp [exprPkg, opPkg] at hq)
  have hsub : TysSub (tysOf c0') (gOf p k arch c0 i).tys := fun l u h => by
    have h1 := TermTyped.tysOf_thread hs hth e3 hRc l u h
    rwa [tysUpd_keep hkeep] at h1
  refine ⟨r.2.2, CE η, Tot', HP, e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, ?_, hni, hsx, by omega, hx0, ?_, ?_, ?_, hZ, hRl⟩
  · rw [hg, e1, e2]; exact hm'
  · rw [e1, e2]; exact memHeldOn_eqsB hHP em ep
  · rw [hg]; exact hb
  · rw [e1, e2]; exact anchR_eqs hA em ep
  · rw [hg]; exact TyOKE_mono (g := gOf p k arch c0 i) hsub hTyE
  · rw [hg]
    exact RecFresh_sub (g := gOf p k arch c0 i) (g' := { gOf p k arch c0 i with tys := tysOf c0' }) hsub rfl rfl
      (RecFresh_mono hRc (TermNallocF.tstep_nallocLe hr))
end
end TermOwnK1.Flat

-- PORTB TermOwnK1.lean:115 ownXStepP_all
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepP_allB {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} :
    ∀ n, OwnXStepPB p k arch i x n := by
  intro n E0 c0 a v w h _ _
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hHP, hb, hni, hsx, hle, hx0, hA, hTyE, hRc, hZ, hR⟩ := h
  obtain ⟨-, h2, h3⟩ := promise_inv (a := a) (v := v) (w := w) hth
  refine ⟨_, E, Tot, HP, h2, (by rw [show (promise c0 i a v w).lbase = c0.lbase from congrArg G.lbase (gOf_promise (p := p) (k := k) (arch := arch)), promise_n]; exact hT), ?_, ?_, ?_, hni, hsx, hle, hx0, anchR_prom hth hA, ?_, ?_, hZ, hR⟩
  · rw [gOf_promise, h3]; exact MemInv_promStB hm
  · rw [h3]; exact memHeldP_promStB hHP
  · rw [gOf_promise]; exact hb
  · rw [gOf_promise]; exact hTyE
  · rw [gOf_promise]; exact hRc
end
end TermOwnK1.Flat

-- PORTB TermOwnK2.lean:24 stepC_keep
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepC_keepB {p : Prog} {g : G} {η : TEnv} {th th1 : TTh} {s s' : St} {Rf Rs HP : Res} {z : AllocLabel}
    (hT : ThInvREB g.lbase g.n g.i p (CE η) (withS th1 s') (Rf + Rs)) (hm : MemInvB g (CE η) s')
    (hH : MemHeldPB (CE η) s HP) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises)
    (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) : StepCKB p g z (CE η) s th (Rf + Rs) HP (s'.mem, s'.pairs, withS th1 s') :=
  ⟨Rf + Rs, HP, hT, hm, memHeldOn_eqsB hH e1 e2, hni, hx, Nat.le_refl _, anchStep_eqsB e1 e2⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:32 privStore
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem privStoreB {E : TEnv} {s s' : St} {HP D : Res} {k : Promises.Knobs} {arch : Arch} {pw : Word}
    {a : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hH : MemHeldPB E s HP) (hpl : PromLt s) (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s)
    (hent : Priv E a.label → ∀ R0, HeldEntryB E s a.label R0 →
      ∃ R2, HeldEntryB E s' a.label R2 ∧ ∀ y : Nat, R2 (.own y) ≤ R0 (.own y) + D (.own y)) :
    ∃ HP', MemHeldPB E s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + D (.own y) := by
  by_cases hq : Priv E a.label
  · obtain ⟨R0, H0, rfl, he, hX⟩ := memHeldOn_focusB hH hq
    obtain ⟨R2, he2, hle⟩ := hent hq R0 he
    refine ⟨R2 + H0, memHeldOn_unfocusB (memHeldOn_storeB hX (fun l h => h.2) hpl hs) he2 hq, fun y => ?_⟩
    have := hle y
    simp only [Res.add_apply]; omega
  · exact ⟨HP, memHeldOn_storeB hH (fun l h e => hq (e ▸ h)) hpl hs, fun y => Nat.le_add_right _ _⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:48 stepC_own
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepC_ownB {p : Prog} {g : G} {η : TEnv} {r : Memory × List Ts × TTh} {Rf Rs Rr D HP : Res}
    {z : AllocLabel} {th : TTh} {s : St} (hnb : ∀ E1, BumpIf th E1) (hT : ThInvREB g.lbase g.n g.i p (CE η) r.2.2 (Rr + Rs)) (hm : MemInvB g (CE η) (stOf r.1 r.2.1 r.2.2))
    (hH : ∃ HP', MemHeldPB (CE η) (stOf r.1 r.2.1 r.2.2) HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + D (.own y))
    (hle : D (.own z) + Rr (.own z) ≤ Rf (.own z)) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) :
    StepCKB p g z (CE η) s th (Rf + Rs) HP r := by
  obtain ⟨HP', hH', hle'⟩ := hH
  refine ⟨Rr + Rs, HP', hT, hm, hH', hni, hx, ?_, anchStep_sameB hnb⟩
  have h2 := hle' z
  simp only [Res.add_apply]
  omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:66 k2_loadOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hnwc : wordOf (close th.σs (.ptr .own u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv (bind_opaqueOK hb)
  have hwr : wordOf (Ty.ptr .own ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  have hvz : VRRB ρ η u (shp ru) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  exact stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:127 k2_loadLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .own u) = some (.own, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .own ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi0.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi0.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := acq)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (cell_lyt hl.2.2.2.2 rfl rfl).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have hvz : VRRB ρ η u (shp ru) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:203 k2_loadAt
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadAtB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.loadAt b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAt hp hbuf hint hlt hltk haf hb =>
  obtain ⟨t, u, n, k, j, hp, hbuf, hint, hlt, hltk, haf, hb⟩ : ∃ t u n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      affine cx.ke u = false ∧ cx.bind x u = .ok c' :=
    ⟨_, _, _, _, _, hp, hbuf, hint, hlt, hltk, haf, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, hini, hsku, hsig, htbS, -⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk (bind_opaqueOK hb)
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htbS (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ur, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have htb : tb cx.ke.length u = true := tb_bufOf (peek_tb htv hp) hbuf
  have hvz : VRRB ρ η u (shp ur) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:251 k2_loadAtF
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadAtFB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {q : List Nat} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.loadAtF b i q) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAtF hp hbuf hct hop hint hlt hltk haf hb =>
  obtain ⟨t, u, c, n, k, j, hp, hbuf, hct, hop, hint, hlt, hltk, haf, hb⟩ : ∃ t u c n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧ IntIdx cx i j ∧
      LtI cx j n ∧ LtI cx j k ∧ affine cx.ke c = false ∧ cx.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, haf, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, -, hsku, hsig, htbS, hiniF⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat' (hiniF o _ hato) hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) (tb_compTy q u c hct htbS) (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco))
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, cR, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, hco, hcs, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct (tb_bufOf (peek_tb htv hp) hbuf)
  have hvz : VRRB ρ η c (shp cR) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:302 k2_loadPub
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadPubB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hnwc : wordOf (close th.σs (.ptr .pub u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk (bind_opaqueOK hb) hi0 hE htv hm
  have hwr : wordOf (Ty.ptr .pub ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay', hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame us 0 _ (s', wsr) hl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  have hvz : VRRB ρ η u (shp ru) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay'
  rw [Res.add_zero] at hfr
  exact stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm' hH f1 f3 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:360 k2_loadPubLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadPubLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .pub u) = some (.pub, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi0.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi0.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  by_cases hown : c.owner = some η.tid
  · 
    obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadIB (arch := g.arch) (pw := pw) (acq := acq)
      (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
      (fun hnr f hf hns => by
        simp only [ModeOKF, ModeOKb] at hmode
        obtain ⟨f0, hf0, hsf⟩ := hmode
        obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
        rcases hsf with hs | hs
        · exact absurd hs hns
        · rcases hs with hs | ⟨hso, hs⟩
          · exact hs pw (by simp)
          · first | exact hs.elim | exact absurd hso hown | exact absurd hs hnr | (rcases hs with hs | hs <;> first | exact hs.elim | exact absurd hs hnr)) hsku hsig
        (cell_lyt hl.2.2.2.2 rfl rfl).2
          (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨hvr, hlay', f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
    have hvz := VR_VRR_copy_finvB hi0 hE haf htb hvr
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay'
    rw [Res.add_zero] at hfr
    exact stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
      (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
  · 
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, hsf⟩ := hmode
    have hfv : f ≤ pw.view := by
      rcases hsf with hs | hs
      · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
        · refine absurd ?_ hown
          have h1' : η.sto ad.label = some c0 := h1
          rw [hsto] at h1'
          rw [Option.some.inj h1']; exact h2
        · have h1' : η.sto ad.label = none := h1
          rw [hsto] at h1'; cases h1'
      · rcases hs with hs | ⟨hso, -⟩
        · exact hs pw (by simp)
        · exact absurd hso hown
    have hlU : accs (cl ρ η.wit 0 0 u) ≠ none := by
      rcases AtOff_lay hat with h | ⟨N, e', h, -⟩
      · exact h
      · exact absurd h (hna N e')
    have hlr := pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
    obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := Option.ne_none_iff_exists'.1 (by rw [hlr]; exact hlU)
    have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    obtain ⟨⟨r0, hr0⟩, hval, hsv⟩ := pubLoadAtB (arch := g.arch) (pw := pw) (acq := acq)
      hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨q, hq, hle⟩ := hval (s', wsr) hl' (hpr0)
    have hrl : wsr.length = nWords us := (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
    obtain ⟨f1, f2, f3, f4⟩ := loadUnits_frame us 0 _ (s', wsr) hl'
    obtain ⟨hvr0, hV0⟩ := ValOfB.env hq
    have hvr : (VRF False) ρ η u (shp ru) wsr := by
      rw [shp_of_sig hsig]
      exact (VR_closeB hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_upB (bkG := False) _ _ q wsr hle hvr0)
    have hlay' : Lay th.σs u ru wsr :=
      ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
        Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩
    have hvz := VR_VRR_copy_finvB hi0 hE haf htb hvr
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay'
    rw [Res.add_zero] at hfr
    refine stepC_keepB ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
      ?_ hH f1 f3 hni hx
    refine MemInv_loadFB hm f1 f2 (fun l c1 hc1 ho1 o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ ?_)
      f3 f4 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')
      (fun l B hB o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ (fun he => by
        have h0 := (hm.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1
        have hl0 : l = ad.label := he
        rw [hl0] at h0; have h1 : η.sto ad.label = none := h0; rw [hsto] at h1; cases h1))
    intro hle'
    have hl'' : l = ad.label := hle'
    have h1 : η.sto l = some c1 := hc1
    rw [hl'', hsto] at h1
    exact hown (by rw [Option.some.inj h1]; exact ho1)
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:503 k2_loadWordOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadWordOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P)))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi0 hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  have hfr := bindR0B hb (pushRB x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keepB ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    ((MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl))) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:551 k2_loadWordPub
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadWordPubB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P)))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk
      (by simp [Cx.opaqueOK, Ty.guardT]) hi0 hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame us 0 _ (s', wsr) hl
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  have hfr := bindR0B hb (pushRB x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keepB ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm' hH f1 f3 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:595 k2_loadWordLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadWordLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  have hg' : P.ghost = false := hg
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg']
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs)
      hpk hμ (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi0 hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, haddr, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.one] 0 _ (s', wsr) hl
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg' hvr
  have hfr := bindR0B hb (pushRB x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keepB ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm' hH f1 f3 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:644 k2_storeOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have hvalR : EnvValRB (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRRB ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_subB hsat hsub _ _ _ hvrv
    have hvc : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRRB η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine stepC_ownB (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩ (MemInv_storeB hm hsto hown husA hval hlen s' hs')
    (privStoreB hH hm.2.2.1 hs' fun hq R0 _ => ?_) (own_le hle z) hni hx
  obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
    (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodupB hm) (Nat.le_refl _) s' hs'
  have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
    have := OwnOKPF_tailB hm.2.1 hsto hown hq.2 hus' j hj
    simpa [offs] using this
  exact ⟨Rv, HeldEntry_ownNB hsto (NVP_store (NVP_priv hq) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
    (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩), fun y => Nat.le_add_left _ _⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:727 k2_storeLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi0 hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine stepC_ownB (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_storeAtB hm hsto hown hat hini hna hval hwUA hlen s' hs') ?_ (own_le hle z) hni hx
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := heldStoreAtPB hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) hat hini hna hvalR hwU hlen
    refine ⟨R2 + H0, hput g.k g.arch pw rel _ rfl rfl (LoadCoh_of_eqB hm.2.1 rfl) (fun _ => Nat.le_refl _)
      hm.2.2.2.2.1 s' hs', fun y => ?_⟩
    have h2 := congrArg (fun R : Res => R (.own y)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · exact ⟨HP, memHeldOn_storeB hH (fun l h e => hq (e ▸ h)) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:802 k2_storePub
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storePubB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hlr : accs ru = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    cases h : accs ru with
    | none => rw [h] at hlr; exact absurd hlr.symm hacc
    | some us => exact ⟨us, rfl⟩
  have husc : accs c.ty = some us := by rw [← hlr, hus]
  have hus' : wc c.ty = some (nWords us) := by simp [wc, husc]
  have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValRB (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRRB ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_subB hsat hsub _ _ _ hvrv
    have hvc : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRRB η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  by_cases hown : c.owner = some η.tid
  · refine stepC_ownB (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩ (MemInv_storeFB hm hsto hown husc hval hlen s' hs')
      (privStoreB hH hm.2.2.1 hs' fun hq R0 _ => ?_) (own_le hle z) hni hx
    obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
      (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodupB hm) (Nat.le_refl _) s' hs'
    have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
      have := OwnOKPF_tailB hm.2.1 hsto hown hq.2 hus' j hj
      simpa [offs] using this
    exact ⟨Rv, HeldEntry_ownNB hsto (NVP_store (NVP_priv hq) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
      (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩), fun y => Nat.le_add_left _ _⟩
  · refine stepC_ownB (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
      (MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs')
      ⟨HP, memHeldOn_storeB hH (fun l h e => ?_) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩ (own_le hle z) hni hx
    obtain ⟨⟨c2, h2, ho⟩, -⟩ := h
    have h3 : η.sto lab = some c2 := by rw [e] at h2; exact h2
    rw [hsto] at h3; cases h3; exact hown ho
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:894 k2_storePubLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storePubLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .pub u) = some (.pub, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  have hlr := pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := hlr.symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  simp only [ModeOKF, ModeOKb] at hmode
  obtain ⟨f, hf, -⟩ := hmode
  refine stepC_ownB (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (by by_cases hown : c.owner = some η.tid
        · exact MemInv_storeAtIB hm hsto hown hat hini hna hval hwUA hlen s' hs'
        · exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval husU hlen s' hs')
    ⟨HP, memHeldOn_storeB hH (fun l h e => ?_) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩ (own_le hle z) hni hx
  have h3 : η.pfr ad.label = none := by rw [← e]; exact h.2
  rw [hf] at h3; cases h3
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:985 oldFree
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem oldFreeB {ρ : Nat → Nat} {η : TEnv} {u ru T : Ty} {ws : List Word} (hco : CohBW η) (hcr : CohRB η)
    (hTU : ∀ S ws, (VRF False) (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) S ws → (VRF False) (fun _ => 0) (CE η) T S ws)
    (hUT : ∀ S ws R, VRRB (fun _ => 0) (CE η) T S ws R → VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) S ws R)
    (hni : noIallV T = true) (hno : Ty.noOwnIn [] T = true) (hv : (VRF False) ρ η u (shp ru) ws) :
    ∃ R, VRRB ρ η u (shp ru) ws R ∧ ∀ y : Nat, R (.own y) = 0 := by
  have h2 := (VR_closeB hco ρ u [] 0 ρ (fun _ => 0) (shp ru) ws (fun k => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨R, hR⟩ := VR_VRRB T hni (RInvZ_CE η) (hTU _ _ h2)
  exact ⟨R, (VRR_closeB hco hcr ρ u [] 0 ρ (fun _ => 0) (shp ru) ws R (fun k => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (hUT _ _ _ hR),
    fun y => TermBlkZ.Flat.VRR_own_zeroB y T [] (CE η) _ _ _ R hno (fun _ _ _ _ h => h.elim) (fun _ _ _ _ h => h.elim) hR⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:998 k2_xchgOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_xchgOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hxz : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValRB (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRRB ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_subB hsat hsub _ _ _ hvrv
    have hvc : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRRB η hcty).2 hvc
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInvB g (CE η) r1.1 :=
    fun r1 h hp => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  by_cases hq : Priv (CE η) lab
  · have hnv := NVP_priv (s := stOf mem pairs th) hq
    obtain ⟨vals, hcell, hlat⟩ := OwnOKPF_cellPB hm.2.1 hsto hown hq.2
    have hwc := (hcell.plain (notArr_of_wc hus')).1
    obtain ⟨vals', hWv, hP'⟩ := own_msgWordsN (E := CE η) hnv vals hlat
    have hl' : vals'.length = nWords us := by
      rw [← hWv.length]; rw [hus'] at hwc; exact (Option.some.inj hwc).symm
    obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focusB hH hq
    have hvR0 : ValOfRB (CE η) c.ty vals' R0 :=
      HeldEntry_valsB hent0 hsto hna (by rw [hus', hl']) (fun o w h => (hP' o w h).2)
    have hWold : WLe vals' old := (loadUnits_latestPA hl'
      (fun j w hj => by simpa [offs] using (hP' j w hj).1) h1 hp1).1
    have hvold : VRRB ρ η u (shp ru) old R0 := by
      have h1 := VRR_upB _ _ _ _ _ hWold hvR0.1
      have h2 : VRRB (fun _ => 0) (CE η) c.ty (shp c.ty) old R0 :=
        VRR_monoB c.ty (CE (CE η).unsee) (CE η) _ _ _ _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
          (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h1
      have h3 := (Fd_VRRB η hcty).1 h2
      rw [(Fd_lay hcty).1, ← shp_of_sig hsig] at h3
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp ru) old R0 (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 h3
    obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 s1 s1.vs.vRelSt hm1'.2.2.1
      hm1'.2.2.2.2.2.2.2.2.2.2.1 (Nat.le_refl _) s2 hs2
    have htail : ∀ j : Nat, j < nWords us → TailP s1 (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
      have := cellP_tailLoadB (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) fc (loadUnits_cohMono us 0 _ _ h1) f1 f3
        hsto hown hus' j hj
      simpa [offs] using this
    have hent : HeldEntryB (CE η) s2 lab Rv := HeldEntry_ownNB hsto (NVP_store (NVP_eqs hnv f1 f3) hm1'.2.2.1 hs2)
      (storeOwn_latestP hlen (g2 htail))
      (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hm1'.2.2.2.2.1⟩)
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + R0 + Rs, Rv + H0, ⟨ρ, η, c', Rr + R0, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeB hm1' hsto hown husA hval hlen s2 hs2,
      memHeldOn_unfocusB (memHeldOn_storeB (memHeldOn_eqsB hX f1 f3) (fun l h => h.2) hm1'.2.2.1 hs2) hent hq, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    simp only [Res.add_apply]; omega
  · obtain ⟨f, hf⟩ : ∃ f, (CE η).pfr lab = some f := by
      cases h : (CE η).pfr lab with
      | none => exact absurd ⟨⟨c, hsto, hown⟩, h⟩ hq
      | some f => exact ⟨f, rfl⟩
    obtain ⟨R1, hvold, hz⟩ := oldFreeB (T := c.ty) hE.2.1 hE.2.2 (fun S ws => (Fd_VRB η hcty).2) (fun S ws R => (Fd_VRRB η hcty).1)
      (hni lab c hsto) (MemInv_noOwnTB hm hsto hf) hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + R1 + Rs, HP, ⟨ρ, η, c', Rr + R1, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeB hm1' hsto hown husA hval hlen s2 hs2,
      memHeldOn_storeB (memHeldOn_eqsB hH f1 f3) (fun l h e => hq (by rw [e] at h; exact h)) hm1'.2.2.1 hs2, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := hz z
    simp only [Res.add_apply]; omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1128 k2_xchgLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_xchgLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hxz : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig (sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1))]
    exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi0 hpk htv ho hwcu
  obtain ⟨us, hus, -, hld, -⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInvB g (CE η) r1.1 :=
    fun r1 h hp => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput⟩ := heldStoreAtPB hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) hat hini hna hvalR hwU hlen
    have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
    have hvold := oldValRB hE.2.1 hE.2.2 hsig (VRR_upB _ _ _ _ _ hWold hvqR)
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      hput g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := congrArg (fun R : Res => R (.own z)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · obtain ⟨f, hf⟩ : ∃ f, (CE η).pfr ad.label = some f := by
      cases h : (CE η).pfr ad.label with
      | none => exact absurd ⟨⟨c, hsto, hown⟩, h⟩ hq
      | some f => exact ⟨f, rfl⟩
    obtain ⟨R1, hvold, hz⟩ := oldFreeB (T := (cl ρ η.wit 0 0 u)) hE.2.1 hE.2.2 (fun _ _ h => h) (fun _ _ _ h => h)
      (TermPlant.noIallV_AtOffP hat (hni _ c hsto)) (noOwn_AtOff hat (MemInv_noOwnTB hm hsto hf)) hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + R1 + Rs, HP, ⟨ρ, η, c', Rr + R1, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      memHeldOn_storeB (memHeldOn_eqsB hH f1 f3) (fun l h e => hq (by rw [e] at h; exact h)) hm1'.2.2.1 hs2, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := hz z
    simp only [Res.add_apply]; omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1229 privStoreAt
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem privStoreAtB {g : G} {E : TEnv} {s : St} {HP Rv : Res} {a : Address} {c : Cell} {us : List Acc}
    {ws : List Word} {U : Ty} {k : Promises.Knobs} {arch : Arch} {pw : Word} {rel : Bool}
    (hm : MemInvB g E s) (hH : MemHeldPB E s HP) (hsto : E.sto a.label = some c) (hat : AtOff c.ty a.offset U)
    (hini : Priv E a.label → IniAt E.rc c a U) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hU : EnvValRB E U ws Rv) (hwU : wc U = some (nWords us)) (hlen : ws.length = nWords us) :
    ∀ s', s' ∈ storeUnits k arch pw a rel us ws 0 s →
      ∃ HP', MemHeldPB E s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + Rv (.own y) := by
  intro s' hs'
  by_cases hq : Priv E a.label
  · obtain ⟨c0, h0, hown⟩ := hq.1
    rw [hsto] at h0; cases h0
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := heldStoreAtPB hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) hat (hini hq) hna hU hwU hlen
    refine ⟨R2 + H0, hput k arch pw rel _ rfl rfl (LoadCoh_of_eqB hm.2.1 rfl) (fun _ => Nat.le_refl _)
      hm.2.2.2.2.1 s' hs', fun y => ?_⟩
    have h2 := congrArg (fun R : Res => R (.own y)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · exact ⟨HP, memHeldOn_storeB hH (fun l h e => hq (by rw [e] at h; exact h)) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1249 wordValR
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wordValRB {η : TEnv} {n : Nat} {P : Proto} {w : Word} {R : Res}
    (hv : VRRB (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [w] R)
    (hV : Valid (.word (.lit n) P) [w]) : EnvValRB (CE η) (.word (.lit n) P) [w] R :=
  ⟨VRR_monoB _ (CE (CE η).unsee) (CE η) _ _ _ _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
    (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) hv, hV⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1257 k2_wordFin
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_wordFinB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {e : Expr}
    {pw w : Word} {A : Address} {n : Nat} {P : Proto} {Rf Rs HP Tf Rv : Res} {z : AllocLabel}
    (hkey : tstep g mem pairs th = (storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s'))
    (hnb : ∀ E1, BumpIf th E1)
    (hmi : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th) → MemInvB g (CE η) s')
    (hHP : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th) →
      ∃ HP', MemHeldPB (CE η) s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + (Rv + wdW P n) (.own y))
    (hv : VRRB (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [w] (Rv + wdW P n))
    (hfr : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .unit, []) :: th.env) Tf) (hle : Tf + Rv ≤ Rf)
    (hE : EnvOKB p η) (he : TypedK p η c' e) (htv' : TvOK c') (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hkey]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hz := TermBlkZ.Flat.VRR_own_zeroB z (.word (.lit n) P) [] (CE (CE η).unsee) (fun _ => 0) _ [w] _ (by simp [Ty.noOwnIn]) (fun _ _ _ _ h => h.elim)
    (fun _ _ _ _ h => h.elim) hv
  refine stepC_ownB hnb ⟨ρ, η, c', Tf, Rs, rfl, hE, he, htv', hfr, rfl, hRPc, hDy.wit rfl⟩ (hmi s' hs') (hHP s' hs') ?_ hni hx
  have h1 := own_le hle z
  rw [hz]; omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1281 k2_storeWordPtr
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordPtrB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hr : EqI c₁ r r') (hj : IntIdx c₁ v j)
    (hst : InState c₁ P j c₂ k') (hcl : P.clauses[c₂]? = some cl') (hxt : StoreKind xt r' P j cl')
    (hb : c₁.bind x xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi.1
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hcellW : ∀ {lab : AllocLabel} {c : Cell}, Fd c.ty (cl ρ η.wit 0 0 (.word r P)) →
      c.ty = .word (.lit (ev ρ r)) P := fun hcty => by
    have h' := hcty; simp only [cl, clI_zero] at h'; exact Fd_word_eq h'
  have hpwf := wordRef_pwfB hpk (Or.inl rfl) hμ hi.1 hE htv hm
  rcases hμ with rfl | rfl
  · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, -, hown, hsku, -⟩ := ownPtr_viewB hi.1 hpk htv ho
    have hct := hcellW (lab := lab) hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs, hg]))
    obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
      storeWord_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
    have husA : accs c.ty = some [Acc.one] := by rw [hct]; simp [accs, hg]
    have hus' : wc c.ty = some (nWords [Acc.one]) := by rw [hct]; simp [wc, accs, hg]
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    exact k2_wordFinB (hDy := hDy.letW hterm rfl) key (bumpIf_nb hterm) (fun s' hs' => MemInv_storeB hm hsto hown husA hval rfl s' hs')
      (privStoreAtB hm hH hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h)
        (fun N e h => by cases h) (wordValRB (hvR _ _) (by rw [← hct]; exact hval.2)) (by simp [wc, accs, hg]) rfl) (hvR _ _) hfr hle hE he htv' hni hx hRPc
  · obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, -, hsku, -⟩ := pubPtr_viewB hi.1 hpk htv ho
    have hct := hcellW (lab := lab) hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs, hg]))
    obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
      storeWord_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
    have husc : accs c.ty = some [.one] := by rw [hct]; simp [accs, hg]
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    refine k2_wordFinB (hDy := hDy.letW hterm rfl) key (bumpIf_nb hterm) (fun s' hs' => ?_)
      (privStoreAtB hm hH hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h)
        (fun N e h => by cases h) (wordValRB (hvR _ _) (by rw [← hct]; exact hval.2)) (by simp [wc, accs, hg]) rfl) (hvR _ _) hfr hle hE he htv' hni hx hRPc
    by_cases hown : c.owner = some η.tid
    · exact MemInv_storeFB hm hsto hown husc hval rfl s' hs'
    · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
      exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc rfl s' hs'
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1343 k2_storeWordLocC
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordLocCB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hr : EqI c₁ r r') (hj : IntIdx c₁ v j)
    (hst : InState c₁ P j c₂ k') (hcl : P.clauses[c₂]? = some cl') (hxt : StoreKind xt r' P j cl')
    (hb : c₁.bind x xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hi0 := hi.1
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi0
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
  have hcell : cellOf (Ty.loc μ (.word r P)) = some (μ, .word r P) := by simp [cellOf]
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ := cell_targetB (bkG := False) hcell (Fd_noarr (by rw [hus1]; simp)) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, -⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs (.word r P))) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hlr := pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk hcell ho hea rfl
  have hus : accs ru = some [.one] := by rw [hlr, hus1]
  have hat' : AtOff c.ty ad.offset (.word (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero] using hat
  have hpwf := wordRef_pwfB hpk (Or.inr rfl) hμ hi.1 hE htv hm
  obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
    storeWord_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
  have hval := storeWord_valB (η := η) (r := r) hpwf hi1.1 hst hwv
  have hna : ∀ N e, cl ρ η.wit 0 0 (.word r P) ≠ .array (.lit N) e := fun N e h => by simp [cl] at h
  have hwUA : accs (cl ρ η.wit 0 0 (.word r P)) = some [Acc.one] := hus1
  have hwU : wc (cl ρ η.wit 0 0 (.word r P)) = some (nWords [Acc.one]) := by simp [wc, hus1]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  refine k2_wordFinB (hDy := hDy.letW hterm rfl) key (bumpIf_nb hterm) (fun s' hs' => ?_) (privStoreAtB hm hH hsto hat' (fun hq => by
      rcases hμ with rfl | rfl
      · have h4 : IniAt η.rc c ad (.word (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero, modeIni_own_rc] using hini
        exact h4
      · simp only [ModeOKF, ModeOKb] at hmode
        obtain ⟨f, hf, -⟩ := hmode
        have h3 : η.pfr ad.label = none := hq.2
        rw [hf] at h3; cases h3) (fun N e h => by cases h)
    (wordValRB (hvR _ _) (by simpa only [cl, clI_zero] using hval.2)) (by simp [wc, accs, hg]) rfl)
    (hvR _ _) hfr hle hE he htv' hni hx hRPc
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtIB hm hsto hown hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hna hval hwUA rfl s' hs'
  · have hpub : μ = .pub := by
      rcases hμ with rfl | rfl
      · exact absurd hmode hown
      · rfl
    subst hpub
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval hus1 rfl s' hs'
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1406 k2_storeWord
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtrB (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordHand hp hw hu hr hj _ _ hst hcl _ _ hh _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtrB (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inl ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordKeep hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtrB (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inr ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1441 k2_storeWordLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocCB (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordHand hp hw hu hr hj _ _ hst hcl _ _ hh _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocCB (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inl ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordKeep hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocCB (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inr ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1476 k2_storeWordGhost
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordGhostB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  obtain ⟨rt, pw, b, μ', ru, hea, hc, hab, hus⟩ := ghostRefKB hpk ht hμ hg hi.1 hE htv
  have hnw : wordOf t ≠ none := by rcases ht with rfl | rfl <;> simp [wordOf]
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  have fin : ∀ {Tf : Res}, FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .unit, []) :: th.env) Tf →
      Tf ≤ Rf → (∃ rv w, evalAt th.env v = some (rv, [w])) →
      ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
    intro Tf hfr hle hevx
    obtain ⟨rv, w, hev⟩ := hevx
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .unit, []) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hea, hev, hc, hab, hus, storeUnits, List.map]
    rw [key]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨Tf + Rs, HP, ⟨ρ, η, c', Tf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm, hH, hni, hx, ?_,
      anchStep_eqsB rfl rfl⟩
    have h1 := (Res.le_def.1 hle) (.own z)
    simp only [Res.add_apply] at h1 ⊢
    omega
  have hL := RLink_ofB hE.2.1 hE.2.2
  cases hop with
  | storeOwn hp hnw' | storePub hp hnw' | storeRgn hp hnw' | storeCap hp hnw' =>
    exfalso; rw [hpk] at hp; cases hp; exact hnw hnw'
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    obtain ⟨-, -, Rt, Rr, -, -, -, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have hfr := bindRB hb hi1 hL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    exact fin hfr (Res.le_def.2 fun k => by
      have := (Res.le_def.1 hle) k; simp only [Res.add_apply] at this; omega) ⟨rv, w, hev⟩
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    obtain ⟨-, -, Rt, Rr, -, -, -, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have hfr := bindRB hb hi1 hL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    exact fin hfr (Res.le_def.2 fun k => by
      have := (Res.le_def.1 hle) k; simp only [Res.add_apply] at this; omega) ⟨rv, w, hev⟩
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    obtain ⟨rt0, ws0, Rt, Rr, hev0, hv0, hl0, hvt, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    simp only [VRRB] at hvt
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have hfr := bindRB (R := Rt) (rt := .unit) (ws := []) hb hi1 hL (by simp only [VRRB]; exact hvt) (tok_Lay _ _ _ _)
    exact fin hfr (by rw [Res.add_comm]; exact hle) ⟨rv, w, hev⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1544 k2_storeWordAny
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordAnyB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  cases hg : P.ghost
  · rcases ht with rfl | rfl
    · exact k2_storeWordB (hDy := hDy) hterm hP hpk hμ hg hT hCk hi hE htv hm hH hni hx hRP
    · exact k2_storeWordLocB (hDy := hDy) hterm hP hpk hμ hg hT hCk hi hE htv hm hH hni hx hRP
  · exact k2_storeWordGhostB (hDy := hDy) hterm hP hpk ht hμ hg hT hCk hi hE htv hm hH hni hx hRP hPS
end
end TermOwnK2.Flat

-- ♭ mirror of W TermOwnK2 k2_isTy.
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_isTyB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {τ : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.isTy a τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : (CE η).sto z ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKB p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | isTy hpk hsl hwf htg _ hb =>
  obtain ⟨rt, ws, hea, hvr0, hlay0⟩ := peek_VRB (bkG := False) hi.1.2.1 hpk
  obtain ⟨pw, ad, cl0, hlast, hpv, ho, hsto, hmo, hacc⟩ := slot_wordB hsl hvr0 hlay0.2.2.1
  obtain ⟨w, hw, hk⟩ := isTy_key (g := g) (mem := mem) (pairs := pairs) hterm hea hlast hpv (close_wf0 th.σs hwf)
  rw [hk]
  intro r0 hr
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : VRRB ρ η (.ptrOpt .pub τ) (shp (.ptrOpt .pub (close th.σs τ))) [w] (ownW .pub [w]) :=
    ⟨isTy_valB htg hTy hpv ho hsto hmo hacc hw, rfl⟩
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvr (isTy_lay (isTy_null_or hpv hw))
  rw [ownW_pub, Res.add_zero] at hfr
  exact stepC_keepB (s' := stOf mem pairs th)
    ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm hH rfl rfl hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1563 finvK2
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem finvK2B {p : Prog} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rs Rf : Res}
    (htv : TvOK cx) (hi : FInvRB glb gnum gi ρ η th.σs (ResumeRB glb gnum gi p th.stack Rs) cx th.env Rf) :
    FInvB glb gnum gi ρ η th.σs (ResumeB glb gnum gi p th.stack) cx th.env :=
  FInvR_FInvB (htv.2.2.2.2.2.2.2)
    (fun E rd ws R h => ResumeR_ResumeB (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hi
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1570 ownXStep_k2
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k2B [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} [ProgRetIall p]
    (hP : ProgT p) (hPS : PwSkel) : ∀ n, OwnXStepPkgB p k arch i x n 2 := fun n =>
  ownXStepPkg_of_localB (ownXStepL_ofB (fun g mem pairs th r ρ η cx Rf Rs HP _ _ hq hsc hE hT htv hi hRP hDy hm hH _ hni hxz
      hTyE hRc hr hpa _ => by
    have hq : exprPkg th.term = 2 := hq
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [h] at hq; simp [exprPkg, opPkg] at hq) hTyE hRc)
    have hsd := hsc ρ η cx hE hT.1 htv (finvK2B htv hi)
    have hT0 := hT.1
    generalize ht : th.term = t0 at hT0 hsd hq
    have hsc' : StepScope cx t0 := by
      rcases hsd with h | ⟨-, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals (subst h; simp [exprPkg, opPkg] at hq)
    cases hT0 with
    | let_ hop _ =>
      cases hop with
      | loadWord hpk hw =>
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact k2_loadWordOwnB (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | pub => exact k2_loadWordPubB (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | rgn r' => exact ((hsc' _ hpk) r' _ rfl).elim
        · cases μ with
          | own => exact k2_loadWordLocB (hDy := hDy) ht hP hpk (.inl rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | pub => exact k2_loadWordLocB (hDy := hDy) ht hP hpk (.inr rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | rgn r' => exact ((hsc' _ hpk) r' _ rfl).elim
      | storeWordGive hpk hw | storeWordKeep hpk hw | storeWordHand hpk hw =>
        obtain ⟨μ, hteq⟩ := wordOf_cases hw
        cases μ with
        | own => exact k2_storeWordAnyB (hDy := hDy) ht hP hpk hteq (.inl rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        | pub => exact k2_storeWordAnyB (hDy := hDy) ht hP hpk hteq (.inr rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        | rgn r' => rcases hteq with rfl | rfl <;> exact ((hsc' _ hpk) r' _ rfl).elim
      | loadRgn hpk _ hc | loadCap hpk _ hc | loadTorn hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
      | storeRgn hpk _ hc | storeCap hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
      | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_loadOwnB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        · exact k2_loadLocB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_loadPubB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        · exact k2_loadPubLocB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | storeOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_storeOwnB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        · exact k2_storeLocB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
      | storePub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_storePubB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        · exact k2_storePubLocB (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
      | xchg hpk hx =>
        cases hx with
        | own _ hc =>
          rcases cell_cases hc with rfl | rfl
          · exact k2_xchgOwnB (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          · exact k2_xchgLocB (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        | rgn _ hc => exact absurd hc (hsc' _ hpk _ _)
      | loadAt => exact k2_loadAtB (hDy := hDy) ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | loadAtF => exact k2_loadAtFB (hDy := hDy) ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | isTy => exact k2_isTyB (hDy := hDy) ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS hTyE r hr
      | _ => simp [exprPkg, opPkg] at hq
    | _ => simp [exprPkg] at hq))
end
end TermOwnK2.Flat

-- PORTB TermOwnK3.lean:23 oldValF
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem oldValFB {ρ : Nat → Nat} {η : TEnv} {u ru T : Ty} {o : Nat} {ws : List Word}
    (hco : CohBW η) (hcr : CohRB η) (hni : noIallV T = true) (hno : Ty.noOwnIn [] T = true)
    (hat : AtOff T o (cl ρ η.wit 0 0 u)) (hv : (VRF False) ρ η u (shp ru) ws) :
    ∃ R, VRRB ρ η u (shp ru) ws R ∧ ∀ l, R (.own l) = 0 := by
  have hc := (VR_closeB hco ρ u [] 0 ρ (fun _ => 0) (shp ru) ws (fun _ => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨R, hR⟩ := VR_VRRB _ (TermIall.noIallV_AtOff hat hni) (RInvZ_CE η) hc
  exact ⟨R, (VRR_closeB hco hcr ρ u [] 0 ρ (fun _ => 0) (shp ru) ws R (fun _ => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).2 hR,
    fun l => TermBlkZ.Flat.VRR_own_zeroB l _ [] (CE η) _ _ _ R (noOwn_AtOff hat hno)
      (fun _ _ _ _ h => (h : False).elim) (fun _ _ _ _ h => (h : False).elim) hR⟩
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:43 stepK3_ldl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_ldlB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.ldl b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk hb =>
  obtain ⟨t, u, n, k, j, q, hp, hbuf, hlo, hint, hlt, hltk, hb⟩ : ∃ t u n k j q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧ cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).filterMap
        fun (s1, old) => (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (ev ρ j % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hni, addrOf, hwv, hbe, lanesOf]
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv',
    bindR0B hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _) trivial, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1),
    memHeldOn_eqsB hH f1 f4, hnie, hx, Nat.le_refl _, anchStep_sameB (bumpIf_nb hterm)⟩
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:115 stepK3_ldlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_ldlwB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.ldlw b wi jl) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk hpj hij hb =>
  obtain ⟨t, u, n, k, jw, tj, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩ : ∃ t u n k jw tj q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi0.2.1 hpj hoj
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).filterMap fun (s1, old) =>
        (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (m % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hni, hnj, addrOf, hwv, hbe, lanesOf]
  
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv',
    bindR0B hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _) trivial, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1),
    memHeldOn_eqsB hH f1 f4, hnie, hx, Nat.le_refl _, anchStep_sameB (bumpIf_nb hterm)⟩
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:188 stepK3_xchgAt
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_xchgAtB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.xchgAt b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, n, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x u = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    obtain ⟨Ro, hvold, hRo⟩ := oldValFB hE.2.1 hE.2.2 (hnie _ _ hsto) (MemInv_noOwnTB hm hsto hpfN) hat hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + Ro + Rs, HP, ⟨ρ, η, c', Rr + Ro, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us))) hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ j * nWords us)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := hle (.own xl)
    have h3 := hRo xl
    simp only [Res.add_apply] at h1 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hown hpfN)
  obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput0⟩ := heldStoreAtPB (a := offs ad (ev ρ j * nWords us)) hm hH (Priv_of hsto hown hpfN) hsto hown hnv (OwnOKPF_cellPB hm.2.1 hsto hown hpfN) hat hini hna hvalR hwU hlen
  have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
  have hvold := oldValRB hE.2.1 hE.2.2 hsig (VRR_upB _ _ _ _ _ hWold hvqR)
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
  refine ⟨Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us))) hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
    hput0 g.k g.arch w false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h1 := hle (.own xl)
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply] at h1 h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:280 stepK3_xchgAtF
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_xchgAtFB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {q : List Nat} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, c, n, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u c n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c ∧ c₁.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, hiniF⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hiniC := hiniF o _ hato
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨cs, hcs, -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat' hiniC hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco))
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsgc hcs
  have hwUA : accs (cl ρ η.wit 0 0 c) = some cs := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco)).symm.trans hcs
  have hwU : wc (cl ρ η.wit 0 0 c) = some (nWords cs) := by rw [← wc_of_sig hsgc]; simp [wc, hcs]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    obtain ⟨Ro, hvold, hRo⟩ := oldValFB hE.2.1 hE.2.2 (hnie _ _ hsto) (MemInv_noOwnTB hm hsto hpfN) hat' hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + Ro + Rs, HP, ⟨ρ, η, c', Rr + Ro, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us + o))) hm1' hsto hown hat' hiniC hna hval hwUA hlen s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ j * nWords us + o)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := hle (.own xl)
    have h3 := hRo xl
    simp only [Res.add_apply] at h1 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hown hpfN)
  obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput0⟩ :=
    heldStoreAtPB (a := offs ad (ev ρ j * nWords us + o)) hm hH (Priv_of hsto hown hpfN) hsto hown hnv (OwnOKPF_cellPB hm.2.1 hsto hown hpfN) hat' hiniC hna hvalR hwU hlen
  have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
  have hvold := oldValRB hE.2.1 hE.2.2 hsgc (VRR_upB _ _ _ _ _ hWold hvqR)
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
  refine ⟨Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us + o))) hm1' hsto hown hat' hiniC hna hval hwUA hlen s2 hs2,
    hput0 g.k g.arch w false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h1 := hle (.own xl)
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply] at h1 h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:379 stepK3_stlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_stlwB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk hpj hij hpv hfx hb =>
  obtain ⟨t, u, n, k, jw, tj, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩ :
      ∃ t u n k jw tj tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi0.2.1 hpj hoj
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi0.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ jw)) false [.one]
            [cst (.num (setLaneN w y (m % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hev, hni, hnj, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨-, -, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    refine ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := offs ad (ev ρ jw)) hm1' hsto hmode hat hini hna
        (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ jw)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    simp only [Res.add_apply]
    omega
  | none =>
  have hnvP := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput0⟩ := heldStoreAtPB (a := offs ad (ev ρ jw)) hm hH (Priv_of hsto hmode hpfN) hsto hmode hnvP (OwnOKPF_cellPB hm.2.1 hsto hmode hpfN) hat hini hna
    (lanes_EnvValRB sg w (setLaneN w y (m % w.lanes) yv)) hwU (by simp [nWords, Acc.size])
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine ⟨Rf + Rs, R2 + H0, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ jw)) hm1' hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
    hput0 g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply, Res.zero_apply] at h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:494 stepK3_stl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_stlB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.stl b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stl hp hbuf hlo hint hlt hltk hpv hfx hb =>
  obtain ⟨t, u, n, k, j, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩ : ∃ t u n k j tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0 hlt hltk
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi0.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one]
            [cst (.num (setLaneN w y (ev ρ j % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hni, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨-, -, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    refine ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := offs ad (ev ρ j / w.lanes)) hm1' hsto hmode hat hini hna
        (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ j / w.lanes)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    simp only [Res.add_apply]
    omega
  | none =>
  have hnvP := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput0⟩ := heldStoreAtPB (a := offs ad (ev ρ j / w.lanes)) hm hH (Priv_of hsto hmode hpfN) hsto hmode hnvP (OwnOKPF_cellPB hm.2.1 hsto hmode hpfN)
    hat hini hna (lanes_EnvValRB sg w (setLaneN w y (ev ρ j % w.lanes) yv)) hwU (by simp [nWords, Acc.size])
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine ⟨Rf + Rs, R2 + H0, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j / w.lanes)) hm1' hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
    hput0 g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply, Res.zero_apply] at h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:609 heldBufInitP
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem heldBufInitPB {Q : AllocLabel → Prop} {g : G} {E E' : TEnv} {s : St} {H : Res} {ad : Address} {c : Cell} {N j : Nat} {e : Ty}
    {us : List Acc} {ws : List Word} {pw : Word} {Rv : Res}
    (hm : MemInvB g E s) (hH : MemHeldOnB Q E s H) (hql : Q ad.label) (hsto : E.sto ad.label = some c) (_hown : c.owner = some E.tid)
    (hnv : NVP E s ad.label)
    (hcP : ∃ vals, CellOKB E (E.rc ad.label) c.ty vals ∧
      ∀ o v, vals[o]? = some v → LatestP s.mem s.promises s.vs.coh ⟨ad.label, o⟩ v)
    (hat : AtOff c.ty ad.offset (.array (.lit N) e)) (hini : IniAt E.ini c ad (.array (.lit N) e))
    (hwe : wc e = some (nWords us)) (hj : j < N) (hjn : j ≤ E.ini ad.label)
    (hq : EnvValRB E e ws Rv) (hlen : ws.length = nWords us)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto)
    (hil : E'.ini ad.label = max (E.ini ad.label) (j + 1)) (hio : ∀ l', l' ≠ ad.label → E'.ini l' = E.ini l')
    (hpf : E'.pfr = E.pfr) (hbx : ∀ l B, E.box l = some B → E'.box l = some B)
    (hq' : ∀ o, ¬ PredU E' ⟨ad.label, o⟩) (hrio : ∀ l', l' ≠ ad.label → E'.rini l' = E.rini l')
    (hjr : j ≤ E.rc ad.label) (hrc' : E'.rc ad.label = max (E.rc ad.label) (j + 1))
    (hfp : E'.fp = E.fp := by first | rfl | assumption)
    (hri : ∀ l, E.rini l ≤ E'.rini l := by rini_le) :
    ∃ H2, H2 ≤ Rv + H ∧
      ∀ s', s' ∈ storeUnits g.k g.arch pw (offs ad (j * nWords us)) false us ws 0 s → MemHeldOnB Q E' s' H2 := by
  obtain ⟨vals, hcell, hlat⟩ := hcP
  obtain ⟨valsm, hW, hP⟩ := own_msgWordsN (E := E) hnv vals hlat
  obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focusB hH hql
  have hcR : CellOKRB E (E.ini ad.label) (E.rc ad.label) c.ty valsm R0 :=
    HeldEntry_cellB hent0 hsto hcell hW.length.symm (fun o w h => (hP o w h).2)
  obtain ⟨N', e', usB, Rl, hT, husB, hn, hvl, hRl, hR, hslots⟩ : BufOKRB E (E.ini ad.label) (E.rc ad.label) c.ty valsm R0 := by
    rcases hcR with ⟨hwc, hv⟩ | hb
    · exfalso
      obtain ⟨n', _, _, hwn, -⟩ := VRR_atB E.unsee hat hv.1 hwc
      simp [wc, accs] at hwn
    · exact hb
  have hoff : ad.offset = 0 := by
    rcases hini N' e' hT with ⟨hUc, h0⟩ | ⟨us', j', o, hus', -, -, hato⟩
    · exact h0.symm
    · exact (accs_AtOff hato (by rw [hus']; simp) (by simp [accs])).elim
  have hUc : Ty.array (.lit N) e = c.ty := by
    rcases hini N' e' hT with ⟨hUc, -⟩ | ⟨us', j', o, hus', -, -, hato⟩
    · exact hUc
    · exact (accs_AtOff hato (by rw [hus']; simp) (by simp [accs])).elim
  have hb0 : BufOKRB E (E.ini ad.label) (E.rc ad.label) (.array (.lit N) e) valsm R0 := by
    rw [hUc]; exact ⟨N', e', usB, Rl, hT, husB, hn, hvl, hRl, hR, hslots⟩
  rw [hT] at hUc
  simp only [Ty.array.injEq, Idx.lit.injEq] at hUc
  obtain ⟨hN, he⟩ := hUc
  subst hN; subst he
  have hnu : nWords usB = nWords us := by rw [wc_of_accs husB] at hwe; exact Option.some.inj hwe
  have hst := hq.store hm.2.2.2.2.1
  obtain ⟨R', hR'le, hb'⟩ := BufOKR_putB hb0 husB hj hjn hjr hst (by rw [List.length_map, hlen, hnu])
  rw [hnu, ← hil, ← hrc'] at hb'
  refine ⟨R' + H0, Res.le_def.2 fun k => ?_, fun s' hs' => ?_⟩
  · have h1 := hR'le k
    simp only [Res.add_apply] at h1 ⊢; omega
  have had : offs ad (j * nWords us) = ⟨ad.label, j * nWords us⟩ := by
    simp only [offs, hoff, Nat.zero_add]
  rw [had] at hs'
  obtain ⟨g2, g3⟩ := storeUnits_latP (a := ⟨ad.label, j * nWords us⟩) us ws 0 s s.vs.vRelSt hm.2.2.1
    hm.2.2.2.2.2.2.2.2.2.2.1 (Nat.le_refl _) s' hs'
  have hlenv : j * nWords us + nWords us ≤ valsm.length := by
    have hm := Nat.mul_le_mul_right (nWords us) (show j + 1 ≤ N by omega)
    rw [Nat.succ_mul] at hm; rw [hvl, hnu]; omega
  have htail : ∀ i : Nat, i < nWords us → TailP s (offs ⟨ad.label, j * nWords us⟩ (0 + i)) := fun i hi => by
    have hlt : j * nWords us + i < vals.length := by have := hW.length; omega
    have hv := hlat (j * nWords us + i) (vals[j * nWords us + i]'hlt) (List.getElem?_eq_getElem hlt)
    have e : offs ⟨ad.label, j * nWords us⟩ (0 + i) = ⟨ad.label, j * nWords us + i⟩ := by simp [offs]
    rw [e]; exact fun t m ht hm hl => hv.2.2 t m ht hm hl
  have hlat' := splice_latestP (a := ⟨ad.label, j * nWords us⟩) hlen hlenv (fun o v h => (hP o v h).1)
    (g2 htail) g3
  have hsto' : E'.sto ad.label = some c := by rw [hs]; exact hsto
  have hile : ∀ l', E.ini l' ≤ E'.ini l' := fun l' => by
    by_cases h : l' = ad.label
    · subst h; rw [hil]; exact Nat.le_max_left _ _
    · rw [hio l' h]; exact Nat.le_refl _
  have hmono : ∀ {U : Ty} {vs : List Word} {Rq : Res}, ValOfRB E U vs Rq → ValOfRB E' U vs Rq :=
    fun h => ValOfR_monoB hp ht (fun l c h => by rw [hs]; exact h) hile h (fun l f h => by rw [hpf]; exact h) hbx
  have hent : HeldEntryB E' s' ad.label R' :=
    HeldEntry_ownNB hsto' (NVP_env (NVP_store hnv hm.2.2.1 hs')
      (fun o h => (VisU_congr (by rw [hs]) ht.symm (by rw [hpf])).1 h)
      (fun h => (Vis_congr (by rw [hs]) ht.symm (by rw [hpf])).1 h) hfp hq') hlat' (Or.inr (by rw [hT]; exact BufOKR_mapB hmono hb'))
  have hX' := memHeldOn_trB (Q' := fun l' => Q l' ∧ l' ≠ ad.label) (E' := E') (s' := s') hX (fun _ => Iff.rfl)
    (fun l' _ => by rw [hs]) (fun l' h => hio l' h.2) (fun l' h => hrio l' h.2) (fun l' _ => by rw [hpf]) ht.symm hfp
    (fun l' h o w hl => LatestNP_growsAtF (storeUnits_growsF us ws 0 s s' hs').1
      (storeUnits_growsF us ws 0 s s' hs').2.1 (storeUnits_fulL hm.2.2.1 hs') h.2 hl) hmono
  exact memHeldOn_unfocusB hX' hent hql
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:693 heldBufInitF
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem heldBufInitFB {g : G} {E E' : TEnv} {s s' : St} {H : Res} {ad : Address} {f : Ts}
    {k : Promises.Knobs} {arch : Arch} {pw : Word} {o : Nat} {us : List Acc} {ws : List Word}
    (hm : MemInvB g E s) (hH : MemHeldPB E s H) (hf : E.pfr ad.label = some f)
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hs : E'.sto = E.sto)
    (hio : ∀ l', l' ≠ ad.label → E'.ini l' = E.ini l') (hrio : ∀ l', l' ≠ ad.label → E'.rini l' = E.rini l')
    (hpf : E'.pfr = E.pfr) (hbx : ∀ l B, E.box l = some B → E'.box l = some B) (hfp : E'.fp = E.fp)
    (hile : ∀ l, E.ini l ≤ E'.ini l) (hri : ∀ l, E.rini l ≤ E'.rini l)
    (hs' : s' ∈ storeUnits k arch pw (offs ad o) false us ws 0 s) : MemHeldPB E' s' H := by
  have hQ : ∀ l, Priv E' l ↔ Priv E l := fun l => by
    unfold Priv OwnL; rw [hs, hpf, ht]
  exact memHeldOn_trB (Q' := Priv E') (E' := E') (s' := s') hH hQ
    (fun l' _ => by rw [hs]) (fun l' h => hio l' (fun e => privOff h e hf))
    (fun l' h => hrio l' (fun e => privOff h e hf)) (fun l' _ => by rw [hpf]) ht.symm hfp
    (fun l' h o w hl => LatestNP_growsAtF (storeUnits_growsF us ws 0 s s' hs').1
      (storeUnits_growsF us ws 0 s s' hs').2.1 (storeUnits_fulL hm.2.2.1 hs')
      (fun e => privOff (a := ad) h (e.trans rfl) hf) hl)
    (fun h => ValOfR_monoB hp ht (fun l c h => by rw [hs]; exact h) hile h (fun l f h => by rw [hpf]; exact h) hbx hri)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:712 stepK3_bufInit
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_bufInitB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hxl : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hTyE : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t, tv, u, n, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t tv u n k j c₁ c₂,
      cx.use b = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨rb, wsb, Rb, Rr1, hea, hvb, hlb, hvrb, hi1, hle1⟩ := useRB (bkG := False) hu hi hE.2.2
  have hRb := VRR_buf_RB hbuf hvrb
  obtain ⟨rv, wsv, Rv, Rr2, hev, hvv, hlv, hvrv, hi2, hle2⟩ := useRB (bkG := False) hu2 hi1 hE.2.2
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1.1
  have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hi1.1.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hvb0 := hvb
  simp only [VRF, VRb2] at hvb
  obtain ⟨hv, hir, -⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmode, hini0⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  have hKi : ev ρ k ≤ η.ini ad.label := by
    simp only [IniR] at hir; exact Nat.le_trans (hir ad (by simp [hwv])) (TEnv.selIni_le_ini _ _ _)
  have hKm : ev ρ k ≤ η.rc ad.label := by
    simp only [IniR] at hir; have h := hir ad (by simp [hwv]); rw [TEnv.selIni_loc] at h; exact h
  have hat := hat0
  have hini := hini0
  simp only [cl, clI_zero] at hat hini
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hweA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 ho htb1 (buf_lyt hlb.2.2.2.2 rfl).2).symm.trans hus
  have hwe : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨hval, hlen⟩ :=
    ownStoreValB (cx := c₁) hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1 hvv hlv hsig hus
  have hvalR := storeValRB (cx := c₁) hE.2.1 hE.2.2 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1
    hvrv hlv hval.2
  let ini' := bumpIni η.ini ad.label (ev ρ j + 1)
  let rini' := bumpIni η.rini ad.label (ev ρ j + 1)
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  have hile : ∀ l, η.ini l ≤ ini' l := bumpIni_le η.ini ad.label (ev ρ j + 1)
  have hx : ExtB η (η.withStoB η.sto ini' (Ri := rini')) := Ext_withStoB hE.2.1 (fun l c h => h) hile (Ri := rini') (hRi := hri')
  let rtR : Ty := Ty.refine (Ty.loc μr (Ty.array nr ur)) (Pred.ini (Idx.lit (ev ρ j + 1)))
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, rtR, [w]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, numOf, hwi, addrOf, hwv, bufElem, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpa
  have hk := tyOKE_keep (r := r) (by rw [key]; exact hr) (fun _ _ _ _ h => by rw [hterm] at h; cases h) hTyE hRc
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hvr : (VRF False) ρ (η.withStoB η.sto ini' (Ri := rini')) (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      (shp rtR) [w] := by
    have h1 := VR_extB hE.2.1 hx hvb0
    simp only [VRF, VRb2] at h1 ⊢
    refine ⟨h1.1, fun a ha => ?_, fun hp => absurd hp (by rintro ⟨_, _, h⟩; simp [pp] at h)⟩
    have hav : a = ad := by simp [hwv] at ha; exact ha.symm
    subst hav
    show ev ρ (.add k (.lit 1)) ≤ min (bumpIni η.ini a.label (ev ρ j + 1) a.label)
      (bumpIni η.rini a.label (ev ρ j + 1) a.label)
    rw [bumpIni_self, bumpIni_self]; simp [ev]; omega
  have hlay : Lay th.σs (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      rtR [w] := Lay_repred hlb
  have hE' : EnvOKB p (η.withStoB η.sto ini' (Ri := rini')) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  have hfr := bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi2) (RLink_ofB hE'.2.1 hE'.2.2) (VRR_ofVR_reflocWB hvr) hlay
  rw [← hRb] at hfr
  have hAS : ∀ s2, AnchStepB g th (CE η) (CE (η.withStoB η.sto ini' (Ri := rini'))) (stOf mem pairs th) s2 :=
    fun _ => anchStep_genB (ext_CEB hx)
      (bufBump hterm hea hwv hei (by simp [numOf, hwi])
        (show ev ρ j + 1 ≤ bumpIni η.ini ad.label (ev ρ j + 1) ad.label by rw [bumpIni_self]; exact Nat.le_max_right _ _)
        (show ev ρ j + 1 ≤ bumpIni η.rini ad.label (ev ρ j + 1) ad.label by rw [bumpIni_self]; exact Nat.le_max_right _ _))
      (fun _ _ h _ => h) (fun l _ => bumpIni_iniLe η.ini η.rini ad.label (ev ρ j + 1) l)
      (fun _ h0 hl => absurd h0 hl)
      (fun l _ => by
        by_cases hl : l = ad.label
        · exact Or.inr ⟨x, b, i, v, e, _, [w], ad, hterm, hea, by simp [hwv], hl.symm⟩
        · exact Or.inl (Nat.le_of_eq (bumpIni_other _ _ _ _ hl)))
      (fun h l => bumpIni_rle h l)
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    refine ⟨CE (η.withStoB η.sto ini' (Ri := rini')), Rr2 + Rb + Rs, HP,
      ⟨ρ, η.withStoB η.sto ini' (Ri := rini'), c', Rr2 + Rb, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
        (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
        (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
      heldBufInitFB (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hH hpfN rfl rfl rfl
        (fun l' h => bumpIni_other _ _ _ l' h) (fun l' h => bumpIni_other _ _ _ l' h) rfl (fun _ _ h => h) rfl
        hile hri' hs', hnie, hxl, ?_, hAS _, hk.1, hk.2⟩
    have h1 := hle1 (.own xl)
    have h2 := hle2 (.own xl)
    simp only [Res.add_apply] at h1 h2 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨H2, hH2, hput⟩ := heldBufInitPB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) (pw := w) (g := g)
    hm hH (Priv_of hsto hmode hpfN) hsto hmode hnv (OwnOKPF_cellPB hm.2.1 hsto hmode hpfN) hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hwe (by omega) (show ev ρ j ≤ η.ini ad.label by omega) hvalR hlen
    rfl rfl rfl (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl (fun _ _ h => h)
    (fun o hq => hnv.2.2 o (PredU_bump (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) (k := ev ρ j + 1) rfl rfl rfl (bumpIni_self _ _ _) (by
      show min (bumpIni η.ini ad.label (ev ρ j + 1) ad.label) (bumpIni η.rini ad.label (ev ρ j + 1) ad.label) =
        max (min (η.ini ad.label) (η.rini ad.label)) (ev ρ j + 1)
      rw [bumpIni_self, bumpIni_self]; omega) hq)) (fun l' h => bumpIni_other _ _ _ l' h)
    (show ev ρ j ≤ min (η.ini ad.label) (η.rini ad.label) by have h := hKm; unfold TEnv.rc at h; omega)
    (show min (bumpIni η.ini ad.label (ev ρ j + 1) ad.label) (bumpIni η.rini ad.label (ev ρ j + 1) ad.label) =
        max (min (η.ini ad.label) (η.rini ad.label)) (ev ρ j + 1) by
      rw [bumpIni_self, bumpIni_self]; omega)
  refine ⟨CE (η.withStoB η.sto ini' (Ri := rini')), Rr2 + Rb + Rs, H2,
    ⟨ρ, η.withStoB η.sto ini' (Ri := rini'), c', Rr2 + Rb, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
      (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
      (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
    hput s' hs', hnie, hxl, ?_, hAS _, hk.1, hk.2⟩
  have h1 := hle1 (.own xl)
  have h2 := hle2 (.own xl)
  have h3 := Res.le_def.1 hH2 (.own xl)
  simp only [Res.add_apply] at h1 h2 h3 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:870 stepK3_new
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_newB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hxl : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hpp : g.p = p) (hTyE : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | new hu _ hb =>
  obtain ⟨tv, c₁, hu, hb, htvT⟩ : ∃ tv c₁, cx.use a = .ok (tv, c₁) ∧ c₁.bind x (.ptr .own tv) = .ok c' ∧ some tv = _ :=
    ⟨_, _, hu, hb, rfl⟩
  have hi0 := hi.1
  obtain ⟨rt, ws, Rv, Rr, hea, hv, hl, hvr, hiR, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have ho : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 tv) := lay_closed hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb hl
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwcT : wc (cl ρ η.wit 0 0 tv) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvc : (VRF False) (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  have hvcR : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws Rv := by
    rw [← shp_of_sig hsig]
    exact (VRR_closeB hE.2.1 hE.2.2 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws Rv (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvr
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, -, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hX := memHeldOn_offB hH (l := freshLabel g.lbase g.n g.i th.nalloc) (fun h => by
    obtain ⟨⟨c0, hc0, -⟩, -⟩ := h; rw [hnone] at hc0; cases hc0)
  have hval : ValOfB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) (cl ρ η.wit 0 0 tv)
      (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) :=
    ValOf_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValB.store (η := CE η) ⟨hvc, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hvalR : ValOfRB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      (cl ρ η.wit 0 0 tv) (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) Rv :=
    ValOfR_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValRB.store (η := CE η) ⟨hvcR, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hx : ExtB η (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto) :=
    Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := CE η) hnone h) (fun _ => Nat.le_refl _)
  have key : ∀ r ∈ tstep g mem pairs th, ∃ s' pw,
      (s', pw) ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i th.nalloc) us ws (stOf mem pairs th) ∧
      ∃ tys, r = (s'.mem, s'.pairs,
        { withS { th with term := e, env := (x, .ptr .own rt, [pw]) :: th.env } s' with tys := tys }) := by
    intro r hr
    obtain ⟨s1, t1, ws1, hm1, tys, rfl⟩ := TermRun.tstep_new_mem hterm hr
    simp only [evalOp, hea, hus, List.mem_map] at hm1
    obtain ⟨⟨s2, pw⟩, hal, he⟩ := hm1
    cases he
    exact ⟨_, _, hal, tys, rfl⟩
  · intro r hr _
    obtain ⟨s', pw, hal, tys, rfl⟩ := key r hr
    obtain ⟨hmo', hoo', hpw⟩ := alloc_okPB hwcT hlen hval hfresh hnone hpl hpo.1 hpo.2.1 hpf0 hmo hoo ⟨s', pw⟩ hal
    obtain ⟨hg, hsubl, hna, hpl', hful⟩ := alloc_growsP hpl ⟨s', pw⟩ hal
    obtain ⟨hla1, -⟩ := alloc_latP (k := g.k) (arch := g.arch) (us := us) (ws := ws) hpl (MemInv_nodupB hm)
      ⟨s', pw⟩ hal
    obtain ⟨hwr, hhid⟩ := alloc_hidPB (s := stOf mem pairs th) hval
      (ShapeC_of_wc hwcT (by rw [List.length_map]; exact hlen))
      (by obtain ⟨_, h, -⟩ := wc_some hwcT; simp [h]) hfresh hpl ⟨s', pw⟩ hal
    simp only at hmo' hoo' hpw hg hsubl hna hwr hhid hla1 hpl' hful
    subst hpw
    have hwA : ∀ T o w, WordOKB (CE η) T o w →
        WordOKB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) T o w :=
      fun T o w h => WordOK_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _)
        (fun _ _ h' => h') (fun _ h' => h') h
    have hoh' : OwnHidPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem s'.vs
        s'.promises := by
      refine ⟨fun l c hc ho o hi => ?_, fun l c hc ho hlt => ?_⟩
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          rw [allocE_eq] at hc; cases hc; exact hhid o
        · rw [allocE_ne hl] at hc
          exact HiddenP_growsAtB (hoh.1 l c hc ho o hi) (hwA _ _) hwr hg hl hful
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
            (Nat.not_lt_zero _)
        · rw [allocE_ne hl] at hc
          obtain ⟨f, hf, hs, hH⟩ := hoh.2 l c hc ho hlt
          exact ⟨f, hf, fun hz => hs (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
            fun o hi => HiddenP_growsAtB (hH o hi) (hwA _ _) (Nat.le_refl _) hg hl hful⟩
    have hpd' : PubDefPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem
        s'.promises := by
      intro l c f hc hown hf o hi
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at hc; cases hc; exact (hown rfl).elim
      · rw [allocE_ne hl] at hc
        exact HiddenP_growsAtB (hpd l c f hc hown hf o hi) (hwA _ _) (Nat.le_refl _) hg hl hful
    have hpi' : PubInvB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      refine PubInv_growB (hbs := fun l hb h => by
          by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
          · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
          · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (alloc_pairs _ hal) hful rfl rfl (fun l c h => allocE_sub hnone h)
        (fun _ => Nat.le_refl _) rfl rfl (fun c h => by rw [allocE_eq] at h; rw [← Option.some.inj h]; rfl)
        (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
          (Nat.not_lt_zero _)) (hrcg := fun _ h => ⟨h, Nat.le_refl _⟩)
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl; exact Or.inr hpf0
        · rw [allocE_ne hl] at h; exact Or.inl h
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at h
        cases h
        refine Or.inr ?_
        rcases hseg with ⟨-, rfl, -⟩ | ⟨N, us0, j0, hT, -, -, -⟩
        · obtain ⟨vals, hcell, -⟩ := hoo' _ _ allocE_eq rfl
          rcases hcell with ⟨hwc, hv⟩ | hb
          · exact ⟨vals, hv, Option.some.inj (hwc.symm.trans (wc_of_accs hu'))⟩
          · obtain ⟨N, e0, us0, hT, -⟩ := hb
            exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
        · exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
      · rw [allocE_ne hl] at h; exact Or.inl ⟨h, hini⟩
    have hopub' : OwnPubV (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      intro l c f hc ho hf
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
      · rw [allocE_ne hl] at hc
        exact ((hopub.alloc hpl hal) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
          fun a ha hi c1 N1 e1 us1 h1 => hi c1 N1 e1 us1 (by rw [allocE_ne (fun e => hl (ha.symm.trans e))]; exact h1))
    
    have hfr' : FInvRB g.lbase g.n g.i ρ (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto)
        th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c'
        ((x, .ptr .own rt, [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env) (Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc))) := by
      refine bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hiR) (RLink_ofB hx.1 hx.2.2.2.2.2.2.2.2.2.2.1) ?_ ?_
      · simp only [VRRB]
        exact ⟨⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, ⟨cl ρ η.wit 0 0 tv, some η.tid⟩, by simp [cst, Promises.TVal.mk0], rfl,
          by simp [TEnv.withStoB, allocE, CE], .refl, by first | rfl | trivial,
          show accs (cl ρ η.wit 0 0 tv) ≠ none from fun h => by simp [wc, h] at hwcT⟩,
          (ownW_own_loc (a := ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩) (g := 0)
            (by simp [cst, Promises.TVal.mk0])).symm⟩
      · refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs],
          ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, by simp [cst, Promises.TVal.mk0]⟩, ?_⟩
        · show Ty.ptr (skelM .own) (etok (skel rt)) = Ty.ptr _ _
          rw [hl.2.1]; rfl
        · show Ty.ptr (modeC 0 .own) (etok (lyt 0 rt)) = Ty.ptr _ _
          rw [hl.2.2.2.2]; rfl
    
    have hent : HeldEntryB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'
        (freshLabel g.lbase g.n g.i th.nalloc) Rv := by
      refine HeldEntry_ownPB allocE_eq (PromAt_privL (Priv_of allocE_eq rfl hpf0)) (fun o v hov => ?_)
        (Or.inl ⟨by rw [List.length_map, hlen]; exact hwcT, hvalR⟩)
      rw [List.getElem?_map] at hov
      cases hw : ws[o]? with
      | none => rw [hw] at hov; cases hov
      | some w =>
        rw [hw] at hov
        simp only [Option.map_some, Option.some.injEq] at hov
        subst hov
        have ho' : o < ws.length := (List.getElem?_eq_some_iff.1 hw).1
        exact hla1 o w (by rw [← hlen]; exact ho') hw
    have hX' := memHeldOn_trB (Q' := fun l' => Priv (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) l' ∧
        l' ≠ freshLabel g.lbase g.n g.i th.nalloc) (s' := s') hX
      (fun l => ⟨fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne] at hc; exact hc, ho⟩, hp⟩, hne⟩,
        fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne]; exact hc, ho⟩, hp⟩, hne⟩⟩)
      (fun l' h => allocE_ne h.2) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
      (fun l' h o w hl => LatestNP_growsAtF hg (fun t h => hsubl.subset h) hful h.2 hl)
      (fun h => ValOfR_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _) h)
    have hxne : xl ≠ freshLabel g.lbase g.n g.i th.nalloc := fun e => hxl (by rw [e]; exact hnone)
    have hTR : ThInvREB g.lbase g.n g.i p (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        { withS { th with term := e, env := (x, .ptr .own rt, [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env } s' with tys := tys }
        (Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs) :=
      ⟨ρ, η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c',
          Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    have hNC : NewCellSto g ρ η th (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) := by
      intro x' a' T' e' h'
      rw [hterm] at h'
      obtain ⟨-, ⟨-, hT'⟩, -⟩ := (by simpa using h' : x = x' ∧ (a = a' ∧ _ = T') ∧ e = e')
      refine ⟨_, allocE_eq, ?_⟩
      show cl ρ η.wit 0 0 tv = cl ρ η.wit 0 0 T'
      rw [Option.some.inj htvT, hT']
    have hk := tyOKE_alloc hn hr (fun _ hl => allocE_ne hl) hTyE hRc
      (fun c t hc ht => TermStep.hnew_of hr hRc (by rw [hpp]; exact hDy) (fun k => (hE.2.1 k).1) hNC c t hc ht)
    refine ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv), Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Rv + HP,
        hTR, ?_,
        memHeldOn_unfocusB hX' hent (Priv_of allocE_eq rfl hpf0), fun l cl hcl => ?_,
        fun h => hxl (by rw [allocE_ne hxne] at h; exact h), ?_,
        anchStep_freshB (ext_CEB hx) (bumpIf_nb hterm (hop := by intro _ _ _ h; cases h) _) (fun _ hl => allocE_ne hl) hpf0 (fun _ _ => rfl) hnone
          (Priv_of allocE_eq rfl hpf0) (fun _ _ => rfl) (fun h => h _), hk.1, hk.2⟩
    · refine ⟨hmo', hoo', hpl', ⟨fun j hj => ?_, PrivCoh_growsAtB hfr.2
          (fun a hu hl => by
            obtain ⟨c, N, e, us, hc, rest⟩ := hu
            exact ⟨c, N, e, us, by rw [allocE_ne hl] at hc; exact hc, rest⟩)
          hoo' hg hful (fun t m _ _ hu hl => by
            obtain ⟨c, N, e, us, hc, -, -, hT, -⟩ := hu
            rw [hl, allocE_eq] at hc; cases hc
            simp only at hT; rw [hT] at hwcT; simp [wc, accs] at hwcT)⟩, ?_, hoh', hpd', hopub', hpi',
        BoxInv_alloc hbi rfl hpl hpo.1 hal rfl rfl (fun _ hl => allocE_ne hl) (fun _ _ => rfl),
        PromOK_alloc hpo hpl hal⟩
      rotate_left 1
      · have e : s'.vs.vRelSt = (stOf mem pairs th).vs.vRelSt := alloc_relSt _ hal
        exact (SeenLE.mono hsn (Nat.le_of_eq e.symm) : SeenLE (CE η) s'.vs.vRelSt)
      · have hj' : th.nalloc ≤ j := by
          have : s'.nalloc ≤ j := hj
          rw [hna] at this; exact Nat.le_of_succ_le this
        obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
        have hne : freshLabel g.lbase g.n g.i j ≠ freshLabel g.lbase g.n g.i th.nalloc := fun h => by
          have := freshLabel_inj_k hn h; subst this
          have : s'.nalloc ≤ th.nalloc := hj
          rw [hna] at this; exact absurd this (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
        refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, f4, f5⟩
        change s'.mem[t]? = some m at ht
        by_cases hlt : t < (stOf mem pairs th).mem.size
        · rw [hg.2.1 t hlt] at ht
          have hp := f2 t m ht hl
          refine Classical.byContradiction fun hn' => ?_
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl; rw [allocE_eq] at hcl; cases hcl
        exact noIallV_cl (WitAF.ni hi.1.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu)
      · rw [allocE_ne hl] at hcl; exact hnie l cl hcl
    · have h1 := hle (.own xl)
      have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) = 0 := by simp [Res.one, hxne]
      simp only [Res.add_apply] at h1 ⊢
      omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1091 stepK3_newBuf
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_newBufB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr} {Rf Rs HP : Res}
    {xl : AllocLabel}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hxl : (CE η).sto xl ≠ none) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hTyE : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCB p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | newBuf hwf hsc hop haf hint hb =>
  rename_i k
  have hiF := hi.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hiF.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hlay : accs (close th.σs τ) ≠ none := accs_close hwf hiF.2.2.2.2.1 haf hiF.2.2.2.2.2.1.2.2
  obtain ⟨us, hus⟩ : ∃ us, accs (close th.σs τ) = some us := Option.ne_none_iff_exists'.1 hlay
  
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hiF.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hiF.2.2.2.1 ρ hop hr
  have hwT : wc (cl ρ η.wit 0 0 τ) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨usT, husT⟩ : ∃ usT, accs (cl ρ η.wit 0 0 τ) = some usT := by
    cases h : accs (cl ρ η.wit 0 0 τ) with
    | none => simp [wc, h] at hwT
    | some usT => exact ⟨usT, rfl⟩
  have hnw : nWords usT = nWords us := by rw [wc_of_accs husT] at hwT; exact Option.some.inj hwT
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hiF.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  
  let z : Option (List WeakMem.Val) := if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none
  have hzv : ∀ zs, z = some zs → ValOfB η (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ wc (cl ρ η.wit 0 0 τ) = some zs.length := by
    intro zs h
    simp only [z] at h
    split at h
    · exact zero_valOfB hiF.2.2.2.1 (fun k => (hE.2.1 k).1) hiF.2.2.2.2.2.2.1 ρ hop hr haf ‹_› h
    · cases h
  have hstat : zeroableIn [] cx.ke τ = true → z.isSome = true := by
    intro h
    have hR := KindSound.zero_close cx.ke th.σs τ hiF.2.2.2.2.2.1.2.1 h
    obtain ⟨zs, hzs, -⟩ := zpB _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
    simp [z, hR, hzs]
  
  let K := ev ρ k
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  let iv : Nat := if z.isSome then K else 0
  let ini' := bumpIni η.ini lbl iv
  let rini' := bumpIni η.rini lbl iv
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  let E0 := CE (η.withStoB η.sto ini' (Ri := rini'))
  let T := Ty.array (.lit K) (cl ρ η.wit 0 0 τ)
  let E' := allocE E0 lbl T
  let η' := η.withStoB E'.sto ini' (Ri := rini')
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, hi0, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hX := memHeldOn_offB hH (l := lbl) (fun h => by
    obtain ⟨⟨c0, hc0, -⟩, -⟩ := h; rw [hnone] at hc0; cases hc0)
  have hnone0 : E0.sto lbl = none := hnone
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := E0) hnone0 h) (bumpIni_le _ _ _)
    (Ri := rini') (hRi := hri')
  let rtR : Ty := .refine (.loc .own (.array (.lit K) (close th.σs τ))) (.ini (.lit iv))
  let R := allocBuf lbl (K * nWords us) z (stOf mem pairs th)
  have key : tstep g mem pairs th =
      [(R.1.mem, R.1.pairs, withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1)] := by
    simp only [tstep, hterm, evalOp, hei, numOf, hus, Option.bind_eq_bind, Option.bind_some, hwi]; rfl
  rw [key]
  intro r hr' _
  simp only [List.mem_singleton] at hr'
  subst hr'
  have hpw : R.2 = cst (.loc ⟨lbl, 0⟩ 0) := rfl
  
  have hsub0 : ∀ l c, (CE η).sto l = some c → E0.sto l = some c := fun l c h => h
  have hile0 : ∀ l, (CE η).ini l ≤ E0.ini l := bumpIni_le η.ini lbl iv
  have hmo0 : MemOKPB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).promises :=
    MemOKP_monoB hmo rfl rfl hsub0 hile0 (fun t m c h hc => hc)
  have hmono0 : ∀ {U : Ty} {vs : List Word}, ValOfB (CE η) U vs → ValOfB E0 U vs :=
    fun h => ValOf_monoB (η₁ := CE η) (η₂ := E0) rfl rfl hsub0 hile0 h
  have hoo0 : OwnOKPFB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).vs
      (stOf mem pairs th).promises := by
    intro l c hc ho
    have hne : l ≠ lbl := fun h => by rw [h] at hc; rw [hnone0] at hc; cases hc
    exact OwnCellF_envB (hoo l c hc ho) hmono0 (bumpIni_other _ _ _ _ hne) rfl hmo.2.2 (bumpIni_other _ _ _ _ hne)
  have hi0' : η.ini lbl = 0 := hi0
  have hini : E0.ini lbl ≤ K := by
    show bumpIni η.ini lbl iv lbl ≤ K
    rw [bumpIni_self, hi0']
    refine Nat.max_le.2 ⟨Nat.zero_le _, ?_⟩
    simp only [iv]; split <;> omega
  have hini0 : 0 < E0.ini lbl → z ≠ none := by
    intro h hz0
    have : E0.ini lbl = 0 := by
      show bumpIni η.ini lbl iv lbl = 0
      rw [bumpIni_self, hi0']; simp [iv, hz0]
    omega
  have hzE : ∀ zs, z = some zs → ValOfB E' (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ zs.length = nWords usT :=
    fun zs h => ⟨ValOf_monoB (η₁ := η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (hzv zs h).1,
      by have := (hzv zs h).2; rw [hwT] at this; rw [hnw]; exact (Option.some.inj this).symm⟩
  have hab := allocBuf_okPB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
    (s := stOf mem pairs th) (η := E0) husT hzE
    hini hini0 hfresh hnone0 hpl hpo.2.1 hmo0 hoo0 hpf0
  rw [hnw] at hab
  obtain ⟨hmo', hoo', -⟩ := hab
  obtain ⟨hg, hpr, hna⟩ := allocBuf_grows lbl (K * nWords us) z (stOf mem pairs th)
  have hwE : ∀ T o w, WordOKB (CE η) T o w → WordOKB E' T o w := fun T o w h =>
    WordOK_monoB (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (fun _ _ h' => h') (fun _ h' => h') h
  have hiniE : ∀ l c o, l ≠ lbl → InitR E' c l o → InitR (CE η) c l o := fun l c o hl hi N1 e1 us1 h1 h2 => by
    have := hi N1 e1 us1 h1 h2
    rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  have hoh' : OwnHidPB E' R.1.mem R.1.vs R.1.promises := by
    refine ⟨?_, ?_⟩
    · intro l c hc ho o hi
      by_cases hl : l = lbl
      · rw [hl] at hc hi
        have hcT : c = ⟨T, some η.tid⟩ := by
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at hc; exact (Option.some.inj hc).symm
        subst hcT
        rw [hl]
        unfold HiddenPB
        intro t m hP hm hloc hnok
        exfalso
        rcases Option.eq_none_or_eq_some z with hzc | ⟨zs, hzc⟩
        · 
          have h0 : E'.ini lbl = 0 := by
            show bumpIni η.ini lbl iv lbl = 0
            rw [bumpIni_self, hi0']; simp [iv, hzc]
          have := hi K (cl ρ η.wit 0 0 τ) usT rfl husT
          rw [show E'.rc lbl = 0 by have := E'.rc_le_ini lbl; omega, Nat.zero_mul] at this; exact Nat.not_lt_zero _ this
        · 
          apply hnok
          by_cases hlt : t < (stOf mem pairs th).mem.size
          · rw [hg.2.1 t hlt] at hm
            exact (hP (hfresh t m hm (by rw [hloc]))).elim
          · have hw := allocBuf_newOKB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
              (s := stOf mem pairs th) (η := E0) husT hzE zs hzc t m (by omega) (by rw [hnw]; exact hm)
            rw [hloc] at hw; exact hw
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        exact HiddenP_growsAtB (hoh.1 l c hc ho o (fun N1 e1 us1 h1 h2 => by
            have := hi N1 e1 us1 h1 h2; rw [hrc] at this; exact this))
          (hwE _ _) (allocBuf_vWr_le _ _ _ _) hg hl
          (fun t h1 h2 => absurd h1 h2)
    · intro l c hc ho hlt
      by_cases hl : l = lbl
      · exfalso
        have h1 : E'.ini lbl ≤ E'.rini lbl := by
          show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl
          rw [bumpIni_self, bumpIni_self, hi0']; omega
        have h2 : E'.rc lbl = E'.ini lbl := Nat.min_eq_left h1
        rw [hl] at hlt; omega
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        have hie : E'.ini l = (CE η).ini l := bumpIni_other _ _ _ _ hl
        obtain ⟨f, hf, hsn', hH⟩ := hoh.2 l c hc ho (by rw [hrc, hie] at hlt; exact hlt)
        exact ⟨f, hf, fun hz => hsn' (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
          fun o hi => HiddenP_growsAtB (hH o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
          (fun t h1 h2 => absurd h1 h2)⟩
  have hpd' : PubDefPB E' R.1.mem R.1.promises := by
    intro l c f hc hown hf o hi
    by_cases hl : l = lbl
    · rw [hl] at hc
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at hc; cases hc; exact (hown rfl).elim
    · rw [allocE_ne hl] at hc
      exact HiddenP_growsAtB (hpd l c f hc hown hf o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
        (fun t h1 h2 => absurd h1 h2)
  have hopub' : OwnPubV E' R.1 := by
    intro l c f hc ho hf
    by_cases hl : l = lbl
    · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
    · rw [allocE_ne hl] at hc
      exact ((hopub.allocBuf hpl lbl (K * nWords us) z) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
        fun a ha hi c1 N1 e1 us1 h1 h2 h3 => by
          have hne : a.label ≠ lbl := fun e => hl (ha.symm.trans e)
          have := hi c1 N1 e1 us1 (by rw [allocE_ne hne]; exact h1) h2 h3
          rwa [show E'.rc a.label = (CE η).rc a.label from
            TEnv.rc_congr (bumpIni_other _ _ _ _ hne) (bumpIni_other _ _ _ _ hne)] at this)
  have hrcl : E'.rc lbl = E'.ini lbl := Nat.min_eq_left (show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl by
    rw [bumpIni_self, bumpIni_self, hi0']; omega)
  have hpi' : PubInvB E' R.1 := by
    refine PubInv_growB (E := CE η) (hbs := fun l hb h => by
        by_cases hl : l = lbl
        · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
        · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (fun _ h => h) (fun t h1 h2 => absurd h1 h2) rfl rfl
      (fun l c h => allocE_sub (η := E0) hnone0 (hsub0 l c h)) hile0 rfl rfl
      (fun c h => by
        have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
        rw [h2] at h; rw [← Option.some.inj h]; rfl)
      (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd hlt (by rw [hrcl]; exact Nat.lt_irrefl _))
      (hrcg := fun l h => by
        by_cases hl : l = lbl
        · rw [hl, hrcl] at h; exact absurd h (Nat.lt_irrefl _)
        · exact ⟨by rwa [TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl),
            show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl] at h,
            Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl)⟩)
      (hfi := fun l c h ho => by
        by_cases hl : l = lbl
        · rw [hl] at h
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at h; rw [← Option.some.inj h] at ho; exact absurd rfl ho
        · exact Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl))
    · by_cases hl : l = lbl
      · exact Or.inr (by rw [hl]; exact hpf0)
      · rw [allocE_ne hl] at h; exact Or.inl h
    by_cases hl : l = lbl
    · rw [hl] at h
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at h; cases h
      refine Or.inr ?_
      rcases hseg with ⟨-, rfl, -⟩ | ⟨N1, us1, j1, hT1, -, -, -⟩
      · simp [T, accs] at hu'
      · have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N1) S := hT1
        simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
        obtain ⟨-, rfl⟩ := hT2
        rw [husT] at hu'; obtain rfl := Option.some.inj hu'
        obtain ⟨-, jb, -, hjb, -⟩ := hini K (cl ρ η.wit 0 0 τ) rfl
        have hpos : 0 < E0.ini lbl := by
          rw [hl] at hjb; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hjb
        obtain ⟨zs, hzs⟩ := Option.ne_none_iff_exists'.1 (hini0 hpos)
        obtain ⟨h1, h2⟩ := hzE zs hzs
        exact ⟨zs.map cst, h1, by rw [List.length_map]; exact h2⟩
    · rw [allocE_ne hl] at h
      refine Or.inl ⟨h, fun N1 e1 h1 => ?_⟩
      have := hini N1 e1 h1
      rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  
  have hzR : ∀ zs, z = some zs → ValOfRB E' (cl ρ η.wit 0 0 τ) (zs.map cst) Res.zero := by
    intro zs h
    simp only [z] at h
    split at h
    · rename_i hR
      have hZ := zrel_WitL hiF.2.2.2.1 (fun k => (hE.2.1 k).1) ρ hop hr
      have hTz := (zrel_zero _ _ [] [] hZ hsig knone_nil).1 hR
      have hwT' := zrel_words _ _ _ [] zs (Nat.lt_succ_self _) hZ hsig h
      obtain ⟨zs', hzw', -, hv⟩ := zpRB _ _ (Nat.lt_succ_self _) [] [] hafT knone_nil hTz
      obtain rfl : zs = zs' := Option.some.inj (hwT'.symm.trans hzw')
      obtain ⟨hV0, hvr0⟩ := hv _ (map_val_cst zs)
      exact ⟨hvr0 _ _ (agree_nil _), hV0⟩
    · cases h
  
  have hfr' : FInvRB g.lbase g.n g.i ρ η' th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, rtR, [R.2]) :: th.env) (Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc))) := by
    refine bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi) (RLink_ofB hx.1 hx.2.2.2.2.2.2.2.2.2.2.1) ?_ ?_
    · 
      simp only [VRRB]
      refine ⟨⟨Or.inr ⟨⟨lbl, 0⟩, ⟨T, some η.tid⟩, _, by simp [hpw, cst, Promises.TVal.mk0],
        (show E'.sto lbl = _ from allocE_eq), ?_, .refl, by first | rfl | trivial, ?_⟩,
        (ownW_own_loc (a := ⟨lbl, 0⟩) (g := 0) (by simp [hpw, cst, Promises.TVal.mk0])).symm⟩, ?_⟩
      · simp only [cl, clI_zero]; exact AtOff.here (Or.inr ⟨K, _, rfl, by simp [husT]⟩)
      · intro N' e' h; left; exact ⟨by simp only [cl, clI_zero]; rfl, rfl⟩
      · refine ⟨fun a ha => ?_, fun hp => absurd hp (by rintro ⟨_, _, h⟩; simp [pp] at h)⟩
        have hav : a = ⟨lbl, 0⟩ := by simp [hpw, cst, Promises.TVal.mk0] at ha; exact ha.symm
        subst hav
        show ev ρ _ ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
        refine Nat.le_min.2 ⟨?_, ?_⟩
        · rw [bumpIni_self]
          split
          · rename_i hzs
            have h1 := hstat hzs
            have h2 : iv = K := by simp only [iv, h1, ite_true]
            rw [h2]; exact Nat.le_max_right _ _
          · exact Nat.zero_le _
        · rw [bumpIni_self]
          split
          · rename_i hzs
            have h1 := hstat hzs
            have h2 : iv = K := by simp only [iv, h1, ite_true]
            rw [h2]; exact Nat.le_max_right _ _
          · exact Nat.zero_le _
    · refine ⟨fun us' h => by simp [rtR, accs] at h; subst h; rfl, ?_, by simp [rtR, wc, accs], ?_, ?_⟩
      · simp [rtR, skel, close, substTs, skelM, rf]
      · simp only [rtR, Valid]; exact Or.inr ⟨⟨lbl, 0⟩, by simp [hpw, cst, Promises.TVal.mk0]⟩
      · simp [rtR, close, substTs, lyt, anyB_zero, idxC, ofMs, modeC]
  
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, bufVal z j, 0⟩
  have hget : ∀ t : Nat, R.1.mem[t]? = if t < (stOf mem pairs th).mem.size then (stOf mem pairs th).mem[t]?
      else if t < (stOf mem pairs th).mem.size + K * nWords us then some (f (t - (stOf mem pairs th).mem.size))
      else none := by
    intro t
    show (allocBuf lbl (K * nWords us) z (stOf mem pairs th)).1.mem[t]? = _
    rw [allocBuf_mem]; exact fold_get f _ _ t
  have hV : R.1.vs.coh = fun b => if b.label = lbl ∧ b.offset < K * nWords us
      then (stOf mem pairs th).mem.size + b.offset else (stOf mem pairs th).vs.coh b := rfl
  have hent : HeldEntryB E' R.1 lbl Res.zero := by
    refine HeldEntry_ownPB (vals := (List.range (K * nWords us)).map (fun j => cst (bufVal z j)))
      allocE_eq (PromAt_privL (Priv_of allocE_eq rfl hpf0)) (fun o v hov => ?_) (Or.inr ?_)
    · obtain ⟨o, rfl⟩ : ∃ o' : Nat, o' = o := ⟨o, rfl⟩
      have ho' : o < K * nWords us := by
        have := (List.getElem?_eq_some_iff.1 hov).1; simpa using this
      rw [List.getElem?_map, List.getElem?_range ho'] at hov
      simp only [Option.map_some, Option.some.injEq] at hov; subst hov
      refine LatestS_of_latest ⟨⟨f o, ?_, by simp [f, offs], rfl, fun _ _ _ => Nat.zero_le _⟩,
        fun t m ht hm' => ?_⟩ ?_
      rotate_left 2
      · intro hp
        have hp' : R.1.vs.coh ⟨lbl, o⟩ ∈ (stOf mem pairs th).promises := by rw [← hpr]; exact hp
        have h1 := hpl _ hp'
        have e : R.1.vs.coh ⟨lbl, o⟩ = (stOf mem pairs th).mem.size + o := by rw [hV]; simp [ho']
        rw [e] at h1; exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h1)
      · rw [hV, hget]; simp [ho']
      · obtain ⟨t, rfl⟩ : ∃ t' : Nat, t' = t := ⟨t, rfl⟩
        rw [hV] at ht; simp [ho'] at ht
        replace ht : (stOf mem pairs th).mem.size + o < (t : Nat) := ht
        rw [hget t] at hm'
        have h0 : ¬ t < (stOf mem pairs th).mem.size := by omega
        simp only [h0, ite_false] at hm'
        split at hm'
        · simp only [Option.some.injEq] at hm'; subst hm'
          simp [f, offs]; intro h; replace h : (t : Nat) - (stOf mem pairs th).mem.size = o := h; omega
        · cases hm'
    · refine ⟨K, cl ρ η.wit 0 0 τ, usT, (List.range (E'.ini lbl)).map (fun _ => Res.zero), rfl, husT, hini,
        by rw [List.length_map, List.length_range, hnw], by simp, (TermStep.sum_map_zero _).symm, fun j Rj hj hRj => ?_⟩
      rw [List.getElem?_map, List.getElem?_range hj] at hRj
      simp only [Option.map_some, Option.some.injEq] at hRj; subst hRj
      have hjK : j < K := Nat.lt_of_lt_of_le hj hini
      obtain ⟨zs, hzc⟩ := Option.ne_none_iff_exists'.1 (hini0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hj))
      have hzl : zs.length = nWords us := by rw [← hnw]; exact (hzE zs hzc).2
      have e1 : ((((List.range (K * nWords us)).map (fun j => cst (bufVal z j))).drop (j * nWords usT)).take
          (nWords usT)) = zs.map cst := by
        rw [hnw]
        apply List.ext_getElem?; intro i
        rw [slice_get]
        by_cases hi : i < nWords us
        · simp only [hi, ↓reduceIte]
          have hjN : j * nWords us + i < K * nWords us := by
            have := Nat.mul_le_mul_right (nWords us) (show j + 1 ≤ K by omega); rw [Nat.succ_mul] at this
            omega
          rw [List.getElem?_map, List.getElem?_range hjN]
          have hg' : zs[(j * nWords us + i) % nWords us]? = some (bufVal z (j * nWords us + i)) := by
            rw [hzc, ← hzl]; exact bufVal_some (by omega)
          have hmod : (j * nWords us + i) % nWords us = i := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
          rw [hmod] at hg'
          rw [List.getElem?_map, hg']; rfl
        · simp only [hi, ↓reduceIte]; symm; exact List.getElem?_eq_none (by simp only [List.length_map]; omega)
      rw [e1]; exact ⟨fun _ _ => rfl, fun _ => hzR zs hzc⟩
  have hX' := memHeldOn_trB (Q' := fun l' => Priv E' l' ∧ l' ≠ lbl) (E' := E') (s' := R.1) hX
    (fun l => ⟨fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne] at hc; exact hc, ho⟩, hp⟩, hne⟩,
      fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne]; exact hc, ho⟩, hp⟩, hne⟩⟩)
    (fun l' h => allocE_ne h.2) (fun l' h => bumpIni_other _ _ _ _ h.2) (fun l' h => bumpIni_other _ _ _ _ h.2)
    (fun _ _ => rfl) rfl rfl
    (fun l' h o w hl => LatestNP_growsAtA hg hpr h.2 hl)
    (fun h => ValOfR_monoB (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) h)
  have hxne : xl ≠ lbl := fun e => hxl (by rw [e]; exact hnone)
  have hk := tyOKE_alloc (E := CE η) (E' := E') hn (by rw [key]; exact List.mem_singleton_self _) (fun _ hl => allocE_ne hl) hTyE hRc
    (fun _ t _ ht => absurd (by rwa [tysUpd_keep (th := th) (th' := withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1) rfl] at ht) (hRc th.nalloc (Nat.le_refl _) t))
  refine ⟨E', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Res.zero + HP,
    ⟨ρ, η', c', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      ⟨hmo', hoo', fun t ht => by
        have ht' : t ∈ R.1.promises := ht
        rw [hpr] at ht'; exact Nat.lt_of_lt_of_le (hpl t ht') hg.1,
      ⟨fun j hj => ?_, PrivCoh_allocBufB hfr.2
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, ho, hp, hT, hus1, hle, hlt⟩ := hu
          refine ⟨c, N, e, us1, by rw [allocE_ne hl] at hc; exact hc, ho, hp, hT, hus1, ?_, hlt⟩
          rwa [TEnv.rc_congr (η' := E') (η := CE η) (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)] at hle)
        hoo' hfresh
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, -, -, hT, hus1, hle, hlt⟩ := hu
          rw [hl, show E'.sto lbl = some ⟨T, some η.tid⟩ from allocE_eq] at hc; cases hc
          have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) e := hT
          simp only [Ty.array.injEq, Idx.lit.injEq] at hT2; obtain ⟨rfl, rfl⟩ := hT2
          refine Classical.byContradiction fun hz => ?_
          have hs : z.isSome = true := Option.ne_none_iff_isSome.1 hz
          have hrc : K ≤ E'.rc lbl := by
            show K ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
            have hiv : iv = K := by simp only [iv, hs, ↓reduceIte]
            rw [bumpIni_self, bumpIni_self, hiv]
            exact Nat.le_min.2 ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
          rw [hl] at hle
          have := Nat.mul_le_mul_right (nWords us1) hrc
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans this hle)) (Nat.lt_irrefl _))⟩, hsn,
        hoh', hpd', hopub', hpi', BoxInv_allocBuf hbi rfl rfl rfl (fun l hl => by rw [allocE_ne hl]; rfl) (fun l hl => bumpIni_other _ _ _ _ hl),
        PromOK_eq hpo rfl rfl⟩,
      memHeldOn_unfocusB hX' hent (Priv_of allocE_eq rfl hpf0), fun l cl hcl => ?_,
      fun h => hxl (by rw [allocE_ne hxne] at h; exact h), ?_,
      anchStep_freshB (ext_CEB hx) (bumpIf_nb hterm (hop := by intro _ _ _ h; cases h) _) (fun _ hl => allocE_ne hl) hpf0
        (fun _ hl => bumpIni_other _ _ _ _ hl) hnone (Priv_of allocE_eq rfl hpf0)
        (fun _ hl => by first | rfl | exact bumpIni_other _ _ _ _ hl)
        (fun h => bumpIni_rle h _), hk.1, hk.2⟩
  · have hj' : th.nalloc ≤ j := by
      have h1 : R.1.nalloc ≤ j := hj
      rw [hna] at h1; exact Nat.le_of_succ_le h1
    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
    have hne : freshLabel g.lbase g.n g.i j ≠ lbl := fun h => by
      have := freshLabel_inj_k hn h; subst this
      have h1 : R.1.nalloc ≤ th.nalloc := hj
      rw [hna] at h1; exact absurd h1 (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
    refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, ?_,
      ⟨by show bumpIni η.rini lbl iv (freshLabel g.lbase g.n g.i j) = 0; rw [bumpIni_other _ _ _ _ hne]; exact f5.1, f5.2⟩⟩
    · change R.1.mem[t]? = some m at ht
      by_cases hlt : t < (stOf mem pairs th).mem.size
      · rw [hg.2.1 t hlt] at ht; exact f2 t m ht hl
      · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · show bumpIni η.ini lbl iv (freshLabel g.lbase g.n g.i j) = 0
      rw [bumpIni_other _ _ _ _ hne]; exact f4
  · by_cases hl : l = lbl
    · subst hl; rw [allocE_eq] at hcl; cases hcl
      exact noIallV_cl (WitAF.ni hiF.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [noIallV] using hniA)
    · rw [allocE_ne hl] at hcl; exact hnie l cl hcl
  · have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) = 0 := by simp [Res.one]; exact hxne
    simp only [Res.add_apply, Res.zero_apply]
    omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1512 ownXStepL_ldl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_ldlB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsLdl :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, hte⟩ := ht
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_ldlB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1517 ownXStepL_ldlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_ldlwB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsLdlw :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_ldlwB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1522 ownXStepL_new
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_newB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsNew :=
  ownXStepL_ofB (fun _ _ _ th r ρ η cx _ Rs _ hpp hn ht hsc hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, a, _, _, hte⟩ := ht
    have hsd := hsc ρ η cx hE hT.1 htv (finv_ofB htv hi)
    rw [hte] at hsd
    have hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true := by
      rcases hsd with h | ⟨_, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals cases h
    exact stepK3_newB (hDy := hDy) hte hniA hP hn hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS hpp hTyE hRc r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1533 ownXStepL_newBuf
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_newBufB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsNewBuf :=
  ownXStepL_ofB (fun _ _ _ th r ρ η cx _ Rs _ _ hn ht hsc hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, τ, _, hte⟩ := ht
    have hsd := hsc ρ η cx hE hT.1 htv (finv_ofB htv hi)
    rw [hte] at hsd
    have hniA : noIallV τ = true := by
      rcases hsd with h | ⟨_, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals cases h
    exact stepK3_newBufB (hDy := hDy) hte hniA hP hn hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS hTyE hRc r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1544 ownXStepL_bufInit
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_bufInitB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsBufInit :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    exact stepK3_bufInitB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS hTyE hRc r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1549 ownXStepL_xchgAt
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_xchgAtB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsXchgAt :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_xchgAtB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1554 ownXStepL_xchgAtF
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_xchgAtFB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsXchgAtF :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, _, hte⟩ := ht
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_xchgAtFB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1559 ownXStepL_stl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_stlB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsStl :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_stlB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1564 ownXStepL_stlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_stlwB [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLB p x n IsStlw :=
  ownXStepL_ofB (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, _, hte⟩ := ht
    refine stepC_ofKB ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_stlwB (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1570 ownXStepL_k3
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_k3B {p : Prog} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepLB p x n IsBufInit) (h2 : OwnXStepLB p x n IsXchgAt) (h3 : OwnXStepLB p x n IsXchgAtF)
    (h4 : OwnXStepLB p x n IsStl) (h5 : OwnXStepLB p x n IsStlw) (h6 : OwnXStepLB p x n IsLdl)
    (h7 : OwnXStepLB p x n IsLdlw) (h8 : OwnXStepLB p x n IsNew) (h9 : OwnXStepLB p x n IsNewBuf) :
    OwnXStepLB p x n (fun t => exprPkg t = 3) := by
  intro g mem pairs th r hp hn ht
  generalize hte : th.term = t at ht
  cases t with
  | let_ y op e =>
    cases op with
    | bufInit a b c => exact h1 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | xchgAt a b c => exact h2 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | xchgAtF a b c d => exact h3 g mem pairs th r hp hn ⟨y, a, b, c, d, e, hte⟩
    | stl a b c => exact h4 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | stlw a b c d => exact h5 g mem pairs th r hp hn ⟨y, a, b, c, d, e, hte⟩
    | ldl a b => exact h6 g mem pairs th r hp hn ⟨y, a, b, e, hte⟩
    | ldlw a b c => exact h7 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | new a T => exact h8 g mem pairs th r hp hn ⟨y, a, T, e, hte⟩
    | newBuf a b => exact h9 g mem pairs th r hp hn ⟨y, a, b, e, hte⟩
    | _ => simp [exprPkg, opPkg] at ht
  | _ => simp [exprPkg] at ht
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1593 ownXStep_k3_of
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k3_ofB {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepLB p x n IsBufInit) (h2 : OwnXStepLB p x n IsXchgAt) (h3 : OwnXStepLB p x n IsXchgAtF)
    (h4 : OwnXStepLB p x n IsStl) (h5 : OwnXStepLB p x n IsStlw) (h6 : OwnXStepLB p x n IsLdl)
    (h7 : OwnXStepLB p x n IsLdlw) (h8 : OwnXStepLB p x n IsNew) (h9 : OwnXStepLB p x n IsNewBuf) :
    OwnXStepPkgB p k arch i x n 3 :=
  ownXStepPkg_of_localB (ownXStepL_k3B h1 h2 h3 h4 h5 h6 h7 h8 h9)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1601 ownXStep_k3
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k3B [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} [ProgRetIall p]
    (hP : ProgT p) (hPS : PwSkel) : ∀ n, OwnXStepPkgB p k arch i x n 3 := fun _ =>
  ownXStep_k3_ofB (ownXStepL_bufInitB hP hPS) (ownXStepL_xchgAtB hP hPS) (ownXStepL_xchgAtFB hP hPS) (ownXStepL_stlB hP hPS)
    (ownXStepL_stlwB hP hPS) (ownXStepL_ldlB hP hPS) (ownXStepL_ldlwB hP hPS) (ownXStepL_newB hP hPS) (ownXStepL_newBufB hP hPS)
end
end TermOwnK3.Flat

-- PORTB TermOwnK4.lean:39 Src
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
structure SrcB (p : Prog) (g : G) (x : AllocLabel) (n : Nat) (mem : Memory) (pairs : List Ts) (th : TTh)
    (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs HP : Res) : Prop where
  gp : g.p = p
  gn : 0 < g.n
  hE : EnvOKB p η
  hT : Typed p cx th.term
  ck : TermA4.CkW p η.wit cx th.term
  tv : TvOK cx
  hF : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf
  hm : MemInvB g (CE η) (stOf mem pairs th)
  hH : MemHeldPB (CE η) (stOf mem pairs th) HP
  bf : g.boxFence = true
  nie : TermOwnX2.StoNIE (CE η)
  sto : (CE η).sto x ≠ none
  le : (Rf + Rs) (.own x) + HP (.own x) ≤ n
  sc : ScopeD th.σs cx th.term
  px : PAx g mem pairs th
  rp : RetPw th.σs th.stack cx.ret
  dy : DyFr p annNew (progTgts p) η th.σs th.term
  ty : TyOKE g (CE η)
  rc : RecFresh g g.i th.nalloc
end
end TermOwnK4.Flat

-- ♭ mirror of W TermOwnK4 Src.tyk (W tgt_tyOKE is layer-free).
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem SrcB.tyk {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    {E' : TEnv} {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hsub : ∀ l c, E'.sto l = some c → (CE η).sto l = some c) :
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E' ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc :=
  TermOwnK4.tgt_tyOKE hS.gn hr hsub (hS.hm.2.2.2.1.1 th.nalloc (Nat.le_refl _)).1 hS.ty hS.rc
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:60 Tgt
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def TgtB (p : Prog) (g : G) (x : AllocLabel) (n' : Nat) (Es : TEnv) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E r.2.2 Tot ∧
    MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
    E.sto x ≠ none ∧
    Tot (.own x) + HP (.own x) ≤ n' ∧ TermOwnX2.Flat.AnchStepB g th Es E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:68 ownXLe_of_src
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXLe_of_srcB [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n n' : Nat}
    {c0 c0' : Cfg} {th : TTh} (hth : c0.ths[i]? = some th) (hsc : ScopeAtB p i c0)
     (hvI : TermViewInv.ViewInv c0) (hI : TermOwnX2.Flat.OwnXLeB p k arch E0 i x n c0)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc : Certified p k arch c0' i) (hnn : n' = 0 → n = 0)
    (h : ∀ ρ η cx Rf Rs HP, SrcB p (gOf p k arch c0 i) x n c0.mem c0.pairs th ρ η cx Rf Rs HP →
      TgtB p (gOf p k arch c0 i) x n' (CE η) c0.mem c0.pairs th) :
    TermOwnX2.Flat.OwnXLeB p k arch E0 i x n' c0' := by
  obtain ⟨th1, E, Tot, HP, hth1, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hFI, rfl, hRP, hDy⟩, hm, hH, hbf, hnie, hsto, hle, hx0, hA, hTy, hRc, hZ, hR⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hFp := TermOwnX2.Flat.finv_ofB htv hFI
  have hS : SrcB p (gOf p k arch c0 i) x n c0.mem c0.pairs th ρ η cx Rf Rs HP :=
    ⟨rfl, Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)), hE, hT.1, hT.2, htv, hFI, hm, hH, hbf, hnie, hsto, hle,
      hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT.1 htv hFp, PAx_of_step hs hc hth, hRP, hDy, hTy, hRc⟩
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨E', Tot', HP', hT', hm', hH', hnie', hsto', hle', hAS, hTy', hRc'⟩ := h ρ η cx Rf Rs HP hS r hr hpa
  have hsub := TermTyped.tysOf_thread hs hth e3 hRc
  obtain ⟨hx', hA'⟩ := hAS.1 E0 hx0 hA hm.2.2.2.1.old hm' (TermOwnX2.Flat.wrHypB hE hT.1 htv hFp hm hS.sc (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth) hr)
  refine ⟨r.2.2, E', Tot', HP', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, by rw [gOf_thread hs]; exact hbf, hnie', hsto', hle', hx', ?_, ?_, ?_, ?_, fun h => hAS.2.2 (hR h)⟩
  · rw [gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hH'
  · rw [e1, e2]; exact hA'
  · rw [gOf_thread hs]; exact TyOKE_mono hsub hTy'
  · rw [gOf_thread hs]
    exact RecFresh_sub (g := { gOf p k arch c0 i with tys := tysUpd (gOf p k arch c0 i).tys th r.2.2 })
      (g' := { gOf p k arch c0 i with tys := tysOf c0' }) hsub rfl rfl hRc'
  · intro hn0
    have hn1 := hnn hn0
    subst hn1
    have hR0 : Rf (.own x) = 0 := by simp only [Res.add_apply] at hle; omega
    rcases hAS.2.1 x hsto with h7 | h7
    · exact Nat.le_trans h7 (hZ rfl)
    · exact absurd h7 (TermOwnX2.Flat.not_bufInitL_ofB hE hT.1 hFI hR0)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:96 tgt_same
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_sameB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hR : ∀ r ∈ tstep g mem pairs th, ∃ Tot', ThInvREB g.lbase g.n g.i p (CE η) r.2.2 Tot' ∧ TotStep th.term η (Rf + Rs) Tot')
    (hsm : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    TgtB p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨Tot', hT', hts⟩ := hR r hr
  have e := hsm r hr
  refine ⟨CE η, Tot', HP, hT', MemInv_sameB hS.hm e, TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH e.1 e.2.2.2.1, hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_eqsB e.1 e.2.2.2.1, hS.tyk hr (fun _ _ h => h)⟩
  have h1 := totStep_own_le hts x
  have h2 := hS.le
  omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:110 tgt_frame
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_frameB {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP) (hscR : StepScopeR th.σs cx th.term)
    (hsm : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    TgtB p g x n (CE η) mem pairs th := fun r hr hpa =>
  tgt_sameB hS (tstepR_stepB (hDy := hS.dy) hP hS.gp (tstep_notDone hr) hscR hS.hT hS.ck hS.hF hS.hE (supI_of_memInvB hS.hm hS.gn) hS.tv hS.rp hPS hSub hSig).2 hsm r hr hpa
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:161 memHeldP_shrink
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldP_shrinkB {E E1 : TEnv} {s s' : St} {HP : Res} (hx : EnvShrink E E1)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (h : MemHeldPB E s HP) :
    ∃ HP', MemHeldPB E1 s' HP' ∧ ∀ k, HP' k ≤ HP k := by
  classical
  obtain ⟨hp, ht, hI, hsto, hini, hri, hpf⟩ := hx
  have hpv : ∀ l, Priv E1 l → Priv E l := fun l ⟨⟨c, hc, ho⟩, hn⟩ =>
    ⟨⟨c, by rw [← hsto]; exact hc, by rw [ht]; exact ho⟩, hpf l hn⟩
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := h
  refine ⟨Res.sum ((L.filter (fun l => decide (Priv E1 l))).map Rl),
    ⟨_, Rl, hn.filter _, fun l c hq1 hs => List.mem_filter.2 ⟨hc l c (hpv l hq1) (by rw [← hsto]; exact hs),
      by simpa using hq1⟩, fun l hl => by simpa using (List.mem_filter.1 hl).2, rfl, fun l hl => ?_⟩,
    fun k => sum_filter_le _ Rl k L⟩
  have hl1 := (List.mem_filter.1 hl).1
  exact TermInterf.Flat.HeldEntry_priv_moveB hp ht hI (hq l hl1) (by simpa using (List.mem_filter.1 hl).2) (by rw [hsto])
    (by rw [hini]) (by rw [hri]) e2 (fun t _ => by rw [e1])
    (fun t m h1 h2 => by rw [e1] at h2; exact absurd (lt_of_get h2) (by omega)) (he l hl1)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:186 pubCell_side
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pubCell_sideB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx c₁ : Cx} {env : Env}
    {a : At} {u : Ty} {c : Cell} (hE : EnvOKB p η) (htv : TvOK cx)
    (hi1 : FInvB glb gnum gi ρ η σs (fun _ _ => True) c₁ env) (hu : cx.use a = .ok (.ptr .own u, c₁))
    (hsh : Ty.sharedOKIn c₁.ke (.ptr .pub u) = true) (hsc : PubScope cx a)
    (hcty : Fd c.ty (cl ρ η.wit 0 0 u)) (hacc : accs c.ty ≠ none) :
    (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOKB S) ∧ Ty.coupledOKIn [] c.ty = true ∧
      Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true := by
  have hcu : Ty.coupledOKIn c₁.ke u = true := by
    simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
  have htbu : tb c₁.ke.length u = true := by
    have h := (use_TvOK hu htv).2.1
    rw [← (use_TvOK hu htv).2.2] at h
    simpa [tb] using h
  have hcp := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu
  refine ⟨fun b S hseg _ => ?_, coupledOK_Fd hcty hcp, noOwn_Fd hcty ?_, rgnFree_Fd hcty
    (rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk) hcu
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl)))⟩
  · obtain ⟨-, rfl⟩ := SegOf_lay hacc hseg
    exact TearOK_FdB hcty (TearOK_of_cplB hcp)
  · have hnu : Ty.noOwnIn c₁.ke u = true := by
      simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
    exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
      (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) u hnu htbu
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:404 ext_shrink
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ext_shrinkB {p : Prog} {η E1 : TEnv} {th : TTh} {Tot : Res} (hRE : ThInvREB glb gnum gi p E1 th Tot)
    (hx : EnvShrink (CE η) E1) (hsn : ∀ l, (CE η).seen l → E1.seen l) : ExtB (CE η) E1 := by
  obtain ⟨_, η', _, _, _, rfl, _⟩ := hRE
  exact ⟨Coh_CEB η', rfl, hx.1.symm, hx.2.1.symm, hx.2.2.1.sto, hx.2.2.1.ini, hx.2.2.1.pfr, hsn, hx.2.2.1.box,
    Nat.le_refl _, CohR_CEB η', hx.2.2.1.rini⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:460 KeepOut
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def KeepOutB (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (T : Res) : Prop :=
  ∀ r ∈ tstep g mem pairs th, stOf r.1 r.2.1 r.2.2 = stOf mem pairs th ∧ ThInvREB g.lbase g.n g.i p (CE η) r.2.2 T
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:463 tgt_keep
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_keepB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (h : KeepOutB p g mem pairs th η (Rf + Rs)) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨e, hT'⟩ := h r hr
  rw [e]
  exact ⟨CE η, Rf + Rs, HP, hT', hS.hm, hS.hH, hS.nie, hS.sto, hS.le, TermOwnX2.Flat.anchStep_eqsB rfl rfl, hS.tyk hr (fun _ _ h => h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:473 mkWord_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem mkWord_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : Proto} {v tk : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.mkWord rn P v tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : KeepOutB p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord hidx hpwf hu heq hv hst hcl hng hho hb =>
    rename_i c₁ r r' j k c cl
    obtain ⟨rt0, ws0, R0, Rr, -, -, -, hR0, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    have hR : R0 = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r)) := by
      simp only [VRRB, tokWd_none] at hR0; rw [hR0, heq ρ hi1.1.1]
    obtain ⟨tv, htvk, hio⟩ := hv
    obtain ⟨rt, w, hea, hwv, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .word (.lit 0) P, [w]) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hng, hea]; rfl
    intro r0 hr
    rw [key, List.mem_singleton] at hr
    subst hr
    obtain ⟨cl', hcl', hent⟩ := hst
    rw [hcl] at hcl'; cases hcl'
    have hn := hent ρ hi1.1.1
    have hvr : VRRB ρ η (.word r P) (shp (.word (.lit 0) P)) [w] (.one (.rg (ev ρ r)) + wdW P (ev ρ r)) := by
      simp only [VRRB]
      refine ⟨⟨hpwf, fun _ => ⟨_, by simp [hwv], _, cl, _, hcl, hn⟩⟩, Or.inl ⟨?_, by first | rfl | trivial⟩⟩
      exact ⟨hng, ev ρ j, c, cl, ev ρ k, by simp [hwv], hcl, hho, hn⟩
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvr (Lay_word th.σs r P hng w)
    have hfr' : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .word (.lit 0) P, [w]) :: th.env) Rf :=
      FInvR_monoB hfr (frame_trade hle (by rw [hR]; exact tokNone_pays P _ _ (Res.le_refl _)))
    exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
  | mkWordGhost hidx hpwf hu heq hv hst hcl hg hho hb =>
    rename_i c₁ r r' j k c cl
    obtain ⟨rt0, ws0, R0, Rr, -, -, -, hR0, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    have hR : R0 = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r)) := by
      simp only [VRRB, tokWd_none] at hR0; rw [hR0, heq ρ hi1.1.1]
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .prod (.word (.lit 0) P) (.tok (.lit 0) none), []) :: th.env }
            (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hg]; rfl
    intro r0 hr
    rw [key, List.mem_singleton] at hr
    subst hr
    have hvr : VRRB ρ η (.prod (.word r P) (.tok r (some (P, j))))
        (shp (.prod (.word (.lit 0) P) (.tok (.lit 0) none))) [] (wdW P (ev ρ r) + .one (.rg (ev ρ r))) := by
      simp only [VRRB]
      refine ⟨_, _, rfl, wdW P (ev ρ r), .one (.rg (ev ρ r)), rfl, fun hn => ?_, fun n hn => ?_⟩
      · simp [shp_wc, wc, accs, hg, nWords] at hn
      · simp [shp_wc, wc, accs, hg, nWords] at hn
        subst hn
        refine ⟨by simp, ⟨⟨hpwf, fun h => by rw [hg] at h; cases h⟩, Or.inr ⟨fun h => ?_, by first | rfl | trivial⟩⟩,
          by first | rfl | trivial⟩
        have h1 := h.1; rw [hg] at h1; cases h1
    have hl2 := Lay_pair (Lay_wordGhost th.σs r P hg) (Lay_tokGhost th.σs r P j)
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvr hl2
    have hfr' : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c'
        ((x, .prod (.word (.lit 0) P) (.tok (.lit 0) none), []) :: th.env) Rf :=
      FInvR_monoB hfr (frame_trade hle (by
        rw [hR]; exact fun k => by have := wdW_le P (ev ρ r) k; simp only [Res.add_apply] at *; omega))
    exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:543 mkWord2_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem mkWord2_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : Proto2} {v0 v1 tk : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.mkWord2 rn P v0 v1 tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : KeepOutB p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord2 hidx hpwf hu heq hv0 hv1 hst hcl hho hb =>
  rename_i c₁ r r' j0 j1 k0 k1 c cl
  obtain ⟨rt0, ws0, R0, Rr, -, -, -, hR0, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hR : R0 = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r)) := by
    simp only [VRRB, tokWd_none] at hR0; rw [hR0, heq ρ hi1.1.1]
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_numB hi1.1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_numB hi1.1.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .word2 (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  intro r0 hr
  rw [key, List.mem_singleton] at hr
  subst hr
  obtain ⟨cl', hcl', hent⟩ := hst
  rw [hcl] at hcl'; cases hcl'
  obtain ⟨h0, h1, h2⟩ := hent ρ hi1.1.1
  have hvr : VRRB ρ η (.word2 r P) (shp (.word2 (.lit 0) P)) [w0, w1] (.one (.rg (ev ρ r)) + .one (.wd (ev ρ r))) := by
    simp only [VRRB]
    refine ⟨⟨hpwf, _, _, by simp [hwv0, hwv1], _, cl, _, _, hcl, h0, h1, h2⟩,
      Or.inl ⟨?_, by first | rfl | trivial⟩⟩
    exact ⟨_, _, c, cl, _, _, by simp [hwv0, hwv1], hcl, hho, h0, h1, h2⟩
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvr (Lay_word2 th.σs r P w0 w1)
  have hfr' : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .word2 (.lit 0) P, [w0, w1]) :: th.env) Rf :=
    FInvR_monoB hfr (by rw [← hR, Res.add_comm]; exact hle)
  exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:586 mkEPair_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem mkEPair_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : ECounter} {v0 v1 : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.mkEPair rn P v0 v1) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : KeepOutB p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkEPair hidx hpwf hv0 hv1 hb =>
  rename_i r j0 j1
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_numB hi.1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_numB hi.1.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .epair (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  intro r0 hr
  rw [key, List.mem_singleton] at hr
  subst hr
  have hvr : VRRB ρ η (.epair r P) (shp (.epair (.lit 0) P)) [w0, w1] .zero := by
    simp only [VRRB]
    exact ⟨⟨hpwf, _, _, by simp [hwv0, hwv1]; exact ⟨rfl, rfl⟩⟩, by first | rfl | trivial⟩
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvr (Lay_epair th.σs r P w0 w1)
  have hfr' : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .epair (.lit 0) P, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr; exact hfr
  exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:623 KeepOutM
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def KeepOutMB (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (T : Res) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
    (stOf r.1 r.2.1 r.2.2).mem = (stOf mem pairs th).mem ∧
    (stOf r.1 r.2.1 r.2.2).promises = (stOf mem pairs th).promises ∧
    MemInvB g (CE η) (stOf r.1 r.2.1 r.2.2) ∧ ThInvREB g.lbase g.n g.i p (CE η) r.2.2 T
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:629 tgt_keepM
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_keepMB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (h : KeepOutMB p g mem pairs th η (Rf + Rs)) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨e1, e2, hm', hT'⟩ := h r hr hpa
  exact ⟨CE η, Rf + Rs, HP, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH e1 e2, hS.nie, hS.sto, hS.le, TermOwnX2.Flat.anchStep_eqsB e1 e2, hS.tyk hr (fun _ _ h => h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:637 ldpOwn_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ldpOwn_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    KeepOutMB p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv hoq
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl hoq hea rfl)
  obtain ⟨hru, hpr⟩ := pair_ru .own hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  intro r0 hr hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  have hfr0 := bindRB hb (pushRB n1 m1 (pushRB n0 m0 hi)) (RLink_ofB hE.2.1 hE.2.2)
    (VR_VRR_copy_closedB (by rfl) (by rfl) (fun k => (hE.2.1 k).1) hvr') (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl))
  have hfr : FInvRB g.lbase g.n g.i (vcons m1 (vcons m0 ρ)) η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c'
      ((x, .prod .int .int, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr0; exact hfr0
  exact ⟨f1, f4, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl),
    ⟨vcons m1 (vcons m0 ρ), η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:685 ldpPub_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ldpPub_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .pub u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    KeepOutMB p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hoq hi0 hE htv hm
  obtain ⟨hru, hpr⟩ := pair_ru .pub hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  intro r0 hr hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.two] 0 _ (s', wsr) hl
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  have hfr0 := bindRB hb (pushRB n1 m1 (pushRB n0 m0 hi)) (RLink_ofB hE.2.1 hE.2.2)
    (VR_VRR_copy_closedB (by rfl) (by rfl) (fun k => (hE.2.1 k).1) hvr') (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl))
  have hfr : FInvRB g.lbase g.n g.i (vcons m1 (vcons m0 ρ)) η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c'
      ((x, .prod .int .int, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr0; exact hfr0
  exact ⟨f1, f3, hm', ⟨vcons m1 (vcons m0 ρ), η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:728 ldpLoc_step
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ldpLoc_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    {Rf Rs : Res}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    KeepOutMB p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ hoq
      (pair_accs_cl hu) hi0 hE htv hm
  obtain ⟨-, hpr⟩ := pair_ru_loc μr hu hsku
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, haddr, ↓reduceIte, List.map_map]; rfl
  intro r0 hr hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.two] 0 _ (s', wsr) hl
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  have hfr0 := bindRB hb (pushRB n1 m1 (pushRB n0 m0 hi)) (RLink_ofB hE.2.1 hE.2.2)
    (VR_VRR_copy_closedB (by rfl) (by rfl) (fun k => (hE.2.1 k).1) hvr') (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl))
  have hfr : FInvRB g.lbase g.n g.i (vcons m1 (vcons m0 ρ)) η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c'
      ((x, .prod .int .int, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr0; exact hfr0
  exact ⟨f1, f3, hm', ⟨vcons m1 (vcons m0 ρ), η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:780 tgt_ldp
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_ldpB {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {acq : Bool} {a : At} {n0 n1 : String} {e : Expr} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .let_ y (.ldp acq a n0 n1) e) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) : TgtB p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.ldp acq a n0 n1) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hT := hS.hT
  rw [ht] at hT
  cases hT with
  | let_ hop _ =>
    cases hop with
    | ldp hpk _ _ =>
      obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc' _ hpk
      · rw [hteq] at hpk
        rcases hμ with rfl | rfl
        · exact tgt_keepMB hS (ldpOwn_stepB (hDy := hS.dy) ht hP hu hpk hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
        · exact tgt_keepMB hS (ldpPub_stepB (hDy := hS.dy) ht hP hu hpk hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
      · rw [hteq] at hpk
        exact tgt_keepMB hS (ldpLoc_stepB (hDy := hS.dy) ht hP hu hpk hμ hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:803 tgt_pstore
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_pstoreB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hnb : ∀ E1, BumpIf th E1)
    {c' : Cx} {y : String} {rel : Bool} {e : Expr} {pw w0 w1 : Word} {A : Address} {c : Cell} {m : Nat}
    {P : Proto2} {Tf Rv : Res}
    (hkey : tstep g mem pairs th = (storeUnits g.k g.arch pw A rel [.two] [w0, w1] 0 (stOf mem pairs th)).map
        fun s' => (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s'))
    (hmi : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.two] [w0, w1] 0 (stOf mem pairs th) → MemInvB g (CE η) s')
    (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset (.word2 (.lit m) P))
    (hini : Priv (CE η) A.label → IniAt (CE η).rc c A (.word2 (.lit m) P))
    (hv : EnvValRB (CE η) (.word2 (.lit m) P) [w0, w1] (Rv + Res.one (.wd m)))
    (hfr : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((y, .unit, []) :: th.env) Tf) (hle : Tf + Rv ≤ Rf)
    (he : TypedK p η c' e) (htv' : TvOK c') (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr _
  have hr0 := hr
  rw [hkey, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hT' : ThInvREB g.lbase g.n g.i p (CE η) (withS { th with term := e, env := (y, .unit, []) :: th.env } s') (Tf + Rs) :=
    ⟨ρ, η, c', Tf, Rs, rfl, hS.hE, he, htv', hfr, rfl, hRPc, hDy.wit rfl⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h0 := hS.le
  simp only [Res.add_apply] at h1 h0
  by_cases hq : Priv (CE η) A.label
  · have hq' := hq
    obtain ⟨⟨c0, hc0, hown0⟩, hpfN⟩ := hq'
    have ec : some c0 = some c := hc0.symm.trans hsto
    cases ec
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := TermOwnHeldQ.Flat.heldStoreAtPB (us := [.two]) hS.hm hS.hH hq hsto
      hown0 (NVP_priv hq) (OwnOKPF_cellPB hS.hm.2.1 hsto hown0 hpfN) hat (hini hq) (fun N e h => by cases h) hv
      (by simp [wc, accs, nWords, Acc.size]) rfl
    refine ⟨CE η, Tf + Rs, R2 + H0, hT', hmi s' hs', hput g.k g.arch pw rel _ rfl rfl
      (LoadCoh_of_eqB hS.hm.2.1 rfl) (fun _ => Nat.le_refl _) hS.hm.2.2.2.2.1 s' hs', hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr0 (fun _ _ h => h)⟩
    have h2 := congrArg (fun R : Res => R (.own x)) hRe
    simp only [Res.add_apply] at h2 ⊢
    have h3 : (Res.one (.wd m)) (.own x) = 0 := by simp [Res.one]
    omega
  · refine ⟨CE η, Tf + Rs, HP, hT', hmi s' hs', TermOwnHeldQ.Flat.memHeldOn_storeB hS.hH (fun l hl e => hq (e ▸ hl))
      hS.hm.2.2.1 hs', hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr0 (fun _ _ h => h)⟩
    simp only [Res.add_apply]
    omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:844 stpPtr_tgt
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stpPtr_tgtB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    {c₁ c' : Cx} {y : String} {rel : Bool} {a v0 v1 tk : At}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause2}
    (hterm : th.term = .let_ y (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hr : EqI c₁ r r') (hj0 : IntIdx c₁ v0 j0)
    (hj1 : IntIdx c₁ v1 j1) (hst : InState2 c₁ P j0 j1 c₂ k0' k1') (hcl : P.clauses[c₂]? = some cl')
    (hxt : (xt = .unit ∧ cl'.holds = true) ∨ (xt = .tok2 r' P j0 j1 ∧ cl'.holds = false))
    (hb : c₁.bind y xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c') (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : TgtB p g x n (CE η) mem pairs th := by
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi.1
  have ho : cx.opaqueOK (.word2 r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hcellW : ∀ {c : Cell}, Fd c.ty (cl ρ η.wit 0 0 (.word2 r P)) →
      c.ty = .word2 (.lit (ev ρ r)) P := fun hcty => by
    have h' := hcty; simp only [cl, clI_zero] at h'; exact Fd_word2_eq h'
  rcases hμ with rfl | rfl
  · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi.1 hpk htv ho
    have hct := hcellW hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word2 (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs]))
    have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
    have hpwf : pwf2 P = true := by
      obtain ⟨-, -, -, -, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
        hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
        (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
        (peek_cell_lytB hi.1.2.1 hpk hea rfl rfl).2 hsig
        (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.1.2.2.2.1 hi.1.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.1.2.1 htv hpk rfl ho hea rfl)
      obtain ⟨_, hvr0, -⟩ := hstw
      simp only [VRF, VRb2] at hvr0; exact hvr0.1
    obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
      stp_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
    have husA : accs c.ty = some [Acc.two] := by rw [hct]; simp [accs]
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
    exact tgt_pstoreB (hDy := hDy.letW hterm rfl) hS (TermOwnX2.bumpIf_nb hterm) (A := ⟨lab, 0⟩) key (fun s' hs' => MemInv_storeB hm hsto hown husA hval rfl s' hs')
      hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h) ⟨hvR _ _, by simp [Valid]⟩ hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
  · obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, -, hsku, -⟩ := pubPtr_viewB hi.1 hpk htv ho
    have hct := hcellW hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word2 (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs]))
    have hpwf : pwf2 P = true := by
      obtain ⟨_, _, _, _, -, -, -, -, -, -, _, hvr0⟩ :=
        loadPub_coreB (p := p) (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi.1 hE htv hm
      simp only [VRF, VRb2] at hvr0; exact hvr0.1
    obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
      stp_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
    have husc : accs c.ty = some [.two] := by rw [hct]; simp [accs]
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
    refine tgt_pstoreB (hDy := hDy.letW hterm rfl) hS (TermOwnX2.bumpIf_nb hterm) (A := ⟨lab, 0⟩) key (fun s' hs' => ?_) hsto hat
      (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h) ⟨hvR _ _, by simp [Valid]⟩ hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
    by_cases hown : c.owner = some η.tid
    · exact MemInv_storeFB hm hsto hown husc hval rfl s' hs'
    · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
      exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc rfl s' hs'
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:914 stpLoc_tgt
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stpLoc_tgtB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    {c₁ c' : Cx} {y : String} {rel : Bool} {a v0 v1 tk : At}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause2}
    (hterm : th.term = .let_ y (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hr : EqI c₁ r r') (hj0 : IntIdx c₁ v0 j0)
    (hj1 : IntIdx c₁ v1 j1) (hst : InState2 c₁ P j0 j1 c₂ k0' k1') (hcl : P.clauses[c₂]? = some cl')
    (hxt : (xt = .unit ∧ cl'.holds = true) ∨ (xt = .tok2 r' P j0 j1 ∧ cl'.holds = false))
    (hb : c₁.bind y xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c') (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : TgtB p g x n (CE η) mem pairs th := by
  have hi := hS.hF
  have hE := hS.hE
  have hm := hS.hm
  have hi0 := hi.1
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi0
  have hus2 : accs (cl ρ η.wit 0 0 (.word2 r P)) = some [.two] := pair_accs_cl (wit := η.wit) (Or.inl ⟨r, P, rfl⟩)
  have hcell : cellOf (Ty.loc μ (.word2 r P)) = some (μ, .word2 r P) := by simp [cellOf]
  have hpwf : pwf2 P = true := by
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, _, hvr0⟩ :=
      locCellB (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus2 hi0 hE hS.tv hm
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ := cell_targetB (bkG := False) hcell (Fd_noarr (by rw [hus2]; simp)) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs (.word2 r P))) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hat' : AtOff c.ty ad.offset (.word2 (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero] using hat
  have hini' : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word2 (.lit (ev ρ r)) P) := fun hq => by
    rcases hμ with rfl | rfl
    · have h2 : IniAt (modeIni .own η.ini η.rini) c ad (.word2 (.lit (ev ρ r)) P) := by
        simpa only [cl, clI_zero] using hini
      exact h2
    · simp only [ModeOKF, ModeOKb] at hmode
      obtain ⟨f, hf, -⟩ := hmode
      have := hq.2; simp only [CE] at this; rw [this] at hf; cases hf
  obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
    stp_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
  have hval := storeWord2_valB (η := η) (r := r) hpwf hi1.1 hst hwv0 hwv1
  have hna : ∀ N e, cl ρ η.wit 0 0 (.word2 r P) ≠ .array (.lit N) e := fun N e h => by simp [cl] at h
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  refine tgt_pstoreB (hDy := hDy.letW hterm rfl) hS (TermOwnX2.bumpIf_nb hterm) (A := ad) key (fun s' hs' => ?_) hsto hat' hini' ⟨hvR _ _, by simp [Valid]⟩
    hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtIB hm hsto hown hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hna hval hus2 rfl s' hs'
  · have hpub : μ = .pub := by
      rcases hμ with rfl | rfl
      · exact absurd hmode hown
      · rfl
    subst hpub
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval hus2 rfl s' hs'
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:976 tgt_stp
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_stpB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {rel : Bool} {a v0 v1 tk : At} {e : Expr} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hP : ProgT p) (ht : th.term = .let_ y (.stp rel a v0 v1 tk) e) (hRP : RetPw th.σs th.stack cx.ret) : TgtB p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.stp rel a v0 v1 tk) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hT := hS.hT
  have hCkL := hS.ck
  rw [ht] at hT hCkL
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
  have htv' := OpT_TvOK hP hop hS.tv
  cases hop with
  | stpGive hp hw hu hr hj0 hj1 _ _ hst hcl _ _ hh _ hb =>
    obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpPtr_tgtB (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpLoc_tgtB (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
  | stpKeep hp hw hu hr hj0 hj1 _ _ hst hcl _ _ hh hb =>
    obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpPtr_tgtB (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inr ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpLoc_tgtB (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inr ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1012 RmwCell
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def RmwCellB (η : TEnv) (x : AllocLabel) (s s1 : St) (ad : Address) (us : List Acc) (ws : List Word) : Prop :=
  ¬ Priv (CE η) ad.label ∨ LoadCohB (CE η) s s1 ∧ SeenLE (CE η) s1.vs.vRelSt ∧
    ∃ c U Rv, η.sto ad.label = some c ∧ AtOff c.ty ad.offset U ∧
    (Priv (CE η) ad.label → IniAt (CE η).rc c ad U) ∧ (∀ N e, U ≠ .array (.lit N) e) ∧
    EnvValRB (CE η) U ws Rv ∧ wc U = some (nWords us) ∧ ws.length = nWords us ∧ Rv (.own x) = 0
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1020 RmwOut
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def RmwOutB (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (x : AllocLabel)
    (m : Nat) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot, ThInvREB g.lbase g.n g.i p (CE η) r.2.2 Tot ∧
    MemInvB g (CE η) (stOf r.1 r.2.1 r.2.2) ∧ Tot (.own x) ≤ m ∧
    (((stOf r.1 r.2.1 r.2.2).mem = (stOf mem pairs th).mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = (stOf mem pairs th).promises) ∨
    ∃ s1 s2 pw ad rel us ws, s1.mem = (stOf mem pairs th).mem ∧ s1.promises = (stOf mem pairs th).promises ∧
      s2 ∈ storeUnits g.k g.arch pw ad rel us ws 0 s1 ∧
      (stOf r.1 r.2.1 r.2.2).mem = s2.mem ∧ (stOf r.1 r.2.1 r.2.2).promises = s2.promises ∧
      RmwCellB η x (stOf mem pairs th) s1 ad us ws)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1031 tgt_rmw
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_rmwB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP) (hnb : ∀ E1, BumpIf th E1)
    (h : RmwOutB p g mem pairs th η x ((Rf + Rs) (.own x))) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨Tot, hT', hm', hle, hk | ⟨s1, s2, pw, ad, rel, us, ws, e1, e2, hs2, e3, e4, hcell⟩⟩ :=
    h r hr hpa
  · exact ⟨CE η, Tot, HP, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH hk.1 hk.2, hS.nie, hS.sto,
      by have := hS.le; omega, TermOwnX2.Flat.anchStep_eqsB hk.1 hk.2, hS.tyk hr (fun _ _ h => h)⟩
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨hlc, hsl, c, U, Rv, hsto, hat, hini, hna, hv, hwU, hlen, hRv⟩ := hcell.resolve_left (fun h => h hq)
    have hq' := hq
    obtain ⟨⟨c0, hc0, hown0⟩, hpfN⟩ := hq'
    have ec : some c0 = some c := hc0.symm.trans hsto
    cases ec
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := TermOwnHeldQ.Flat.heldStoreAtPB hS.hm hS.hH hq hsto
      hown0 (NVP_priv hq) (OwnOKPF_cellPB hS.hm.2.1 hsto hown0 hpfN) hat (hini hq) hna hv hwU hlen
    refine ⟨CE η, Tot, R2 + H0, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB
      (hput g.k g.arch pw rel s1 e1 e2 hlc hlc.2.2 hsl s2 hs2) e3 e4, hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr (fun _ _ h => h)⟩
    have h2 := congrArg (fun R : Res => R (.own x)) hRe
    have h0 := hS.le
    simp only [Res.add_apply] at h2 h0 hle ⊢
    omega
  · have hpl : PromLt s1 := fun t ht => by rw [e1]; rw [e2] at ht; exact hS.hm.2.2.1 t ht
    have hH1 : MemHeldPB (CE η) s1 HP := TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH e1 e2
    exact ⟨CE η, Tot, HP, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB
      (TermOwnHeldQ.Flat.memHeldOn_storeB hH1 (fun l hl e => hq (e ▸ hl)) hpl hs2) e3 e4, hS.nie, hS.sto,
      by have := hS.le; simp only [Res.add_apply] at this hle ⊢; omega, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr (fun _ _ h => h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1060 pub_npriv
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pub_nprivB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {t u rt : Ty} {pw : Word} {ad : Address} (hi : FInvB glb gnum gi ρ η σs K cx env)
    (hpk : cx.peek w = .ok t) (hc : cellOf t = some (.pub, u)) (hna : accs (cl ρ η.wit 0 0 u) ≠ none)
    (hea : evalAt env w = some (rt, [pw])) (haddr : addrOf pw = some ad) : ¬ Priv (CE η) ad.label := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  obtain ⟨ad', c, hws, -, -, hmode, -⟩ := cell_targetB (bkG := False) hc (Fd_noarr hna) hv
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨-, rfl⟩ := hea'
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have e : ad = ad' := by simp only [addrOf, hws, Option.some.injEq] at haddr; exact haddr.symm
  subst e
  simp only [ModeOKF, ModeOKb] at hmode
  obtain ⟨f, hf, -⟩ := hmode
  intro hq
  have h2 := hq.2
  simp only [CE] at h2
  rw [h2] at hf
  cases hf
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1080 loadCoh_bump
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem loadCoh_bumpB {E : TEnv} {s s1 : St} (X : Ts) (h : LoadCohB E s s1) : LoadCohB E s (bumpRel s1 X) :=
  ⟨OwnOKSF_congrB h.1 (fun _ _ _ _ _ => rfl), h.2.1, h.2.2⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1084 fetchCell_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem fetchCell_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {tw tv : Ty} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .let_ y (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok tw) (hcw : cellOf tw = some (.pub, .int))
    (hu : cx.use v = .ok (tv, c₁)) (hsub : SubS c₁ tv .int) (hb : c₁.bind y .int = .ok c')
    (he : TypedK p η c' e) (htv' : TvOK c')
    (hFC : FetchIntCellB g mem pairs th η acq rel a)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hRL := RLink_ofB hE.2.1 hE.2.2
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hvi := VR_subB (bkG := False) hi1.1.1 hsub _ _ hvv
  simp only [VRF, VRb2] at hvi
  obtain ⟨dd, hdd⟩ := hvi
  obtain ⟨nw, rfl, hnw⟩ := map_singleton hdd
  obtain ⟨ad, pw, rt, hea, haddr, hrt, hne, hcell⟩ := hFC
  have hnp := pub_nprivB hi.1 hpk hcw (by simp [cl, accs]) hea haddr
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (y, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨hm1, ⟨n, hn⟩, hst⟩ := hcell s1 [rd] hl1 hp1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
  obtain ⟨k, hk⟩ := FetchOp.apply_num o n dd
  rw [hnw] at hs2
  have hkv : (cst (o.kind.apply rd.val (.num dd))).val = .num k := by
    simp [cst, Promises.TVal.mk0, hn, hk]
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  have hm1b := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
  have hfr := bindRB hb hi1 hRL (show VRRB ρ η .int (shp .int) [rd] .zero by simp [VRRB, hn]) (Lay_int rd rfl)
  have hmi := MemInv_sameB (MemInv_lockSB g.arch
    (MemInv_setRelB (hst _ hm1b _ ⟨k, hkv⟩ s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame
  subst hrd
  refine ⟨Rr + .zero + Rs, ⟨ρ, η, c', Rr + .zero, Rs, rfl, hE, he, htv', (by rw [hrt]; exact hfr), rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩, hmi, ?_,
    Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
      hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inl hnp⟩⟩
  have h1 := Res.le_def.1 hle (.own xk)
  simp only [Res.add_apply, Res.zero_apply] at h1 ⊢
  omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1139 cellTargetP
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem cellTargetPB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {t u rt : Ty} {μ : Mode} {pw : Word} {ad : Address} (hi : FInvB glb gnum gi ρ η σs K cx env)
    (hpk : cx.peek w = .ok t) (hc : cellOf t = some (μ, u)) (hμ : μ = .own ∨ μ = .pub)
    (hna : accs (cl ρ η.wit 0 0 u) ≠ none)
    (hea : evalAt env w = some (rt, [pw])) (haddr : addrOf pw = some ad) :
    ∃ c, η.sto ad.label = some c ∧ AtOff c.ty ad.offset (cl ρ η.wit 0 0 u) ∧
      (Priv (CE η) ad.label → IniAt (CE η).rc c ad (cl ρ η.wit 0 0 u)) := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  obtain ⟨ad', c, hws, hsto, hat, hmode, hini⟩ := cell_targetB (bkG := False) hc (Fd_noarr hna) hv
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨-, rfl⟩ := hea'
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have e : ad = ad' := by simp only [addrOf, hws, Option.some.injEq] at haddr; exact haddr.symm
  subst e
  refine ⟨c, hsto, hat, fun hq => ?_⟩
  rcases hμ with rfl | rfl
  · exact hini
  · simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    have h2 := hq.2
    simp only [CE] at h2
    rw [h2] at hf
    cases hf
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1169 fetchW_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem fetchW_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {c : Cell} {n : Nat} {P : Proto} {pw nw : Word} {rt rv : Ty} {dd : Nat}
    {Rf Rs : Res} {xk : AllocLabel} {Q : List Word → Prop} {SOK : Word → Prop}
    (hterm : th.term = .let_ y (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
      MemInvB g (CE η) s1 ∧ Q ws ∧ ∀ s1', MemInvB g (CE η) s1' → ∀ w, SOK w →
        ∀ s2, s2 ∈ storeUnits g.k g.arch pw ad rel [.one] [w] 0 s1' → MemInvB g (CE η) s2)
    (hsto : η.sto ad.label = some c) (hat : AtOff c.ty ad.offset (.word (.lit n) P))
    (hini : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word (.lit n) P)) (hpwf : pwf P = true)
    (hg : P.ghost = false)
    (hpost : ∀ rd, Q [rd] → SOK (cst (o.kind.apply rd.val (.num dd))) ∧
      (∃ k, o.kind.apply rd.val (.num dd) = .num k ∧ InP P k) ∧
      ∃ ρ' cx' Rok, TypedK p η cx' e ∧ TvOK cx' ∧ RetPw th.σs th.stack cx'.ret ∧
        FInvRB g.lbase g.n g.i ρ' η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx' ((y, fetchRtTy rt, [rd]) :: th.env) Rok ∧
        Rok (.own xk) ≤ Rf (.own xk))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (y, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨hm1, hq, hst⟩ := hcell s1 [rd] hl1 hp1
  obtain ⟨hsok, ⟨k, happ, hink⟩, ρ', cx', Rok, he', htv', hRPx, hi', hres⟩ := hpost rd hq
  rw [hnw] at hs2
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  have hm1b := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
  have hlc := loadCoh_bumpB (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
    (LoadCoh_loadB hl1 hp1 hm.2.1 ⟨c, hsto⟩)
  subst hrd
  refine ⟨Rok + Rs, ⟨ρ', η, cx', Rok, Rs, rfl, hE, he', htv', hi', rfl, hRPx, hDy.letW hterm rfl⟩,
    MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB (hst _ hm1b _ hsok s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame, ?_,
    Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
      hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inr ⟨hlc, hm1b.2.2.2.2.1, c, _, _, hsto, hat, hini,
        (fun N e h => by cases h),
        ⟨VRR_word_ofB hpwf ⟨k, by simp [cst, Promises.TVal.mk0, happ], hink⟩, by simp [Valid]⟩,
        by simp [wc, accs, nWords, Acc.size, hg], rfl, wrW_own _ _ _ _⟩⟩⟩
  simp only [Res.add_apply]
  omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1225 fetchWord_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem fetchWord_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {tw : Ty} {μ : Mode} {r j : Idx} {P : Proto} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .let_ y (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok tw) (hcw : cellOf tw = some (μ, .word r P)) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hpwf : pwf P = true) (hFC : FetchCellB g mem pairs th ρ η acq rel a r P)
    (ho : o = .add) (hj : IntIdx cx v j)
    (hcase : (P.epoch = true ∧ EqI cx j (.lit 1) ∧ cx.bind y (fetchEpochTy r P) = .ok c') ∨
      (∃ d, P.epoch = false ∧ EqI cx j (.lit d) ∧ fetchOK P d = true ∧ cx.bind y .int = .ok c'))
    (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  subst ho
  have hRL := RLink_ofB hE.2.1 hE.2.2
  obtain ⟨ad, pw, rt, r', hea, haddr, hwo, hne, hcell⟩ := hFC
  obtain ⟨c, hsto, hat, hini⟩ := cellTargetPB hi.1 hpk hcw hμ (by simp [cl, accs, hg]) hea haddr
  have hcl : cl ρ η.wit 0 0 (.word r P) = .word (.lit (ev ρ r)) P := by simp [cl, clI_zero]
  rw [hcl] at hat hini
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.1.2.1 htvk hjo
  rcases hcase with ⟨hep, heq, hb⟩ | ⟨d, hep, heq, hok, hb⟩
  · have hj1 := heq ρ hi.1.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    have hrt : fetchRtTy rt = fetchEpochTy r' P := by simp [fetchRtTy, hwo, hep]
    refine fetchW_outB (hDy := hDy) hterm hea haddr hev hnwv hcell hsto hat hini hpwf hg (fun rd hq => ?_) hE hm
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    have happ : (FetchOp.add).kind.apply rd.val (.num 1) = .num (n + 1) := by
      simp [hn, FetchOp.kind, WeakMem.RmwKind.apply]
    refine ⟨wordValB hpwf (m := n + 1) (by simp [cst, Promises.TVal.mk0, happ]) (InP_epoch hpwf hep (n + 1)),
      ⟨n + 1, happ, InP_epoch hpwf hep (n + 1)⟩, ρ, c', Rf + .one (.ep (ev ρ r) (n + 1)), he, htv', (by rw [bind_ret hb]; exact hRP), ?_,
      by simp [Res.add_apply, Res.one]⟩
    rw [hrt]
    exact bindRB hb hi hRL (VRR_fetchEpochB hn) (Lay_fetchEpoch _ r r' P rd)
  · have hjd := heq ρ hi.1.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    have hrt : fetchRtTy rt = .int := by simp [fetchRtTy, hwo, hep]
    refine fetchW_outB (hDy := hDy) hterm hea haddr hev hnwv hcell hsto hat hini hpwf hg (fun rd hq => ?_) hE hm
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, hin⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    have happ : (FetchOp.add).kind.apply rd.val (.num d) = .num (n + d) := by
      simp [hn, FetchOp.kind, WeakMem.RmwKind.apply]
    refine ⟨wordValB hpwf (m := n + d) (by simp [cst, Promises.TVal.mk0, happ]) (InP_fetch hok hin),
      ⟨n + d, happ, InP_fetch hok hin⟩, ρ, c', Rf + .zero, he, htv', (by rw [bind_ret hb]; exact hRP), ?_, by simp [Res.add_apply]⟩
    rw [hrt]
    exact bindRB hb hi hRL (show VRRB ρ η .int (shp .int) [rd] .zero by simp [VRRB, hn]) (Lay_int rd rfl)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1279 fetchRef_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem fetchRef_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {acq rel : Bool} {a v : At} {e : Expr}
    {t : Ty} {μ : Mode} {r j : Idx} {P : Proto} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .let_ y (.fetch .add acq rel a v) e)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P)) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false) (hpwf : pwf P = true) (hj : IntIdx cx v j)
    (hcase : (P.epoch = true ∧ EqI cx j (.lit 1) ∧ cx.bind y (fetchEpochTy r P) = .ok c') ∨
      (∃ d, P.epoch = false ∧ EqI cx j (.lit d) ∧ fetchOK P d = true ∧ cx.bind y .int = .ok c'))
    (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  rcases ht with rfl | rfl
  · obtain ⟨lab, pw, μ', r', hea, hpw, hne, hcell⟩ :=
      wordCellFB (bkG := False) (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hμ hg hi.1 hE htv hm
    exact fetchWord_outB (hDy := hDy) hterm hp rfl hμ hg hpwf ⟨⟨lab, 0⟩, pw, _, r', hea, by simp [addrOf, hpw], rfl, hne, hcell⟩
      rfl hj hcase he htv' hi hE hm hRP
  · have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, -⟩ :=
      locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi.1 hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    exact fetchWord_outB (hDy := hDy) hterm hp rfl hμ hg hpwf ⟨ad, pw, _, r', hea, haddr, rfl, hne,
        fun s1 ws hl hp => ⟨(hld s1 ws hl hp).2.2, (hld s1 ws hl hp).1,
          fun s1' hm1' w hw s2 hs2 => hsto s1' [w] hm1' hw rfl s2 hs2⟩⟩
      rfl hj hcase he htv' hi hE hm hRP
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1307 tgt_fetch
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_fetchB {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .let_ y (.fetch o acq rel a v) e) (hRP : RetPw th.σs th.stack cx.ret) : TgtB p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.fetch o acq rel a v) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hT := hS.hT
  have hCkL := hS.ck
  rw [ht] at hT hCkL
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
  have htv' := OpT_TvOK hP hop htv
  refine tgt_rmwB hS (TermOwnX2.bumpIf_nb ht) ?_
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      rcases hc with hc | ⟨r, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨lab, pw, ru, hea, hpw, hnwr, hne, hcell⟩ :=
          pubIntCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hi.1 hE htv hm
        have hrt : fetchRtTy (.ptr .pub ru) = .int := by
          cases ru <;> simp [fetchRtTy, wordOf]
          exact (hnwr _ _ rfl).elim
        exact fetchCell_outB (hDy := hS.dy) ht hp rfl hu hsub hb ⟨he, hck⟩ htv'
          ⟨⟨lab, 0⟩, pw, _, hea, by simp [addrOf, hpw], hrt, hne, hcell⟩ hi hE hRP
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        rcases hμ with h | h <;> cases h
    · subst hteq
      rcases hc with hc | ⟨r, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
        obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, -⟩ :=
          locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp (Or.inr rfl)
            (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi.1 hE htv hm
        have hrt : fetchRtTy (.loc μr ru) = .int := by
          cases ru <;> simp [fetchRtTy, wordOf]
          simp [skel, etok, close, substTs] at hsku
        refine fetchCell_outB (hDy := hS.dy) ht hp rfl hu hsub hb ⟨he, hck⟩ htv'
          ⟨ad, pw, _, hea, haddr, hrt, hne, fun s1 ws hl hp => ?_⟩ hi hE hRP
        obtain ⟨hvr, -, hm1⟩ := hld s1 ws hl hp
        exact ⟨hm1, by simpa [VRF, VRb2] using hvr, fun s1' hm1' w ⟨m, hw⟩ s2 hs2 =>
          hsto s1' [w] hm1' (intValB (ρ := ρ) hw) rfl s2 hs2⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp <;> subst hteq <;>
    · cases u <;> simp [wordOf] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rename_i r P
      have hpwf := wordRef_pwfB hp (by first | exact .inl rfl | exact .inr rfl) hμ hi.1 hE htv hm
      have hg : P.ghost = false := by
        have := pwf_epochOK hpwf hep
        unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1.2
      exact fetchRef_outB (hDy := hS.dy) ht hp (by first | exact .inl rfl | exact .inr rfl) hμ hg hpwf hj (.inl ⟨hep, heq, hb⟩)
        ⟨he, hck⟩ htv' hi hE htv hm hS.rp
  | fetchShare hp hw hep hj heq hok hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp <;> subst hteq <;>
    · cases u <;> simp [wordOf] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rename_i r P
      have hpwf := wordRef_pwfB hp (by first | exact .inl rfl | exact .inr rfl) hμ hi.1 hE htv hm
      have hg : P.ghost = false := by
        have hok' := hok
        unfold fetchOK at hok'; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok'
        exact hok'.1.1.1.1
      exact fetchRef_outB (hDy := hS.dy) ht hp (by first | exact .inl rfl | exact .inr rfl) hμ hg hpwf hj
        (.inr ⟨_, hep, heq, hok, hb⟩) ⟨he, hck⟩ htv' hi hE htv hm hS.rp
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1399 casW_core
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem casW_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {P : Proto} {n : Nat} {ad : Address} {c : Cell} {pw ew nw : Word} {rw rte rtv : Ty}
    {Rf Rs Rok : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hea : evalAt th.env w = some (rw, [pw])) (haddr : addrOf pw = some ad)
    (hee : evalAt th.env e = some (rte, [ew])) (hev : evalAt th.env v = some (rtv, [nw]))
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
        MemInvB g (CE η) s1 ∧ ∀ s1', MemInvB g (CE η) s1' →
          ∀ s2, s2 ∈ storeUnits g.k g.arch pw ad rel [.one] [nw] 0 s1' → MemInvB g (CE η) s2)
    (hsto : η.sto ad.label = some c) (hat : AtOff c.ty ad.offset (.word (.lit n) P))
    (hini : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word (.lit n) P)) (hg : P.ghost = false)
    (hpwf : pwf P = true) (hnin : ∃ k, nw.val = .num k ∧ InP P k)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, haddr]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  have hp1 := hpS (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 hp1
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb]
    exact ⟨Rf + Rs, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hfail, htv, hi, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame,
      Nat.le_refl _, Or.inl ⟨hsame.1.trans ((lockS_memP _ _).1.trans f1),
        hsame.2.2.2.1.trans ((lockS_memP _ _).2.trans f2)⟩⟩
  · have hb : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb, ite_true]
    have hm1b := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
    have hlc := loadCoh_bumpB (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
      (LoadCoh_loadB hl1 hp1 hm.2.1 ⟨c, hsto⟩)
    obtain ⟨k, hk, hink⟩ := hnin
    refine ⟨Rok + Rs, ⟨ρ, η, cok, Rok, Rs, rfl, hE, hok, htvok, hiok, rfl, hRPo, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB (hst2 _ hm1b s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame, ?_,
      Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
        hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inr ⟨hlc, hm1b.2.2.2.2.1, c, _, _, hsto, hat, hini,
          (fun N e h => by cases h), ⟨VRR_word_ofB hpwf ⟨k, hk, hink⟩, by simp [Valid]⟩,
          by simp [wc, accs, nWords, Acc.size, hg], rfl, wrW_own _ _ _ _⟩⟩⟩
    simp only [Res.add_apply]
    omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1455 casW_mid
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem casW_midB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {tw : Ty} {μ : Mode} {r i j k' : Idx} {P : Proto} {c₂ : Nat} {Rf Rs Rok : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (μ, .word r P)) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false) (hpwf : pwf P = true)
    (hie : IntIdx cx e i) (hj : IntIdx cx v j) (hst : InState cx P j c₂ k')
    (hcellL : ∀ nw : Word, nw.val = .num (ev ρ j) → CasCellB g mem pairs th η acq rel w nw)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  obtain ⟨te, hte, hio⟩ := hie
  obtain ⟨rte, ew, hee, hewv, -⟩ := atom_numB hi.1.2.1 hte hio
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.1.2.1 htvk hjo
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := hcellL nw hnwv
  obtain ⟨c, hsto, hat, hini⟩ := cellTargetPB hi.1 hpk hcw hμ (by simp [cl, accs, hg]) hea haddr
  have hcl : cl ρ η.wit 0 0 (.word r P) = .word (.lit (ev ρ r)) P := by simp [cl, clI_zero]
  rw [hcl] at hat hini
  exact casW_coreB (hDy := hDy) hterm hea haddr hee hev hcell hsto hat hini hg hpwf ⟨_, hnwv, InP_of_st hi.1.1 hst⟩
    hok htvok hiok hres hfail hi hE htv hm hRP hRPo
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1481 casW_typed
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem casW_typedB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {tw : Ty} {μ : Mode} {r : Idx} {P : Proto} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (μ, .word r P)) (hwo : wordOf tw = some (r, P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false) (hpwf : pwf P = true)
    (hL : ∀ {j k' : Idx} {c₂ : Nat}, InState cx P j c₂ k' → ∀ nw : Word, nw.val = .num (ev ρ j) →
      CasCellB g mem pairs th η acq rel w nw)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hRL := RLink_ofB hE.2.1 hE.2.2
  have hT0 := hT
  rw [hterm] at hT0 hCk
  cases TermA4.CkW_inv_cas hCk with
  | casCell hp hnw => exfalso; rw [hpk] at hp; cases hp; rw [hwo] at hnw; cases hnw
  | casShare hp hw _ hie hj hsti hcl hst hcl' hh _ hh' hlend hok hfail =>
    rw [hpk] at hp; cases hp
    rw [hwo] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have htv2 := LendCx_TvOK hlend htv
    cases hlend with
    | none hsm hb =>
      have hiok := bindRB hb hi hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
      exact casW_midB (hDy := hDy) hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv2 hiok
        (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    | up hsm _ hb =>
      have hiok := bindRB (rt := .unit) (ws := []) (R := .one (.sh (ev ρ r))) hb hi hRL rfl (Lay_etok_unit rfl)
      exact casW_midB (hDy := hDy) hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv2 hiok
        (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    | down _ _ _ _ hu hb =>
      obtain ⟨-, -, R, Rr, -, -, -, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
      have hiok := bindRB hb hi1 hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
      exact casW_midB (hDy := hDy) hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv2 hiok
        (by have := Res.le_def.1 hle (.own xk); simp only [Res.add_apply, Res.zero_apply] at this ⊢; omega)
        hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | casTake hp hw hgh hie hj hsti hcl hst hcl' hh hstp hh' hl1 hl2 hacq hb hok hfail =>
    rw [hpk] at hp; cases hp
    rw [hwo] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hiok := bindRB (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    have htv' := (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1
    split at hok
    · exact casW_midB (hDy := hDy) hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv' hiok
        (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    · exact casW_midB (hDy := hDy) hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv' hiok
        (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | casEpoch hp hw hep hacq hie hj hsti hst hstep hb hok hfail =>
    rw [hpk] at hp; cases hp
    rw [hwo] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hiok := bindRB (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    exact casW_midB (hDy := hDy) hterm hpk hcw hμ hg hpwf hie hj hst (hL hst)
      hok.tk (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok
      (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1535 casC_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem casC_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c₂ : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {tw : Ty} {u te tv : Ty} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (.pub, u)) (hone : u.rawWords = some 1)
    (hpe : cx.peek e = .ok te) (hu : cx.use v = .ok (tv, c₁))
    (hsube : SubS c₁ te u) (hsubv : SubS c₁ tv u) (hb : c₁.bind t .unit = .ok c₂)
    (hok : TypedK p η c₂ ok) (hfail : TypedK p η c₁ fail)
    (hcellL : ∀ nw, EnvValB (CE η) (cl ρ η.wit 0 0 u) [nw] → CasCellB g mem pairs th η acq rel w nw)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hRL := RLink_ofB hE.2.1 hE.2.2
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) hcw
  have hus : accs (cl ρ η.wit 0 0 u) = some [.one] := accs_cl_one hone
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have htv1 := (use_TvOK hu htv).1
  obtain ⟨hval, hlen⟩ := ownStoreValB (ru := cl ρ η.wit 0 0 u) hE.2.1 hi.1.2.2.2.1 hi.1.2.2.2.2.1 hi1.1.1
    hsubv ho htb hvv hlv rfl hus
  obtain ⟨nw, rfl⟩ := len_one hlen
  obtain ⟨rte, wse, hee, hve, hle'⟩ := peek_VRB (bkG := False) hi.1.2.1 hpe
  obtain ⟨hve1, hlene⟩ := ownStoreValB (ru := cl ρ η.wit 0 0 u) hE.2.1 hi.1.2.2.2.1 hi.1.2.2.2.2.1 hi1.1.1
    hsube ho htb hve hle' rfl hus
  obtain ⟨ew, rfl⟩ := len_one hlene
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := hcellL nw hval
  have hnp := pub_nprivB hi.1 hpk hcw (by rw [hus]; simp) hea haddr
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, haddr]; rfl
  have h1 := Res.le_def.1 hle (.own xk)
  simp only [Res.add_apply] at h1
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb']
    exact ⟨Rr + Rs, ⟨ρ, η, c₁, Rr, Rs, rfl, hE, hfail, htv1, hi1, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame,
      by simp only [Res.add_apply]; omega, Or.inl ⟨hsame.1.trans ((lockS_memP _ _).1.trans f1),
        hsame.2.2.2.1.trans ((lockS_memP _ _).2.trans f2)⟩⟩
  · have hb' : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb', ite_true]
    have hm1b := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
    have hfr := bindRB hb hi1 hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    exact ⟨Rr + .zero + Rs, ⟨ρ, η, c₂, Rr + .zero, Rs, rfl, hE, hok,
      (bind_TvOK hb htv1 (by simp [tb]) (by simp [mg])).1, (by exact hfr), rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB (hst2 _ hm1b s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame,
      by simp only [Res.add_apply, Res.zero_apply]; omega,
      Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
        hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inl hnp⟩⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1597 tgt_cas
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_casB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .cas acq rel w e v t ok fail) (hRP : RetPw th.σs th.stack cx.ret) : TgtB p g x n (CE η) mem pairs th := by
  have hsc' : StepScope cx (.cas acq rel w e v t ok fail) :=
    stepScope_of (by rw [← ht]; exact hS.sc) (fun _ _ _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hT := hS.hT
  have hCk0 := hS.ck
  refine tgt_rmwB hS (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [ht] at h; cases h) ?_
  have hT0 := hT
  rw [ht] at hT0 hCk0
  have hcasW : ∀ {μ r P}, (cx.peek w = .ok (.ptr μ (.word r P)) ∨ cx.peek w = .ok (.loc μ (.word r P))) →
      (μ = .own ∨ μ = .pub) → P.ghost = false → RmwOutB p g mem pairs th η x ((Rf + Rs) (.own x)) := by
    intro μ r P hpk hμ hg
    rcases hpk with hpk | hpk
    · exact casW_typedB (hDy := hS.dy) ht hpk rfl rfl hμ hg (wordRef_pwfB hpk (.inl rfl) hμ hi.1 hE htv hm)
        (fun hst nw hnwv => by
          obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := casWordCellB (acq := acq) (rel := rel) (g := g)
            (mem := mem) (pairs := pairs) hpk hμ hg hst hnwv hi.1 hE htv hm
          exact ⟨⟨lab, 0⟩, pw, rw, hea, by simp [addrOf, hpw], hne, hcell⟩) hT hS.ck hi hE htv hm hRP
    · exact casW_typedB (hDy := hS.dy) ht hpk rfl rfl hμ hg (wordRef_pwfB hpk (.inr rfl) hμ hi.1 hE htv hm)
        (fun hst _ hnwv => wordLocCellB (acq := acq) (rel := rel) (g := g)
          (mem := mem) (pairs := pairs) hpk hμ hg hst hnwv hi.1 hE htv hm) hT hS.ck hi hE htv hm hRP
  cases TermA4.CkW_inv_cas hCk0 with
  | casCell hpk hnw0 hc hone haff hpe hu hsube hsubv _ hb hok hfail =>
    rcases hsc' _ hpk with ⟨μ, r, P, hteq | hteq, hμ⟩ | ⟨u, rfl | rfl, hnw⟩
    · subst hteq; simp [wordOf] at hnw0
    · subst hteq; simp [wordOf] at hnw0
    · rcases hc with hc | ⟨_, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
        subst hc
        have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv
          (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
        exact casC_outB (hDy := hS.dy) ht hpk rfl hone hpe hu hsube hsubv hb hok.tk hfail.tk
          (plainCellPtrB hpk hone ho hi.1 hE htv hm) hi hE htv hRP
      · simp [cellOf] at hc
    · rcases hc with hc | ⟨_, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
        subst hc
        have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv
          (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
        refine casC_outB (hDy := hS.dy) ht hpk rfl hone hpe hu hsube hsubv hb hok.tk hfail.tk (fun nw hval => ?_) hi hE htv hRP
        obtain ⟨ad, pw, μr, ru, hea, haddr, -, -, -, hne, hld, hsto, -⟩ :=
          locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk (.inr rfl) ho
            (accs_cl_one hone) hi.1 hE htv hm
        exact ⟨ad, pw, _, hea, haddr, hne, fun s1 ws hl hp => ⟨(hld s1 ws hl hp).2.2,
          fun s1' hm1 s2 hs2 => hsto s1' [nw] hm1 hval rfl s2 hs2⟩⟩
      · simp [cellOf] at hc
  | casShare hpk hw | casTake hpk hw | casEpoch hpk hw =>
    rcases hsc' _ hpk with ⟨μ, r, P, hteq, hμ⟩ | ⟨u, hteq, hnw⟩
    · cases hg : P.ghost
      · rcases hteq with rfl | rfl
        · exact hcasW (.inl hpk) hμ hg
        · exact hcasW (.inr hpk) hμ hg
      · exact (cas_ghost_absurd (by rw [← ht]; exact hT) hpk hteq
          (wordRef_pwfB hpk hteq hμ hi.1 hE htv hm) hg).elim
    · rw [hnw] at hw; cases hw
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1663 pairRef_vr
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pairRef_vrB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {K : TEnv → List Word → Prop} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {w : At} {t u : Ty} {μ : Mode}
    (hpk : cx.peek w = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th)) : ∃ R ws, (VRF False) ρ η u R ws := by
  have ho : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  rcases ht with rfl | rfl
  · rcases hμ with rfl | rfl
    · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv ho
      have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
      obtain ⟨-, -, -, -, _, hvr, -⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
        hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
        (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
        (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
        (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl)
      exact ⟨_, _, hvr⟩
    · obtain ⟨_, _, _, _, -, -, -, -, -, -, _, hvr⟩ :=
        loadPub_coreB (p := p) (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
      exact ⟨_, _, hvr⟩
  · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, _, hvr⟩ :=
      locCellB (acq := false) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ ho
        (pair_accs_cl hu) hi hE htv hm
    exact ⟨_, _, hvr⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1690 caspA_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem caspA_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {A : Address} {c : Cell} {U : Ty}
    {pw x0 x1 n0 n1 : Word} {rw rt0 rt1 rtv0 rtv1 : Ty} {Rf Rs Rok Rv : Res} {xk : AllocLabel}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hea : evalAt th.env w = some (rw, [pw])) (haddr : addrOf pw = some A)
    (hee0 : evalAt th.env e0 = some (rt0, [x0])) (hee1 : evalAt th.env e1 = some (rt1, [x1]))
    (hev0 : evalAt th.env v0 = some (rtv0, [n0])) (hev1 : evalAt th.env v1 = some (rtv1, [n1]))
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw A acq [.two] 0 (stOf mem pairs th) → PromAbove s1 →
        MemInvB g (CE η) s1 ∧ ∀ s1', MemInvB g (CE η) s1' →
          ∀ s2, s2 ∈ storeUnits g.k g.arch pw A rel [.two] [n0, n1] 0 s1' → MemInvB g (CE η) s2)
    (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset U)
    (hini : Priv (CE η) A.label → IniAt (CE η).rc c A U)
    (hwU : wc U = some (nWords [.two])) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hv : EnvValRB (CE η) U [n0, n1] Rv) (hRv : Rv (.own xk) = 0)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hpd : ∀ t, t ∈ th.promises → t ∉ pairs := MemInv_nopairB hm
  have key : tstep g mem pairs th =
      (Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw n0 n1) 1 2 A x0.val x1.val
          (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
        (mem', pairs', withS (if (th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1, th'.regs 2]⟩) := by
    simp only [tstep, hterm, hea, hee0, hee1, hev0, hev1, haddr]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd0, rd1, hl1, hr0, hr1, hcase⟩ := stepRmwPair_split (k := g.k) (s := stOf mem pairs th) hin
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.two] 0 _ (s1, [rd0, rd1]) hl1
  rcases hcase with ⟨hne', hsame⟩ | ⟨h0, h1, s2, hs2, hsame⟩ | ⟨h0, h1, tw', pm, htw', hpm, hpl, hsame⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = false := by
      rw [hr0, hr1]
      cases e0 : (rd0.val == x0.val) <;> cases e1 : (rd1.val == x1.val) <;> simp_all
    simp only [hb]
    have hp1 : PromAbove s1 := PromAbove_lockS (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1i, -⟩ := hcell s1 [rd0, rd1] hl1 hp1
    exact ⟨Rf + Rs, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hfail, htv, hi, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1i) hsame,
      Nat.le_refl _, Or.inl ⟨hsame.1.trans ((lockS_memP _ _).1.trans f1),
        hsame.2.2.2.1.trans ((lockS_memP _ _).2.trans f2)⟩⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = true := by
      rw [hr0, hr1]; simp [h0, h1]
    simp only [hb, ite_true]
    have hp2 : PromAbove s2 :=
      PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
    have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
    obtain ⟨hm1i, hst2⟩ := hcell s1 [rd0, rd1] hl1 hp1
    have hm1b := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1i) (max (max (Promises.pairTop (stOf mem pairs th).pairs rd0.rts) rd0.view)
      (max (Promises.pairTop (stOf mem pairs th).pairs rd1.rts) rd1.view))
    have hlc := loadCoh_bumpB (max (max (Promises.pairTop (stOf mem pairs th).pairs rd0.rts) rd0.view)
      (max (Promises.pairTop (stOf mem pairs th).pairs rd1.rts) rd1.view)) (LoadCoh_loadB hl1 hp1 hm.2.1 ⟨c, hsto⟩)
    refine ⟨Rok + Rs, ⟨ρ, η, cok, Rok, Rs, rfl, hE, hok, htvok, hiok, rfl, hRPo, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB (hst2 _ hm1b s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1i).2.2.2.2.1)) hsame, ?_,
      Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, A, rel, [.two], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
        hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inr ⟨hlc, hm1b.2.2.2.2.1, c, U, Rv, hsto, hat, hini, hna, hv,
          hwU, rfl, hRv⟩⟩⟩
    simp only [Res.add_apply]
    omega
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hmc, _⟩ := stepRmwPair_memR hin (by decide) hpd
    have hp3 : th'.promises = th.promises := by
      rcases hmc with ⟨_, _, h⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h
    have hs1p : s1.promises = th.promises :=
      (TermMem.loadUnits_frame [.two] 0 (stOf mem pairs th) (s1, [rd0, rd1]) hl1).2.2.1
    have e := hsame.2.2.2.1
    rw [lockS_prom] at e
    simp only [pairFulS] at e
    rw [hp3, hs1p] at e
    rw [hs1p] at htw'
    have hl := congrArg List.length e
    have h1 := List.length_erase_of_mem htw'
    have h2 := List.length_erase_le (l := th.promises.erase tw') (a := tw' + 1)
    have h3 := List.length_pos_of_mem htw'
    omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1772 casp_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem casp_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {μ : Mode} {tw u : Ty} {i0 i1 j0 j1 : Idx} {Rf Rs Rok : Res} {xk : AllocLabel}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok tw) (ht : tw = .ptr μ u ∨ tw = .loc μ u) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hnv : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      EnvValB (CE η) (cl ρ η.wit 0 0 u) [n0, n1])
    (hvR : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      ∃ Rv, EnvValRB (CE η) (cl ρ η.wit 0 0 u) [n0, n1] Rv ∧ Rv (.own xk) = 0)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  obtain ⟨te0, hte0, hio0⟩ := hie0
  obtain ⟨rt0, x0, hee0, hx0, -⟩ := atom_numB hi.1.2.1 hte0 hio0
  obtain ⟨te1, hte1, hio1⟩ := hie1
  obtain ⟨rt1, x1, hee1, hx1, -⟩ := atom_numB hi.1.2.1 hte1 hio1
  obtain ⟨tv0, htv0, hjo0⟩ := hj0
  obtain ⟨rtv0, n0, hev0, hn0, -⟩ := atom_numB hi.1.2.1 htv0 hjo0
  obtain ⟨tv1, htv1, hjo1⟩ := hj1
  obtain ⟨rtv1, n1, hev1, hn1, -⟩ := atom_numB hi.1.2.1 htv1 hjo1
  obtain ⟨A, pw, rw, hea, haddr, -, hcell⟩ : ∃ A pw rw, evalAt th.env w = some (rw, [pw]) ∧
      addrOf pw = some A ∧ loadUnits g.arch pw A acq [.two] 0 (stOf mem pairs th) ≠ [] ∧
      ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw A acq [.two] 0 (stOf mem pairs th) → PromAbove s1 →
        MemInvB g (CE η) s1 ∧ ∀ s1', MemInvB g (CE η) s1' →
          ∀ s2, s2 ∈ storeUnits g.k g.arch pw A rel [.two] [n0, n1] 0 s1' → MemInvB g (CE η) s2 := by
    rcases ht with rfl | rfl
    · obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := caspCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
        (pairs := pairs) hpk hμ hu (fun _ => hnv n0 n1 hn0 hn1) hi.1 hE htv hm
      exact ⟨⟨lab, 0⟩, pw, rw, hea, by simp [addrOf, hpw], hne, hcell⟩
    · exact caspLocCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hu
        (fun _ => hnv n0 n1 hn0 hn1) hi.1 hE htv hm
  have hus2 := pair_accs_cl (ρ := ρ) (wit := η.wit) hu
  obtain ⟨c, hsto, hat, hini⟩ := cellTargetPB hi.1 hpk (by rcases ht with rfl | rfl <;> rfl) hμ
    (by rw [hus2]; simp) hea haddr
  obtain ⟨Rv, hv, hRv⟩ := hvR n0 n1 hn0 hn1
  exact caspA_outB (hDy := hDy) hterm hea haddr hee0 hee1 hev0 hev1 hcell hsto hat hini (by simp [wc, hus2])
    (fun N e h => by rw [h] at hus2; simp [accs] at hus2) hv hRv hok htvok hiok hres hfail hi hE htv hm hRP hRPo
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1821 caspW_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem caspW_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {tw : Ty} {r i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {Rf Rs Rok : Res}
    {xk : AllocLabel}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail) (hpk : cx.peek w = .ok tw)
    (hw : word2Of tw = some (r, P))
    (hsc : ∃ μ u, (tw = .ptr μ u ∨ tw = .loc μ u) ∧ (μ = .own ∨ μ = .pub) ∧
      ((∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P)))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hst : InState2 cx P j0 j1 c₂ k0' k1')
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    RmwOutB p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  obtain ⟨μ, u, ht, hμ, -⟩ := hsc
  have hu' : u = .word2 r P := by
    rcases ht with rfl | rfl <;> cases u <;> simp [word2Of] at hw <;> obtain ⟨rfl, rfl⟩ := hw <;> rfl
  subst hu'
  have hu : (∃ r' P', Ty.word2 r P = .word2 r' P') ∨ (∃ r' P', Ty.word2 r P = .epair r' P') := .inl ⟨_, _, rfl⟩
  obtain ⟨R, ws, hvr⟩ := pairRef_vrB (g := g) (mem := mem) (pairs := pairs) hpk ht hμ hu hi.1 hE htv hm
  have hpwf : pwf2 P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
  have hsat : Sat cx.facts ρ := hi.1.1
  refine casp_outB (hDy := hDy) hterm hpk ht hμ hu hie0 hie1 hj0 hj1
    (fun n0 n1 hn0 hn1 => storeWord2_valB hpwf hsat hst hn0 hn1) (fun n0 n1 hn0 hn1 => ?_)
    hok htvok hiok hres hfail hi hE htv hm hRP hRPo
  have hvs : [n0, n1].map (·.val) = [.num (ev ρ j0), .num (ev ρ j1)] := by simp [hn0, hn1]
  refine ⟨wr2 P (ev ρ r) ([n0, n1].map (·.val)) + Res.one (.wd (ev ρ r)), ⟨?_, by simp [cl, Valid]⟩,
    wr2W_own _ _ _ _⟩
  simp only [cl, clI_zero]
  exact VRR_word2_ofB hpwf hvs (InP2_of_st hsat hst)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1855 tgt_casp
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_caspB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail) (hRP : RetPw th.σs th.stack cx.ret) : TgtB p g x n (CE η) mem pairs th := by
  have hsc' : StepScope cx (.casp acq rel w e0 e1 v0 v1 t ok fail) :=
    stepScope_of (by rw [← ht]; exact hS.sc) (fun _ _ _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hRL := RLink_ofB hE.2.1 hE.2.2
  refine tgt_rmwB hS (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [ht] at h; cases h) ?_
  have hT0 := hS.hT
  have hCk0 := hS.ck
  rw [ht] at hT0 hCk0
  cases TermA4.CkW_inv_casp hCk0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    obtain ⟨μ, u, ht', hμ, -⟩ := hsc' _ hp
    obtain ⟨r, P⟩ : ∃ r P, epairOf _ = some (r, P) := ⟨_, _, hwe⟩
    have hu' : ∃ r P, u = .epair r P := by
      rcases ht' with rfl | rfl <;> cases u <;> simp [epairOf] at hwe <;> exact ⟨_, _, rfl⟩
    obtain ⟨r, P, rfl⟩ := hu'
    have hu : (∃ r' P', Ty.epair r P = .word2 r' P') ∨ (∃ r' P', Ty.epair r P = .epair r' P') := .inr ⟨_, _, rfl⟩
    obtain ⟨R, ws, hvr⟩ := pairRef_vrB (g := g) (mem := mem) (pairs := pairs) hp ht' hμ hu hi.1 hE htv hm
    have hpwf : pwfE P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    have hiok := bindRB hb hi hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    refine casp_outB (hDy := hS.dy) ht hp ht' hμ hu hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 => storeEPair_valB hpwf ⟨_, _, hn0, hn1⟩) (fun n0 n1 hn0 hn1 => ?_) hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    refine ⟨.zero, ⟨?_, by simp [cl, Valid]⟩, rfl⟩
    simp only [cl, clI_zero, VRRB]
    exact ⟨⟨hpwf, _, _, by rw [List.map_cons, List.map_cons, List.map_nil, hn0, hn1]⟩, trivial⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' hep hbump _ hb hok hfail =>
    have hiok := bindRB (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    exact caspW_outB (hDy := hS.dy) ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | caspMove hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' hb hok hfail =>
    have hiok := bindRB hb hi hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    exact caspW_outB (hDy := hS.dy) ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | caspTake hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' _ hb hok hfail =>
    have hiok := bindRB (rt := .unit) (ws := []) (R := .one (.rg _)) hb hi hRL rfl (Lay_etok_unit rfl)
    exact caspW_outB (hDy := hS.dy) ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1904 memHeldP_box
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem memHeldP_boxB {g : G} {E : TEnv} {s : St} {HP : Res} {us : List Acc} {ws : List Word} {r : St × Word}
    (hm : MemInvB g E s) (hH : MemHeldPB E s HP)
    (hr : r ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i s.nalloc) us ws s) (B : Box) (F : Ts) :
    MemHeldPB (seeBoxE E (freshLabel g.lbase g.n g.i s.nalloc) B F) (if g.boxFence then fenceS r.1 .st else r.1) HP := by
  have hnone := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hbnone : E.box (freshLabel g.lbase g.n g.i s.nalloc) = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hpfn : E.pfr (freshLabel g.lbase g.n g.i s.nalloc) = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  obtain ⟨hg, hsub, -, -, hful⟩ := alloc_growsP hm.2.2.1 r hr
  have hQ : ∀ l, Priv E l → l ≠ freshLabel g.lbase g.n g.i s.nalloc := fun l h e => by
    obtain ⟨⟨c, hc, -⟩, -⟩ := h
    rw [e, hnone] at hc; cases hc
  have key : MemHeldPB (seeBoxE E (freshLabel g.lbase g.n g.i s.nalloc) B F) r.1 HP := by
    refine TermOwnHeldQ.Flat.memHeldOn_trB hH (fun l => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun l hq => by simp [seeBoxE, hQ l hq]) rfl rfl
      (fun l hq o w hw => LatestNP_growsAtF hg (fun t h => hsub.subset h) hful (hQ l hq) hw)
      (fun h => ValOfR_monoB (η₁ := E) (η₂ := seeBoxE E (freshLabel g.lbase g.n g.i s.nalloc) B F) rfl rfl
        (fun _ _ h => h) (fun _ => Nat.le_refl _) h
        (hP := fun l f h' => by
          have hne : l ≠ freshLabel g.lbase g.n g.i s.nalloc := fun e => by rw [e, hpfn] at h'; cases h'
          simp only [seeBoxE, hne, ↓reduceIte]; exact h')
        (hB := fun l B' h' => by
          have hne : l ≠ freshLabel g.lbase g.n g.i s.nalloc := fun e => by rw [e, hbnone] at h'; cases h'
          simp only [seeBoxE, hne, ↓reduceIte]; exact h'))
    by_cases e : l = freshLabel g.lbase g.n g.i s.nalloc
    · subst e
      refine ⟨fun h => ?_, fun h => absurd rfl (hQ _ h)⟩
      have h2 := h.2
      simp [seeBoxE] at h2
    · simp only [Priv, OwnL, seeBoxE, e, ↓reduceIte]
  split
  · exact TermOwnHeldQ.Flat.memHeldOn_eqsB key rfl rfl
  · exact key
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1939 BoxRes
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def BoxResB (p : Prog) (g : G) (η : TEnv) (s0 : St) (T : Res) (th' : TTh) (S' : St) : Prop :=
  ∃ E, ThInvREB g.lbase g.n g.i p E th' T ∧ MemInvB g E S' ∧ E.sto = (CE η).sto ∧
    (∀ HP, MemHeldPB (CE η) s0 HP → MemHeldPB E S' HP) ∧ ExtB (CE η) E ∧ E.ini = (CE η).ini ∧ E.rini = (CE η).rini
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1944 BoxOut
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def BoxOutB (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (T : Res) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
    BoxResB p g η (stOf mem pairs th) T r.2.2 (stOf r.1 r.2.1 r.2.2)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1948 tgt_box
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_boxB {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hX : SrcB p g x n mem pairs th ρ η cx Rf Rs HP)
    (hnb : ∀ E1, BumpIf th E1)
    (h : BoxOutB p g mem pairs th η (Rf + Rs)) : TgtB p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨E, hT, hm, hsto, hH, hXE, hini, hri⟩ := h r hr hpa
  exact ⟨E, Rf + Rs, HP, hT, hm, hH HP hX.hH, fun l c hc => hX.nie l c (by rw [← hsto]; exact hc),
    by rw [hsto]; exact hX.sto, hX.le,
    TermOwnX2.Flat.anchStep_genB hXE (hnb E) (fun _ _ h _ => by rw [← hsto]; exact h)
      (fun _ _ => by rw [hini]; exact Nat.le_max_left _ _) (fun l h0 hl => absurd (by rw [hsto]; exact h0) hl)
      (fun _ _ => Or.inl (by rw [hri]; exact Nat.le_refl _)) (fun h l => by rw [hri, hini]; exact h l), hX.tyk hr (fun _ _ h => by rw [← hsto]; exact h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1960 inlB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem inlB_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRRB ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    BoxOutB p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close th.σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed (.sum rt (close th.σs τ)) = true := by simp [isBoxed, sumHead, hS]
  have hRa : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num j) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum rt (close th.σs τ), [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  intro r hr _
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  let B : Box := ⟨j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohRB η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm hn hbf hal hnw.symm
  simp only at hpw
  subst hpw
  obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
  have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
  have eqw : VEq ws q' := eq1.symm.trans eq'.vals
  have hv2 : VRRB ρ η'.unsee t (shp rt) q' R :=
    VRR_extB hE.2.1.unsee hE.2.2.unsee (Ext_unseeB hx) (VRR_storeB hE.2.1 hE.2.2 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
      (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VRR_upB _ _ _ _ _ hwq hv))
  have hvr : VRRB ρ η' (.sum t τ) (shp (.sum rt (close th.σs τ))) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxLB (B := B) hS hRa rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) hj hq' hv2
      (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
      (by show ((armsOf (.sum rt (close th.σs τ)))[j]?).bind wc = some (p0.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hnw, List.length_map])
  have hf := FInvR_monoB (bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1) (RLink_ofB hx.1 hcr') hvr
    (Lay_box ⟨hshape, hsk, hwc, hval, hly⟩ hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, (⟨he.1, by rw [hx.2.1]; exact he.2⟩ : TypedK _ _ _ _), htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_boxB hm hH hal B _, TermOwnX2.Flat.ext_CEB hx, rfl, rfl⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2028 inrB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem inrB_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRRB ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    BoxOutB p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  let τc := close th.σs τ
  let n := (armsOf τc).length
  have harmS : (armsOf (.sum τc rt))[n + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed (.sum τc rt) = true := by simp [isBoxed, sumHead, τc, hS]
  have hRb : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num (n + j)) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum τc rt, [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box (t := Ty.sum (close th.σs τ) rt) (j := (armsOf (close th.σs τ)).length + j) hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  intro r hr _
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  let B : Box := ⟨n + j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohRB η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm hn hbf hal hnw.symm
  simp only at hpw
  subst hpw
  obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
  have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
  have eqw : VEq ws q' := eq1.symm.trans eq'.vals
  have hv2 : VRRB ρ η'.unsee t (shp rt) q' R :=
    VRR_extB hE.2.1.unsee hE.2.2.unsee (Ext_unseeB hx) (VRR_storeB hE.2.1 hE.2.2 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
      (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VRR_upB _ _ _ _ _ hwq hv))
  have hvr : VRRB ρ η' (.sum τ t) (shp (.sum τc rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxRB (B := B) hS hRb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) (Nat.le_add_right _ _)
      (by show ofArm rt (n + j - n) _ = _; rw [Nat.add_sub_cancel_left]; exact hq') hv2
      (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
      (by show ((armsOf (.sum τc rt))[n + j]?).bind wc = some (p0.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hnw, List.length_map])
  have hf := FInvR_monoB (bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1) (RLink_ofB hx.1 hcr') hvr
    (TermSound.Lay_boxR ⟨hshape, hsk, hwc, hval, hly⟩ hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, (⟨he.1, by rw [hx.2.1]; exact he.2⟩ : TypedK _ _ _ _), htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_boxB hm hH hal B _, TermOwnX2.Flat.ext_CEB hx, rfl, rfl⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2099 inlBB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem inlBB_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hvV : (VRF False) ρ η t (shp rt) ws) (hv : VRRB ρ η t (shp rt) ws R)
    (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    BoxOutB p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hvV
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let S := Ty.sum rt (close th.σs τ)
  have harmS : (armsOf S)[B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S r1.2.1 r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num B0.tag) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  intro r hr hpr0
  rw [key, List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    have hpa' := hpr0
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
    exact injM_pa hpl1 hr2 hpa'
  obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
  rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
  have hm1 : MemInvB g (CE η) s1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
  have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
  let lbl := freshLabel g.lbase g.n g.i s1.nalloc
  let V := s1.vs.vRelSt
  let B : Box := ⟨B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
  simp only at hpw
  subst hpw
  have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
  have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
  let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohRB η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
  have hv0 : VRRB ρ η' t (vsh 0 (shp rt)) [w] R := by rw [vsh_zero rt hrb]; exact VRR_extB hE.2.1 hE.2.2 hx hv
  have hv1 : VRRB ρ η' t (vsh 0 (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_renB (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
      (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
      (by simpa [η', TEnv.withStoB] using hsto0)
      (by simp [η', TEnv.withStoB, hini0]) rfl (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
      (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
      (by simp [η', TEnv.withStoB, hini0])
  have hvr : VRRB ρ η' (.sum t τ) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxLBB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) hj hv1
      (by show ((armsOf S)[B0.tag]?).bind wc = some (p1.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hlen, List.length_map])
  have hf := FInvR_monoB (bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1) (RLink_ofB hx.1 hcr') hvr
    (Lay_box hl hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, (⟨he.1, by rw [hx.2.1]; exact he.2⟩ : TypedK _ _ _ _), htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_boxB hm1 (TermOwnHeldQ.Flat.memHeldOn_eqsB hH e1 e4) hal B _, TermOwnX2.Flat.ext_CEB hx, rfl, rfl⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2187 inrBB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem inrBB_outB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hvV : (VRF False) ρ η t (shp rt) ws) (hv : VRRB ρ η t (shp rt) ws R)
    (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    BoxOutB p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hvV
  let n := (armsOf (close th.σs τ)).length
  let S := Ty.sum (close th.σs τ) rt
  have harmS : (armsOf S)[n + B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S (n + r1.2.1) r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num (n + B0.tag)) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  intro r hr hpr0
  rw [key, List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    have hpa' := hpr0
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
    exact injM_pa hpl1 hr2 hpa'
  obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
  rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
  have hm1 : MemInvB g (CE η) s1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
  have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
  let lbl := freshLabel g.lbase g.n g.i s1.nalloc
  let V := s1.vs.vRelSt
  let B : Box := ⟨n + B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
  simp only at hpw
  subst hpw
  have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
  have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
  let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohRB η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
  have hv0 : VRRB ρ η' t (vsh 0 (shp rt)) [w] R := by rw [vsh_zero rt hrb]; exact VRR_extB hE.2.1 hE.2.2 hx hv
  have hv1 : VRRB ρ η' t (vsh n (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_renB (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
      (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
      (by simpa [η', TEnv.withStoB] using hsto0)
      (by simp [η', TEnv.withStoB, hini0]) (show B0.tag + n = (n + B0.tag) + 0 by omega) (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
      (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
      (by simp [η', TEnv.withStoB, hini0])
  have hvr : VRRB ρ η' (.sum τ t) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxRBB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) (Nat.le_add_right _ _) hv1
      (by show ((armsOf S)[n + B0.tag]?).bind wc = some (p1.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hlen, List.length_map])
  have hf := FInvR_monoB (bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1) (RLink_ofB hx.1 hcr') hvr
    (TermSound.Lay_boxR hl hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, (⟨he.1, by rw [hx.2.1]; exact he.2⟩ : TypedK _ _ _ _), htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.letW hterm rfl⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_boxB hm1 (TermOwnHeldQ.Flat.memHeldOn_eqsB hH e1 e4) hal B _, TermOwnX2.Flat.ext_CEB hx, rfl, rfl⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2276 caseArmNB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem caseArmNB_outB {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 q1 : List Word} {R Rr Rf Rs : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOKB p η)
    (hm1 : MemInvB g (CE η) s1) {S0 : St} (hH1 : ∀ HP, MemHeldPB (CE η) S0 HP → MemHeldPB (CE η) s1 HP)
    (hty : isBoxed ty = false) (hq : ofArm ty j p1 = some q1) (hlay : Lay th.σs u ty q1)
    (hvr : VRRB ρ η u (shp ty) q1 R) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e') :
    ∀ r2 ∈ injM g s1 ty j p1,
      BoxResB p g η S0 (Rf + Rs) (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) r2.1 := by
  rw [injM_nbB hty, hq]
  intro r2 hr2
  simp [ol] at hr2; subst hr2
  have hf := FInvR_monoB (bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvr hlay) (res_swap_le hle)
  exact ⟨CE η, ⟨ρ, η, c', Rf, Rs, rfl, hE, he, htv, by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.wit rfl⟩, hm1, rfl, hH1, Ext_reflB (Coh_CEB η) (CohR_CEB η), rfl, rfl⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2292 caseArmB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem caseArmB_outB {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 : List Word} {us : List Acc} {w : Word}
    {x0 : Address} {B0 : Box} {s0 : Nat} {R Rr Rf Rs : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOKB p η)
    (hm1 : MemInvB g (CE η) s1) {S0 : St} (hH1 : ∀ HP, MemHeldPB (CE η) S0 HP → MemHeldPB (CE η) s1 HP)
    (hn : 0 < g.n) (hbf : g.boxFence = true) (hty : isBoxed ty = true) (hus : (armsOf ty)[j]?.bind accs = some us)
    (hlen : p1.length = nWords us) (hw : w.val = .loc x0 0) (hB0 : η.box x0.label = some B0)
    (hsto0 : η.sto x0.label = none) (hini0 : η.ini x0.label = 0) (ht : B0.tag = j + s0)
    (hWp : WLe B0.pay p1) (hv : VRRB ρ η u (vsh s0 (shp ty)) [w] R) (hlay : ∀ pw, Lay th.σs u ty [pw]) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e') :
    ∀ r2 ∈ injM g s1 ty j p1,
      BoxResB p g η S0 (Rf + Rs) (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) r2.1 := by
  rw [injM_box hty hus]
  intro r2 hr2
  rw [List.mem_map] at hr2
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr2
  let lbl := freshLabel g.lbase g.n g.i s1.nalloc
  let V := s1.vs.vRelSt
  let B : Box := ⟨j, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
  simp only at hpw
  subst hpw
  have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
  have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
  let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohRB η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
  have hv0 : VRRB ρ η' u (vsh s0 (shp ty)) [w] R := VRR_extB hE.2.1 hE.2.2 hx hv
  have hv1 : VRRB ρ η' u (vsh 0 (shp ty)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_renB (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
      (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
      (by simpa [η', TEnv.withStoB] using hsto0)
      (by simp [η', TEnv.withStoB, hini0]) (by show B0.tag + 0 = j + s0; omega)
      (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS) (bh_shp ty hty) hv0
      (by simp [η', TEnv.withStoB, hini0])
  rw [vsh_zero ty hty] at hv1
  have hf := FInvR_monoB (bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi1) (RLink_ofB hx.1 hcr') hv1 (hlay _))
    (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he, htv, by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :)), hDy.wit rfl⟩,
    by rw [hCE]; exact hm', rfl, fun HP hH => by rw [hCE]; exact memHeldP_boxB hm1 (hH1 HP hH) hal B _, TermOwnX2.Flat.ext_CEB hx, rfl, rfl⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2344 caseB_out
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem caseB_outB {bkG : Prop} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} {c₁ c₂ c₃ : Cx}
    {ra rb : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hb1 : c₁.bind x u = .ok c₂) (he1 : TypedK p η c₂ e₁) (htv1 : TvOK c₂)
    (hb2 : c₁.bind y v = .ok c₃) (he2 : TypedK p η c₃ e₂) (htv2 : TvOK c₃)
    (hi1 : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (.sum ra rb, ws)) (hvV : (VRF bkG) ρ η (.sum u v) (shp (.sum ra rb)) ws)
    (hvR : VRRB ρ η (.sum u v) (shp (.sum ra rb)) ws R)
    (hl : Lay th.σs (.sum u v) (.sum ra rb) ws) (hS : (Ty.sum ra rb).tier = .boxed)
    (hsg : sig (.sum ra rb) = sig (cl ρ η.wit 0 0 (.sum u v)))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    BoxOutB p g mem pairs th η (Rf + Rs) := by
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  have hrb : isBoxed (.sum ra rb) = true := by simp [isBoxed, sumHead, hS]
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hvV
  have hv' := hvR
  simp only [VRRB, shp] at hv'
  obtain ⟨n0, Ra, Rb, hR, hv'⟩ := hv'
  simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have htl : (Ty.sum (lnorm ra) (lnorm rb)).tier = .boxed := by
    rw [← hS]; exact tier_lnorm (.sum ra rb)
  have hv3 := hv'.resolve_right (fun ⟨j, p, hd, _, _⟩ => by rw [htl] at hd; simp [decodeArm] at hd)
  obtain ⟨-, x1, s0, B, hx1, -, hB, hn1, -, -, hA, hB'⟩ := hv3
  rw [wc_boxed hS] at hn1
  have hs0 : s0 = 0 := by simp at hn1; omega
  subst hs0
  simp only [List.map_cons, List.map_nil, hw, List.cons.injEq, and_true] at hx1
  cases hx1
  rw [hB0, Option.some.injEq] at hB
  subst hB
  have la : (armsOf (lnorm ra)).length = (armsOf ra).length := by rw [armsOf_lnorm, List.length_map]
  simp only [Nat.sub_zero, Nat.zero_add, la, isBoxed_lnorm, shp_lnorm] at hA hB'
  have hsg2 : Ty.sum (sig ra) (sig rb) = Ty.sum (sig (cl ρ η.wit 0 0 u)) (sig (cl ρ η.wit 0 0 v)) := hsg
  simp only [Ty.sum.injEq] at hsg2
  have hs := hl.2.1
  simp only [close, substTs, skel, etok, Ty.sum.injEq] at hs
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨-, -, -, -, hly⟩ := hl
  simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
  have layB : ∀ (ty : Ty) (t : Ty), isBoxed ty = true → etok (skel ty) = etok (skel (close th.σs t)) →
      etok (lyt 0 ty) = etok (lyt 0 (close th.σs t)) → ∀ pw, Lay th.σs t ty [pw] := by
    intro ty t hty hk hy pw
    refine ⟨fun us hu => ?_, hk, by rw [wc_isBoxed ty hty]; simp, Valid_boxed ty _ hty, hy⟩
    have h1 := wc_isBoxed ty hty
    simp only [wc, hu, Option.map_some, Option.some.injEq] at h1
    simp [h1]
  let s := stOf mem pairs th
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := .sum ra rb) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have hlen : ∀ p1 : List Word, WLe B0.pay p1 → p1.length = nWords us := fun p1 h => h.length.symm.trans hnw.symm
  intro r hr hpr0
  simp only [tstep, hterm, hea] at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    have hpa' := hpr0
    try simp only at hr
    split at hr
    · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
    · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
  obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
  have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
  have hH1 : ∀ HP, MemHeldPB (CE η) s HP → MemHeldPB (CE η) r1.1 HP := fun HP h =>
    TermOwnHeldQ.Flat.memHeldOn_eqsB h e1 e4
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at htag hWp hm1 hH1
  subst htag
  by_cases hj : B0.tag < (armsOf ra).length
  · simp only [hj, ite_true, List.mem_map] at hr
    obtain ⟨r2, hr2, rfl⟩ := hr
    cases hty : isBoxed ra with
    | false =>
        obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hA hj).2 hty
        obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
          case_arm_nbRB hE.2.1 hE.2.2 hty hsg2.1 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
        exact caseArmNB_outB (hDy := hDy.leftW (fun _ => by rw [hterm]; rfl) rfl) hb1 he1 htv1 hi1 hle hE hm1 hH1 hty hq1 ⟨hs1, hsa, hw1, hv1, hly.1⟩ hvr1 hRP1 r2 hr2
    | true =>
        have harmA : (armsOf ra)[B0.tag]? = some arm := by
          rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_left hj]
        exact caseArmB_outB (hDy := hDy.leftW (fun _ => by rw [hterm]; rfl) rfl) (hbf := hbf) (s0 := 0) hb1 he1 htv1 hi1 hle hE hm1 hH1 hn hty (by rw [harmA]; exact hus)
          (hlen p1 hWp) hw hB0 hsto0 hini0 (by omega) hWp ((hA hj).1 hty) (layB ra u hty hsa hly.1) hRP1 r2 hr2
  · have hj' : (armsOf ra).length ≤ B0.tag := by omega
    simp only [hj, ite_false, List.mem_map] at hr
    obtain ⟨r2, hr2, rfl⟩ := hr
    cases hty : isBoxed rb with
    | false =>
        obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hB' hj').2 hty
        obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
          case_arm_nbRB hE.2.1 hE.2.2 hty hsg2.2 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
        exact caseArmNB_outB (hDy := hDy.rightW (fun _ => by rw [hterm]; rfl) rfl) hb2 he2 htv2 hi1 hle hE hm1 hH1 hty hq1 ⟨hs1, hsb, hw1, hv1, hly.2⟩ hvr1 hRP1 r2 hr2
    | true =>
        have harmB : (armsOf rb)[B0.tag - (armsOf ra).length]? = some arm := by
          rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_right hj']
        exact caseArmB_outB (hDy := hDy.rightW (fun _ => by rw [hterm]; rfl) rfl) (hbf := hbf) (s0 := (armsOf ra).length) hb2 he2 htv2 hi1 hle hE hm1 hH1 hn hty
          (by rw [harmB]; exact hus) (hlen p1 hWp)
          hw hB0 hsto0 hini0 (by omega) hWp ((hB' hj').1 hty) (layB rb v hty hsb hly.2) hRP1 r2 hr2
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2445 tgt_inl
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_inlB {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : SrcB p g xl n mem pairs th ρ η cx Rf Rs HP) {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtB p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkL := hX.ck
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop hX.tv
    cases hop with
    | inl _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum t τ) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useRB (bkG := False) hu hX.hF hX.hE.2.2
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum t τ) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · apply tgt_boxB hX (TermOwnX2.bumpIf_nb hterm)
        cases hrb : isBoxed rt with
        | false => exact inlB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK hX.tv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu hX.tv).2.1
            exact inlBB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl) hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · have h : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs (.sum t' τ)).tier ≠ .boxed :=
          fun t' c₁' hu' => by
            rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
            rw [← hsk]; exact hS
        exact tgt_frameB hP hX (by rw [hterm]; exact h) (same_inlRB hterm h hX.hT hX.hF) hPS hSub hSig
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2483 tgt_inr
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_inrB {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : SrcB p g xl n mem pairs th ρ η cx Rf Rs HP) {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtB p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkL := hX.ck
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop hX.tv
    cases hop with
    | inr _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum τ t) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useRB (bkG := False) hu hX.hF hX.hE.2.2
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum τ t) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · apply tgt_boxB hX (TermOwnX2.bumpIf_nb hterm)
        cases hrb : isBoxed rt with
        | false => exact inrB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK hX.tv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu hX.tv).2.1
            exact inrBB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl) hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · have h : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs (.sum τ t')).tier ≠ .boxed :=
          fun t' c₁' hu' => by
            rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
            rw [← hsk]; exact hS
        exact tgt_frameB hP hX (by rw [hterm]; exact h) (same_inrRB hterm h hX.hT hX.hF) hPS hSub hSig
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2521 tgt_case
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_caseB {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : SrcB p g xl n mem pairs th ρ η cx Rf Rs HP) {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtB p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkC := hX.ck
  rw [hterm] at hT0 hCkC
  cases hT0 with
  | case hu hb1 he1 hb2 he2 =>
    obtain ⟨u, v, c₁, c₂, c₃, hu, hb1, he1, hb2, he2⟩ : ∃ u v c₁ c₂ c₃,
        cx.use a = .ok (.sum u v, c₁) ∧ c₁.bind x u = .ok c₂ ∧ Typed p c₂ e₁ ∧
        c₁.bind y v = .ok c₃ ∧ Typed p c₃ e₂ := ⟨_, _, _, _, _, hu, hb1, he1, hb2, he2⟩
    have hck12 := TermA4.CkW_case hCkC hu hb1 hb2
    obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useRB (bkG := False) hu hX.hF hX.hE.2.2
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have htv12 := case_TvOK hu hb1 hb2 hX.tv
      have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK hX.tv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu hX.tv).2.1
      have hsg := lay_closed (ρ := ρ) hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl
      exact tgt_boxB hX (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [hterm] at h; cases h) (caseB_outB (bkG := False) (hDy := hX.dy) hterm hX.gn hb1 ⟨he1, hck12.1⟩ htv12.1 hb2 ⟨he2, hck12.2⟩ htv12.2 hi1 hle hea hvV hv hl hS hsg
        hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu))))
    · have hnb : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs t').tier ≠ .boxed := fun t' c₁' hu' => by
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← tier_of_eskel hl.2.1]; exact hS
      exact tgt_frameB hP hX (by rw [hterm]; exact hnb) (same_caseRB hterm hnb hX.hT hX.ck hX.hF hX.hE hX.tv) hPS hSub hSig
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2562 tgt_easy
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_easyB {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : SrcB p g x n mem pairs th ρ η cx Rf Rs HP) (h : EasyK4 th.term) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hpub : ∀ y a e, th.term = .let_ y (.publish a) e → TgtB p g x n (CE η) mem pairs th) :
    TgtB p g x n (CE η) mem pairs th := by
  have hsc := hS.sc
  cases ht : th.term with
  | let_ y op e =>
    rw [ht] at h hsc
    cases op with
    | inl τ a => exact tgt_inlB hP hS ht hPS hSub hSig
    | inr τ a => exact tgt_inrB hP hS ht hPS hSub hSig
    | intoRgn rn a =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | mkTicket a1 a2 a3 a4 a5 =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | claim a1 a2 =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | publish a => exact hpub _ _ _ ht
    | mkWord a1 a2 a3 a4 => exact tgt_keepB hS (mkWord_stepB (hDy := hS.dy) ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | mkWord2 a1 a2 a3 a4 a5 => exact tgt_keepB hS (mkWord2_stepB (hDy := hS.dy) ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | mkEPair a1 a2 a3 a4 => exact tgt_keepB hS (mkEPair_stepB (hDy := hS.dy) ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | ldp a1 a2 a3 a4 => exact tgt_ldpB hP hS ht hRP hPS
    | stp a1 a2 a3 a4 a5 => exact tgt_stpB hS hP ht hRP
    | fetch a1 a2 a3 a4 a5 => exact tgt_fetchB hP hS ht hRP
    | _ => exact False.elim h
  | cas acq rel w e v t ok fail => exact tgt_casB hS ht hRP
  | casp acq rel w e0 e1 v0 v1 t ok fail => exact tgt_caspB hS ht hRP
  | case a y1 e1 y2 e2 => exact tgt_caseB hP hS ht hPS hSub hSig
  | _ => rw [ht] at h; exact False.elim h
end
end TermOwnK4.Flat

