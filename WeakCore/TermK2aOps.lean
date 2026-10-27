import WeakCore.TermK2a
import WeakCore.TermK2aRts
import WeakCore.TermBNamed

/-! # TermK2aOps (K-2a block A): binding contracts of the copy / no-label operations -/

namespace TermK2a
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermPtrRts
open WeakMem (Msg Memory Address Ts AllocLabel)

/-! ## Old counted words -/

/-- Every label a word of `ws` names is named by a counted word of an old binding, of no larger
`rts`. -/
def CntOld (th : TTh) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∀ l, Names l w → ∃ b ∈ Binds th, ∃ w0 ∈ pubWords b.2.1 b.2.2, Names l w0 ∧ w0.rts ≤ w.rts

theorem valB_of_cntOld {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rt : Ty}
    {ws : List Word} (h : CntOld th (pubWords rt ws)) : ValB sto s a N th rt ws := by
  intro w hw
  refine ⟨.inl fun hn => h w hw a hn, .inl fun l hn => ?_⟩
  obtain ⟨b, hb, w0, h0, hn0, -⟩ := h w hw l hn
  exact ⟨b, hb, w0, h0, hn0⟩

theorem cntOld_of_rtsSub {th : TTh} {ws ws' : List Word} (hs : RtsSub ws' ws) (h : CntOld th ws) :
    CntOld th ws' := by
  intro w hw l hn
  obtain ⟨w1, h1, hn1, hr1⟩ := hs w hw l hn
  obtain ⟨b, hb, w0, h0, hn0, hr0⟩ := h w1 h1 l hn1
  exact ⟨b, hb, w0, h0, hn0, Nat.le_trans hr0 hr1⟩

theorem cntOld_append {th : TTh} {ws ws' : List Word} (h1 : CntOld th ws) (h2 : CntOld th ws') :
    CntOld th (ws ++ ws') := by
  intro w hw
  rcases List.mem_append.1 hw with hw | hw
  · exact h1 w hw
  · exact h2 w hw

theorem cntOld_nil (th : TTh) : CntOld th [] := fun _ hw => by cases hw

theorem cntOld_bind {th : TTh} {b : String × Ty × List Word} (hb : b ∈ Binds th) :
    CntOld th (pubWords b.2.1 b.2.2) := fun w hw _ hn => ⟨b, hb, w, hw, hn, Nat.le_refl _⟩

theorem mem_binds_of_env {th : TTh} {b : String × Ty × List Word} (h : b ∈ th.env) : b ∈ Binds th :=
  List.mem_append_left _ h

theorem cntOld_env {th : TTh} {x : String} {rt : Ty} {ws : List Word} (h : (x, rt, ws) ∈ th.env) :
    CntOld th (pubWords rt ws) := cntOld_bind (b := (x, rt, ws)) (mem_binds_of_env h)

theorem cntOld_lookup {th : TTh} {x : String} {rt : Ty} {ws : List Word} (h : lookupE th.env x = some (rt, ws)) :
    CntOld th (pubWords rt ws) := cntOld_env (TermNoFul.lookupE_mem h)

/-- Words naming no label are old (vacuously). -/
theorem cntOld_noNames {th : TTh} {ws : List Word} (h : ∀ w ∈ ws, ∀ l, ¬ Names l w) : CntOld th ws :=
  fun w hw l hn => absurd hn (h w hw l)

/-- Counted words of a value naming no label are old. -/
theorem cntOld_pub_noNames {th : TTh} {rt : Ty} {ws : List Word} (h : ∀ w ∈ ws, ∀ l, ¬ Names l w) :
    CntOld th (pubWords rt ws) :=
  cntOld_of_rtsSub ((pubWords_rtsSub rt).1 ws) (cntOld_noNames h)

theorem not_names_num (n : Nat) (l : AllocLabel) : ¬ Names l (cst (.num n)) := by
  rintro ⟨a', g', hv', -⟩
  have e : (cst (.num n)).val = WeakMem.Val.num n := rfl
  rw [e] at hv'; cases hv'

/-- An atom's value is a binding's (a variable) or names nothing (a literal, unit). -/
theorem cntOld_evalAt {th : TTh} {v : At} {rt : Ty} {ws : List Word} (h : evalAt th.env v = some (rt, ws)) :
    CntOld th (pubWords rt ws) := by
  cases v with
  | var x => exact cntOld_lookup h
  | lit n =>
    simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact cntOld_pub_noNames fun w hw l => by
      rw [List.mem_singleton] at hw; subst hw; exact not_names_num n l
  | unit =>
    simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact cntOld_pub_noNames fun w hw => by cases hw

#print axioms valB_of_cntOld
#print axioms cntOld_evalAt

/-! ## Numeric helpers -/


theorem not_names_addW (u v : Word) (l : AllocLabel) : ¬ Names l (addW u v) := by
  rintro ⟨a', g', hv', -⟩
  unfold addW at hv'
  split at hv' <;> cases hv'

theorem not_names_subW (u v : Word) (l : AllocLabel) : ¬ Names l (subW u v) := by
  rintro ⟨a', g', hv', -⟩
  unfold subW at hv'
  split at hv' <;> cases hv'

set_option hygiene false in
macro "num_op" : tactic => `(tactic| (
  simp [evalOp, ol, Option.bind_eq_some_iff] at h
  repeat' (first | (apply Or.elim h <;> intro h) | (obtain ⟨_, h⟩ := h))
  all_goals (first | subst h | skip)
  all_goals (first
    | (split at h <;> first | (cases h) | (simp only [Option.some.injEq] at h; subst h))
    | skip)
  all_goals (exact valB_of_cntOld (cntOld_pub_noNames fun w hw l => by
    simp at hw; subst hw
    first | exact not_names_num _ l | exact not_names_addW _ _ l | exact not_names_subW _ _ l))))


/-! ## Numeric operations: one fresh `num` word -/

theorem valB_add {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y : At}
    (h : r ∈ evalOp g env σs s (.add x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_sub {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y : At}
    (h : r ∈ evalOp g env σs s (.sub x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_cvt {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {sg : Bool} {wd : Wd} {x : At}
    (h : r ∈ evalOp g env σs s (.cvt sg wd x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_toInt {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x : At}
    (h : r ∈ evalOp g env σs s (.toInt x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_asLanes {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {sg : Bool} {wd : Wd} {x : At}
    (h : r ∈ evalOp g env σs s (.asLanes sg wd x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_fop {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {o : FOp} {x y : At}
    (h : r ∈ evalOp g env σs s (.fop o x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_fcmp {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {o : FCmp} {x y : At}
    (h : r ∈ evalOp g env σs s (.fcmp o x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_fop1 {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {o : FOp1} {x : At}
    (h : r ∈ evalOp g env σs s (.fop1 o x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_lane {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y : At}
    (h : r ∈ evalOp g env σs s (.lane x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_setLane {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y z : At}
    (h : r ∈ evalOp g env σs s (.setLane x y z)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_rem {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y : At}
    (h : r ∈ evalOp g env σs s (.rem x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_bits {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {o : BitOp} {x y : At}
    (h : r ∈ evalOp g env σs s (.bits o x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_bit1 {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {o : BitOp1} {x : At}
    (h : r ∈ evalOp g env σs s (.bit1 o x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_vmatch {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y z : At}
    (h : r ∈ evalOp g env σs s (.vmatch x y z)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

theorem valB_band {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x y : At}
    (h : r ∈ evalOp g env σs s (.band x y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  num_op

/-! ## Unit results, copies, references -/

theorem valB_nil {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rt : Ty} :
    ValB sto s a N th rt [] :=
  valB_of_cntOld (cntOld_pub_noNames fun _ hw => by cases hw)

theorem valB_of_nil {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rt : Ty}
    {ws : List Word} (h : ws = []) : ValB sto s a N th rt ws := by
  subst h; exact valB_nil

set_option hygiene false in
macro "nil_op" : tactic => `(tactic| (
  apply valB_of_nil
  simp only [evalOp] at h
  repeat' split at h
  all_goals simp [ol, Option.bind_eq_some_iff] at h
  all_goals (repeat' (first | (apply Or.elim h <;> intro h) | (obtain ⟨_, h⟩ := h)))
  all_goals (repeat' split at h)
  all_goals (try simp [ol, Option.bind_eq_some_iff] at h)
  all_goals (repeat' (first | (apply Or.elim h <;> intro h) | (obtain ⟨_, h⟩ := h)))
  all_goals (first | rfl | (subst h; rfl))))

theorem valB_store {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rel : Bool} {x v : At} {tk : Option At}
    (h : r ∈ evalOp g env σs s (.store rel x v tk)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_stl {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {b i v : At}
    (h : r ∈ evalOp g env σs s (.stl b i v)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_stlw {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {b i j v : At}
    (h : r ∈ evalOp g env σs s (.stlw b i j v)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_stp {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rel : Bool} {x v0 v1 tk : At}
    (h : r ∈ evalOp g env σs s (.stp rel x v0 v1 tk)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_fence {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {f : Fence}
    (h : r ∈ evalOp g env σs s (.fence f)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_borrow {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {c : Cap} {t : At}
    (h : r ∈ evalOp g env σs s (.borrow c t)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_call {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {f : String} {is : List String} {x : At} {ts : List Ty}
    (h : r ∈ evalOp g env σs s (.call f is x ts)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp] at h

theorem valB_zero {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {τ : Ty}
    (h : r ∈ evalOp g env σs s (.zero τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol, Option.bind_eq_some_iff] at h
  obtain ⟨z, hz, rfl⟩ := h
  refine valB_of_cntOld (cntOld_pub_noNames fun w hw l hn => ?_)
  simp only [List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨a', g', e, -⟩ := hn
  exact TermBNamed.zeroWords_nv (fun _ => False) _ _ hz v hv a' g' e

theorem valB_claim {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x tk : At}
    (h : r ∈ evalOp g env σs s (.claim x tk)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_freeze {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {t : At}
    (h : r ∈ evalOp g env σs s (.freeze t)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_endBorrow {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {t : At}
    (h : r ∈ evalOp g env σs s (.endBorrow t)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  nil_op

theorem valB_callc {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {f x : At}
    (h : r ∈ evalOp g env σs s (.callc f x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp] at h

theorem valB_atom {g : G} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x : At}
    (h : r ∈ evalOp g th.env σs s (.atom x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol] at h
  obtain ⟨t, ws, he, rfl⟩ := h
  exact valB_of_cntOld (cntOld_evalAt he)

theorem valB_nameI {g : G} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x : At}
    (h : r ∈ evalOp g th.env σs s (.nameI x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol] at h
  obtain ⟨t, ws, he, rfl⟩ := h
  exact valB_of_cntOld (cntOld_evalAt he)

theorem valB_validate {g : G} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y : String}
    (h : r ∈ evalOp g th.env σs s (.validate y)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol] at h
  obtain ⟨t, ws, he, rfl⟩ := h
  exact valB_of_cntOld (cntOld_lookup he)

theorem valB_null {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {μ : Mode} {τ : Ty}
    (h : r ∈ evalOp g env σs s (.null μ τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp] at h
  subst h
  exact valB_of_cntOld (cntOld_pub_noNames fun w hw l => by
    rw [List.mem_singleton] at hw; subst hw; exact not_names_null l)

theorem valB_fnptr {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {f : String}
    (h : r ∈ evalOp g env σs s (.fnptr f)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp only [evalOp] at h
  split at h
  · simp only [List.mem_singleton] at h
    subst h
    exact valB_of_cntOld (cntOld_pub_noNames fun w hw l => by
      rw [List.mem_singleton] at hw; subst hw; exact not_names_num _ l)
  · cases h

/-- A value whose counted words are none. -/
theorem valB_of_pubNil {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rt : Ty}
    {ws : List Word} (h : pubWords rt ws = []) : ValB sto s a N th rt ws := by
  intro w hw; rw [h] at hw; cases hw

theorem valB_new {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {x : At}
    (h : r ∈ evalOp g env σs s (.new x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals simp at h
  obtain ⟨_, _, _, rfl⟩ := h
  exact valB_of_pubNil (pubWords_ptr_own _ _)

theorem valB_newBuf {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {n : At} {τ : Ty}
    (h : r ∈ evalOp g env σs s (.newBuf n τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := h
  exact valB_of_pubNil (by simp [pubWords, sNo, mPub])

theorem valB_intoRgn {g : G} {env : Env} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {rg : String} {x : At}
    (h : r ∈ evalOp g env σs s (.intoRgn rg x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol, Option.bind_eq_some_iff] at h
  obtain ⟨t, ws, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    exact valB_of_pubNil (by simp [pubWords, sNo, mPub])
  · simp only [Option.some.injEq] at h; subst h
    exact valB_of_pubNil (by simp [pubWords, sNo, mPub])
  · cases h

theorem pubWords_cellOf {t u : Ty} {μ : Mode} (h : cellOf t = some (μ, u)) (ws : List Word) :
    pubWords t ws = if mPub μ then ws else [] := by
  cases t <;> simp [cellOf] at h
  all_goals (obtain ⟨rfl, rfl⟩ := h; simp only [pubWords, sNo]; split <;> simp_all)

theorem pubWords_loc (μ : Mode) (u : Ty) (ws : List Word) : pubWords (.loc μ u) ws = if mPub μ then ws else [] :=
  pubWords_cellOf (t := .loc μ u) rfl ws

theorem pubWords_bufElem {t u : Ty} {μ : Mode} (h : bufElem t = some (μ, u)) (ws : List Word) :
    pubWords t ws = if mPub μ then ws else [] := by
  unfold bufElem at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [pubWords, sNo]; split <;> simp_all
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [pubWords, sNo]; split <;> simp_all
  · cases h

/-- A re-addressed word (same label, same `rts`) of a single-word reference value of the same mode. -/
theorem valB_reword {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {t t' : Ty}
    {μ : Mode} {pw w' : Word} (hold : CntOld th (pubWords t [pw]))
    (ht : pubWords t [pw] = if mPub μ then [pw] else [])
    (ht' : pubWords t' [w'] = if mPub μ then [w'] else [])
    (hw : ∀ l, Names l w' → Names l pw) (hr : w'.rts = pw.rts) : ValB sto s a N th t' [w'] := by
  refine valB_of_cntOld ?_
  rw [ht']
  rw [ht] at hold
  cases hm : mPub μ
  · exact cntOld_nil th
  · rw [hm] at hold
    simp only [ite_true]
    intro w hw' l hn
    rw [List.mem_singleton] at hw'; subst hw'
    obtain ⟨b, hb, w0, h0, hn0, hr0⟩ := hold pw (List.mem_singleton_self _) l (hw l hn)
    exact ⟨b, hb, w0, h0, hn0, by rw [hr]; exact hr0⟩

theorem names_offs {pw : Word} {b : Address} {k g : Nat} (hv : pw.val = .loc b g) (l : AllocLabel)
    (hn : Names l { pw with val := .loc (offs b k) g }) : Names l pw := by
  obtain ⟨a', g', e, rfl⟩ := hn
  simp only [WeakMem.Val.loc.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨b, g, hv, rfl⟩

theorem valB_fld {g : G} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {i : Nat} {x : At}
    (h : r ∈ evalOp g th.env σs s (.fld i x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol, Option.bind_eq_some_iff] at h
  obtain ⟨t, ws, he, h⟩ := h
  split at h
  · rename_i pw
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨μ, u⟩, hc, h⟩ := h
    have hold := cntOld_evalAt he
    repeat' split at h
    all_goals (try rw [Option.bind_eq_some_iff] at h)
    all_goals (try obtain ⟨_, -, h⟩ := h)
    all_goals (try split at h)
    all_goals (first | cases h | skip)
    all_goals (try simp only [Option.some.injEq] at h)
    all_goals (try subst h)
    all_goals exact valB_reword hold (pubWords_cellOf hc _) (pubWords_loc _ _ _) (names_offs (by assumption)) rfl
  · cases h

theorem valB_idx {g : G} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {b i : At}
    (h : r ∈ evalOp g th.env σs s (.idx b i)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp [evalOp, ol, Option.bind_eq_some_iff] at h
  obtain ⟨t, ws, he, h⟩ := h
  split at h
  · rw [Option.bind_eq_some_iff] at h; obtain ⟨_, -, h⟩ := h
    rw [Option.bind_eq_some_iff] at h; obtain ⟨_, -, h⟩ := h
    rw [Option.bind_eq_some_iff] at h; obtain ⟨⟨μ, u⟩, hbe, h⟩ := h
    rw [Option.bind_eq_some_iff] at h; obtain ⟨_, -, h⟩ := h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact valB_reword (cntOld_evalAt he) (pubWords_bufElem hbe _) (pubWords_loc _ _ _)
        (names_offs (by assumption)) rfl
    · cases h
  · cases h

theorem valB_bufRes {sto : Sto} {s : St} {a : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {μ : Mode}
    {n : Idx} {τ u : Ty} {ψ ψ' : Pred} {pw : Word}
    (hold : CntOld th (pubWords ((Ty.loc μ (.array n τ)).refine ψ) [pw])) :
    ValB sto s a N th ((Ty.loc μ (.array n u)).refine ψ') [pw] :=
  valB_reword hold (pubWords_bufElem rfl _) (pubWords_bufElem rfl _) (fun _ hn => hn) rfl

theorem valB_bufInit {g : G} {σs : List Ty} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {b i x : At}
    (h : r ∈ evalOp g th.env σs s (.bufInit b i x)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals simp at h
  obtain ⟨s2, -, rfl⟩ := h
  rename_i hev _
  exact valB_bufRes (cntOld_evalAt hev)


/-! ## Typed operations -/

theorem not_names_of_num {w : Word} {n : Nat} (hv : w.val = .num n) (l : AllocLabel) : ¬ Names l w := by
  rintro ⟨a', g', e, -⟩
  rw [hv] at e; cases e

/-- An integer of known index evaluates to one `num` word. -/
theorem num_of_intIdx {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {v : At} {j : Idx} (hF : FInv ρ η σs K cx env) (hi : IntIdx cx v j) :
    ∃ rt w n, evalAt env v = some (rt, [w]) ∧ w.val = .num n := by
  obtain ⟨t, hp, ht⟩ := hi
  exact atom_int hF.2.1 hp ht

theorem cntOld_num {th : TTh} {ws : List Word} {w : Word} {n : Nat} (hw : ws = [w]) (hv : w.val = .num n) :
    CntOld th ws := by
  subst hw
  exact cntOld_noNames fun w' hw' l => by
    rw [List.mem_singleton] at hw'; subst hw'; exact not_names_of_num hv l

theorem valB_pair {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y : String} {a b : At} {e : Expr}
    (hT : ThInvE p E th) (hterm : th.term = .let_ y (.pair a b) e)
    (h : r ∈ evalOp g th.env th.σs s (.pair a b)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | pair h1 _ _ =>
      obtain ⟨-, rt, ws, he, -, hl⟩ := use_FInv h1 hF
      simp [evalOp, ol, Option.bind_eq_some_iff] at h
      obtain ⟨t', ws', he', u, us, hu, rfl⟩ := h
      rw [he] at he'
      simp only [Option.some.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      have hc1 := cntOld_evalAt he
      have hc2 := cntOld_evalAt hu
      refine valB_of_cntOld ?_
      have hwc : wc rt = some ws.length := by
        obtain ⟨hs, -, hw, -⟩ := hl
        unfold wc at hw ⊢
        cases hacc : accs rt with
        | none => rw [hacc] at hw; exact absurd rfl hw
        | some us0 => simp only [Option.map_some]; rw [hs us0 hacc]
      show CntOld th (pubWords (.prod rt u) (ws ++ us))
      rw [pubWords]
      split
      · rename_i hsn
        simp only [sNo, Bool.and_eq_true] at hsn
        rw [pubWords_of_sNo hsn.1] at hc1
        rw [pubWords_of_sNo hsn.2] at hc2
        exact cntOld_append hc1 hc2
      · rw [hwc]
        simp only [List.take_left, List.drop_left]
        exact cntOld_append hc1 hc2

theorem valB_mkWord {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y rn : String} {P : Proto} {v tk : At}
    {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .let_ y (.mkWord rn P v tk) e)
    (h : r ∈ evalOp g th.env th.σs s (.mkWord rn P v tk)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | mkWord _ _ h1 _ hi _ _ hg _ _ =>
      obtain ⟨hF1, -⟩ := use_FInv h1 hF
      obtain ⟨rt, w, n, he, hv⟩ := num_of_intIdx hF1 hi
      simp [evalOp, ol, hg, he] at h
      subst h
      exact valB_of_cntOld (cntOld_of_rtsSub ((pubWords_rtsSub _).1 _) (cntOld_num rfl hv))
    | mkWordGhost _ _ _ _ _ _ _ hg _ _ =>
      simp [evalOp, hg] at h
      subst h
      exact valB_of_cntOld (cntOld_pub_noNames fun _ hw => by cases hw)

theorem valB_mkWord2 {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y rn : String} {P : Proto2}
    {v0 v1 tk : At} {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .let_ y (.mkWord2 rn P v0 v1 tk) e)
    (h : r ∈ evalOp g th.env th.σs s (.mkWord2 rn P v0 v1 tk)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | mkWord2 _ _ h1 _ hi0 hi1 _ _ _ _ =>
      obtain ⟨hF1, -⟩ := use_FInv h1 hF
      obtain ⟨rt0, w0, n0, he0, hv0⟩ := num_of_intIdx hF1 hi0
      obtain ⟨rt1, w1, n1, he1, hv1⟩ := num_of_intIdx hF1 hi1
      simp [evalOp, ol, he0, he1] at h
      subst h
      exact valB_of_cntOld (cntOld_of_rtsSub ((pubWords_rtsSub _).1 _)
        (cntOld_append (cntOld_num rfl hv0) (cntOld_num rfl hv1)))

theorem valB_mkEPair {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y rn : String} {P : ECounter}
    {v0 v1 : At} {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .let_ y (.mkEPair rn P v0 v1) e)
    (h : r ∈ evalOp g th.env th.σs s (.mkEPair rn P v0 v1)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | mkEPair _ _ hi0 hi1 _ =>
      obtain ⟨rt0, w0, n0, he0, hv0⟩ := num_of_intIdx hF hi0
      obtain ⟨rt1, w1, n1, he1, hv1⟩ := num_of_intIdx hF hi1
      simp [evalOp, ol, he0, he1] at h
      subst h
      exact valB_of_cntOld (cntOld_of_rtsSub ((pubWords_rtsSub _).1 _)
        (cntOld_append (cntOld_num rfl hv0) (cntOld_num rfl hv1)))

theorem valB_mkTicket {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y rn : String} {N0 P : Proto}
    {v tk : At} {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .let_ y (.mkTicket rn N0 P v tk) e)
    (h : r ∈ evalOp g th.env th.σs s (.mkTicket rn N0 P v tk)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | mkTicket _ _ _ _ _ h1 _ hi _ =>
      obtain ⟨hF1, -⟩ := use_FInv h1 hF
      obtain ⟨rt, w, n, he, hv⟩ := num_of_intIdx hF1 hi
      simp [evalOp, ol, he] at h
      subst h
      exact valB_of_cntOld (cntOld_of_rtsSub ((pubWords_rtsSub _).1 _)
        (cntOld_append (cntOld_num rfl hv) (cntOld_num rfl hv)))


/-! ## Non-`let_` steps (`StepB`) -/

theorem newW_of_cntOld {sto : Sto} {mem : Memory} {pairs P : List Ts} {a : AllocLabel} {N : AllocLabel → Prop}
    {th : TTh} {ws : List Word} (h : CntOld th ws) : ∀ w ∈ ws, NewW sto mem pairs P a N th w := by
  intro w hw
  refine ⟨.inl fun hn => h w hw a hn, .inl fun l hn => ?_⟩
  obtain ⟨b, hb, w0, h0, hn0, -⟩ := h w hw l hn
  exact ⟨b, hb, w0, h0, hn0⟩

/-- A step that keeps the stack and pushes bindings whose counted words are old. -/
theorem stepB_push {sto : Sto} {mem : Memory} {pairs : List Ts} {a : AllocLabel} {N : AllocLabel → Prop}
    {th th' : TTh} (bs : List (String × Ty × List Word)) (hs : th'.stack = th.stack) (he : th'.env = bs ++ th.env)
    (hb : ∀ b ∈ bs, CntOld th (pubWords b.2.1 b.2.2)) : StepB sto mem pairs a N th th' := by
  intro b hm
  unfold Binds at hm
  rw [hs, he, List.append_assoc] at hm
  rcases List.mem_append.1 hm with h | h
  · exact .inr (newW_of_cntOld (hb b h))
  · exact .inl h

theorem stepB_same {sto : Sto} {mem : Memory} {pairs : List Ts} {a : AllocLabel} {N : AllocLabel → Prop}
    {th th' : TTh} (hs : th'.stack = th.stack) (he : th'.env = th.env) : StepB sto mem pairs a N th th' :=
  stepB_push [] hs he (fun _ h => by cases h)

theorem stepB_split {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) (hr : r ∈ tstep g mem pairs th) :
    StepB sto mem pairs lb N th r.2.2 := by
  simp only [tstep, hterm] at hr
  split at hr
  · rename_i u w ws he
    split at hr
    · rename_i us hu
      simp only [List.mem_singleton] at hr
      subst hr
      have hold := cntOld_evalAt he
      have hwc : wc u = some (nWords us) := by simp [wc, hu]
      refine stepB_push [(y, w, ws.drop (nWords us)), (x, u, ws.take (nWords us))] rfl rfl ?_
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rw [pubWords] at hold
      split at hold
      · rename_i hsn
        simp only [sNo, Bool.and_eq_true] at hsn
        rcases hb with rfl | rfl
        · show CntOld th (pubWords w _)
          rw [pubWords_of_sNo hsn.2]; exact cntOld_of_rtsSub (rtsSub_drop _ _) hold
        · show CntOld th (pubWords u _)
          rw [pubWords_of_sNo hsn.1]; exact cntOld_of_rtsSub (rtsSub_take _ _) hold
      · rw [hwc] at hold
        rcases hb with rfl | rfl
        · exact fun v hv => hold v (List.mem_append_right _ hv)
        · exact fun v hv => hold v (List.mem_append_left _ hv)
    · cases hr
  · cases hr

theorem stepB_unpack {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At} {i x : String} {e : Expr}
    (hterm : th.term = .unpack a i x e) (hr : r ∈ tstep g mem pairs th) :
    StepB sto mem pairs lb N th r.2.2 := by
  simp only [tstep, hterm] at hr
  split at hr
  · rename_i b ws he
    simp only [List.mem_singleton] at hr
    subst hr
    have hold := cntOld_evalAt he
    refine stepB_push [(x, b, ws)] rfl rfl ?_
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    show CntOld th (pubWords b ws)
    rw [pubWords] at hold
    split at hold
    · rename_i hsn
      simp only [sNo] at hsn
      rw [pubWords_of_sNo hsn]; exact hold
    · exact hold
  · cases hr

theorem stepB_ifnull {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At} {y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .ifnull a e₁ y e₂) (hr : r ∈ tstep g mem pairs th) :
    StepB sto mem pairs lb N th r.2.2 := by
  simp only [tstep, hterm] at hr
  split at hr
  · rename_i μ u w he
    split at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      exact stepB_same rfl rfl
    · simp only [List.mem_singleton] at hr
      subst hr
      have hold := cntOld_evalAt he
      refine stepB_push [(y, .ptr μ u, [w])] rfl rfl ?_
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      have e : pubWords (.ptr μ u) [w] = pubWords (.ptrOpt μ u) [w] := by
        cases μ <;> simp [pubWords, sNo, mPub]
      show CntOld th (pubWords (.ptr μ u) [w])
      rw [e]; exact hold
    · cases hr
  · cases hr

theorem stepB_parity {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At} {k : String} {ev od : Expr}
    (hterm : th.term = .parity a k ev od) (hr : r ∈ tstep g mem pairs th) :
    StepB sto mem pairs lb N th r.2.2 := by
  simp only [tstep, hterm] at hr
  repeat' split at hr
  all_goals first
    | (simp only [List.mem_singleton] at hr; subst hr; exact stepB_same rfl rfl)
    | cases hr

theorem stepB_ifeq {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a b : At} {yes no : Expr}
    (hterm : th.term = .ifeq a b yes no) (hr : r ∈ tstep g mem pairs th) :
    StepB sto mem pairs lb N th r.2.2 := by
  simp only [tstep, hterm] at hr
  repeat' split at hr
  all_goals first
    | (simp only [List.mem_singleton] at hr; subst hr; exact stepB_same rfl rfl)
    | cases hr

/-! ## `unpackT`: the erased witness, through the Lay bridge -/

theorem guardT_shiftIN (k : Nat) : ∀ (d : Nat) (t : Ty), (shiftIN d t).guardT k = t.guardT k := by
  intro d
  induction d with
  | zero => intro t; rfl
  | succ d ih => intro t; simp only [shiftIN]; rw [TermTv.guardT_shiftI, ih]

theorem guardT_shiftTN : ∀ (c k : Nat) (t : Ty), k < c → (shiftTN c t).guardT k = true := by
  intro c
  induction c with
  | zero => intro k t h; exact absurd h (Nat.not_lt_zero _)
  | succ c ih =>
    intro k t h
    simp only [shiftTN]
    cases k with
    | zero => exact TermTv.guardT_shiftT_at _ 0
    | succ k => rw [TermTv.guardT_shiftT_succ _ 0 k (Nat.zero_le _)]; exact ih k t (Nat.lt_of_succ_lt_succ h)

/-- Closing the variables at or above `c` (all of them bound by `σs`) keeps a variable below `c`
guarded. -/
theorem guardT_substTs (σs : List Ty) : ∀ (b : Ty) (c d k : Nat), k < c → TermClose.tb (σs.length + c) b = true →
    b.guardT k = true → (substTs σs c d b).guardT k = true := by
  intro b
  induction b with
  | tvar j =>
    intro c d k hk htb hg
    simp only [substTs]
    split
    · exact hg
    · rename_i hjc
      split
      · rw [guardT_shiftIN]; exact guardT_shiftTN c k _ hk
      · rename_i hn
        simp only [TermClose.tb, decide_eq_true_eq] at htb
        rw [List.getElem?_eq_none_iff] at hn
        exact absurd htb (by omega)
  | prod a b iha ihb =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs, Bool.and_eq_true] at htb hg ⊢
    exact ⟨iha c d k hk htb.1 hg.1, ihb c d k hk htb.2 hg.2⟩
  | sum a b iha ihb =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs, Bool.and_eq_true] at htb hg ⊢
    exact ⟨iha c d k hk htb.1 hg.1, ihb c d k hk htb.2 hg.2⟩
  | code a b _ iha ihb =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs, Bool.and_eq_true] at htb hg ⊢
    exact ⟨iha c d k hk htb.1 hg.1, ihb c d k hk htb.2 hg.2⟩
  | array i t ih =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs] at htb hg ⊢
    exact ih c d k hk htb hg
  | mu t ih =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs] at htb hg ⊢
    exact ih (c + 1) d (k + 1) (Nat.succ_lt_succ hk) (by rw [← Nat.add_assoc]; exact htb) hg
  | tex κ t ih =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs] at htb hg ⊢
    exact ih (c + 1) d (k + 1) (Nat.succ_lt_succ hk) (by rw [← Nat.add_assoc]; exact htb) hg
  | iall t ih =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs] at htb hg ⊢
    exact ih c (d + 1) k hk htb hg
  | iex t ih =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs] at htb hg ⊢
    exact ih c (d + 1) k hk htb hg
  | refine t ψ ih =>
    intro c d k hk htb hg
    simp only [TermClose.tb, Ty.guardT, substTs] at htb hg ⊢
    exact ih c d k hk htb hg
  | _ => intro c d k _ _ _; simp [substTs, Ty.guardT]

theorem stepB_unpackT {p : Prog} {E : TEnv} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At} {α x : String}
    {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .unpackT a α x e) (hr : r ∈ tstep g mem pairs th) :
    StepB sto mem pairs lb N th r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, htv, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | unpackT hu hg hb hTe =>
    rename_i κ b
    obtain ⟨-, rt, ws, hea, -, hl⟩ := use_FInv hu hF
    obtain ⟨-, htb, -⟩ := TermTv.use_TvOK hu htv
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨rb, rfl, -⟩ := eskel_eq_tex hs
    have hy := hl.2.2.2.2
    simp only [close, substTs, lyt, etok, Ty.tex.injEq] at hy
    have hgL : (substTs th.σs 1 0 b).guardT 0 = true := by
      refine guardT_substTs _ b 1 0 0 Nat.zero_lt_one (TermClose.tb_mono b (by simpa [TermClose.tb] using htb) ?_) hg
      have := hF.2.2.2.2.1
      omega
    have e2 : pubWords (Ty.tex κ rb) ws = pubWords (Ty.tex κ (substTs th.σs 1 0 b)) ws := pubWords_Lay hl
    have e3 : pubWords (Ty.substT 0 .unit rb) ws = pubWords (Ty.substT 0 .unit (substTs th.σs 1 0 b)) ws := by
      refine pubWords_elyt (d := 0) ?_ ws
      congr 1
      rw [lyt_substT_unit, lyt_substT_unit, hy.2]
    have e1 : pubWords (Ty.substT 0 .unit rb) ws = pubWords (Ty.tex κ rb) ws := by
      rw [e3, pubWords_unpackT hgL, e2]
    simp only [tstep, hterm, hea, List.mem_singleton] at hr
    subst hr
    refine stepB_push [(x, Ty.substT 0 .unit rb, ws)] rfl rfl ?_
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    show CntOld th (pubWords (Ty.substT 0 .unit rb) ws)
    rw [e1]
    exact cntOld_evalAt hea

end TermK2a

#print axioms TermK2a.cntOld_of_rtsSub
#print axioms TermK2a.cntOld_append
#print axioms TermK2a.cntOld_nil
#print axioms TermK2a.cntOld_bind
#print axioms TermK2a.mem_binds_of_env
#print axioms TermK2a.cntOld_env
#print axioms TermK2a.cntOld_lookup
#print axioms TermK2a.cntOld_noNames
#print axioms TermK2a.cntOld_pub_noNames
#print axioms TermK2a.not_names_num
#print axioms TermK2a.not_names_addW
#print axioms TermK2a.not_names_subW
#print axioms TermK2a.valB_add
#print axioms TermK2a.valB_sub
#print axioms TermK2a.valB_cvt
#print axioms TermK2a.valB_toInt
#print axioms TermK2a.valB_asLanes
#print axioms TermK2a.valB_fop
#print axioms TermK2a.valB_fcmp
#print axioms TermK2a.valB_fop1
#print axioms TermK2a.valB_lane
#print axioms TermK2a.valB_setLane
#print axioms TermK2a.valB_rem
#print axioms TermK2a.valB_bits
#print axioms TermK2a.valB_bit1
#print axioms TermK2a.valB_vmatch
#print axioms TermK2a.valB_band
#print axioms TermK2a.valB_nil
#print axioms TermK2a.valB_of_nil
#print axioms TermK2a.valB_store
#print axioms TermK2a.valB_stl
#print axioms TermK2a.valB_stlw
#print axioms TermK2a.valB_stp
#print axioms TermK2a.valB_fence
#print axioms TermK2a.valB_borrow
#print axioms TermK2a.valB_call
#print axioms TermK2a.valB_zero
#print axioms TermK2a.valB_claim
#print axioms TermK2a.valB_freeze
#print axioms TermK2a.valB_endBorrow
#print axioms TermK2a.valB_callc
#print axioms TermK2a.valB_atom
#print axioms TermK2a.valB_nameI
#print axioms TermK2a.valB_validate
#print axioms TermK2a.valB_null
#print axioms TermK2a.valB_fnptr
#print axioms TermK2a.valB_of_pubNil
#print axioms TermK2a.valB_new
#print axioms TermK2a.valB_newBuf
#print axioms TermK2a.valB_intoRgn
#print axioms TermK2a.pubWords_cellOf
#print axioms TermK2a.pubWords_loc
#print axioms TermK2a.pubWords_bufElem
#print axioms TermK2a.valB_reword
#print axioms TermK2a.names_offs
#print axioms TermK2a.valB_fld
#print axioms TermK2a.valB_idx
#print axioms TermK2a.valB_bufRes
#print axioms TermK2a.valB_bufInit
#print axioms TermK2a.not_names_of_num
#print axioms TermK2a.num_of_intIdx
#print axioms TermK2a.cntOld_num
#print axioms TermK2a.valB_pair
#print axioms TermK2a.valB_mkWord
#print axioms TermK2a.valB_mkWord2
#print axioms TermK2a.valB_mkEPair
#print axioms TermK2a.valB_mkTicket
#print axioms TermK2a.newW_of_cntOld
#print axioms TermK2a.stepB_push
#print axioms TermK2a.stepB_same
#print axioms TermK2a.stepB_split
#print axioms TermK2a.stepB_unpack
#print axioms TermK2a.stepB_ifnull
#print axioms TermK2a.stepB_parity
#print axioms TermK2a.stepB_ifeq
#print axioms TermK2a.guardT_shiftIN
#print axioms TermK2a.guardT_shiftTN
#print axioms TermK2a.guardT_substTs
#print axioms TermK2a.stepB_unpackT
