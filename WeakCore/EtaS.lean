import WeakCore.EtaL
/-! **EtaS** (B11 on (R′), the supply obligation): the supply `∃ b, FreshSup P b E` is preserved by every
`EFootPB` env step.  The new base is the max of the old base, a bound on the step's fresh labels, and a bound on
the payload labels of the boxes at those labels (finitely many), so no invariant beyond `EFootPB` is needed. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermOwnX2.Flat
  TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A strict upper bound on the labels the words mention. -/
def supWB : List Word → Nat
  | [] => 0
  | w :: ws => (match w.val with | WeakMem.Val.loc a _ => a.label + 1 | _ => 0) + supWB ws

theorem lt_supWB : ∀ {ws : List Word} {w : Word}, w ∈ ws → ∀ {a : Address} {t : Nat},
    w.val = WeakMem.Val.loc a t → @LT.lt Nat instLTNat a.label (supWB ws)
  | [], _, hm, _, _, _ => absurd hm (List.not_mem_nil)
  | w' :: ws, w, hm, a, t, hv => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [supWB, hv]; omega
    · have := lt_supWB hm hv; simp only [supWB]; omega

/-- A bound on the payload labels of the boxes below label `L`. -/
def supBB (E : TEnv) : Nat → Nat
  | 0 => 0
  | L + 1 => supBB E L + (match E.box L with | some B => supWB B.pay | none => 0)

theorem le_supBB {E : TEnv} {B : Box} {l : Nat} (hb : E.box l = some B) : ∀ {L : Nat}, l < L → supWB B.pay ≤ supBB E L
  | 0, h => absurd h (Nat.not_lt_zero _)
  | L + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · have := le_supBB hb h; simp only [supBB]; omega
    · simp only [supBB, hb]; omega

/-- A strict bound on the fresh labels of a step ending at `n'` allocations. -/
def supFB (g : G) (n' : Nat) : Nat := g.lbase + g.i + g.n * n' + 1

theorem freshIn_lt_supFB {g : G} {n n' : Nat} {l : AllocLabel} (h : FreshIn g n n' l) : @LT.lt Nat instLTNat l (supFB g n') := by
  obtain ⟨j, -, hj, rfl⟩ := h
  have := Nat.mul_le_mul_left g.n (Nat.le_of_lt hj)
  unfold freshLabel supFB; show @LT.lt Nat instLTNat _ _; omega

theorem tail_ge {P : Plan} {b : Nat} {l : AllocLabel} (h : P.Tail b l) : @LE.le Nat instLENat b l := by
  obtain ⟨k, hk, rfl⟩ := h; exact Nat.le_trans hk (Plan.fl_ge k)

/-- The new base after an env step ending at `n'` allocations. -/
def supB (b : Nat) (g : G) (E' : TEnv) (n' : Nat) : Nat := max b (max (supFB g n') (supBB E' (supFB g n')))

theorem freshSup_foot {P : Plan} {b : Nat} {g : G} {E E' : TEnv} {s s' : St} (hs : FreshSup P b E)
    (hf : EFootPB g E E' s s') : FreshSup P (supB b g E' s'.nalloc) E' := by
  obtain ⟨_, _, hsto, hbox, hini, hpfr, _, hseen, _, _, _, _, hrini, _⟩ := hf
  have hb : b ≤ supB b g E' s'.nalloc := Nat.le_max_left _ _
  have hF : supFB g s'.nalloc ≤ supB b g E' s'.nalloc := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hP : supBB E' (supFB g s'.nalloc) ≤ supB b g E' s'.nalloc :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have tl : ∀ l, P.Tail (supB b g E' s'.nalloc) l → P.Tail b l := fun l ht => Plan.Tail_mono hb ht
  have nF : ∀ l, P.Tail (supB b g E' s'.nalloc) l → ¬ FreshIn g s.nalloc s'.nalloc l := fun l ht hfi => by
    have := tail_ge ht; have := freshIn_lt_supFB hfi; omega
  have nO : ∀ l, P.Tail (supB b g E' s'.nalloc) l → ¬ OwnAt E l := fun l ht ho => by
    obtain ⟨c, hc, -⟩ := ho; rw [hs.sto l (tl l ht)] at hc; cases hc
  refine ⟨fun l ht => ?_, fun l ht => ?_, fun l ht => ?_, fun l ht => ?_, fun l ht => ?_, fun l ht => ?_, ?_⟩
  · rcases hsto l with h | ⟨h, -⟩
    · rw [h]; exact hs.sto l (tl l ht)
    · exact absurd h (nF l ht)
  · rcases hbox l with h | ⟨h, -⟩
    · rw [h]; exact hs.box l (tl l ht)
    · exact absurd h (nF l ht)
  · rcases (hini l).2 with h | h | ⟨h, -⟩
    · rw [h]; exact hs.ini l (tl l ht)
    · exact absurd h (nF l ht)
    · exact absurd h (nO l ht)
  · rcases hrini l with h | h | h
    · rw [h]; exact hs.rini l (tl l ht)
    · exact absurd h (nF l ht)
    · exact absurd h (nO l ht)
  · rcases hpfr l with h | ⟨-, F, -, -, -, h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hs.pfr l (tl l ht)
    · exact absurd h (nO l ht)
    · exact absurd h (nF l ht)
  · intro hsn
    rcases hseen l hsn with h | h | h
    · exact hs.seen l (tl l ht) h
    · exact nO l ht h
    · exact nF l ht h
  · intro x B hx w hw a t hv ht
    rcases hbox x with h | ⟨hfi, -⟩
    · rw [h] at hx; exact hs.pay x B hx w hw a t hv (tl _ ht)
    · have h1 := lt_supWB hw hv
      have h2 := le_supBB hx (freshIn_lt_supFB hfi)
      have := tail_ge ht; omega

/-- The supply obligation: the supply is preserved by an env step. -/
theorem sup_foot {P : Plan} {g : G} {E E' : TEnv} {s s' : St} (hs : ∃ b, FreshSup P b E)
    (hf : EFootPB g E E' s s') : ∃ b, FreshSup P b E' :=
  let ⟨_, h⟩ := hs; ⟨_, freshSup_foot h hf⟩

/-- An env step that only grows nothing (`E' = E`) keeps the supply trivially. -/
theorem sup_of_eq {P : Plan} {E E' : TEnv} (hs : ∃ b, FreshSup P b E) (h : E' = E) : ∃ b, FreshSup P b E' :=
  h ▸ hs

end CertWinProof
