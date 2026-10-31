import WeakCore.LiftPosZero
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! **DPub**: the value-keyed pub-position predicate `PubPos η t rt ws` and the named
D5 (b) fact `D5bTmp`.

`PubPos η t rt ws`: position 0 of the value `ws` at type `t` / runtime shape `rt` reaches a `pub`
reference head, following `gc`'s own recursion: single-word wrappers refine/iex/iall/mu/tex, prod components
by width, UNBOXED sums by the value's decoded arm (`decodeArm`), boxed sums false (except a nested boxed arm,
which re-reads the same pointer, as `gc` does); type variables read through the witness `η.wit` by the same
recursion (their own variables false).  It over-approximates exactly the positions where `gc` can choose the
copy (`gc_pp`, proved), so `D5bTmp` is used only there.  `D5bTmp` is D5 (b)'s refine clause at `PubPos`; it is
discharged by definition (`D5bTmp_holds`) and never appears in an exit statement. -/

/-- **D5bTmp** (the named D5 (b) fact): the refine clause at `PubPos`. -/
def D5bTmp : Prop :=
  ∀ (ρ : Nat → Nat) (η : TEnv) (t : Ty) (ψ : Pred) (rt : Shp) (ws : List Word),
    (VRF False) ρ η (.refine t ψ) rt ws → PubPos η t rt ws = true → FreshW η ws ∨ IniR ρ η.rc ψ ws

/-- **D5bTmp discharged**: the ♭ refine arm reads `PubPosE`, and `PubPos` gives it at
`η.box` (`PubPosE_of`).  `D5bTmp` is no longer a premise of anything. -/
theorem D5bTmp_holds : D5bTmp := fun _ _ _ _ _ _ h hp => h.2.2 (PubPosE_of hp)

/-- The resourceful reading of `D5bTmp` (one named fact, stated resource-free). -/
theorem D5bTmp.toR (hD : D5bTmp) {ρ : Nat → Nat} {η : TEnv} {t : Ty} {ψ : Pred} {rt : Shp} {ws : List Word}
    {R : Res} (hl : RLink η) (h : VRRB ρ η (.refine t ψ) rt ws R) (hp : PubPos η t rt ws = true) :
    FreshW η ws ∨ IniR ρ η.rc ψ ws :=
  hD ρ η t ψ rt ws (VRR_VRB (bkG := False) (.refine t ψ) hl h) hp

section
variable {cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

/-- The tvar oracle puts the copy only where the pub-position oracle is true. -/
def TDp (cpy : WeakMem.AllocLabel → WeakMem.AllocLabel)
    (T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
    (PT : Nat → Shp → List Word → Nat → Bool) : Prop :=
  ∀ k rt ws i, T k rt ws i = cpy → PT k rt ws i = true

theorem TDp.sh {T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel}
    {PT : Nat → Shp → List Word → Nat → Bool} (hσ : σ ≠ cpy) (h : TDp cpy T PT) : TDp cpy (shT σ T) (shPT PT)
  | 0, _, _, _, e => absurd e hσ
  | k + 1, rt, ws, i, e => h k rt ws i e

theorem TDp.cst (hσ : σ ≠ cpy) (PT : Nat → Shp → List Word → Nat → Bool) : TDp cpy (fun _ _ _ _ => σ) PT :=
  fun _ _ _ _ e => absurd e hσ

/-- The relabel's three maps differ as functions (from any copied label). -/
def NeC (cpy σ : WeakMem.AllocLabel → WeakMem.AllocLabel) (bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel) : Prop :=
  σ ≠ cpy ∧ ∀ k, (fun y => bv y k) ≠ cpy

theorem TDp.push0 {T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {η : TEnv}
    (h : NeC cpy σ bv → TDp cpy T (PTop η)) (s : Ty) : NeC cpy σ bv → TDp cpy (shT σ T) (PTop (η.push0 s))
  | hn, 0, _, _, _, e => absurd e hn.1
  | hn, k + 1, rt, ws, i, e => by
    have := h hn k rt ws i e
    simpa [PTop, TEnv.push0, TEnv.ins, TEnv.insR] using this

/-- The copy at some position `i` implies `Q i`. -/
def CpAt (cpy : WeakMem.AllocLabel → WeakMem.AllocLabel) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
    (Q : Nat → Prop) : Prop := ∀ i, G i = cpy → Q i

/-- **gc_pp**: `gc` chooses the copy only at a pub position. -/
theorem gc_pp (hσ : σ ≠ cpy) (hbv : ∀ k, (fun y => bv y k) ≠ cpy) (t : Ty) :
    ∀ (T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (η : TEnv)
      (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word) (i : Nat), TDp cpy T PT →
      gc cpy σ Cp bv T TU η t rt ws i = cpy → pp PT η.box t rt ws i = true := by
  induction t with
  | ptr μ u _ =>
    intro T TU η PT rt ws i hT h; cases μ <;> simp only [gc, pubG] at h <;> simp only [pp] <;>
      first | exact absurd h hσ | (split at h <;> rename_i hc <;> first | simp [hc.1] | exact absurd h hσ)
  | ptrOpt μ u _ =>
    intro T TU η PT rt ws i hT h; cases μ <;> simp only [gc, pubG] at h <;> simp only [pp] <;>
      first | exact absurd h hσ | (split at h <;> rename_i hc <;> first | simp [hc.1] | exact absurd h hσ)
  | loc μ u _ =>
    intro T TU η PT rt ws i hT h; cases μ <;> simp only [gc, pubG] at h <;> simp only [pp] <;>
      first | exact absurd h hσ | (split at h <;> rename_i hc <;> first | simp [hc.1] | exact absurd h hσ)
  | refine t ψ ih => intro T TU η PT rt ws i hT h; simp only [gc] at h; simp only [pp]; exact ih T TU η PT rt ws i hT h
  | iex b ih =>
    intro T TU η PT rt ws i hT h
    cases rt <;> simp only [gc] at h <;> simp only [pp] <;> first | exact absurd h hσ | exact ih T TU η PT _ ws i hT h
  | iall b ih => intro T TU η PT rt ws i hT h; simp only [gc] at h; simp only [pp]; exact ih T TU η PT rt ws i hT h
  | tvar k => intro T TU η PT rt ws i hT h; simp only [gc] at h; simp only [pp]; exact hT k rt ws i h
  | mu b ih =>
    intro T TU η PT rt ws i hT h; simp only [gc] at h; simp only [pp]
    exact ih _ _ η (shPT PT) rt ws i (TDp.sh hσ hT) h
  | tex κ b ih =>
    intro T TU η PT rt ws i hT h
    cases rt <;> simp only [gc] at h <;> simp only [pp] <;>
      first | exact absurd h hσ | exact ih _ _ η (shPT PT) _ ws i (TDp.sh hσ hT) h
  | prod a b iha ihb =>
    intro T TU η PT rt ws i hT h
    cases rt <;> simp only [gc] at h <;> simp only [pp] <;> try exact absurd h hσ
    rename_i ra rb
    cases hw : ra.wc <;> simp only [hw] at h ⊢
    · exact absurd h hσ
    · rename_i n
      by_cases hi : i < n <;> simp only [hi, if_true, if_false] at h ⊢
      · exact iha T TU η PT _ _ _ hT h
      · exact ihb T TU η PT _ _ _ hT h
  | sum a b iha ihb =>
    intro T TU η PT rt ws i hT h
    cases rt <;> simp only [gc] at h <;> simp only [pp] <;> try exact absurd h hσ
    rename_i n R
    cases R <;> simp only at h ⊢ <;> try exact absurd h hσ
    rename_i Ra Rb
    by_cases hb : (Ty.sum Ra Rb).tier = .boxed <;> simp only [hb, if_true, if_false] at h ⊢
    · revert h
      generalize ws.map (fun w : Word => w.val) = vs
      intro h
      split at h
      · rename_i s x
        try dsimp only
        cases hB : η.box x.label with
        | none => (try rw [hB] at h); exact absurd h hσ
        | some B =>
          simp only [hB] at h ⊢
          by_cases hc : B.tag - s < (armsOf Ra).length
          · rw [if_pos hc] at h ⊢
            by_cases hr : isBoxed Ra = true
            · rw [if_pos hr] at h ⊢; exact iha T TU η PT _ _ _ hT h
            · rw [if_neg hr] at h
              cases ho : ofArm Ra (B.tag - s) B.pay <;> (try simp only [ho] at h) <;>
                first | exact absurd h (hbv _) | exact absurd h hσ
          · rw [if_neg hc] at h ⊢
            by_cases hr : isBoxed Rb = true
            · rw [if_pos hr] at h ⊢; exact ihb T TU η PT _ _ _ hT h
            · rw [if_neg hr] at h
              cases ho : ofArm Rb (B.tag - s - (armsOf Ra).length) B.pay <;> (try simp only [ho] at h) <;>
                first | exact absurd h (hbv _) | exact absurd h hσ
      · exact absurd h hσ
    · cases hd : decodeArm (Ty.sum Ra Rb).tier (armsOf (Ty.sum Ra Rb)) ws with
      | none => (try simp only [hd] at h); exact absurd h hσ
      | some jp =>
        obtain ⟨j, p⟩ := jp
        (try simp only [hd] at h); try dsimp only at h ⊢
        by_cases hp : p = []
        · rw [if_pos hp] at h; exact absurd h hσ
        · rw [if_neg hp] at h ⊢
          by_cases hj : j < (armsOf Ra).length
          · rw [if_pos hj] at h ⊢
            cases ho : ofArm Ra j p with
            | none => (try simp only [ho] at h); exact absurd h hσ
            | some q =>
              (try simp only [ho] at h); (try dsimp only at h ⊢); rw [unI_shIA] at h; exact iha T TU η PT _ _ _ hT h
          · rw [if_neg hj] at h ⊢
            cases ho : ofArm Rb (j - (armsOf Ra).length) p with
            | none => (try simp only [ho] at h); exact absurd h hσ
            | some q =>
              (try simp only [ho] at h); (try dsimp only at h ⊢); rw [unI_shIA] at h; exact ihb T TU η PT _ _ _ hT h
  | tid =>
    intro T TU η PT rt ws i hT h; simp only [gc, pubG] at h; simp only [pp]
    split at h
    · rename_i hc; simp [hc.1]
    · exact absurd h hσ
  | _ => intro T TU η PT rt ws i hT h; simp only [gc] at h; exact absurd h hσ

end
end TermSound.Flat
