import WeakCore.PubPos
/-! **PubPosL** (P3): the `pp` / `PubPosE` twins of the `TEnv.pubTop`
lemmas.  All `pp` lemmas are generic over the box map `bx` and the tvar oracle `PT`. -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! ### Index-only maps (`pp` reads no index). -/

theorem pp_shiftI (bx : WeakMem.AllocLabel → Option Box) (t : Ty) :
    ∀ (c : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (t.shiftI c) rt ws = pp PT bx t rt ws := by
  induction t with
  | ptr μ u _ => intro c PT rt ws; cases μ <;> rfl
  | ptrOpt μ u _ => intro c PT rt ws; cases μ <;> rfl
  | loc μ u _ => intro c PT rt ws; cases μ <;> rfl
  | prod a b iha ihb => intro c PT rt ws; simp only [Ty.shiftI, pp, iha, ihb]
  | sum a b iha ihb => intro c PT rt ws; simp only [Ty.shiftI, pp, iha, ihb]
  | refine t ψ ih => intro c PT rt ws; simp only [Ty.shiftI, pp, ih]
  | iall t ih => intro c PT rt ws; simp only [Ty.shiftI, pp, ih]
  | iex t ih => intro c PT rt ws; simp only [Ty.shiftI, pp, ih]
  | mu t ih => intro c PT rt ws; simp only [Ty.shiftI, pp, ih]
  | tex κ t ih => intro c PT rt ws; simp only [Ty.shiftI, pp, ih]
  | _ => intro c PT rt ws; rfl

theorem pp_shiftIN (bx : WeakMem.AllocLabel → Option Box) (σ : Ty) :
    ∀ (n : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (shiftIN n σ) rt ws = pp PT bx σ rt ws := by
  intro n
  induction n with
  | zero => intro PT rt ws; rfl
  | succ n ih => intro PT rt ws; simp only [shiftIN]; rw [pp_shiftI, ih]

theorem pp_instT (bx : WeakMem.AllocLabel → Option Box) (us : List Idx) (t : Ty) :
    ∀ (d : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (instT us d t) rt ws = pp PT bx t rt ws := by
  induction t with
  | ptr μ u _ => intro d PT rt ws; cases μ <;> rfl
  | ptrOpt μ u _ => intro d PT rt ws; cases μ <;> rfl
  | loc μ u _ => intro d PT rt ws; cases μ <;> rfl
  | prod a b iha ihb => intro d PT rt ws; simp only [instT, pp, iha, ihb]
  | sum a b iha ihb => intro d PT rt ws; simp only [instT, pp, iha, ihb]
  | refine t ψ ih => intro d PT rt ws; simp only [instT, pp, ih]
  | iall t ih => intro d PT rt ws; simp only [instT, pp, ih]
  | iex t ih => intro d PT rt ws; simp only [instT, pp, ih]
  | mu t ih => intro d PT rt ws; simp only [instT, pp, ih]
  | tex κ t ih => intro d PT rt ws; simp only [instT, pp, ih]
  | _ => intro d PT rt ws; rfl

theorem pp_tyEq (bx : WeakMem.AllocLabel → Option Box) {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) :
    ∀ (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx t rt ws = pp PT bx u rt ws := by
  induction h with
  | refl => intro PT rt ws; rfl
  | ptr hm _ _ => intro PT rt ws; cases hm <;> rfl
  | ptrOpt hm _ _ => intro PT rt ws; cases hm <;> rfl
  | loc hm _ _ => intro PT rt ws; cases hm <;> rfl
  | prod _ _ iha ihb => intro PT rt ws; simp only [pp, iha, ihb]
  | sum _ _ iha ihb => intro PT rt ws; simp only [pp, iha, ihb]
  | mu _ ih => intro PT rt ws; simp only [pp, ih]
  | tex _ ih => intro PT rt ws; simp only [pp, ih]
  | iall _ ih => intro PT rt ws; simp only [pp, ih]
  | iex _ ih => intro PT rt ws; simp only [pp, ih]
  | refine _ ih => intro PT rt ws; simp only [pp, ih]
  | refineIni _ _ ih => intro PT rt ws; simp only [pp, ih]
  | _ => intro PT rt ws; rfl

/-! ### Oracle irrelevance / agreement. -/

theorem pp_agree (bx : WeakMem.AllocLabel → Option Box) (t : Ty) :
    ∀ (PT PT' : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    (∀ k, t.tyMentions k = true → PT k = PT' k) → pp PT bx t rt ws = pp PT' bx t rt ws := by
  induction t with
  | tvar k => intro PT PT' rt ws h; simp only [pp]; rw [h k (by simp [Ty.tyMentions])]
  | ptr μ u _ => intro PT PT' rt ws _; cases μ <;> rfl
  | ptrOpt μ u _ => intro PT PT' rt ws _; cases μ <;> rfl
  | loc μ u _ => intro PT PT' rt ws _; cases μ <;> rfl
  | prod a b iha ihb =>
    intro PT PT' rt ws h
    have ea : ∀ rt ws, pp PT bx a rt ws = pp PT' bx a rt ws :=
      fun rt ws => iha PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
    have eb : ∀ rt ws, pp PT bx b rt ws = pp PT' bx b rt ws :=
      fun rt ws => ihb PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
    simp only [pp, ea, eb]
  | sum a b iha ihb =>
    intro PT PT' rt ws h
    have ea : ∀ rt ws, pp PT bx a rt ws = pp PT' bx a rt ws :=
      fun rt ws => iha PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
    have eb : ∀ rt ws, pp PT bx b rt ws = pp PT' bx b rt ws :=
      fun rt ws => ihb PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
    simp only [pp, ea, eb]
  | refine t ψ ih =>
    intro PT PT' rt ws h; simp only [pp]; exact ih PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
  | iall t ih =>
    intro PT PT' rt ws h; simp only [pp]; exact ih PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
  | iex t ih =>
    intro PT PT' rt ws h
    have e : ∀ rt ws, pp PT bx t rt ws = pp PT' bx t rt ws :=
      fun rt ws => ih PT PT' rt ws (fun k hk => h k (by simp [Ty.tyMentions, hk]))
    simp only [pp, e]
  | mu t ih =>
    intro PT PT' rt ws h; simp only [pp]
    refine ih _ _ rt ws (fun k hk => ?_)
    cases k with
    | zero => rfl
    | succ k => funext rt' ws'; exact congrFun (congrFun (h k (by simpa [Ty.tyMentions] using hk)) rt') ws'
  | tex κ t ih =>
    intro PT PT' rt ws h
    have e : ∀ rt ws, pp (shPT PT) bx t rt ws = pp (shPT PT') bx t rt ws := by
      intro rt ws
      refine ih _ _ rt ws (fun k hk => ?_)
      cases k with
      | zero => rfl
      | succ k => funext rt' ws'; exact congrFun (congrFun (h k (by simpa [Ty.tyMentions] using hk)) rt') ws'
    simp only [pp, e]
  | _ => intro PT PT' rt ws _; rfl

theorem pp_tb (bx : WeakMem.AllocLabel → Option Box) (t : Ty) :
    ∀ (c : Nat) (PT PT' : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    tb c t = true → (∀ k, k < c → PT k = PT' k) → pp PT bx t rt ws = pp PT' bx t rt ws := by
  intro c PT PT' rt ws h hP
  refine pp_agree bx t PT PT' rt ws (fun k hk => hP k ?_)
  exact tb_mentions t c h k hk
where
  tb_mentions : ∀ (t : Ty) (c : Nat), tb c t = true → ∀ k, t.tyMentions k = true → k < c := by
    intro t
    induction t with
    | tvar j => intro c h k hk; simp [tb] at h; simp [Ty.tyMentions] at hk; omega
    | prod a b iha ihb =>
      intro c h k hk; simp [tb] at h; simp [Ty.tyMentions] at hk
      rcases hk with hk | hk
      · exact iha c h.1 k hk
      · exact ihb c h.2 k hk
    | sum a b iha ihb =>
      intro c h k hk; simp [tb] at h; simp [Ty.tyMentions] at hk
      rcases hk with hk | hk
      · exact iha c h.1 k hk
      · exact ihb c h.2 k hk
    | code a b _ iha ihb =>
      intro c h k hk; simp [tb] at h; simp [Ty.tyMentions] at hk
      rcases hk with hk | hk
      · exact iha c h.1 k hk
      · exact ihb c h.2 k hk
    | array _ t ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | ptr _ t ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | ptrOpt _ t ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | loc _ t ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | iall t ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | iex t ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | refine t _ ih => intro c h k hk; exact ih c (by simpa [tb] using h) k (by simpa [Ty.tyMentions] using hk)
    | mu t ih =>
      intro c h k hk
      have := ih (c + 1) (by simpa [tb] using h) (k + 1) (by simpa [Ty.tyMentions] using hk); omega
    | tex _ t ih =>
      intro c h k hk
      have := ih (c + 1) (by simpa [tb] using h) (k + 1) (by simpa [Ty.tyMentions] using hk); omega
    | _ => intro c _ k hk; simp [Ty.tyMentions] at hk

/-! ### Type-variable maps: the oracle moves. -/

theorem shPT_sh (PT : Nat → Shp → List Word → Nat → Bool) (c : Nat) :
    (fun k => shPT PT (if k < c + 1 then k else k + 1)) = shPT (fun k => PT (if k < c then k else k + 1)) := by
  funext k rt ws
  cases k with
  | zero => simp [shPT]
  | succ k =>
    by_cases h : k < c
    · simp [shPT, h, show k + 1 < c + 1 by omega]
    · simp [shPT, h, show ¬ k + 1 < c + 1 by omega]

theorem pp_shiftT (bx : WeakMem.AllocLabel → Option Box) (t : Ty) :
    ∀ (c : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (t.shiftT c) rt ws = pp (fun k => PT (if k < c then k else k + 1)) bx t rt ws := by
  induction t with
  | tvar k =>
    intro c PT rt ws
    simp only [Ty.shiftT, pp]
    by_cases h : k < c
    · rw [if_neg (by omega), if_pos h]; rfl
    · rw [if_pos (by omega), if_neg h]; rfl
  | ptr μ u _ => intro c PT rt ws; cases μ <;> rfl
  | ptrOpt μ u _ => intro c PT rt ws; cases μ <;> rfl
  | loc μ u _ => intro c PT rt ws; cases μ <;> rfl
  | prod a b iha ihb => intro c PT rt ws; simp only [Ty.shiftT, pp, iha, ihb]
  | sum a b iha ihb => intro c PT rt ws; simp only [Ty.shiftT, pp, iha, ihb]
  | refine t ψ ih => intro c PT rt ws; simp only [Ty.shiftT, pp, ih]
  | iall t ih => intro c PT rt ws; simp only [Ty.shiftT, pp, ih]
  | iex t ih => intro c PT rt ws; simp only [Ty.shiftT, pp, ih]
  | mu t ih => intro c PT rt ws; simp only [Ty.shiftT, pp]; rw [ih, shPT_sh]
  | tex κ t ih =>
    intro c PT rt ws
    cases rt <;> simp only [Ty.shiftT, pp]
    rw [ih, shPT_sh]
  | _ => intro c PT rt ws; rfl

theorem pp_shiftTN (bx : WeakMem.AllocLabel → Option Box) (σ : Ty) :
    ∀ (n : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (shiftTN n σ) rt ws = pp (fun j => PT (j + n)) bx σ rt ws := by
  intro n
  induction n with
  | zero => intro PT rt ws; rfl
  | succ n ih =>
    intro PT rt ws
    simp only [shiftTN]
    rw [pp_shiftT, ih]
    have e : (fun j => (fun k => PT (if k < 0 then k else k + 1)) (j + n)) = fun j => PT (j + (n + 1)) := by
      funext j; simp only [Nat.not_lt_zero, if_false]; rw [Nat.add_assoc]
    rw [e]

/-- The closing oracle: variables `≥ c` read the (closed) witness by the closed recursion. -/
def ClO (bx : WeakMem.AllocLabel → Option Box) (W : Nat → Ty) (c : Nat)
    (PT : Nat → Shp → List Word → Nat → Bool) : Nat → Shp → List Word → Nat → Bool :=
  fun k => if k < c then PT k else pp (fun _ _ _ _ => false) bx (W (k - c))

theorem ClO_sh (bx : WeakMem.AllocLabel → Option Box) (W : Nat → Ty) (c : Nat)
    (PT : Nat → Shp → List Word → Nat → Bool) : ClO bx W (c + 1) (shPT PT) = shPT (ClO bx W c PT) := by
  funext k rt ws
  cases k with
  | zero => simp [ClO, shPT]
  | succ k =>
    by_cases h : k < c
    · simp [ClO, shPT, h, show k + 1 < c + 1 by omega]
    · simp [ClO, shPT, h, show ¬ k + 1 < c + 1 by omega]

theorem pp_cl (bx : WeakMem.AllocLabel → Option Box) (ρ : Nat → Nat) (W : Nat → Ty) (hW : ∀ j, tb 0 (W j) = true)
    (t : Ty) : ∀ (c d : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (cl ρ W c d t) rt ws = pp (ClO bx W c PT) bx t rt ws := by
  induction t with
  | tvar k =>
    intro c d PT rt ws
    simp only [cl, pp]
    by_cases h : k < c
    · rw [if_pos h]; simp only [pp, ClO, h, if_true]
    · rw [if_neg h]; simp only [ClO, h, if_false]
      exact pp_tb bx _ 0 _ _ rt ws (hW _) (fun k hk => absurd hk (Nat.not_lt_zero k))
  | ptr μ u _ => intro c d PT rt ws; cases μ <;> rfl
  | ptrOpt μ u _ => intro c d PT rt ws; cases μ <;> rfl
  | loc μ u _ => intro c d PT rt ws; cases μ <;> rfl
  | prod a b iha ihb => intro c d PT rt ws; simp only [cl, pp, iha, ihb]
  | sum a b iha ihb => intro c d PT rt ws; simp only [cl, pp, iha, ihb]
  | refine t ψ ih => intro c d PT rt ws; simp only [cl, pp, ih]
  | iall t ih => intro c d PT rt ws; simp only [cl, pp, ih]
  | iex t ih => intro c d PT rt ws; simp only [cl, pp, ih]
  | mu t ih => intro c d PT rt ws; simp only [cl, pp]; rw [ih, ClO_sh]
  | tex κ t ih =>
    intro c d PT rt ws
    cases rt <;> simp only [cl, pp]
    rw [ih, ClO_sh]
  | _ => intro c d PT rt ws; rfl

/-- The simultaneous-substitution oracle. -/
def SubO (bx : WeakMem.AllocLabel → Option Box) (σs : List Ty) (c : Nat)
    (PT : Nat → Shp → List Word → Nat → Bool) : Nat → Shp → List Word → Nat → Bool :=
  fun k => if k < c then PT k else
    match σs[k - c]? with
    | some σ => pp (fun j => PT (j + c)) bx σ
    | none => PT (k - σs.length)

theorem SubO_sh (bx : WeakMem.AllocLabel → Option Box) (σs : List Ty) (c : Nat)
    (PT : Nat → Shp → List Word → Nat → Bool) : SubO bx σs (c + 1) (shPT PT) = shPT (SubO bx σs c PT) := by
  funext k
  cases k with
  | zero => funext rt ws; simp [SubO, shPT]
  | succ k =>
    show SubO bx σs (c + 1) (shPT PT) (k + 1) = SubO bx σs c PT k
    by_cases h : k < c
    · simp only [SubO, h, show k + 1 < c + 1 by omega, if_true]; rfl
    · simp only [SubO, h, show ¬ k + 1 < c + 1 by omega, if_false, show k + 1 - (c + 1) = k - c by omega]
      rcases hs : σs[k - c]? with _ | σ
      · have hl : σs.length ≤ k - c := by
          rcases Nat.lt_or_ge (k - c) σs.length with h' | h'
          · rw [List.getElem?_eq_getElem h'] at hs; cases hs
          · exact h'
        show shPT PT (k + 1 - σs.length) = PT (k - σs.length)
        rw [show k + 1 - σs.length = (k - σs.length) + 1 by omega]; rfl
      · show pp (fun j => shPT PT (j + (c + 1))) bx σ = pp (fun j => PT (j + c)) bx σ
        rfl

theorem pp_substTs (bx : WeakMem.AllocLabel → Option Box) (σs : List Ty) (t : Ty) :
    ∀ (c d : Nat) (PT : Nat → Shp → List Word → Nat → Bool) (rt : Shp) (ws : List Word),
    pp PT bx (substTs σs c d t) rt ws = pp (SubO bx σs c PT) bx t rt ws := by
  induction t with
  | tvar k =>
    intro c d PT rt ws
    simp only [substTs]
    by_cases h : k < c
    · rw [if_pos h]; simp only [pp, SubO, h, if_true]
    · rw [if_neg h]
      simp only [pp, SubO, h, if_false]
      rcases hs : σs[k - c]? with _ | σ
      · rfl
      · simp only []; rw [pp_shiftIN, pp_shiftTN]
  | ptr μ u _ => intro c d PT rt ws; cases μ <;> rfl
  | ptrOpt μ u _ => intro c d PT rt ws; cases μ <;> rfl
  | loc μ u _ => intro c d PT rt ws; cases μ <;> rfl
  | prod a b iha ihb => intro c d PT rt ws; simp only [substTs, pp, iha, ihb]
  | sum a b iha ihb => intro c d PT rt ws; simp only [substTs, pp, iha, ihb]
  | refine t ψ ih => intro c d PT rt ws; simp only [substTs, pp, ih]
  | iall t ih => intro c d PT rt ws; simp only [substTs, pp, ih]
  | iex t ih => intro c d PT rt ws; simp only [substTs, pp, ih]
  | mu t ih => intro c d PT rt ws; simp only [substTs, pp]; rw [ih, SubO_sh]
  | tex κ t ih =>
    intro c d PT rt ws
    cases rt <;> simp only [substTs, pp]
    rw [ih, SubO_sh]
  | _ => intro c d PT rt ws; rfl

end TermSound.Flat
