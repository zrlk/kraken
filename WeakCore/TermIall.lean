import WeakCore.TermScope

/-!
# TermIall: the restated `hia` (T2, option (ii))

`StoreIall ρ η cx th`: at a plain store (`wordOf … = none`) through an `own` or
`pub` reference, the stored cell (for a pointer) or the stored component (for
a locative) has `IallOK` components.  This is the only instance of the old
`hia` the store lemmas use.

Discharge: the reference's cell type is `Fd`-related to `cl ρ η.wit 0 0 u`,
`u` the typing context's target, which the runtime invariant pins (`drf`,
now also `∀`-free, `ProgScopeOK` = ProgScope + ProgIall); the witnesses
`η.wit k` carry no `∀` at traversed positions (`WitAF.ni`).
-/

namespace TermIall
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem IallOK_of_noIallV : ∀ (t : Ty) (ke : KEnv), noIallV t = true → TermTear.IallOK ke t = true := by
  intro t
  induction t with
  | prod a b iha ihb => intro ke h; simp only [noIallV, Bool.and_eq_true] at h; simp [TermTear.IallOK, iha ke h.1, ihb ke h.2]
  | sum a b iha ihb => intro ke h; simp only [noIallV, Bool.and_eq_true] at h; simp [TermTear.IallOK, iha ke h.1, ihb ke h.2]
  | iex t ih => intro ke h; simp only [TermTear.IallOK]; exact ih ke h
  | tex κ t ih => intro ke h; simp only [TermTear.IallOK]; exact ih _ h
  | mu t ih => intro ke h; simp only [TermTear.IallOK]; exact ih _ h
  | refine t ψ ih => intro ke h; simp only [TermTear.IallOK]; exact ih ke h
  | iall t _ => intro ke h; simp [noIallV] at h
  | _ => intro ke _; rfl

theorem noIallV_shiftT : ∀ (t : Ty) (c : Nat), noIallV (t.shiftT c) = noIallV t := by
  intro t
  induction t with
  | tvar k => intro c; simp only [Ty.shiftT]; split <;> rfl
  | prod a b iha ihb => intro c; simp [Ty.shiftT, noIallV, iha, ihb]
  | sum a b iha ihb => intro c; simp [Ty.shiftT, noIallV, iha, ihb]
  | array i t ih => intro c; simp [Ty.shiftT, noIallV, ih]
  | mu t ih => intro c; simp [Ty.shiftT, noIallV, ih]
  | tex κ t ih => intro c; simp [Ty.shiftT, noIallV, ih]
  | iex t ih => intro c; simp [Ty.shiftT, noIallV, ih]
  | refine t ψ ih => intro c; simp [Ty.shiftT, noIallV, ih]
  | _ => intro c; rfl

theorem noIallV_shiftI : ∀ (t : Ty) (c : Nat), noIallV (t.shiftI c) = noIallV t := by
  intro t
  induction t with
  | prod a b iha ihb => intro c; simp [Ty.shiftI, noIallV, iha, ihb]
  | sum a b iha ihb => intro c; simp [Ty.shiftI, noIallV, iha, ihb]
  | array i t ih => intro c; simp [Ty.shiftI, noIallV, ih]
  | mu t ih => intro c; simp [Ty.shiftI, noIallV, ih]
  | tex κ t ih => intro c; simp [Ty.shiftI, noIallV, ih]
  | iex t ih => intro c; simp [Ty.shiftI, noIallV, ih]
  | refine t ψ ih => intro c; simp [Ty.shiftI, noIallV, ih]
  | _ => intro c; rfl

theorem noIallV_substT : ∀ (t : Ty) (j : Nat) (s : Ty), noIallV s = true → noIallV t = true →
    noIallV (Ty.substT j s t) = true := by
  intro t
  induction t with
  | tvar k =>
    intro j s hs _
    simp only [Ty.substT]
    split
    · exact hs
    · split <;> rfl
  | prod a b iha ihb => intro j s hs h; simp only [Ty.substT, noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | sum a b iha ihb => intro j s hs h; simp only [Ty.substT, noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha j s hs h.1, ihb j s hs h.2⟩
  | array i t ih => intro j s hs h; exact ih j s hs h
  | mu t ih => intro j s hs h; exact ih (j + 1) (s.shiftT 0) (by rw [noIallV_shiftT]; exact hs) h
  | tex κ t ih => intro j s hs h; exact ih (j + 1) (s.shiftT 0) (by rw [noIallV_shiftT]; exact hs) h
  | iex t ih => intro j s hs h; exact ih j (s.shiftI 0) (by rw [noIallV_shiftI]; exact hs) h
  | refine t ψ ih => intro j s hs h; exact ih j s hs h
  | iall t _ => intro j s hs h; simp [noIallV] at h
  | _ => intro j s _ _; rfl

theorem noIallV_of_substT : ∀ (t : Ty) (j : Nat) (s : Ty), noIallV (Ty.substT j s t) = true → noIallV t = true := by
  intro t
  induction t with
  | prod a b iha ihb => intro j s h; simp only [Ty.substT, noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha j s h.1, ihb j s h.2⟩
  | sum a b iha ihb => intro j s h; simp only [Ty.substT, noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha j s h.1, ihb j s h.2⟩
  | array i t ih => intro j s h; exact ih j s h
  | mu t ih => intro j s h; exact ih (j + 1) _ h
  | tex κ t ih => intro j s h; exact ih (j + 1) _ h
  | iex t ih => intro j s h; exact ih j _ h
  | refine t ψ ih => intro j s h; exact ih j s h
  | iall t _ => intro j s h; simp [Ty.substT, noIallV] at h
  | _ => intro j s _; rfl

theorem noIallV_unfold {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : noIallV (cl ρ W 0 0 (.mu s)) = true) : noIallV (cl ρ W 0 0 (unfold1 (.mu s))) = true := by
  rw [cl_unfold1 hW, cl_mu_eq]
  rw [cl_mu_eq] at h
  exact noIallV_substT _ 0 _ h (by simp only [noIallV] at h; exact h)

theorem noIallV_fold {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {s : Ty}
    (h : noIallV (cl ρ W 0 0 (unfold1 (.mu s))) = true) : noIallV (cl ρ W 0 0 (.mu s)) = true := by
  rw [cl_unfold1 hW, cl_mu_eq] at h
  rw [cl_mu_eq]
  simp only [unfold1] at h
  simp only [noIallV]
  exact noIallV_of_substT _ 0 _ h

/-- Every `AtOff` component of a `∀`-free type is `∀`-free. -/
theorem noIallV_AtOff {U V : Ty} {d : Nat} (h : AtOff U d V) (hU : noIallV U = true) : noIallV V = true := by
  induction h with
  | here _ => exact hU
  | fst _ ih => simp only [noIallV, Bool.and_eq_true] at hU; exact ih hU.1
  | snd _ _ ih => simp only [noIallV, Bool.and_eq_true] at hU; exact ih hU.2
  | elem _ _ _ ih => exact ih hU
  | mu hW _ _ ih => exact ih (noIallV_unfold hW hU)
  | fold hW _ _ _ ih => exact noIallV_fold hW (ih hU)

/-- A folded cell type of a `∀`-free type is `∀`-free. -/
theorem noIallV_Fd {T U : Ty} (h : Fd T U) (hU : noIallV U = true) : noIallV T = true := by
  induction h with
  | refl => exact hU
  | fold hW _ _ _ ih => exact ih (noIallV_unfold hW hU)

/-! ## The restated `hia` and its discharge -/

/-- **`StoreIall` at a term whose free variables have `drf` runtime types**,
for every typing, given `∀`-free witnesses. -/
theorem storeIall_term {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {cx : Cx}
    {th : TTh} {Rf : Res} (hi : FInvR ρ η th.σs K cx th.env Rf) (henv : EnvDRF th.env th.term)
    (hW : ∀ k, noIallV (η.wit k) = true) : StoreIall ρ η cx th := by
  intro x rel a v tok e t hterm hpk _ rt pw ad hev had cl0 hcl
  have hdt : drf t = true :=
    peek_drf hi hpk (fun y hy => henv y (by rw [hterm]; exact free_let_op (by simp [opAts]) hy))
  refine ⟨fun μ u htu o U hat => ?_, fun μ u U htu _ hfd => ?_⟩
  · subst htu
    simp only [drf, Bool.and_eq_true] at hdt
    cases a with
    | lit n => simp [Cx.peek] at hpk
    | unit => simp [Cx.peek] at hpk
    | var y =>
      obtain ⟨ent, hent, het⟩ := TermScope.peek_var hpk
      obtain ⟨rt', ws, hl, hv, -⟩ := hi.1.2.1 y ent hent
      rw [het] at hv
      simp only [evalAt] at hev
      rw [hl] at hev
      simp only [Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨-, rfl⟩ := hev
      obtain ⟨a0, c0, hws, -, hsto, hfd, -, -⟩ := hv
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
      simp only [addrOf, hws, Option.some.injEq] at had
      subst had
      have hs : (CE η).sto a0.label = η.sto a0.label := rfl
      rw [hs, hsto] at hcl
      cases hcl
      exact IallOK_of_noIallV _ _ (noIallV_AtOff hat (noIallV_Fd hfd (noIallV_cl hW u 0 0 (noIallV_of_drf u hdt.2))))
  · subst htu
    simp only [drf, Bool.and_eq_true] at hdt
    exact IallOK_of_noIallV _ _ (noIallV_Fd hfd (noIallV_cl hW u 0 0 (noIallV_of_drf u hdt.2)))

/-- **T2 restated (`StoreIall`)** at every reachable thread step of a program
passing `ProgScopeOK` (which now includes ProgIall), on runs from a `RunScope`
configuration, the witnesses being `∀`-free by `WitAF`. -/
theorem iall_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hp : ProgScopeOK p = true) (h0 : TermScope.RunScopeR p k arch Sp c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreIall ρ η cx th := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y
  have h := run_drf hp h0 X.run i th X.hth
  have hFI := Y.2.2.2.2.2.1
  exact storeIall_term hFI h.env (WitAF.ni hFI.1.2.2.2.2.2.2.1)

#print axioms noIallV_AtOff
#print axioms noIallV_Fd
#print axioms storeIall_term
#print axioms iall_of

end TermIall
