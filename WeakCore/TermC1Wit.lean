import WeakCore.TermC1Pay

/-! # TermC1Wit: every witness is `drf1`

`WitR1` (frame invariant: every type parameter's witness is `drf1`) and `WitOK1` (a package's witness)
replace `WitR`/`WitOK`'s `share → rgnFree` by an unconditional `drf1`, because `drf1` also looks behind
references.  They are kept at a call (`WitR1_call`), at `unpackT` (`WitR1_pushT`), along a frame's
witness-preserving extensions (`WitR1_wit`) and from the start (`WitR1_nil`); `packT` makes a
`WitOK1` witness (`WitOK1_pack`).  `WitR1_occ` supplies `rgnPay_cl0`'s occurring-witness premise
(`rgnPay_cl0_frame`).
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermScope TermTv

/-- Every type parameter's witness is `drf1` (also behind references). -/
def WitR1 (ke : KEnv) (η : TEnv) : Prop := ∀ k, ke.ask k true (fun _ => true) = true → drf1 (η.wit k) = true

/-- `TermSound.WitOK` with an unconditional `drf1` in place of `share → rgnFree`: what a package's
witness carries at runtime. -/
def WitOK1 (κ : Kind) (s : Ty) : Prop := s.arrFree = true ∧ (κ.share = true → Ty.coupledOK s = true) ∧
    (κ.copy = true → Ty.affine s = false) ∧ (κ.noOwn = true → Ty.noOwn s = true) ∧
    drf1 s = true ∧ noIallV s = true ∧ TermTv.mg s = true

theorem ask_true_iff (ke : KEnv) (k : Nat) : ke.ask k true (fun _ => true) = true ↔ k < ke.length := by
  unfold KEnv.ask
  cases e : ke[k]? with
  | none => simp only [List.getElem?_eq_none_iff] at e; simp; omega
  | some o =>
      have := (List.getElem?_eq_some_iff.mp e).1
      cases o <;> simp [this]

/-- `WitR1` in index form. -/
theorem WitR1_iff {ke : KEnv} {η : TEnv} : WitR1 ke η ↔ ∀ k, k < ke.length → drf1 (η.wit k) = true :=
  ⟨fun h k hk => h k ((ask_true_iff ke k).2 hk), fun h k hk => h k ((ask_true_iff ke k).1 hk)⟩

/-- At the start (no type parameters). -/
theorem WitR1_nil (η : TEnv) : WitR1 [] η := WitR1_iff.2 (fun k hk => absurd hk (Nat.not_lt_zero k))

/-- Along any change that keeps the witnesses (store extensions, `withSto`, `unsee`, ...). -/
theorem WitR1_wit {ke : KEnv} {η η' : TEnv} (he : ∀ k, η'.wit k = η.wit k) (h : WitR1 ke η) :
    WitR1 ke η' := fun k hk => by rw [he k]; exact h k hk

/-- A type variable a `tb c` type mentions is below `c`. -/
theorem mentions_lt : ∀ (t : Ty) (c j : Nat), tb c t = true → t.tyMentions j = true → j < c := by
  intro t
  induction t with
  | tvar k => intro c j h hm; simp only [tb, decide_eq_true_eq] at h; simp only [Ty.tyMentions, beq_iff_eq] at hm; omega
  | prod a b iha ihb | sum a b iha ihb | code a b iha ihb =>
      intro c j h hm; simp only [tb, Bool.and_eq_true] at h; simp only [Ty.tyMentions, Bool.or_eq_true] at hm
      rcases hm with hm | hm
      · exact iha c j h.1 hm
      · exact ihb c j h.2 hm
  | array _ t ih | ptr _ t ih | ptrOpt _ t ih | loc _ t ih | iall t ih | iex t ih | refine t _ ih =>
      intro c j h hm; simp only [tb] at h; simp only [Ty.tyMentions] at hm; exact ih c j h hm
  | mu t ih | tex _ t ih =>
      intro c j h hm; simp only [tb] at h; simp only [Ty.tyMentions] at hm; have := ih (c + 1) (j + 1) h hm; omega
  | _ => intro c j _ hm; simp [Ty.tyMentions] at hm

/-- The witnesses a frame's type mentions are `drf1` (`rgnPay_cl0`'s `hD`). -/
theorem WitR1_occ {ke : KEnv} {η : TEnv} {u : Ty} (h : WitR1 ke η) (ht : tb ke.length u = true) :
    ∀ k, u.tyMentions k = true → drf1 (η.wit k) = true :=
  fun k hm => WitR1_iff.1 h k (mentions_lt u ke.length k ht hm)

/-- A `drf1` type closes to a `drf1` type in a `WitR1` frame. -/
theorem drf1_cl_frame (ρ : Nat → Nat) {ke : KEnv} {η : TEnv} {σ : Ty} (h : WitR1 ke η)
    (ht : tb ke.length σ = true) (hd : drf1 σ = true) : drf1 (cl ρ η.wit 0 0 σ) = true :=
  drf1_cl0K ρ (WitR1_occ h ht) hd

/-- **A region payload in a frame**: `rgnPay_cl0` with `FInv`'s `WitSh`/`WitC` and `WitR1`. -/
theorem rgnPay_cl0_frame (ρ : Nat → Nat) {ke : KEnv} {η : TEnv} {u : Ty} (hC : ∀ k, Clo (η.wit k))
    (hS : WitSh ke η) (hc : WitC ke η) (hR : WitR1 ke η)
    (hp : rgnPay ke u = true) (hd : drf1 u = true) (ht : tb ke.length u = true) :
    Ty.coupledOK (cl ρ η.wit 0 0 u) = true ∧ Ty.affine (cl ρ η.wit 0 0 u) = false ∧
      drf1 (cl ρ η.wit 0 0 u) = true :=
  rgnPay_cl0 ρ hC hS hc (WitR1_occ hR ht) hp hd ht

/-- A callee frame's witness at a parameter position is the closure of a checked type argument. -/
theorem subE_wit_call {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hinst : instantiate cx d is ts = .ok (at_, rt)) {k : Nat} (hk : k < d.tparams.length) :
    ∃ κ σ, admitsIn cx κ σ = true ∧ σ ∈ ts ∧ (subE ρ₀ η ts.reverse).wit k = cl ρ₀ η.wit 0 0 σ := by
  obtain ⟨hl, ha⟩ := instantiate_admits hinst
  have hκ : d.tparams.reverse[k]? = some (d.tparams.reverse[k]'(by simpa using hk)) :=
    List.getElem?_eq_getElem _
  generalize d.tparams.reverse[k]'(by simpa using hk) = κ at hκ
  rw [List.getElem?_reverse hk] at hκ
  have hj : d.tparams.length - 1 - k < ts.length := by omega
  have hσ : ts[d.tparams.length - 1 - k]? = some (ts[d.tparams.length - 1 - k]'hj) :=
    List.getElem?_eq_getElem hj
  generalize ts[d.tparams.length - 1 - k]'hj = σ at hσ
  have hm : (κ, σ) ∈ d.tparams.zip ts := List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨hκ, hσ⟩)
  have e : ts.reverse[k]? = some σ := by rw [List.getElem?_reverse (by omega), hl]; exact hσ
  refine ⟨κ, σ, ha κ σ hm, List.mem_of_getElem? hσ, ?_⟩
  show (match ts.reverse[k]? with | some σ => cl ρ₀ η.wit 0 0 σ | none => η.wit (k - ts.reverse.length)) = _
  rw [e]

/-- **At a call**: the callee's witnesses are closures of `drf1` type arguments (`opOK1`'s check). -/
theorem WitR1_call {ρ₀ : Nat → Nat} {η : TEnv} {cx : Cx} {d : Decl} {is : List String} {ts : List Ty}
    {at_ rt : Ty} (hS : WitR1 cx.ke η) (hinst : instantiate cx d is ts = .ok (at_, rt))
    (hrt : ∀ σ ∈ ts, drf1 σ = true) :
    WitR1 (d.tparams.reverse.map some) (subE ρ₀ η ts.reverse) := by
  refine WitR1_iff.2 (fun k hk => ?_)
  simp only [List.length_map, List.length_reverse] at hk
  obtain ⟨κ, σ, had, hm, e⟩ := subE_wit_call (ρ₀ := ρ₀) (η := η) hinst hk
  rw [e]
  exact drf1_cl_frame ρ₀ hS (tb_of_wf σ (admitsIn_wf had)) (hrt σ hm)

/-- **At `unpackT`**: the unpacked witness is `WitOK1`, so `drf1`. -/
theorem WitR1_pushT {ke : KEnv} {η : TEnv} {κ : Kind} {s : Ty} (haf : WitOK1 κ s) (h : WitR1 ke η) :
    WitR1 (some κ :: ke) (η.consC s) := by
  refine WitR1_iff.2 (fun k hk => ?_)
  cases k with
  | zero => simpa [TEnv.consC, TEnv.insR] using haf.2.2.2.2.1
  | succ k =>
      simp only [List.length_cons] at hk
      simpa [TEnv.consC, TEnv.insR] using WitR1_iff.1 h k (by omega)

theorem noIallV_of_drf1 : ∀ t : Ty, drf1 t = true → noIallV t = true := by
  intro t
  induction t with
  | prod a b iha ihb | sum a b iha ihb =>
      intro h; simp only [drf1, noIallV, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | array _ t ih | mu t ih | tex _ t ih | iex t ih | refine t _ ih =>
      intro h; simp only [drf1, noIallV] at h ⊢; exact ih h
  | iall t _ => intro h; simp [drf1] at h
  | _ => intro _; simp [noIallV]

/-- **At `packT`**: the closure of an admitted, `drf1` witness is `WitOK1` in an `FInv` frame. -/
theorem WitOK1_pack (ρ : Nat → Nat) {η : TEnv} {cx : Cx} {κ : Kind} {σ : Ty} (hw : ∀ k, Clo (η.wit k))
    (haf : WitAF η) (hSh : WitSh cx.ke η) (hCp : WitC cx.ke η) (hN : WitN cx.ke η) (hR : WitR1 cx.ke η)
    (had : admitsIn cx κ σ = true) (hd : drf1 σ = true) : WitOK1 κ (cl ρ η.wit 0 0 σ) := by
  have ht := tb_of_wf σ (admitsIn_wf had)
  exact ⟨arrFree_cl haf.af σ 0 0 (admitsIn_arrFree had),
    fun hsh => coupledOK_cl0 ρ η.wit cx.ke hw (fun k _ hk => hSh k hk) (admitsIn_share had hsh) ht,
    fun hcp => AffineCl.affine_cl0 ρ η.wit cx.ke hw (fun k _ hk => hCp k hk) σ ((admitsIn_word had).2 hcp) ht,
    fun hno => NoOwnCl.noOwn_cl0 ρ η.wit cx.ke hw (fun k _ hk => hN k hk) σ (admitsIn_noOwn had hno) ht,
    drf1_cl_frame ρ hR ht hd, noIallV_cl haf.ni σ 0 0 (noIallV_of_drf1 σ hd),
    TermTv.mg_cl (fun k => (hw k).1) haf.mg σ 0 0 (TermTv.mg_of_wf σ (admitsIn_wf had))⟩

/-- `opOK1` checks every annotation of an operation other than `null` (the `call`/`spawn` type
arguments, the `packT` witness). -/
theorem opOK1_tys {op : Op} (h : opOK1 op = true) (hn : ∀ μ τ, op ≠ .null μ τ) :
    ∀ σ ∈ opTys op, drf1 σ = true := by
  cases op
  all_goals first
    | (simp [opOK1] at h; done)
    | (exact absurd rfl (hn _ _))
    | (intro σ hσ; simp only [opOK1, List.all_eq_true] at h; exact h σ hσ)

/-- `allOK1` checks `tail`'s type arguments. -/
theorem allOK1_tail {f : String} {is : List String} {x : At} {ts : List Ty} (h : allOK1 (.tail f is x ts) = true) :
    ∀ σ ∈ ts, drf1 σ = true := by
  simp only [allOK1, List.all_eq_true] at h; exact h

/-- The scope's check at `packT` under c1: the witness of a type existential is `drf1`. -/
def PackTOK1 (σ : Ty) : Ty → Prop
  | .tex _ _ => drf1 σ = true
  | _ => True

/-- `PackTOK1` at an existential gives `WitOK1_pack`'s `drf1` premise. -/
theorem PackTOK1.drf1 {σ : Ty} {κ : Kind} {t : Ty} (h : PackTOK1 σ (.tex κ t)) : drf1 σ = true := h

/-- `opOK1` at `packT` gives `PackTOK1` and the witness's `noIallV` (the `packT` arm of `PureOp`
at the switch). -/
theorem packTOK1_of_opOK1 {a : At} {σ τ : Ty} (h : opOK1 (.packT a σ τ) = true) :
    PackTOK1 σ τ ∧ noIallV σ = true := by
  have hd : drf1 σ = true := opOK1_tys h (fun _ _ hn => Op.noConfusion hn) σ (by simp [opTys])
  refine ⟨?_, noIallV_of_drf1 σ hd⟩
  unfold PackTOK1
  split
  · exact hd
  · trivial

end TermC1

#print axioms TermC1.ask_true_iff
#print axioms TermC1.WitR1_iff
#print axioms TermC1.WitR1_nil
#print axioms TermC1.WitR1_wit
#print axioms TermC1.mentions_lt
#print axioms TermC1.WitR1_occ
#print axioms TermC1.drf1_cl_frame
#print axioms TermC1.rgnPay_cl0_frame
#print axioms TermC1.subE_wit_call
#print axioms TermC1.WitR1_call
#print axioms TermC1.WitR1_pushT
#print axioms TermC1.noIallV_of_drf1
#print axioms TermC1.WitOK1_pack
#print axioms TermC1.opOK1_tys
#print axioms TermC1.allOK1_tail
#print axioms TermC1.PackTOK1.drf1
#print axioms TermC1.packTOK1_of_opOK1
