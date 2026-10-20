import WeakCore.TermTyped
import WeakCore.TermK2aRet
import WeakCore.TermK2aLd

/-!
# TermBufPW: the slot an exchange/initialisation writes has the operand's counted words (K1c)

`xchgAt_pw`, `xchgAtF_pw`, `bufInit_pw`: the cell slot type `U` that a buffer write targets
(`TermTyped.xchgAt_ua` etc.) counts the same words, with the same word count, as the operand's runtime
type `rt`.
-/

namespace TermBufPW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermTyped TermPtrRts
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The operand chain: a value of runtime type `rt` laid out at `tv`, `tv` subsumed by `u`,
counts as the closed `u`. -/
theorem pw_chain {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ : Cx} {env : Env} {rt tv u : Ty} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hl : Lay σs tv rt ws) (hsub : SubS c₁ tv u)
    (ho : cx.opaqueOK u = true) (htb : tb cx.ke.length u = true) :
    (∀ L, pubWords (cl ρ η.wit 0 0 u) L = pubWords rt L) ∧ wc rt = wc (cl ρ η.wit 0 0 u) := by
  have hsg := sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  refine ⟨fun L => ?_, ?_⟩
  · rw [pubWords_elyt hl.2.2.2.2]
    exact (TermK2aLd.pubWords_sig hsg L).symm.trans ((TermK2a.pubWords_subS hsub σs 0 0).2.1 L).symm
  · have e1 : wc rt = wc (close σs tv) := by simp only [wc, accs_of_elyt hl.2.2.2.2]
    rw [e1]
    exact (wc_sub hsub σs 0 0).trans (wc_of_sig hsg)

theorem xchgAt_pw {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx cP : Cx} {env : Env} {y x : String} {bb i : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {rt : Ty}
    (hop : OpT p cx y (.xchgAt bb i (.var x)) cP)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchgAt bb i (.var x)) pw b rel us ws) (hlk : lookupE env x = some (rt, ws)) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
      (∀ L, pubWords U L = pubWords rt L) ∧ wc rt = wc U ∧ ShapeC rt ws := by
  obtain ⟨-, rt0, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk huP hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) huP).1)
      obtain ⟨rtP, w, ad, c, μr, ur, usP, rti, wi, heaP, hwv, heiP, hnjP, hbeP, husP, hsto, hat, -, -, -, -,
        htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at heaP
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at heaP
      obtain ⟨rfl, rfl⟩ := heaP
      rw [hei] at heiP
      simp only [Option.some.injEq, Prod.mk.injEq] at heiP
      obtain ⟨rfl, rfl⟩ := heiP
      rw [hbe] at hbeP
      simp only [Option.some.injEq, Prod.mk.injEq] at hbeP
      obtain ⟨rfl, rfl⟩ := hbeP
      rw [hnj] at hnjP
      simp only [Option.some.injEq] at hnjP
      subst hnjP
      rw [hus] at husP
      simp only [Option.some.injEq] at husP
      subst husP
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨-, rtv, wsv, hev, -, hl⟩ := use_FInv huP hi
      simp only [evalAt, hlk, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      obtain ⟨hpw, hwc⟩ := pw_chain hi hl hsub ho htb
      exact ⟨_, _, hsto, hat, (buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus, hpw, hwc, hl.1⟩

theorem xchgAtF_pw {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx cP : Cx} {env : Env} {y x : String} {bb i : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {rt : Ty}
    (hop : OpT p cx y (.xchgAtF bb i q (.var x)) cP)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchgAtF bb i q (.var x)) pw b rel us ws) (hlk : lookupE env x = some (rt, ws)) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
      (∀ L, pubWords U L = pubWords rt L) ∧ wc rt = wc U ∧ ShapeC rt ws := by
  obtain ⟨-, rt0, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk huP hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) huP).1)
      obtain ⟨rtP, w, ad, cc, μr, ur, usP, rti, wi, heaP, hwv, heiP, hnjP, hbeP, husP, hsto, hat, -, -,
        hsku, hsig, htbu, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at heaP
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at heaP
      obtain ⟨rfl, rfl⟩ := heaP
      rw [hei] at heiP
      simp only [Option.some.injEq, Prod.mk.injEq] at heiP
      obtain ⟨rfl, rfl⟩ := heiP
      rw [hbe] at hbeP
      simp only [Option.some.injEq, Prod.mk.injEq] at hbeP
      obtain ⟨rfl, rfl⟩ := hbeP
      rw [hnj] at hnjP
      simp only [Option.some.injEq] at hnjP
      subst hnjP
      rw [hus0] at husP
      simp only [Option.some.injEq] at husP
      subst husP
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      have htbc := TermStep.tb_compTy q _ _ hct htbu
      obtain ⟨-, rtv, wsv, hev, -, hl⟩ := use_FInv huP hi
      simp only [evalAt, hlk, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      obtain ⟨hpw, hwc⟩ := pw_chain hi hl hsub ho htbc
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT htbc hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), hpw, hwc, hl.1⟩
      simpa [offs, Nat.add_assoc] using AtOff_trans hat hato

theorem bufInit_pw {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx cP : Cx} {env : Env} {y x : String} {bb i : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {rt : Ty}
    (hop : OpT p cx y (.bufInit bb i (.var x)) cP)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.bufInit bb i (.var x)) pw b rel us ws) (hlk : lookupE env x = some (rt, ws)) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
      (∀ L, pubWords U L = pubWords rt L) ∧ wc rt = wc U ∧ ShapeC rt ws := by
  obtain ⟨-, rt0, t1, t2, iws, μ0, u0, j0, a0, μP, nP, eP, ψ, hea, hei, -, hbe, hnj, hb, hus, -, rfl⟩ := hu
  cases hop with
  | bufInit huP hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, jj, c₁, tv, c₂, huP, hbuf, hint, heq, hlt, hu2, hsub⟩ :
          ∃ t u n k jj c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            IntIdx c₁ i jj ∧ EqI c₁ jj k ∧ LtI c₁ k n ∧ c₁.use (.var x) = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, _, huP, hbuf, hint, heq, hlt, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK huP htv
      obtain ⟨hi1, rb, wsb, heaP, hvb, hlb⟩ := use_FInv huP hi
      have hJK : ev ρ jj = ev ρ k := heq ρ hi1.1
      have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wsi, heiP, hvi, -⟩ := peek_VR hi1.2.1 hpi
      obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
      rw [hea] at heaP
      simp only [Option.some.injEq, Prod.mk.injEq] at heaP
      obtain ⟨rfl, rfl⟩ := heaP
      rw [hei] at heiP
      simp only [Option.some.injEq, Prod.mk.injEq] at heiP
      obtain ⟨rfl, rfl⟩ := heiP
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [VR] at hvb
      obtain ⟨hv, -⟩ := hvb
      rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, -, -⟩
      · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
        simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
        omega
      obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hwv : pw.val = .loc ad 0 := by simpa using hws
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      simp only [cl, clI_zero] at hat0
      have htb1 : tb c₁.ke.length u = true := by
        have h := htu.2.1
        rw [← htu.2.2] at h
        simp [tb] at h
        exact h
      have ho : c₁.opaqueOK u = true :=
        sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu2).1)
      have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
        (accs_WitL hi1.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (buf_lyt hlb.2.2.2.2 hbe).2).symm.trans hus)
      have hel := AtOff.elem (n := ev ρ n) hacc (show ev ρ jj < ev ρ n by omega)
        (AtOff.here (Or.inl (by simp [hacc])))
      obtain ⟨-, rtv, wsv, hev, -, hl⟩ := use_FInv hu2 hi1
      simp only [evalAt, hlk, Option.some.injEq, Prod.mk.injEq] at hev
      obtain ⟨rfl, rfl⟩ := hev
      obtain ⟨hpw, hwc⟩ := pw_chain hi1 hl hsub ho htb1
      refine ⟨_, _, hsto, ?_, hacc, hpw, hwc, hl.1⟩
      simpa [offs] using AtOff_trans hat0 hel

end TermBufPW

#print axioms TermBufPW.pw_chain
#print axioms TermBufPW.xchgAt_pw
#print axioms TermBufPW.xchgAtF_pw
#print axioms TermBufPW.bufInit_pw
