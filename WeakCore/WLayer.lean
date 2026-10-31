import WeakCore.ShadowWinChain
import WeakCore.TermTyped
import WeakCore.TermPlantF
import WeakCore.TermB5
import WeakCore.TermAnch
import WeakCore.TermPredStoreFree
import WeakCore.TermWrSiteA
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
set_option autoImplicit false
set_option maxErrors 100000
namespace TermPlantF.Flat
def anchorW_TermPlantF : Unit := ()
end TermPlantF.Flat
namespace TermB5.Flat
def anchorW_TermB5 : Unit := ()
end TermB5.Flat
namespace TermAnch.Flat
def anchorW_TermAnch : Unit := ()
end TermAnch.Flat
namespace TermPredStoreFree.Flat
def anchorW_TermPredStoreFree : Unit := ()
end TermPredStoreFree.Flat
namespace TermPredStoreFree.PVc.Flat
def anchorW_TermPredStoreFree_PVc : Unit := ()
end TermPredStoreFree.PVc.Flat
namespace TermWrSiteA.Flat
def anchorW_TermWrSiteA : Unit := ()
end TermWrSiteA.Flat
-- PORTB TermTyped.lean:1273 buf_accs
namespace TermTyped.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem buf_accsB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {b : At} {t u rt ur : Ty} {μ μr : Mode} {n k : Idx} {ws : List Word}
    (hi : FInvB glb gnum gi ρ η σs K cx env) (hE : EnvOKB p η)
    (hp : cx.peek b = .ok t) (hbuf : bufOf t = some (μ, n, u, k)) (ho : cx.opaqueOK u = true)
    (htb : tb cx.ke.length u = true)
    (hea : evalAt env b = some (rt, ws)) (hbe : bufElem rt = some (μr, ur)) :
    accs ur = accs (cl ρ η.wit 0 0 u) :=
  (accs_of_elyt (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2).trans
    (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb hi.2.2.2.2.1))
end
end TermTyped.Flat

-- PORTB TermPlantF.lean:1021 ptr_targetI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem ptr_targetIB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ IniAt η.ini c b U := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VRB (bkG := False) hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VRF, VRb2] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, -, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty, fun N e hc => ?_⟩
    · rw [hoff]; exact Fd_AtOff Fd.refl hacc
    · rw [hc] at hacc; simp [accs] at hacc
  · simp only [VRF, VRb2] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, -, hini⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd, IniAt_mono (modeIni_le μ η) hini⟩
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1048 cell_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem cell_uaIB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInvB glb gnum gi ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : UnitsAtI η b us := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetIB hi.2.1 hp (cell_cases hc) hea hb
  have hacc : accs U = some us := by
    rw [Fd_accs hFd, ← pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
      hus]
  exact ⟨_, _, hsto, hat, hacc, hini⟩
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1061 store_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem store_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.store rl a v tok) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_uaIB hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_uaIB hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      rcases ht with rfl | rfl
      · exact cell_uaIB hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
      · exact cell_uaIB hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1083 xchg_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem xchg_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_uaIB hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1098 xchgAt_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem xchgAt_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, hini, -, -,
        htb, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, _, hsto, hat, (buf_accsB hi hE hp hbuf ho htb hea hbe).symm.trans hus,
        IniAt_mono (modeIni_le _ η) hini⟩
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1131 xchgAtF_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem xchgAtF_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -,
        hsku, hsig, htbu, hiniV⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), ?_⟩
      · simpa [offs, Nat.add_assoc] using AtOff_trans hat hato
      · have h := IniAt_mono (modeIni_le _ η) (hiniV _ _ hato)
        simpa [offs, Nat.add_assoc] using h
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1174 stl_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem stl_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_numB hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, -, hini, hsku, -⟩ :=
        slot_viewNB (bkG := False) (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], IniAt_mono (modeIni_le _ η) hini⟩
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1223 stlw_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem stlw_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, -, hini,
        hsku, -, -, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], IniAt_mono (modeIni_le _ η) hini⟩
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1260 tgt_swI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem tgt_swIB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some [.one]) : UnitsAtI η b [.one] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetIB hvars hp ht hea hb
  exact ⟨c, U, hsto, hat, (Fd_accs hFd).trans hacc, hini⟩
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1285 fetch_swI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem fetch_swIB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      exact tgt_swIB hi.2.1 hp ht hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwfB hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_swIB hi.2.1 hp ht hea hb (by simp [cl, accs, hok.1.1.1.1])
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1310 cas_swI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem cas_swIB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swIB hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swIB hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        exact tgt_swIB hi.2.1 hp ht hea hb
          (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwfB hp ht hμ hi hE htv hm) hep])
      · rw [hw] at hnw; cases hnw
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1339 unitsOp_uaI
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem unitsOp_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s op pw b rel us ws) :
    UnitsAtI η b us ∨ ∃ bb i v, op = .bufInit bb i v := by
  cases op
  case store => exact .inl (store_uaIB hop hsc hi hE htv hu)
  case xchg => exact .inl (xchg_uaIB hop hsc hi hE htv hu)
  case xchgAt => exact .inl (xchgAt_uaIB hop hi hE htv hu)
  case xchgAtF => exact .inl (xchgAtF_uaIB hop hi hE htv hu)
  case bufInit bb i v => exact .inr ⟨bb, i, v, rfl⟩
  case stl => exact .inl (stl_uaIB hop hi htv hu)
  case stlw => exact .inl (stlw_uaIB hop hi htv hu)
  all_goals simp [TermFul.UnitsOp] at hu
end
end TermPlantF.Flat

-- PORTB TermPlantF.lean:1358 SWIni
namespace TermPlantF.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Classical in
open Classical in
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}
theorem SWIniB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {loc : Address} {val : WeakMem.Val}
    (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hsw : TermFul.SW g mem pairs th loc val) :
    (∃ c, η.sto loc.label = some c ∧ InitR η c loc.label loc.offset) ∨
      ∃ x bb i v e, th.term = .let_ x (.bufInit bb i v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hT' := hT
    rw [hterm] at hT' hsc
    cases hT' with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, rfl, -⟩ |
            ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · rcases unitsOp_uaIB hop hsc hi hE htv hu with hU | ⟨bb, i, v, rfl⟩
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initR hU hj
            exact .inl ⟨c, hc, by simpa [offs] using hI⟩
          · exact .inr ⟨x, bb, i, v, e, hterm⟩
        · obtain ⟨c, hc, hI⟩ := unitsAtI_initR (fetch_swIB hop hsc hi hE htv hm hea hb) (.here _)
          exact .inl ⟨c, hc, by simpa using hI⟩
  · rw [hterm] at hT hsc
    obtain ⟨c, hc, hI⟩ := unitsAtI_initR (cas_swIB hT hsc hi hE htv hm hea hb) (.here _)
    exact .inl ⟨c, hc, by simpa using hI⟩
end
end TermPlantF.Flat

-- PORTB TermB5.lean:309 ptr_targetI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem ptr_targetIB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧ IniAt η.ini c b U := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VRB (bkG := False) hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VRF, VRb2] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, -, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty, IniAt_of_ne fun N e' hc => hacc (by rw [hc]; simp [accs])⟩
    rw [hoff]; exact Fd_AtOff Fd.refl hacc
  · simp only [VRF, VRb2] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, -, hini⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd, IniAt_mono (fun l => modeIni_le_ini _ _ _ l) hini⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:336 tgt_swI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem tgt_swIB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some [.one]) : UnitsAtI η b [.one] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetIB hvars hp ht hea hb
  exact ⟨c, U, hsto, hat, (Fd_accs hFd).trans hacc, .inr hini⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:344 cell_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem cell_uaIB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInvB glb gnum gi ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : UnitsAtI η b us := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := ptr_targetIB hi.2.1 hp (cell_cases hc) hea hb
  have hacc : accs U = some us := by
    rw [Fd_accs hFd, ← pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
      hus]
  exact ⟨_, _, hsto, hat, hacc, .inr hini⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:357 store_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem store_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.store rl a v tok) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_uaIB hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_uaIB hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      rcases ht with rfl | rfl
      · exact cell_uaIB hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
      · exact cell_uaIB hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
end
end TermB5.Flat

-- PORTB TermB5.lean:379 xchg_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem xchg_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_uaIB hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
end
end TermB5.Flat

-- PORTB TermB5.lean:394 xchgAt_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem xchgAt_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -, -, -,
        htb, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, _, hsto, hat, (buf_accsB hi hE hp hbuf ho htb hea hbe).symm.trans hus, .inl hmo⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:426 xchgAtF_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem xchgAtF_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -,
        hsku, hsig, htbu, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), .inl hmo⟩
      simpa [offs, Nat.add_assoc] using AtOff_trans hat hato
end
end TermB5.Flat

-- PORTB TermB5.lean:470 bufInit_inv
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem bufInit_invB {bkG : Prop} {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws) :
    ∃ rt rti wi ad c N U jv, evalAt env bb = some (rt, [pw]) ∧ pw.val = .loc ad 0 ∧
      evalAt env i = some (rti, [wi]) ∧ numOf [wi] = some jv ∧ b = offs ad (jv * nWords us) ∧
      η.sto ad.label = some c ∧ (ModeOKF bkG) η.tid η.pfr η.seen Mode.own ad.label c [pw] ∧
      IniAt (modeIni Mode.own η.ini η.rini) c ad (.array (.lit N) U) ∧ AtOff c.ty ad.offset (.array (.lit N) U) ∧
      jv < N ∧ accs U = some us := by
  obtain ⟨-, rt, t1, t2, iws, μ0, u0, j0, a0, μ', n', e', ψ, hea, hei, -, hbe, hnj, hb, hus, -, rfl⟩ := hu
  cases hop with
  | bufInit hu' hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, jj, c₁, tv, c₂, hu', hbuf, hint, heq, hlt, hu2, hsub⟩ :
          ∃ t u n k jj c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            IntIdx c₁ i jj ∧ EqI c₁ jj k ∧ LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, _, hu', hbuf, hint, heq, hlt, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK hu' htv
      obtain ⟨hi1, rb, wsb, hea', hvb, hlb⟩ := use_FInvB (bkG := bkG) hu' hi
      have hJK : ev ρ jj = ev ρ k := heq ρ hi1.1
      have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wsi, hei', hvi, -⟩ := peek_VRB (bkG := bkG) hi1.2.1 hpi
      obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := bkG) hti hvi)
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [VRF, VRb2] at hvb
      obtain ⟨hv, -⟩ := hvb
      rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmo, hini0⟩
      · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
        simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
        omega
      obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hwv : pw.val = .loc ad 0 := by simpa using hws
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      simp only [cl, clI_zero] at hat0 hini0
      have htb1 : tb c₁.ke.length u = true := by
        have h := htu.2.1
        rw [← htu.2.2] at h
        simp [tb] at h
        exact h
      have ho : c₁.opaqueOK u = true :=
        sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu2).1)
      have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
        (accs_WitL hi1.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (buf_lyt hlb.2.2.2.2 hbe).2).symm.trans hus)
      exact ⟨_, _, wi, a0, c, _, _, _, hea, hwv, hei, hnj, rfl, hsto, hmo, hini0, hat0, by omega, hacc⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:532 bufInit_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem bufInit_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, -, -, ad, c, N, U, jv, -, -, -, -, rfl, hsto, hmo, -, hat0, hjv, hacc⟩ :=
    bufInit_invB (bkG := False) hop hi hE htv hu
  have hel := AtOff.elem (n := N) hacc hjv (AtOff.here (Or.inl (by simp [hacc])))
  refine ⟨_, _, hsto, ?_, hacc, .inl hmo⟩
  simpa [offs] using AtOff_trans hat0 hel
end
end TermB5.Flat

-- PORTB TermB5.lean:544 stl_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem stl_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_numB hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, hmo, -, hsku, -⟩ :=
        slot_viewNB (bkG := False) (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat
      exact ⟨_, _, hsto, hat, by simp [cl, accs], .inl hmo⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:593 stlw_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem stlw_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAtI η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, hmo, -,
        hsku, -, -, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat
      exact ⟨_, _, hsto, hat, by simp [cl, accs], .inl hmo⟩
end
end TermB5.Flat

-- PORTB TermB5.lean:630 fetch_swI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem fetch_swIB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      exact tgt_swIB hi.2.1 hp ht hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwfB hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_swIB hi.2.1 hp ht hea hb (by simp [cl, accs, hok.1.1.1.1])
end
end TermB5.Flat

-- PORTB TermB5.lean:655 cas_swI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem cas_swIB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : UnitsAtI η loc [.one] := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
      · exact tgt_swIB hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swIB hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_swIB hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        exact tgt_swIB hi.2.1 hp ht hea hb
          (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwfB hp ht hμ hi hE htv hm) hep])
      · rw [hw] at hnw; cases hnw
end
end TermB5.Flat

-- PORTB TermB5.lean:718 unitsOp_uaI
namespace TermB5.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (stepRmwPair_shape loadUnits_keep)
open TermTyped
theorem unitsOp_uaIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s op pw b rel us ws) : UnitsAtI η b us := by
  cases op
  case store => exact store_uaIB hop hsc hi hE htv hu
  case xchg => exact xchg_uaIB hop hsc hi hE htv hu
  case xchgAt => exact xchgAt_uaIB hop hi hE htv hu
  case xchgAtF => exact xchgAtF_uaIB hop hi hE htv hu
  case bufInit => exact bufInit_uaIB hop hi hE htv hu
  case stl => exact stl_uaIB hop hi htv hu
  case stlw => exact stlw_uaIB hop hi htv hu
  all_goals simp [TermFul.UnitsOp] at hu
end
end TermB5.Flat

-- PORTB TermAnch.lean:35 pair_uaIP
namespace TermAnch.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pair_uaIPB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) : TermPlantF.UnitsAtI η b [.two] := by
  obtain ⟨c, U, hsto, hat, hFd, hini⟩ := TermPlantF.Flat.ptr_targetIB hvars hp ht hea hb
  refine ⟨c, U, hsto, hat, (Fd_accs hFd).trans ?_, hini⟩
  rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [cl, accs]
end
end TermAnch.Flat

-- PORTB TermAnch.lean:44 stp_uaIP
namespace TermAnch.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stp_uaIPB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty} {pw : Word}
    {b : Address} (hop : OpT p cx x (.stp rel a v0 v1 tk) c') (hsc : OpScope cx (.stp rel a v0 v1 tk))
    (hi : FInvB glb gnum gi ρ η σs K cx env) (hea : evalAt env a = some (t, [pw])) (hb : addrOf pw = some b) :
    TermPlantF.UnitsAtI η b [.two] := by
  have hp : ∃ t, cx.peek a = .ok t := by cases hop <;> exact ⟨_, ‹_›⟩
  obtain ⟨t', hp⟩ := hp
  obtain ⟨μ, r, P, ht, -⟩ := hsc t' hp
  exact pair_uaIPB hi.2.1 hp ht (.inl ⟨r, P, rfl⟩) hea hb
end
end TermAnch.Flat

-- PORTB TermAnch.lean:54 casp_uaIP
namespace TermAnch.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem casp_uaIPB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e0 e1 v0 v1 : At} {tn : String} {ok fail : Expr}
    {tw : Ty} {pw : Word} {A : Address}
    (hT : Typed p cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hsc : StepScope cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hi : FInvB glb gnum gi ρ η σs K cx env) (hea : evalAt env w = some (tw, [pw])) (hb : addrOf pw = some A) :
    TermPlantF.UnitsAtI η A [.two] := by
  have hp : ∃ t, cx.peek w = .ok t := by cases hT <;> exact ⟨_, ‹_›⟩
  obtain ⟨t, hp⟩ := hp
  obtain ⟨μ, u, ht, -, hu⟩ := hsc t hp
  exact pair_uaIPB hi.2.1 hp ht hu hea hb
end
end TermAnch.Flat

-- PORTB TermAnch.lean:84 bufInit_site
namespace TermAnch.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem bufInit_siteB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb ib v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {j : Nat}
    (hop : OpT p cx x (.bufInit bb ib v) c') (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.bufInit bb ib v) pw b rel us ws) (hj : j < nWords us) :
    ∃ rt w ad rti wi n c, evalAt env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧
      evalAt env ib = some (rti, [wi]) ∧ numOf [wi] = some n ∧ ad.label = (offs b j).label ∧
      η.sto (offs b j).label = some c ∧
      ∀ N el us', c.ty = .array (.lit N) el → accs el = some us' → (offs b j).offset < (n + 1) * nWords us' := by
  obtain ⟨rt, rti, wi, ad, c, N, U, jv, hea, hw, hei, hn, hb, hsto, -, hini, hat, -, hus⟩ :=
    TermB5.Flat.bufInit_invB (bkG := False) hop hi hE htv hu
  subst hb
  refine ⟨rt, pw, ad, rti, wi, jv, c, hea, hw, hei, hn, rfl, hsto, fun N' el us' hT he => ?_⟩
  have := bufInit_slot (jv := jv) hini hat hus hj N' el us' hT he
  simpa [offs, Nat.add_assoc] using this
end
end TermAnch.Flat

-- PORTB TermAnch.lean:108 wrSite_ok
namespace TermAnch.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrSite_okB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hr : r ∈ tstep g mem pairs th) : WrSite g (CE η) mem pairs th r := by
  intro t m ht hmt
  by_cases hlt : t < mem.size
  · have hm0 : mem[t]? = some mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow hr).1 t _ hm0
    rw [hmt] at e2
    simp only [Option.some.injEq] at e2
    have hm1 : mem[t]? = some m := by rw [hm0, e2]
    by_cases htp : t ∈ th.promises
    · obtain ⟨m', hm', hsw, -, -⟩ :=
        (TermFul.tstep_fulfil (MemInv_promLtB hm) (MemInv_nopairB hm) hr).2 t htp ht
      have hm'' : mem[t]? = some m' := hm'
      rw [hm1] at hm''; cases hm''
      rcases TermPlantF.Flat.SWIniB hE hT htv hi hm (TermTyped.scopeD_SW hsc hsw) hsw with h | ⟨x, bb, ib, v, e, hterm⟩
      · exact .inr (.inr (.inl h))
      · refine .inr (.inr (.inr ⟨x, bb, ib, v, e, hterm, ?_⟩))
        rcases hsw with ⟨x', op, e', hterm', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm', -⟩
        · rw [hterm] at hterm'
          simp only [Expr.let_.injEq] at hterm'
          obtain ⟨rfl, rfl, rfl⟩ := hterm'
          rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop', -⟩
          · have hT' := hT
            rw [hterm] at hT'
            cases hT' with
            | let_ hop _ => rw [hl]; exact bufInit_siteB (η := η) hop hi hE htv hu (TermFul.OneAt_lt hj)
          · cases hop'
        · rw [hterm] at hterm'; cases hterm'
    · exact .inl ⟨htp, hm1⟩
  · rcases TermB5.tstep_newR (MemInv_promLtB hm) hr t m (by omega) hmt with hf | hn
    · exact .inr (.inl hf)
    rcases hn with ⟨x, op, e, hterm, b, us, j, hon, hl, hrole⟩ |
        ⟨acq, rel, w, e, v, tn, ok, fail, tw, pw, hterm, hea, hb⟩ |
        ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩
    · have hjl := TermB5.roleR_lt hrole
      have hss : StepScope cx th.term := hsc.elim id fun h => (newR_cap h.2 hterm hon).elim
      rw [hterm] at hT hss
      cases hT with
      | let_ hop _ =>
          rcases hon with ⟨pw, rel, ws, hu⟩ | ⟨rel, a, v0, v1, tk, t', pw, rfl, hea, hb, rfl⟩ |
              ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb, rfl⟩
          · rcases TermPlantF.Flat.unitsOp_uaIB hop hss hi hE htv hu with hU | ⟨bb, ib, v, rfl⟩
            · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hU hjl
              exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
            · refine .inr (.inr (.inr ⟨x, bb, ib, v, e, hterm, ?_⟩))
              rw [hl]; exact bufInit_siteB (η := η) hop hi hE htv hu hjl
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (stp_uaIPB hop hss hi hea hb) hjl
            exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
          · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (TermPlantF.Flat.fetch_swIB hop hss hi hE htv hm hea hb) hjl
            exact .inr (.inr (.inl ⟨c, by rw [hl]; exact hc, by rw [hl]; exact hI⟩))
    · have hss : StepScope cx th.term := hsc.elim id fun h => by
        obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := h.2 <;> rw [he] at hterm <;> cases hterm
      rw [hterm] at hT hss
      obtain ⟨c, hc, hI⟩ := unitsAtI_initRn (TermPlantF.Flat.cas_swIB hT hss hi hE htv hm hea hb)
        (show 0 < nWords [Acc.one] by decide)
      have e0 : m.loc = offs m.loc 0 := (TermStepper.offs_zero _).symm
      exact .inr (.inr (.inl ⟨c, hc, by rw [e0]; exact hI⟩))
    · have hss : StepScope cx th.term := hsc.elim id fun h => by
        obtain ⟨x', e', ⟨a, b', he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := h.2 <;> rw [he] at hterm <;> cases hterm
      rw [hterm] at hT hss
      have hua := casp_uaIPB hT hss hi hea hb
      rcases hl with ⟨hl, -⟩ | ⟨hl, -⟩
      · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hua (show 0 < nWords [Acc.two] by decide)
        have e0 : m.loc = offs A 0 := by rw [hl, TermStepper.offs_zero]
        exact .inr (.inr (.inl ⟨c, by rw [e0]; exact hc, by rw [e0]; exact hI⟩))
      · obtain ⟨c, hc, hI⟩ := unitsAtI_initRn hua (show 1 < nWords [Acc.two] by decide)
        have e0 : m.loc = offs A 1 := hl
        exact .inr (.inr (.inl ⟨c, by rw [e0]; exact hc, by rw [e0]; exact hI⟩))
end
end TermAnch.Flat

-- PORTB TermPredStoreFree.lean:141 ptr_targetM
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ptr_targetMB {bkG : Prop} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) ∧
      ModeOKb η.tid η.pfr η.seen (bkG ∨ IniAt η.rc c b U) μ b.label c [pw] ∧ IniAt (modeIni μ η.ini η.rini) c b U := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VRB (bkG := bkG) hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VRF, VRb2] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, hmo, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty, ModeOKb_flag (fun h => h.imp id (fun hn N e hc => absurd hc (hn N e))) hmo, fun N e hc => ?_⟩
    · rw [hoff]; exact Fd_AtOff Fd.refl hacc
    · rw [hc] at hacc; simp [accs] at hacc
  · simp only [VRF, VRb2] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, hmo, hini⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd, hmo, hini⟩
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:169 xchgAt_uaR
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem xchgAt_uaRB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, hini, -, -,
        htb, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨_, _, hsto, hat, (buf_accsB hi hE hp hbuf ho htb hea hbe).symm.trans hus,
        hini⟩
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:202 xchgAtF_uaR
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem xchgAtF_uaRB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -,
        hsku, hsig, htbu, hiniV⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      refine ⟨_, _, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
        (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
        ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
          hco0)).symm.trans hus), ?_⟩
      · simpa [offs, Nat.add_assoc] using AtOff_trans hat hato
      · have h := hiniV _ _ hato
        simpa [offs, Nat.add_assoc] using h
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:245 stl_uaR
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem stl_uaRB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_numB hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, -, hini, hsku, -⟩ :=
        slot_viewNB (bkG := False) (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], hini⟩
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:294 stlw_uaR
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem stlw_uaRB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAtRc η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, -, hini,
        hsku, -, -, -⟩ := slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨_, _, hsto, hat, by simp [cl, accs], hini⟩
end
end TermPredStoreFree.Flat

-- TI over ModeOKb with the exemption flag IniAt rc (the ♭ store/xchg/fetch/cas target).
namespace TermPredStoreFree.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermSound.Flat
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def TIB (η : TEnv) (b : Address) (us : List Acc) (pw : Word) : Prop :=
  ∃ c U μ, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us ∧
    ModeOKb η.tid η.pfr η.seen (IniAt η.rc c b U) μ b.label c [pw] ∧ IniAt (modeIni μ η.ini η.rini) c b U ∧
      (μ = .own ∨ μ = .pub)
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:351 tgt_TI
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_TIB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} {us : List Acc} (hvars : VarsOKB ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u) (hμ : μ = .own ∨ μ = .pub)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some us) : TIB η b us pw := by
  obtain ⟨c, U, hsto, hat, hFd, hmo, hini⟩ := ptr_targetMB (bkG := False) hvars hp ht hea hb
  exact ⟨c, U, μ, hsto, hat, (Fd_accs hFd).trans hacc, ModeOKb_flag (fun h => h.resolve_left id) hmo, hini, hμ⟩
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:359 cell_TI
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem cell_TIB {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInvB glb gnum gi ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hμ : μ = .own ∨ μ = .pub)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : TIB η b us pw :=
  tgt_TIB hi.2.1 hp (cell_cases hc) hμ hea hb (by
    rw [← pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr, hus])
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:370 store_TI
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem store_TIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.store rl a v tok) pw b rel us ws) : TIB η b us pw := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_TIB hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1))
        (mode_of_cell hc (hsc _ hp)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_TIB hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1))
        (mode_of_cell hc (hsc _ hp)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, hc⟩ := TermSeenHid.cellOf_of_wordOf hw
      exact cell_TIB hi hE htv hp hc (by simp [Cx.opaqueOK, Ty.guardT]) (mode_of_cell hc (hsc _ hp))
        hea hcr hb hus
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:393 xchg_TI
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem xchg_TIB {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hu : TermFul.UnitsOp g env s (.xchg a v) pw b rel us ws) : TIB η b us pw := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_TIB hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1))
            (mode_of_cell hc (hsc _ hp)) hea hcr hb hus
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:409 fetch_TI
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem fetch_TIB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : TIB η loc [.one] pw := by
  cases hop with
  | fetchCell hp _ hc =>
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_TIB hi.2.1 hp (cell_cases hc) (mode_ok (cell_cases hc) ht' hμ') hea hb
          (by simp [cl, accs])
      · exact tgt_TIB hi.2.1 hp (cell_cases hc) (mode_ok (cell_cases hc) ht' hμ') hea hb
          (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ : μ = .own ∨ μ = .pub := mode_ok ht ht' hμ'
      exact tgt_TIB hi.2.1 hp ht hμ hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwfB hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ : μ = .own ∨ μ = .pub := mode_ok ht ht' hμ'
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_TIB hi.2.1 hp ht hμ hea hb (by simp [cl, accs, hok.1.1.1.1])
end
end TermPredStoreFree.Flat

-- PORTB TermPredStoreFree.lean:446 cas_TI
namespace TermPredStoreFree.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermCert TermMain TermTyped TermPredHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem cas_TIB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInvB g.lbase g.n g.i ρ η th.σs K cx th.env) (hE : EnvOKB p η) (htv : TvOK cx)
    (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : TIB η loc [.one] pw := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_TIB hi.2.1 hp (cell_cases hc) (cas_mode hsc hp (cell_cases hc)) hea hb (accs_cl_one hraw)
      · exact tgt_TIB hi.2.1 hp (cell_cases hc) (cas_mode hsc hp (cell_cases hc)) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_TIB hi.2.1 hp ht (cas_mode hsc hp ht) hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_TIB hi.2.1 hp ht (cas_mode hsc hp ht) hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      have hμ := cas_mode hsc hp ht
      exact tgt_TIB hi.2.1 hp ht hμ hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwfB hp ht hμ hi hE htv hm) hep])
end
end TermPredStoreFree.Flat

-- PORTB TermWrSiteA.lean:32 pub_x
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem pub_xB {k : Promises.Knobs} {η : TEnv} {l : AllocLabel} {c : Cell} {pw : Word} {o t : Nat} {bk : Prop}
    (hsto : η.sto l = some c) (hmo : ModeOKb η.tid η.pfr η.seen bk .pub l c [pw]) (hvr : pw.view ≤ pw.rts)
    (hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep k pw → False) (hex : bk → c.owner = some η.tid → FulX η l o t) :
    FulX η l o t := by
  by_cases hs : η.seen l
  · exact ⟨c, hsto, .inr (.inr hs)⟩
  obtain ⟨f, hf, h⟩ := id hmo
  rcases h with h | h | ⟨ho, hb⟩
  · exact absurd h hs
  · have hd : f ≤ TermStoreNI.dep k pw :=
      TermPredStoreFree.PVc.dep_of_modeOK (i := η.tid) (S := η.seen) (c := c) ⟨f, hf, .inr h⟩ hf hs hvr
    refine ⟨c, hsto, .inr (.inl fun f' hf' => ?_)⟩
    rw [hf] at hf'; cases hf'
    exact Nat.lt_of_not_le fun hle => hk f hle hd
  · exact hex hb ho
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:47 ful_x
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ful_xB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} {t : Nat} {m : Msg} (hE : EnvOKB p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hvr : TermSeenHid.EnvVR th) (hr : r ∈ tstep g mem pairs th)
    (htp : t ∈ th.promises) (htn : t ∉ r.2.2.promises) (hsw : TermFul.SW g mem pairs th m.loc m.val) :
    FulX η m.loc.label m.loc.offset t ∨ ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, hee, hev, hb, -⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
      rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hloc, -⟩ |
          ⟨o, acq, rel, a', v, ty1, ty2, pw, nw, tr, mr, rfl, hea, hev, hb, -⟩
      · have hjl := TermFul.OneAt_lt hj
        rw [hloc]
        cases op
        case store rl a1 v1 tok =>
          have hsc' : OpScope cx (.store rl a1 v1 tok) := hsc
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := store_TIB hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact .inl (own_x hsto hus' hini hjl)
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
              intro F h1 h2
              have hr' := hr
              rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
              obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr'
              rw [← hreq] at htn
              simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_map] at hin
              obtain ⟨s'', hs'', he⟩ := hin
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, -, -⟩ := he
              exact htn (PVc.storeUnits_keepLow hs'' htp h1 h2)
            exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk (fun hb0 _ => own_x hsto hus' hb0 hjl))
        case xchg a1 v1 =>
          have hsc' : OpScope cx (.xchg a1 v1) := hsc
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := xchg_TIB hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact .inl (own_x hsto hus' hini hjl)
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
              intro F h1 h2
              have hr' := hr
              rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
              obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr'
              rw [← hreq] at htn
              simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_flatMap, List.mem_map] at hin
              obtain ⟨⟨s1, old⟩, hl, s'', hs'', he⟩ := hin
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, -, -⟩ := he
              have hk1 := (TermFul.loadUnits_keep us 0 _ _ hl).2.2
              have hh1 : t ∈ s1.promises := by rw [hk1]; exact htp
              exact htn (PVc.storeUnits_keepLow hs'' hh1 h1 h2)
            exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk (fun hb0 _ => own_x hsto hus' hb0 hjl))
        case xchgAt =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAt_uaRB hop hi hE htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case xchgAtF =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAtF_uaRB hop hi hE htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case stl =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stl_uaRB hop hi htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case stlw =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stlw_uaRB hop hi htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case bufInit bb i1 v1 =>
          exact .inr ⟨x, bb, i1, v1, e, hterm⟩
        all_goals simp [TermFul.UnitsOp] at hu
      · have hsc' : OpScope cx (.fetch o acq rel a' v) := hsc
        obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := fetch_TIB hop hsc' hi hE htv hm hea hb
        rcases hμ with rfl | rfl
        · exact .inl (add_zero_x (own_x (j := 0) hsto hus' hini (by decide)))
        · have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
            intro F h1 h2
            have hr' := hr
            rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
            obtain ⟨⟨s', t'', ws'⟩, hin, hreq⟩ := hr'
            rw [← hreq] at htn
            simp only [evalOp, hea, hev, hb, List.mem_map] at hin
            obtain ⟨⟨mem', th'⟩, hst, he⟩ := hin
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, -, -⟩ := he
            exact htn (PVc.stepRmw_keepLow hst htp h1 h2)
          exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk
            (fun hb0 _ => add_zero_x (own_x (j := 0) hsto hus' hb0 (by decide))))
  · rw [hterm] at hT hsc
    obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := cas_TIB hT hsc hi hE htv hm hea hb
    rcases hμ with rfl | rfl
    · exact .inl (add_zero_x (own_x (j := 0) hsto hus' hini (by decide)))
    · have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
        intro F h1 h2
        have hr' := hr
        simp only [tstep, hterm, hea, hee, hev, hb, List.mem_map] at hr'
        obtain ⟨⟨mem', th'⟩, hst, hreq⟩ := hr'
        rw [← hreq] at htn
        exact htn (PVc.stepRmw_keepLow (s := stOf mem pairs th) hst htp h1 h2)
      exact .inl (pub_xB hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk
            (fun hb0 _ => add_zero_x (own_x (j := 0) hsto hus' hb0 (by decide))))
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:146 buf_x
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem buf_xB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {m : Msg} (hE : EnvOKB p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hsw : TermFul.SW g mem pairs th m.loc m.val) {x : String} {bb ib v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit bb ib v) e) :
    ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e ∧ ∃ rt w ad rti wi n c,
      evalAt th.env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧ evalAt th.env ib = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ad.label = m.loc.label ∧ (CE η).sto m.loc.label = some c ∧
      ∀ N el us, c.ty = .array (.lit N) el → accs el = some us → m.loc.offset < (n + 1) * nWords us := by
  refine ⟨x, bb, ib, v, e, hterm, ?_⟩
  rcases hsw with ⟨x', op, e', hterm', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm', -⟩
  · rw [hterm] at hterm'
    simp only [Expr.let_.injEq] at hterm'
    obtain ⟨rfl, rfl, rfl⟩ := hterm'
    rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop', -⟩
    · have hT' := hT
      rw [hterm] at hT'
      cases hT' with
      | let_ hop _ => rw [hl]; exact TermAnch.Flat.bufInit_siteB (η := η) hop hi hE htv hu (TermFul.OneAt_lt hj)
    · cases hop'
  · rw [hterm] at hterm'; cases hterm'
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:169 wrSiteA_ok
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrSiteA_okB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : TermSeenHid.EnvVR th) (hr : r ∈ tstep g mem pairs th) :
    WrSiteA g (CE η) mem pairs th r := by
  intro t m ht hmt
  by_cases hlt : t < mem.size
  · have hm0 : mem[t]? = some mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow hr).1 t _ hm0
    rw [hmt] at e2
    simp only [Option.some.injEq] at e2
    have hm1 : mem[t]? = some m := by rw [hm0, e2]
    by_cases htp : t ∈ th.promises
    · obtain ⟨m', hm', hsw, -, -⟩ :=
        (TermFul.tstep_fulfil (MemInv_promLtB hm) (MemInv_nopairB hm) hr).2 t htp ht
      have hm'' : mem[t]? = some m' := hm'
      rw [hm1] at hm''; cases hm''
      have hss := TermTyped.scopeD_SW hsc hsw
      rcases TermPlantF.Flat.SWIniB hE hT htv hi hm hss hsw with ⟨c, hc, hI⟩ | ⟨x, bb, ib, v, e, hterm⟩
      · rcases ful_xB hE hT htv hi hm hss hvr hr htp ht hsw with ⟨c', hc', hx⟩ | ⟨x, bb, ib, v, e, hterm⟩
        · rw [hc] at hc'; cases hc'
          refine .inr (.inr (.inl ⟨c, hc, hI, ?_⟩))
          rcases hx with h | h | h
          · exact .inl h
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr h))
        · exact .inr (.inr (.inr (buf_xB hE hT htv hi hsw hterm)))
      · exact .inr (.inr (.inr (buf_xB hE hT htv hi hsw hterm)))
    · exact .inl ⟨htp, hm1⟩
  · have hge : mem.size ≤ t := Nat.le_of_not_lt hlt
    rcases TermAnch.Flat.wrSite_okB hE hT htv hi hm hsc hr t m ht hmt with h | h | ⟨c, hc, hI⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨c, hc, hI, .inr (.inl hge)⟩))
    · exact .inr (.inr (.inr h))
end
end TermWrSiteA.Flat

-- PORTB TermWrSiteA.lean:206 wrSiteA_okU
namespace TermWrSiteA.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat TermPlantF.Flat TermB5.Flat TermAnch.Flat TermPredStoreFree.Flat TermPredStoreFree.PVc.Flat TermWrSiteA.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem wrSiteA_okUB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOKB p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term)
    (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts) (hr : r ∈ tstep g mem pairs th) :
    WrSiteA g (CE η) mem pairs th r :=
  wrSiteA_okB hE hT htv hi hm hsc hvr hr
end
end TermWrSiteA.Flat

