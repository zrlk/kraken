import WeakCore.EtaW
import WeakCore.TermRunLocK
import WeakCore.TermK5Z
import WeakCore.TermIniOpK
import WeakCore.TermPlantW2
import WeakCore.TermBiiF

/-! **EtaCertWinFst** (B12 conj 2): internal retype of the W run facts that read only conjunct 1 of `CertWinP`
(`(hw X).1`) to the conjunct-1 type `CertWinP1`.  Bodies are W's, with `(hw X).1` → `hw X`. -/
namespace TermCertScope
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- Conjunct 1 of `CertWinP` (the pre-promise anchor). -/
def CertWinP1 (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → NoHoldPubA p k arch (Cut Eg j S) (Cut Eg j S) j c1
end TermCertScope

namespace TermOwnK5
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnK1 TermCertScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem winQP1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (Y : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {S : AllocLabel → Prop} (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S) :
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
      ScopeAt p j c1 ∧ NoHoldPubA p k arch (Cut Eg j S) (Cut Eg j S) j c1 :=
  fun c1 h1 h2 => ⟨hsc Y c1 h1 h2, (hw Y) S hS c1 h1 h2⟩

theorem bufInitIniF_pub1 [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel}
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (Y : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hpub : Eg.pubd l) (hsto : Eg.sto l ≠ none)
    {c1 : Cfg} {th1 : TTh} {y : String} {bb ib v' : At} {e : Expr}
    (h1 : Solo p k arch j (promise c j a v w) c1) (hc1 : Certified p k arch c1 j)
    (hth1 : c1.ths[j]? = some th1) (hterm : th1.term = .let_ y (.bufInit bb ib v') e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ rt w' ad g0, evalAt th1.env bb = some (rt, [w']) → w'.val = .loc ad g0 → ad.label ≠ l := by
  obtain ⟨S, hS⟩ := Y.inv.thr j th Y.hth
  obtain ⟨th2, hth2, h⟩ := ownXLe0_prom_noOwnUse hP (winQP1 hsc hw Y hS) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 Y.run) Y.hw)
    (ownXLe_start_pub Y.inv Y.hth hS hpub hsto) (TermMain.tidAt_cut Y.inv j S) Y.hw h1 hc1 hPS hSub hSig
  obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
  exact bufInit_ne_of_use hterm h

end TermOwnK5

namespace TermNoBufOwn
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnK5 TermCertScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem noBufF_noKey1 [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {x : AllocLabel} {cl : Cell} (hsto : Eg.sto x = some cl) (hin : cl.owner = some j ∨ Eg.pfr x ≠ none)
    (hk0 : (Tot j + HP j) (.own x) = 0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → ∀ th1, c1.ths[j]? = some th1 →
      ¬ BufInitOn th1 x := by
  intro c1 h1 hc1 th1 hth1
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  obtain ⟨th2, hth2, h⟩ := ownXLe0_prom_noOwnUse hP (winQP1 hsc hw X hS) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw)
    (ownXLe_start_le X.inv X.hth hS hsto hin (Nat.le_of_eq hk0)) (TermMain.tidAt_cut X.inv j S) X.hw h1 hc1 hPS hSub hSig
  obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
  exact not_bufInitOn h

theorem noFul_preP1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hk : k.storeDepRts = true) {l : AllocLabel} {cl : Cell} {f t : Ts}
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some j) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP j l) (htm : TermPtrRts.tminG Eg c j l = some t) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → t ∈ th2.promises := by
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  exact TermPlantAtW.noFul_ofNF hNP hps hk
    (TermPtrKey.nfInv_prom (TermPlantAtW.nfInv_pre hps h0d X.inv X.run X.hth hS hk hsto hown hf hnp htm))
    (fun c2 h2 hc2 => hsc X c2 h2 hc2) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw) (fun c2 h2 hc2 => (hw X) S hS c2 h2 hc2)

theorem winF1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hk : k.storeDepRts = true) {l : AllocLabel} {cl : Cell} {f t : Ts} {mP : Msg}
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some j) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP j l) (htm : TermPtrRts.tminG Eg c j l = some t) (hmP : c.mem[t]? = some mP) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → th2.vs.vWr ≤ mP.view := by
  intro c2 th2 h2 hc2 hth2
  have hNo := noFul_preP1 (hV0 := hV0) hps h0d hsc hw hNP X hk hsto hown hf hnp htm
  have hlt : t < c.mem.size := TermMem.lt_of_get hmP
  have hmB : ∀ c3, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c3 → c3.mem[t]? = some mP :=
    fun c3 h3 => W2New.solo_mem h3.toSolo (by
      rw [(TermLiveProps.promise_ext _ _ a v w).get t hlt]; exact hmP)
  obtain ⟨cs, hs, hn⟩ := hc2
  exact TermPtrRts.winLe_gen (j := j) (a := l) hNo hmB hs hn h2 th2 hth2 (hNo c2 th2 h2 ⟨cs, hs, hn⟩ hth2)

end TermNoBufOwn

namespace TermK5R
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermCut TermSys TermCertScope TermOwnK5 TermOwnK1 TermOwnX2 TermPlantF TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem bufInitPubFR1 [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} {cl : Cell} (hsto : Eg.sto l = some cl) (hin : cl.owner = some j ∨ Eg.pfr l ≠ none)
    {c1 c1' c2 : Cfg} {th1 th2 : TTh} (h1 : Solo p k arch j (promise c j a v w) c1)
    (hth1 : c1.ths[j]? = some th1) (hpub : TermOwnG0Defs.PubAt th1 l) (hs : c1' ∈ threadSteps p k arch c1 j)
    (h2 : Solo p k arch j c1' c2) (hc2 : Certified p k arch c2 j) (hth2 : c2.ths[j]? = some th2) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ¬ BufInitOn th2 l := by
  rintro ⟨y, bb, ib, v', e, rt, w', ad, g, hterm, hea, hwv, hl⟩
  obtain ⟨y1, a1, e1, rt1, ws1, ad1, hterm1, hea1, hws1, hx1⟩ := hpub
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  have h0 : OwnXLe p k arch (Cut Eg j S) j l 1 (promise c j a v w) :=
    ownXStepP_all 1 _ c a v w (ownXLe_start X.inv X.hth hS hsto hin) X.hw X.cert
  obtain ⟨th3, hth3, h⟩ :=
    ownXLe_pub_noOwnUse hP (winQP1 hsc hw X hS) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw) h0 (TermMain.tidAt_cutP X.inv j S) h1 hs hth1 hterm1 hea1 hws1 hx1 h2 hc2 hPS hSub hSig
  obtain rfl : th3 = th2 := Option.some.inj (hth3.symm.trans hth2)
  exact bufInit_ne_of_use hterm h rt w' ad g hea hwv hl

theorem bufInitPubFR_plant1 [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} (hL : PlantL c Eg j th a v w l)
    {c1 c1' c2 : Cfg} {th1 th2 : TTh} (h1 : Solo p k arch j (promise c j a v w) c1)
    (hth1 : c1.ths[j]? = some th1) (hpub : TermOwnG0Defs.PubAt th1 l) (hs : c1' ∈ threadSteps p k arch c1 j)
    (h2 : Solo p k arch j c1' c2) (hc2 : Certified p k arch c2 j) (hth2 : c2.ths[j]? = some th2) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ¬ BufInitOn th2 l := by
  obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, -⟩ := hL
  subst hal
  exact bufInitPubFR1 (hV0 := hV0) hP hsc hw X (cutSto_sub hc1) (.inl ho1) h1 hth1 hpub hs h2 hc2 hth2 hPS hSub hSig

end TermK5R

namespace TermK5Z
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermCut TermSys TermCertScope TermPlantF TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem hZp_of1 [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : WeakMem.Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (S : WeakMem.AllocLabel → Prop) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c1 → c1.ths[j]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 j → Solo p k arch j c1' c3 →
      Certified p k arch c3 j → c3.ths[j]? = some th3 → (Cut Eg j S).sto l = some cl →
      cl.owner = some (Cut Eg j S).tid → ¬ BufInitOn th3 l :=
  fun _ _ _ _ _ _ _ h1 hth1 hpub hs h2 hc3 hth3 hcl ho =>
    TermK5R.bufInitPubFR1 (hV0 := hV0) hP hsc hw X ((cutSto_some.1 hcl).1) (.inl ho) h1.toSolo hth1 hpub hs h2 hc3 hth3 hPS hSub hSig

theorem bufInitPubFR_of1 [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitPubFR p k arch Sp Init MintOK c0 :=
  fun X S => hZp_of1 (hV0 := hV0) hP hsc hw X S hPS hSub hSig

end TermK5Z

namespace TermIniOpK
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open TermCertScope TermOwnK5 TermPlantF
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem bufInitPubF_of1 [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitPubF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w Y c1 h1 hc1 th1 hth1 l hb hz
  rcases hz with ⟨hpub, hsto⟩ | ⟨cl, hsto, ho, hk0⟩
  · obtain ⟨y, bb, ib, v', e, rt, w', ad, g, hterm, hea, hwv, hl⟩ := hb
    exact bufInitIniF_pub1 (hV0 := hV0) hP hsc hw Y hpub hsto h1 hc1 hth1 hterm hPS hSub hSig rt w' ad g hea hwv hl
  · exact TermNoBufOwn.noBufF_noKey1 (hV0 := hV0) hP hsc hw Y hsto (.inl ho) hk0 hPS hSub hSig c1 h1 hc1 th1 hth1 hb

end TermIniOpK

namespace TermRunLoc
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermTyped TermMain TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem runAgreeF2_of1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (_hk : k.storeDepRts = true) (hP : ProgT p) [ProgRetIall p] [TermTyped.WrIniC]
    (hS : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hWn : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (h : RunAgreeF3K p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TermRunPay.RunAgreeF2 p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV hPO
  have hvl : ∀ t, t ∈ th.promises → ∃ m : Msg, c.mem[t]? = some m ∧ m.view < t :=
    fun t ht => promViewLt_run h0 X.run j th t X.hth ht
  have hpl : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => by
    obtain ⟨m, hm, -⟩ := hvl t ht
    rcases Nat.lt_or_ge t c.mem.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hm; cases hm
  have hG : ∀ l, PlantL c Eg j th a v w l →
      ∃ wt, wt < c.mem.size ∧ TermOwnG0W.G0WinW p k arch c j a v w l wt := by
    intro l hl
    have hpf : (cutP Eg j).pfr l = none := by
      obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, -, -, hpf⟩ := hl
      subst hal; exact hpf
    obtain ⟨t, b, a', g, wt, ca, cr0, -, hmt, ha, hca, hno, hrf, hcr, hwt⟩ := plantRoot X.hth X.hw hvl hl
    obtain ⟨S0, hS0⟩ := X.inv.thr j th X.hth
    obtain ⟨E0, hE0e, hE0, h0P⟩ := rootH0P (cl := cr0) X hS0 hpf
    have hcr0 : E0.sto l = some cr0 := by rw [hE0]; exact hcr
    exact ⟨wt, hwt, TermOwnG0.g0WinT_ofP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP (hS X) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw)
      (fun c1 h1 h2 => by rw [hE0e]; exact (hWn X) S0 hS0 c1 h1 h2) X.hth hpl hcr0
      (TermCert.winInv_prom (TermCert.winInv_refl X.hth)) h0P hmt ha (by rw [hE0]; exact hca) hno hrf hcr0 (hTA := by rw [hE0e]; exact TermMain.tidAt_cut X.inv j S0)⟩
  have hini : ∀ l, (Cut Eg j S).ini l ≤ (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)).ini l :=
    fun l => by
      by_cases hl : PlantL c Eg j th a v w l
      · rw [plantE_ini_in hl]; exact Nat.le_max_left _ _
      · rw [plantE_ini_ne hl]; exact Nat.le_refl _
  refine runAgreeW2_of hfb hext (fun l B hB => (hmi.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1) hini
    (fun l hl => plantE_pfr_ne hl) (fun l hl => ?_)
    (runAgreeW3_of_iniLoc hini (iniLoc_mono (fun _ hz => .inl hz) hIL) (runAgreeW3Z_of_K (fun l => X.inv.rle l) hc hth2 hIH hext hmi hPV
      (fun l hl => by
        obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, -, -, hpf⟩ := hl
        subst hal; exact hpf)
      (h X S c2 th2 E2 hs hc hth2 hext hmi hfb hIL hIH hPV hPO) hG))
  · obtain ⟨l', -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, -⟩ := hl
    subst hal
    exact ⟨cl1, hc1, ho1⟩

end TermRunLoc

namespace TermRunLocK
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermTyped
open TermMain TermPlantF TermGbLp
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open TermCertScope
theorem w3K_F1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hk : k.storeDepRts = true)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {S : AllocLabel → Prop} {c2 : Cfg} {th2 : TTh} {E2 : TEnv}
    (hc2 : Certified p k arch c2 j) (hth2 : c2.ths[j]? = some th2) (hext : Ext (Cut Eg j S) E2)
    (hmi : MemInv (gOf p k arch c2 j) E2 (stOf c2.mem c2.pairs th2))
    (hIL : IniLoc (IniZK Eg Tot HP j) (Cut Eg j S) E2)
    (hIH : IniHeld (WitP c.mem th.promises) (Cut Eg j S) E2 th2.vs.vWr)
    (hPO : TermK5O.PfrProvO p k arch j (WitP c.mem th.promises) (Cut Eg j S) (promise c j a v w) c2 E2) :
    TermRunLoc.RunAgreeW3K (IniZF Eg) (Cut Eg j S)
      (plantE (Cut Eg j S) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) (PlantL c Eg j th a v w) E2 := by
  refine ⟨fun l cl hcl ho hz hf0 hL => ?_⟩
  obtain ⟨f, hf⟩ := hf0
  rw [plantE_ini_ne hL]
  have hEg : Eg.sto l = some cl := cutSto_sub hcl
  have hoj : cl.owner = some j := ho
  have hnz : ¬ IniZF Eg l := by
    rcases hz with h | h
    · exact h
    · rw [h] at hf; cases hf
  by_cases hk0 : (Tot j + HP j) (.own l) = 0
  · rw [(hIL l cl f (.inr ⟨cl, hEg, hoj, hk0⟩) hcl hf).1]
    exact Nat.le_refl _
  have hKey : TermPlantAtT.KeyG Tot HP j l := Nat.pos_of_ne_zero hk0
  have hfg : Eg.pfr l = some f := hf
  obtain ⟨t, mP, htm, hmP, htP, -, -, -⟩ :=
    X.inv.plantIdx hk j th l cl X.hth hEg hoj (by rw [hfg]; exact fun e => by cases e) hKey
  have hvt : mP.view < c.mem.size := by
    obtain ⟨m, hm, hlt⟩ := promViewLt_run h0 X.run j th t X.hth htP
    rw [hmP] at hm
    cases hm
    exact Nat.lt_trans hlt (TermMem.lt_of_get hmP)
  have hwin := TermNoBufOwn.winF1 (hV0 := hV0) hps h0d hsc hw hNP X hk hEg hoj hfg hKey htm hmP
  refine TermRunLocK.iniK_core (fun l => X.inv.rle l) hIH hext hmi hcl ho
    (fun N e us hT hus hw0 hinh => X.inv.zwIni l cl N e us (by rw [hfg]; exact fun e => by cases e)
      (fun hp => hnz ⟨hp, by rw [hEg]; exact fun e => by cases e⟩) hEg hT hus hw0 hinh)
    (fun τ m hτ hm hlab N e us hT hus => by
      have h := X.inv.promIni j th τ m X.hth hτ hm cl (by rw [hlab]; exact hEg) ⟨f, by rw [hlab]; exact hfg⟩
        N e us hT hus
      rw [hlab] at h
      exact h)
    (fun N e us hT hus o ho1 ho2 => ?_)
  rcases hPO l cl f hcl ho hf with hNP2 | ⟨c1, th1, c1', hNP1, hth1, -, hs1, hsolo, hu⟩
  · obtain ⟨τ, hτ, hW⟩ := (hIH (fun l => X.inv.rle l)).2.1 l cl hcl ho N e us hT hus o ho1 ho2
    exact ⟨τ, Nat.lt_of_le_of_lt (Nat.le_trans hτ (hwin c2 th2 hNP2 hc2 hth2)) hvt, hW⟩
  · have hc1 : Certified p k arch c1 j := TermGlob.certified_back (.thread hs1 hsolo) hc2
    obtain ⟨τ, hτ, hW⟩ := hu N e us hT hus o ho1 ho2
    exact ⟨τ, Nat.lt_of_le_of_lt (Nat.le_trans hτ (hwin c1 th1 hNP1 hc1 hth1)) hvt, hW⟩

theorem runAgreeF3K_of1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hk : k.storeDepRts = true) :
    TermRunLoc.RunAgreeF3K p k arch Sp Init MintOK c0 :=
  fun X _ _ _ _ _ hc hth2 hext hmi _ hIL hIH _ hPO => w3K_F1 (hV0 := hV0) h0 hps h0d hsc hw hNP hk X hc hth2 hext hmi hIL hIH hPO

theorem runAgreeFT3_holds1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hk : k.storeDepRts = true) (hP : ProgT p) [ProgRetIall p] [TermTyped.WrIniC]
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hS : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hWn : TermCertScope.CertWinP1 p k arch Sp Init MintOK c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0) (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TermRunPayT.RunAgreeFT3 p k arch Sp Init MintOK c0 :=
  ⟨TermRunLoc.runAgreeF2_of1 (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) h0 hk hP hS hWn
      (runAgreeF3K_of1 (hV0 := hV0) h0 hps h0d hS hWn hNP hk),
    TermRunLoc.runAgreeT2_of (runAgreeT3K_of (hV0 := hV0) h0 hps h0d hCW hNP hk)⟩

end TermRunLocK

