import WeakCore.TermK5O
import WeakCore.TermRunLoc
import WeakCore.TermNoBufOwn
import WeakCore.TermBufPubT

/-!
# TermRunLocK: the own-cell count residual at key-held frontier cells (runAgree)

`iniK_core`: at an own start cell `a` with a start frontier, the run's count is at most the start
count, given (1) the run's held counts `IniHeld`, (2) the owner's invariant at the end (`TermK5Lp.bufCap_gt`),
(3) at a buffer of inhabited zero-width elements, the start count covers every slot (`ZwIniG` at the
start), (4) every outstanding promise of the start at `a` lies below the start count (`PromIniOK` at
the start), and (5) every unit added beyond the start count has a witness index below the start
memory's size (the window). No unit-free argument is needed at zero width: the count there is bounded
by the slot count, which the start count already covers.
-/

namespace TermRunLocK
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermTyped
open TermMain TermPlantF TermGbLp
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- **The count bound at a key-held own frontier cell.** -/
theorem iniK_core {E0 E2 : TEnv} {mem : Memory} {P : List Ts} {v : Nat} {g : G} {s2 : St}
    (hrl : ∀ l, E0.rini l ≤ E0.ini l) (hIH : IniHeld (WitP mem P) E0 E2 v) (hext : Ext E0 E2)
    (hmi : MemInv g E2 s2) {a : AllocLabel} {c : Cell} (hc : E0.sto a = some c) (ho : c.owner = some E0.tid)
    (hzw : ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → nWords us = 0 → InhZ E0.prog e →
      N ≤ E0.ini a)
    (hpI : ∀ τ m, τ ∈ P → mem[τ]? = some m → m.loc.label = a → ∀ N e us, c.ty = .array (.lit N) e →
      accs e = some us → m.loc.offset < E0.ini a * nWords us)
    (hu : ∀ N e us, c.ty = .array (.lit N) e → accs e = some us →
      ∀ o, o < E2.ini a * nWords us → ¬ o < E0.ini a * nWords us → ∃ τ, τ < mem.size ∧ WitP mem P a o τ) :
    E2.ini a ≤ E0.ini a := by
  refine Classical.byContradiction fun hle => ?_
  have hlt : E0.ini a < E2.ini a := Nat.lt_of_not_le hle
  obtain ⟨N, e, hT⟩ : ∃ N e, c.ty = .array (.lit N) e :=
    Classical.byContradiction fun hb => hle (capNAt_of hrl hIH a c hc hb)
  obtain ⟨us, hus, hN, hZ⟩ := TermK5Lp.bufCap_gt hrl hIH hext hmi hc ho hle hT
  by_cases hw0 : nWords us = 0
  · have hinh := hZ hw0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
    rw [hext.2.2.1] at hinh
    exact hle (Nat.le_trans hN (hzw N e us hT hus hw0 hinh))
  · have hpos : 0 < nWords us := Nat.pos_of_ne_zero hw0
    have ho1 : E0.ini a * nWords us < E2.ini a * nWords us := Nat.mul_lt_mul_of_pos_right hlt hpos
    obtain ⟨τ, hτ, hW⟩ := hu N e us hT hus _ ho1 (Nat.lt_irrefl _)
    rcases hW with h | ⟨hτP, m, hm, hloc⟩
    · exact absurd hτ (Nat.not_lt.2 h)
    · have h := hpI τ m hτP hm (by rw [hloc]) N e us hT hus
      rw [hloc] at h
      exact Nat.lt_irrefl _ h

/-- **The promise-step residual holds** at the key-held own frontier cells: by `iniK_core`, with
the window `TermNoBufOwn.winF` at the run's end (no publish of the cell) or at its publish point
(`PfrProvO`), the start's `plantIdx`, `promIni`, `zwIni`; at the key-less ones by `IniLoc`. -/
theorem w3K_F {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP p k arch Sp Init MintOK c0)
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
  have hwin := TermNoBufOwn.winF (hV0 := hV0) hps h0d hsc hw hNP X hk hEg hoj hfg hKey htm hmP
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

/-- An element of an array below its size is some element. -/
theorem get_some {mem : Memory} {t : Nat} (h : t < mem.size) : ∃ m, mem[t]? = some m :=
  ⟨mem[t], Array.getElem?_eq_getElem h⟩

/-- **The thread-step residual holds** at the key-held own frontier cells of the post-step
environment: such a cell is a start cell with a start frontier (the footprint; a frontier set in the
step is the step's publish, `PfrG`, so `IniZT`), the step is not its publish, and `iniK_core` with the
window `TermNoBufOwn.winT` at the run's end or its publish point (`PfrProvO`); the promises of `r`
are the start's (`tstep_fulfil`), at the same messages (`tstep_grow`). -/
theorem w3K_T {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hk : k.storeDepRts = true)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {η : TEnv} {E' : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (hCE : CE η = Cut Eg i S)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {c1 : Cfg} {th1 : TTh} {E1 : TEnv}
    (hc1 : Certified p k arch c1 i) (hth1 : c1.ths[i]? = some th1) (hext : Ext E' E1)
    (hmi : MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1))
    (hIL : IniLoc (IniZTK Eg Tot HP i th) E' E1)
    (hIH : IniHeld (WitP c'.mem r.2.2.promises) E' E1 th1.vs.vWr)
    (hPO : TermK5O.PfrProvO p k arch i (WitP c'.mem r.2.2.promises) E' c' c1 E1) :
    TermRunLoc.RunAgreeW3Z (IniZT Eg i th) E' E' (fun _ => False) E1 := by
  refine ⟨fun l cl hcl ho hz hf0 => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f, E'.pfr l = some f := hf0.resolve_right (fun h => h)
  have hnz : ¬ IniZT Eg i th l := hz.resolve_right (by rw [hf]; exact fun e => by cases e)
  have htid : E'.tid = i := by rw [hF.2.1, hCE]; rfl
  have hoi : cl.owner = some i := by rw [ho, htid]
  obtain ⟨hEg, hfg⟩ : Eg.sto l = some cl ∧ Eg.pfr l = some f :=
    (TermBufPubT.post_pfr_sto X hCE hF hPfrP hcl hf).resolve_right (fun h => hnz (.inr h))
  have hnpub : ¬ TermOwnG0Defs.PubAt th l := fun hp => hnz (.inr (TermBufPubT.pubStep_of hp hEg hoi))
  by_cases hk0 : (Tot i + HP i) (.own l) = 0
  · rw [(hIL l cl f (.inr ⟨cl, hEg, hoi, hk0⟩) hcl hf).1]
    exact Nat.le_refl _
  have hKey : TermPlantAtT.KeyG Tot HP i l := Nat.pos_of_ne_zero hk0
  obtain ⟨t, mP, htm, hmP, htP, -, -, -⟩ :=
    X.inv.plantIdx hk i th l cl X.hth hEg hoi (by rw [hfg]; exact fun e => by cases e) hKey
  have hvt : mP.view < c.mem.size := by
    obtain ⟨m, hm, hlt⟩ := promViewLt_run h0 X.run i th t X.hth htP
    rw [hmP] at hm
    cases hm
    exact Nat.lt_trans hlt (TermMem.lt_of_get hmP)
  have hwin := TermNoBufOwn.winT (hV0 := hV0) hps h0d hCW hNP X hk hEg hoi hfg hKey htm hmP hnpub
  obtain ⟨S', -, -, hmi0, -⟩ := X.inv.thr i th X.hth
  have hsub := (TermFul.tstep_fulfil (MemInv_promLt hmi0) (MemInv_nopair hmi0) X.hr).1
  have hgr := (TermFul.tstep_grow X.hr).1
  have hiniLe : Eg.ini l ≤ E'.ini l := by
    have h := (hF.2.2.2.2.1 l).1
    rw [hCE] at h
    exact h
  have hlt' : ∀ τ, τ < c.mem.size → τ < c'.mem.size := fun τ hτ => by
    obtain ⟨m0, hm0⟩ := get_some hτ
    have h := hgr τ m0 hm0
    rw [← X.e1] at h
    exact TermMem.lt_of_get h
  refine TermRunLocK.iniK_core (hF.2.2.2.2.2.2.2.2.2.2.1 (fun l => by rw [hCE]; exact X.inv.rle l)) hIH hext hmi
    hcl ho
    (fun N e us hT hus hw0 hinh => Nat.le_trans (X.inv.zwIni l cl N e us
      (by rw [hfg]; exact fun e => by cases e) (fun hp => hnz (.inl ⟨hp, by rw [hEg]; exact fun e => by cases e⟩))
      hEg hT hus hw0 (by rw [hF.1, hCE] at hinh; exact hinh)) hiniLe)
    (fun τ m hτ hm hlab N e us hT hus => by
      have hτ0 : τ ∈ th.promises := hsub.subset hτ
      have hlt : τ < c.mem.size := MemInv_promLt hmi0 τ hτ0
      obtain ⟨m0, hm0⟩ := get_some hlt
      have hm1 := hgr τ m0 hm0
      rw [← X.e1, hm] at hm1
      cases hm1
      have h := X.inv.promIni i th τ m X.hth hτ0 hm0 cl (by rw [hlab]; exact hEg) ⟨f, by rw [hlab]; exact hfg⟩
        N e us hT hus
      rw [hlab] at h
      exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right _ hiniLe))
    (fun N e us hT hus o ho1 ho2 => ?_)
  rcases hPO l cl f hcl ho hf with hNP2 | ⟨c2, th2, c2', hNP1, hth2, -, hs2, hsolo, hu⟩
  · obtain ⟨τ, hτ, hW⟩ := (hIH (hF.2.2.2.2.2.2.2.2.2.2.1 (fun l => by rw [hCE]; exact X.inv.rle l))).2.1
      l cl hcl ho N e us hT hus o ho1 ho2
    exact ⟨τ, hlt' τ (Nat.lt_of_le_of_lt (Nat.le_trans hτ (hwin c1 th1 hNP2 hc1 hth1)) hvt), hW⟩
  · have hc2 : Certified p k arch c2 i := TermGlob.certified_back (.thread hs2 hsolo) hc1
    obtain ⟨τ, hτ, hW⟩ := hu N e us hT hus o ho1 ho2
    exact ⟨τ, hlt' τ (Nat.lt_of_le_of_lt (Nat.le_trans hτ (hwin c2 th2 hNP1 hc2 hth2)) hvt), hW⟩

/-- **`RunAgreeF3K` holds** (`w3K_F`). -/
theorem runAgreeF3K_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hw : TermCertScope.CertWinP p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hk : k.storeDepRts = true) :
    TermRunLoc.RunAgreeF3K p k arch Sp Init MintOK c0 :=
  fun X _ _ _ _ _ hc hth2 hext hmi _ hIL hIH _ hPO => w3K_F (hV0 := hV0) h0 hps h0d hsc hw hNP hk X hc hth2 hext hmi hIL hIH hPO

/-- **`RunAgreeT3K` holds** (`w3K_T`). -/
theorem runAgreeT3K_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch) (hk : k.storeDepRts = true) :
    TermRunLoc.RunAgreeT3K p k arch Sp Init MintOK c0 :=
  fun X Y Z hPfrP _ _ _ _ hc hth1 hext hmi _ hIL hIH hPO =>
    w3K_T (hV0 := hV0) h0 hps h0d hCW hNP hk X Y.1 Z.1 hPfrP hc hth1 hext hmi hIL hIH hPO

/-- **The `RunAgree` field's content holds** (`TermRunPayT.RunAgreeFT3`): `runAgreeF2_of`/`runAgreeT2_of`
at `runAgreeF3K_of`/`runAgreeT3K_of`. -/
theorem runAgreeFT3_holds {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hk : k.storeDepRts = true) (hP : ProgT p) [ProgRetIall p] [TermTyped.WrIniC]
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hS : TermCertScope.CertScopeP p k arch Sp Init MintOK c0) (hWn : TermCertScope.CertWinP p k arch Sp Init MintOK c0)
    (hCW : TermCertScope.CertWinC p k arch Sp Init MintOK c0) (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TermRunPayT.RunAgreeFT3 p k arch Sp Init MintOK c0 :=
  ⟨TermRunLoc.runAgreeF2_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) h0 hk hP hS hWn
      (runAgreeF3K_of (hV0 := hV0) h0 hps h0d hS hWn hNP hk),
    TermRunLoc.runAgreeT2_of (runAgreeT3K_of (hV0 := hV0) h0 hps h0d hCW hNP hk)⟩

end TermRunLocK

#print axioms TermRunLocK.iniK_core
#print axioms TermRunLocK.w3K_F
#print axioms TermRunLocK.w3K_T
#print axioms TermRunLocK.runAgreeF3K_of
#print axioms TermRunLocK.runAgreeT3K_of
#print axioms TermRunLocK.runAgreeFT3_holds
