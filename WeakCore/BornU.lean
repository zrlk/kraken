import WeakCore.ShadowPubStep
/-! **BornU** (ownXLe_born): the U-variant of the ♭ x-machinery (KLayer closure of `OwnXLeB` + ShadowPubStep's package-4/run
tail), generated, with hand fixes.  The tracked label `x` may be UNBORN: the x slots
`E.sto x ≠ none ∧ T ≤ n` become `(E.sto x = none → T ≤ n) ∧ T ≤ n + 1`; per step, `BornMono` (born stays born)
and `T' ≤ T0 + bornInc` (the count grows by one only where the step gives `x` its cell); the `n = 0` rini slot
is `True`. -/
set_option autoImplicit false
set_option maxErrors 100000
namespace TermOwnX2.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- Born stays born: `x` has no cell after the step only if it had none before. -/
def BornMono (x : AllocLabel) (E E' : TEnv) : Prop := E'.sto x = none → E.sto x = none

open Classical in
/-- `1` exactly when the step gives the unborn `x` its cell. -/
noncomputable def bornInc (x : AllocLabel) (E E' : TEnv) : Nat :=
  if E.sto x = none ∧ E'.sto x ≠ none then 1 else 0

open Classical in
/-- `1` once `x` has its cell (the ♭ bound is `n` before, `n + 1` after). -/
noncomputable def bornBit (x : AllocLabel) (E : TEnv) : Nat := if E.sto x = none then 0 else 1

theorem bornBit_none {x : AllocLabel} {E : TEnv} (h : E.sto x = none) : bornBit x E = 0 := by
  unfold bornBit; rw [if_pos h]

theorem bornBit_some {x : AllocLabel} {E : TEnv} (h : E.sto x ≠ none) : bornBit x E = 1 := by
  unfold bornBit; rw [if_neg h]

theorem bornBit_congr {x : AllocLabel} {E E' : TEnv} (h : E'.sto = E.sto) : bornBit x E' = bornBit x E := by
  unfold bornBit; rw [h]

theorem bornInc_born {x : AllocLabel} {E E' : TEnv} (h0 : E.sto x = none) (h1 : E'.sto x ≠ none) :
    bornInc x E E' = 1 := by
  unfold bornInc; rw [if_pos ⟨h0, h1⟩]

theorem bornMono_refl (x : AllocLabel) (E : TEnv) : BornMono x E E := fun h => h

theorem bornInc_of_none {x : AllocLabel} {E E' : TEnv} (h : E'.sto x = none) : bornInc x E E' = 0 := by
  unfold bornInc
  rw [if_neg]
  exact fun hh => hh.2 h

theorem bornInc_of_some {x : AllocLabel} {E E' : TEnv} (h : E.sto x ≠ none) : bornInc x E E' = 0 := by
  unfold bornInc
  rw [if_neg]
  exact fun hh => h hh.1
/-- The ♭ step bound: `T0 ≤ n + bornBit E`, born stays born, `T' ≤ T0 + bornInc` give `T' ≤ n + bornBit E'`. -/
theorem bornBit_step {x : AllocLabel} {E E' : TEnv} {T0 T' n : Nat} (h0 : T0 ≤ n + bornBit x E)
    (hm : BornMono x E E') (h1 : T' ≤ T0 + bornInc x E E') : T' ≤ n + bornBit x E' := by
  by_cases hE : E.sto x = none
  · rw [bornBit_none hE] at h0
    by_cases hE' : E'.sto x = none
    · rw [bornInc_of_none hE'] at h1; rw [bornBit_none hE']; omega
    · rw [bornInc_born hE hE'] at h1; rw [bornBit_some hE']; omega
  · have hE' : E'.sto x ≠ none := fun h => hE (hm h)
    rw [bornBit_some hE] at h0; rw [bornInc_of_some hE] at h1; rw [bornBit_some hE']; omega

end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:319 OwnXLe
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXLeBU (p : Prog) (k : Promises.Knobs) (arch : Arch) (E0 : TEnv) (i : Nat) (x : AllocLabel) (n : Nat)
    (c : Cfg) :
    Prop :=
  ∃ th E Tot HP, c.ths[i]? = some th ∧ ThInvREB c.lbase c.n i p E th Tot ∧
    MemInvB (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ MemHeldPB E (stOf c.mem c.pairs th) HP ∧
    (gOf p k arch c i).boxFence = true ∧ StoNIE E ∧ True ∧ Tot (.own x) + HP (.own x) ≤ n + bornBit x E ∧
    ExtB E0 E ∧ AnchR E0 E0 E (stOf c.mem c.pairs th) ∧
    TyOKE (gOf p k arch c i) E ∧ RecFresh (gOf p k arch c i) i th.nalloc ∧ True ∧
    ((∀ l, E0.rini l ≤ E0.ini l) → ∀ l, E.rini l ≤ E.ini l)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:327 OwnXLe.mono
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem OwnXLeBU.mono {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n m : Nat}
    {c : Cfg} (h : OwnXLeBU p k arch E0 i x n c) (hnm : n ≤ m) : OwnXLeBU p k arch E0 i x m c :=
  let ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hs, hle, hx, hA, hTy, hRc, hZ, hR⟩ := h
  ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hs, by omega, hx, hA, hTy, hRc, trivial, hR⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:333 ownXLe_ext
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXLe_extBU {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat}
    {c c' : Cfg} (h : OwnXLeBU p k arch E0 i x n c) (hs : c' ∈ extSteps c i) (hTA : TermTyped.TidAt i c E0) :
    OwnXLeBU p k arch E0 i x n c' := by
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hsx, hle, hx, hA, hTy, hRc, hZ, hR⟩ := h
  rcases TermTyped.extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ | ⟨x1, a1, e1, lb, hterm, htl, rfl⟩
  · exact ⟨_, E, Tot, HP, set_self hth, (by rw [extSteps_n hs]; exact TermTyped.Flat.ThInvRE_extB hn1 hterm hev1 hrs1 hT), by rw [gOf_ext hs]; exact hm, hP,
      by rw [gOf_ext hs]; exact hb, hn, hsx, hle, hx, hA, by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc, hZ, hR⟩
  · obtain ⟨hbs, hbp⟩ := TermTyped.Flat.tidBox_extB hx (hTA th hth lb htl)
    exact ⟨_, E, Tot, HP, set_self (tr := c.trace) hth, (by rw [extSteps_n hs]; exact TermTyped.Flat.ThInvRE_curB hterm hbs hbp hT),
      by rw [gOf_ext hs]; exact hm, hP, by rw [gOf_ext hs]; exact hb, hn, hsx, hle, hx, hA,
      by rw [gOf_ext hs]; exact hTy, by rw [gOf_ext hs]; exact hRc, hZ, hR⟩
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:544 OwnXStepT
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepTBU (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 c0', ScopeAtB p i c0 → TermViewInv.ViewInv c0 → OwnXLeBU p k arch E0 i x n c0 →
    c0' ∈ threadSteps p k arch c0 i → Certified p k arch c0' i → OwnXLeBU p k arch E0 i x n c0'
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:549 OwnXStepP
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepPBU (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 a v w, OwnXLeBU p k arch E0 i x n c0 → w < c0.mem.size → Certified p k arch (promise c0 i a v w) i →
    OwnXLeBU p k arch E0 i x n (promise c0 i a v w)
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:591 OwnXStepPkg
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepPkgBU (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n q : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 c0' th, c0.ths[i]? = some th → exprPkg th.term = q →
    ScopeAtB p i c0 → TermViewInv.ViewInv c0 → OwnXLeBU p k arch E0 i x n c0 →
    c0' ∈ threadSteps p k arch c0 i → Certified p k arch c0' i → OwnXLeBU p k arch E0 i x n c0'
end
end TermOwnX2.Flat

-- PORTB TermOwnX2.lean:604 ownXStepT_of_pkgs
namespace TermOwnX2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepT_of_pkgsBU {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepPkgBU p k arch i x n 1) (h2 : OwnXStepPkgBU p k arch i x n 2)
    (h3 : OwnXStepPkgBU p k arch i x n 3) (h4 : OwnXStepPkgBU p k arch i x n 4) : OwnXStepTBU p k arch i x n := by
  intro E0 c0 c0' hsc hvI hI hs hc
  obtain ⟨th, hth⟩ := mem_threadSteps_th hs
  rcases exprPkg_cases th.term with e | e | e | e
  · exact h1 E0 c0 c0' th hth e hsc hvI hI hs hc
  · exact h2 E0 c0 c0' th hth e hsc hvI hI hs hc
  · exact h3 E0 c0 c0' th hth e hsc hvI hI hs hc
  · exact h4 E0 c0 c0' th hth e hsc hvI hI hs hc
end
end TermOwnX2.Flat

-- PORTB TermOwnHeldQ.lean:286 OwnXLeS
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXLeSBU (p : Prog) (g : G) (E0 : TEnv) (x : AllocLabel) (n : Nat) (mem : Memory) (pairs : List Ts)
    (th : TTh) : Prop :=
  ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E th Tot ∧ MemInvB g E (stOf mem pairs th) ∧ MemHeldPB E (stOf mem pairs th) HP ∧
    g.boxFence = true ∧ StoNIE E ∧ True ∧ Tot (.own x) + HP (.own x) ≤ n + bornBit x E ∧
    ExtB E0 E ∧ AnchR E0 E0 E (stOf mem pairs th) ∧ TyOKE g E ∧ RecFresh g g.i th.nalloc ∧ True ∧
    ((∀ l, E0.rini l ≤ E0.ini l) → ∀ l, E.rini l ≤ E.ini l)
end
end TermOwnHeldQ.Flat

-- ♭ MemInv_tys.
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem MemInvB_tysU (g : G) (t : AllocLabel → Option (Ty × Bool)) (E : TEnv) (s : St) :
    MemInvB { g with tys := t } E s ↔ MemInvB g E s := by
  unfold MemInvB; rw [BoxInv_tys]; exact Iff.rfl
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:294 OwnXStepL
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def OwnXStepLBU (p : Prog) (x : AllocLabel) (n : Nat) (T : Expr → Prop) : Prop :=
  ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh), g.p = p → 0 < g.n →
    T th.term → ∀ E0 : TEnv, ScopeOKB g.lbase g.n g.i p th →
    (∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts) → OwnXLeSBU p g E0 x n mem pairs th →
    r ∈ tstep g mem pairs th → PromAbove (stOf r.1 r.2.1 r.2.2) → PAx g mem pairs th →
    OwnXLeSBU p { g with tys := tysUpd g.tys th r.2.2 } E0 x n r.1 r.2.1 r.2.2
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:302 ownXStepPkg_of_local
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepPkg_of_localBU {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n q : Nat}
    (h : OwnXStepLBU p x n (fun t => exprPkg t = q)) : OwnXStepPkgBU p k arch i x n q := by
  intro E0 c0 c0' th hth hq hsc hvI hI hs hc
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨th1, E, Tot, HP, hth1, hT, hm, hP, hb, hni, hsx, hle, hx0, hA, hTy, hRc, hZ, hR⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hS := h (gOf p k arch c0 i) c0.mem c0.pairs th r rfl
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))) hq E0 (hsc th hth (TermTyped.not_spawnT_of_steps hth hs)) (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth)
    ⟨E, Tot, HP, hT, hm, hP, hb, hni, hsx, hle, hx0, hA, hTy, hRc, hZ, hR⟩ hr hpa (PAx_of_step hs hc hth)
  obtain ⟨E', Tot', HP', hT', hm', hP', hb', hni', hsx', hle', hx', hA', hTy', hRc', hZ', hR'⟩ := hS
  have hsub := TermTyped.tysOf_thread hs hth e3 hRc
  refine ⟨r.2.2, E', Tot', HP', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, ?_, hni', hsx', hle', hx', ?_, ?_, ?_, hZ', hR'⟩
  · rw [gOf_thread hs, e1, e2, MemInvB_tysU]; exact (MemInvB_tysU _ _ _ _).1 hm'
  · rw [e1, e2]; exact hP'
  · rw [gOf_thread hs]; exact hb'
  · rw [e1, e2]; exact hA'
  · rw [gOf_thread hs]; exact TyOKE_mono hsub hTy'
  · rw [gOf_thread hs]
    exact RecFresh_sub (g := { gOf p k arch c0 i with tys := tysUpd (gOf p k arch c0 i).tys th r.2.2 })
      (g' := { gOf p k arch c0 i with tys := tysOf c0' }) hsub rfl rfl hRc'
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:323 StepC
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def StepCBU (p : Prog) (g : G) (x : AllocLabel) (E : TEnv) (s : St) (th : TTh) (Tot0 HP0 : Res)
    (r : Memory × List Ts × TTh) : Prop :=
  ∃ E' Tot' HP', ThInvREB g.lbase g.n g.i p E' r.2.2 Tot' ∧ MemInvB g E' (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldPB E' (stOf r.1 r.2.1 r.2.2) HP' ∧ StoNIE E' ∧ BornMono x E E' ∧
    Tot' (.own x) + HP' (.own x) ≤ Tot0 (.own x) + HP0 (.own x) + bornInc x E E' ∧
    AnchStepB g th E E' s (stOf r.1 r.2.1 r.2.2) ∧
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E' ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc
end
end TermOwnHeldQ.Flat

-- ♭ mirrors of W TermOwnHeldQ StepCK / stepC_ofK.
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def StepCKBU (p : Prog) (g : G) (x : AllocLabel) (E : TEnv) (s : St) (th : TTh) (Tot0 HP0 : Res)
    (r : Memory × List Ts × TTh) : Prop :=
  ∃ Tot' HP', ThInvREB g.lbase g.n g.i p E r.2.2 Tot' ∧ MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧
    MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP' ∧ StoNIE E ∧ BornMono x E E ∧
    Tot' (.own x) + HP' (.own x) ≤ Tot0 (.own x) + HP0 (.own x) ∧
    AnchStepB g th E E s (stOf r.1 r.2.1 r.2.2)
theorem stepC_ofKBU {p : Prog} {g : G} {x : AllocLabel} {E : TEnv} {s : St} {th : TTh} {Tot0 HP0 : Res}
    {r : Memory × List Ts × TTh} (h : StepCKBU p g x E s th Tot0 HP0 r)
    (hk : TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc) :
    StepCBU p g x E s th Tot0 HP0 r :=
  let ⟨T', H', h1, h2, h3, h4, h5, h6, h7⟩ := h
  ⟨E, T', H', h1, h2, h3, h4, h5, Nat.le_trans h6 (Nat.le_add_right _ _), h7, hk.1, hk.2⟩
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnHeldQ.lean:331 ownXStepL_of
namespace TermOwnHeldQ.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_ofBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} {T : Expr → Prop}
    (h : ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh) (ρ : Nat → Nat)
      (η : TEnv) (cx : Cx) (Rf Rs HP : Res), g.p = p → 0 < g.n → T th.term → ScopeOKB g.lbase g.n g.i p th →
      EnvOKB p η → TypedK p η cx th.term → TvOK cx →
      FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf → RetPw th.σs th.stack cx.ret →
      DyFr p annNew (progTgts p) η th.σs th.term → MemInvB g (CE η) (stOf mem pairs th) →
      MemHeldPB (CE η) (stOf mem pairs th) HP → g.boxFence = true → StoNIE (CE η) → BornMono x (CE η) (CE η) →
      TyOKE g (CE η) → RecFresh g g.i th.nalloc →
      r ∈ tstep g mem pairs th → PromAbove (stOf r.1 r.2.1 r.2.2) → PAx g mem pairs th →
      StepCBU p g x (CE η) (stOf mem pairs th) th (Rf + Rs) HP r) :
    OwnXStepLBU p x n T := by
  intro g mem pairs th r hp hn ht E0 hsc hvr hS hr hpa hpx
  obtain ⟨E, Tot, HP, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hi, rfl, hRP, hDy⟩, hm, hP, hb, hni, hx, hle, hx0, hA, hTy, hRc, hZ, hR⟩ := hS
  obtain ⟨E', Tot', HP', h1, h2, h3, h0, h4, h5, h6, h7, h8⟩ :=
    h g mem pairs th r ρ η cx Rf Rs HP hp hn ht hsc hE hT htv hi hRP hDy hm hP hb hni (bornMono_refl x _) hTy hRc hr hpa hpx
  have hFp := finv_ofB htv hi
  obtain ⟨hx', hA'⟩ := h6.1 E0 hx0 hA hm.2.2.2.1.old h2 (wrHypB hE hT.1 htv hFp hm (hsc ρ η cx hE hT.1 htv hFp) hvr hr)
  refine ⟨E', Tot', HP', h1, (MemInvB_tysU _ _ _ _).2 h2, h3, hb, h0, trivial, bornBit_step hle h4 h5, hx', hA', h7, h8, trivial, fun h => h6.2.2 (hR h)⟩
end
end TermOwnHeldQ.Flat

-- PORTB TermOwnK1.lean:90 ownXStep_k1
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k1BU {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : ∀ n, OwnXStepPkgBU p k arch i x n 1 := by
  intro n E0 c0 c0' th hth hq hsc _ hI hs _
  obtain ⟨th0, E, Tot, HP, hth0, hT, hm, hHP, hb, hni, hsx, hle, hx0, hA, hTyE, hRc, hZ, hRl⟩ := hI
  obtain rfl : th0 = th := Option.some.inj (hth0.symm.trans hth)
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hTy, htv, hFI, hsum, hRP, hDy⟩ := hT
  subst hCE
  have hFI0 : FInvB c0.lbase c0.n i ρ η th0.σs (ResumeB c0.lbase c0.n i p th0.stack) cx th0.env :=
    FInvR_FInvB htv.2.2.2.2.2.2.2
      (fun E rd ws R h => ResumeR_ResumeB (fun _ h => h.2.2.2.2.2.2.2) th0.stack Rs E rd ws R h) hFI
  have hR := scopeR_of_pkg1 hTy.1 hq (hsc th0 hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hTy.1 htv hFI0)
  obtain ⟨th1, r, hth1, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  obtain rfl : th1 = th0 := Option.some.inj (hth1.symm.trans hth)
  obtain ⟨Tot', hT', hts⟩ := (tstepR_stepB (hDy := hDy) hP rfl (tstep_notDone hr) hR hTy.1 hTy.2 hFI hE
    (supI_of_memInvB hm (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (TermCert.arr_lt hth)))) htv hRP hPS hSub hSig).2 r hr
  obtain ⟨em, ep, hm'⟩ := frame_keepB hR hTy.1 hTy.2 hFI hE htv hm r hr
  have hg := gOf_thread hs
  have h0 := totStep_own_le hts x
  rw [hsum] at h0
  have hkeep := TermNallocF.tstep_tys_keep hr (fun x a T e h => by rw [h] at hq; simp [exprPkg, opPkg] at hq)
  have hsub : TysSub (tysOf c0') (gOf p k arch c0 i).tys := fun l u h => by
    have h1 := TermTyped.tysOf_thread hs hth e3 hRc l u h
    rwa [tysUpd_keep hkeep] at h1
  refine ⟨r.2.2, CE η, Tot', HP, e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, ?_, hni, hsx, by omega, hx0, ?_, ?_, ?_, hZ, hRl⟩
  · rw [hg, e1, e2]; exact hm'
  · rw [e1, e2]; exact memHeldOn_eqsB hHP em ep
  · rw [hg]; exact hb
  · rw [e1, e2]; exact anchR_eqs hA em ep
  · rw [hg]; exact TyOKE_mono (g := gOf p k arch c0 i) hsub hTyE
  · rw [hg]
    exact RecFresh_sub (g := gOf p k arch c0 i) (g' := { gOf p k arch c0 i with tys := tysOf c0' }) hsub rfl rfl
      (RecFresh_mono hRc (TermNallocF.tstep_nallocLe hr))
end
end TermOwnK1.Flat

-- PORTB TermOwnK1.lean:115 ownXStepP_all
namespace TermOwnK1.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepP_allBU {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} :
    ∀ n, OwnXStepPBU p k arch i x n := by
  intro n E0 c0 a v w h _ _
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hHP, hb, hni, hsx, hle, hx0, hA, hTyE, hRc, hZ, hR⟩ := h
  obtain ⟨-, h2, h3⟩ := promise_inv (a := a) (v := v) (w := w) hth
  refine ⟨_, E, Tot, HP, h2, (by rw [show (promise c0 i a v w).lbase = c0.lbase from congrArg G.lbase (gOf_promise (p := p) (k := k) (arch := arch)), promise_n]; exact hT), ?_, ?_, ?_, hni, hsx, hle, hx0, anchR_prom hth hA, ?_, ?_, hZ, hR⟩
  · rw [gOf_promise, h3]; exact MemInv_promStB hm
  · rw [h3]; exact memHeldP_promStB hHP
  · rw [gOf_promise]; exact hb
  · rw [gOf_promise]; exact hTyE
  · rw [gOf_promise]; exact hRc
end
end TermOwnK1.Flat

-- PORTB TermOwnK2.lean:24 stepC_keep
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepC_keepBU {p : Prog} {g : G} {η : TEnv} {th th1 : TTh} {s s' : St} {Rf Rs HP : Res} {z : AllocLabel}
    (hT : ThInvREB g.lbase g.n g.i p (CE η) (withS th1 s') (Rf + Rs)) (hm : MemInvB g (CE η) s')
    (hH : MemHeldPB (CE η) s HP) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises)
    (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) : StepCKBU p g z (CE η) s th (Rf + Rs) HP (s'.mem, s'.pairs, withS th1 s') :=
  ⟨Rf + Rs, HP, hT, hm, memHeldOn_eqsB hH e1 e2, hni, hx, Nat.le_refl _, anchStep_eqsB e1 e2⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:48 stepC_own
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepC_ownBU {p : Prog} {g : G} {η : TEnv} {r : Memory × List Ts × TTh} {Rf Rs Rr D HP : Res}
    {z : AllocLabel} {th : TTh} {s : St} (hnb : ∀ E1, BumpIf th E1) (hT : ThInvREB g.lbase g.n g.i p (CE η) r.2.2 (Rr + Rs)) (hm : MemInvB g (CE η) (stOf r.1 r.2.1 r.2.2))
    (hH : ∃ HP', MemHeldPB (CE η) (stOf r.1 r.2.1 r.2.2) HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + D (.own y))
    (hle : D (.own z) + Rr (.own z) ≤ Rf (.own z)) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) :
    StepCKBU p g z (CE η) s th (Rf + Rs) HP r := by
  obtain ⟨HP', hH', hle'⟩ := hH
  refine ⟨Rr + Rs, HP', hT, hm, hH', hni, hx, ?_, anchStep_sameB hnb⟩
  have h2 := hle' z
  simp only [Res.add_apply]
  omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:66 k2_loadOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadOwnBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hnwc : wordOf (close th.σs (.ptr .own u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv (bind_opaqueOK hb)
  have hwr : wordOf (Ty.ptr .own ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  have hvz : VRRB ρ η u (shp ru) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  exact stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:127 k2_loadLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .own u) = some (.own, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .own ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi0.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi0.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := acq)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (cell_lyt hl.2.2.2.2 rfl rfl).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have hvz : VRRB ρ η u (shp ru) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:203 k2_loadAt
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadAtBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.loadAt b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAt hp hbuf hint hlt hltk haf hb =>
  obtain ⟨t, u, n, k, j, hp, hbuf, hint, hlt, hltk, haf, hb⟩ : ∃ t u n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      affine cx.ke u = false ∧ cx.bind x u = .ok c' :=
    ⟨_, _, _, _, _, hp, hbuf, hint, hlt, hltk, haf, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, hini, hsku, hsig, htbS, -⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk (bind_opaqueOK hb)
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htbS (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ur, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have htb : tb cx.ke.length u = true := tb_bufOf (peek_tb htv hp) hbuf
  have hvz : VRRB ρ η u (shp ur) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:251 k2_loadAtF
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadAtFBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {q : List Nat} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.loadAtF b i q) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAtF hp hbuf hct hop hint hlt hltk haf hb =>
  obtain ⟨t, u, c, n, k, j, hp, hbuf, hct, hop, hint, hlt, hltk, haf, hb⟩ : ∃ t u c n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧ IntIdx cx i j ∧
      LtI cx j n ∧ LtI cx j k ∧ affine cx.ke c = false ∧ cx.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, haf, hb⟩
  have hi0 := hi.1
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, -, hsku, hsig, htbS, hiniF⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat' (hiniF o _ hato) hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) (tb_compTy q u c hct htbS) (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco))
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, cR, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, hco, hcs, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct (tb_bufOf (peek_tb htv hp) hbuf)
  have hvz : VRRB ρ η c (shp cR) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay
  rw [Res.add_zero] at hfr
  refine stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:302 k2_loadPub
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadPubBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hnwc : wordOf (close th.σs (.ptr .pub u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk (bind_opaqueOK hb) hi0 hE htv hm
  have hwr : wordOf (Ty.ptr .pub ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay', hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame us 0 _ (s', wsr) hl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  have hvz : VRRB ρ η u (shp ru) wsr .zero := VR_VRR_copy_finvB hi0 hE haf htb hvr
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay'
  rw [Res.add_zero] at hfr
  exact stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm' hH f1 f3 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:360 k2_loadPubLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadPubLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadPub hp _ hc haf _ hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.pub, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .pub u) = some (.pub, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi0.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi0.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi0.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  by_cases hown : c.owner = some η.tid
  · 
    obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadIB (arch := g.arch) (pw := pw) (acq := acq)
      (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.1 hsto hown hat hini hna
      (fun hnr f hf hns => by
        simp only [ModeOKF, ModeOKb] at hmode
        obtain ⟨f0, hf0, hsf⟩ := hmode
        obtain rfl : f0 = f := Option.some.inj (hf0.symm.trans hf)
        rcases hsf with hs | hs
        · exact absurd hs hns
        · rcases hs with hs | ⟨hso, hs⟩
          · exact hs pw (by simp)
          · first | exact hs.elim | exact absurd hso hown | exact absurd hs hnr | (rcases hs with hs | hs <;> first | exact hs.elim | exact absurd hs hnr)) hsku hsig
        (cell_lyt hl.2.2.2.2 rfl rfl).2
          (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨hvr, hlay', f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
    have hvz := VR_VRR_copy_finvB hi0 hE haf htb hvr
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay'
    rw [Res.add_zero] at hfr
    exact stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
      (MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')) hH f1 f4 hni hx
  · 
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, hsf⟩ := hmode
    have hfv : f ≤ pw.view := by
      rcases hsf with hs | hs
      · rcases hm.2.2.2.2.2.2.2.2.1.1 ad.label hs with ⟨c0, h1, h2⟩ | ⟨h1, -⟩
        · refine absurd ?_ hown
          have h1' : η.sto ad.label = some c0 := h1
          rw [hsto] at h1'
          rw [Option.some.inj h1']; exact h2
        · have h1' : η.sto ad.label = none := h1
          rw [hsto] at h1'; cases h1'
      · rcases hs with hs | ⟨hso, -⟩
        · exact hs pw (by simp)
        · exact absurd hso hown
    have hlU : accs (cl ρ η.wit 0 0 u) ≠ none := by
      rcases AtOff_lay hat with h | ⟨N, e', h, -⟩
      · exact h
      · exact absurd h (hna N e')
    have hlr := pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl
    obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := Option.ne_none_iff_exists'.1 (by rw [hlr]; exact hlU)
    have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
    have key : tstep g mem pairs th =
        (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
    rw [key] at ⊢
    obtain ⟨⟨r0, hr0⟩, hval, hsv⟩ := pubLoadAtB (arch := g.arch) (pw := pw) (acq := acq)
      hm.2.2.2.2.2.2.2.2.1 hm.2.2.2.2.2.2.1 hsto hown hf hfv hat hini hna husU
    intro r hr hpr0
    rw [List.mem_map] at hr
    obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
    obtain ⟨q, hq, hle⟩ := hval (s', wsr) hl' (hpr0)
    have hrl : wsr.length = nWords us := (Reads_unit us 0 wsr (loadUnits_reads us 0 _ (s', wsr) hl' [] (fun _ _ h => by cases h))).1
    obtain ⟨f1, f2, f3, f4⟩ := loadUnits_frame us 0 _ (s', wsr) hl'
    obtain ⟨hvr0, hV0⟩ := ValOfB.env hq
    have hvr : (VRF False) ρ η u (shp ru) wsr := by
      rw [shp_of_sig hsig]
      exact (VR_closeB hE.2.1 ρ u [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 u)) wsr (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 (VR_upB (bkG := False) _ _ q wsr hle hvr0)
    have hlay' : Lay th.σs u ru wsr :=
      ⟨fun us' h => by rw [hus] at h; cases h; exact hrl, hsku, by simp [wc, hus],
        Valid_of_sig hsig.symm (Valid_vals _ q wsr hle.vals hV0), (cell_lyt hl.2.2.2.2 rfl rfl).2⟩
    have hvz := VR_VRR_copy_finvB hi0 hE haf htb hvr
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvz hlay'
    rw [Res.add_zero] at hfr
    refine stepC_keepBU ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
      ?_ hH f1 f3 hni hx
    refine MemInv_loadFB hm f1 f2 (fun l c1 hc1 ho1 o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ ?_)
      f3 f4 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')
      (fun l B hB o => loadUnits_cohF us 0 _ (s', wsr) hl' ⟨l, o⟩ (fun he => by
        have h0 := (hm.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1
        have hl0 : l = ad.label := he
        rw [hl0] at h0; have h1 : η.sto ad.label = none := h0; rw [hsto] at h1; cases h1))
    intro hle'
    have hl'' : l = ad.label := hle'
    have h1 : η.sto l = some c1 := hc1
    rw [hl'', hsto] at h1
    exact hown (by rw [Option.some.inj h1]; exact ho1)
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:503 k2_loadWordOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadWordOwnBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P)))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi0 hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  have hfr := bindR0B hb (pushRB x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keepBU ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    ((MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl))) hH f1 f4 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:551 k2_loadWordPub
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadWordPubBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P)))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk
      (by simp [Cx.opaqueOK, Ty.guardT]) hi0 hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame us 0 _ (s', wsr) hl
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  have hfr := bindR0B hb (pushRB x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keepBU ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm' hH f1 f3 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:595 k2_loadWordLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_loadWordLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  have hg' : P.ghost = false := hg
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg']
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs)
      hpk hμ (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi0 hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, haddr, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  intro r0 hr hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.one] 0 _ (s', wsr) hl
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg' hvr
  have hfr := bindR0B hb (pushRB x n hi) hvr' (Lay_int w rfl) trivial
  exact stepC_keepBU ⟨vcons n ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm' hH f1 f3 hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:644 k2_storeOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeOwnBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have hvalR : EnvValRB (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRRB ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_subB hsat hsub _ _ _ hvrv
    have hvc : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRRB η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine stepC_ownBU (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩ (MemInv_storeB hm hsto hown husA hval hlen s' hs')
    (privStoreB hH hm.2.2.1 hs' fun hq R0 _ => ?_) (own_le hle z) hni hx
  obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
    (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodupB hm) (Nat.le_refl _) s' hs'
  have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
    have := OwnOKPF_tailB hm.2.1 hsto hown hq.2 hus' j hj
    simpa [offs] using this
  exact ⟨Rv, HeldEntry_ownNB hsto (NVP_store (NVP_priv hq) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
    (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩), fun y => Nat.le_add_left _ _⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:727 k2_storeLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi0 hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine stepC_ownBU (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (MemInv_storeAtB hm hsto hown hat hini hna hval hwUA hlen s' hs') ?_ (own_le hle z) hni hx
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := heldStoreAtPB hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) hat hini hna hvalR hwU hlen
    refine ⟨R2 + H0, hput g.k g.arch pw rel _ rfl rfl (LoadCoh_of_eqB hm.2.1 rfl) (fun _ => Nat.le_refl _)
      hm.2.2.2.2.1 s' hs', fun y => ?_⟩
    have h2 := congrArg (fun R : Res => R (.own y)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · exact ⟨HP, memHeldOn_storeB hH (fun l h e => hq (e ▸ h)) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:802 k2_storePub
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storePubBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hlr : accs ru = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    cases h : accs ru with
    | none => rw [h] at hlr; exact absurd hlr.symm hacc
    | some us => exact ⟨us, rfl⟩
  have husc : accs c.ty = some us := by rw [← hlr, hus]
  have hus' : wc c.ty = some (nWords us) := by simp [wc, husc]
  have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValRB (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRRB ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_subB hsat hsub _ _ _ hvrv
    have hvc : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRRB η hcty).2 hvc
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hsn := hm.2.2.2.2.1
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  by_cases hown : c.owner = some η.tid
  · refine stepC_ownBU (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩ (MemInv_storeFB hm hsto hown husc hval hlen s' hs')
      (privStoreB hH hm.2.2.1 hs' fun hq R0 _ => ?_) (own_le hle z) hni hx
    obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 (stOf mem pairs th)
      (stOf mem pairs th).vs.vRelSt hm.2.2.1 (MemInv_nodupB hm) (Nat.le_refl _) s' hs'
    have htail : ∀ j : Nat, j < nWords us → TailP (stOf mem pairs th) (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
      have := OwnOKPF_tailB hm.2.1 hsto hown hq.2 hus' j hj
      simpa [offs] using this
    exact ⟨Rv, HeldEntry_ownNB hsto (NVP_store (NVP_priv hq) hm.2.2.1 hs') (storeOwn_latestP hlen (g2 htail))
      (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hsn⟩), fun y => Nat.le_add_left _ _⟩
  · refine stepC_ownBU (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
      (MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs')
      ⟨HP, memHeldOn_storeB hH (fun l h e => ?_) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩ (own_le hle z) hni hx
    obtain ⟨⟨c2, h2, ho⟩, -⟩ := h
    have h3 : η.sto lab = some c2 := by rw [e] at h2; exact h2
    rw [hsto] at h3; cases h3; exact hown ho
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:894 k2_storePubLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storePubLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storePub hp _ hc hwf hu hsub _ hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.pub, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .pub u) = some (.pub, u)) (Fd_noarr fun h => hwcu (by simp [wc, h])) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .pub ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact hsigu
  have hlr := pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have husU : accs (cl ρ η.wit 0 0 u) = some us := by rw [← hlr, hus]
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := hlr.symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  simp only [ModeOKF, ModeOKb] at hmode
  obtain ⟨f, hf, -⟩ := hmode
  refine stepC_ownBU (bumpIf_nb hterm) ⟨ρ, η, c', Rr, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    (by by_cases hown : c.owner = some η.tid
        · exact MemInv_storeAtIB hm hsto hown hat hini hna hval hwUA hlen s' hs'
        · exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval husU hlen s' hs')
    ⟨HP, memHeldOn_storeB hH (fun l h e => ?_) hm.2.2.1 hs', fun y => Nat.le_add_right _ _⟩ (own_le hle z) hni hx
  have h3 : η.pfr ad.label = none := by rw [← e]; exact h.2
  rw [hf] at h3; cases h3
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:998 k2_xchgOwn
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_xchgOwnBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hxz : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi0 hpk htv ho
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, -, hld, -⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1)
  have hvalR : EnvValRB (CE η) c.ty wsv Rv := by
    obtain ⟨hs, -⟩ := Lay_canon hsub hlv
    have hvu : VRRB ρ η u (shp (close th.σs u)) wsv Rv := by rw [← hs]; exact VRR_subB hsat hsub _ _ _ hvrv
    have hvc : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) wsv Rv := by
      rw [← shp_of_sig hsigu]
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp (close th.σs u)) wsv Rv (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu
    refine ⟨?_, hval.2⟩
    rw [(Fd_lay hcty).1]
    exact (Fd_VRRB η hcty).2 hvc
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInvB g (CE η) r1.1 :=
    fun r1 h hp => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  by_cases hq : Priv (CE η) lab
  · have hnv := NVP_priv (s := stOf mem pairs th) hq
    obtain ⟨vals, hcell, hlat⟩ := OwnOKPF_cellPB hm.2.1 hsto hown hq.2
    have hwc := (hcell.plain (notArr_of_wc hus')).1
    obtain ⟨vals', hWv, hP'⟩ := own_msgWordsN (E := CE η) hnv vals hlat
    have hl' : vals'.length = nWords us := by
      rw [← hWv.length]; rw [hus'] at hwc; exact (Option.some.inj hwc).symm
    obtain ⟨R0, H0, rfl, hent0, hX⟩ := memHeldOn_focusB hH hq
    have hvR0 : ValOfRB (CE η) c.ty vals' R0 :=
      HeldEntry_valsB hent0 hsto hna (by rw [hus', hl']) (fun o w h => (hP' o w h).2)
    have hWold : WLe vals' old := (loadUnits_latestPA hl'
      (fun j w hj => by simpa [offs] using (hP' j w hj).1) h1 hp1).1
    have hvold : VRRB ρ η u (shp ru) old R0 := by
      have h1 := VRR_upB _ _ _ _ _ hWold hvR0.1
      have h2 : VRRB (fun _ => 0) (CE η) c.ty (shp c.ty) old R0 :=
        VRR_monoB c.ty (CE (CE η).unsee) (CE η) _ _ _ _ (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) rfl rfl rfl (fun _ _ h => h)
          (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h1
      have h3 := (Fd_VRRB η hcty).1 h2
      rw [(Fd_lay hcty).1, ← shp_of_sig hsig] at h3
      exact (VRR_closeB hE.2.1 hE.2.2 ρ u [] 0 ρ (fun _ => 0) (shp ru) old R0 (fun k => rfl)
        (fun k hk => absurd hk (Nat.not_lt_zero _))).2 h3
    obtain ⟨g2, -⟩ := storeUnits_latP (a := ⟨lab, 0⟩) us wsv 0 s1 s1.vs.vRelSt hm1'.2.2.1
      hm1'.2.2.2.2.2.2.2.2.2.2.1 (Nat.le_refl _) s2 hs2
    have htail : ∀ j : Nat, j < nWords us → TailP s1 (offs ⟨lab, 0⟩ (0 + j)) := fun j hj => by
      have := cellP_tailLoadB (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) fc (loadUnits_cohMono us 0 _ _ h1) f1 f3
        hsto hown hus' j hj
      simpa [offs] using this
    have hent : HeldEntryB (CE η) s2 lab Rv := HeldEntry_ownNB hsto (NVP_store (NVP_eqs hnv f1 f3) hm1'.2.2.1 hs2)
      (storeOwn_latestP hlen (g2 htail))
      (Or.inl ⟨by rw [hus', List.length_map, hlen], hvalR.store hm1'.2.2.2.2.1⟩)
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + R0 + Rs, Rv + H0, ⟨ρ, η, c', Rr + R0, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeB hm1' hsto hown husA hval hlen s2 hs2,
      memHeldOn_unfocusB (memHeldOn_storeB (memHeldOn_eqsB hX f1 f3) (fun l h => h.2) hm1'.2.2.1 hs2) hent hq, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    simp only [Res.add_apply]; omega
  · obtain ⟨f, hf⟩ : ∃ f, (CE η).pfr lab = some f := by
      cases h : (CE η).pfr lab with
      | none => exact absurd ⟨⟨c, hsto, hown⟩, h⟩ hq
      | some f => exact ⟨f, rfl⟩
    obtain ⟨R1, hvold, hz⟩ := oldFreeB (T := c.ty) hE.2.1 hE.2.2 (fun S ws => (Fd_VRB η hcty).2) (fun S ws R => (Fd_VRRB η hcty).1)
      (hni lab c hsto) (MemInv_noOwnTB hm hsto hf) hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + R1 + Rs, HP, ⟨ρ, η, c', Rr + R1, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeB hm1' hsto hown husA hval hlen s2 hs2,
      memHeldOn_storeB (memHeldOn_eqsB hH f1 f3) (fun l h e => hq (by rw [e] at h; exact h)) hm1'.2.2.1 hs2, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := hz z
    simp only [Res.add_apply]; omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1128 k2_xchgLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_xchgLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hxz : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hi0 := hi.1
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig (sig_WitL hi0.2.2.2.1 ρ ho (lt_of_guardT htb hi0.2.2.2.2.1))]
    exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi0 hpk htv ho hwcu
  obtain ⟨us, hus, -, hld, -⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_cell_lytB hi0.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInvB g (CE η) r1.1 :=
    fun r1 h hp => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput⟩ := heldStoreAtPB hm hH hq hsto hown (NVP_priv hq)
      (OwnOKPF_cellPB hm.2.1 hsto hown hq.2) hat hini hna hvalR hwU hlen
    have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
    have hvold := oldValRB hE.2.1 hE.2.2 hsig (VRR_upB _ _ _ _ _ hWold hvqR)
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      hput g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := congrArg (fun R : Res => R (.own z)) hRe
    simp only [Res.add_apply] at h2 ⊢; omega
  · obtain ⟨f, hf⟩ : ∃ f, (CE η).pfr ad.label = some f := by
      cases h : (CE η).pfr ad.label with
      | none => exact absurd ⟨⟨c, hsto, hown⟩, h⟩ hq
      | some f => exact ⟨f, rfl⟩
    obtain ⟨R1, hvold, hz⟩ := oldFreeB (T := (cl ρ η.wit 0 0 u)) hE.2.1 hE.2.2 (fun _ _ h => h) (fun _ _ _ h => h)
      (TermPlant.noIallV_AtOffP hat (hni _ c hsto)) (noOwn_AtOff hat (MemInv_noOwnTB hm hsto hf)) hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + R1 + Rs, HP, ⟨ρ, η, c', Rr + R1, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      memHeldOn_storeB (memHeldOn_eqsB hH f1 f3) (fun l h e => hq (by rw [e] at h; exact h)) hm1'.2.2.1 hs2, hni, hxz, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := own_le hle z
    have h2 := hz z
    simp only [Res.add_apply]; omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1257 k2_wordFin
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_wordFinBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {e : Expr}
    {pw w : Word} {A : Address} {n : Nat} {P : Proto} {Rf Rs HP Tf Rv : Res} {z : AllocLabel}
    (hkey : tstep g mem pairs th = (storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s'))
    (hnb : ∀ E1, BumpIf th E1)
    (hmi : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th) → MemInvB g (CE η) s')
    (hHP : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.one] [w] 0 (stOf mem pairs th) →
      ∃ HP', MemHeldPB (CE η) s' HP' ∧ ∀ y : Nat, HP' (.own y) ≤ HP (.own y) + (Rv + wdW P n) (.own y))
    (hv : VRRB (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [w] (Rv + wdW P n))
    (hfr : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .unit, []) :: th.env) Tf) (hle : Tf + Rv ≤ Rf)
    (hE : EnvOKB p η) (he : TypedK p η c' e) (htv' : TvOK c') (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hkey]
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hz := TermBlkZ.Flat.VRR_own_zeroB z (.word (.lit n) P) [] (CE (CE η).unsee) (fun _ => 0) _ [w] _ (by simp [Ty.noOwnIn]) (fun _ _ _ _ h => h.elim)
    (fun _ _ _ _ h => h.elim) hv
  refine stepC_ownBU hnb ⟨ρ, η, c', Tf, Rs, rfl, hE, he, htv', hfr, rfl, hRPc, hDy.wit rfl⟩ (hmi s' hs') (hHP s' hs') ?_ hni hx
  have h1 := own_le hle z
  rw [hz]; omega
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1281 k2_storeWordPtr
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordPtrBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hr : EqI c₁ r r') (hj : IntIdx c₁ v j)
    (hst : InState c₁ P j c₂ k') (hcl : P.clauses[c₂]? = some cl') (hxt : StoreKind xt r' P j cl')
    (hb : c₁.bind x xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi.1
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hcellW : ∀ {lab : AllocLabel} {c : Cell}, Fd c.ty (cl ρ η.wit 0 0 (.word r P)) →
      c.ty = .word (.lit (ev ρ r)) P := fun hcty => by
    have h' := hcty; simp only [cl, clI_zero] at h'; exact Fd_word_eq h'
  have hpwf := wordRef_pwfB hpk (Or.inl rfl) hμ hi.1 hE htv hm
  rcases hμ with rfl | rfl
  · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, -, hown, hsku, -⟩ := ownPtr_viewB hi.1 hpk htv ho
    have hct := hcellW (lab := lab) hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs, hg]))
    obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
      storeWord_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
    have husA : accs c.ty = some [Acc.one] := by rw [hct]; simp [accs, hg]
    have hus' : wc c.ty = some (nWords [Acc.one]) := by rw [hct]; simp [wc, accs, hg]
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    exact k2_wordFinBU (hDy := hDy.letW hterm rfl) key (bumpIf_nb hterm) (fun s' hs' => MemInv_storeB hm hsto hown husA hval rfl s' hs')
      (privStoreAtB hm hH hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h)
        (fun N e h => by cases h) (wordValRB (hvR _ _) (by rw [← hct]; exact hval.2)) (by simp [wc, accs, hg]) rfl) (hvR _ _) hfr hle hE he htv' hni hx hRPc
  · obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, -, hsku, -⟩ := pubPtr_viewB hi.1 hpk htv ho
    have hct := hcellW (lab := lab) hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs, hg]))
    obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
      storeWord_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
    have husc : accs c.ty = some [.one] := by rw [hct]; simp [accs, hg]
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
    refine k2_wordFinBU (hDy := hDy.letW hterm rfl) key (bumpIf_nb hterm) (fun s' hs' => ?_)
      (privStoreAtB hm hH hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h)
        (fun N e h => by cases h) (wordValRB (hvR _ _) (by rw [← hct]; exact hval.2)) (by simp [wc, accs, hg]) rfl) (hvR _ _) hfr hle hE he htv' hni hx hRPc
    by_cases hown : c.owner = some η.tid
    · exact MemInv_storeFB hm hsto hown husc hval rfl s' hs'
    · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
      exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc rfl s' hs'
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1343 k2_storeWordLocC
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordLocCBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause}
    {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hr : EqI c₁ r r') (hj : IntIdx c₁ v j)
    (hst : InState c₁ P j c₂ k') (hcl : P.clauses[c₂]? = some cl') (hxt : StoreKind xt r' P j cl')
    (hb : c₁.bind x xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hi0 := hi.1
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi0
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
  have hcell : cellOf (Ty.loc μ (.word r P)) = some (μ, .word r P) := by simp [cellOf]
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ := cell_targetB (bkG := False) hcell (Fd_noarr (by rw [hus1]; simp)) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, -⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs (.word r P))) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hlr := pub_accsB hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk hcell ho hea rfl
  have hus : accs ru = some [.one] := by rw [hlr, hus1]
  have hat' : AtOff c.ty ad.offset (.word (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero] using hat
  have hpwf := wordRef_pwfB hpk (Or.inr rfl) hμ hi.1 hE htv hm
  obtain ⟨rt, w, Tf, Rv, hev, hwv, hfr, hle, hvR⟩ :=
    storeWord_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hg hu hr hj hst hcl hb hxt
  have hval := storeWord_valB (η := η) (r := r) hpwf hi1.1 hst hwv
  have hna : ∀ N e, cl ρ η.wit 0 0 (.word r P) ≠ .array (.lit N) e := fun N e h => by simp [cl] at h
  have hwUA : accs (cl ρ η.wit 0 0 (.word r P)) = some [Acc.one] := hus1
  have hwU : wc (cl ρ η.wit 0 0 (.word r P)) = some (nWords [Acc.one]) := by simp [wc, hus1]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  refine k2_wordFinBU (hDy := hDy.letW hterm rfl) key (bumpIf_nb hterm) (fun s' hs' => ?_) (privStoreAtB hm hH hsto hat' (fun hq => by
      rcases hμ with rfl | rfl
      · have h4 : IniAt η.rc c ad (.word (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero, modeIni_own_rc] using hini
        exact h4
      · simp only [ModeOKF, ModeOKb] at hmode
        obtain ⟨f, hf, -⟩ := hmode
        have h3 : η.pfr ad.label = none := hq.2
        rw [hf] at h3; cases h3) (fun N e h => by cases h)
    (wordValRB (hvR _ _) (by simpa only [cl, clI_zero] using hval.2)) (by simp [wc, accs, hg]) rfl)
    (hvR _ _) hfr hle hE he htv' hni hx hRPc
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtIB hm hsto hown hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hna hval hwUA rfl s' hs'
  · have hpub : μ = .pub := by
      rcases hμ with rfl | rfl
      · exact absurd hmode hown
      · rfl
    subst hpub
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval hus1 rfl s' hs'
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1406 k2_storeWord
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtrBU (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordHand hp hw hu hr hj _ _ hst hcl _ _ hh _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtrBU (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inl ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordKeep hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordPtrBU (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inr ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1441 k2_storeWordLoc
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordLocBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocCBU (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordHand hp hw hu hr hj _ _ hst hcl _ _ hh _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocCBU (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inl ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | storeWordKeep hp hw hu hr hj _ _ hst hcl _ _ hh _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact k2_storeWordLocCBU (hDy := hDy) hterm hpk hμ hg hu hr hj hst hcl (Or.inr (Or.inr ⟨rfl, hh⟩)) hb ⟨he, hck⟩ htv' hi hE htv hm hH hni hx (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1476 k2_storeWordGhost
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordGhostBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  obtain ⟨rt, pw, b, μ', ru, hea, hc, hab, hus⟩ := ghostRefKB hpk ht hμ hg hi.1 hE htv
  have hnw : wordOf t ≠ none := by rcases ht with rfl | rfl <;> simp [wordOf]
  have hT0 := hT
  have hCk0 := hCk
  rw [hterm] at hT0 hCk0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk0
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  have fin : ∀ {Tf : Res}, FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, .unit, []) :: th.env) Tf →
      Tf ≤ Rf → (∃ rv w, evalAt th.env v = some (rv, [w])) →
      ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
    intro Tf hfr hle hevx
    obtain ⟨rv, w, hev⟩ := hevx
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .unit, []) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hea, hev, hc, hab, hus, storeUnits, List.map]
    rw [key]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    refine ⟨Tf + Rs, HP, ⟨ρ, η, c', Tf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm, hH, hni, hx, ?_,
      anchStep_eqsB rfl rfl⟩
    have h1 := (Res.le_def.1 hle) (.own z)
    simp only [Res.add_apply] at h1 ⊢
    omega
  have hL := RLink_ofB hE.2.1 hE.2.2
  cases hop with
  | storeOwn hp hnw' | storePub hp hnw' | storeRgn hp hnw' | storeCap hp hnw' =>
    exfalso; rw [hpk] at hp; cases hp; exact hnw hnw'
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    obtain ⟨-, -, Rt, Rr, -, -, -, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have hfr := bindRB hb hi1 hL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    exact fin hfr (Res.le_def.2 fun k => by
      have := (Res.le_def.1 hle) k; simp only [Res.add_apply] at this; omega) ⟨rv, w, hev⟩
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    obtain ⟨-, -, Rt, Rr, -, -, -, -, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have hfr := bindRB hb hi1 hL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    exact fin hfr (Res.le_def.2 fun k => by
      have := (Res.le_def.1 hle) k; simp only [Res.add_apply] at this; omega) ⟨rv, w, hev⟩
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    obtain ⟨rt0, ws0, Rt, Rr, hev0, hv0, hl0, hvt, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
    simp only [VRRB] at hvt
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.1.2.1 htvk hio
    have hfr := bindRB (R := Rt) (rt := .unit) (ws := []) hb hi1 hL (by simp only [VRRB]; exact hvt) (tok_Lay _ _ _ _)
    exact fin hfr (by rw [Res.add_comm]; exact hle) ⟨rv, w, hev⟩
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1544 k2_storeWordAny
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_storeWordAnyBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  cases hg : P.ghost
  · rcases ht with rfl | rfl
    · exact k2_storeWordBU (hDy := hDy) hterm hP hpk hμ hg hT hCk hi hE htv hm hH hni hx hRP
    · exact k2_storeWordLocBU (hDy := hDy) hterm hP hpk hμ hg hT hCk hi hE htv hm hH hni hx hRP
  · exact k2_storeWordGhostBU (hDy := hDy) hterm hP hpk ht hμ hg hT hCk hi hE htv hm hH hni hx hRP hPS
end
end TermOwnK2.Flat

-- ♭ mirror of W TermOwnK2 k2_isTy.
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem k2_isTyBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {τ : Ty} {e : Expr} {Rf Rs HP : Res} {z : AllocLabel}
    (hterm : th.term = .let_ x (.isTy a τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term)
    (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hni : StoNIE (CE η)) (hx : BornMono z (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, StepCKBU p g z (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | isTy hpk hsl hwf htg _ hb =>
  obtain ⟨rt, ws, hea, hvr0, hlay0⟩ := peek_VRB (bkG := False) hi.1.2.1 hpk
  obtain ⟨pw, ad, cl0, hlast, hpv, ho, hsto, hmo, hacc⟩ := slot_wordB hsl hvr0 hlay0.2.2.1
  obtain ⟨w, hw, hk⟩ := isTy_key (g := g) (mem := mem) (pairs := pairs) hterm hea hlast hpv (close_wf0 th.σs hwf)
  rw [hk]
  intro r0 hr
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : VRRB ρ η (.ptrOpt .pub τ) (shp (.ptrOpt .pub (close th.σs τ))) [w] (ownW .pub [w]) :=
    ⟨isTy_valB htg hTy hpv ho hsto hmo hacc hw, rfl⟩
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) hvr (isTy_lay (isTy_null_or hpv hw))
  rw [ownW_pub, Res.add_zero] at hfr
  exact stepC_keepBU (s' := stOf mem pairs th)
    ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    hm hH rfl rfl hni hx
end
end TermOwnK2.Flat

-- PORTB TermOwnK2.lean:1570 ownXStep_k2
namespace TermOwnK2.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k2BU [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} [ProgRetIall p]
    (hP : ProgT p) (hPS : PwSkel) : ∀ n, OwnXStepPkgBU p k arch i x n 2 := fun n =>
  ownXStepPkg_of_localBU (ownXStepL_ofBU (fun g mem pairs th r ρ η cx Rf Rs HP _ _ hq hsc hE hT htv hi hRP hDy hm hH _ hni hxz
      hTyE hRc hr hpa _ => by
    have hq : exprPkg th.term = 2 := hq
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [h] at hq; simp [exprPkg, opPkg] at hq) hTyE hRc)
    have hsd := hsc ρ η cx hE hT.1 htv (finvK2B htv hi)
    have hT0 := hT.1
    generalize ht : th.term = t0 at hT0 hsd hq
    have hsc' : StepScope cx t0 := by
      rcases hsd with h | ⟨-, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals (subst h; simp [exprPkg, opPkg] at hq)
    cases hT0 with
    | let_ hop _ =>
      cases hop with
      | loadWord hpk hw =>
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact k2_loadWordOwnBU (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | pub => exact k2_loadWordPubBU (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | rgn r' => exact ((hsc' _ hpk) r' _ rfl).elim
        · cases μ with
          | own => exact k2_loadWordLocBU (hDy := hDy) ht hP hpk (.inl rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | pub => exact k2_loadWordLocBU (hDy := hDy) ht hP hpk (.inr rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          | rgn r' => exact ((hsc' _ hpk) r' _ rfl).elim
      | storeWordGive hpk hw | storeWordKeep hpk hw | storeWordHand hpk hw =>
        obtain ⟨μ, hteq⟩ := wordOf_cases hw
        cases μ with
        | own => exact k2_storeWordAnyBU (hDy := hDy) ht hP hpk hteq (.inl rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        | pub => exact k2_storeWordAnyBU (hDy := hDy) ht hP hpk hteq (.inr rfl) hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        | rgn r' => rcases hteq with rfl | rfl <;> exact ((hsc' _ hpk) r' _ rfl).elim
      | loadRgn hpk _ hc | loadCap hpk _ hc | loadTorn hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
      | storeRgn hpk _ hc | storeCap hpk _ hc => exact absurd hc (hsc' _ hpk _ _)
      | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_loadOwnBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        · exact k2_loadLocBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_loadPubBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        · exact k2_loadPubLocBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | storeOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_storeOwnBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        · exact k2_storeLocBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
      | storePub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact k2_storePubBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
        · exact k2_storePubLocBU (hDy := hDy) ht hP hpk hnw hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr
      | xchg hpk hx =>
        cases hx with
        | own _ hc =>
          rcases cell_cases hc with rfl | rfl
          · exact k2_xchgOwnBU (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
          · exact k2_xchgLocBU (hDy := hDy) ht hP hpk hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
        | rgn _ hc => exact absurd hc (hsc' _ hpk _ _)
      | loadAt => exact k2_loadAtBU (hDy := hDy) ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | loadAtF => exact k2_loadAtFBU (hDy := hDy) ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS r hr hpa
      | isTy => exact k2_isTyBU (hDy := hDy) ht hP hT.1 hT.2 hi hE htv hm hH hni hxz hRP hPS hTyE r hr
      | _ => simp [exprPkg, opPkg] at hq
    | _ => simp [exprPkg] at hq))
end
end TermOwnK2.Flat

-- PORTB TermOwnK3.lean:43 stepK3_ldl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_ldlBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.ldl b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hx : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk hb =>
  obtain ⟨t, u, n, k, j, q, hp, hbuf, hlo, hint, hlt, hltk, hb⟩ : ∃ t u n k j q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧ cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).filterMap
        fun (s1, old) => (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (ev ρ j % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hni, addrOf, hwv, hbe, lanesOf]
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv',
    bindR0B hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _) trivial, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1),
    memHeldOn_eqsB hH f1 f4, hnie, hx, Nat.le_refl _, anchStep_sameB (bumpIf_nb hterm)⟩
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:115 stepK3_ldlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_ldlwBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.ldlw b wi jl) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hx : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have hi0 := hi.1
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk hpj hij hb =>
  obtain ⟨t, u, n, k, jw, tj, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩ : ∃ t u n k jw tj q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi0.2.1 hpj hoj
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).filterMap fun (s1, old) =>
        (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (m % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hni, hnj, addrOf, hwv, hbe, lanesOf]
  
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv',
    bindR0B hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _) trivial, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1),
    memHeldOn_eqsB hH f1 f4, hnie, hx, Nat.le_refl _, anchStep_sameB (bumpIf_nb hterm)⟩
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:188 stepK3_xchgAt
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_xchgAtBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.xchgAt b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, n, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x u = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    obtain ⟨Ro, hvold, hRo⟩ := oldValFB hE.2.1 hE.2.2 (hnie _ _ hsto) (MemInv_noOwnTB hm hsto hpfN) hat hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + Ro + Rs, HP, ⟨ρ, η, c', Rr + Ro, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us))) hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ j * nWords us)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := hle (.own xl)
    have h3 := hRo xl
    simp only [Res.add_apply] at h1 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hown hpfN)
  obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput0⟩ := heldStoreAtPB (a := offs ad (ev ρ j * nWords us)) hm hH (Priv_of hsto hown hpfN) hsto hown hnv (OwnOKPF_cellPB hm.2.1 hsto hown hpfN) hat hini hna hvalR hwU hlen
  have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
  have hvold := oldValRB hE.2.1 hE.2.2 hsig (VRR_upB _ _ _ _ _ hWold hvqR)
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
  refine ⟨Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us))) hm1' hsto hown hat hini hna hval hwUA hlen s2 hs2,
    hput0 g.k g.arch w false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h1 := hle (.own xl)
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply] at h1 h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:280 stepK3_xchgAtF
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_xchgAtFBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {q : List Nat} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, c, n, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u c n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c ∧ c₁.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩
  have hi0 := hi.1
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, hiniF⟩ :=
    slot_viewB (bkG := False) hi0.1 hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi0.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hiniC := hiniF o _ hato
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have hsat : Sat c₁.facts ρ := hi1.1.1
  obtain ⟨cs, hcs, -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat' hiniC hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco))
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvv hlv hsgc hcs
  have hwUA : accs (cl ρ η.wit 0 0 c) = some cs := (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2 hco)).symm.trans hcs
  have hwU : wc (cl ρ η.wit 0 0 c) = some (nWords cs) := by rw [← wc_of_sig hsgc]; simp [wc, hcs]
  have hvalR := storeValRB hE.2.1 hE.2.2 hi0.2.2.2.1 hi0.2.2.2.2.1 hsat hsub ho htb hvrv hlv hval.2
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key] at ⊢
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hvr, hlay, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    obtain ⟨Ro, hvold, hRo⟩ := oldValFB hE.2.1 hE.2.2 (hnie _ _ hsto) (MemInv_noOwnTB hm hsto hpfN) hat' hvr
    have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
    refine ⟨Rr + Ro + Rs, HP, ⟨ρ, η, c', Rr + Ro, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us + o))) hm1' hsto hown hat' hiniC hna hval hwUA hlen s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ j * nWords us + o)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    have h1 := hle (.own xl)
    have h3 := hRo xl
    simp only [Res.add_apply] at h1 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hown hpfN)
  obtain ⟨vq, Rq, R2, H0, hRe, hvql, hvqlat, hvqR, hput0⟩ :=
    heldStoreAtPB (a := offs ad (ev ρ j * nWords us + o)) hm hH (Priv_of hsto hown hpfN) hsto hown hnv (OwnOKPF_cellPB hm.2.1 hsto hown hpfN) hat' hiniC hna hvalR hwU hlen
  have hWold : WLe vq old := (loadUnits_latestPA hvql hvqlat h1 hp1).1
  have hvold := oldValRB hE.2.1 hE.2.2 hsgc (VRR_upB _ _ _ _ _ hWold hvqR)
  have hfr := bindRB hb hi1 (RLink_ofB hE.2.1 hE.2.2) hvold hlay
  refine ⟨Rr + Rq + Rs, R2 + H0, ⟨ρ, η, c', Rr + Rq, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := (offs ad (ev ρ j * nWords us + o))) hm1' hsto hown hat' hiniC hna hval hwUA hlen s2 hs2,
    hput0 g.k g.arch w false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h1 := hle (.own xl)
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply] at h1 h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:379 stepK3_stlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_stlwBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk hpj hij hpv hfx hb =>
  obtain ⟨t, u, n, k, jw, tj, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩ :
      ∃ t u n k jw tj tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi0.2.1 hpj hoj
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi0.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ := hlt ρ hi0.1
  have hJk := hltk ρ hi0.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ jw)) false [.one]
            [cst (.num (setLaneN w y (m % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hev, hni, hnj, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨-, -, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    refine ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := offs ad (ev ρ jw)) hm1' hsto hmode hat hini hna
        (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ jw)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    simp only [Res.add_apply]
    omega
  | none =>
  have hnvP := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput0⟩ := heldStoreAtPB (a := offs ad (ev ρ jw)) hm hH (Priv_of hsto hmode hpfN) hsto hmode hnvP (OwnOKPF_cellPB hm.2.1 hsto hmode hpfN) hat hini hna
    (lanes_EnvValRB sg w (setLaneN w y (m % w.lanes) yv)) hwU (by simp [nWords, Acc.size])
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine ⟨Rf + Rs, R2 + H0, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ jw)) hm1' hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
    hput0 g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply, Res.zero_apply] at h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:494 stepK3_stl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_stlBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.stl b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hx : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCKBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stl hp hbuf hlo hint hlt hltk hpv hfx hb =>
  obtain ⟨t, u, n, k, j, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩ : ∃ t u n k j tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩
  have hi0 := hi.1
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0 hlt hltk
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi0.2.1 hpi hti
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi0.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi0.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi0.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi0.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', -, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi0.2.2.2.1 hi0.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi0.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one]
            [cst (.num (setLaneN w y (ev ρ j % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hni, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  rw [key]
  intro r hr hpr0
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 (fun t ht m hm => hpr t ht m hm)
  obtain ⟨-, -, f1, -, fc, f3, -⟩ := hld (s1, old) h1 hp1
  have hm1' := hm1 (s1, old) h1 hp1
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    rw [Res.add_zero] at hfr
    refine ⟨Rf + Rs, HP, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_storeAtB (a := offs ad (ev ρ j / w.lanes)) hm1' hsto hmode hat hini hna
        (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
      memHeldOn_storeB (s' := s2) (a := offs ad (ev ρ j / w.lanes)) (memHeldOn_eqsB hH f1 f3)
        (fun l hl e => privOff (a := ad) hl (e.trans rfl) hpfN) (MemInv_promLtB hm1') hs2,
      hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
    simp only [Res.add_apply]
    omega
  | none =>
  have hnvP := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput0⟩ := heldStoreAtPB (a := offs ad (ev ρ j / w.lanes)) hm hH (Priv_of hsto hmode hpfN) hsto hmode hnvP (OwnOKPF_cellPB hm.2.1 hsto hmode hpfN)
    hat hini hna (lanes_EnvValRB sg w (setLaneN w y (ev ρ j % w.lanes) yv)) hwU (by simp [nWords, Acc.size])
  have hfr := bindRB hb hi (RLink_ofB hE.2.1 hE.2.2) (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
  rw [Res.add_zero] at hfr
  refine ⟨Rf + Rs, R2 + H0, ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j / w.lanes)) hm1' hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2,
    hput0 g.k g.arch pw false s1 f1 f3 fc (loadUnits_cohMono _ 0 _ _ h1) hm1'.2.2.2.2.1 s2 hs2, hnie, hx, ?_, anchStep_sameB (bumpIf_nb hterm)⟩
  have h2 := congrArg (fun R : Res => R (.own xl)) hRe
  simp only [Res.add_apply, Res.zero_apply] at h2 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:712 stepK3_bufInit
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_bufInitBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP)
    (hnie : StoNIE (CE η)) (hxl : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hTyE : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t, tv, u, n, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t tv u n k j c₁ c₂,
      cx.use b = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨rb, wsb, Rb, Rr1, hea, hvb, hlb, hvrb, hi1, hle1⟩ := useRB (bkG := False) hu hi hE.2.2
  have hRb := VRR_buf_RB hbuf hvrb
  obtain ⟨rv, wsv, Rv, Rr2, hev, hvv, hlv, hvrv, hi2, hle2⟩ := useRB (bkG := False) hu2 hi1 hE.2.2
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1.1
  have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hi1.1.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hvb0 := hvb
  simp only [VRF, VRb2] at hvb
  obtain ⟨hv, hir, -⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmode, hini0⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  have hKi : ev ρ k ≤ η.ini ad.label := by
    simp only [IniR] at hir; exact Nat.le_trans (hir ad (by simp [hwv])) (TEnv.selIni_le_ini _ _ _)
  have hKm : ev ρ k ≤ η.rc ad.label := by
    simp only [IniR] at hir; have h := hir ad (by simp [hwv]); rw [TEnv.selIni_loc] at h; exact h
  have hat := hat0
  have hini := hini0
  simp only [cl, clI_zero] at hat hini
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hweA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 ho htb1 (buf_lyt hlb.2.2.2.2 rfl).2).symm.trans hus
  have hwe : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨hval, hlen⟩ :=
    ownStoreValB (cx := c₁) hE.2.1 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1 hvv hlv hsig hus
  have hvalR := storeValRB (cx := c₁) hE.2.1 hE.2.2 hi1.1.2.2.2.1 hi1.1.2.2.2.2.1 hi2.1.1 hsub ho htb1
    hvrv hlv hval.2
  let ini' := bumpIni η.ini ad.label (ev ρ j + 1)
  let rini' := bumpIni η.rini ad.label (ev ρ j + 1)
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  have hile : ∀ l, η.ini l ≤ ini' l := bumpIni_le η.ini ad.label (ev ρ j + 1)
  have hx : ExtB η (η.withStoB η.sto ini' (Ri := rini')) := Ext_withStoB hE.2.1 (fun l c h => h) hile (Ri := rini') (hRi := hri')
  let rtR : Ty := Ty.refine (Ty.loc μr (Ty.array nr ur)) (Pred.ini (Idx.lit (ev ρ j + 1)))
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, rtR, [w]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, numOf, hwi, addrOf, hwv, bufElem, hus, List.map_map]; rfl
  rw [key]
  intro r hr hpa
  have hk := tyOKE_keep (r := r) (by rw [key]; exact hr) (fun _ _ _ _ h => by rw [hterm] at h; cases h) hTyE hRc
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hvr : (VRF False) ρ (η.withStoB η.sto ini' (Ri := rini')) (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      (shp rtR) [w] := by
    have h1 := VR_extB hE.2.1 hx hvb0
    simp only [VRF, VRb2] at h1 ⊢
    refine ⟨h1.1, fun a ha => ?_, fun hp => absurd hp (by rintro ⟨_, _, h⟩; simp [pp] at h)⟩
    have hav : a = ad := by simp [hwv] at ha; exact ha.symm
    subst hav
    show ev ρ (.add k (.lit 1)) ≤ min (bumpIni η.ini a.label (ev ρ j + 1) a.label)
      (bumpIni η.rini a.label (ev ρ j + 1) a.label)
    rw [bumpIni_self, bumpIni_self]; simp [ev]; omega
  have hlay : Lay th.σs (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      rtR [w] := Lay_repred hlb
  have hE' : EnvOKB p (η.withStoB η.sto ini' (Ri := rini')) := ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
  have hfr := bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi2) (RLink_ofB hE'.2.1 hE'.2.2) (VRR_ofVR_reflocWB hvr) hlay
  rw [← hRb] at hfr
  have hAS : ∀ s2, AnchStepB g th (CE η) (CE (η.withStoB η.sto ini' (Ri := rini'))) (stOf mem pairs th) s2 :=
    fun _ => anchStep_genB (ext_CEB hx)
      (bufBump hterm hea hwv hei (by simp [numOf, hwi])
        (show ev ρ j + 1 ≤ bumpIni η.ini ad.label (ev ρ j + 1) ad.label by rw [bumpIni_self]; exact Nat.le_max_right _ _)
        (show ev ρ j + 1 ≤ bumpIni η.rini ad.label (ev ρ j + 1) ad.label by rw [bumpIni_self]; exact Nat.le_max_right _ _))
      (fun _ _ h _ => h) (fun l _ => bumpIni_iniLe η.ini η.rini ad.label (ev ρ j + 1) l)
      (fun _ h0 hl => absurd h0 hl)
      (fun l _ => by
        by_cases hl : l = ad.label
        · exact Or.inr ⟨x, b, i, v, e, _, [w], ad, hterm, hea, by simp [hwv], hl.symm⟩
        · exact Or.inl (Nat.le_of_eq (bumpIni_other _ _ _ _ hl)))
      (fun h l => bumpIni_rle h l)
  cases hpfN : (CE η).pfr ad.label with
  | some f =>
    refine ⟨CE (η.withStoB η.sto ini' (Ri := rini')), Rr2 + Rb + Rs, HP,
      ⟨ρ, η.withStoB η.sto ini' (Ri := rini'), c', Rr2 + Rb, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      MemInv_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
        (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
        (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
      heldBufInitFB (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hH hpfN rfl rfl rfl
        (fun l' h => bumpIni_other _ _ _ l' h) (fun l' h => bumpIni_other _ _ _ l' h) rfl (fun _ _ h => h) rfl
        hile hri' hs', hnie, hxl, ?_, hAS _, hk.1, hk.2⟩
    have h1 := hle1 (.own xl)
    have h2 := hle2 (.own xl)
    simp only [Res.add_apply] at h1 h2 ⊢
    omega
  | none =>
  have hnv := NVP_priv (s := stOf mem pairs th) (Priv_of hsto hmode hpfN)
  obtain ⟨H2, hH2, hput⟩ := heldBufInitPB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) (pw := w) (g := g)
    hm hH (Priv_of hsto hmode hpfN) hsto hmode hnv (OwnOKPF_cellPB hm.2.1 hsto hmode hpfN) hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hwe (by omega) (show ev ρ j ≤ η.ini ad.label by omega) hvalR hlen
    rfl rfl rfl (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl (fun _ _ h => h)
    (fun o hq => hnv.2.2 o (PredU_bump (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) (k := ev ρ j + 1) rfl rfl rfl (bumpIni_self _ _ _) (by
      show min (bumpIni η.ini ad.label (ev ρ j + 1) ad.label) (bumpIni η.rini ad.label (ev ρ j + 1) ad.label) =
        max (min (η.ini ad.label) (η.rini ad.label)) (ev ρ j + 1)
      rw [bumpIni_self, bumpIni_self]; omega) hq)) (fun l' h => bumpIni_other _ _ _ l' h)
    (show ev ρ j ≤ min (η.ini ad.label) (η.rini ad.label) by have h := hKm; unfold TEnv.rc at h; omega)
    (show min (bumpIni η.ini ad.label (ev ρ j + 1) ad.label) (bumpIni η.rini ad.label (ev ρ j + 1) ad.label) =
        max (min (η.ini ad.label) (η.rini ad.label)) (ev ρ j + 1) by
      rw [bumpIni_self, bumpIni_self]; omega)
  refine ⟨CE (η.withStoB η.sto ini' (Ri := rini')), Rr2 + Rb + Rs, H2,
    ⟨ρ, η.withStoB η.sto ini' (Ri := rini'), c', Rr2 + Rb, Rs, rfl, hE', ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
      (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
      (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
    hput s' hs', hnie, hxl, ?_, hAS _, hk.1, hk.2⟩
  have h1 := hle1 (.own xl)
  have h2 := hle2 (.own xl)
  have h3 := Res.le_def.1 hH2 (.own xl)
  simp only [Res.add_apply] at h1 h2 h3 ⊢
  omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:870 stepK3_new
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_newBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr} {Rf Rs HP : Res} {xl : AllocLabel}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hxl : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hpp : g.p = p) (hTyE : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | new hu _ hb =>
  obtain ⟨tv, c₁, hu, hb, htvT⟩ : ∃ tv c₁, cx.use a = .ok (tv, c₁) ∧ c₁.bind x (.ptr .own tv) = .ok c' ∧ some tv = _ :=
    ⟨_, _, hu, hb, rfl⟩
  have hi0 := hi.1
  obtain ⟨rt, ws, Rv, Rr, hea, hv, hl, hvr, hiR, hle⟩ := useRB (bkG := False) hu hi hE.2.2
  have ho : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 tv) := lay_closed hi0.2.2.2.1 hi0.2.2.2.2.1 ho htb hl
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwcT : wc (cl ρ η.wit 0 0 tv) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvc : (VRF False) (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  have hvcR : VRRB (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws Rv := by
    rw [← shp_of_sig hsig]
    exact (VRR_closeB hE.2.1 hE.2.2 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws Rv (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvr
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, -, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hX := memHeldOn_offB hH (l := freshLabel g.lbase g.n g.i th.nalloc) (fun h => by
    obtain ⟨⟨c0, hc0, -⟩, -⟩ := h; rw [hnone] at hc0; cases hc0)
  have hval : ValOfB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) (cl ρ η.wit 0 0 tv)
      (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) :=
    ValOf_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValB.store (η := CE η) ⟨hvc, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hvalR : ValOfRB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      (cl ρ η.wit 0 0 tv) (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) Rv :=
    ValOfR_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValRB.store (η := CE η) ⟨hvcR, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hx : ExtB η (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto) :=
    Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := CE η) hnone h) (fun _ => Nat.le_refl _)
  have key : ∀ r ∈ tstep g mem pairs th, ∃ s' pw,
      (s', pw) ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i th.nalloc) us ws (stOf mem pairs th) ∧
      ∃ tys, r = (s'.mem, s'.pairs,
        { withS { th with term := e, env := (x, .ptr .own rt, [pw]) :: th.env } s' with tys := tys }) := by
    intro r hr
    obtain ⟨s1, t1, ws1, hm1, tys, rfl⟩ := TermRun.tstep_new_mem hterm hr
    simp only [evalOp, hea, hus, List.mem_map] at hm1
    obtain ⟨⟨s2, pw⟩, hal, he⟩ := hm1
    cases he
    exact ⟨_, _, hal, tys, rfl⟩
  · intro r hr _
    obtain ⟨s', pw, hal, tys, rfl⟩ := key r hr
    obtain ⟨hmo', hoo', hpw⟩ := alloc_okPB hwcT hlen hval hfresh hnone hpl hpo.1 hpo.2.1 hpf0 hmo hoo ⟨s', pw⟩ hal
    obtain ⟨hg, hsubl, hna, hpl', hful⟩ := alloc_growsP hpl ⟨s', pw⟩ hal
    obtain ⟨hla1, -⟩ := alloc_latP (k := g.k) (arch := g.arch) (us := us) (ws := ws) hpl (MemInv_nodupB hm)
      ⟨s', pw⟩ hal
    obtain ⟨hwr, hhid⟩ := alloc_hidPB (s := stOf mem pairs th) hval
      (ShapeC_of_wc hwcT (by rw [List.length_map]; exact hlen))
      (by obtain ⟨_, h, -⟩ := wc_some hwcT; simp [h]) hfresh hpl ⟨s', pw⟩ hal
    simp only at hmo' hoo' hpw hg hsubl hna hwr hhid hla1 hpl' hful
    subst hpw
    have hwA : ∀ T o w, WordOKB (CE η) T o w →
        WordOKB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) T o w :=
      fun T o w h => WordOK_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _)
        (fun _ _ h' => h') (fun _ h' => h') h
    have hoh' : OwnHidPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem s'.vs
        s'.promises := by
      refine ⟨fun l c hc ho o hi => ?_, fun l c hc ho hlt => ?_⟩
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          rw [allocE_eq] at hc; cases hc; exact hhid o
        · rw [allocE_ne hl] at hc
          exact HiddenP_growsAtB (hoh.1 l c hc ho o hi) (hwA _ _) hwr hg hl hful
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
            (Nat.not_lt_zero _)
        · rw [allocE_ne hl] at hc
          obtain ⟨f, hf, hs, hH⟩ := hoh.2 l c hc ho hlt
          exact ⟨f, hf, fun hz => hs (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
            fun o hi => HiddenP_growsAtB (hH o hi) (hwA _ _) (Nat.le_refl _) hg hl hful⟩
    have hpd' : PubDefPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem
        s'.promises := by
      intro l c f hc hown hf o hi
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at hc; cases hc; exact (hown rfl).elim
      · rw [allocE_ne hl] at hc
        exact HiddenP_growsAtB (hpd l c f hc hown hf o hi) (hwA _ _) (Nat.le_refl _) hg hl hful
    have hpi' : PubInvB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      refine PubInv_growB (hbs := fun l hb h => by
          by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
          · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
          · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (alloc_pairs _ hal) hful rfl rfl (fun l c h => allocE_sub hnone h)
        (fun _ => Nat.le_refl _) rfl rfl (fun c h => by rw [allocE_eq] at h; rw [← Option.some.inj h]; rfl)
        (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
          (Nat.not_lt_zero _)) (hrcg := fun _ h => ⟨h, Nat.le_refl _⟩)
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl; exact Or.inr hpf0
        · rw [allocE_ne hl] at h; exact Or.inl h
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at h
        cases h
        refine Or.inr ?_
        rcases hseg with ⟨-, rfl, -⟩ | ⟨N, us0, j0, hT, -, -, -⟩
        · obtain ⟨vals, hcell, -⟩ := hoo' _ _ allocE_eq rfl
          rcases hcell with ⟨hwc, hv⟩ | hb
          · exact ⟨vals, hv, Option.some.inj (hwc.symm.trans (wc_of_accs hu'))⟩
          · obtain ⟨N, e0, us0, hT, -⟩ := hb
            exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
        · exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
      · rw [allocE_ne hl] at h; exact Or.inl ⟨h, hini⟩
    have hopub' : OwnPubV (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      intro l c f hc ho hf
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
      · rw [allocE_ne hl] at hc
        exact ((hopub.alloc hpl hal) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
          fun a ha hi c1 N1 e1 us1 h1 => hi c1 N1 e1 us1 (by rw [allocE_ne (fun e => hl (ha.symm.trans e))]; exact h1))
    
    have hfr' : FInvRB g.lbase g.n g.i ρ (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto)
        th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c'
        ((x, .ptr .own rt, [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env) (Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc))) := by
      refine bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hiR) (RLink_ofB hx.1 hx.2.2.2.2.2.2.2.2.2.2.1) ?_ ?_
      · simp only [VRRB]
        exact ⟨⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, ⟨cl ρ η.wit 0 0 tv, some η.tid⟩, by simp [cst, Promises.TVal.mk0], rfl,
          by simp [TEnv.withStoB, allocE, CE], .refl, by first | rfl | trivial,
          show accs (cl ρ η.wit 0 0 tv) ≠ none from fun h => by simp [wc, h] at hwcT⟩,
          (ownW_own_loc (a := ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩) (g := 0)
            (by simp [cst, Promises.TVal.mk0])).symm⟩
      · refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs],
          ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, by simp [cst, Promises.TVal.mk0]⟩, ?_⟩
        · show Ty.ptr (skelM .own) (etok (skel rt)) = Ty.ptr _ _
          rw [hl.2.1]; rfl
        · show Ty.ptr (modeC 0 .own) (etok (lyt 0 rt)) = Ty.ptr _ _
          rw [hl.2.2.2.2]; rfl
    
    have hent : HeldEntryB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'
        (freshLabel g.lbase g.n g.i th.nalloc) Rv := by
      refine HeldEntry_ownPB allocE_eq (PromAt_privL (Priv_of allocE_eq rfl hpf0)) (fun o v hov => ?_)
        (Or.inl ⟨by rw [List.length_map, hlen]; exact hwcT, hvalR⟩)
      rw [List.getElem?_map] at hov
      cases hw : ws[o]? with
      | none => rw [hw] at hov; cases hov
      | some w =>
        rw [hw] at hov
        simp only [Option.map_some, Option.some.injEq] at hov
        subst hov
        have ho' : o < ws.length := (List.getElem?_eq_some_iff.1 hw).1
        exact hla1 o w (by rw [← hlen]; exact ho') hw
    have hX' := memHeldOn_trB (Q' := fun l' => Priv (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) l' ∧
        l' ≠ freshLabel g.lbase g.n g.i th.nalloc) (s' := s') hX
      (fun l => ⟨fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne] at hc; exact hc, ho⟩, hp⟩, hne⟩,
        fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne]; exact hc, ho⟩, hp⟩, hne⟩⟩)
      (fun l' h => allocE_ne h.2) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl rfl
      (fun l' h o w hl => LatestNP_growsAtF hg (fun t h => hsubl.subset h) hful h.2 hl)
      (fun h => ValOfR_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _) h)
    have hTR : ThInvREB g.lbase g.n g.i p (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        { withS { th with term := e, env := (x, .ptr .own rt, [cst (.loc ⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩ 0)]) :: th.env } s' with tys := tys }
        (Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs) :=
      ⟨ρ, η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c',
          Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩
    have hNC : NewCellSto g ρ η th (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) := by
      intro x' a' T' e' h'
      rw [hterm] at h'
      obtain ⟨-, ⟨-, hT'⟩, -⟩ := (by simpa using h' : x = x' ∧ (a = a' ∧ _ = T') ∧ e = e')
      refine ⟨_, allocE_eq, ?_⟩
      show cl ρ η.wit 0 0 tv = cl ρ η.wit 0 0 T'
      rw [Option.some.inj htvT, hT']
    have hk := tyOKE_alloc hn hr (fun _ hl => allocE_ne hl) hTyE hRc
      (fun c t hc ht => TermStep.hnew_of hr hRc (by rw [hpp]; exact hDy) (fun k => (hE.2.1 k).1) hNC c t hc ht)
    refine ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv), Rr + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Rv + HP,
        hTR, ?_,
        memHeldOn_unfocusB hX' hent (Priv_of allocE_eq rfl hpf0), fun l cl hcl => ?_,
        fun h => by
          by_cases hxe : xl = freshLabel g.lbase g.n g.i th.nalloc
          · rw [hxe, allocE_eq] at h; cases h
          · rw [allocE_ne hxe] at h; exact h, ?_,
        anchStep_freshB (ext_CEB hx) (bumpIf_nb hterm (hop := by intro _ _ _ h; cases h) _) (fun _ hl => allocE_ne hl) hpf0 (fun _ _ => rfl) hnone
          (Priv_of allocE_eq rfl hpf0) (fun _ _ => rfl) (fun h => h _), hk.1, hk.2⟩
    · refine ⟨hmo', hoo', hpl', ⟨fun j hj => ?_, PrivCoh_growsAtB hfr.2
          (fun a hu hl => by
            obtain ⟨c, N, e, us, hc, rest⟩ := hu
            exact ⟨c, N, e, us, by rw [allocE_ne hl] at hc; exact hc, rest⟩)
          hoo' hg hful (fun t m _ _ hu hl => by
            obtain ⟨c, N, e, us, hc, -, -, hT, -⟩ := hu
            rw [hl, allocE_eq] at hc; cases hc
            simp only at hT; rw [hT] at hwcT; simp [wc, accs] at hwcT)⟩, ?_, hoh', hpd', hopub', hpi',
        BoxInv_alloc hbi rfl hpl hpo.1 hal rfl rfl (fun _ hl => allocE_ne hl) (fun _ _ => rfl),
        PromOK_alloc hpo hpl hal⟩
      rotate_left 1
      · have e : s'.vs.vRelSt = (stOf mem pairs th).vs.vRelSt := alloc_relSt _ hal
        exact (SeenLE.mono hsn (Nat.le_of_eq e.symm) : SeenLE (CE η) s'.vs.vRelSt)
      · have hj' : th.nalloc ≤ j := by
          have : s'.nalloc ≤ j := hj
          rw [hna] at this; exact Nat.le_of_succ_le this
        obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
        have hne : freshLabel g.lbase g.n g.i j ≠ freshLabel g.lbase g.n g.i th.nalloc := fun h => by
          have := freshLabel_inj_k hn h; subst this
          have : s'.nalloc ≤ th.nalloc := hj
          rw [hna] at this; exact absurd this (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
        refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, f4, f5⟩
        change s'.mem[t]? = some m at ht
        by_cases hlt : t < (stOf mem pairs th).mem.size
        · rw [hg.2.1 t hlt] at ht
          have hp := f2 t m ht hl
          refine Classical.byContradiction fun hn' => ?_
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl; rw [allocE_eq] at hcl; cases hcl
        exact noIallV_cl (WitAF.ni hi.1.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu)
      · rw [allocE_ne hl] at hcl; exact hnie l cl hcl
    · have h1 := hle (.own xl)
      by_cases hxe : xl = freshLabel g.lbase g.n g.i th.nalloc
      · rw [bornInc_born (by rw [hxe]; exact hnone) (by rw [hxe, allocE_eq]; exact Option.some_ne_none _)]
        have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) ≤ 1 := by
          simp only [Res.one]; split <;> omega
        simp only [Res.add_apply] at h1 ⊢
        omega
      · have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) = 0 := by simp [Res.one, hxe]
        simp only [Res.add_apply] at h1 ⊢
        omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1091 stepK3_newBuf
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stepK3_newBufBU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr} {Rf Rs HP : Res}
    {xl : AllocLabel}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hH : MemHeldPB (CE η) (stOf mem pairs th) HP) (hnie : StoNIE (CE η)) (hxl : BornMono xl (CE η) (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hTyE : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → StepCBU p g xl (CE η) (stOf mem pairs th) th (Rf + Rs) HP r := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | newBuf hwf hsc hop haf hint hb =>
  rename_i k
  have hiF := hi.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hiF.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hlay : accs (close th.σs τ) ≠ none := accs_close hwf hiF.2.2.2.2.1 haf hiF.2.2.2.2.2.1.2.2
  obtain ⟨us, hus⟩ : ∃ us, accs (close th.σs τ) = some us := Option.ne_none_iff_exists'.1 hlay
  
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hiF.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hiF.2.2.2.1 ρ hop hr
  have hwT : wc (cl ρ η.wit 0 0 τ) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨usT, husT⟩ : ∃ usT, accs (cl ρ η.wit 0 0 τ) = some usT := by
    cases h : accs (cl ρ η.wit 0 0 τ) with
    | none => simp [wc, h] at hwT
    | some usT => exact ⟨usT, rfl⟩
  have hnw : nWords usT = nWords us := by rw [wc_of_accs husT] at hwT; exact Option.some.inj hwT
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hiF.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  
  let z : Option (List WeakMem.Val) := if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none
  have hzv : ∀ zs, z = some zs → ValOfB η (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ wc (cl ρ η.wit 0 0 τ) = some zs.length := by
    intro zs h
    simp only [z] at h
    split at h
    · exact zero_valOfB hiF.2.2.2.1 (fun k => (hE.2.1 k).1) hiF.2.2.2.2.2.2.1 ρ hop hr haf ‹_› h
    · cases h
  have hstat : zeroableIn [] cx.ke τ = true → z.isSome = true := by
    intro h
    have hR := KindSound.zero_close cx.ke th.σs τ hiF.2.2.2.2.2.1.2.1 h
    obtain ⟨zs, hzs, -⟩ := zpB _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
    simp [z, hR, hzs]
  
  let K := ev ρ k
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  let iv : Nat := if z.isSome then K else 0
  let ini' := bumpIni η.ini lbl iv
  let rini' := bumpIni η.rini lbl iv
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  let E0 := CE (η.withStoB η.sto ini' (Ri := rini'))
  let T := Ty.array (.lit K) (cl ρ η.wit 0 0 τ)
  let E' := allocE E0 lbl T
  let η' := η.withStoB E'.sto ini' (Ri := rini')
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, hi0, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hX := memHeldOn_offB hH (l := lbl) (fun h => by
    obtain ⟨⟨c0, hc0, -⟩, -⟩ := h; rw [hnone] at hc0; cases hc0)
  have hnone0 : E0.sto lbl = none := hnone
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := E0) hnone0 h) (bumpIni_le _ _ _)
    (Ri := rini') (hRi := hri')
  let rtR : Ty := .refine (.loc .own (.array (.lit K) (close th.σs τ))) (.ini (.lit iv))
  let R := allocBuf lbl (K * nWords us) z (stOf mem pairs th)
  have key : tstep g mem pairs th =
      [(R.1.mem, R.1.pairs, withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1)] := by
    simp only [tstep, hterm, evalOp, hei, numOf, hus, Option.bind_eq_bind, Option.bind_some, hwi]; rfl
  rw [key]
  intro r hr' _
  simp only [List.mem_singleton] at hr'
  subst hr'
  have hpw : R.2 = cst (.loc ⟨lbl, 0⟩ 0) := rfl
  
  have hsub0 : ∀ l c, (CE η).sto l = some c → E0.sto l = some c := fun l c h => h
  have hile0 : ∀ l, (CE η).ini l ≤ E0.ini l := bumpIni_le η.ini lbl iv
  have hmo0 : MemOKPB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).promises :=
    MemOKP_monoB hmo rfl rfl hsub0 hile0 (fun t m c h hc => hc)
  have hmono0 : ∀ {U : Ty} {vs : List Word}, ValOfB (CE η) U vs → ValOfB E0 U vs :=
    fun h => ValOf_monoB (η₁ := CE η) (η₂ := E0) rfl rfl hsub0 hile0 h
  have hoo0 : OwnOKPFB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).vs
      (stOf mem pairs th).promises := by
    intro l c hc ho
    have hne : l ≠ lbl := fun h => by rw [h] at hc; rw [hnone0] at hc; cases hc
    exact OwnCellF_envB (hoo l c hc ho) hmono0 (bumpIni_other _ _ _ _ hne) rfl hmo.2.2 (bumpIni_other _ _ _ _ hne)
  have hi0' : η.ini lbl = 0 := hi0
  have hini : E0.ini lbl ≤ K := by
    show bumpIni η.ini lbl iv lbl ≤ K
    rw [bumpIni_self, hi0']
    refine Nat.max_le.2 ⟨Nat.zero_le _, ?_⟩
    simp only [iv]; split <;> omega
  have hini0 : 0 < E0.ini lbl → z ≠ none := by
    intro h hz0
    have : E0.ini lbl = 0 := by
      show bumpIni η.ini lbl iv lbl = 0
      rw [bumpIni_self, hi0']; simp [iv, hz0]
    omega
  have hzE : ∀ zs, z = some zs → ValOfB E' (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ zs.length = nWords usT :=
    fun zs h => ⟨ValOf_monoB (η₁ := η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (hzv zs h).1,
      by have := (hzv zs h).2; rw [hwT] at this; rw [hnw]; exact (Option.some.inj this).symm⟩
  have hab := allocBuf_okPB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
    (s := stOf mem pairs th) (η := E0) husT hzE
    hini hini0 hfresh hnone0 hpl hpo.2.1 hmo0 hoo0 hpf0
  rw [hnw] at hab
  obtain ⟨hmo', hoo', -⟩ := hab
  obtain ⟨hg, hpr, hna⟩ := allocBuf_grows lbl (K * nWords us) z (stOf mem pairs th)
  have hwE : ∀ T o w, WordOKB (CE η) T o w → WordOKB E' T o w := fun T o w h =>
    WordOK_monoB (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (fun _ _ h' => h') (fun _ h' => h') h
  have hiniE : ∀ l c o, l ≠ lbl → InitR E' c l o → InitR (CE η) c l o := fun l c o hl hi N1 e1 us1 h1 h2 => by
    have := hi N1 e1 us1 h1 h2
    rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  have hoh' : OwnHidPB E' R.1.mem R.1.vs R.1.promises := by
    refine ⟨?_, ?_⟩
    · intro l c hc ho o hi
      by_cases hl : l = lbl
      · rw [hl] at hc hi
        have hcT : c = ⟨T, some η.tid⟩ := by
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at hc; exact (Option.some.inj hc).symm
        subst hcT
        rw [hl]
        unfold HiddenPB
        intro t m hP hm hloc hnok
        exfalso
        rcases Option.eq_none_or_eq_some z with hzc | ⟨zs, hzc⟩
        · 
          have h0 : E'.ini lbl = 0 := by
            show bumpIni η.ini lbl iv lbl = 0
            rw [bumpIni_self, hi0']; simp [iv, hzc]
          have := hi K (cl ρ η.wit 0 0 τ) usT rfl husT
          rw [show E'.rc lbl = 0 by have := E'.rc_le_ini lbl; omega, Nat.zero_mul] at this; exact Nat.not_lt_zero _ this
        · 
          apply hnok
          by_cases hlt : t < (stOf mem pairs th).mem.size
          · rw [hg.2.1 t hlt] at hm
            exact (hP (hfresh t m hm (by rw [hloc]))).elim
          · have hw := allocBuf_newOKB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
              (s := stOf mem pairs th) (η := E0) husT hzE zs hzc t m (by omega) (by rw [hnw]; exact hm)
            rw [hloc] at hw; exact hw
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        exact HiddenP_growsAtB (hoh.1 l c hc ho o (fun N1 e1 us1 h1 h2 => by
            have := hi N1 e1 us1 h1 h2; rw [hrc] at this; exact this))
          (hwE _ _) (allocBuf_vWr_le _ _ _ _) hg hl
          (fun t h1 h2 => absurd h1 h2)
    · intro l c hc ho hlt
      by_cases hl : l = lbl
      · exfalso
        have h1 : E'.ini lbl ≤ E'.rini lbl := by
          show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl
          rw [bumpIni_self, bumpIni_self, hi0']; omega
        have h2 : E'.rc lbl = E'.ini lbl := Nat.min_eq_left h1
        rw [hl] at hlt; omega
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        have hie : E'.ini l = (CE η).ini l := bumpIni_other _ _ _ _ hl
        obtain ⟨f, hf, hsn', hH⟩ := hoh.2 l c hc ho (by rw [hrc, hie] at hlt; exact hlt)
        exact ⟨f, hf, fun hz => hsn' (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
          fun o hi => HiddenP_growsAtB (hH o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
          (fun t h1 h2 => absurd h1 h2)⟩
  have hpd' : PubDefPB E' R.1.mem R.1.promises := by
    intro l c f hc hown hf o hi
    by_cases hl : l = lbl
    · rw [hl] at hc
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at hc; cases hc; exact (hown rfl).elim
    · rw [allocE_ne hl] at hc
      exact HiddenP_growsAtB (hpd l c f hc hown hf o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
        (fun t h1 h2 => absurd h1 h2)
  have hopub' : OwnPubV E' R.1 := by
    intro l c f hc ho hf
    by_cases hl : l = lbl
    · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
    · rw [allocE_ne hl] at hc
      exact ((hopub.allocBuf hpl lbl (K * nWords us) z) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
        fun a ha hi c1 N1 e1 us1 h1 h2 h3 => by
          have hne : a.label ≠ lbl := fun e => hl (ha.symm.trans e)
          have := hi c1 N1 e1 us1 (by rw [allocE_ne hne]; exact h1) h2 h3
          rwa [show E'.rc a.label = (CE η).rc a.label from
            TEnv.rc_congr (bumpIni_other _ _ _ _ hne) (bumpIni_other _ _ _ _ hne)] at this)
  have hrcl : E'.rc lbl = E'.ini lbl := Nat.min_eq_left (show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl by
    rw [bumpIni_self, bumpIni_self, hi0']; omega)
  have hpi' : PubInvB E' R.1 := by
    refine PubInv_growB (E := CE η) (hbs := fun l hb h => by
        by_cases hl : l = lbl
        · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
        · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (fun _ h => h) (fun t h1 h2 => absurd h1 h2) rfl rfl
      (fun l c h => allocE_sub (η := E0) hnone0 (hsub0 l c h)) hile0 rfl rfl
      (fun c h => by
        have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
        rw [h2] at h; rw [← Option.some.inj h]; rfl)
      (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd hlt (by rw [hrcl]; exact Nat.lt_irrefl _))
      (hrcg := fun l h => by
        by_cases hl : l = lbl
        · rw [hl, hrcl] at h; exact absurd h (Nat.lt_irrefl _)
        · exact ⟨by rwa [TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl),
            show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl] at h,
            Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl)⟩)
      (hfi := fun l c h ho => by
        by_cases hl : l = lbl
        · rw [hl] at h
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at h; rw [← Option.some.inj h] at ho; exact absurd rfl ho
        · exact Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl))
    · by_cases hl : l = lbl
      · exact Or.inr (by rw [hl]; exact hpf0)
      · rw [allocE_ne hl] at h; exact Or.inl h
    by_cases hl : l = lbl
    · rw [hl] at h
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at h; cases h
      refine Or.inr ?_
      rcases hseg with ⟨-, rfl, -⟩ | ⟨N1, us1, j1, hT1, -, -, -⟩
      · simp [T, accs] at hu'
      · have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N1) S := hT1
        simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
        obtain ⟨-, rfl⟩ := hT2
        rw [husT] at hu'; obtain rfl := Option.some.inj hu'
        obtain ⟨-, jb, -, hjb, -⟩ := hini K (cl ρ η.wit 0 0 τ) rfl
        have hpos : 0 < E0.ini lbl := by
          rw [hl] at hjb; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hjb
        obtain ⟨zs, hzs⟩ := Option.ne_none_iff_exists'.1 (hini0 hpos)
        obtain ⟨h1, h2⟩ := hzE zs hzs
        exact ⟨zs.map cst, h1, by rw [List.length_map]; exact h2⟩
    · rw [allocE_ne hl] at h
      refine Or.inl ⟨h, fun N1 e1 h1 => ?_⟩
      have := hini N1 e1 h1
      rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  
  have hzR : ∀ zs, z = some zs → ValOfRB E' (cl ρ η.wit 0 0 τ) (zs.map cst) Res.zero := by
    intro zs h
    simp only [z] at h
    split at h
    · rename_i hR
      have hZ := zrel_WitL hiF.2.2.2.1 (fun k => (hE.2.1 k).1) ρ hop hr
      have hTz := (zrel_zero _ _ [] [] hZ hsig knone_nil).1 hR
      have hwT' := zrel_words _ _ _ [] zs (Nat.lt_succ_self _) hZ hsig h
      obtain ⟨zs', hzw', -, hv⟩ := zpRB _ _ (Nat.lt_succ_self _) [] [] hafT knone_nil hTz
      obtain rfl : zs = zs' := Option.some.inj (hwT'.symm.trans hzw')
      obtain ⟨hV0, hvr0⟩ := hv _ (map_val_cst zs)
      exact ⟨hvr0 _ _ (agree_nil _), hV0⟩
    · cases h
  
  have hfr' : FInvRB g.lbase g.n g.i ρ η' th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((x, rtR, [R.2]) :: th.env) (Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc))) := by
    refine bindRB hb (FInvR_extB hE.2.1 hE.2.2 hx hi) (RLink_ofB hx.1 hx.2.2.2.2.2.2.2.2.2.2.1) ?_ ?_
    · 
      simp only [VRRB]
      refine ⟨⟨Or.inr ⟨⟨lbl, 0⟩, ⟨T, some η.tid⟩, _, by simp [hpw, cst, Promises.TVal.mk0],
        (show E'.sto lbl = _ from allocE_eq), ?_, .refl, by first | rfl | trivial, ?_⟩,
        (ownW_own_loc (a := ⟨lbl, 0⟩) (g := 0) (by simp [hpw, cst, Promises.TVal.mk0])).symm⟩, ?_⟩
      · simp only [cl, clI_zero]; exact AtOff.here (Or.inr ⟨K, _, rfl, by simp [husT]⟩)
      · intro N' e' h; left; exact ⟨by simp only [cl, clI_zero]; rfl, rfl⟩
      · refine ⟨fun a ha => ?_, fun hp => absurd hp (by rintro ⟨_, _, h⟩; simp [pp] at h)⟩
        have hav : a = ⟨lbl, 0⟩ := by simp [hpw, cst, Promises.TVal.mk0] at ha; exact ha.symm
        subst hav
        show ev ρ _ ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
        refine Nat.le_min.2 ⟨?_, ?_⟩
        · rw [bumpIni_self]
          split
          · rename_i hzs
            have h1 := hstat hzs
            have h2 : iv = K := by simp only [iv, h1, ite_true]
            rw [h2]; exact Nat.le_max_right _ _
          · exact Nat.zero_le _
        · rw [bumpIni_self]
          split
          · rename_i hzs
            have h1 := hstat hzs
            have h2 : iv = K := by simp only [iv, h1, ite_true]
            rw [h2]; exact Nat.le_max_right _ _
          · exact Nat.zero_le _
    · refine ⟨fun us' h => by simp [rtR, accs] at h; subst h; rfl, ?_, by simp [rtR, wc, accs], ?_, ?_⟩
      · simp [rtR, skel, close, substTs, skelM, rf]
      · simp only [rtR, Valid]; exact Or.inr ⟨⟨lbl, 0⟩, by simp [hpw, cst, Promises.TVal.mk0]⟩
      · simp [rtR, close, substTs, lyt, anyB_zero, idxC, ofMs, modeC]
  
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, bufVal z j, 0⟩
  have hget : ∀ t : Nat, R.1.mem[t]? = if t < (stOf mem pairs th).mem.size then (stOf mem pairs th).mem[t]?
      else if t < (stOf mem pairs th).mem.size + K * nWords us then some (f (t - (stOf mem pairs th).mem.size))
      else none := by
    intro t
    show (allocBuf lbl (K * nWords us) z (stOf mem pairs th)).1.mem[t]? = _
    rw [allocBuf_mem]; exact fold_get f _ _ t
  have hV : R.1.vs.coh = fun b => if b.label = lbl ∧ b.offset < K * nWords us
      then (stOf mem pairs th).mem.size + b.offset else (stOf mem pairs th).vs.coh b := rfl
  have hent : HeldEntryB E' R.1 lbl Res.zero := by
    refine HeldEntry_ownPB (vals := (List.range (K * nWords us)).map (fun j => cst (bufVal z j)))
      allocE_eq (PromAt_privL (Priv_of allocE_eq rfl hpf0)) (fun o v hov => ?_) (Or.inr ?_)
    · obtain ⟨o, rfl⟩ : ∃ o' : Nat, o' = o := ⟨o, rfl⟩
      have ho' : o < K * nWords us := by
        have := (List.getElem?_eq_some_iff.1 hov).1; simpa using this
      rw [List.getElem?_map, List.getElem?_range ho'] at hov
      simp only [Option.map_some, Option.some.injEq] at hov; subst hov
      refine LatestS_of_latest ⟨⟨f o, ?_, by simp [f, offs], rfl, fun _ _ _ => Nat.zero_le _⟩,
        fun t m ht hm' => ?_⟩ ?_
      rotate_left 2
      · intro hp
        have hp' : R.1.vs.coh ⟨lbl, o⟩ ∈ (stOf mem pairs th).promises := by rw [← hpr]; exact hp
        have h1 := hpl _ hp'
        have e : R.1.vs.coh ⟨lbl, o⟩ = (stOf mem pairs th).mem.size + o := by rw [hV]; simp [ho']
        rw [e] at h1; exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h1)
      · rw [hV, hget]; simp [ho']
      · obtain ⟨t, rfl⟩ : ∃ t' : Nat, t' = t := ⟨t, rfl⟩
        rw [hV] at ht; simp [ho'] at ht
        replace ht : (stOf mem pairs th).mem.size + o < (t : Nat) := ht
        rw [hget t] at hm'
        have h0 : ¬ t < (stOf mem pairs th).mem.size := by omega
        simp only [h0, ite_false] at hm'
        split at hm'
        · simp only [Option.some.injEq] at hm'; subst hm'
          simp [f, offs]; intro h; replace h : (t : Nat) - (stOf mem pairs th).mem.size = o := h; omega
        · cases hm'
    · refine ⟨K, cl ρ η.wit 0 0 τ, usT, (List.range (E'.ini lbl)).map (fun _ => Res.zero), rfl, husT, hini,
        by rw [List.length_map, List.length_range, hnw], by simp, (TermStep.sum_map_zero _).symm, fun j Rj hj hRj => ?_⟩
      rw [List.getElem?_map, List.getElem?_range hj] at hRj
      simp only [Option.map_some, Option.some.injEq] at hRj; subst hRj
      have hjK : j < K := Nat.lt_of_lt_of_le hj hini
      obtain ⟨zs, hzc⟩ := Option.ne_none_iff_exists'.1 (hini0 (Nat.lt_of_le_of_lt (Nat.zero_le _) hj))
      have hzl : zs.length = nWords us := by rw [← hnw]; exact (hzE zs hzc).2
      have e1 : ((((List.range (K * nWords us)).map (fun j => cst (bufVal z j))).drop (j * nWords usT)).take
          (nWords usT)) = zs.map cst := by
        rw [hnw]
        apply List.ext_getElem?; intro i
        rw [slice_get]
        by_cases hi : i < nWords us
        · simp only [hi, ↓reduceIte]
          have hjN : j * nWords us + i < K * nWords us := by
            have := Nat.mul_le_mul_right (nWords us) (show j + 1 ≤ K by omega); rw [Nat.succ_mul] at this
            omega
          rw [List.getElem?_map, List.getElem?_range hjN]
          have hg' : zs[(j * nWords us + i) % nWords us]? = some (bufVal z (j * nWords us + i)) := by
            rw [hzc, ← hzl]; exact bufVal_some (by omega)
          have hmod : (j * nWords us + i) % nWords us = i := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
          rw [hmod] at hg'
          rw [List.getElem?_map, hg']; rfl
        · simp only [hi, ↓reduceIte]; symm; exact List.getElem?_eq_none (by simp only [List.length_map]; omega)
      rw [e1]; exact ⟨fun _ _ => rfl, fun _ => hzR zs hzc⟩
  have hX' := memHeldOn_trB (Q' := fun l' => Priv E' l' ∧ l' ≠ lbl) (E' := E') (s' := R.1) hX
    (fun l => ⟨fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne] at hc; exact hc, ho⟩, hp⟩, hne⟩,
      fun ⟨⟨⟨c, hc, ho⟩, hp⟩, hne⟩ => ⟨⟨⟨c, by rw [allocE_ne hne]; exact hc, ho⟩, hp⟩, hne⟩⟩)
    (fun l' h => allocE_ne h.2) (fun l' h => bumpIni_other _ _ _ _ h.2) (fun l' h => bumpIni_other _ _ _ _ h.2)
    (fun _ _ => rfl) rfl rfl
    (fun l' h o w hl => LatestNP_growsAtA hg hpr h.2 hl)
    (fun h => ValOfR_monoB (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) h)
  have hk := tyOKE_alloc (E := CE η) (E' := E') hn (by rw [key]; exact List.mem_singleton_self _) (fun _ hl => allocE_ne hl) hTyE hRc
    (fun _ t _ ht => absurd (by rwa [tysUpd_keep (th := th) (th' := withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1) rfl] at ht) (hRc th.nalloc (Nat.le_refl _) t))
  refine ⟨E', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) + Rs, Res.zero + HP,
    ⟨ρ, η', c', Rf + Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)), Rs, rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨he, hck⟩, htv', hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
      ⟨hmo', hoo', fun t ht => by
        have ht' : t ∈ R.1.promises := ht
        rw [hpr] at ht'; exact Nat.lt_of_lt_of_le (hpl t ht') hg.1,
      ⟨fun j hj => ?_, PrivCoh_allocBufB hfr.2
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, ho, hp, hT, hus1, hle, hlt⟩ := hu
          refine ⟨c, N, e, us1, by rw [allocE_ne hl] at hc; exact hc, ho, hp, hT, hus1, ?_, hlt⟩
          rwa [TEnv.rc_congr (η' := E') (η := CE η) (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)] at hle)
        hoo' hfresh
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, -, -, hT, hus1, hle, hlt⟩ := hu
          rw [hl, show E'.sto lbl = some ⟨T, some η.tid⟩ from allocE_eq] at hc; cases hc
          have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) e := hT
          simp only [Ty.array.injEq, Idx.lit.injEq] at hT2; obtain ⟨rfl, rfl⟩ := hT2
          refine Classical.byContradiction fun hz => ?_
          have hs : z.isSome = true := Option.ne_none_iff_isSome.1 hz
          have hrc : K ≤ E'.rc lbl := by
            show K ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
            have hiv : iv = K := by simp only [iv, hs, ↓reduceIte]
            rw [bumpIni_self, bumpIni_self, hiv]
            exact Nat.le_min.2 ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
          rw [hl] at hle
          have := Nat.mul_le_mul_right (nWords us1) hrc
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans this hle)) (Nat.lt_irrefl _))⟩, hsn,
        hoh', hpd', hopub', hpi', BoxInv_allocBuf hbi rfl rfl rfl (fun l hl => by rw [allocE_ne hl]; rfl) (fun l hl => bumpIni_other _ _ _ _ hl),
        PromOK_eq hpo rfl rfl⟩,
      memHeldOn_unfocusB hX' hent (Priv_of allocE_eq rfl hpf0), fun l cl hcl => ?_,
      fun h => by
        by_cases hxe : xl = lbl
        · rw [hxe, allocE_eq] at h; cases h
        · rw [allocE_ne hxe] at h; exact h, ?_,
      anchStep_freshB (ext_CEB hx) (bumpIf_nb hterm (hop := by intro _ _ _ h; cases h) _) (fun _ hl => allocE_ne hl) hpf0
        (fun _ hl => bumpIni_other _ _ _ _ hl) hnone (Priv_of allocE_eq rfl hpf0)
        (fun _ hl => by first | rfl | exact bumpIni_other _ _ _ _ hl)
        (fun h => bumpIni_rle h _), hk.1, hk.2⟩
  · have hj' : th.nalloc ≤ j := by
      have h1 : R.1.nalloc ≤ j := hj
      rw [hna] at h1; exact Nat.le_of_succ_le h1
    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
    have hne : freshLabel g.lbase g.n g.i j ≠ lbl := fun h => by
      have := freshLabel_inj_k hn h; subst this
      have h1 : R.1.nalloc ≤ th.nalloc := hj
      rw [hna] at h1; exact absurd h1 (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
    refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, ?_,
      ⟨by show bumpIni η.rini lbl iv (freshLabel g.lbase g.n g.i j) = 0; rw [bumpIni_other _ _ _ _ hne]; exact f5.1, f5.2⟩⟩
    · change R.1.mem[t]? = some m at ht
      by_cases hlt : t < (stOf mem pairs th).mem.size
      · rw [hg.2.1 t hlt] at ht; exact f2 t m ht hl
      · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · show bumpIni η.ini lbl iv (freshLabel g.lbase g.n g.i j) = 0
      rw [bumpIni_other _ _ _ _ hne]; exact f4
  · by_cases hl : l = lbl
    · subst hl; rw [allocE_eq] at hcl; cases hcl
      exact noIallV_cl (WitAF.ni hiF.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [noIallV] using hniA)
    · rw [allocE_ne hl] at hcl; exact hnie l cl hcl
  · by_cases hxe : xl = lbl
    · rw [bornInc_born (by rw [hxe]; exact hnone0) (by rw [hxe, allocE_eq]; exact Option.some_ne_none _)]
      have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) ≤ 1 := by
        simp only [Res.one]; split <;> omega
      simp only [Res.add_apply, Res.zero_apply]
      omega
    · have h2 : Res.one (.own (freshLabel g.lbase g.n g.i th.nalloc)) (.own xl) = 0 := by simp [Res.one]; exact hxe
      simp only [Res.add_apply, Res.zero_apply]
      omega
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1512 ownXStepL_ldl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_ldlBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsLdl :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, hte⟩ := ht
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_ldlBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1517 ownXStepL_ldlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_ldlwBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsLdlw :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_ldlwBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1522 ownXStepL_new
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_newBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsNew :=
  ownXStepL_ofBU (fun _ _ _ th r ρ η cx _ Rs _ hpp hn ht hsc hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, a, _, _, hte⟩ := ht
    have hsd := hsc ρ η cx hE hT.1 htv (finv_ofB htv hi)
    rw [hte] at hsd
    have hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true := by
      rcases hsd with h | ⟨_, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals cases h
    exact stepK3_newBU (hDy := hDy) hte hniA hP hn hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS hpp hTyE hRc r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1533 ownXStepL_newBuf
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_newBufBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsNewBuf :=
  ownXStepL_ofBU (fun _ _ _ th r ρ η cx _ Rs _ _ hn ht hsc hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, τ, _, hte⟩ := ht
    have hsd := hsc ρ η cx hE hT.1 htv (finv_ofB htv hi)
    rw [hte] at hsd
    have hniA : noIallV τ = true := by
      rcases hsd with h | ⟨_, _, _, ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩⟩
      · exact h
      all_goals cases h
    exact stepK3_newBufBU (hDy := hDy) hte hniA hP hn hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS hTyE hRc r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1544 ownXStepL_bufInit
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_bufInitBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsBufInit :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    exact stepK3_bufInitBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS hTyE hRc r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1549 ownXStepL_xchgAt
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_xchgAtBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsXchgAt :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_xchgAtBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1554 ownXStepL_xchgAtF
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_xchgAtFBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsXchgAtF :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, _, hte⟩ := ht
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_xchgAtFBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1559 ownXStepL_stl
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_stlBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsStl :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, hte⟩ := ht
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_stlBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1564 ownXStepL_stlw
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_stlwBU [WrIniCB] {p : Prog} {x : AllocLabel} {n : Nat} (hP : ProgT p) (hPS : PwSkel) : OwnXStepLBU p x n IsStlw :=
  ownXStepL_ofBU (fun _ _ _ _ r _ _ _ _ _ _ _ _ ht _ hE hT htv hi hRP hDy hm hH _ hni hx hTyE hRc hr hpa _ => by
    obtain ⟨_, _, _, _, _, _, hte⟩ := ht
    refine stepC_ofKBU ?_ (tyOKE_keep hr (fun _ _ _ _ h => by rw [hte] at h; cases h) hTyE hRc)
    exact stepK3_stlwBU (hDy := hDy) hte hP hT.1 hT.2 hi hE htv hm hH hni hx hRP hPS r hr hpa)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1570 ownXStepL_k3
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStepL_k3BU {p : Prog} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepLBU p x n IsBufInit) (h2 : OwnXStepLBU p x n IsXchgAt) (h3 : OwnXStepLBU p x n IsXchgAtF)
    (h4 : OwnXStepLBU p x n IsStl) (h5 : OwnXStepLBU p x n IsStlw) (h6 : OwnXStepLBU p x n IsLdl)
    (h7 : OwnXStepLBU p x n IsLdlw) (h8 : OwnXStepLBU p x n IsNew) (h9 : OwnXStepLBU p x n IsNewBuf) :
    OwnXStepLBU p x n (fun t => exprPkg t = 3) := by
  intro g mem pairs th r hp hn ht
  generalize hte : th.term = t at ht
  cases t with
  | let_ y op e =>
    cases op with
    | bufInit a b c => exact h1 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | xchgAt a b c => exact h2 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | xchgAtF a b c d => exact h3 g mem pairs th r hp hn ⟨y, a, b, c, d, e, hte⟩
    | stl a b c => exact h4 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | stlw a b c d => exact h5 g mem pairs th r hp hn ⟨y, a, b, c, d, e, hte⟩
    | ldl a b => exact h6 g mem pairs th r hp hn ⟨y, a, b, e, hte⟩
    | ldlw a b c => exact h7 g mem pairs th r hp hn ⟨y, a, b, c, e, hte⟩
    | new a T => exact h8 g mem pairs th r hp hn ⟨y, a, T, e, hte⟩
    | newBuf a b => exact h9 g mem pairs th r hp hn ⟨y, a, b, e, hte⟩
    | _ => simp [exprPkg, opPkg] at ht
  | _ => simp [exprPkg] at ht
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1593 ownXStep_k3_of
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k3_ofBU {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepLBU p x n IsBufInit) (h2 : OwnXStepLBU p x n IsXchgAt) (h3 : OwnXStepLBU p x n IsXchgAtF)
    (h4 : OwnXStepLBU p x n IsStl) (h5 : OwnXStepLBU p x n IsStlw) (h6 : OwnXStepLBU p x n IsLdl)
    (h7 : OwnXStepLBU p x n IsLdlw) (h8 : OwnXStepLBU p x n IsNew) (h9 : OwnXStepLBU p x n IsNewBuf) :
    OwnXStepPkgBU p k arch i x n 3 :=
  ownXStepPkg_of_localBU (ownXStepL_k3BU h1 h2 h3 h4 h5 h6 h7 h8 h9)
end
end TermOwnK3.Flat

-- PORTB TermOwnK3.lean:1601 ownXStep_k3
namespace TermOwnK3.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXStep_k3BU [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} [ProgRetIall p]
    (hP : ProgT p) (hPS : PwSkel) : ∀ n, OwnXStepPkgBU p k arch i x n 3 := fun _ =>
  ownXStep_k3_ofBU (ownXStepL_bufInitBU hP hPS) (ownXStepL_xchgAtBU hP hPS) (ownXStepL_xchgAtFBU hP hPS) (ownXStepL_stlBU hP hPS)
    (ownXStepL_stlwBU hP hPS) (ownXStepL_ldlBU hP hPS) (ownXStepL_ldlwBU hP hPS) (ownXStepL_newBU hP hPS) (ownXStepL_newBufBU hP hPS)
end
end TermOwnK3.Flat

-- PORTB TermOwnK4.lean:39 Src
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
structure SrcBU (p : Prog) (g : G) (x : AllocLabel) (n : Nat) (mem : Memory) (pairs : List Ts) (th : TTh)
    (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs HP : Res) : Prop where
  gp : g.p = p
  gn : 0 < g.n
  hE : EnvOKB p η
  hT : Typed p cx th.term
  ck : TermA4.CkW p η.wit cx th.term
  tv : TvOK cx
  hF : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) cx th.env Rf
  hm : MemInvB g (CE η) (stOf mem pairs th)
  hH : MemHeldPB (CE η) (stOf mem pairs th) HP
  bf : g.boxFence = true
  nie : TermOwnX2.StoNIE (CE η)
  sto : BornMono x (CE η) (CE η)
  le : (Rf + Rs) (.own x) + HP (.own x) ≤ n + bornBit x (CE η)
  sc : ScopeD th.σs cx th.term
  px : PAx g mem pairs th
  rp : RetPw th.σs th.stack cx.ret
  dy : DyFr p annNew (progTgts p) η th.σs th.term
  ty : TyOKE g (CE η)
  rc : RecFresh g g.i th.nalloc
end
end TermOwnK4.Flat

-- ♭ mirror of W TermOwnK4 Src.tyk (W tgt_tyOKE is layer-free).
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem SrcBU.tyk {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    {E' : TEnv} {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hsub : ∀ l c, E'.sto l = some c → (CE η).sto l = some c) :
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E' ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc :=
  TermOwnK4.tgt_tyOKE hS.gn hr hsub (hS.hm.2.2.2.1.1 th.nalloc (Nat.le_refl _)).1 hS.ty hS.rc
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:60 Tgt
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
def TgtBU (p : Prog) (g : G) (x : AllocLabel) (n' : Nat) (Es : TEnv) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E r.2.2 Tot ∧
    MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
    BornMono x Es E ∧
    Tot (.own x) + HP (.own x) ≤ n' + bornBit x E ∧ TermOwnX2.Flat.AnchStepB g th Es E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
    TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:68 ownXLe_of_src
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem ownXLe_of_srcBU [WrIniCB] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n n' : Nat}
    {c0 c0' : Cfg} {th : TTh} (hth : c0.ths[i]? = some th) (hsc : ScopeAtB p i c0)
     (hvI : TermViewInv.ViewInv c0) (hI : TermOwnX2.Flat.OwnXLeBU p k arch E0 i x n c0)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc : Certified p k arch c0' i) (hnn : n' = 0 → n = 0)
    (h : ∀ ρ η cx Rf Rs HP, SrcBU p (gOf p k arch c0 i) x n c0.mem c0.pairs th ρ η cx Rf Rs HP →
      TgtBU p (gOf p k arch c0 i) x n' (CE η) c0.mem c0.pairs th) :
    TermOwnX2.Flat.OwnXLeBU p k arch E0 i x n' c0' := by
  obtain ⟨th1, E, Tot, HP, hth1, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hFI, rfl, hRP, hDy⟩, hm, hH, hbf, hnie, hsto, hle, hx0, hA, hTy, hRc, hZ, hR⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hFp := TermOwnX2.Flat.finv_ofB htv hFI
  have hS : SrcBU p (gOf p k arch c0 i) x n c0.mem c0.pairs th ρ η cx Rf Rs HP :=
    ⟨rfl, Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)), hE, hT.1, hT.2, htv, hFI, hm, hH, hbf, hnie, bornMono_refl x _, hle,
      hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT.1 htv hFp, PAx_of_step hs hc hth, hRP, hDy, hTy, hRc⟩
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨E', Tot', HP', hT', hm', hH', hnie', hsto', hle', hAS, hTy', hRc'⟩ := h ρ η cx Rf Rs HP hS r hr hpa
  have hsub := TermTyped.tysOf_thread hs hth e3 hRc
  obtain ⟨hx', hA'⟩ := hAS.1 E0 hx0 hA hm.2.2.2.1.old hm' (TermOwnX2.Flat.wrHypB hE hT.1 htv hFp hm hS.sc (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth) hr)
  refine ⟨r.2.2, E', Tot', HP', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, by rw [gOf_thread hs]; exact hbf, hnie', trivial, hle', hx', ?_, ?_, ?_, trivial, fun h => hAS.2.2 (hR h)⟩
  · rw [gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hH'
  · rw [e1, e2]; exact hA'
  · rw [gOf_thread hs]; exact TyOKE_mono hsub hTy'
  · rw [gOf_thread hs]
    exact RecFresh_sub (g := { gOf p k arch c0 i with tys := tysUpd (gOf p k arch c0 i).tys th r.2.2 })
      (g' := { gOf p k arch c0 i with tys := tysOf c0' }) hsub rfl rfl hRc'
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:96 tgt_same
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_sameBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (hR : ∀ r ∈ tstep g mem pairs th, ∃ Tot', ThInvREB g.lbase g.n g.i p (CE η) r.2.2 Tot' ∧ TotStep th.term η (Rf + Rs) Tot')
    (hsm : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    TgtBU p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨Tot', hT', hts⟩ := hR r hr
  have e := hsm r hr
  refine ⟨CE η, Tot', HP, hT', MemInv_sameB hS.hm e, TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH e.1 e.2.2.2.1, hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_eqsB e.1 e.2.2.2.1, hS.tyk hr (fun _ _ h => h)⟩
  have h1 := totStep_own_le hts x
  have h2 := hS.le
  omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:110 tgt_frame
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_frameBU {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP) (hscR : StepScopeR th.σs cx th.term)
    (hsm : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    TgtBU p g x n (CE η) mem pairs th := fun r hr hpa =>
  tgt_sameBU hS (tstepR_stepB (hDy := hS.dy) hP hS.gp (tstep_notDone hr) hscR hS.hT hS.ck hS.hF hS.hE (supI_of_memInvB hS.hm hS.gn) hS.tv hS.rp hPS hSub hSig).2 hsm r hr hpa
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:463 tgt_keep
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_keepBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (h : KeepOutB p g mem pairs th η (Rf + Rs)) : TgtBU p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨e, hT'⟩ := h r hr
  rw [e]
  exact ⟨CE η, Rf + Rs, HP, hT', hS.hm, hS.hH, hS.nie, hS.sto, hS.le, TermOwnX2.Flat.anchStep_eqsB rfl rfl, hS.tyk hr (fun _ _ h => h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:629 tgt_keepM
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_keepMBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (h : KeepOutMB p g mem pairs th η (Rf + Rs)) : TgtBU p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨e1, e2, hm', hT'⟩ := h r hr hpa
  exact ⟨CE η, Rf + Rs, HP, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH e1 e2, hS.nie, hS.sto, hS.le, TermOwnX2.Flat.anchStep_eqsB e1 e2, hS.tyk hr (fun _ _ h => h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:780 tgt_ldp
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_ldpBU {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {acq : Bool} {a : At} {n0 n1 : String} {e : Expr} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .let_ y (.ldp acq a n0 n1) e) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) : TgtBU p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.ldp acq a n0 n1) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hT := hS.hT
  rw [ht] at hT
  cases hT with
  | let_ hop _ =>
    cases hop with
    | ldp hpk _ _ =>
      obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc' _ hpk
      · rw [hteq] at hpk
        rcases hμ with rfl | rfl
        · exact tgt_keepMBU hS (ldpOwn_stepB (hDy := hS.dy) ht hP hu hpk hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
        · exact tgt_keepMBU hS (ldpPub_stepB (hDy := hS.dy) ht hP hu hpk hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
      · rw [hteq] at hpk
        exact tgt_keepMBU hS (ldpLoc_stepB (hDy := hS.dy) ht hP hu hpk hμ hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:803 tgt_pstore
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_pstoreBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (hnb : ∀ E1, BumpIf th E1)
    {c' : Cx} {y : String} {rel : Bool} {e : Expr} {pw w0 w1 : Word} {A : Address} {c : Cell} {m : Nat}
    {P : Proto2} {Tf Rv : Res}
    (hkey : tstep g mem pairs th = (storeUnits g.k g.arch pw A rel [.two] [w0, w1] 0 (stOf mem pairs th)).map
        fun s' => (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s'))
    (hmi : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.two] [w0, w1] 0 (stOf mem pairs th) → MemInvB g (CE η) s')
    (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset (.word2 (.lit m) P))
    (hini : Priv (CE η) A.label → IniAt (CE η).rc c A (.word2 (.lit m) P))
    (hv : EnvValRB (CE η) (.word2 (.lit m) P) [w0, w1] (Rv + Res.one (.wd m)))
    (hfr : FInvRB g.lbase g.n g.i ρ η th.σs (ResumeRB g.lbase g.n g.i p th.stack Rs) c' ((y, .unit, []) :: th.env) Tf) (hle : Tf + Rv ≤ Rf)
    (he : TypedK p η c' e) (htv' : TvOK c') (hRPc : RetPw th.σs th.stack c'.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e) : TgtBU p g x n (CE η) mem pairs th := by
  intro r hr _
  have hr0 := hr
  rw [hkey, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hT' : ThInvREB g.lbase g.n g.i p (CE η) (withS { th with term := e, env := (y, .unit, []) :: th.env } s') (Tf + Rs) :=
    ⟨ρ, η, c', Tf, Rs, rfl, hS.hE, he, htv', hfr, rfl, hRPc, hDy.wit rfl⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h0 := hS.le
  simp only [Res.add_apply] at h1 h0
  by_cases hq : Priv (CE η) A.label
  · have hq' := hq
    obtain ⟨⟨c0, hc0, hown0⟩, hpfN⟩ := hq'
    have ec : some c0 = some c := hc0.symm.trans hsto
    cases ec
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := TermOwnHeldQ.Flat.heldStoreAtPB (us := [.two]) hS.hm hS.hH hq hsto
      hown0 (NVP_priv hq) (OwnOKPF_cellPB hS.hm.2.1 hsto hown0 hpfN) hat (hini hq) (fun N e h => by cases h) hv
      (by simp [wc, accs, nWords, Acc.size]) rfl
    refine ⟨CE η, Tf + Rs, R2 + H0, hT', hmi s' hs', hput g.k g.arch pw rel _ rfl rfl
      (LoadCoh_of_eqB hS.hm.2.1 rfl) (fun _ => Nat.le_refl _) hS.hm.2.2.2.2.1 s' hs', hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr0 (fun _ _ h => h)⟩
    have h2 := congrArg (fun R : Res => R (.own x)) hRe
    simp only [Res.add_apply] at h2 ⊢
    have h3 : (Res.one (.wd m)) (.own x) = 0 := by simp [Res.one]
    omega
  · refine ⟨CE η, Tf + Rs, HP, hT', hmi s' hs', TermOwnHeldQ.Flat.memHeldOn_storeB hS.hH (fun l hl e => hq (e ▸ hl))
      hS.hm.2.2.1 hs', hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr0 (fun _ _ h => h)⟩
    simp only [Res.add_apply]
    omega
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:844 stpPtr_tgt
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stpPtr_tgtBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    {c₁ c' : Cx} {y : String} {rel : Bool} {a v0 v1 tk : At}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause2}
    (hterm : th.term = .let_ y (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hr : EqI c₁ r r') (hj0 : IntIdx c₁ v0 j0)
    (hj1 : IntIdx c₁ v1 j1) (hst : InState2 c₁ P j0 j1 c₂ k0' k1') (hcl : P.clauses[c₂]? = some cl')
    (hxt : (xt = .unit ∧ cl'.holds = true) ∨ (xt = .tok2 r' P j0 j1 ∧ cl'.holds = false))
    (hb : c₁.bind y xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c') (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : TgtBU p g x n (CE η) mem pairs th := by
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi.1
  have ho : cx.opaqueOK (.word2 r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hcellW : ∀ {c : Cell}, Fd c.ty (cl ρ η.wit 0 0 (.word2 r P)) →
      c.ty = .word2 (.lit (ev ρ r)) P := fun hcty => by
    have h' := hcty; simp only [cl, clI_zero] at h'; exact Fd_word2_eq h'
  rcases hμ with rfl | rfl
  · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi.1 hpk htv ho
    have hct := hcellW hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word2 (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs]))
    have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
    have hpwf : pwf2 P = true := by
      obtain ⟨-, -, -, -, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
        hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
        (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
        (peek_cell_lytB hi.1.2.1 hpk hea rfl rfl).2 hsig
        (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.1.2.2.2.1 hi.1.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.1.2.1 htv hpk rfl ho hea rfl)
      obtain ⟨_, hvr0, -⟩ := hstw
      simp only [VRF, VRb2] at hvr0; exact hvr0.1
    obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
      stp_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
    have husA : accs c.ty = some [Acc.two] := by rw [hct]; simp [accs]
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
    exact tgt_pstoreBU (hDy := hDy.letW hterm rfl) hS (TermOwnX2.bumpIf_nb hterm) (A := ⟨lab, 0⟩) key (fun s' hs' => MemInv_storeB hm hsto hown husA hval rfl s' hs')
      hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h) ⟨hvR _ _, by simp [Valid]⟩ hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
  · obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, -, hsku, -⟩ := pubPtr_viewB hi.1 hpk htv ho
    have hct := hcellW hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word2 (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs]))
    have hpwf : pwf2 P = true := by
      obtain ⟨_, _, _, _, -, -, -, -, -, -, _, hvr0⟩ :=
        loadPub_coreB (p := p) (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi.1 hE htv hm
      simp only [VRF, VRb2] at hvr0; exact hvr0.1
    obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
      stp_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
    have husc : accs c.ty = some [.two] := by rw [hct]; simp [accs]
    have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
    refine tgt_pstoreBU (hDy := hDy.letW hterm rfl) hS (TermOwnX2.bumpIf_nb hterm) (A := ⟨lab, 0⟩) key (fun s' hs' => ?_) hsto hat
      (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h) ⟨hvR _ _, by simp [Valid]⟩ hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
    by_cases hown : c.owner = some η.tid
    · exact MemInv_storeFB hm hsto hown husc hval rfl s' hs'
    · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
      exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc rfl s' hs'
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:914 stpLoc_tgt
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem stpLoc_tgtBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    {c₁ c' : Cx} {y : String} {rel : Bool} {a v0 v1 tk : At}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause2}
    (hterm : th.term = .let_ y (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hr : EqI c₁ r r') (hj0 : IntIdx c₁ v0 j0)
    (hj1 : IntIdx c₁ v1 j1) (hst : InState2 c₁ P j0 j1 c₂ k0' k1') (hcl : P.clauses[c₂]? = some cl')
    (hxt : (xt = .unit ∧ cl'.holds = true) ∨ (xt = .tok2 r' P j0 j1 ∧ cl'.holds = false))
    (hb : c₁.bind y xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c') (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) : TgtBU p g x n (CE η) mem pairs th := by
  have hi := hS.hF
  have hE := hS.hE
  have hm := hS.hm
  have hi0 := hi.1
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi0
  have hus2 : accs (cl ρ η.wit 0 0 (.word2 r P)) = some [.two] := pair_accs_cl (wit := η.wit) (Or.inl ⟨r, P, rfl⟩)
  have hcell : cellOf (Ty.loc μ (.word2 r P)) = some (μ, .word2 r P) := by simp [cellOf]
  have hpwf : pwf2 P = true := by
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, _, hvr0⟩ :=
      locCellB (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus2 hi0 hE hS.tv hm
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ := cell_targetB (bkG := False) hcell (Fd_noarr (by rw [hus2]; simp)) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs (.word2 r P))) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hat' : AtOff c.ty ad.offset (.word2 (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero] using hat
  have hini' : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word2 (.lit (ev ρ r)) P) := fun hq => by
    rcases hμ with rfl | rfl
    · have h2 : IniAt (modeIni .own η.ini η.rini) c ad (.word2 (.lit (ev ρ r)) P) := by
        simpa only [cl, clI_zero] using hini
      exact h2
    · simp only [ModeOKF, ModeOKb] at hmode
      obtain ⟨f, hf, -⟩ := hmode
      have := hq.2; simp only [CE] at this; rw [this] at hf; cases hf
  obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
    stp_frameB hi hE.2.2 (RLink_ofB hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
  have hval := storeWord2_valB (η := η) (r := r) hpwf hi1.1 hst hwv0 hwv1
  have hna : ∀ N e, cl ρ η.wit 0 0 (.word2 r P) ≠ .array (.lit N) e := fun N e h => by simp [cl] at h
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  refine tgt_pstoreBU (hDy := hDy.letW hterm rfl) hS (TermOwnX2.bumpIf_nb hterm) (A := ad) key (fun s' hs' => ?_) hsto hat' hini' ⟨hvR _ _, by simp [Valid]⟩
    hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtIB hm hsto hown hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hna hval hus2 rfl s' hs'
  · have hpub : μ = .pub := by
      rcases hμ with rfl | rfl
      · exact absurd hmode hown
      · rfl
    subst hpub
    simp only [ModeOKF, ModeOKb] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAtB hm hsto hown hf hat hini hna hval hus2 rfl s' hs'
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:976 tgt_stp
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_stpBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {rel : Bool} {a v0 v1 tk : At} {e : Expr} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (hP : ProgT p) (ht : th.term = .let_ y (.stp rel a v0 v1 tk) e) (hRP : RetPw th.σs th.stack cx.ret) : TgtBU p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.stp rel a v0 v1 tk) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hT := hS.hT
  have hCkL := hS.ck
  rw [ht] at hT hCkL
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
  have htv' := OpT_TvOK hP hop hS.tv
  cases hop with
  | stpGive hp hw hu hr hj0 hj1 _ _ hst hcl _ _ hh _ hb =>
    obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpPtr_tgtBU (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpLoc_tgtBU (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
  | stpKeep hp hw hu hr hj0 hj1 _ _ hst hcl _ _ hh hb =>
    obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpPtr_tgtBU (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inr ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpLoc_tgtBU (hDy := hS.dy) hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inr ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1031 tgt_rmw
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_rmwBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP) (hnb : ∀ E1, BumpIf th E1)
    (h : RmwOutB p g mem pairs th η x ((Rf + Rs) (.own x))) : TgtBU p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨Tot, hT', hm', hle, hk | ⟨s1, s2, pw, ad, rel, us, ws, e1, e2, hs2, e3, e4, hcell⟩⟩ :=
    h r hr hpa
  · exact ⟨CE η, Tot, HP, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH hk.1 hk.2, hS.nie, hS.sto,
      by have := hS.le; omega, TermOwnX2.Flat.anchStep_eqsB hk.1 hk.2, hS.tyk hr (fun _ _ h => h)⟩
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨hlc, hsl, c, U, Rv, hsto, hat, hini, hna, hv, hwU, hlen, hRv⟩ := hcell.resolve_left (fun h => h hq)
    have hq' := hq
    obtain ⟨⟨c0, hc0, hown0⟩, hpfN⟩ := hq'
    have ec : some c0 = some c := hc0.symm.trans hsto
    cases ec
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := TermOwnHeldQ.Flat.heldStoreAtPB hS.hm hS.hH hq hsto
      hown0 (NVP_priv hq) (OwnOKPF_cellPB hS.hm.2.1 hsto hown0 hpfN) hat (hini hq) hna hv hwU hlen
    refine ⟨CE η, Tot, R2 + H0, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB
      (hput g.k g.arch pw rel s1 e1 e2 hlc hlc.2.2 hsl s2 hs2) e3 e4, hS.nie, hS.sto, ?_, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr (fun _ _ h => h)⟩
    have h2 := congrArg (fun R : Res => R (.own x)) hRe
    have h0 := hS.le
    simp only [Res.add_apply] at h2 h0 hle ⊢
    omega
  · have hpl : PromLt s1 := fun t ht => by rw [e1]; rw [e2] at ht; exact hS.hm.2.2.1 t ht
    have hH1 : MemHeldPB (CE η) s1 HP := TermOwnHeldQ.Flat.memHeldOn_eqsB hS.hH e1 e2
    exact ⟨CE η, Tot, HP, hT', hm', TermOwnHeldQ.Flat.memHeldOn_eqsB
      (TermOwnHeldQ.Flat.memHeldOn_storeB hH1 (fun l hl e => hq (e ▸ hl)) hpl hs2) e3 e4, hS.nie, hS.sto,
      by have := hS.le; simp only [Res.add_apply] at this hle ⊢; omega, TermOwnX2.Flat.anchStep_sameB hnb, hS.tyk hr (fun _ _ h => h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1307 tgt_fetch
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_fetchBU {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .let_ y (.fetch o acq rel a v) e) (hRP : RetPw th.σs th.stack cx.ret) : TgtBU p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.fetch o acq rel a v) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hT := hS.hT
  have hCkL := hS.ck
  rw [ht] at hT hCkL
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
  have htv' := OpT_TvOK hP hop htv
  refine tgt_rmwBU hS (TermOwnX2.bumpIf_nb ht) ?_
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      rcases hc with hc | ⟨r, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨lab, pw, ru, hea, hpw, hnwr, hne, hcell⟩ :=
          pubIntCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hi.1 hE htv hm
        have hrt : fetchRtTy (.ptr .pub ru) = .int := by
          cases ru <;> simp [fetchRtTy, wordOf]
          exact (hnwr _ _ rfl).elim
        exact fetchCell_outB (hDy := hS.dy) ht hp rfl hu hsub hb ⟨he, hck⟩ htv'
          ⟨⟨lab, 0⟩, pw, _, hea, by simp [addrOf, hpw], hrt, hne, hcell⟩ hi hE hRP
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        rcases hμ with h | h <;> cases h
    · subst hteq
      rcases hc with hc | ⟨r, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
        obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, -⟩ :=
          locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp (Or.inr rfl)
            (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi.1 hE htv hm
        have hrt : fetchRtTy (.loc μr ru) = .int := by
          cases ru <;> simp [fetchRtTy, wordOf]
          simp [skel, etok, close, substTs] at hsku
        refine fetchCell_outB (hDy := hS.dy) ht hp rfl hu hsub hb ⟨he, hck⟩ htv'
          ⟨ad, pw, _, hea, haddr, hrt, hne, fun s1 ws hl hp => ?_⟩ hi hE hRP
        obtain ⟨hvr, -, hm1⟩ := hld s1 ws hl hp
        exact ⟨hm1, by simpa [VRF, VRb2] using hvr, fun s1' hm1' w ⟨m, hw⟩ s2 hs2 =>
          hsto s1' [w] hm1' (intValB (ρ := ρ) hw) rfl s2 hs2⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp <;> subst hteq <;>
    · cases u <;> simp [wordOf] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rename_i r P
      have hpwf := wordRef_pwfB hp (by first | exact .inl rfl | exact .inr rfl) hμ hi.1 hE htv hm
      have hg : P.ghost = false := by
        have := pwf_epochOK hpwf hep
        unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1.2
      exact fetchRef_outB (hDy := hS.dy) ht hp (by first | exact .inl rfl | exact .inr rfl) hμ hg hpwf hj (.inl ⟨hep, heq, hb⟩)
        ⟨he, hck⟩ htv' hi hE htv hm hS.rp
  | fetchShare hp hw hep hj heq hok hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp <;> subst hteq <;>
    · cases u <;> simp [wordOf] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rename_i r P
      have hpwf := wordRef_pwfB hp (by first | exact .inl rfl | exact .inr rfl) hμ hi.1 hE htv hm
      have hg : P.ghost = false := by
        have hok' := hok
        unfold fetchOK at hok'; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok'
        exact hok'.1.1.1.1
      exact fetchRef_outB (hDy := hS.dy) ht hp (by first | exact .inl rfl | exact .inr rfl) hμ hg hpwf hj
        (.inr ⟨_, hep, heq, hok, hb⟩) ⟨he, hck⟩ htv' hi hE htv hm hS.rp
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1597 tgt_cas
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_casBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .cas acq rel w e v t ok fail) (hRP : RetPw th.σs th.stack cx.ret) : TgtBU p g x n (CE η) mem pairs th := by
  have hsc' : StepScope cx (.cas acq rel w e v t ok fail) :=
    stepScope_of (by rw [← ht]; exact hS.sc) (fun _ _ _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hT := hS.hT
  have hCk0 := hS.ck
  refine tgt_rmwBU hS (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [ht] at h; cases h) ?_
  have hT0 := hT
  rw [ht] at hT0 hCk0
  have hcasW : ∀ {μ r P}, (cx.peek w = .ok (.ptr μ (.word r P)) ∨ cx.peek w = .ok (.loc μ (.word r P))) →
      (μ = .own ∨ μ = .pub) → P.ghost = false → RmwOutB p g mem pairs th η x ((Rf + Rs) (.own x)) := by
    intro μ r P hpk hμ hg
    rcases hpk with hpk | hpk
    · exact casW_typedB (hDy := hS.dy) ht hpk rfl rfl hμ hg (wordRef_pwfB hpk (.inl rfl) hμ hi.1 hE htv hm)
        (fun hst nw hnwv => by
          obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := casWordCellB (acq := acq) (rel := rel) (g := g)
            (mem := mem) (pairs := pairs) hpk hμ hg hst hnwv hi.1 hE htv hm
          exact ⟨⟨lab, 0⟩, pw, rw, hea, by simp [addrOf, hpw], hne, hcell⟩) hT hS.ck hi hE htv hm hRP
    · exact casW_typedB (hDy := hS.dy) ht hpk rfl rfl hμ hg (wordRef_pwfB hpk (.inr rfl) hμ hi.1 hE htv hm)
        (fun hst _ hnwv => wordLocCellB (acq := acq) (rel := rel) (g := g)
          (mem := mem) (pairs := pairs) hpk hμ hg hst hnwv hi.1 hE htv hm) hT hS.ck hi hE htv hm hRP
  cases TermA4.CkW_inv_cas hCk0 with
  | casCell hpk hnw0 hc hone haff hpe hu hsube hsubv _ hb hok hfail =>
    rcases hsc' _ hpk with ⟨μ, r, P, hteq | hteq, hμ⟩ | ⟨u, rfl | rfl, hnw⟩
    · subst hteq; simp [wordOf] at hnw0
    · subst hteq; simp [wordOf] at hnw0
    · rcases hc with hc | ⟨_, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
        subst hc
        have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv
          (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
        exact casC_outB (hDy := hS.dy) ht hpk rfl hone hpe hu hsube hsubv hb hok.tk hfail.tk
          (plainCellPtrB hpk hone ho hi.1 hE htv hm) hi hE htv hRP
      · simp [cellOf] at hc
    · rcases hc with hc | ⟨_, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
        subst hc
        have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv
          (peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
        refine casC_outB (hDy := hS.dy) ht hpk rfl hone hpe hu hsube hsubv hb hok.tk hfail.tk (fun nw hval => ?_) hi hE htv hRP
        obtain ⟨ad, pw, μr, ru, hea, haddr, -, -, -, hne, hld, hsto, -⟩ :=
          locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk (.inr rfl) ho
            (accs_cl_one hone) hi.1 hE htv hm
        exact ⟨ad, pw, _, hea, haddr, hne, fun s1 ws hl hp => ⟨(hld s1 ws hl hp).2.2,
          fun s1' hm1 s2 hs2 => hsto s1' [nw] hm1 hval rfl s2 hs2⟩⟩
      · simp [cellOf] at hc
  | casShare hpk hw | casTake hpk hw | casEpoch hpk hw =>
    rcases hsc' _ hpk with ⟨μ, r, P, hteq, hμ⟩ | ⟨u, hteq, hnw⟩
    · cases hg : P.ghost
      · rcases hteq with rfl | rfl
        · exact hcasW (.inl hpk) hμ hg
        · exact hcasW (.inr hpk) hμ hg
      · exact (cas_ghost_absurd (by rw [← ht]; exact hT) hpk hteq
          (wordRef_pwfB hpk hteq hμ hi.1 hE htv hm) hg).elim
    · rw [hnw] at hw; cases hw
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1855 tgt_casp
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_caspBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail) (hRP : RetPw th.σs th.stack cx.ret) : TgtBU p g x n (CE η) mem pairs th := by
  have hsc' : StepScope cx (.casp acq rel w e0 e1 v0 v1 t ok fail) :=
    stepScope_of (by rw [← ht]; exact hS.sc) (fun _ _ _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hRL := RLink_ofB hE.2.1 hE.2.2
  refine tgt_rmwBU hS (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [ht] at h; cases h) ?_
  have hT0 := hS.hT
  have hCk0 := hS.ck
  rw [ht] at hT0 hCk0
  cases TermA4.CkW_inv_casp hCk0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    obtain ⟨μ, u, ht', hμ, -⟩ := hsc' _ hp
    obtain ⟨r, P⟩ : ∃ r P, epairOf _ = some (r, P) := ⟨_, _, hwe⟩
    have hu' : ∃ r P, u = .epair r P := by
      rcases ht' with rfl | rfl <;> cases u <;> simp [epairOf] at hwe <;> exact ⟨_, _, rfl⟩
    obtain ⟨r, P, rfl⟩ := hu'
    have hu : (∃ r' P', Ty.epair r P = .word2 r' P') ∨ (∃ r' P', Ty.epair r P = .epair r' P') := .inr ⟨_, _, rfl⟩
    obtain ⟨R, ws, hvr⟩ := pairRef_vrB (g := g) (mem := mem) (pairs := pairs) hp ht' hμ hu hi.1 hE htv hm
    have hpwf : pwfE P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    have hiok := bindRB hb hi hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    refine casp_outB (hDy := hS.dy) ht hp ht' hμ hu hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 => storeEPair_valB hpwf ⟨_, _, hn0, hn1⟩) (fun n0 n1 hn0 hn1 => ?_) hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    refine ⟨.zero, ⟨?_, by simp [cl, Valid]⟩, rfl⟩
    simp only [cl, clI_zero, VRRB]
    exact ⟨⟨hpwf, _, _, by rw [List.map_cons, List.map_cons, List.map_nil, hn0, hn1]⟩, trivial⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' hep hbump _ hb hok hfail =>
    have hiok := bindRB (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    exact caspW_outB (hDy := hS.dy) ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | caspMove hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' hb hok hfail =>
    have hiok := bindRB hb hi hRL (show VRRB ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    exact caspW_outB (hDy := hS.dy) ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | caspTake hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' _ hb hok hfail =>
    have hiok := bindRB (rt := .unit) (ws := []) (R := .one (.rg _)) hb hi hRL rfl (Lay_etok_unit rfl)
    exact caspW_outB (hDy := hS.dy) ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:1948 tgt_box
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_boxBU {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hX : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (hnb : ∀ E1, BumpIf th E1)
    (h : BoxOutB p g mem pairs th η (Rf + Rs)) : TgtBU p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨E, hT, hm, hsto, hH, hXE, hini, hri⟩ := h r hr hpa
  exact ⟨E, Rf + Rs, HP, hT, hm, hH HP hX.hH, fun l c hc => hX.nie l c (by rw [← hsto]; exact hc),
    fun h => by rw [hsto] at h; exact h, by rw [bornBit_congr hsto]; exact hX.le,
    TermOwnX2.Flat.anchStep_genB hXE (hnb E) (fun _ _ h _ => by rw [← hsto]; exact h)
      (fun _ _ => by rw [hini]; exact Nat.le_max_left _ _) (fun l h0 hl => absurd (by rw [hsto]; exact h0) hl)
      (fun _ _ => Or.inl (by rw [hri]; exact Nat.le_refl _)) (fun h l => by rw [hri, hini]; exact h l), hX.tyk hr (fun _ _ h => by rw [← hsto]; exact h)⟩
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2445 tgt_inl
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_inlBU {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : SrcBU p g xl n mem pairs th ρ η cx Rf Rs HP) {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtBU p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkL := hX.ck
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop hX.tv
    cases hop with
    | inl _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum t τ) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useRB (bkG := False) hu hX.hF hX.hE.2.2
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum t τ) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · apply tgt_boxBU hX (TermOwnX2.bumpIf_nb hterm)
        cases hrb : isBoxed rt with
        | false => exact inlB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK hX.tv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu hX.tv).2.1
            exact inlBB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl) hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · have h : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs (.sum t' τ)).tier ≠ .boxed :=
          fun t' c₁' hu' => by
            rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
            rw [← hsk]; exact hS
        exact tgt_frameBU hP hX (by rw [hterm]; exact h) (same_inlRB hterm h hX.hT hX.hF) hPS hSub hSig
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2483 tgt_inr
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_inrBU {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : SrcBU p g xl n mem pairs th ρ η cx Rf Rs HP) {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtBU p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkL := hX.ck
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop hX.tv
    cases hop with
    | inr _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum τ t) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useRB (bkG := False) hu hX.hF hX.hE.2.2
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum τ t) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · apply tgt_boxBU hX (TermOwnX2.bumpIf_nb hterm)
        cases hrb : isBoxed rt with
        | false => exact inrB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK hX.tv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu hX.tv).2.1
            exact inrBB_outB (hDy := hX.dy) hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl) hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · have h : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs (.sum τ t')).tier ≠ .boxed :=
          fun t' c₁' hu' => by
            rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
            rw [← hsk]; exact hS
        exact tgt_frameBU hP hX (by rw [hterm]; exact h) (same_inrRB hterm h hX.hT hX.hF) hPS hSub hSig
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2521 tgt_case
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_caseBU {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : SrcBU p g xl n mem pairs th ρ η cx Rf Rs HP) {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtBU p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkC := hX.ck
  rw [hterm] at hT0 hCkC
  cases hT0 with
  | case hu hb1 he1 hb2 he2 =>
    obtain ⟨u, v, c₁, c₂, c₃, hu, hb1, he1, hb2, he2⟩ : ∃ u v c₁ c₂ c₃,
        cx.use a = .ok (.sum u v, c₁) ∧ c₁.bind x u = .ok c₂ ∧ Typed p c₂ e₁ ∧
        c₁.bind y v = .ok c₃ ∧ Typed p c₃ e₂ := ⟨_, _, _, _, _, hu, hb1, he1, hb2, he2⟩
    have hck12 := TermA4.CkW_case hCkC hu hb1 hb2
    obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useRB (bkG := False) hu hX.hF hX.hE.2.2
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have htv12 := case_TvOK hu hb1 hb2 hX.tv
      have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK hX.tv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu hX.tv).2.1
      have hsg := lay_closed (ρ := ρ) hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl
      exact tgt_boxBU hX (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [hterm] at h; cases h) (caseB_outB (bkG := False) (hDy := hX.dy) hterm hX.gn hb1 ⟨he1, hck12.1⟩ htv12.1 hb2 ⟨he2, hck12.2⟩ htv12.2 hi1 hle hea hvV hv hl hS hsg
        hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu))))
    · have hnb : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs t').tier ≠ .boxed := fun t' c₁' hu' => by
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← tier_of_eskel hl.2.1]; exact hS
      exact tgt_frameBU hP hX (by rw [hterm]; exact hnb) (same_caseRB hterm hnb hX.hT hX.ck hX.hF hX.hE hX.tv) hPS hSub hSig
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:2562 tgt_easy
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_easyBU {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP) (h : EasyK4 th.term) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hpub : ∀ y a e, th.term = .let_ y (.publish a) e → TgtBU p g x n (CE η) mem pairs th) :
    TgtBU p g x n (CE η) mem pairs th := by
  have hsc := hS.sc
  cases ht : th.term with
  | let_ y op e =>
    rw [ht] at h hsc
    cases op with
    | inl τ a => exact tgt_inlBU hP hS ht hPS hSub hSig
    | inr τ a => exact tgt_inrBU hP hS ht hPS hSub hSig
    | intoRgn rn a =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | mkTicket a1 a2 a3 a4 a5 =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | claim a1 a2 =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | publish a => exact hpub _ _ _ ht
    | mkWord a1 a2 a3 a4 => exact tgt_keepBU hS (mkWord_stepB (hDy := hS.dy) ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | mkWord2 a1 a2 a3 a4 a5 => exact tgt_keepBU hS (mkWord2_stepB (hDy := hS.dy) ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | mkEPair a1 a2 a3 a4 => exact tgt_keepBU hS (mkEPair_stepB (hDy := hS.dy) ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | ldp a1 a2 a3 a4 => exact tgt_ldpBU hP hS ht hRP hPS
    | stp a1 a2 a3 a4 a5 => exact tgt_stpBU hS hP ht hRP
    | fetch a1 a2 a3 a4 a5 => exact tgt_fetchBU hP hS ht hRP
    | _ => exact False.elim h
  | cas acq rel w e v t ok fail => exact tgt_casBU hS ht hRP
  | casp acq rel w e0 e1 v0 v1 t ok fail => exact tgt_caspBU hS ht hRP
  | case a y1 e1 y2 e2 => exact tgt_caseBU hP hS ht hPS hSub hSig
  | _ => rw [ht] at h; exact False.elim h
end
end TermOwnK4.Flat

-- PORTB TermOwnK4.lean:411 tgt_publish
namespace TermOwnK4.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
theorem tgt_publishSU {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {a : At} {e : Expr} (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP)
    (hterm : th.term = .let_ y (.publish a) e) (hPS : PwSkel) : TgtBU p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨rt, ws, E1, Tot', -, hT', hm', e1, e2, hle, hx, hsn⟩ := pub_stepS (hDy := hS.dy) hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    (pubScope_of (by rw [← hterm]; exact hS.sc)) hS.rp hPS r hr
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrinkB hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    fun h => by rw [hx.2.2.2.1] at h; exact h, ?_,
    TermOwnX2.Flat.anchStep_shrinkB (ext_shrinkB hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2 hx.2.2.2.2.2.1, hS.tyk hr (fun l c h => by rw [← hx.2.2.2.1]; exact h)⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  rw [bornBit_congr hx.2.2.2.1]
  simp only [Res.add_apply] at h1 h3
  omega
end
end TermOwnK4.Flat


namespace TermOwnK4.Flat
open TermSound.Flat TermStep.Flat TermOwnX2.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- The package-4 easy-step target with the publish case discharged by the shadow publish. -/
theorem tgt_easySU {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat}
    {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : SrcBU p g x n mem pairs th ρ η cx Rf Rs HP) (h : EasyK4 th.term) (hRP : RetPw th.σs th.stack cx.ret)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TgtBU p g x n (CE η) mem pairs th :=
  tgt_easyBU hP hS h hRP hPS hSub hSig (fun _ _ _ ht => tgt_publishSU hP hS ht hPS)
end TermOwnK4.Flat

namespace TermOwnK4.Flat
open TermSound.Flat TermStep.Flat TermOwnX2.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnHeldQ.Flat TermTyped.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- B6: package 4 (word/pub/cas/ldp/stp/sum ops) with the shadow publish; no window premise. -/
theorem ownXStep_k4SU [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {i : Nat} {x : AllocLabel} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ n, TermOwnX2.Flat.OwnXStepPkgBU p k arch i x n 4 := by
  intro n E0 c0 c0' th hth hq hsc hvI hI hs hc
  exact ownXLe_of_srcBU hth hsc hvI hI hs hc id fun ρ η cx Rf Rs HP hS => tgt_easySU hP hS (easyK4_of_pkg hq) hS.rp hPS hSub hSig

/-- B6: `OwnXLeBU` along a certified solo run, with no publish-window premise (W's `run_ind_win`, generic). -/
theorem ownXLe_runSU {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat}
    {c c2 : Cfg} (hT : OwnXStepTBU p k arch i x n) (hPr : OwnXStepPBU p k arch i x n)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0)
    (hvI : TermViewInv.ViewInv c) (h0 : OwnXLeBU p k arch E0 i x n c) (hTA : TermTyped.TidAt i c E0)
    (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) : OwnXLeBU p k arch E0 i x n c2 :=
  (TermOwnX2.run_ind_win (Q := fun c0 => ScopeAtB p i c0 ∧ TermViewInv.ViewInv c0)
    (fun c0 h1 h2 _ => ⟨hQ c0 h1 h2, TermViewInv.viewInv_solo hvI h1⟩)
    (fun c0 c0' _ hI hq hs hc => hT E0 c0 c0' hq.1 hq.2 hI hs hc)
    (fun c0 a v w _ hI hw hc => hPr E0 c0 a v w hI hw hc)
    (fun _ _ h1 hI hs => ownXLe_extBU hI hs (TermTyped.tidAt_solo h1 hTA)) h0 h hc2).1
end TermOwnK4.Flat

namespace TermOwnK4.Flat
open TermSound.Flat TermStep.Flat TermOwnX2.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnHeldQ.Flat TermTyped.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
/-- B6: the ♭ resource clause along a certified solo run, all packages (packages 1–3 ported, package 4 with the shadow
publish), no publish-window premise. -/
theorem ownXLe_runAllSU [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat} {c c2 : Cfg} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0)
    (hvI : TermViewInv.ViewInv c) (h0 : OwnXLeBU p k arch E0 i x n c) (hTA : TermTyped.TidAt i c E0)
    (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) : OwnXLeBU p k arch E0 i x n c2 :=
  ownXLe_runSU (ownXStepT_of_pkgsBU (ownXStep_k1BU hP hPS hSub hSig n) (ownXStep_k2BU hP hPS n) (ownXStep_k3BU hP hPS n)
    (ownXStep_k4SU hP hPS hSub hSig n)) (ownXStepP_allBU n) hQ hvI h0 hTA h hc2
end TermOwnK4.Flat

