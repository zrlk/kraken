import WeakCore.TermCohLe

/-!
# TermWin: `NoHold` at a publish (`win`, T6)

`win` is the run premise `CertRunC` read at the stepping configuration itself (the empty solo
run, certified because its successor is): `NoHoldPub` there is `PubWinS`, which applies at any
typing of the frame whose memory invariant holds.
-/

namespace TermWin
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermTyped TermCert
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(T6) `PubWinT` at a thread step**, at the step's typing `η` with its memory invariant. -/
theorem winM_of (hrun : TermCohLe.CertRunC p k arch Sp Init MintOK c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) →
      PubWinT (CE η) (stOf c.mem c.pairs th) th := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y hS hm0
  obtain ⟨ρ1, η1, cx1, Rf1, Rs1, hCE0, -, hE, hT, htv, hF, -, -, hm, -, -, hrp, hDy⟩ := ThSysAt.env X.inv.clo hS
  have hCE1 : CE η1 = Cut Eg i S := hCE0
  have hCE : CE η = CE η1 := Y.1.trans hCE1.symm
  rw [hCE]
  have hc : Certified p k arch c i := by
    obtain ⟨c'', hs, hn⟩ := X.cert
    exact ⟨c'', .thread X.hc' hs, hn⟩
  have hw := (hrun X S hS c (.refl _) hc).2 th X.hth
  rw [← hCE1] at hw
  have hTy : TyOKE (gOf p k arch c i) (CE η1) := by rw [hCE1]; exact (X.inv.tyRec X.hth S).1
  have hA := TermTyped.anchR_start hm (by rw [hCE1]; exact X.inv.riniCoh i th S X.hth)
    (fun l cl f hs hp => by rw [hCE1] at hs hp; exact X.inv.frlt l cl f (cutSto_sub hs) hp)
  have hFi : FInv ρ1 η1 th.σs (Resume p th.stack) cx1 th.env :=
    FInvR_FInv (htv.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs1 E rd ws R h) hF
  exact hw ρ1 η1 cx1 hE hT.1 htv hFi hm (Ext_refl (Coh_CE η1) (CohR_CE η1)) hA.1 hA.2.2.1 hTy hDy hrp

end

end TermWin

#print axioms TermWin.winM_of
