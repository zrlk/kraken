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
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y hS hm
  obtain ⟨hCE, -, hE, hT, htv, hF, -⟩ := Y
  have hc : Certified p k arch c i := by
    obtain ⟨c'', hs, hn⟩ := X.cert
    exact ⟨c'', .thread X.hc' hs, hn⟩
  have hw := (hrun X S hS c (.refl _) hc).2 th X.hth
  rw [← hCE] at hw
  have hA := TermTyped.anchR_start hm (by rw [hCE]; exact X.inv.riniCoh i th S X.hth)
    (fun l cl f hs hp => by rw [hCE] at hs hp; exact X.inv.frlt l cl f (cutSto_sub hs) hp)
  have hFi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv (htv.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF
  exact hw ρ η cx hE hT.1 htv hFi hm (Ext_refl (Coh_CE η) (CohR_CE η)) hA.1 hA.2.2.1

end

end TermWin

#print axioms TermWin.winM_of
