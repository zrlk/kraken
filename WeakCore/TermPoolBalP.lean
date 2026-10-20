import WeakCore.TermPoolSplit

/-! The thread-step pool members `poolBalT`/`poolKnetT`/`poolRidT` in form P:
`IneqH` gains the stepper's released pool `pld` on its RHS, instantiated
at `plDis pl i s'`.  The defs below are the form-P texts as named stand-ins (`IneqHP`, `pool*TP`).  Proofs: copies of `TermPoolBal.keyT_pool` / `pool*T_of` with
`plStep_le` replaced by the sharp `TermPoolSplit.plStep_split`. -/

namespace TermPoolBalP
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh TermPoolStaging TermPoolBal TermPoolSplit
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (form P) The thread step's inequality with the released stepper pool `pld` on the right. -/
def IneqHP (Tot' HP' HS' C F Rf Rs H : Res) (s s' : St) (cr cr' db db' plh δ pld : Ts → Res) : Prop :=
  ∃ Fd : List Ts, (∀ t, δ t ≠ .zero → t ∈ Fd) ∧
    Tot' + (HP' + HS') + pSum s' cr' + pSum s' plh + Res.sum (Fd.map δ) + pSum s db + C ≤
      Rf + Rs + H + pSum s cr + pSum s pld + pSum s' db' + F

/-- (form P) `poolBalT` at `IneqHP`. -/
def poolBalTP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  MintClosedT p k arch Sp Init MintOK c0 → PromNodupR p k arch Sp c0 →
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ dc dh plh : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ →
    (∀ t, dc t + dh t ≤ δ t) → PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) →
    IneqHP Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) (cr i) cr' (db i) db'
      plh δ (plDis pl i (stOf r.1 r.2.1 r.2.2)) →
    ∃ M, MintOK M ∧
      thSum c'.ths.size (fun j => upd Tot i Tot' j +
          pSumAt c' j (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh j) + upd HP i HP' j) + HS' ≤
        Init + M + thSum c'.ths.size (fun j => pSumAt c' j (upd db i db' j))

/-- (form P) `poolKnetT` at `IneqHP`. -/
def poolKnetTP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  AllocGT p k arch Sp Init MintOK c0 → TicketFreeRun p k arch Sp c0 → PromNodupR p k arch Sp c0 →
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ dc dh plh : Ts → Res} {rc : Nat → Nat},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ →
    (∀ t, dc t + dh t ≤ δ t) → PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) → (∀ t, TermPlant.CrKeys (plh t)) →
    (∀ t, TermPlant.CrKeys (dh t)) →
    IneqHP Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) (cr i) cr' (db i) db'
      plh δ (plDis pl i (stOf r.1 r.2.1 r.2.2)) →
    ClaimAt th.term C F → OwnFreshZ c Tot HP HS cr →
    RidOK c Tot HP HS (crPl cr pl) db rc → rc i ≤ η.rid →
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS'
      (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh) (upd db i db') key

/-- (form P) `poolRidT` at `IneqHP`. -/
def poolRidTP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  TicketFreeRun p k arch Sp c0 → PromNodupR p k arch Sp c0 →
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ dc dh plh : Ts → Res} {rc : Nat → Nat},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ →
    (∀ t, dc t + dh t ≤ δ t) → PoolInv Init MintOK c Eg Tot HP HS cr db pl →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) →
    IneqHP Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) (cr i) cr' (db i) db'
      plh δ (plDis pl i (stOf r.1 r.2.1 r.2.2)) →
    ClaimAt th.term C F → RidOK c Tot HP HS (crPl cr pl) db rc → rc i ≤ η.rid →
    ∃ rc', RidOK c' (upd Tot i Tot') (upd HP i HP') HS' (crN cr pl i cr' (stOf r.1 r.2.1 r.2.2) plh dc dh)
      (upd db i db') rc'

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **One key across a thread step at `crN`** (`keyT_pool` at form P: the released pool pays). -/
theorem keyT_poolP (hN : PromNodupR p k arch Sp c0) {c cq : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {Totq HPq HSq C F : Res} {crq dbq δ dc dh plh : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c cq Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hdd : ∀ t, dc t + dh t ≤ δ t)
    (hI : IneqHP Totq HPq HSq C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) (cr i) crq
      (db i) dbq plh δ (plDis pl i (stOf r.1 r.2.1 r.2.2)))
    (key : Key) (b : Nat) (hroom : KeyLoad c Tot HP HS (crPl cr pl) key + F key ≤ b + KeyDebt c db key) :
    KeyLoad cq (upd Tot i Totq) (upd HP i HPq) HSq (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh) key ≤
      b + KeyDebt cq (upd db i dbq) key
 :=
  TermPoolBal.keyT_poolG hN X Y hdd hI key b hroom (plStep_split hN X pl plh key)

/-- **`poolBalT`** at form P. -/
theorem poolBalTP_of : poolBalTP p k arch Sp Init MintOK c0 := by
  intro hM hN c cq Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs Eo Totq HPq HSq C F crq dbq δ dc dh plh X Y Z hdd hP
    _ hI
  obtain ⟨M, hMo, hb⟩ := hP.bal
  refine ⟨M + F, hM X Y (Z.toC _ _ _ _ _) M hMo, Res.le_def.2 fun key => ?_⟩
  have hold := hb key
  have e1 := bal_key c Tot HP HS (crPl cr pl) key
  have e2 := debt_key c db key
  simp only [Res.add_apply] at hold e1
  have h := keyT_poolP (pl := pl) hN X Y hdd hI key (Init key + M key + F key) (by omega)
  have g1 := bal_key cq (upd Tot i Totq) (upd HP i HPq) HSq (crN cr pl i crq (stOf r.1 r.2.1 r.2.2) plh dc dh) key
  have g2 := debt_key cq (upd db i dbq) key
  simp only [Res.add_apply] at g1 ⊢
  omega

/-- **`poolKnetT`** at form P. -/
theorem poolKnetTP_of : poolKnetTP p k arch Sp Init MintOK c0 := by
  intro hb1 hres hN c cq Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs Eo Totq HPq HSq C F crq dbq δ dc dh plh rc
    X Y Z hdd hP _ _ _ hI hcl hof hrc hle key hk
  have hroom : KeyLoad c Tot HP HS (crPl cr pl) key + F key ≤ 1 + KeyDebt c db key := by
    by_cases hF : F key = 0
    · have := hP.knet key hk
      rw [keyNet_iff] at this
      omega
    · exact room_pool hb1 hres X Y Z hcl hP.tag hof hrc hle key hk hF
  exact keyT_poolP hN X Y hdd hI key 1 hroom

/-- **`poolRidT`** at form P. -/
theorem poolRidTP_of : poolRidTP p k arch Sp Init MintOK c0 := by
  intro hres hN c cq Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs Eo Totq HPq HSq C F crq dbq δ dc dh plh rc
    X Y Z hdd _ _ hI hcl hrc hle
  have htid : η.tid = i := Y.2.1
  have hleq : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  obtain ⟨-, hU, hmono⟩ := TermOnce.fresh_bump hleq
  refine ⟨TermOnce.ridSet rc η.tid (η.rid + 1), fun n hn key hkey => ?_⟩
  have hn0 : ¬ TermOnce.RidUsed rc n := fun h => hn (hmono n h)
  have hnf : n ≠ ridNext η := fun e => hn (e ▸ hU)
  have hcl : ∀ j, ¬ (C = Res.one (.ep n j) ∧ F = Res.one (.rg n)) := fun j ⟨h1, h2⟩ => by
    obtain ⟨x, w, tk, e, he⟩ := hcl n j h1 h2
    have h := hres c X.run i th X.hth
    rw [he] at h
    simp [exprNoTicket, opTicket] at h
  have hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F := Z.2.2.2.2.2.2.1
  have hF0 : F key = 0 := by
    rcases hkey with rfl | rfl
    · rcases TermOnce.MintStep_rg hMS n with h0 | ⟨e, -⟩ | ⟨j, h1, h2⟩
      · exact h0
      · exact absurd e hnf
      · exact absurd ⟨h1, h2⟩ (hcl j)
    · rcases TermOnce.MintStep_wd hMS n with h0 | ⟨e, -⟩
      · exact h0
      · exact absurd e hnf
  have hold : KeyLoad c Tot HP HS (crPl cr pl) key ≤ KeyDebt c db key := hrc n hn0 key hkey
  have h := keyT_poolP (pl := pl) hN X Y hdd hI key 0 (by omega)
  unfold KeyLoad KeyDebt at h
  omega

end

end TermPoolBalP

#print axioms TermPoolBalP.keyT_poolP
#print axioms TermPoolBalP.poolBalTP_of
#print axioms TermPoolBalP.poolKnetTP_of
#print axioms TermPoolBalP.poolRidTP_of
