import WeakCore.TermPlantFul

/-! # TermPlantOpG: `PlantOp`'s window clauses from `PlantAtT` (T7b)

`PlantOp` (the plant facts an own-path op on an own frontier cell needs) splits into
the window clauses W1–W3 and the cover part (the credited items `Gs`).  W2 and W3 are
`PlantAtT` (A) and (B); W1 at the taken step is (C) with `promViewLt_run`
(`plantOp_W1T`).  What is left as a named per-step fact is the cover part,
`PlantOpG`, at any window bound meeting (A)–(C).
-/

namespace TermPlantOpG
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The cover part of `PlantOp` at a window bound `wB`. -/
def CoverAt (s : St) (E : TEnv) (cr : Ts → Res) (l : AllocLabel) (c : Cell) (wB : Ts) : Prop :=
  ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
    (Gs.map (·.1)).Nodup ∧ (∀ x ∈ Gs, TermPlant.CrItem E s cr l c x) ∧
    ∀ o tw, InitRr E c l o → ¬ VisU E ⟨l, o⟩ → TermPlant.LowOwn s ⟨l, o⟩ tw → tw ≤ wB →
      TermPlant.OverT E s ⟨l, o⟩ tw →
      ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
        x.2.2.2.2.2 i = true

/-- (T7b, per step) **The cover part of `PlantOp`**: at an own-path op on an own
frontier cell, for every window bound meeting `PlantAtT` (A)–(C), the credited items
covering the overtaken units below it.  (R4) The items are credited at the credits plus the
pool credits, `cr i + pl i`, for any pool credits `pl` meeting `Q` (the pool clause). -/
def PlantOpG (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Q : Cfg → GEnv → (Nat → Ts → Res) → (Nat → Ts → Res) → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {pl : Nat → Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    Q c Eg cr pl → TermPlant.OwnFrOp (CE η) cx th → ∀ lab cl, (CE η).sto lab = some cl → cl.owner = some (CE η).tid →
      (CE η).pfr lab ≠ none → TermPlant.OpTgt th lab → ∀ wB : Ts,
      (∀ t m, c.mem[t]? = some m → m.loc.label = lab → t ≤ wB → t ∈ th.promises ∨ t ≤ th.vs.coh m.loc) →
      (∀ t m, t ∈ FpAt (CE η) ⟨lab, 0⟩ → c.mem[t]? = some m → m.loc.label = lab → wB < t) →
      (1 ≤ Rf (.own lab) → ∃ mB : Msg, c.mem[wB]? = some mB ∧ wB ∈ r.2.2.promises ∧ r.2.2.vs.vWr ≤ mB.view) →
      CoverAt (stOf c.mem c.pairs th) (CE η) (fun t => cr i t + pl i t) lab cl wB

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`plantOp`** (the `TermMain` field, W1 at the taken step) from `OwnKeyT`,
`PlantAtT` and the cover part `PlantOpG`, at `cr i + pl i` (R4). -/
theorem plantOp_of {Q : Cfg → GEnv → (Nat → Ts → Res) → (Nat → Ts → Res) → Prop} (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hK : TermPlantFul.OwnKeyT p k arch Sp Init MintOK c0)
    (hA : TermPlantFul.PlantAtT p k arch Sp Init MintOK c0) (hG : PlantOpG p k arch Sp Init MintOK c0 Q)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {pl : Nat → Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hq : Q c Eg cr pl) (hOF : TermPlant.OwnFrOp (CE η) cx th) (lab : AllocLabel) (cl : Cell) (hsto : (CE η).sto lab = some cl)
    (hown : cl.owner = some (CE η).tid) (hpf : (CE η).pfr lab ≠ none) (htg : TermPlant.OpTgt th lab) :
    TermPlant.PlantOp (gOf p k arch c i) c.mem c.pairs th (CE η) (fun t => cr i t + pl i t) (· = r) lab cl := by
  obtain ⟨cl1, hsto1, hown1, hkey⟩ := hK X Y hOF.1 htg
  obtain ⟨wB, hAo, hB, hC⟩ := hA X Y hsto hown hpf
  obtain ⟨Gs, hnd, hit, hcov⟩ := hG X Y hq hOF lab cl hsto hown hpf htg wB hAo hB hC
  obtain ⟨mB, hmB, hwB, hle⟩ := hC hkey
  obtain ⟨-, -, hsub, hful, -⟩ := TermCert.tstep_appUp X.hr
  obtain ⟨m1, hm1, hv⟩ := TermPlantF.promViewLt_run h0 X.run i th wB X.hth (hsub wB hwB)
  rw [hmB, Option.some.injEq] at hm1
  have hv1 : mB.view < wB := by rw [hm1]; exact hv
  refine ⟨wB, Gs, fun r1 _ _ hr1 t ht hn => ?_, TermPlantFul.plantOp_W2 hAo, hB, hnd, hit, hcov⟩
  subst hr1
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (hful t ht hn) hle) hv1)

end

end TermPlantOpG

#print axioms TermPlantOpG.plantOp_of
