import WeakCore.TermSpawnStartO
/-!
# Spawn-era finals over the Sp-parametric retype

No shims: `TermSpawnStep.StepsG`, `TermMain.TCtxX`/`PCtxX`/`TCtx.toX`/`PCtx.toX`,
`TermCertScope.CertWinCNX`/`PNX`, `TermMain.ObligationsFX`/`ofF_bot`/`ObligationsFX.toObligationsCX`/`SpArms`
and the run-closed leaves `ViewInvR`/`RunScopeR`/`PromViewLtR`/`PromPosR`/`PromNodupR` are the single copies.

`StepArmX` is now a THEOREM (`stepArmX`): `TermSpawn.sysInvO_step` (hrun over `StepsG Sp`) at
`ObligationsFX.toObligationsCX`, with `SpArms` built from the five per-step `Sp`-arms `SpLeafArms`
(the L1–L5 spawn arms; at `Sp := Spawn …`: SpawnV `viewInv_spawn`, the RunScope arm,
TermSpawnArms `promViewLt_spawnT`/`promPos_spawnT`/`promNodupI_spawnT`).
Named hypotheses left: `SpLeafArms` (5 per-step facts) and `SpawnArmX` (`sysInvN_spawnMid`).
-/
namespace A9SpawnFinal
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermCertScope TermSpawn TermTyped TermSpawnStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The old bundle from the new one (the easy direction; the other uses `ofF_bot`) -/
theorem ObligationsFX.toF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (O : ObligationsFX p k arch Sp Init MintOK c0) :
    ObligationsF p k arch Init MintOK c0 :=
  ⟨O.checked, O.progScope, O.runDRF0⟩

/-! ## The spawn-era start state -/

/-- **`StartOKX`** (NEW, beside the unchanged `StartOK`): `StartOK` with `SysInvNx` strengthened to
`SysInvO`. -/
def StartOKX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (c0 : Cfg) : Prop :=
  SysInvO p k arch Init (fun _ => True) c0 ∧ AllNoProm c0 ∧ TermViewInv.ViewInv c0 ∧
    (c0.ths.size = 0 ∨ TermFul.PWFall c0)

theorem StartOKX.toStartOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (h : StartOKX p k arch Init c0) : StartOK p k arch Init (fun _ => True) c0 := by
  obtain ⟨⟨Eg, Tot, HP, HS, cr, db, hN, -, -⟩, h2, h3, h4⟩ := h
  exact ⟨⟨Eg, Tot, HP, HS, cr, db, hN⟩, h2, h3, h4⟩

/-- Route 1: an `InitOK` start. -/
theorem startOKX_of_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (h0 : InitOK p k arch Init (fun _ => True) c0) : StartOKX p k arch Init c0 :=
  ⟨sysInvO_of_initOK h0, (startOK_of_initOK h0).2⟩

/-- Route 2: the barrier-spawn start (the `sysInvO_spawnS_proved` + `startOK_spawnS_proved`). -/
theorem startOKX_spawnS {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {cpre cs : Cfg} {th0 th : TTh} {f : String} {ts : List Ty} {d : Decl} {a : At} {rt : Ty} {res : List Word}
    {kids : List Kid}
    (O0 : ObligationsF p k arch Init (fun _ => True) (phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre))
    (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) cpre) (h1 : cpre.ths.size = 1)
    (hpre : cpre.ths[0]? = some th0) (hset : th0.term = .tail f [] (.var "a") ts) (hstk0 : th0.stack = [])
    (hd : p.find f = .ok d)
    (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (hR0a : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hR0w : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true)
    (hrun : TermStep.Steps p k arch cpre cs) (hnp : AllNoProm cs)
    (hth : cs.ths[0]? = some th) (hret : th.term = .ret a) (hstk : th.stack = [])
    (hev : evalAt th.env a = some (rt, res))
    (hkids : kids ≠ []) (hok : ∀ kd ∈ kids, KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) :
    StartOKX p k arch Init (spawnS cs res kids) :=
  ⟨sysInvO_spawnS_proved O0 hk h0 h1 hpre hset hstk0 hd hR0 hR0a hR0w hrun hnp hth hret hstk hev hkids hok,
    (startOK_spawnS_proved O0 hk h0 h1 hpre hset hstk0 hd hR0 hR0a hR0w hrun hnp hth hret hstk hev hkids hok).2⟩

/-! ## The per-step `Sp`-arms (L1–L5) and the spawn arm -/

/-- **(named) The five per-step `Sp`-arms** feeding the `*R_of` (L1–L5). -/
structure SpLeafArms (Sp : Cfg → Cfg → Prop) : Prop where
  viewInv : ∀ c c', Sp c c' → TermViewInv.ViewInv c → TermViewInv.ViewInv c'
  runDRF : ∀ c c', Sp c c' → TermScope.RunScope c → TermScope.RunScope c'
  promViewLt : ∀ c c', Sp c c' → TermPlantF.PromViewLt c → TermPlantF.PromViewLt c'
  promPos : ∀ c c', Sp c c' → TermPlantAtPos.PromPos c → TermPlantAtPos.PromPos c'
  promNodup : ∀ c c', Sp c c' → TermBal.PromNodupI c → TermBal.PromNodupI c'

/-- `SpArms` from the leaf arms at a `StartOKX` start (the generic `*R_of`). -/
theorem spArms_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (L : SpLeafArms Sp) (hS : StartOKX p k arch Init c0) :
    SpArms p k arch Sp c0 :=
  ⟨TermViewInv.viewInvR_of L.viewInv hS.2.2.1,
    TermBal.promNodupR_of L.promNodup (fun n th h => by rw [hS.2.1 n th h]; exact List.nodup_nil) hS.2.2.2,
    TermScope.runDRFR_of (TermScope.ProgScopeOKW.scope O.progScope) L.runDRF O.runDRF0,
    TermPlantF.promViewLtR_of L.promViewLt hS.2.1,
    TermPlantAtPos.promPosR_of L.promPos hS.2.1⟩

/-- **(named) Spawn arm** (`sysInvN_spawnMid`): a spawn from a reachable configuration keeps `SysInvO`. -/
def SpawnArmX (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (c0 : Cfg) : Prop :=
  ObligationsFX p k arch Sp Init (fun _ => True) c0 → k.storeDepRts = true → StartOKX p k arch Init c0 →
    ∀ {c c' : Cfg}, StepsG p k arch Sp c0 c → SysInvO p k arch Init (fun _ => True) c →
      Sp c c' → SysInvO p k arch Init (fun _ => True) c'

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res} {c0 : Cfg}

/-- **`StepArmX`, proved**: a machine step from a `StepsG Sp`-reachable configuration keeps `SysInvO`. -/
theorem stepArmX (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (L : SpLeafArms Sp) (hS : StartOKX p k arch Init c0) {c c' : Cfg}
    (hr : StepsG p k arch Sp c0 c) (h : SysInvO p k arch Init (fun _ => True) c) (hs : Step p k arch c c') :
    SysInvO p k arch Init (fun _ => True) c' :=
  TermSpawn.sysInvO_step (O.toObligationsCX hk (spArms_of O L hS)) hr h hs

/-- `SysInvO` along spawning runs, hence `SysInvNx`. -/
theorem sysInv_runX (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0) (L : SpLeafArms Sp) (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) : SysInvNx p k arch Init (fun _ => True) c := by
  have key : ∀ {c1 c2 : Cfg}, StepsG p k arch Sp c1 c2 → StepsG p k arch Sp c0 c1 →
      SysInvO p k arch Init (fun _ => True) c1 → SysInvO p k arch Init (fun _ => True) c2 := by
    intro c1 c2 h12
    induction h12 with
    | refl => exact fun _ h => h
    | step hs _ ih =>
      exact fun h01 h1 => ih (h01.tail hs)
        (hs.elim (fun h => stepArmX O hk L hS h01 h1 h) (fun h => hP O hk hS h01 h1 h))
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, -, -⟩ := key hr (.refl _) hS.1
  exact ⟨Eg, Tot, HP, HS, cr, db, hN⟩

/-- The headline from `SysInvN` at `c` (the body of `machine_tokens_mainS`, verbatim). -/
theorem headline_of_sysInv {c : Cfg} (h : SysInvNx p k arch Init (fun _ => True) c) : Headline p k arch Init c := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN⟩ := h
  refine ⟨Eg, Tot, HP, HS, cr, db, hN, hN.knet,
    fun hn => ⟨hN.toW hn, fun i j n hi hj h1 h2 => (hN.toW hn).tokUniq hi hj h1 h2⟩, fun i th hth => ?_⟩
  obtain ⟨S, ρ, η, cx, Rf, Rs, hCE, -, hE, hT, -, hFI, hsum, -, hm, -⟩ := (hN.thr i th hth).env hN.clo
  exact ⟨S, ρ, η, cx, Rf, Rs, hCE, hE, hT.1, hFI, hsum, hm⟩
end

/-! ## The spawn-era finals -/

/-- **`machine_tokens_mainF`, spawn era.** -/
theorem machine_tokens_mainX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    (L : SpLeafArms Sp) (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  headline_of_sysInv (sysInv_runX O hk hS L hP hr)

/-- **`token_unique_netF`, spawn era.** -/
theorem token_unique_netX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    (L : SpLeafArms Sp) (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hk, -, ht⟩ := machine_tokens_mainX O hk hS L hP hr
  exact ⟨Eg, Tot, HP, HS, cr, db, ht, hN, tokUniq_of_knet hk⟩

/-- **`token_unique_finalF`, spawn era.** -/
theorem token_unique_finalX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    (L : SpLeafArms Sp) (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, -, -, hg, ht⟩ := machine_tokens_mainX O hk hS L hP hr
  exact ⟨Eg, Tot, ht, (hg hn).2⟩

/-- **`reachable_typedF`, spawn era.** -/
theorem reachable_typedX {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    (L : SpLeafArms Sp) (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, -, -, -, ht⟩ := machine_tokens_mainX O hk hS L hP hr
  exact ⟨Eg, Tot, ht⟩

/-- **Spawn-era final at an `InitOK` start.** -/
theorem machine_tokens_mainX_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0)
    (L : SpLeafArms Sp) (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) : Headline p k arch Init c :=
  headline_of_sysInv (sysInv_runX O hk (startOKX_of_initOK h0) L hP hr)

/-! ## Sanity: at `Sp = ⊥` every hypothesis is discharged and the old final is recovered -/

theorem spLeafArms_bot : SpLeafArms (fun _ _ => False) :=
  ⟨fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ h => h.elim⟩

theorem spawnArmX_bot {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg} :
    SpawnArmX p k arch (fun _ _ => False) Init c0 :=
  fun _ _ _ _ _ _ _ h => h.elim

/-- The old `machine_tokens_mainF` conclusion from `ObligationsF` + `InitOK` (via `ofF_bot`). -/
theorem mainX_bot {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    Headline p k arch Init c :=
  machine_tokens_mainX_init (ofF_bot O) hk h0 spLeafArms_bot spawnArmX_bot (StepsG.ofSteps hr)

#print axioms StartOKX.toStartOK
#print axioms startOKX_of_initOK
#print axioms spArms_of
#print axioms sysInv_runX
#print axioms headline_of_sysInv
#print axioms spLeafArms_bot
#print axioms spawnArmX_bot
end A9SpawnFinal

#print axioms A9SpawnFinal.machine_tokens_mainX
#print axioms A9SpawnFinal.token_unique_netX
#print axioms A9SpawnFinal.token_unique_finalX
#print axioms A9SpawnFinal.reachable_typedX
#print axioms A9SpawnFinal.machine_tokens_mainX_init
#print axioms A9SpawnFinal.stepArmX
#print axioms A9SpawnFinal.mainX_bot
#print axioms A9SpawnFinal.startOKX_spawnS
#print axioms A9SpawnFinal.ObligationsFX.toF
