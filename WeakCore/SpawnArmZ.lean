import WeakCore.SpawnLeafZ
import WeakCore.TermSpawnMidM0
/-!
# SpawnArmZ — `SpawnArmX` at `Sp := Spawn p k arch c0.cap`, and the finals

* `spawnArmX_spawn` — the `TermSpawnMid.sysInvN_spawnArm` (M0; the typing premise is discharged
  inside by `spawnTy_of_sysInvN`), with `hc` from the `TermSpawnMid.StepsG.cap_eq`. No hypotheses.
* `machine_tokens_main_spawn`, `token_unique_net_spawn`, `token_unique_final_spawn`, `reachable_typed_spawn`,
  `machine_tokens_main_spawn_init` — the SpawnFinalX finals at `Sp := Spawn … c0.cap`.
-/
namespace SpawnArmZ
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermCertScope TermSpawn TermTyped TermSpawnStep A9SpawnFinal
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem spawnArmX_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg} :
    SpawnArmX p k arch (Spawn p k arch c0.cap) Init c0 := by
  intro _ _ _ c c' hr hI hsp
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs⟩ := hI
  exact TermSpawnMid.sysInvN_spawnArm hN hOL hObs hsp (TermSpawnMid.StepsG.cap_eq hr)

#print axioms spawnArmX_spawn

/-! ### The balance conjunct at `MintOK := fun _ => True`

The finals below instantiate `MintOK` with `fun _ => True`, so the balance conjunct of `SysInvW`
(`∃ M, MintOK M ∧ Σ(Tot + credits + HP) + HS ≤ Init + M + Σ debits`) is vacuous: any `M`
witnesses it.  Nothing is lost by this.  The per-key bounds for the exclusive keys `rg`, `wd` and
`own` are carried separately, by the `tok`, `wd` and `own` clauses of `SysInvW` (`KeySum ≤ 1`)
and by `KeyNet` (net of outstanding promise debits).  Epoch keys `ep` and share keys `sh` are
not bounded by these theorems.  No other proof consumes the balance conjunct; it is only
re-established step by step. -/

/-- **`machine_tokens_mainX` at `Sp := Spawn p k arch c0.cap`** (all Sp-arms discharged). -/
theorem machine_tokens_main_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsFX p k arch (Spawn p k arch c0.cap) Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    {c : Cfg} (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  machine_tokens_mainX O hk hS SpawnLeafZ.spLeafArms_spawn spawnArmX_spawn hr

/-- **`token_unique_netX` at `Sp := Spawn p k arch c0.cap`** (all Sp-arms discharged). -/
theorem token_unique_net_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsFX p k arch (Spawn p k arch c0.cap) Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    {c : Cfg} (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_netX O hk hS SpawnLeafZ.spLeafArms_spawn spawnArmX_spawn hr

/-- **`token_unique_finalX` at `Sp := Spawn p k arch c0.cap`** (all Sp-arms discharged). -/
theorem token_unique_final_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsFX p k arch (Spawn p k arch c0.cap) Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    {c : Cfg} (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  token_unique_finalX O hk hS SpawnLeafZ.spLeafArms_spawn spawnArmX_spawn hr hn

/-- **`reachable_typedX` at `Sp := Spawn p k arch c0.cap`** (all Sp-arms discharged). -/
theorem reachable_typed_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsFX p k arch (Spawn p k arch c0.cap) Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0)
    {c : Cfg} (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot :=
  reachable_typedX O hk hS SpawnLeafZ.spLeafArms_spawn spawnArmX_spawn hr

/-- **`machine_tokens_mainX_init` at `Sp := Spawn p k arch c0.cap`** (all Sp-arms discharged). -/
theorem machine_tokens_main_spawn_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {c0 : Cfg}
    (O : ObligationsFX p k arch (Spawn p k arch c0.cap) Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) : Headline p k arch Init c :=
  machine_tokens_mainX_init O hk h0 SpawnLeafZ.spLeafArms_spawn spawnArmX_spawn hr

#print axioms machine_tokens_main_spawn
#print axioms token_unique_net_spawn
#print axioms token_unique_final_spawn
#print axioms reachable_typed_spawn
#print axioms machine_tokens_main_spawn_init

end SpawnArmZ
