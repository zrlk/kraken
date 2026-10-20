import WeakCore.TermSpawnArms
import WeakCore.SpawnFinalX
/-!
# SpawnLeaf — `SpLeafArms` from the spawn *shape*

`SpLeafArms Sp` (SpawnFinalX) has five per-step arms.  For any `Sp` whose steps are mid-run spawns
`spawnT c i par kid` with the parent keeping its promises and the kid having none (`SpawnShapeT`),
the three promise arms (L3/L4/L5) are the `promViewLt_spawnT` / `promPos_spawnT` /
`promNodupI_spawnT` (TermSpawnArms).  The remaining two arms are taken as hypotheses:

* `viewInv` — `Z2SpawnV.viewInv_spawnCfg` (SpawnVZ);
* `runDRF`  — the `runScope_spawnStep` / `runScope_spawnStep` (needs `Op.spawn`).

With `Op.spawn`: `spLeafArms_spawn := spLeafArms_of_shape spawn_shapeT viewInv_spawnStep runScope_spawnStep`.

NOTE: the shape below uses `TermSpawnStep.spawnT` (body `{ c with ths := (c.ths.set! i par).push kid }`).
-/

namespace SpawnLeaf
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermCertScope TermSpawn TermTyped TermSpawnStep A9SpawnFinal
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (named) Every `Sp`-step is a mid-run spawn with promise-preserving parent and promise-free kid. -/
def SpawnShapeT (Sp : Cfg → Cfg → Prop) : Prop :=
  ∀ c c', Sp c c' → ∃ (i : Nat) (th par kid : TTh), c.ths[i]? = some th ∧
    par.promises = th.promises ∧ kid.promises = [] ∧ c' = TermSpawnStep.spawnT c i par kid

/-- **`SpLeafArms` from the shape** plus the ViewInv and RunScope spawn arms. -/
theorem spLeafArms_of_shape {Sp : Cfg → Cfg → Prop} (hShape : SpawnShapeT Sp)
    (hV : ∀ c c', Sp c c' → TermViewInv.ViewInv c → TermViewInv.ViewInv c')
    (hD : ∀ c c', Sp c c' → TermScope.RunScope c → TermScope.RunScope c') : SpLeafArms Sp where
  viewInv := hV
  runDRF := hD
  promViewLt := fun c c' h hc => by
    obtain ⟨i, th, par, kid, hth, hpp, hkp, rfl⟩ := hShape c c' h
    exact TermSpawnMid.promViewLt_spawnT hth hpp hkp hc
  promPos := fun c c' h hc => by
    obtain ⟨i, th, par, kid, hth, hpp, hkp, rfl⟩ := hShape c c' h
    exact TermSpawnMid.promPos_spawnT hth hpp hkp hc
  promNodup := fun c c' h hc => by
    obtain ⟨i, th, par, kid, hth, hpp, hkp, rfl⟩ := hShape c c' h
    exact TermSpawnMid.promNodupI_spawnT hth hpp hkp hc

/-- Sanity: the empty relation has the shape. -/
theorem spawnShapeT_bot : SpawnShapeT (fun (_ _ : Cfg) => False) := fun _ _ h => h.elim

/-- **Headline over a spawn-shaped `Sp`** — only `SpawnArmX` (plus the ViewInv / RunScope spawn arms)
remains as a hypothesis. -/
theorem machine_tokens_mainX_shape {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (O : ObligationsFX p k arch Sp Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hS : StartOKX p k arch Init c0) (hShape : SpawnShapeT Sp)
    (hV : ∀ c c', Sp c c' → TermViewInv.ViewInv c → TermViewInv.ViewInv c')
    (hD : ∀ c c', Sp c c' → TermScope.RunScope c → TermScope.RunScope c')
    (hP : SpawnArmX p k arch Sp Init c0)
    {c : Cfg} (hr : StepsG p k arch Sp c0 c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  machine_tokens_mainX O hk hS (spLeafArms_of_shape hShape hV hD) hP hr

#print axioms spLeafArms_of_shape
#print axioms machine_tokens_mainX_shape

#print axioms spawnShapeT_bot
end SpawnLeaf
