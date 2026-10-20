/- Re-base of SpawnV onto `TermSpawnStep.spawnCfg`: the spawn arm of `ViewInv`
(`viewInv_spawnCfg`), its `Spawn`-step form, and `ViewInv` / `envVR` along `StepsG … Spawn` runs. -/
import WeakCore.TermViewInvH
import WeakCore.TermSpawnStep
namespace Z2SpawnV
open CoreLang CoreTerm TermRun TermViewInv TermSpawnStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem WV_bump {n V : Nat} {w : Word} (h : WV n w) (hV : V ≤ n) : WV n (TermSpawn.bumpW V w) :=
  ⟨Nat.max_le.2 ⟨Nat.le_trans h.1 (Nat.le_max_left _ _), Nat.le_max_right _ _⟩, Nat.max_le.2 ⟨h.2, hV⟩⟩

theorem EnvV_cons {n : Nat} {y : String × Ty × List Word} {env : Env} (h1 : WsV n y.2.2) (h2 : EnvV n env) :
    EnvV n (y :: env) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact h1
  · exact h2 e he

/-- **The spawn arm of `ViewInv`**, over `TermSpawnStep.spawnCfg`. -/
theorem viewInv_spawnCfg {c : Cfg} {i : Nat} {th : TTh} {x : String} {e : Expr} {f : String} {ts : List Ty}
    {a : At} {T rt : Ty} {ws : List Word} (hv : ViewInv c) (hth : c.ths[i]? = some th)
    (hev : evalAt th.env a = some (rt, ws)) : ViewInv (spawnCfg c i th x e f ts T ws) := by
  have hT : ThV c.mem.size th := hv.2 i th hth
  have hF := (stepFence_V (n := c.mem.size)
    (th := mth (stOf c.mem c.pairs th) (cst (.num 0)) (cst (.num 0)) (cst (.num 0))) hT.2.2 .sy).1
  refine ⟨hv.1, fun j th0 hj => ?_⟩
  simp only [spawnCfg, spawnT] at hj
  rw [Array.getElem?_push] at hj
  split at hj
  · -- the child
    cases hj
    unfold ThV
    refine ⟨fun e' he' => ?_, fun fr hf => by simp [spawnKid] at hf, ?_⟩
    · simp only [spawnKid] at he'
      rcases List.mem_singleton.1 he' with rfl
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      exact WV_bump (evalAt_V hT.1 hev w0 hw0) hF.2.2.2.2
    · exact hF
  · rcases getElem?_set!_cases hj with rfl | hj
    · -- the parent
      unfold ThV
      exact ⟨EnvV_cons (WsV_cons (WV_cst _ _) (WsV_nil _)) hT.1, hT.2.1, hF⟩
    · exact hv.2 j th0 hj

/-- The `Spawn`-step form. -/
theorem viewInv_spawnStep {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : Spawn p k arch cap c c') (hv : ViewInv c) : ViewInv c' := by
  cases h with
  | mk i x f a T ts e th rt ws h1 _ _ _ h5 => exact viewInv_spawnCfg hv h1 h5

/-- **`ViewInv` along every run with spawns.** -/
theorem viewInv_runX {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg} (h0 : ViewInv c0)
    (hr : StepsX p k arch cap c0 c) : ViewInv c :=
  stepsX_pres (fun _ _ hs hv => viewInv_step hv hs) (fun _ _ hs hv => viewInv_spawnStep hs hv) hr h0

/-- **`envVR` along every run with spawns** (the `envVR_of_run` consumer form). -/
theorem envVR_of_runX {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg} (h0 : ViewInv c0)
    (hr : StepsX p k arch cap c0 c) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) :
    ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts :=
  fun _ _ _ w hev hw => (evalAt_V ((viewInv_runX h0 hr).2 i th hth).1 hev w hw).1

end Z2SpawnV

#print axioms Z2SpawnV.viewInv_spawnCfg
#print axioms Z2SpawnV.viewInv_runX
#print axioms Z2SpawnV.envVR_of_runX
#print axioms Z2SpawnV.viewInv_spawnStep
#print axioms Z2SpawnV.WV_bump
#print axioms Z2SpawnV.EnvV_cons
