import WeakCore.TermInit
import WeakCore.TermViewInvH
import WeakCore.TermSpawnStep

/-! # TermSpawnScope (ASSEMBLY L2): the scope run invariant under `Spawn`

`RunScope` (TermScope) is preserved by the `Spawn` step from an **arbitrary** configuration:

* the parent `spawnPar` continues with `e` (`allOK` of `let x = spawn … in e`), keeps its type
  arguments and stack (`withS`), and binds `x : int`; every other free variable of `e` was free in
  the `let`;
* the child `spawnKid` runs `tail f [] (var "a") ts` with env `[("a", T, _)]`, no type arguments
  and no stack; `drf T` and `ts.all drf` come from the parent's `allOK` via
  `opTys (.spawn _ _ T ts) = T :: ts` (so `opOK` checks them; no `ProgScopeOK` premise is needed
  for the arm itself, and no fact about the runtime type of the argument);
* other threads are untouched.

`runScopeR_spawn` / `run_scopeX` lift it to `StepsX` through TermScope's generic `runDRFR_of`
(the `Step` arm is `runDRF_step`; the `Sp := Spawn` arm is `runScope_spawnStep`).
-/

namespace TermSpawnScope

open CoreLang CoreTerm TermRun TermScope TermSpawnStep TermViewInv TermInit

/-- The parent after a spawn keeps `ThScope`. -/
theorem thScope_spawnPar {c : Cfg} {th : TTh} {x f : String} {a : At} {T : Ty} {ts : List Ty}
    {e : Expr} (h : ThScope th) (ht : th.term = .let_ x (.spawn f a T ts) e) :
    ThScope (spawnPar c th x e) := by
  have hok := h.ok
  rw [ht] at hok
  simp only [allOK, Bool.and_eq_true] at hok
  refine ⟨hok.2, h.σs, envDRF_cons (fun _ => rfl) fun y hy hne => ?_, h.stk⟩
  exact h.env y (ht ▸ free_let_body hy hne)

/-- The child of a spawn satisfies `ThScope` when its checked type and type arguments are `drf`. -/
theorem thScope_spawnKid {c : Cfg} {th : TTh} {f : String} {ts : List Ty} {T : Ty} {ws : List Word}
    (hT : drf T = true) (hts : ts.all drf = true) : ThScope (spawnKid c th f ts T ws) := by
  refine ⟨hts, fun σ hσ => by simp [spawnKid] at hσ, envDRF_all ?_, fun fr hf => by simp [spawnKid] at hf⟩
  intro en hen
  simp only [spawnKid, List.mem_singleton] at hen
  subst hen
  exact hT

/-- **`RunScope` is preserved by `Spawn`**, from any configuration. -/
theorem runScope_spawnStep {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat}
    {c c' : Cfg} (h : Spawn p k arch cap c c') (hc : RunScope c) : RunScope c' := by
  obtain ⟨i, x, f, a, T, ts, e, th, rt, ws, hth, ht, -, -, -, rfl⟩ := h.elim
  have hT := hc i th hth
  have hok := hT.ok
  rw [ht] at hok
  simp only [allOK, opOK, opTys, List.all_cons, Bool.and_eq_true] at hok
  intro j th0 hj
  simp only [spawnCfg, spawnT] at hj
  rw [Array.getElem?_push] at hj
  split at hj
  · cases hj
    exact thScope_spawnKid hok.1.1 hok.1.2
  · rcases getElem?_set!_cases hj with rfl | hj
    · exact thScope_spawnPar hT ht
    · exact hc j th0 hj

/-- **`RunScopeR` with spawns**: `RunScope` at every configuration reachable by machine steps and
spawns (`runDRFR_of` at `Sp := Spawn`, the spawn arm `runScope_spawnStep`). -/
theorem runScopeR_spawn {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {c0 : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScope c0) : RunScopeR p k arch (Spawn p k arch cap) c0 :=
  runDRFR_of hp (fun _ _ hs h => runScope_spawnStep hs h) h0

/-- **`RunScope` along every run with spawns** of a checked program. -/
theorem run_scopeX {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {c0 c : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScope c0) (hr : StepsX p k arch cap c0 c) : RunScope c :=
  runScopeR_spawn hp h0 hr

end TermSpawnScope

#print axioms TermSpawnScope.thScope_spawnPar
#print axioms TermSpawnScope.thScope_spawnKid
#print axioms TermSpawnScope.runScope_spawnStep
#print axioms TermSpawnScope.runScopeR_spawn
#print axioms TermSpawnScope.run_scopeX
