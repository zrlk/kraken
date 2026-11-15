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
theorem thScope_spawnPar {c : Cfg} {i : Nat} {th : TTh} {x f : String} {a : At} {T : Ty} {ts : List Ty}
    {e : Expr} (h : ThScopeI th) (ht : th.term = .let_ x (.spawn f a T ts) e) :
    ThScopeI (spawnPar c i th x e) := by
  have hok := h.ok
  rw [ht] at hok
  simp only [allOK, Bool.and_eq_true] at hok
  refine ⟨hok.2, h.σs, envDRF_cons (fun _ => rfl) fun y hy hne => ?_, h.stk⟩
  exact h.env y (ht ▸ free_let_body hy hne)

/-- The parent after a `spawnI` keeps `ThScope`. -/
theorem thScope_spawnParI {c : Cfg} {i : Nat} {th : TTh} {x f : String} {is : List String} {a : At} {T : Ty}
    {ts : List Ty} {e : Expr} (h : ThScopeI th) (ht : th.term = .let_ x (.spawnI f is a T ts) e) :
    ThScopeI (spawnPar c i th x e) := by
  have hok := h.ok
  rw [ht] at hok
  simp only [allOK, Bool.and_eq_true] at hok
  refine ⟨hok.2, h.σs, envDRF_cons (fun _ => rfl) fun y hy hne => ?_, h.stk⟩
  exact h.env y (ht ▸ free_let_body hy hne)

/-- The child of a spawn satisfies `ThScope` when its checked type and type arguments are `drf1` and its
type arguments `rgnFree` (the `tail` arm of `allOK`). -/
theorem thScope_spawnKid {c : Cfg} {i : Nat} {th : TTh} {f : String} {ts : List Ty} {T : Ty} {ws : List Word}
    (hT : TermC1.drf1 T = true) (hts : ts.all TermC1.drf1 = true) (hrf : ts.all TermSound.rgnFree = true) :
    ThScope (spawnKid c i th f ts T ws) := by
  refine ⟨by simp only [spawnKid, allOK, hts, hrf, Bool.and_self], fun σ hσ => by simp [spawnKid] at hσ, ?_,
    fun fr hf => by simp [spawnKid] at hf⟩
  intro x _ rt ws0 hl
  unfold lookupE at hl
  simp only [spawnKid, List.find?_cons, List.find?_nil] at hl
  split at hl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    rw [← hl.1]
    exact hT
  · cases hl

/-- (option A) The kid of a `spawnI` keeps `ThScope`, given the program scope check (`drf1 d.argTy`). -/
theorem scope_kidI_hp {p : Prog} {c : Cfg} {i : Nat} {th : TTh} {x f : String} {is : List String} {a : At}
    {T : Ty} {ts : List Ty} {e : Expr} {d : Decl} {ws : List Word} (hp : ProgScopeOK p = true)
    (hT : ThScopeI th) (ht : th.term = .let_ x (.spawnI f is a T ts) e) (hd : p.find? (·.name == f) = some d) :
    ThScopeI (spawnKidI c i th d ts ws) := by
  have hok := hT.ok
  rw [ht] at hok
  simp only [allOK, opOK, opTys, List.all_cons, Bool.and_eq_true] at hok
  have hsh := hok.1.2
  simp only [TermC1.opShareOK, Bool.and_eq_true] at hsh
  have hts : ts.all TermC1.drf1 = true := hok.1.1
  have hA := (ProgScopeOK.decl hp (List.mem_of_find?_eq_some hd)).1
  refine ⟨by simp only [spawnKidI, allOK, hts, hsh.1, Bool.and_self], fun σ hσ => by simp [spawnKidI] at hσ, ?_,
    fun fr hf => by simp [spawnKidI] at hf⟩
  intro y _ rt ws0 hl
  unfold lookupE at hl
  simp only [spawnKidI, List.find?_cons, List.find?_nil] at hl
  split at hl
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    rw [← hl.1]
    refine drf1L_of_drf1 _ (drf1_close (fun σ hσ => ?_) hA)
    simp only [List.mem_reverse, List.mem_map] at hσ
    obtain ⟨u, hu, rfl⟩ := hσ
    exact drf1_close (fun _ h => by simp at h) (List.all_eq_true.1 hts u hu)
  · simp at hl

/-- **`RunScope` is preserved by `Spawn`**, from any configuration. -/
theorem runScope_spawnStep {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat}
    {c c' : Cfg} (hp : ProgScopeOK p = true) (h : Spawn p k arch cap c c') (hc : RunScopeI c) : RunScopeI c' := by
  rcases h.elim with ⟨i, x, f, a, T, ts, e, th, rt, ws, hth, ht, -, -, -, rfl⟩ |
      ⟨i, x, f, is, a, T, ts, e, th, d, rt, ws, hth, ht, -, -, hd, -, rfl⟩
  · have hT := hc i th hth
    have hok := hT.ok
    rw [ht] at hok
    simp only [allOK, opOK, opTys, List.all_cons, Bool.and_eq_true] at hok
    intro j th0 hj
    simp only [spawnCfg, spawnT] at hj
    rw [Array.getElem?_push] at hj
    split at hj
    · cases hj
      have hsh := hok.1.2
      simp only [TermC1.opShareOK, Bool.and_eq_true] at hsh
      exact thScopeI_of (thScope_spawnKid hok.1.1.1 hok.1.1.2 hsh.1)
    · rcases getElem?_set!_cases hj with rfl | hj
      · exact thScope_spawnPar hT ht
      · exact hc j th0 hj
  · intro j th0 hj
    simp only [spawnT] at hj
    rw [Array.getElem?_push] at hj
    split at hj
    · cases hj
      exact scope_kidI_hp hp (hc i th hth) ht hd
    · rcases getElem?_set!_cases hj with rfl | hj
      · exact thScope_spawnParI (hc i th hth) ht
      · exact hc j th0 hj

/-- **`RunScopeR` with spawns**: `RunScope` at every configuration reachable by machine steps and
spawns (`runDRFR_of` at `Sp := Spawn`, the spawn arm `runScope_spawnStep`). -/
theorem runScopeR_spawn {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {c0 : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScope c0) : RunScopeR p k arch (Spawn p k arch cap) c0 :=
  runDRFR_of hp (fun _ _ hs h => runScope_spawnStep hp hs h) h0

/-- **`RunScope` along every run with spawns** of a checked program. -/
theorem run_scopeX {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {cap : Nat} {c0 c : Cfg}
    (hp : ProgScopeOK p = true) (h0 : RunScope c0) (hr : StepsX p k arch cap c0 c) : RunScopeI c :=
  runScopeR_spawn hp h0 hr

end TermSpawnScope

#print axioms TermSpawnScope.thScope_spawnPar
#print axioms TermSpawnScope.thScope_spawnKid
#print axioms TermSpawnScope.runScope_spawnStep
#print axioms TermSpawnScope.scope_kidI_hp
#print axioms TermSpawnScope.runScopeR_spawn
#print axioms TermSpawnScope.run_scopeX
