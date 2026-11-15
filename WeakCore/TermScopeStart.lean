import WeakCore.TermInit
import WeakCore.TermSpawnDefs

/-! # TermScopeStart: the scope run invariant `RunScope` at the standard start shapes

`ObligationsF.runDRF0 : RunScope c0` at the two start shapes the
finals use, each reduced to the program's scope check (`ProgScopeOK`) or the kids' `KidOK`:

* `runScope_entry`: every start thread is an **entry call** `tail d.name [] (var "a") ts` of a code
  block `d ∈ p`, its argument `a` bound at `d.argTy`, no type arguments, an empty stack, and `ts`
  region-free: TermInit's `runDRF_spawn` shape, with `drf1 d.argTy` from `ProgScopeOK p`.
  This entry-call thread shape (`TermScopeLib.EntryStart`) is an extra syntactic hypothesis,
  beyond `InitShape`, that the caller supplies.
* `runScope_spawnS`: the barrier-spawn start `TermSpawn.spawnS cs res kids` (the spawn finals' start),
  from `KidOK` of every kid.
-/

namespace TermScopeStart

open CoreLang CoreTerm TermRun TermScope TermSpawn

/-- **`RunScope` at an entry-call start** of a scope-checked program (TermInit's `runDRF_spawn` shape;
the argument type is the code block's declared `argTy`). -/
theorem runScope_entry {p : Prog} {c0 : Cfg} (hp : ProgScopeOK p = true)
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → ∃ d ∈ p, ∃ (ts : List Ty) (ws : List Word),
      th.term = .tail d.name [] (.var "a") ts ∧ th.env = [("a", d.argTy, ws)] ∧ th.σs = [] ∧
      th.stack = [] ∧ ts.all drf = true) :
    RunScope c0 := by
  -- `ProgScopeOK` gives `drf1 d.argTy` (M10), which is what `EnvDRF` asks of the entry variable;
  -- the rest is `runDRF_spawn`'s proof (`ts` region-free, no type frames, empty stack).
  intro i th hth
  obtain ⟨d, hd, ts, ws, h1, h2, h3, h4, h5⟩ := h i th hth
  refine ⟨?_, ?_, fun x _ rt ws' hl => ?_, ?_⟩
  · rw [h1]; simp only [allOK, Bool.and_eq_true, List.all_eq_true] at h5 ⊢
    exact ⟨fun x hx => TermC1.drf1_of_drf _ (h5 x hx), fun x hx => TermScope.rgnFree_of_drf _ (h5 x hx)⟩
  · rw [h3]; intro σ hσ; cases hσ
  · rw [h2] at hl
    unfold lookupE at hl
    cases hx : ("a" == x)
    · simp only [List.find?, hx, Option.map_none] at hl
      cases hl
    · simp only [List.find?, hx, Option.map_some, Option.some.injEq] at hl
      rw [← (Prod.mk.inj hl).1]
      exact (ProgScopeOK.decl hp hd).1
  · rw [h4]; intro f hf; cases hf

/-! ### `drf1` twins of `TermInit.envDRF_all`/`runDRF_init`/`runDRF_spawn`: the run invariant only needs `drf1`. -/

theorem envDRF_all1 {env : Env} {t : Expr} (h : ∀ e ∈ env, TermC1.drf1 e.2.1 = true) : EnvDRF env t := by
  intro x _ rt ws hl
  unfold lookupE at hl
  cases hf : env.find? (·.1 == x) with
  | none => rw [hf] at hl; cases hl
  | some e =>
    rw [hf] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    have := h e (List.mem_of_find?_eq_some hf)
    rw [hl] at this
    exact this

theorem runDRF_init1 {c0 : Cfg}
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
      allOK th.term = true ∧ AllDrf th.σs ∧ (∀ e ∈ th.env, TermC1.drf1 e.2.1 = true) ∧ th.stack = []) :
    RunScope c0 := by
  intro i th hth
  obtain ⟨h1, h2, h3, h4⟩ := h i th hth
  exact ⟨h1, h2, envDRF_all1 h3, by rw [h4]; intro f hf; cases hf⟩

/-- `runDRF_spawn` with the argument type only `drf1` (the type arguments stay `drf`, as `allOK` needs). -/
theorem runDRF_spawn1 {c0 : Cfg}
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → ∃ (f : String) (ts : List Ty) (t : Ty) (ws : List Word),
      th.term = .tail f [] (.var "a") ts ∧ th.env = [("a", t, ws)] ∧ th.σs = [] ∧ th.stack = [] ∧
      ts.all drf = true ∧ TermC1.drf1 t = true) :
    RunScope c0 := by
  refine runDRF_init1 fun i th hth => ?_
  obtain ⟨f, ts, t, ws, h1, h2, h3, h4, h5, h6⟩ := h i th hth
  refine ⟨by
      rw [h1]; simp only [allOK, Bool.and_eq_true, List.all_eq_true] at h5 ⊢
      exact ⟨fun x hx => TermC1.drf1_of_drf _ (h5 x hx), fun x hx => TermScope.rgnFree_of_drf _ (h5 x hx)⟩,
    ?_, ?_, h4⟩
  · rw [h3]; intro σ hσ; cases hσ
  rw [h2]
  intro e he
  simp only [List.mem_singleton] at he
  rw [he]
  exact h6

/-- **`RunScope` at the barrier-spawn start** `spawnS cs res kids`, from `KidOK` of every kid. -/
theorem runScope_spawnS {p : Prog} {rt : Ty} {cs : Cfg} {res : List Word} {kids : List Kid}
    (hk : ∀ kd ∈ kids, KidOK p rt kd) : RunScope (spawnS cs res kids) := by
  unfold spawnS
  split
  · rename_i h0
    intro i th hth
    have hi : i < cs.ths.size := (Array.getElem?_eq_some_iff.1 hth).1
    have h0' : cs.ths.size = 0 := by
      rcases Nat.eq_zero_or_pos cs.ths.size with e | e
      · exact e
      · rw [Array.getElem?_eq_getElem e] at h0; cases h0
    omega
  · rename_i th0 _
    refine runDRF_spawn1 fun i th hth => ?_
    simp only [List.getElem?_toArray, List.getElem?_map] at hth
    cases hkd : kids[i]? with
    | none => rw [hkd] at hth; cases hth
    | some kd =>
      rw [hkd] at hth
      cases hth
      obtain ⟨-, -, hdrf, hts, -⟩ := hk kd (List.mem_of_getElem? hkd)
      exact ⟨kd.f, kd.ts, kd.ty, _, rfl, rfl, rfl, rfl, hts, hdrf⟩

end TermScopeStart

#print axioms TermScopeStart.runScope_entry
#print axioms TermScopeStart.runScope_spawnS
