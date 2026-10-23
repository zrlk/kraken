import WeakCore.TermInit
import WeakCore.TermSpawnDefs

/-! # TermScopeStart: the scope run invariant `RunScope` at the standard start shapes

`ObligationsF.runDRF0 : RunScope c0` at the two start shapes the
finals use, each reduced to the program's scope check (`ProgScopeOK`) or the kids' `KidOK`:

* `runScope_entry`: every start thread is an **entry call** `tail d.name [] (var "a") ts` of a code
  block `d ∈ p`, its argument `a` bound at `d.argTy`, no type arguments, an empty stack, and `ts`
  region-free: TermInit's `runDRF_spawn` shape, with `drf d.argTy` from `ProgScopeOK p`.
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
    RunScope c0 :=
  TermInit.runDRF_spawn fun i th hth =>
    have ⟨d, hd, ts, ws, h1, h2, h3, h4, h5⟩ := h i th hth
    ⟨d.name, ts, d.argTy, ws, h1, h2, h3, h4, h5, (ProgScopeOK.decl hp hd).1⟩

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
    refine TermInit.runDRF_spawn fun i th hth => ?_
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
