import WeakCore.TermSpawnMid
import WeakCore.TermPlantF
import WeakCore.TermPlantAtPos
/-!
# TermSpawnArms — the `Sp := Spawn` arms of the run-closed leaves L3/L4/L5

A mid-run spawn `spawnT c i par kid` keeps memory and pairs, gives the parent its old promises and the
kid none, so every promise-indexed run invariant transfers.  With the `spawnCfg` (parent
`spawnPar`, promises `th.promises`; kid `spawnKid`, none) these are the `hSpV`/`hSpP`/`hSpN` arms.
-/
namespace TermSpawnMid
open CoreLang CoreTerm TermRun TermStep TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {c : Cfg} {i : Nat} {th par kid : TTh}

/-- Promise membership after the spawn comes from the old configuration (same thread index off the kid). -/
theorem spawnT_prom (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises) (hkp : kid.promises = [])
    {j : Nat} {tj : TTh} {t : Ts} (hj : (spawnT c i par kid).ths[j]? = some tj) (ht : t ∈ tj.promises) :
    ∃ t0, c.ths[j]? = some t0 ∧ t ∈ t0.promises ∧ tj.promises = t0.promises := by
  rcases spawnT_get_cases (TermSpawn.lt_of_get hth) hj with ⟨rfl, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, hj'⟩
  · exact ⟨th, hth, hpp ▸ ht, hpp⟩
  · rw [hkp] at ht; cases ht
  · exact ⟨tj, hj', ht, rfl⟩

/-- **L3 arm** (`hSpV`). -/
theorem promViewLt_spawnT (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises) (hkp : kid.promises = [])
    (h : TermPlantF.PromViewLt c) : TermPlantF.PromViewLt (spawnT c i par kid) := by
  intro j tj t hj ht
  obtain ⟨t0, h0, ht0, -⟩ := spawnT_prom hth hpp hkp hj ht
  exact h j t0 t h0 ht0

/-- **L4 arm** (`hSpP`). -/
theorem promPos_spawnT (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises) (hkp : kid.promises = [])
    (h : TermPlantAtPos.PromPos c) : TermPlantAtPos.PromPos (spawnT c i par kid) := by
  intro j tj hj t ht
  obtain ⟨t0, h0, ht0, -⟩ := spawnT_prom hth hpp hkp hj ht
  exact h j t0 h0 t ht0

/-- **L5 arm** (`hSpN`; the invariant `PromNodupI` spelled out, as in `TermBal.PromNodupI`). -/
theorem promNodupI_spawnT (hth : c.ths[i]? = some th) (hpp : par.promises = th.promises) (hkp : kid.promises = [])
    (h : (c.ths.size = 0 ∨ TermFul.PWFall c) ∧ ∀ (n : Nat) (t : TTh), c.ths[n]? = some t → t.promises.Nodup) :
    ((spawnT c i par kid).ths.size = 0 ∨ TermFul.PWFall (spawnT c i par kid)) ∧
      ∀ (n : Nat) (t : TTh), (spawnT c i par kid).ths[n]? = some t → t.promises.Nodup := by
  have hi := TermSpawn.lt_of_get hth
  obtain ⟨hw, hn⟩ := h
  have hw' : TermFul.PWFall c := hw.resolve_left (by omega)
  refine ⟨Or.inr fun j => ⟨(hw' j).1, fun t ht => ?_⟩, fun n t hn' => ?_⟩
  · unfold TermFul.promsOf at ht
    cases hj : (spawnT c i par kid).ths[j]? with
    | none => simp [hj] at ht
    | some tj =>
      simp only [hj, Option.map_some, Option.getD_some] at ht
      obtain ⟨t0, h0, ht0, -⟩ := spawnT_prom hth hpp hkp hj ht
      exact (hw' j).2 t (by rw [TermFul.promsOf_some h0]; exact ht0)
  · rcases spawnT_get_cases hi hn' with ⟨rfl, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, hj'⟩
    · rw [hpp]; exact hn _ _ hth
    · rw [hkp]; exact List.nodup_nil
    · exact hn _ _ hj'

end
end TermSpawnMid

#print axioms TermSpawnMid.promViewLt_spawnT
#print axioms TermSpawnMid.promPos_spawnT
#print axioms TermSpawnMid.promNodupI_spawnT
#print axioms TermSpawnMid.spawnT_prom
