import WeakCore.TermSpawnMid
/-!
# TermSpawnMidBridge — the canonical spawn shapes satisfy the abstract hypotheses

`spawnS`/`spawnPar`/`spawnKid` are the `TermSpawnStep` definitions (exported here).
-/
namespace TermSpawnMidZ
open CoreLang CoreTerm TermRun TermSpawn TermSpawnMid
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

export TermSpawnStep (spawnS spawnPar spawnKid spawnCfg)

/-- `spawnPar` meets the `hpar` hypothesis of `thSys_kidFull`/`sysInvN_spawn`. -/
theorem spawnPar_hpar (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) :
    (spawnPar c i th x e).vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧
    (spawnPar c i th x e).promises = th.promises ∧ (spawnPar c i th x e).nalloc = th.nalloc + 1 ∧
    (spawnPar c i th x e).undefs = th.undefs := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [spawnPar, spawnS, withS, fenceS, stOf]

/-- `spawnPar`'s env/stack/term/σs (for `thLbl_par` and `hParTy`). -/
theorem spawnPar_shape (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) :
    (spawnPar c i th x e).term = e ∧
    (spawnPar c i th x e).env = (x, .tid, [cst (.loc ⟨TermSpawnStep.tidLabel c i th, 0⟩ 0)]) :: th.env ∧
    (spawnPar c i th x e).stack = th.stack ∧ (spawnPar c i th x e).σs = th.σs ∧
    (spawnPar c i th x e).tidLbl = th.tidLbl :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `spawnKid` has the `KidShape` (with the bound type `t := T`, the op's checked type). -/
theorem spawnKid_shape (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) (f : String) (ts : List Ty)
    (T : Ty) (ws : List Word) : KidShape (spawnPar c i th x e) (spawnKid c i th f ts T ws) f ts T ws :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TermSpawnMidZ

#print axioms TermSpawnMidZ.spawnPar_hpar
#print axioms TermSpawnMidZ.spawnKid_shape
#print axioms TermSpawnMidZ.spawnPar_shape
