import Lean
open Lean Elab Command in
elab "#axall " m:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "no module"
  let mut bad : Array Name := #[]
  let mut n : Nat := 0
  let mut all : NameSet := {}
  for (c, _) in env.constants.toList do
    if env.getModuleIdxFor? c == some idx && !c.isInternal then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms c)
      for a in axs do all := all.insert a
      if axs.any (fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound) then bad := bad.push c
  logInfo m!"decls={n} axioms={all.toList} nonstd={bad}"
