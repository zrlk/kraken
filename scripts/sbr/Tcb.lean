import Kraken.X64.Examples.Sbr.Link

/-! The trusted closure of the linked theorem (run by ci.sh, step `tcb`).

Collects every declaration reachable from the statement of `ff_aac_sbr_apply_linked`
through statements and definition bodies, but not through proofs: the definitions whose
meaning the theorem depends on. Prints, per project module (`Kraken*`), the source lines
those declarations span and their number; program texts (`Program`/`List Directive`
constants, checked by translation validation) are counted on their own rows.

The last line, `FINGERPRINT`, is a hash of the closure's names, types and definition
bodies (independent of which module or line a declaration sits in). It changes exactly
when the meaning of the statement can change; ci.sh compares it with
`baseline/tcb_fingerprint.txt`. After an intended change to the specification, the
machine model or a program text, re-record it (`lake env lean scripts/sbr/Tcb.lean`)
and review the change. -/

open Lean Meta

namespace SbrTcb

/-- Constants reachable from `root`'s type through types and definition bodies. -/
partial def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let some ci0 := env.find? root | return {}
  let mut todo : Array Name := ci0.type.getUsedConstants
  let mut seen : NameSet := {}
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.defnInfo d) => todo := todo ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | some (.opaqueInfo d) => todo := todo ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | some (.inductInfo i) =>
        todo := todo ++ i.type.getUsedConstants
        for c in i.ctors do todo := todo.push c
    | some ci => todo := todo ++ ci.type.getUsedConstants
    | none => pure ()
  return seen

def isProgramText (ci : ConstantInfo) : Bool :=
  let ty := toString ci.type
  ty.endsWith "Program" || ty.endsWith "Directive"

def main : MetaM Unit := do
  let env ← getEnv
  let seen := closure env `Kraken.Examples.Sbr.ff_aac_sbr_apply_linked
  if seen.isEmpty then throwError "ff_aac_sbr_apply_linked not found"
  let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  let mut cnt : Std.HashMap Name Nat := {}
  let mut fp : UInt64 := 0
  for n in seen.toList do
    -- fingerprint over every reachable constant (Lean core included); order-independent
    if let some ci := env.find? n then
      let hv := match ci with
        | .defnInfo d => mixHash (hash d.type) (hash d.value)
        | .opaqueInfo d => mixHash (hash d.type) (hash d.value)
        | ci => hash ci.type
      fp := fp + mixHash (hash n) hv
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`Kraken).isPrefixOf m || (`KrakenTactics).isPrefixOf m do continue
    let isProg := (env.find? n).map isProgramText |>.getD false
    let m := if isProg then m.str "[program text]" else m
    cnt := cnt.insert m (cnt.getD m 0 + 1)
    if let some rg ← findDeclarationRanges? n then
      byMod := byMod.insert m ((byMod.getD m #[]).push (rg.range.pos.line, rg.range.endPos.line))
  let mut total := 0
  let mut decls := 0
  let mut rows : Array (Nat × Name × Nat) := #[]
  for (m, rs) in byMod.toList do
    let rs := rs.qsort (fun a b => a.1 < b.1)
    let mut lines := 0
    let mut cur : Option (Nat × Nat) := none
    for (a, b) in rs do
      match cur with
      | none => cur := some (a, b)
      | some (ca, cb) =>
        if a ≤ cb + 1 then cur := some (ca, max cb b)
        else
          lines := lines + (cb - ca + 1)
          cur := some (a, b)
    if let some (ca, cb) := cur then lines := lines + (cb - ca + 1)
    total := total + lines
    decls := decls + cnt.getD m 0
    rows := rows.push (lines, m, cnt.getD m 0)
  IO.println "lines\tdecls\tmodule"
  for (l, m, c) in rows.qsort (fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)) do
    IO.println s!"{l}\t{c}\t{m}"
  IO.println s!"TOTAL\t{total}\t{decls} project decls ({seen.size} reachable in all modules)"
  IO.println s!"FINGERPRINT {fp}"

end SbrTcb

#eval SbrTcb.main
