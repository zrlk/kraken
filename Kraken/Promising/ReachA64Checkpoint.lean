/-
**AArch64 checkpoints for `ReachCheckpoint`**.

`reachA64Cfg c0 ds msgs` is the configuration with `c0`'s threads, each
with its dynamic part (machine state, register views, views, promises)
replaced from `ds`, and `c0`'s memory with messages `msgs`. It has `c0`'s
static parts (`reachA64Cfg_sameStatic`), which is what `reach_segment`
needs of a checkpoint. `reachA64ShowCfg` prints a configuration as such a
term, for generating checkpoints (`#eval` with `isa.exec`; it is not used by
any proof).
-/
import Kraken.Promising.ReachCheckpoint
import Kraken.Promising.ReachA64Core
import Kraken.Promising.CertifyAArch64

namespace Kraken.Promising.Reach

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The dynamic part of an AArch64 thread. -/
abbrev ReachA64Dyn := MachineState × Array View × Array View × Views × List Time

/-- Thread `t` with its dynamic part replaced by `d`. -/
def reachA64WithDyn (t : Thread isa) (d : ReachA64Dyn) : Thread isa :=
  { st := { t.st with st := d.1 }, rview := d.2.1, wview := d.2.2.1, views := d.2.2.2.1, prom := d.2.2.2.2 }

/-- `c0` with the threads' dynamic parts from `ds` and the messages `msgs`. -/
def reachA64Cfg (c0 : Config isa) (ds : List ReachA64Dyn) (msgs : Array Msg) : Config isa :=
  { threads := (List.zipWith reachA64WithDyn c0.threads.toList ds).toArray, mem := { c0.mem with msgs } }

theorem reachA64Cfg_sameStatic (c0 : Config isa) (ds : List ReachA64Dyn) (msgs : Array Msg)
    (h : ds.length = c0.threads.size) : ReachSameStatic c0 (reachA64Cfg c0 ds msgs) := by
  intro i
  simp only [reachA64Cfg, List.getElem?_toArray, List.getElem?_zipWith, Array.getElem?_toList]
  cases hc : c0.threads[i]? with
  | none => rfl
  | some t =>
    have hi : i < ds.length := h ▸ (Array.getElem?_eq_some_iff.mp hc).1
    rw [List.getElem?_eq_getElem hi]
    rfl

/-! ## Printing checkpoints -/

private def reachHex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

private def reachRepr {α : Type} [Repr α] (a : α) : String := (repr a).pretty 100000

/-- A machine state as a term (registers that are not `0` only). -/
def reachA64ShowMS (m : MachineState) : String :=
  let regs := (List.range 31).filterMap fun i =>
    let v := (m.1.regs.getXReg (XReg.ofNat i)).toNat
    if v != 0 then some s!"X{i} := {reachHex v}" else none
  let regs := if m.1.regs.SP != 0 then regs ++ [s!"SP := {reachHex m.1.regs.SP.toNat}"] else regs
  let st := m.1.status
  let dmem := if m.1.dmem.isEmpty then "∅" else "(private memory not empty)"
  s!"(⟨\{ {", ".intercalate regs} }, ⟨{st.n}, {st.z}, {st.c}, {st.v}⟩, {dmem}⟩, {reachHex m.2.toNatClampNeg})"

/-- A configuration as a `reachA64Cfg c0 …` term. -/
def reachA64ShowCfg (c : Config isa) : String :=
  let ds := c.threads.toList.map fun t =>
    s!"({reachA64ShowMS t.st.st},\n     {reachRepr t.rview},\n     {reachRepr t.wview},\n     {reachRepr t.views},\n     {reachRepr t.prom})"
  s!"reachA64Cfg c0\n  [{",\n   ".intercalate ds}]\n  {reachRepr c.mem.msgs}"

end Kraken.Promising.Reach

#print axioms Kraken.Promising.Reach.reachA64Cfg_sameStatic
