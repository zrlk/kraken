/-
**The slot order of an `Accepted1` code block's function on AArch64**:
`Emit.A64.funcRegs` is `Spike/Lib/SlotOrderC1.lean`'s `slots_func1`.

- `dedupFold_eq`: `funcRegs`' first-occurrence fold is `eraseDups`;
- `funcRegs_eq`: `funcRegs f` is the first occurrences of the parameters
  and, per block, `instDefs i ++ instUsesR i` of each instruction and
  `termUses` of the terminator;
- `funcRegs_func1`: for `func1` of a closed form `lowerC`, the parameter
  registers, then the definitions in order (`fnCtx_slots_func1`: the
  emitter's `FnCtx.slots`).
-/
import Spike.Lib.SlotOrderC1
import Scc.Emit.A64

namespace Spike.Lib.SlotOrder

open Scc.IR
open Scc.Lower
open Scc.Lower.Inv
open Scc.IR.StackMap (opRegs instDefs instUses termUses)

/-- `funcRegs`' fold: append a register unless already present. -/
def dedupStep (acc : List Reg) (r : Reg) : List Reg := if acc.contains r then acc else acc ++ [r]

theorem foldl_dedupStep : ∀ (l acc : List Reg),
    l.foldl dedupStep acc = acc ++ (l.removeAll acc).eraseDups
  | [], acc => by simp [List.removeAll]
  | a :: l, acc => by
    rw [List.foldl_cons]
    by_cases h : a ∈ acc
    · have hs : dedupStep acc a = acc := by simp [dedupStep, h]
      rw [hs, foldl_dedupStep l acc]
      simp [List.removeAll, h]
    · have hs : dedupStep acc a = acc ++ [a] := by simp [dedupStep, h]
      rw [hs, foldl_dedupStep l (acc ++ [a])]
      simp only [List.removeAll, List.filter_cons, List.elem_eq_mem, h, decide_false, Bool.not_false,
        ite_true, List.eraseDups_cons, List.append_assoc, List.singleton_append, List.filter_filter]
      congr 3
      apply List.filter_congr
      intro x _
      by_cases hx : x = a <;> simp [hx]

/-- **`funcRegs`' first-occurrence fold is `eraseDups`.** -/
theorem dedupFold_eq (l : List Reg) : l.foldl dedupStep [] = l.eraseDups := by
  rw [foldl_dedupStep]
  simp only [List.removeAll, List.nil_append]
  congr 1
  exact List.filter_eq_self.mpr (by simp)

/-- **`funcRegs` by `StackMap`'s definitions and uses**: the first
occurrences of the parameters, then per block each instruction's
definitions and uses (`instUsesR`) and the terminator's uses. -/
theorem funcRegs_eq (f : Func) :
    Scc.Emit.A64.funcRegs f =
      (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap (fun i => instDefs i ++ instUsesR i) ++
        termUses b.term).eraseDups := by
  rw [← dedupFold_eq]
  refine congrArg (fun l => List.foldl dedupStep [] (f.params ++ l)) ?_
  refine congrArg (fun g => f.blocks.flatMap g) (funext fun b => ?_)
  refine congr (congrArg (· ++ ·) (congrArg (fun g => b.insts.flatMap g) (funext fun i => ?_))) ?_
  · cases i <;> simp only [instDefs, instUsesR, instUses] <;> (try simp only [opRegs]) <;> (repeat' split) <;>
      (try simp_all) <;> (congr 1 <;> funext o <;> cases o <;> rfl)
  · cases b.term <;> simp only [termUses] <;> (try simp only [opRegs]) <;> (repeat' split) <;>
      (try simp_all) <;> (congr 1 <;> funext o <;> cases o <;> rfl)

/-- **The AArch64 slots of an `Accepted1` code block's function**: for
`func1` of a body's closed form `lowerC` (`accepted1_lowerC`), its
parameter registers, then its definitions (`StackMap.instDefs`) in order. -/
theorem funcRegs_func1 (cx : Scc.Lower.Ctx) {d : CoreTerm.Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    Scc.Emit.A64.funcRegs (func1 name (params1R d) r) =
      (func1 name (params1R d) r).params ++ defsOf instDefs (func1 name (params1R d) r) := by
  rw [funcRegs_eq]
  exact slots_func1 shape_instUsesR _ (fun _ => rfl) cx hr name

/-- **`fnCtx`'s slots** for `func1` of a closed form: the parameter
registers, then the definitions in order. -/
theorem fnCtx_slots_func1 (abortFn : String) (growth : Option Growth) (areas : List (Sym × Nat)) (fi : Nat)
    (cx : Scc.Lower.Ctx) {d : CoreTerm.Decl} {r : Res1}
    (hr : lowerC cx (env1 d) 0 "entry" 0 d.body = some r) (name : Sym) :
    (Scc.Emit.A64.fnCtx abortFn growth areas fi (func1 name (params1R d) r)).slots =
      (func1 name (params1R d) r).params ++ defsOf instDefs (func1 name (params1R d) r) :=
  funcRegs_func1 cx hr name

end Spike.Lib.SlotOrder
