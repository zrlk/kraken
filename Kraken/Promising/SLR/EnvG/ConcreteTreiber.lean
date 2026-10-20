/-
Part 11: **concrete instance of
`Treiber.treiber_pp_envG`** (non-vacuity of its start hypotheses). The pusher
laid out at `0x100000`, the popper at `0x200000` (each directive its
`fakeSize`, as the `.kl` runner lays out text), `top` at `0x1000` (8 bytes,
initially `0`), the node `n1` at `0x1100`; thread `0` starts the pusher with
`X0 = top`, `X1 = n1`, `X9 = 1`, thread `1` the popper with `X0 = top`. Every
hypothesis is discharged by `decide`, `rfl` or `simp` (no `native_decide`).
`codeMatches`: the `.kl`'s shared `code` block parses to `treiberPusher`,
the `pdone` `NOP`, then `treiberPopper`.
-/
import Kraken.Promising.SLR.EnvG.TreiberPublic
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.ConcreteTreiber

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.Treiber

/-! ## The layouts -/

/-- The pusher's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def pushLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiberPusher

/-- The popper's layout: text at `0x200000`, each directive its `fakeSize`. -/
@[reducible] def popLayout : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize treiberPopper

instance pushValid : Executable.ValidLayout (pushLayout treiberPusher) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance popValid : Executable.ValidLayout (popLayout treiberPopper) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- `top`'s address. -/
def topAddr : BitVec 64 := 0x1000
/-- The node's address. -/
def n1Addr : BitVec 64 := 0x1100

/-- The pusher's initial state: `X0 = top`, `X1 = n1`, `X9 = 1`, at
`pusher`, halting at `pdone` (the end of its text); no declarations, empty
private memory. -/
def pusher0 : AArch64.State where
  exe := pushLayout treiberPusher
  endPc := 0x100000 + 32
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X9 := 1 } }, 0x100000)

/-- The popper's initial state: `X0 = top`, at `popper`, halting at `qdone`
(the end of its text); no declarations, empty private memory. -/
def popper0 : AArch64.State where
  exe := popLayout treiberPopper
  endPc := 0x200000 + 40
  st := ({ regs := { X0 := 0x1000 } }, 0x200000)

/-- The initial memory: `top = 0`, `n1`'s data word `0`. -/
def treiberInitMem : List (Loc × Val) := [(⟨topAddr, 8⟩, 0), (⟨n1Addr, 4⟩, 0)]

section
attribute [local instance] pushLayout

theorem pusher0_start : StartPush topAddr n1Addr pusher0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;>
    simp [pusher0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, topAddr, n1Addr]

end

section
attribute [local instance] popLayout

theorem popper0_start : StartPop topAddr popper0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, ?_, fun a => ?_⟩ <;>
    simp [popper0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, topAddr]

end

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def treiberPpKl : String := include_str "../../../Examples/LockFree/AArch64/treiber_pp.kl"

/-- The shared `code` block of the `.kl` parses to the pusher, the `pdone`
`NOP`, then the popper. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog.take treiberPusher.length == treiberPusher &&
        prog.drop (treiberPusher.length + 1) == treiberPopper && prog.length == treiberPusher.length + 1 + treiberPopper.length
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches treiberPpKl

/-! ## The instance -/

/-- **`1:X10 = n1 ∧ 1:X11 = 1`** for `treiber_pp.kl` under `Arch.armv8`,
concrete instance of `treiber_pp_envG`. -/
theorem treiber_pp_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [pusher0, popper0] treiberInitMem) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.X10.toBitVec = n1Addr ∧ th.st.st.1.regs.X11.toBitVec = 1 :=
  treiber_pp_envG pushLayout popLayout topAddr n1Addr (by decide) pusher0_start popper0_start
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.ConcreteTreiber

#print axioms Kraken.Promising.SLR.EnvG.ConcreteTreiber.treiber_pp_envG_concrete
