/-
**Part 8: a concrete instance of
`TreiberX.x64_treiber_pp_envG`** (non-vacuity of its start hypotheses;
`X64RelayXchgConcrete.lean`'s pattern). The pusher laid out as the `.kl`
runner lays it out (`klLayout`) at `0x100000`, the popper at `0x200000`,
`top` at `0x1000` (8 bytes, initially `0`), the node `n1` at `0x1100`;
thread `0` starts the pusher with `%rdi = top`, `%rbx = n1`, thread `1` the
popper with `%rdi = top`; empty private memories. Every hypothesis is
discharged by `decide`, `rfl`, `simp` or `Split.empty` (no `native_decide`).
`codeMatchesX`: the `.kl`'s shared `code` block parses to `treiberPusherX`
(through `pdone:`), the `pdone` `nop`, then `treiberPopperX`.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberPublic
import Kraken.Promising.SLR.EnvG.ConcreteX64Layout
import Kraken.Litmus.Program

namespace Kraken.Promising.X64.EnvG.ConcreteTreiberX

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX Kraken.Promising.X64.EnvG.Concrete

/-! ## The layouts -/

/-- The pusher's layout: text at `0x100000`. -/
@[reducible] def pushLayoutX : _root_.Layout := klLayout treiberPusherX 0x100000

/-- The popper's layout: text at `0x200000`. -/
@[reducible] def popLayoutX : _root_.Layout := klLayout treiberPopperX 0x200000

theorem pushLayoutX_cells : ((pushLayoutX treiberPusherX).2.map (·.2)) = [0, 1, 0, 1, 1, 1, 1, 1, 0] := by decide

theorem popLayoutX_cells : ((popLayoutX treiberPopperX).2.map (·.2)) = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0] := by
  decide

instance pushValidX : Executable.ValidLayout (pushLayoutX treiberPusherX) :=
  validLayout_of_cells _ (by decide) (by decide)

instance popValidX : Executable.ValidLayout (popLayoutX treiberPopperX) :=
  validLayout_of_cells _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- `top`'s address. -/
def topAddrX : BitVec 64 := 0x1000
/-- The node's address. -/
def n1AddrX : BitVec 64 := 0x1100

/-- The pusher's initial state: `%rdi = top`, `%rbx = n1`, at `pusher`,
halting at `pdone` (the end of its text, `0x100000 + 6`); empty private
memory. -/
def pusherX0 : X64.State where
  exe := pushLayoutX treiberPusherX
  endPc := 0x100000 + 6
  st := ({ regs := (({} : Reg64s).set64 .rdi 0x1000).set64 .rbx 0x1100 }, 0x100000)

/-- The popper's initial state: `%rdi = top`, at `popper`, halting at
`qdone` (the end of its text, `0x200000 + 9`); empty private memory. -/
def popperX0 : X64.State where
  exe := popLayoutX treiberPopperX
  endPc := 0x200000 + 9
  st := ({ regs := ({} : Reg64s).set64 .rdi 0x1000 }, 0x200000)

/-- The initial memory: `top = 0`, `n1`'s data word `0`. -/
def treiberInitMemX : List (Loc × Val) := [(⟨topAddrX, 8⟩, 0), (⟨n1AddrX, 4⟩, 0)]

section
attribute [local instance] pushLayoutX

theorem pusherX0_start : StartPushX topAddrX n1AddrX pusherX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, by decide, Split.empty _⟩

end

section
attribute [local instance] popLayoutX

theorem popperX0_start : StartPopX topAddrX popperX0 :=
  ⟨rfl, rfl, by decide, by decide, by decide, fun _ => by simp [popperX0]⟩

end

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def treiberPpKlX : String := include_str "../../../Examples/LockFree/X64/treiber_pp.kl"

/-- The shared `code` block of the `.kl` parses to the pusher (through its
`pdone:` label), the `pdone` `nop`, then the popper. -/
def codeMatchesX (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog.take treiberPusherX.length == treiberPusherX &&
        prog.drop (treiberPusherX.length + 1) == treiberPopperX &&
        prog.length == treiberPusherX.length + 1 + treiberPopperX.length
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatchesX treiberPpKlX

/-! ## The instance -/

/-- **`1:r10 = n1 ∧ 1:r11d = 1`** for the x64 `treiber_pp.kl` under
`Arch.tso`, concrete instance of `x64_treiber_pp_envG`. -/
theorem x64_treiber_pp_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [pusherX0, popperX0] treiberInitMemX) c)
    (hf : c.final = true) :
    ∃ th, c.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = n1AddrX ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1 :=
  x64_treiber_pp_envG pushLayoutX popLayoutX topAddrX n1AddrX (by decide) pusherX0_start popperX0_start
    (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.X64.EnvG.ConcreteTreiberX

#print axioms Kraken.Promising.X64.EnvG.ConcreteTreiberX.x64_treiber_pp_envG_concrete
