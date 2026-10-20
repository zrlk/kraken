/-
**Concrete instance of `Lower.PilotX.pilotX_promising`.**
ISA: x64; machine: the executable Promising machine
(`Reachable Arch.tso`).

The instance is at the explorer's configuration of `Lower/PilotX64Prog.lean`
(the one its `#guard_msgs` run `pilotXRun` explores): both threads at the
layout `xLayout` (text at `0x100000`, labels 0 bytes, every instruction 1),
the start states `threadX 0x2000` and `threadX 0x3000` (`rbx = &top =
0x1000`, the arena of thread `w` at its node, `rsp = sp0` with the end of the
text in its slot, the 24-byte stack `stack0` mapped in `dmem`) and the initial
memory `initMemX` (`top` and both links `0`).

- `Mem.loadInt_isSome_storeInt_of_le`: a load inside the range of a store is
  mapped (`Mem.loadInt_isSome_storeInt` of `Kraken/WordLemmas.lean` at width 64).
- `pX`: the parameters (`top` at `0x1000`, node `0` at `0x2000`, node `1`
  at `0x3000`) and `pX_locs` (`TLocs`, by `decide`).
- `stack0_split`: the stack is off the shared layout (`Split`), by finitely
  many byte checks.
- `threadX_start`: both start states satisfy `StartPX` (the return address
  and the callees' slot through the store/load lemmas of `Kraken/Mem.lean`).
- `initMemX_inv`: the initial memory satisfies the value invariant `GV pX`
  (`MemInv.of_init`).
- `pilotX_concrete`: every final configuration reachable under `Arch.tso`
  from that configuration has the two threads' `r12` the two nodes
  `0x2000`/`0x3000`, in some order. Its only hypotheses are the reachability
  `hc` and finality `hf`.
-/
import Kraken.Promising.Lower.PilotX64Whole
import Kraken.Promising.SLR.EnvG.ConcreteCommon
import Kraken.WordLemmas

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

/-- **A load inside the range of a store is mapped**: after storing `n`
bytes at `a`, the first `k ≤ n` bytes at `a` load (`Mem.loadInt_isSome_storeInt`,
`Kraken/WordLemmas.lean`, at width 64). -/
theorem Mem.loadInt_isSome_storeInt_of_le (m : Mem 64) (a : BitVec 64) {n k : Nat} (v : Int) (hk : k ≤ n)
    (hn : n ≤ 2 ^ 64) : (Mem.loadInt (Mem.storeInt m a n v) a k).isSome = true :=
  Mem.loadInt_isSome_storeInt m a v hk hn

namespace Kraken.Promising.Lower.PilotX.Concrete

open Kraken.Promising.Lower.PilotX
open Kraken.Promising.X64.EnvG.Treiber2X

/-- The explorer's parameters: `top` at `0x1000`, node `0` at `0x2000`,
node `1` at `0x3000` (`threadX`'s arenas). -/
def pX : Params := ⟨0x1000, fun w => if w = 0 then 0x2000 else 0x3000⟩

/-- `top` is not a node; the nodes are distinct and non-null. -/
theorem pX_locs : TLocs pX :=
  ⟨by decide, by decide, by decide⟩

/-- **The stack is off the shared layout**: no byte of `top` or of a link is
mapped in `stack0 ra`. -/
theorem stack0_split (ra : BitVec 64) : Split (SL pX) (stack0 ra) := by
  refine Split.of_get fun a n ha i hi => ?_
  rw [stack0, Mem.storeInt, Mem.get?_storeBytes_of_not_mem, Mem.storeInt, Mem.get?_storeBytes_of_not_mem]
  · simp
  all_goals
    rw [mem_At_iff, Int.toBytes_length]
    simp only [SL, pX, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert i <;> decide

section
attribute [local instance] xLayout

/-- **Both explorer start states satisfy `StartPX`.** -/
theorem threadX_start (w : Nat) (hw : w < 2) :
    StartPX pX w (threadX (if w = 0 then 0x2000 else 0x3000)) := by
  have he : endX = endPX := by decide
  have hret (b : UInt64) : RetAt (threadX b).st.1 endPX :=
    ⟨_, Mem.loadInt_storeInt _ _ _ _ (by decide), by
      simpa [he] using Int64.ofBitVec_ofBytes_toBytes endPX⟩
  have hslot (b : UInt64) :
      (Mem.loadInt (threadX b).st.1.dmem ((threadX b).st.1.regs.get64 .rsp - 16) 8).isSome = true := by
    show (Mem.loadInt (stack0 endX.toBitVec) (sp0 - 16) 8).isSome = true
    rw [stack0, Mem.loadInt_storeInt_of_above _ _ _ _ _ _ (by decide) (by decide)]
    exact Mem.loadInt_isSome_storeInt_of_le _ _ _ (by decide) (by decide)
  rcases w with _ | _ | w
  · exact ⟨rfl, rfl, by decide, by decide, rfl, rfl, by decide, hret _, hslot _, stack0_split _⟩
  · exact ⟨rfl, rfl, by decide, by decide, rfl, rfl, by decide, hret _, hslot _, stack0_split _⟩
  · omega

/-- **The explorer's initial memory satisfies the value invariant** `GV pX`
(every value `0`, no message). -/
theorem initMemX_inv :
    MemInv (GV pX) (Config.init (I := isa) [threadX 0x2000, threadX 0x3000] initMemX).mem := by
  refine MemInv.of_init rfl (fun _ => .inl rfl) ?_
  simp [initMemX, GV]

/-- **The x64 Treiber pilot with a `dmem` call stack, at the explorer's
configuration**: every final configuration reachable under `Arch.tso` from
the two `threadX` threads and `initMemX` has the threads' `r12` the two
nodes (`0x2000`, `0x3000`), in some order. -/
theorem pilotX_concrete {fuel : Nat} {cfg : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [threadX 0x2000, threadX 0x3000] initMemX) cfg)
    (hf : cfg.final = true) : Treiber2FinalX 0x2000 0x3000 cfg :=
  pilotX_promising (P := pX) xLayout xLayout pX_locs (threadX_start 0 (by decide))
    (threadX_start 1 (by decide)) (by simp only [Config.init_mem]; decide) initMemX_inv hc hf

end

end Kraken.Promising.Lower.PilotX.Concrete

#print axioms Kraken.Promising.Lower.PilotX.Concrete.pilotX_concrete
