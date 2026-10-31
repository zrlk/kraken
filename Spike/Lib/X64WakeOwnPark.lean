/-
**Main owns its TCB word at `scc_rt_park`** (x86-64): the `hown` premise of
`WaitLoop.seg_parkCall` / `seg_waitLoopP` (`OwnAt ms exe endPc
".Lscc_rt_park.entry" tp tp` at `tp = tcbM`) for a memory side whose own map
is `ownGX` (`ownG ++ ownS`), where every state at the pc runs on a pool
stack (`spPool`, so `selfOwn`). Main reaches `scc_rt_park` only from
`wc_waitLoop`, past `scc_rt_main`'s switch to the taken stack.

- `ownS_of_self`, `tcbM_mem_ownGX`: at a `selfOwn` state `ownGX` holds
  `tcbM` with its address.
- `ownAt_ownGX`: `OwnAt … pc tcbM tcbM` for `ms.own = ownGX L a`, every state
  at `pc` `selfOwn` (`hself`).
- `ownAt_park`: at `.Lscc_rt_park.entry`, every state there on a pool stack
  (`hsp`) at a pc from `scc_rt_start`'s `.x1` on (`hx`; `scc_rt_park` lies
  above it in the layout).

`OwnAt` quantifies over every state at the pc, not only a node's, so `hsp`
does not follow from a call site's frame. Main reaches `scc_rt_park` only
after its `clone` (`.Lwc_waitLoop.else2`), where its memory side's own map
is the constant `[(tcbM, tcbM)]` (the post-spawn map, `ownAt` at every pc
with no `hsp`); `ownAt_park` serves a memory side at `ownGX` only.
-/
import Spike.Lib.X64WakeOwnS
import Spike.Lib.X64RtNodes

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {a : BitVec 64}

/-- **`ownS` at a `selfOwn` state**: `tcbM` holding its address. -/
theorem ownS_of_self {s : State} (h : selfOwn L s) : ownS L s = [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] := by
  unfold ownS; simp [h]

/-- **`ownGX` holds `tcbM`** with its address at a `selfOwn` state. -/
theorem tcbM_mem_ownGX {s : State} (h : selfOwn L s) : (⟨tcbM L, 8⟩, (tcbM L).setWidth 128) ∈ ownGX L a s := by
  unfold ownGX; rw [ownS_of_self h]; exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **Main owns `tcbM` at `pc`**: a memory side with own map `ownGX L a`,
every state of the executable at `pc` `selfOwn`. -/
theorem ownAt_ownGX {ms : MemSide isa} {exe : _root_.Executable} {endPc pc : Int64}
    (hown : ∀ s, ms.own s = ownGX L a s)
    (hself : ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = pc → selfOwn L s) :
    Spike.Lib.X64.OwnAt ms exe endPc pc (tcbM L) (tcbM L) := fun s he hend hpc => by
  have h := hown s; exact h ▸ tcbM_mem_ownGX (hself s he hend hpc)

/-- **Main owns `tcbM` at `scc_rt_park`'s entry** (`seg_parkCall`'s
`hown` at `tp = tcbM`): own map `ownGX L a`, every state there on a pool
stack (`hsp`). -/
theorem ownAt_park {ms : MemSide isa} {exe : _root_.Executable} {endPc : Int64}
    (hown : ∀ s, ms.own s = ownGX L a s)
    (hsp : ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" → spPool L s)
    (hx : ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" →
      (L.lab ".Lscc_rt_start.x1").toBitVec.toNat ≤ Scc.Sem.X64.pcOf s) :
    Spike.Lib.X64.OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry")
      (tcbM L) (tcbM L) :=
  ownAt_ownGX hown fun s he hend hpc => .inl ⟨hsp s he hend hpc, hx s he hend hpc⟩

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ownS_of_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownS_of_self

/-- info: 'Spike.Lib.X64.WakePh.tcbM_mem_ownGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcbM_mem_ownGX

/-- info: 'Spike.Lib.X64.WakePh.ownAt_ownGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownAt_ownGX

/-- info: 'Spike.Lib.X64.WakePh.ownAt_park' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownAt_park
