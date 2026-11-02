/-
**hello.w's state at main's `clone` decodes as a `clone` call on x86-64** (the twin of
`Spike/Lib/A64HelloWcInv.lean`; wake's x86-64 version is `Spike/Lib/X64WakeWcInv.lean`): the machine-only part
at hello's `ClonePostH` (`X64HelloClonePreHOf`).

- `clonePcH L`: the clone's pc as a number (label based, no literal), `cloneAtH`.
- `clone_decode_of_postH`: at `ClonePostH` (`wcNSH`'s `%rax = 56`, `%rdi = cloneFlags`, `%rdx = %r10 = 0`) the
  clone's call decodes (`Cl`'s third conjunct).

## Differences from the AArch64 version

- The call decodes from `wcNSH`'s registers by `WcSp6.wcNSH_call` (as wake's x86-64 `WcClone.wcNS_call`;
  A64's `x8 = 220`, `x0`, `x2`, `x4` spelled out here); `cloneAtH` has no label prefix.
- A64's `clone_decodeH` (at `CloneInvH`) is dead and not twinned.
-/
import Spike.Lib.X64HelloClonePreHOf

namespace Spike.Lib.X64HelloPreA

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **The clone's pc** in `L`'s executable, as `pcOf` reads it. -/
def clonePcH (L : RuntimeLayout) : Nat := (cloneAtH L.exe).toBitVec.toNat

/-- **The clone's call decodes** at `ClonePostH`: `wcNSH`'s `%rax = 56`, `%rdi = cloneFlags`, `%rdx = %r10 = 0`
(`clone(flags, k, 0, 0, t)`), for `Cl`'s `decode` conjunct. -/
theorem clone_decode_of_postH {L : RuntimeLayout} {endPc : Int64} {t : UInt64} {s : State} {c : Ctl}
    (h : ClonePostH L endPc t s c) :
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
      some (.clone st tl) := by
  obtain ⟨_, _, _, _, _, _, _, _, -, ⟨-, -, -, -, σ, hA, -, hJ⟩, -⟩ := h
  have hc := Spike.Lib.X64.HelloPh.WcSp6.wcNSH_call hJ
  rw [← hA.regs] at hc
  exact ⟨_, _, hc⟩

end Spike.Lib.X64HelloPreA

/-- info: 'Spike.Lib.X64HelloPreA.clone_decode_of_postH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.clone_decode_of_postH
