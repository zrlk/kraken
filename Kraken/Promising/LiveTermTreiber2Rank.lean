/-
**Stage 4: the rank table of the
`treiber2` termination proof**, indexed by the positions of `treiber2DWorker`
(`LiveTermTreiber2Trees.lean`). Layout-free definitions shared by
`LiveTermTreiber2P.lean` (the position-parametric proof) and
`LiveTermTreiber2.lean` (its `treiber2DWorker` instance); the `#tk_clone`
modules `LiveTermTreiber2Arm.lean` and `LiveTermTreiber2Relaxed.lean` clone
this file beside `LiveTermTreiber2.lean`. Namespace `Live.TermTreiber2`
(unchanged); the rank itself is explained in `LiveTermTreiber2.lean`.
-/
import Kraken.Promising.LiveTerm
import Kraken.Promising.SLR.A64Trees

namespace Kraken.Promising.Live.TermTreiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The stack's `top`. -/
abbrev topL (t : BitVec 64) : Loc := ⟨t, 8⟩

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

/-- The register fact at each position: `X3 = X2` at the `CASAL`s. -/
def PcI (s : MachineData) : Nat → Prop
  | 6 => s.regs.X3.toBitVec = s.regs.X2.toBitVec
  | 14 => s.regs.X3.toBitVec = s.regs.X2.toBitVec
  | _ => True

/-- The flag term: `10` unless `X2` holds the current value of `top`. -/
def fl (s : MachineData) (cur : Val) : Nat :=
  if s.regs.X2.toBitVec = BitVec.setWidth 64 cur then 0 else 10

/-- **The rank at position `p`** (registers `s`, `cnt` writes to `top` at or
below the coherence view, current value `cur`); `N` bounds `cnt`. -/
def rk (N p : Nat) (s : MachineData) (cnt : Nat) (cur : Val) : Nat :=
  match p with
  | 1 => 42 + 20 * N
  | 3 => 32 + 10 * N + 10 * (N - cnt)
  | 4 => 31 + 10 * N + 10 * (N - cnt) + fl s cur
  | 5 => 30 + 10 * N + 10 * (N - cnt) + fl s cur
  | 6 => 29 + 10 * N + 10 * (N - cnt) + fl s cur
  | 7 => if s.regs.X3.toBitVec = s.regs.X2.toBitVec then 26 + 10 * N else 35 + 10 * N + 10 * (N - cnt)
  | 8 => if s.status.z = true then 25 + 10 * N else 34 + 10 * N + 10 * (N - cnt)
  | 10 => 12 + 10 * (N - cnt)
  | 11 => 11 + 10 * (N - cnt) + fl s cur
  | 12 => 10 + 10 * (N - cnt) + fl s cur
  | 13 => 9 + 10 * (N - cnt) + fl s cur
  | 14 => 8 + 10 * (N - cnt) + fl s cur
  | 15 => if s.regs.X3.toBitVec = s.regs.X2.toBitVec then 5 else 14 + 10 * (N - cnt)
  | 16 => if s.status.z = true then 4 else 13 + 10 * (N - cnt)
  | 17 => 3
  | 18 => 2
  | 19 => 1
  | _ => 0

/-- The successful `CASAL`s executed, read off position and registers. -/
def sOf (p : Nat) (s : MachineData) : Nat :=
  match p with
  | 7 => if s.regs.X3.toBitVec = s.regs.X2.toBitVec then 1 else 0
  | 8 => if s.status.z = true then 1 else 0
  | 10 | 11 | 12 | 13 | 14 => 1
  | 15 => if s.regs.X3.toBitVec = s.regs.X2.toBitVec then 2 else 1
  | 16 => if s.status.z = true then 2 else 1
  | 17 | 18 | 19 | 21 => 2
  | _ => 0

/-- The bound on `cnt` for `n` threads. -/
def cntBound (n fuel : Nat) : Nat := n * (2 + fuel)

end Kraken.Promising.Live.TermTreiber2
