/-
**`print`'s abort off the transfer sites, with no `exit`** (`HelloSegTCS.NoTop`,
x86-64): the x64 twin of the live part of
`Spike/Lib/A64HelloAbortX.lean`. The fragment `NNZXH` narrows `NNZH`
(`Spike/Lib/X64HelloNN.lean`) so that the worker's system calls are also not a
plain `exit`; the abort path's flat rows are then `OutTS` rows at `print`'s
frames (`HelloSegTCS.SegTCS.liftL` with `NoTop`; `noTopX`).

The stub's two system calls are `write(2, …)` and
`exit_group(abortStatus)` at `scc_rt_abort_write`'s pinned sites (`AbW`).
**What justifies them is still `safeH`'s `AbC` branch** (each call at its own site);
`NNXH` only adds that neither is a plain `exit`, the thread-only row
(`OutT.texit`) `NoTop` excludes.

- `NNXH`, `NNZXH`: `NNH` with the call not `exit`; with `Z`.
- `NNXH.toH`, `NNZXH.toH`: into `NNH`, `NNZH`.
- `noTopX`: no thread-only row at an `NNXH` state whose control is at no
  `unpark` binding.
- `abortRuns`, `abPc_of`: the abort path's pcs (the dispatcher's prefix up
  to its fourth test's taken jump and the `write` stub), as
  `Spike.Lib.X64.PcRuns.PcIn` runs; a pc `label l + off + x` in one.
  `hello_abortRunsOk`: the runs are in hello's listing (decided).

**Unlike AArch64** (forced by the x64 shape): the runs are byte ranges after
their labels (`Spike/Lib/X64PcRuns.lean`; AArch64: instruction counts, the pc
`label l + 4 j`), so `abPc_of` takes a byte offset `off` of the node and a
byte offset `x` of the state in it (AArch64: `j0`, `k`). The dispatcher's
labels are `scc_rt_abort`, `.Lscc_rt_abort.entry`/`.next1`/`.next3`/`.next5`,
`.is6` (each test with its jump to the next is one run of 18 bytes, the
fourth test alone 16); the `write` stub is `scc_rt_abort_write` (8 bytes of
prologue), `.Lscc_rt_abort_write.entry` (52 bytes: the `leaq`, the argument
block, the `syscall` at 34, the block after it) and the exit call (2 bytes).
The A64 file's `blkW_nnzX`, `nodeW_nnzX`, `nodeW_nnzXSvc`, `stubWW_nnzX`,
`seg_jabort4X` are dead in the hello proof (replaced by the `AbortObl` forms
of `Spike/Lib/X64HelloAbortObl.lean`) and are not twinned.
-/
import Spike.Lib.X64HelloNN
import Spike.Lib.X64PcRuns
import Spike.Lib.X64HelloCode

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.HelloSegTCS (NoTop)
open Spike.Lib.X64.PcRuns (PcIn runsOk)

/-- **A hello worker state off the transfer sites, its call not `exit`**
(`NNH`, the call also not a plain `exit`; `safeH`'s `AbC` branch still the
abort's justification). -/
def NNXH (exe : _root_.Executable) (endPc : Int64) (s : State) : Prop :=
  NNP (fun call => safeH (AbC exe s) call ∧ call ≠ .exit) exe endPc s

/-- **`NNXH` with `Z`.** -/
def NNZXH (exe : _root_.Executable) (endPc : Int64) (Z : Frag isa) : Frag isa :=
  fun s c => NNXH exe endPc s ∧ Z s c

variable {exe : _root_.Executable} {endPc : Int64} {Z : Frag isa}

theorem NNXH.toH {s : State} (h : NNXH exe endPc s) : NNH exe endPc s :=
  NNP.mono h fun _ h => h.1

theorem NNZXH.toH {s : State} {c : Ctl} (h : NNZXH exe endPc Z s c) : NNZH exe endPc Z s c :=
  ⟨h.1.toH, h.2⟩

/-- **No thread-only row at an `NNXH` state** whose control is at no
`unpark` binding (`hu`). -/
theorem noTopX {ms : MemSide isa} {s : State} {c : Ctl} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : NNXH exe endPc s) (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) : NoTop ms s c := by
  refine ⟨hu, fun K hk ha hd => ?_⟩
  rw [hK] at hk
  cases hk
  exact (h.2.2.2 ha _ hd).2 rfl

/-- **The abort path's pcs**: `scc_rt_abort`'s prologue, its first four
tests with their jumps (the fourth's taken), the jump to the `write` stub,
and the stub (prologue, entry block with its `write` call, exit call), as
byte ranges after their labels. -/
def abortRuns : List (Label × Nat × Nat) :=
  [("scc_rt_abort", 0, 12), (".Lscc_rt_abort.entry", 0, 18), (".Lscc_rt_abort.next1", 0, 18),
    (".Lscc_rt_abort.next3", 0, 18), (".Lscc_rt_abort.next5", 0, 16), (".Lscc_rt_abort.is6", 0, 9),
    ("scc_rt_abort_write", 0, 8), (".Lscc_rt_abort_write.entry", 0, 52), ("scc_rt_abort_write_exit", 0, 2)]

/-- **The runs are in hello's listing.** -/
theorem hello_abortRunsOk : runsOk SccCode.helloCells abortRuns = true := by decide +kernel

/-- **A pc `label l + off + x` of a run of `abortRuns`** is in it. -/
theorem abPc_of {s : State} {l : Label} {lo hi : Nat} {q : Int64} (hq : (l, lo, hi) ∈ abortRuns) (off x : Nat)
    (h1 : lo ≤ off + x) (h2 : off + x < hi) (he : s.exe = exe) (hs : s.st.2 = q + Int64.ofNat x)
    (hl : q = (_root_.Executable.labels exe).label l + Int64.ofNat off) :
    PcIn abortRuns s :=
  ⟨(l, lo, hi), hq, off + x, h1, h2, by rw [he, hs, hl, ← Flow.ofNat_add']⟩

end Spike.Lib.X64.Flow.Worker

/-- info: 'Spike.Lib.X64.Flow.Worker.abPc_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.abPc_of

/-- info: 'Spike.Lib.X64.Flow.Worker.noTopX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.noTopX
