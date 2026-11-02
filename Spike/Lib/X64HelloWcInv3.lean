/-
**The pre-spawn segments' invariants at main's `clone`, at hello's three-level fragment on x86-64** (the twin of
`Spike/Lib/A64HelloWcInv3.lean`): statement shapes at `X64ConsumerA.I3` (`Spike/Lib/X64SegInstA3.lean`): hello
allocates rodata's buffer (the first allocation, `l`) and then main's box (the second, `l'`, in the post-rodata
segment) before the `clone`.

- `H0StmtH`: `h0` (before rodata's allocation, at `L0`) with its invariant containing the start's states and
  never at the clone (`clonePcH`).
- `H1StmtH`: for every fresh `l` the arena lands, the segment after rodata's allocation at `upd L0 l b` with the
  allocation fragment `I3` (the box allocates in it), containing rodata's landing (`Rd l b n`), never at the
  clone; its rows may start after the source's publication (`SegInvSP`).
- `H2StmtH`: for every such `l` and every `l'` fresh at `upd L0 l b`, the segment after the box with no
  allocation, containing the box's landing (`Box l b n l' b' n'`), at the clone in `CloneInvH` at the twice
  extended placement.
- `i3_cloneInvH`: every pair of `I3` at the clone is in `CloneInvH` at its placement (`HPre`'s source of
  `ClonePreH`).
- `H0TakeH`, `H2TakeH`, `H0TakeOwnH`, `H2TakeOwnH`: the take site's range and the stacks' ownership at `h0`'s
  and `h2`'s levels (main's `r0Of` before the box, the child's `r1Of` after it).
- An `example`: `I3` is not vacuous at hello (the box's landing at hello's labels).

## Differences from the AArch64 version

- `H1StmtH`'s segment is a `SegInvSP` (`Spike/Lib/X64SegWPub.lean`), not a `SegInvS`: rodata publishes its
  buffer inside `h1`'s segment, and x86-64 has no fence instruction to carry the publication, so the source takes
  it as a stutter before the next row.
- Over x86-64's `X64ConsumerA` (`SegInvS`, `I3`, `upd`, `updN`, `msOfA`, `land_I3b`), `X64HelloSrc.helloSrc`,
  `X64HelloOkW.lBH`, `X64WakeSrcDefs.mainTidLbl`, `X64.Rt.Ti2.r0Of`, `X64.Rt.PreChild.r1Of`; `CloneInvH` and
  `clonePcH` are `X64HelloPreA`'s (no label prefix).
- A64's `H1TakeH`, `boxH`, `boxH_eq`, `hsplitH`, `land_I3aH`, `land_I3bH` are dead and not twinned (the
  example's box label is a private definition here, and it uses `X64ConsumerA.land_I3b` directly); the
  `WakeOSplit` import (`hsplitH`'s) is dropped.
-/
import Spike.Lib.X64SegInstA3
import Spike.Lib.X64HelloWcInv
import Spike.Lib.X64HeldOk2
import Spike.Lib.X64OwnedStackM
import Spike.Lib.X64HelloOkW
import Spike.Lib.Rt.X64RtPreChild
import Spike.Lib.Rt.X64RtTi2

namespace Spike.Lib.X64HelloPreA

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize Owned Unowned HeldOk2)
open Spike.Lib.X64ConsumerA (SegInvS I3 TakeCKS)
open Spike.Lib.X64SegWPub (SegInvSP)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- **`h0` as hello's instance proves it**: the segment before rodata's
allocation with its invariant `inv0`, containing the start's states, never
at the clone. -/
def H0StmtH (W0 : FragS isa) (K : State → State → Prop) (L0 : Lbl)
    (ms0 : List TermRun.Frame → MemSide isa) (L : RuntimeLayout) (Start inv0 : FragS isa) : Prop :=
  SegInvS W0 K helloSrc L0 ms0 inv0 ∧ (∀ s c fs, Start s c fs → inv0 s c fs) ∧
    ∀ s c fs, inv0 s c fs → pcOf s ≠ clonePcH L

/-- **`h1` as hello's instance proves it**: for every fresh `l` the arena
places at `b` with `n` words, the segment after rodata's allocation with its
invariant `inv1 l b n` (at `ms1 l b n`, whose allocation fragment is `I3`:
the box allocates in it), containing rodata's landing `Rd l b n`, never at
the clone. -/
def H1StmtH (W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) (K : State → State → Prop) (ar : Arena)
    (L0 : Lbl) (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa)
    (L : RuntimeLayout) (Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa) : Prop :=
  ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
    SegInvSP (W1 l b n) K helloSrc (X64ConsumerA.upd L0 l b) (ms1 l b n) (inv1 l b n) ∧
    (∀ s c, Rd l b n s c → inv1 l b n s c []) ∧
    ∀ s c fs, inv1 l b n s c fs → pcOf s ≠ clonePcH L

/-- **`h2` as hello's instance proves it**: for every rodata label `l` and
every box label `l'` fresh at `X64ConsumerA.upd L0 l b` the arena places at `b'` with
`n'` words, the segment after the box with no allocation, containing the
box's landing `Box l b n l' b' n'`, at the clone in `CloneInvH` at the
twice extended placement. -/
def H2StmtH (W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (K : State → State → Prop) (ar : Arena) (L0 : Lbl)
    (ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa)
    (L : RuntimeLayout) (endPc : Int64)
    (Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : Prop :=
  ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n → X64ConsumerA.upd L0 l b l' = none →
    AllocLand ar.heap ar.cells b' n' →
    SegInvS (W2 l b n l' b' n') K helloSrc (X64ConsumerA.upd (X64ConsumerA.upd L0 l b) l' b') (ms2 l b n l' b' n')
      (inv2 l b n l' b' n') ∧
    (∀ s c, Box l b n l' b' n' s c → inv2 l b n l' b' n' s c []) ∧
    ∀ s c fs, inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      CloneInvH L endPc (X64ConsumerA.upd (X64ConsumerA.upd L0 l b) l' b') s c fs

section Stmt

variable {W0 : FragS isa} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
  {ms0 : List TermRun.Frame → MemSide isa} {L : RuntimeLayout} {endPc : Int64} {Start inv0 : FragS isa}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

/-- **`HPre`'s fact from `R1`'s fragment at hello**: every pair of `I3` at
the clone is in `CloneInvH` at its placement (`h0`'s and `h1`'s never there,
`h2`'s in it). -/
theorem i3_cloneInvH (h0 : H0StmtH W0 K L0 ms0 L Start inv0) (h1 : H1StmtH W1 K ar L0 ms1 L Rd inv1)
    (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box inv2)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs) (hpc : pcOf s = clonePcH L) :
    CloneInvH L endPc lbl s c fs := by
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, hl, hb, -, -, hi⟩ | ⟨l, b, n, l', b', n', hl, hb, hl', hb', rfl, -, hi⟩
  · exact absurd hpc (h0.2.2 s c fs hi)
  · exact absurd hpc ((h1 l b n hl hb).2.2 s c fs hi)
  · exact (h2 l b n l' b' n' hl hb hl' hb').2.2 s c fs hi hpc

end Stmt

/-! ## The take facts -/

/-- **`h0`'s take range**: at the take pc `a`, `inv0`'s states have the
site's range main's stack. -/
def H0TakeH (L : RuntimeLayout) (a : Int64) (inv0 : FragS isa) : Prop :=
  ∀ s c fs, inv0 s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = Spike.Lib.X64.Rt.Ti2.r0Of L.lab

/-- **`h2`'s take range**: at the take pc `a`, the box level's states have
the site's range the child's stack. -/
def H2TakeH (L : RuntimeLayout) (a : Int64)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : Prop :=
  ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.X64.abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab

/-- **`h0`'s ownership at the take**: main's stack not in private memory. -/
def H0TakeOwnH (L : RuntimeLayout) (a : Int64) (inv0 : FragS isa) : Prop :=
  ∀ s c fs, inv0 s c fs → pcOf s = a.toBitVec.toNat →
    ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s.st.1

/-- **`h2`'s ownership at the take**: main's stack owned, the child's not
in private memory. -/
def H2TakeOwnH (L : RuntimeLayout) (a : Int64)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : Prop :=
  ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = a.toBitVec.toNat →
    Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s.st.1

/-! ## `I3` is not vacuous at hello

hello's two allocations before the `clone`: rodata's buffer at
`HelloOkW.lBH` (thread 0's allocation `1`, after the `ThreadId` box) and
main's box at `boxH` (allocation `2`). At the start's placement (main's
`ThreadId` label placed), both labels are fresh in turn, the box's landing
is in `I3`'s third level, and it is an allocation landing of `h1`'s memory
side (`msOfA … (I3 …)`'s `xa` at rodata's level): the box is allocated
inside the `h1` segment. -/

section Example

/-- **main's box label**: thread 0's allocation `2` in stripe `2`. -/
private def boxH : WeakMem.AllocLabel := TermRun.freshLabel 0 2 0 2

/-- An arena of 100 cells at `0` (any arena holding both objects). -/
private def arX : Arena := ⟨0, 100, 4096, fun _ _ => 0, fun _ _ => 0, False, False⟩

/-- The start's placement: main's `ThreadId` label at `tcb`. -/
private def L0X (tcb : Nat) : Lbl := X64ConsumerA.upd (fun _ => none) (Spike.Lib.X64WakeSrcDefs.mainTidLbl 2) tcb

/-- Both labels are fresh in turn at the start's placement. -/
private theorem fresh2 (tcb : Nat) : L0X tcb Spike.Lib.X64HelloOkW.lBH = none ∧
    X64ConsumerA.upd (L0X tcb) Spike.Lib.X64HelloOkW.lBH 8 boxH = none := by
  simp [L0X, X64ConsumerA.upd, Spike.Lib.X64HelloOkW.lBH, boxH, Spike.Lib.X64WakeSrcDefs.mainTidLbl, TermRun.freshLabel]

/-- **The box's landing is in `I3`'s third level** at hello's labels, and
is an allocation landing of `h1`'s memory side at rodata's level. -/
example (tcb : Nat) {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64ConsumerS.OwnS} (ls0 : Lsize) (s : State) (c : Ctl) :
    let I := I3 arX (L0X tcb) ls0 (fun _ _ _ => True) (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ => True)
    I (X64ConsumerA.upd (X64ConsumerA.upd (L0X tcb) Spike.Lib.X64HelloOkW.lBH 8) boxH 48)
        (X64ConsumerA.updN (X64ConsumerA.updN ls0 Spike.Lib.X64HelloOkW.lBH 2) boxH 1) s c [] ∧
      (Spike.Lib.X64ConsumerA.msOfA Λ μ rd G own arX I (X64ConsumerA.upd (L0X tcb) Spike.Lib.X64HelloOkW.lBH 8)
        (X64ConsumerA.updN ls0 Spike.Lib.X64HelloOkW.lBH 2) []).xa boxH 48 1 s c := by
  intro I
  obtain ⟨hl, hl'⟩ := fresh2 tcb
  have hb : AllocLand arX.heap arX.cells 8 2 := by simp only [AllocLand, arX]; omega
  have hb' : AllocLand arX.heap arX.cells 48 1 := by simp only [AllocLand, arX]; omega
  have h := Spike.Lib.X64ConsumerA.land_I3b (inv0 := fun _ _ _ => True) (inv1 := fun _ _ _ _ _ _ => True)
    (inv2 := fun _ _ _ _ _ _ _ _ _ => True) (ls0 := ls0) (s := s) (c := c) (fs := []) hl hb hl' hb' trivial
  exact ⟨h, hb', h⟩

end Example

end Spike.Lib.X64HelloPreA

/-- info: 'Spike.Lib.X64HelloPreA.i3_cloneInvH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.i3_cloneInvH
