/-
**The pre-spawn segments' invariants at main's `clone`, at hello's
three-level fragment** (hello.w, AArch64): the twin
of `Spike/Lib/A64WakeWcInv.lean`'s statement shapes at
`A64ConsumerA.I3` (`Spike/Lib/A64SegInstA3.lean`): hello allocates rodata's
buffer (the first allocation, `l`) and then main's box (the second, `l'`,
in the post-rodata segment) before the `clone`.

- `H0StmtH`: `h0` (before rodata's allocation, at `L0`) with its invariant
  containing the start's states and never at the clone (`clonePcH`).
- `H1StmtH`: for every fresh `l` the arena lands, the segment after rodata's
  allocation at `upd L0 l b` with the allocation fragment `I3` (the box
  allocates in it), containing rodata's landing (`Rd l b n`), never at the
  clone.
- `H2StmtH`: for every such `l` and every `l'` fresh at `upd L0 l b`, the
  segment after the box with no allocation, containing the box's landing
  (`Box l b n l' b' n'`), at the clone in `CloneInvH` at the twice extended
  placement.
- `i3_cloneInvH`: every pair of `I3` at the clone is in `CloneInvH` at its
  placement (`HPre`'s source of `ClonePreH`).
- `land_I3aH`, `land_I3bH`: rodata's and the box's landings are in `I3`.
- `H0TakeH`, `H1TakeH`, `H2TakeH`, `H0TakeOwnH`, `H1TakeOwnH`,
  `H2TakeOwnH`: the take site's range and the stacks' ownership at each
  level (main's `r0Of` before the box, the child's `r1Of` after it; the
  take of `r0` is `scc_rt_start`'s, before rodata, the child's in
  `wc_main` after the box).
- `hsplitH`: `OPrem.hsplit`'s shape at `I3` from the take facts (wake's
  `WakeOSplit.hsplit_W`'s argument at three levels).
-/
import Spike.Lib.A64SegInstA3
import Spike.Lib.A64HelloWcInv
import Spike.Lib.A64HeldOk2
import Spike.Lib.A64OwnedStackM
import Spike.Lib.WakeOSplit
import Spike.Lib.HelloOkW

namespace Spike.Lib.HelloPreA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize Owned Unowned HeldOk2)
open Spike.Lib.A64ConsumerA (SegInvS I3 TakeCKS)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.HelloSrc (helloSrc)

/-- **`h0` as hello's instance proves it**: the segment before rodata's
allocation with its invariant `inv0`, containing the start's states, never
at the clone. -/
def H0StmtH (W0 : FragS isaLSE2) (K : State → State → Prop) (L0 : Lbl)
    (ms0 : List TermRun.Frame → MemSide isaLSE2) (L : RuntimeLayout) (Start inv0 : FragS isaLSE2) : Prop :=
  SegInvS W0 K helloSrc L0 ms0 inv0 ∧ (∀ s c fs, Start s c fs → inv0 s c fs) ∧
    ∀ s c fs, inv0 s c fs → pcOf s ≠ clonePcH L

/-- **`h1` as hello's instance proves it**: for every fresh `l` the arena
places at `b` with `n` words, the segment after rodata's allocation with its
invariant `inv1 l b n` (at `ms1 l b n`, whose allocation fragment is `I3`:
the box allocates in it), containing rodata's landing `Rd l b n`, never at
the clone. -/
def H1StmtH (W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (K : State → State → Prop) (ar : Arena)
    (L0 : Lbl) (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2)
    (L : RuntimeLayout) (Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
    SegInvS (W1 l b n) K helloSrc (A64ConsumerA.upd L0 l b) (ms1 l b n) (inv1 l b n) ∧
    (∀ s c, Rd l b n s c → inv1 l b n s c []) ∧
    ∀ s c fs, inv1 l b n s c fs → pcOf s ≠ clonePcH L

/-- **`h2` as hello's instance proves it**: for every rodata label `l` and
every box label `l'` fresh at `A64ConsumerA.upd L0 l b` the arena places at `b'` with
`n'` words, the segment after the box with no allocation, containing the
box's landing `Box l b n l' b' n'`, at the clone in `CloneInvH` at the
twice extended placement. -/
def H2StmtH (W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (K : State → State → Prop) (ar : Arena) (L0 : Lbl)
    (ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2)
    (L : RuntimeLayout) (endPc : Int64)
    (Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n → A64ConsumerA.upd L0 l b l' = none →
    AllocLand ar.heap ar.cells b' n' →
    SegInvS (W2 l b n l' b' n') K helloSrc (A64ConsumerA.upd (A64ConsumerA.upd L0 l b) l' b') (ms2 l b n l' b' n') (inv2 l b n l' b' n') ∧
    (∀ s c, Box l b n l' b' n' s c → inv2 l b n l' b' n' s c []) ∧
    ∀ s c fs, inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      CloneInvH L endPc (A64ConsumerA.upd (A64ConsumerA.upd L0 l b) l' b') s c fs

section Stmt

variable {W0 : FragS isaLSE2} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
  {ms0 : List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout} {endPc : Int64} {Start inv0 : FragS isaLSE2}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}

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

/-- **Rodata's landing is in `I3`** at the extended placement (`h0`'s
`msOfA` `xa`). -/
theorem land_I3aH (h1 : H1StmtH W1 K ar L0 ms1 L Rd inv1) {l : WeakMem.AllocLabel} {b n : Nat} {s : State}
    {c : Ctl} (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hR : Rd l b n s c) :
    I3 ar L0 ls0 inv0 inv1 inv2 (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) s c [] :=
  Spike.Lib.A64ConsumerA.land_I3a hl hb ((h1 l b n hl hb).2.1 s c hR)

/-- **The box's landing is in `I3`** at the twice extended placement
(`h1`'s `msOfA` `xa`). -/
theorem land_I3bH (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box inv2) {l l' : WeakMem.AllocLabel} {b n b' n' : Nat}
    {s : State} {c : Ctl} (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hl' : A64ConsumerA.upd L0 l b l' = none)
    (hb' : AllocLand ar.heap ar.cells b' n') (hB : Box l b n l' b' n' s c) :
    I3 ar L0 ls0 inv0 inv1 inv2 (A64ConsumerA.upd (A64ConsumerA.upd L0 l b) l' b') (A64ConsumerA.updN (A64ConsumerA.updN ls0 l n) l' n') s c [] :=
  Spike.Lib.A64ConsumerA.land_I3b hl hb hl' hb' ((h2 l b n l' b' n' hl hb hl' hb').2.1 s c hB)

end Stmt

/-! ## The take facts -/

/-- **`h0`'s take range**: at the take pc `a`, `inv0`'s states have the
site's range main's stack. -/
def H0TakeH (L : RuntimeLayout) (a : Int64) (inv0 : FragS isaLSE2) : Prop :=
  ∀ s c fs, inv0 s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab

/-- **`h1`'s take range**: rodata's level never reaches the take pc (the
next take is the child's, after the box). -/
def H1TakeH (a : Int64) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n s c fs, inv1 l b n s c fs → pcOf s ≠ a.toBitVec.toNat

/-- **`h2`'s take range**: at the take pc `a`, the box level's states have
the site's range the child's stack. -/
def H2TakeH (L : RuntimeLayout) (a : Int64)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab

/-- **`h0`'s ownership at the take**: main's stack not in private memory. -/
def H0TakeOwnH (L : RuntimeLayout) (a : Int64) (inv0 : FragS isaLSE2) : Prop :=
  ∀ s c fs, inv0 s c fs → pcOf s = a.toBitVec.toNat →
    ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1

/-- **`h2`'s ownership at the take**: main's stack owned, the child's not
in private memory. -/
def H2TakeOwnH (L : RuntimeLayout) (a : Int64)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = a.toBitVec.toNat →
    Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1

/-- **`OPrem.hsplit`'s shape at `I3`**: at the take pc `a`, a fragment
state with held list `hl` takes `r0` with nothing held (`h0`'s) or `r1`
with `r0` held (`h2`'s); `h1`'s never there. The stacks `r0`, `r1` are
8-aligned of a word at least (`hr0`, `hr1`). -/
theorem hsplitH {L : RuntimeLayout} {a : Int64} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hr0 : (Spike.Lib.A64.Rt.Ti2.r0Of L.lab).lo % 8 = 0 ∧ 8 ≤ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab).size)
    (h0t : H0TakeH L a inv0) (h0o : H0TakeOwnH L a inv0) (h1t : H1TakeH a inv1)
    (h2t : H2TakeH L a inv2) (h2o : H2TakeOwnH L a inv2) :
    ∀ lbl lsize s c fs hl, I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs →
      HeldOk2 L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s hl →
      pcOf s = a.toBitVec.toNat →
      (hl = [] ∧ Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab) ∨
        (hl = [(0, Spike.Lib.A64.Rt.Ti2.r0Of L.lab)] ∧
          Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab) := by
  intro lbl lsize s c fs hl hI hH hpc
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, -, -, hi⟩ | ⟨l, b, n, l', b', n', -, -, -, -, -, -, hi⟩
  · have hr := h0t s c fs hi hpc
    have hu := h0o s c fs hi hpc
    rcases hH with ⟨rfl, -, -⟩ | ⟨-, ho, -⟩ | ⟨-, ho, -⟩
    · exact .inl ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho hu).elim
  · exact absurd hpc (h1t l b n s c fs hi)
  · have hr := h2t l b n l' b' n' s c fs hi hpc
    obtain ⟨ho0, hu1⟩ := h2o l b n l' b' n' s c fs hi hpc
    rcases hH with ⟨-, hu0, -⟩ | ⟨rfl, -, -⟩ | ⟨-, -, ho1⟩
    · exact (Spike.Lib.WakeOSplit.owned_not_unowned ho0 hu0 hr0.1 hr0.2).elim
    · exact .inr ⟨rfl, hr⟩
    · exact (Spike.Lib.A64Consumer.owned_not_stackM ho1 hu1).elim

/-! ## `I3` is not vacuous at hello

hello's two allocations before the `clone`: rodata's buffer at
`HelloOkW.lBH` (thread 0's allocation `1`, after the `ThreadId` box) and
main's box at `boxH` (allocation `2`). At the start's placement (main's
`ThreadId` label placed), both labels are fresh in turn, the box's landing
is in `I3`'s third level, and it is an allocation landing of `h1`'s memory
side (`msOfA … (I3 …)`'s `xa` at rodata's level): the box is allocated
inside the `h1` segment. -/

/-- **main's box label**: thread 0's allocation `2` in stripe `2`. -/
def boxH : WeakMem.AllocLabel := TermRun.freshLabel 0 2 0 2

theorem boxH_eq : boxH = 4 := rfl

section Example

/-- An arena of 100 cells at `0` (any arena holding both objects). -/
private def arX : Arena := ⟨0, 100, 4096, fun _ _ => 0, fun _ _ => 0, False, False⟩

/-- The start's placement: main's `ThreadId` label at `tcb`. -/
private def L0X (tcb : Nat) : Lbl := A64ConsumerA.upd (fun _ => none) (Spike.Lib.WakeT1.mainTidLbl 2) tcb

/-- Both labels are fresh in turn at the start's placement. -/
private theorem fresh2 (tcb : Nat) : L0X tcb Spike.Lib.HelloOkW.lBH = none ∧
    A64ConsumerA.upd (L0X tcb) Spike.Lib.HelloOkW.lBH 8 boxH = none := by
  simp [L0X, A64ConsumerA.upd, Spike.Lib.HelloOkW.lBH, boxH, Spike.Lib.WakeT1.mainTidLbl, TermRun.freshLabel]

/-- **The box's landing is in `I3`'s third level** at hello's labels, and
is an allocation landing of `h1`'s memory side at rodata's level. -/
example (tcb : Nat) {Λ : Scc.Sem.Layout} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} (ls0 : Lsize) (s : State) (c : Ctl) :
    let I := I3 arX (L0X tcb) ls0 (fun _ _ _ => True) (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ => True)
    I (A64ConsumerA.upd (A64ConsumerA.upd (L0X tcb) Spike.Lib.HelloOkW.lBH 8) boxH 48)
        (A64ConsumerA.updN (A64ConsumerA.updN ls0 Spike.Lib.HelloOkW.lBH 2) boxH 1) s c [] ∧
      (Spike.Lib.A64ConsumerA.msOfA Λ μ rd G own arX I (A64ConsumerA.upd (L0X tcb) Spike.Lib.HelloOkW.lBH 8)
        (A64ConsumerA.updN ls0 Spike.Lib.HelloOkW.lBH 2) []).xa boxH 48 1 s c := by
  intro I
  obtain ⟨hl, hl'⟩ := fresh2 tcb
  have hb : AllocLand arX.heap arX.cells 8 2 := by simp only [AllocLand, arX]; omega
  have hb' : AllocLand arX.heap arX.cells 48 1 := by simp only [AllocLand, arX]; omega
  have h := Spike.Lib.A64ConsumerA.land_I3b (inv0 := fun _ _ _ => True) (inv1 := fun _ _ _ _ _ _ => True)
    (inv2 := fun _ _ _ _ _ _ _ _ _ => True) (ls0 := ls0) (s := s) (c := c) (fs := []) hl hb hl' hb' trivial
  exact ⟨h, hb', h⟩

end Example

/-- info: 'Spike.Lib.HelloPreA.i3_cloneInvH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms i3_cloneInvH

/-- info: 'Spike.Lib.HelloPreA.hsplitH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsplitH

end Spike.Lib.HelloPreA
