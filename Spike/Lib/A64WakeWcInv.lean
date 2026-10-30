/-
**The pre-spawn segments' invariants at main's `clone`** (wake.w, AArch64): the statement shapes of `WakePreAsm.pre1T_of_seg`'s `h0` (before the
box's allocation, at the placement `L0`) and `h1` (after it, at `upd L0 l b`)
as this branch proves them, and what their invariants say at the clone's
`svc` (`cloneAt pfxM`): the fact `HPre` reads from `R1`'s fragment `I2`.

- `clonePc L`: the clone's pc as a number (label based, no literal).
- `CloneInv L endPc lbl s c fs`: at the clone, the source stack empty (main
  is the source's root), the machine side `ClonePost`, the source at
  `spawnTerm` with `c` bound to a label placed at `x9` and `me` to main's
  `ThreadId` label placed at `x10`.
- `H0Stmt`, `H1Stmt`: `h0`/`h1` with their invariant's facts at the clone
  (`h0`'s never reaches it; `h1`'s is there in `CloneInv`) and the entry
  (`h0`: the start's states, `Start`; `h1`: the box's landing, `Box`).
- `i2_cloneInv`: every pair of `I2 ar L0 ls0 inv0 inv1` at the clone is in
  `CloneInv` at its placement (`HPre`'s source of `ClonePre` and `ClonePost`).
- `land_I2`: the box's landing in `h1`'s entry is in `I2` at the extended
  placement (`msOfA`'s `xa` for `h0`'s memory side).
- `H0Take`, `H1Take`: the take site's range at each invariant's states at
  the take pc `a` (main's stack `r0Of` before the allocation, the child's
  `r1Of` after it), for `OPrem.hsplit` (with `HeldOk2`'s held list).
- `H0TakeOwn`, `H1TakeOwn`: the stacks' ownership there (`¬ StackM r0`
  before the allocation; `Owned r0 ∧ ¬ StackM r1` after it, `StackM`
  every aligned word of `r1` loading), fixing the held list (`[]`, `[(0, r0)]`).
- `clone_decode_of_post`, `clone_decode`: the clone's call decodes there
  (`Cl`'s third conjunct).
-/
import Spike.Lib.A64WakeWcSeg
import Spike.Lib.A64SFactsACH
import Spike.Lib.Rt.A64RtTi2
import Spike.Lib.A64OwnedPz

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range Marks Entry)
open Scc.Sem.A64 (pcOf)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.WakeT1 (mainTidLbl wakeSrc)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SegInvS I2)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.WakePreA (cloneAt spawnTerm)

/-- **The clone's pc** in `L`'s executable, as `pcOf` reads it. -/
def clonePc (L : RuntimeLayout) : Nat := (cloneAt pfxM L.exe).toBitVec.toNat

/-- **The pair at main's `clone`** at the placement `lbl`: the source stack
empty, the machine side `ClonePost` (for some caller node `J` and thread
pointer `t`), the source at `spawnTerm` with no hold, `c` bound to the
locative of a label `l` placed at `x9`'s value and `me` to main's
`ThreadId` locative, its label placed at `x10`'s value, and `p` bound.
`ClonePost`'s `wcNS` pins `x8 = 220`, `x0 = cloneFlags`, `x2 = x4 = 0`, so
the clone's call decodes (`clone_decode`, `ClW`'s third conjunct). -/
def CloneInv (L : RuntimeLayout) (endPc : Int64) (lbl : Lbl) : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ ∃ (J : AS → Ctl → Prop) (t : UInt64) (l : WeakMem.AllocLabel), ClonePost L endPc J t s c ∧
    c.term = spawnTerm ∧ c.hold = none ∧
    TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
    TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]) ∧
    (∃ rt ws, TermRun.evalAt c.env (.var "p") = some (rt, ws)) ∧
    lbl l = some (s.st.1.regs.getXReg .X9).toNat ∧ lbl (mainTidLbl 2) = some (s.st.1.regs.getXReg .X10).toNat

/-- **`h0` as this branch proves it**: the segment before the box's
allocation with its invariant `inv0` (`pre1T_of_seg`'s `h0` at `ms0`, the
memory side `msOfA … (I2 ar L0 ls0 inv0 inv1) L0 ls0`), containing the
start's states (`Start`, for `hinit`), never at the clone. -/
def H0Stmt (W0 : FragS isaLSE2) (K : State → State → Prop) (L0 : Lbl)
    (ms0 : List TermRun.Frame → MemSide isaLSE2) (L : RuntimeLayout) (Start inv0 : FragS isaLSE2) : Prop :=
  SegInvS W0 K wakeSrc L0 ms0 inv0 ∧ (∀ s c fs, Start s c fs → inv0 s c fs) ∧
    ∀ s c fs, inv0 s c fs → pcOf s ≠ clonePc L

/-- **`h1` as this branch proves it**: for every fresh `l` the arena places
at `b` with `n` bytes, the segment after the allocation with its invariant
`inv1 l b n` (`pre1T_of_seg`'s `h1` at `ms1 l b n`, the memory side with no
allocation), containing the box's landing (`Box l b n`, `wake_wc_mid_hatW`'s
entry with the thread pointer), at the clone in `CloneInv` at `upd L0 l b`.

The clone conjunct holds at EVERY `inv1` state at `clonePc` (not only at the
segment's run into the clone): WakeOD's `ClW` (`pcOf s = clonePc L ∧
abi.atSys s ∧ ∃ st tl, decode … = some (.clone st tl)`) is consumed at the
negative sites (the `NodesA` rows, `AbortPathSC.sysC`, `AcSt.acSys`), which
get the `decode` conjunct from it by `clone_decode`. -/
def H1Stmt (W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) (K : State → State → Prop) (ar : Arena)
    (L0 : Lbl) (ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2)
    (L : RuntimeLayout) (endPc : Int64) (Box : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
    SegInvS (W1 l b n) K wakeSrc (A64ConsumerA.upd L0 l b) (ms1 l b n) (inv1 l b n) ∧
    (∀ s c, Box l b n s c → inv1 l b n s c []) ∧
    ∀ s c fs, inv1 l b n s c fs → pcOf s = clonePc L → CloneInv L endPc (A64ConsumerA.upd L0 l b) s c fs

/-- **`HPre`'s fact from `R1`'s fragment**: every pair of `I2` at the clone
is in `CloneInv` at its placement (`h0`'s never there, `h1`'s in it). -/
theorem i2_cloneInv {W0 : FragS isaLSE2} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
    {ms0 : List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout} {endPc : Int64} {Start inv0 : FragS isaLSE2}
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {ar : Arena}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {Box : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h0 : H0Stmt W0 K L0 ms0 L Start inv0) (h1 : H1Stmt W1 K ar L0 ms1 L endPc Box inv1)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs) (hpc : pcOf s = clonePc L) : CloneInv L endPc lbl s c fs := by
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, hl, hb, rfl, -, hi⟩
  · exact absurd hpc (h0.2.2 s c fs hi)
  · exact (h1 l b n hl hb).2.2 s c fs hi hpc

/-- **The box's landing is in `I2` at the extended placement** (`h0`'s
`msOfA` `xa`: `AllocLand` and `I2` at `upd L0 l b`, `updN ls0 l n`). -/
theorem land_I2 {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop} {ar : Arena}
    {L0 : Lbl} {ls0 : Lsize} {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    {L : RuntimeLayout} {endPc : Int64} {Box : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
    {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h1 : H1Stmt W1 K ar L0 ms1 L endPc Box inv1) {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl}
    (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hB : Box l b n s c) :
    I2 ar L0 ls0 inv0 inv1 (A64ConsumerA.upd L0 l b) (A64ConsumerA.updN ls0 l n) s c [] :=
  .inr ⟨l, b, n, hl, hb, rfl, rfl, (h1 l b n hl hb).2.1 s c hB⟩

/-- **`h0`'s take range**: at the take pc `a`, `inv0`'s states have the
site's range main's stack (`Ti2.r0Of`). -/
def H0Take (L : RuntimeLayout) (a : Int64) (inv0 : FragS isaLSE2) : Prop :=
  ∀ s c fs, inv0 s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.Ti2.r0Of L.lab

/-- **`h1`'s take range**: at the take pc `a`, every `inv1 l b n`'s states
have the site's range the child's stack (`PreChild.r1Of`). -/
def H1Take (L : RuntimeLayout) (a : Int64) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n s c fs, inv1 l b n s c fs → pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange Scc.Sem.A64.abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab

/-- **`h0`'s ownership at the take**: at the take pc `a`, `inv0`'s states
own neither stack (main's `r0Of` not in private memory, `¬ StackM`), fixing `HeldOk2`'s
held list to `[]`. -/
def H0TakeOwn (L : RuntimeLayout) (a : Int64) (inv0 : FragS isaLSE2) : Prop :=
  ∀ s c fs, inv0 s c fs → pcOf s = a.toBitVec.toNat →
    ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s.st.1

/-- **`h1`'s ownership at the take**: at the take pc `a`, every `inv1 l b n`'s
states own main's stack `r0Of` and the child's `r1Of` is not in private
memory (`¬ StackM`, refuting it owned), fixing
`HeldOk2`'s held list to `[(0, r0)]`. -/
def H1TakeOwn (L : RuntimeLayout) (a : Int64) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) : Prop :=
  ∀ l b n s c fs, inv1 l b n s c fs → pcOf s = a.toBitVec.toNat →
    Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1

/-- **The clone's call decodes** at `ClonePost`: `wcNS`'s `x8 = 220`,
`x0 = cloneFlags`, `x2 = 0`, `x4 = 0` (`clone(flags, k, 0, t, 0)`), for
`Cl`'s `decode` conjunct (`OPrem.hClc`). -/
theorem clone_decode_of_post {L : RuntimeLayout} {endPc : Int64} {J : AS → Ctl → Prop} {t : UInt64}
    {s : State} {c : Ctl} (h : ClonePost L endPc J t s c) :
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl) := by
  obtain ⟨_, _, _, _, _, _, -, -, ⟨-, -, -, -, σ, hA, -, hJ⟩, -⟩ := h
  obtain ⟨-, h0, -, h2, -, h4, h8, -⟩ := hJ
  have hr := hA.regs
  refine ⟨σ.regs.X1.toNat, σ.regs.X3.toNat, ?_⟩
  simp only [Scc.Sem.Kernel.decode, Scc.Sem.A64.abi, Scc.Sem.A64.xRegs, hr]
  have e8 : σ.regs.X8.toNat = 220 := by rw [← UInt64.toNat_toBitVec, h8]; rfl
  have e0 : σ.regs.X0.toNat = 855808 := by rw [← UInt64.toNat_toBitVec, h0]; rfl
  have e2 : σ.regs.X2.toNat = 0 := by rw [← UInt64.toNat_toBitVec, h2]; rfl
  have e4 : σ.regs.X4.toNat = 0 := by rw [← UInt64.toNat_toBitVec, h4]; rfl
  simp [e8, e0, e2, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.Kernel.cloneFlags]
  exact ⟨e4, rfl⟩

/-- **The clone's call decodes** at `CloneInv`. -/
theorem clone_decode {L : RuntimeLayout} {endPc : Int64} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : CloneInv L endPc lbl s c fs) :
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl) := by
  obtain ⟨-, _, _, _, hP, -⟩ := h
  exact clone_decode_of_post hP

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.i2_cloneInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.i2_cloneInv

/-- info: 'Spike.Lib.A64.Flow.WakeWc.land_I2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.land_I2

/-- info: 'Spike.Lib.A64.Flow.WakeWc.clone_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.clone_decode
