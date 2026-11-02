/-
**hello.w's worker abort facts at every node of the child's run** (x86-64; the twin of
`Spike/Lib/A64HelloAbObl.lean`: the fragment, the marks' hypothesis and the node lemmas). The root's `hab1W`
(`X64HelloPostAbH.tw_step_hello`) asks `AbFacts μE AbT s` at every state of the worker's invariant `D.Wi`, which
lies inside `Pend (Z w)`. Taking the worker segment's fragment `Z := ZHR ∧ AbX μ lab`, the abort facts are the
fragment's second conjunct outright: `AbX` is `AbFacts μ (WriteAb.Ab lab)` of the state, with no disjunct, and
the bridge is `Pend`'s witness plus `MarksL μE lab` at the placed layout.

## The shape

- `AbX μ lab : FragS`: `X64HelloPostAb.AbFacts μ (WriteAb.Ab lab) s` (the frame list and the control unused).
- `MarksL μ lab`: the marks' take, release and abort sites are the addresses of `scc_rt_take_site`,
  `scc_rt_release_site` and `Link.abortName k`; the `writeErr` exit's label differs from the other four exits'.
- `pcOff_of`: a pc `PcOffA lab` (`X64WakeOffDef`, the five exits and the two transfer sites, by label) is
  `PcOff μ` under `MarksL`.
- `AbX.of_off`: `AbSt` and `PcOffA` give `AbX` (`at_` vacuous).
- `AbX.of_ab`: in the phase `WriteAb.Ab lab`, `AbSt` is vacuous; at the `writeErr` exit or off every exit
  (`hk`) `at_` holds (`MarksL.k_of_wexit`).

## The node lemmas

Each of `SegRP.ZObl`'s / `SegRP.WcObl`'s fields at `X := AbX μ lab` (the labels
`lab := (_root_.Executable.labels exe).label`) is a `NodeZA`, a `NodeW` or an `XProW` at one node. Two lemmas
cover every quiet node:

- `blkW_abX`: a covered block (`X64ConsumerA.blkW_abSt`'s premises: the code `hcode`, `okBlk` `hok`, the
  region, the block at `lab l + k` (`he`, `k` in bytes), its targets off the write abort's pcs `abOffH`, decided
  as `abOffHC_sound hlab chX` with `chX : abOffHC l k rl blk = true` by `decide +kernel` (`hph`), each `ret`'s
  target `hret`), its pcs `PcOffA` (`hoff`).
- `nodeW_abX`: a single instruction of `z` bytes other than a `syscall`, stepping to `pc + z` (`hstep`), its next
  pc off the write abort's pcs (`abSiH`; at hello's code labels `HelloWf.siAbH_sound`), its pc `PcOffA`.

The write abort's checks only (`abOffH`, `abSiH`): `HelloWf.phOffW` also checks the threads abort's pcs, which
include the spawn's next to the child's stub.

Unlike AArch64, instructions have their cells' sizes: a block's pcs are `n.pc + cellOff blk k`, a block sits at
`lab l + k` with `k` in bytes, a single instruction of `z` bytes steps to `pc + z` and is not a `syscall`
(A64's `svc`), a `ret`'s target is the slot at `%rsp` (`X64ConsumerA.blkAb_sound`), and the region needs no
alignment. The single-instruction check at hello's code labels is `X64HelloRefAbT`'s `HelloWf.siAbH`, so this
file states `abSiH` at any labels and no `abSiHC`.
-/
import Spike.Lib.X64HelloWorkerSegRP
import Spike.Lib.X64HelloPostAb
import Spike.Lib.X64HelloWfPh
import Spike.Lib.X64HelloRefAbT
import Spike.Lib.X64AbSt
import Spike.Lib.X64AllocAbOk

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt)
open Spike.Lib.X64 (CodeAt ND BlkW NodeW At okBlk classify arun cellOff)
open Scc.Sem (Marks TreeLeaf)
open Scc.Sem.X64 (pcOf abi codeLabel)
open SccCode (helloCells)
open Spike.Lib (FragS Region)
open Spike.Lib.X64.Flow.Worker (NodeZA NodeZ)
open Spike.Lib.X64Consumer (PcOff)
open Spike.Lib.X64ConsumerA (AbSt)
open Spike.Lib.X64HelloPostAb (AbFacts)
open Spike.Lib.X64WakeOff (PcOffA)

/-- **The worker's abort facts as a segment fragment**: `AbFacts` at the write abort's phase of the labels
`lab`. -/
def AbX (μ : Marks) (lab : Label → Int64) : FragS isa := fun s _ _ =>
  AbFacts μ (Spike.Lib.X64.WriteAb.Ab lab) s

/-- **The marks' sites at the labels**: the take, release and abort sites are the addresses of
`scc_rt_take_site`, `scc_rt_release_site` and the abort exits (`Link.abortName`); the `writeErr` exit is no other
exit. -/
structure MarksL (μ : Marks) (lab : Label → Int64) : Prop where
  take : ∀ a, μ.site .take = some a → a = (lab "scc_rt_take_site").toBitVec.toNat
  release : ∀ a, μ.site .release = some a → a = (lab "scc_rt_release_site").toBitVec.toNat
  abortAt : ∀ k a, μ.abortAt k = some a → a = (lab (Scc.Cert.Link.abortName k)).toBitVec.toNat
  wexit : ∀ k, k ≠ .writeErr → lab (Scc.Cert.Link.abortName k) ≠ lab "scc_rt_abort_write_exit"

section Marks

variable {μ : Marks} {lab : Label → Int64}

/-- A pc at the address of a label is the label. -/
theorem pc_eq_of {s : State} {l : Label} {a : Nat} (ha : a = (lab l).toBitVec.toNat) (hpc : pcOf s = a) :
    s.st.2 = lab l :=
  Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq ((show s.st.2.toBitVec.toNat = a from hpc).trans ha))

/-- **A pc off the exits and the transfer sites by label is off the marks' sites.** -/
theorem pcOff_of (hμ : MarksL μ lab) {s : State} (hq : PcOffA lab s.st.2) : PcOff μ s where
  noSite a ha hpc := hq.2.2.2.2.2.2 (pc_eq_of (hμ.release a ha) hpc)
  noTake a ha hpc := hq.2.2.2.2.2.1 (pc_eq_of (hμ.take a ha) hpc)
  noAbort k a ha hpc := by
    have heq := pc_eq_of (hμ.abortAt k a ha) hpc
    cases k
    · exact hq.1 heq
    · exact hq.2.1 heq
    · exact hq.2.2.1 heq
    · exact hq.2.2.2.2.1 heq
    · exact hq.2.2.2.1 heq

/-- **At the `writeErr` exit an abort site is `writeErr`'s.** -/
theorem MarksL.k_of_wexit (hμ : MarksL μ lab) {s : State} (hpc : s.st.2 = lab "scc_rt_abort_write_exit") :
    ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .writeErr := by
  intro k a ha hpc'
  exact if hk : k = .writeErr then hk else
    (hμ.wexit k hk (by rw [← pc_eq_of (hμ.abortAt k a ha) hpc', hpc])).elim

/-- **`AbX` off the exits**: `AbSt` there, and no abort site. -/
theorem AbX.of_off (hμ : MarksL μ lab) {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hab : AbSt μ (Spike.Lib.X64.WriteAb.Ab lab) s) (hq : PcOffA lab s.st.2) : AbX μ lab s c fs :=
  ⟨hab, fun k a ha hpc => ((pcOff_of hμ hq).noAbort k a ha hpc).elim⟩

/-- **`AbX` in the write abort's phase**: `AbSt` is vacuous; an abort site there is `writeErr`'s (`hk`:
`MarksL.k_of_wexit` at the exit, `pcOff_of` off it). -/
theorem AbX.of_ab {s : State} {c : Ctl} {fs : List TermRun.Frame} (hab : Spike.Lib.X64.WriteAb.Ab lab s)
    (hk : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .writeErr) : AbX μ lab s c fs :=
  ⟨⟨fun h => (h hab).elim, fun h => (h hab).elim, fun h => (h hab).elim⟩,
    fun k a ha hpc => ⟨hk k a ha hpc, hab⟩⟩

end Marks

/-! ## The write abort's checks

`HelloWf.phOffW`/`siOffW` check both abort phases' pcs; the child's run needs the write abort's only. -/

/-- **A block's targets off the write abort's pcs**, at `lab l + k` (bytes), every `ret` to `lab rl`
(`AllocG.blkAbC`). -/
def abOffH (lab : Label → Int64) (l : Label) (k : Nat) (rl : Label) (blk : List (Directive × Nat)) : Bool :=
  Spike.Lib.X64.AllocG.blkAbC lab (lab l + Int64.ofNat k) (lab rl) blk

/-- **A single instruction's next pc off the write abort's pcs**, the instruction of `z` bytes at `lab l + k`. -/
def abSiH (lab : Label → Int64) (l : Label) (k z : Nat) : Bool :=
  !(Spike.Lib.X64.WriteAb.abPcs lab).contains (lab l + Int64.ofNat k + Int64.ofNat z)

/-- The labels `abOffH` reads. -/
def abLabsH (l rl : Label) (blk : List (Directive × Nat)) : List String :=
  l :: rl :: Spike.Lib.LowerX64.blkLabs blk ++ Spike.Lib.X64.AllocG.abLabs

theorem abOffH_congr {lab lab' : Label → Int64} {l rl : Label} {k : Nat} {blk : List (Directive × Nat)}
    (h : ∀ x ∈ abLabsH l rl blk, lab x = lab' x) : abOffH lab l k rl blk = abOffH lab' l k rl blk := by
  unfold abOffH
  rw [Spike.Lib.X64.AllocG.blkAbC_congr (fun x hx => h x (by simp [abLabsH, hx]))
    (fun x hx => h x (by simp [abLabsH, hx])), h l (by simp [abLabsH]), h rl (by simp [abLabsH])]

/-- **`abOffH` at helloCells' code labels**, every label it reads resolving. -/
def abOffHC (l : Label) (k : Nat) (rl : Label) (blk : List (Directive × Nat)) : Bool :=
  (abLabsH l rl blk).all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) &&
    abOffH (Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells) l k rl blk

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → lab l = Int64.ofNat x)
include hlab

/-- The labels a check reads, resolving, are the code labels. -/
theorem lab_labCA {xs : List String}
    (h : xs.all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) = true) :
    ∀ x ∈ xs, lab x = Spike.Lib.LowerX64.labC Spike.Lib.X64.HelloPh.lo helloCells x := fun x hx => by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp h x hx)
  rw [hlab x y hy]; simp [Spike.Lib.LowerX64.labC, hy]

/-- **`abOffHC` at any labels agreeing with the code labels.** -/
theorem abOffHC_sound {l rl : Label} {k : Nat} {blk : List (Directive × Nat)} (h : abOffHC l k rl blk = true) :
    abOffH lab l k rl blk = true := by
  simp only [abOffHC, Bool.and_eq_true] at h
  rw [abOffH_congr (lab_labCA hlab h.1)]; exact h.2

end Sound

/-! ## The node lemmas -/

section Nodes

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`AbX` at a covered block's states** (`X64ConsumerA.blkW_abSt`), its targets off the write abort's pcs
(`hph`), its pcs off the exits and the transfer sites by label (`hoff`). -/
theorem blkW_abX (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l rl : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hoff : ∀ j < blk.length, PcOffA (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (cellOff blk j)))
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hph : abOffH (_root_.Executable.labels exe).label l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length), classify blk[j].1 = some .ret →
      Int64.ofBitVec ((arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ.slot
        (arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so.sp) =
        (_root_.Executable.labels exe).label rl) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n blk := by
  simp only [abOffH, he] at hph
  exact NodeZA.mono (NodeZA.and
      (Spike.Lib.X64ConsumerA.blkW_abSt hcode hok hR hlo hhi
        (fun j hj s _ _ hs => pcOff_of hμ (hs ▸ hoff j hj)) (Spike.Lib.X64ConsumerA.blkAb_sound hph hret))
      (NodeZ.toA (Z := fun s _ => PcOffA (_root_.Executable.labels exe).label s.st.2)
        fun _ _ _ j hj _ hs _ => by simp only; rw [hs]; exact hoff j hj))
    fun _ _ h => AbX.of_off hμ h.1 h.2

/-- **`AbX` at a single instruction without an event** (a cell of `z` bytes other than a `syscall` whose leaves
are `z` bytes on, `hstep`), its next pc off the write abort's pcs (`h`), its pc off the exits and the transfer
sites by label (`hoff`). -/
theorem nodeW_abX (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {l : Label} {k z : Nat}
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (h : abSiH (_root_.Executable.labels exe).label l k z = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hA
  simp only [abSiH, he, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hq : PcOffA (_root_.Executable.labels exe).label s.st.2 := hpc ▸ hoff
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.X64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h)
  refine ⟨AbX.of_off hμ (Spike.Lib.X64ConsumerA.AbSt.ofLeaves (pcOff_of hμ hq).noTake
    (Scc.Sem.X64.atSyscall_false_of_cellAt hc hd) fun t ht => ?_) hq, fun _ h => h⟩
  rw [hex] at ht; cases ht; exact Spike.Lib.X64Consumer.allInv_of_leaf tree hnab

end Nodes

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.pc_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.pc_eq_of

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.pcOff_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.pcOff_of

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.MarksL.k_of_wexit'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.MarksL.k_of_wexit

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.AbX.of_off'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.AbX.of_off

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.AbX.of_ab'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.AbX.of_ab

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abOffH_congr'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abOffH_congr

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.lab_labCA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.lab_labCA

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abOffHC_sound'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abOffHC_sound


/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.blkW_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.blkW_abX

/--
info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.nodeW_abX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.nodeW_abX
