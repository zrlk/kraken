/-
**hello.w's worker abort facts at every node of the child's run** (row 5i-hab1, AArch64; P1 of the row: the fragment,
the marks'
hypothesis and the node lemmas). The root's `hab1W`
(`HelloAssemblyRV.hello_obligations_RV`) asks `AbFacts μE AbT s` at every
state of the worker's invariant `D.Wi`, which lies inside `Pend (Z w)`
(`HelloWorkerRR.helloDR_inv`). Taking the worker segment's fragment
`Z := ZHR ∧ AbX μ lab` (`SegRP.seg_childPP`, `HelloAssemblyI.hsegIP`), the
abort facts are the fragment's second conjunct outright: `AbX` is
`AbFacts μ (WriteAb.Ab lab)` of the state, with no disjunct, and the bridge
(P5) is `Pend`'s witness plus `MarksL μE lab` at the placed layout.

## The shape

- `AbX μ lab : FragS`: `HelloPostAb.AbFacts μ (WriteAb.Ab lab) s` (the
  frame list and the control unused).
- `MarksL μ lab`: the marks' take, release and abort sites are the
  `codeOf` addresses of `scc_rt_take_site`, `scc_rt_release_site` and
  `Link.abortName k`; the `writeErr` exit's label differs from the other
  four exits'. P5 proves it at `μE` and the placed layout's labels
  (`A64AbOffL.off_of_A_ofPlaceOK`/`noSite_of_A_ofPlaceOK`'s argument).
- `pcOff_of`: a pc `PcOffA lab` (`A64WakeOffDef`, the five exits and the
  two transfer sites, by label) is `PcOff μ` under `MarksL`.
- `AbX.of_off`: `AbSt` and `PcOffA` give `AbX` (`at_` vacuous).
- `AbX.of_ab`: in the phase `WriteAb.Ab lab`, `AbSt` is vacuous; at the
  `writeErr` exit or off every exit (`hk`) `at_` holds (`MarksL.k_of_wexit`).

## The node lemmas (for P2, P3, P4)

Each of `SegRP.ZObl`'s / `SegRP.WcObl`'s fields at `X := AbX μ lab` (the
labels `lab := (_root_.Executable.labels exe).label`) is a `NodeZA`, a
`NodeW` or a `ProW` (four `NodeZA`/`NodeW` parts, `⟨w0, w1, w2, w3⟩`) at
one node. Two lemmas cover every quiet node:

- `blkW_abX`: a covered block (`A64ConsumerA.blkW_abSt`'s premises: the
  code `hcode`, `okBlk` `hok`, the region, the block at `lab l + 4k` (`he`),
  its targets off the write abort's pcs `abOffH`, decided as
  `abOffHC_sound hlab chX` with `chX : abOffHC l k rl blk = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel` (`hph`;
  a separate theorem per block, `A64HelloAbOblC.chC_cb` the template), each
  `ret`'s target `hret` (`A64Consumer.noRet_false (by decide)` for a
  `ret`-free block)), its pcs `PcOffA` (`hoff`, decided as
  `A64WakeOff.pcOffA_add (RunsOff.runsOffA_of_chk hp (by decide +kernel)) …`
  on a runs list of the piece's blocks; `A64HelloRunsOffM` is the
  template).
- `nodeW_abX`: a single instruction without an event stepping to `pc + 4`
  (`hstep`), its next pc off the write abort's pcs (`abSiHC_sound hlab`, the
  check `abSiHC` decided as `abOffHC`), its pc `PcOffA`.

The write abort's checks only (`abOffH`, `abSiH`): `HelloWf.phOffH` also
checks the threads abort's pcs, which include the spawn's next to the
child's stub, and fails there.

The code facts (`hcode`, `okBlk`) of every node of the child's run are the
ones `A64HelloRelZ` (`Wk.child_relH`, `thrPro_relH`, `thrHead_relH`,
`thrTail_relH`, `wcPro_relH`, `wE_relH`, `wCall_relH`, `tail_relH`,
`unpk_relH`, `print_relH`) uses; each piece mirrors that file, node by
node, with `blkW_abX`/`nodeW_abX` for its `rb`. The `hlab` premise
(`codeOf HelloPh.lo helloProg` labels) is `HelloOInit.hlab_H` at the
instance.

- P2 (stub, thread worker): `ZObl.hZc`, `hzT`, `hZEt`, `hZT`.
- P3 (`wc_worker`): `WcObl.hz`, `hZE`, `hZC`, `hZW`, `hZU`.
- P4 (`print`): `WcObl.hZP` (the `svc` node by
  `WakeWf.nodeW_abSt_svc`) and `hZA` (the abort path, `AbX.of_ab` and
  `AbX.of_off`).
- P5: `ZObl (AbX μ lab)` assembled, `MarksL` at the placed layout,
  `hab1W` from `hsegIP`, and an example at the child's entry state.
-/
import Spike.Lib.A64HelloWorkerSegRP
import Spike.Lib.HelloPostAb
import Spike.Lib.A64HelloWfPh
import Spike.Lib.A64RunsOff

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt)
open Spike.Lib.A64 (CodeAt)
open Scc.Sem (Marks TreeLeaf)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib (FragS Region)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.Flow.Worker (NodeZA NodeZ)
open Spike.Lib.A64Consumer (PcOff)
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.HelloPostAb (AbFacts)
open Spike.Lib.A64WakeOff (PcOffA)

/-- **The worker's abort facts as a segment fragment**: `AbFacts` at the
write abort's phase of the labels `lab`. -/
def AbX (μ : Marks) (lab : Label → Int64) : FragS isaLSE2 := fun s _ _ =>
  AbFacts μ (Spike.Lib.A64.WriteAb.Ab lab) s

/-- **The marks' sites at the labels**: the take, release and abort sites
are the addresses of `scc_rt_take_site`, `scc_rt_release_site` and the
abort exits (`Link.abortName`); the `writeErr` exit is no other exit. -/
structure MarksL (μ : Marks) (lab : Label → Int64) : Prop where
  take : ∀ a, μ.site .take = some a → a = (lab "scc_rt_take_site").toBitVec.toNat
  release : ∀ a, μ.site .release = some a → a = (lab "scc_rt_release_site").toBitVec.toNat
  abortAt : ∀ k a, μ.abortAt k = some a → a = (lab (Scc.Cert.Link.abortName k)).toBitVec.toNat
  wexit : ∀ k, k ≠ .writeErr → lab (Scc.Cert.Link.abortName k) ≠ lab "scc_rt_abort_write_exit"

section Marks

variable {μ : Marks} {lab : Label → Int64}

/-- A pc at the `codeOf` address of a label is the label. -/
theorem pc_eq_of {s : State} {l : Label} {a : Nat} (ha : a = (lab l).toBitVec.toNat) (hpc : pcOf s = a) :
    s.st.2 = lab l :=
  Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq ((show s.st.2.toBitVec.toNat = a from hpc).trans ha))

/-- **A pc off the exits and the transfer sites by label is off the marks'
sites.** -/
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
    (hab : AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s) (hq : PcOffA lab s.st.2) : AbX μ lab s c fs :=
  ⟨hab, fun k a ha hpc => ((pcOff_of hμ hq).noAbort k a ha hpc).elim⟩

/-- **`AbX` in the write abort's phase**: `AbSt` is vacuous; an abort site
there is `writeErr`'s (`hk`: `MarksL.k_of_wexit` at the exit, `pcOff_of`
off it). -/
theorem AbX.of_ab {s : State} {c : Ctl} {fs : List TermRun.Frame} (hab : Spike.Lib.A64.WriteAb.Ab lab s)
    (hk : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .writeErr) : AbX μ lab s c fs :=
  ⟨⟨fun h => (h hab).elim, fun h => (h hab).elim, fun h => (h hab).elim⟩,
    fun k a ha hpc => ⟨hk k a ha hpc, hab⟩⟩

end Marks

/-! ## The write abort's checks

`HelloWf.phOffH`/`siOffH` check both abort phases' pcs; the child's run
needs the write abort's only (the threads abort's pcs include the spawn's,
next to the child's stub, so `phOffH` fails there). -/

/-- **A block's targets off the write abort's pcs**, at `lab l + 4 k`, every
`ret` to `lab rl` (`AllocG.blkAbC`). -/
def abOffH (lab : Label → Int64) (l : Label) (k : Nat) (rl : Label) (blk : List Directive) : Bool :=
  Spike.Lib.A64.AllocG.blkAbC lab (lab l + Int64.ofNat (4 * k)) (lab rl) blk

/-- **A single instruction's next pc off the write abort's pcs**, at `lab l + 4 k`. -/
def abSiH (lab : Label → Int64) (l : Label) (k : Nat) : Bool :=
  !(Spike.Lib.A64.WriteAb.abPcs lab).contains (lab l + Int64.ofNat (4 * k) + 4)

/-- The labels `abOffH` reads. -/
def abLabsH (l rl : Label) (blk : List Directive) : List String :=
  l :: rl :: Spike.Lib.LowerA64.blkLabs blk ++ Spike.Lib.A64.AllocG.abLabs

theorem abOffH_congr {lab lab' : Label → Int64} {l rl : Label} {k : Nat} {blk : List Directive}
    (h : ∀ x ∈ abLabsH l rl blk, lab x = lab' x) : abOffH lab l k rl blk = abOffH lab' l k rl blk := by
  unfold abOffH
  rw [Spike.Lib.A64.AllocG.blkAbC_congr (fun x hx => h x (by simp [abLabsH, hx]))
    (fun x hx => h x (by simp [abLabsH, hx])), h l (by simp [abLabsH]), h rl (by simp [abLabsH])]

theorem abSiH_congr {lab lab' : Label → Int64} {l : Label} {k : Nat}
    (h : ∀ x ∈ abLabsH l l [], lab x = lab' x) : abSiH lab l k = abSiH lab' l k := by
  unfold abSiH
  rw [Spike.Lib.A64.AllocG.abPcs_congr (fun x hx => h x (by simp [abLabsH, hx])), h l (by simp [abLabsH])]

/-- **`abOffH` at helloProg's code labels**, every label it reads resolving. -/
def abOffHC (l : Label) (k : Nat) (rl : Label) (blk : List Directive) : Bool :=
  (abLabsH l rl blk).all (fun x => (Scc.Cert.Link.A64.codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    abOffH (Spike.Lib.LowerA64.labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg) l k rl blk

/-- **`abSiH` at helloProg's code labels**, every label it reads resolving. -/
def abSiHC (l : Label) (k : Nat) : Bool :=
  (abLabsH l l []).all (fun x => (Scc.Cert.Link.A64.codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    abSiH (Spike.Lib.LowerA64.labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg) l k

section Sound

variable {lab : Label → Int64}
  (hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x →
    lab l = Int64.ofNat x)
include hlab

/-- **`abOffHC` at any labels agreeing with the code labels.** -/
theorem abOffHC_sound {l rl : Label} {k : Nat} {blk : List Directive} (h : abOffHC l k rl blk = true) :
    abOffH lab l k rl blk = true := by
  simp only [abOffHC, Bool.and_eq_true] at h
  rw [abOffH_congr (Spike.Lib.A64.HelloWf.lab_labCH hlab h.1)]; exact h.2

/-- **`abSiHC` at any labels agreeing with the code labels.** -/
theorem abSiHC_sound {l : Label} {k : Nat} (h : abSiHC l k = true) : abSiH lab l k = true := by
  simp only [abSiHC, Bool.and_eq_true] at h
  rw [abSiH_congr (Spike.Lib.A64.HelloWf.lab_labCH hlab h.1)]; exact h.2

end Sound

/-! ## The node lemmas -/

section Nodes

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`AbX` at a covered block's states** (`A64ConsumerA.blkW_abSt`), its
targets off the write abort's pcs (`hph`), its pcs off the exits and the
transfer sites by label (`hoff`). -/
theorem blkW_abX (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {blk : List Directive} {lo hi : Int} {l rl : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hoff : ∀ j < blk.length, PcOffA (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * j)))
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hph : abOffH (_root_.Executable.labels exe).label l k rl blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ j (hj : j < blk.length) r, Spike.Lib.A64.Flow.classify blk[j] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take j)
        ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed
        = (_root_.Executable.labels exe).label rl) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n blk := by
  simp only [abOffH, he] at hph
  exact NodeZA.mono (NodeZA.and
      (Spike.Lib.A64ConsumerA.blkW_abSt hcode hok hR hal hlo hhi
        (fun j hj s _ _ hs => pcOff_of hμ (hs ▸ hoff j hj)) (Spike.Lib.A64ConsumerA.blkAb_sound hph hret))
      (NodeZ.toA (Z := fun s _ => PcOffA (_root_.Executable.labels exe).label s.st.2)
        fun _ _ _ j hj _ hs _ => by simp only; rw [hs]; exact hoff j hj))
    fun _ _ h => AbX.of_off hμ h.1 h.2

/-- **`AbX` at a single instruction without an event** (a cell other than an
`svc` whose leaves are 4 bytes on, `hstep`), its next pc off the write
abort's pcs (`h`), its pc off the exits and the transfer sites by label
(`hoff`). -/
theorem nodeW_abX (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {l : Label} {k : Nat}
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : abSiH (_root_.Executable.labels exe).label l k = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, CellAt s d 4 ∧
      (∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) ∧ isaLSE2.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeW (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  obtain ⟨d, tree, hc, hd, hex, hl⟩ := hstep s c hA
  simp only [abSiH, he, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hq : PcOffA (_root_.Executable.labels exe).label s.st.2 := hpc ▸ hoff
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.A64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h)
  refine ⟨AbX.of_off hμ (AbSt.ofLeaves (pcOff_of hμ hq).noTake (Scc.Sem.A64.atSvc_false_of_cellAt hc hd)
    fun t ht => ?_) hq, fun _ h => h⟩
  rw [hex] at ht; cases ht; exact Spike.Lib.A64Consumer.allInv_of_leaf tree hnab

end Nodes

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.blkW_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.blkW_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.nodeW_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.nodeW_abX
