/-
**`AbX` at `print`'s nodes** (x86-64; the twin of `Spike/Lib/A64HelloAbOblP.lean`, `X64HelloAbObl`'s recipe):
`WcObl.hZP` (`X64HelloWorkerSegRP`) at `X := AbX μ lab`, from the generic `PrintG.printAb` (`AbSt` at `print`'s
blocks, the tests' blocks kept by the stored result) and `PrintG.printSvcAb` (the system call's refusal), at an
instance `instOkP` of `Rt.InstOk` with no phase (`ph := 0`), no owned words and no outside move, its off-site pcs
those of none of `abPtsA`'s labels (`okPcH`); `AbX`'s abort-site half from print's pcs off the exits
(`printRuns_chk`).

- `okPcH`, `instOkP`: the instance.
- `printPLabs`, `printPLabs_chk`, `printPLabs_eq`: the labels the checks read, at the code labels.
- `printPhP_chk`, `printPhP`: the phase check at it (decided at the code labels, `PrintG.printPhOk`).
- `printRuns`, `printRuns_chk`: print's pcs off the exits and the transfer sites.
- `wcRet_chk`: `wc_worker`'s return address `.x17` off the write abort's pcs.
- `NodeW.toZA1`: a single cell's `NodeW` as its `NodeZA` (`FStable`).
- `nodeZA_abX_of`: `AbX` at a node from `AbSt` there, with the thread pointer.
- `print_abX`: `AbX` at every node of `print` entered at `σC`, the count below `2^63` and the return address off
  the write abort's pcs.
- `wcRet_abX`: that return address at `wc_worker`'s call.

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants): `wcPrint_abX`.

Unlike AArch64 (a barrier node `.fence`, the `svc` at `.2_write + 4·5`, the return address in `x30`, the count in
`x1`, a 16-aligned region `[-48, 0]`, the phase check `printPhOkF` with the barrier's labels), `print` has no
barrier, its system call is the `syscall` at `.write + 20` (`.sys`), the return address is the caller's cell
`ko` (`-96` at `wc_worker`'s call, the `.x17` the `call` pushes), the count is `%rsi`, the region is `[-40, 16]`
with no alignment, the phase check is `PrintG.printPhOk`, and the pcs are byte offsets.
-/
import Spike.Lib.X64HelloAbOblU
import Spike.Lib.X64PrintGAb
import Spike.Lib.X64HelloPrintNN

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Scc.Sem.X64 (codeLabel)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region)
open Spike.Lib.X64 (ND NodeW BlkW At AS cellOff)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Worker (NodeZA NodeZ)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64WakeOff (PcOffA RunsOffA pcOffA_add)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open Spike.Lib.LowerX64 (labC)
open SccCode (helloCells)

/-! ## The instance -/

/-- **The off-site pcs**: none of `abPtsA`'s labels' code addresses. -/
def okPcH (p : Nat) : Bool :=
  abPtsA.all fun q => p != (labC Spike.Lib.X64.HelloPh.lo helloCells q.1).toBitVec.toNat

/-- The labels `printPhOk` and `abPcs` read, `abPtsA`'s and `wc_worker`'s return label `.x17`. -/
def printPLabs : List String :=
  Spike.Lib.X64.PrintG.printLabs ++ Spike.Lib.X64.AllocG.abLabs ++ abPtsA.map Prod.fst ++ [".Lwc_worker.x17"]

theorem printPLabs_chk :
    printPLabs.all (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) = true := by
  decide +kernel

/-- **The phase check at the code labels** with no phase. -/
theorem printPhP_chk :
    Spike.Lib.X64.PrintG.printPhOk okPcH (fun _ => 0) (labC Spike.Lib.X64.HelloPh.lo helloCells) = true := by
  decide +kernel

/-- **`print`'s pcs**: its blocks from each label (the system call in `.write`'s 44 bytes). -/
def printRuns : List (Label × Nat × Nat) :=
  [("scc_rt_print", 0, 16), (".Lscc_rt_print.entry", 0, 2), (".Lscc_rt_print.loop", 0, 22),
    (".Lscc_rt_print.write", 0, 44), (".Lscc_rt_print.chk2", 0, 18), (".Lscc_rt_print.chk3", 0, 18),
    (".Lscc_rt_print.adv", 0, 35), (".Lscc_rt_print.fail", 0, 12), (".Lscc_rt_print.done", 0, 5)]

theorem printRuns_chk : runsNeChk helloCells printRuns abPtsA = true := by decide +kernel

/-- `wc_worker`'s return address from `print` (`.x17`), off the write abort's pcs. -/
theorem wcRet_chk :
    !(Spike.Lib.X64.WriteAb.abPcs (labC Spike.Lib.X64.HelloPh.lo helloCells)).contains
      (labC Spike.Lib.X64.HelloPh.lo helloCells ".Lwc_worker.x17") = true := by
  decide +kernel

/-! ## A single cell's node -/

/-- **A single cell's `NodeW` as its `NodeZA`**, the frame condition stable. -/
theorem NodeW.toZA1 {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Z : Frag isa} {K : State → State → Prop} {n : ND} {d : Directive} {z : Nat} (hF : FStable R F)
    (h : NodeW Z K exe endPc R F n) : NodeZA Z exe endPc R F n [(d, z)] :=
  fun s σ c he hn hd _ _ hD hJ k hk m hA' hD' => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨(h { s with st := (m, n.pc + Int64.ofNat (cellOff [(d, z)] 0)) } c
      ⟨he, hn, hd, Spike.Lib.X64.Flow.Worker.cellOff_zero _ _, σ, hA', hF _ _ hD hD', hJ⟩).1, fun _ h => h⟩

/-! ## The instance's facts -/

section Inst

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
include hlab

omit [Kraken.Executable.ValidLayout exe] in
/-- The labels `printPLabs` at the code labels. -/
theorem printPLabs_eq : ∀ x ∈ printPLabs,
    (_root_.Executable.labels exe).label x = labC Spike.Lib.X64.HelloPh.lo helloCells x :=
  Spike.Lib.X64.HelloWf.lab_labC hlab printPLabs_chk

omit [Kraken.Executable.ValidLayout exe] in
/-- **An off-site pc (`okPcH`) is off the exits and the transfer sites.** -/
theorem pcOffA_of_okPcH {q : Int64} (h : okPcH q.toBitVec.toNat = true) :
    PcOffA (_root_.Executable.labels exe).label q := by
  have hl := printPLabs_eq hlab
  simp only [okPcH, abPtsA, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e : ∀ {x : String}, x ∈ printPLabs →
      ¬ q.toBitVec.toNat = (labC Spike.Lib.X64.HelloPh.lo helloCells x).toBitVec.toNat →
      q ≠ (_root_.Executable.labels exe).label x := fun hx hn heq => hn (by rw [heq, hl _ hx])
  exact ⟨e (by decide) h1, e (by decide) h2, e (by decide) h3, e (by decide) h4, e (by decide) h5,
    e (by decide) h6, e (by decide) h7⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The phase check at the executable's labels.** -/
theorem printPhP :
    Spike.Lib.X64.PrintG.printPhOk okPcH (fun _ => 0) (_root_.Executable.labels exe).label = true := by
  have hl := printPLabs_eq hlab
  rw [Spike.Lib.X64.PrintG.printPhOk_congr (lab' := labC Spike.Lib.X64.HelloPh.lo helloCells) fun l hm =>
    hl l (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm)))]
  exact printPhP_chk

/-- **`wc_worker`'s return address from `print`** (`Body.wkC`'s cell `-96`, the `.x17` its `call` pushes) is off
the write abort's pcs. -/
theorem wcRet_abX (hp : Lays exe helloCells kp) {J Kc : AS → Ctl → Prop} {σC : AS} {c : Ctl}
    (hJ : (Body.wCall (_root_.Executable.labels exe).label J Kc).J σC c) :
    Int64.ofBitVec (σC.slot (-96)) ∉ Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label := by
  obtain ⟨⟨σ0, c0, fl, -, rfl⟩, -⟩ := hJ
  have hl := printPLabs_eq hlab
  rw [Body.wkC_ra _ σ0 fl (Wk.hgap hp), Spike.Lib.int64_ofBitVec_toBitVec,
    Spike.Lib.X64.AllocG.abPcs_congr (lab' := labC Spike.Lib.X64.HelloPh.lo helloCells) fun l hm =>
      hl l (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))),
    hl _ (by decide)]
  have h := wcRet_chk
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  simpa using h

variable (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hμ

omit [Kraken.Executable.ValidLayout exe] in
/-- **The instance**: no phase, no owned words, no outside move. -/
theorem instOkP :
    InstOk exe endPc helloCells (_root_.Executable.labels exe).label μ (fun _ => []) (fun _ => False)
      (fun _ _ => False) okPcH (fun _ => 0) kp where
  lays := hp
  endOk := hend
  labOk := rfl
  same := fun _ _ _ => ⟨rfl, Iff.rfl⟩
  off := fun _ h => ⟨pcOff_of hμ (pcOffA_of_okPcH hlab h), fun _ h => h⟩

omit hlab hp hend [Kraken.Executable.ValidLayout exe] in
/-- **`AbX` at a node from `AbSt` there**, its pcs in a run of `runs` off the exits and the transfer sites
(`hoff`, `hm`, `hc`, `he`), with the thread pointer. -/
theorem nodeZA_abX_of {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {n : ND}
    {blk : List (Directive × Nat)} {runs : List (Label × Nat × Nat)} {l : Label} {c hi : Nat} (tp : UInt64)
    (h : NodeZA (fun s _ => Spike.Lib.X64ConsumerA.AbSt μ (Spike.Lib.X64.WriteAb.Ab
      (_root_.Executable.labels exe).label) s) exe endPc R F n blk)
    (hoff : RunsOffA (_root_.Executable.labels exe).label runs) (hm : (l, 0, hi) ∈ runs)
    (hc : ∀ j < blk.length, c + cellOff blk j < hi)
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat c) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F (n.withTp tp) blk :=
  Spike.Lib.LowerX64.BlkW.withTp (NodeZA.mono (NodeZA.and h
    (NodeZ.toA (Z := fun s _ => PcOffA (_root_.Executable.labels exe).label s.st.2)
      fun s _ _ j hj _ hs _ => by
        show PcOffA _ s.st.2; rw [hs]; exact pcOffA_add hoff hm (Nat.zero_le _) (hc j hj) he))
    fun _ _ h => AbX.of_off hμ h.1 h.2) tp

set_option hygiene false in
/-- A node of `print`: `nodeZA_abX_of` at `printRuns`' run of label `l`, from byte `c`. -/
local macro "pnode " h:term:max l:term:max c:term:max hi:term:max : tactic =>
  `(tactic| exact nodeZA_abX_of hμ (l := $l) (c := $c) (hi := $hi) _ $h hoff (by decide) (by decide)
      (by first | rfl | exact (ofNat_zero' _).symm))

set_option maxHeartbeats 1600000 in
/-- **`AbX` at every node of `print` entered at `σC`** (`WcObl.hZP`'s nodes): `PrintG.printAb`'s blocks,
`PrintG.printSvcAb`'s system call, at `instOkP`; the count below `2^63` (`hlen`), the return address in the
caller's cell `ko` off the write abort's pcs (`hra`), in a region of print's frame. -/
theorem print_abX {R : Region} {F : MachineData → Prop} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40)
    (hhi : 16 ≤ R.hi) {Pc Qc : AS → Nat → Ctl → Prop} {ko : Int} {σC : AS} {fs : List TermRun.Frame}
    (hlen : (σC.regs.get64 .rsi).toNat < 2 ^ 63)
    (hra : Int64.ofBitVec (σC.slot ko) ∉ Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label)
    (i : Spike.Lib.X64.Print.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F
      (PrintF.cN (_root_.Executable.labels exe).label Pc Qc ko σC i) (PrintF.FA.blkN i) := by
  have hI := instOkP hlab hp hend hμ
  have hW := Spike.Lib.X64.PrintG.printAb (rbp0 := σC.regs.rbp.toBitVec) (ra := σC.slot ko)
    (buf0 := σC.regs.get64 .rdi) (len0 := (σC.regs.get64 .rsi).toNat) (P := Pc σC) (Q := Qc σC) (R := R) (F := F)
    hI SccCode.hello_print SccCode.hello_abort (printPhP hlab) hR hlo hhi hlen rfl hra
  have hS := Spike.Lib.X64.PrintG.printSvcAb (rbp0 := σC.regs.rbp.toBitVec) (ra := σC.slot ko)
    (buf0 := σC.regs.get64 .rdi) (len0 := (σC.regs.get64 .rsi).toNat) (P := Pc σC) (Q := Qc σC) (R := R) (F := F)
    hI SccCode.hello_print SccCode.hello_abort (printPhP hlab) (by omega) (by omega)
  have hoff := runsOffA_of_chk hp printRuns_chk
  cases i
  case e => pnode hW.e "scc_rt_print" 0 16
  case n1 => pnode hW.n1 ".Lscc_rt_print.entry" 0 2
  case loop => pnode hW.loop ".Lscc_rt_print.loop" 0 22
  case n3 => pnode hW.n3 ".Lscc_rt_print.loop" 20 22
  case write => pnode hW.write ".Lscc_rt_print.write" 0 44
  case sys => pnode (NodeW.toZA1 hF hS) ".Lscc_rt_print.write" 20 44
  case n5 => pnode hW.n5 ".Lscc_rt_print.write" 22 44
  case n6 => pnode hW.n6 ".Lscc_rt_print.write" 42 44
  case chk2 => pnode hW.chk2 ".Lscc_rt_print.chk2" 0 18
  case n8 => pnode hW.n8 ".Lscc_rt_print.chk2" 16 18
  case chk3 => pnode hW.chk3 ".Lscc_rt_print.chk3" 0 18
  case n10 => pnode hW.n10 ".Lscc_rt_print.chk3" 16 18
  case adv => pnode hW.adv ".Lscc_rt_print.adv" 0 35
  case fail => pnode hW.fail ".Lscc_rt_print.fail" 0 12
  case done => pnode hW.done ".Lscc_rt_print.done" 0 5

end Inst

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPLabs_chk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPLabs_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPhP_chk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPhP_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.printRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.printRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRet_chk'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRet_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.NodeW.toZA1'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.NodeW.toZA1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPLabs_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPLabs_eq

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.pcOffA_of_okPcH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.pcOffA_of_okPcH

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPhP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.printPhP

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRet_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRet_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.instOkP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.instOkP

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.nodeZA_abX_of'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.nodeZA_abX_of

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.print_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.print_abX
