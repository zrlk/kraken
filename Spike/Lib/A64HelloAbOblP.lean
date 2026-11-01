/-
**`AbX` at `print`'s nodes** (row 5i-hab1, P4, AArch64;
`A64HelloAbObl`'s recipe): `WcObl.hZP` at `X := AbX μ lab`, from the
generic `PrintG.printAb` (`AbSt` at `print`'s blocks and barrier, the
tests' blocks kept by the stored result) and `PrintG.printSvcAb` (the
system call's refusal), at an instance `instOkP` of `Rt.InstOk` with no
phase (`ph := 0`), no owned words and no outside move, its off-site pcs
those of none of `abPtsA`'s labels (`okPcH`); `AbX`'s abort-site half
from print's pcs off the exits (`printRuns_chk`).

- `okPcH`, `instOkP`: the instance.
- `printPhP_chk`, `printPhP`: the phase check at it (decided at the code
  labels, `PrintG.printPhOkF`).
- `printRuns`, `printRuns_chk`: print's pcs off the exits and the
  transfer sites.
- `NodeW.toZA1`: a single cell's `NodeW` as its `NodeZA` (`FStable`).
- `print_abX`: `AbX` at every node of `print` entered at `σC`, the count
  below `2^63` and the return address off the write abort's pcs.
- `wcRet_abX`: that return address at `wc_worker`'s call.
- `wcPrint_abX`: `WcObl.hZP`'s shape, the count `printN n m` below `2^63`.
-/
import Spike.Lib.A64HelloAbOblW
import Spike.Lib.A64PrintGAb
import Spike.Lib.A64PrintGSvc
import Spike.Lib.A64HelloPrintNN

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND NodeW BlkW At AS)
open Spike.Lib.A64.Flow.Worker (NodeZA NodeZ)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64WakeOff (PcOffA pcOffA_add)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open Spike.Lib.LowerA64 (labC)
open SccCode (helloProg)

/-! ## The instance -/

/-- **The off-site pcs**: none of `abPtsA`'s labels' code addresses. -/
def okPcH (p : Nat) : Bool :=
  abPtsA.all fun q => p != (labC Spike.Lib.A64.HelloPh.lo helloProg q.1).toBitVec.toNat

/-- The labels `printPhOkF` and `abPcs` read, and `abPtsA`'s. -/
def printPLabs : List String :=
  Spike.Lib.A64.StubW.printLabs ++ Spike.Lib.A64.AllocG.abLabs ++ abPtsA.map Prod.fst ++
    [".L20_wc_worker.0_entry"]

theorem printPLabs_chk :
    printPLabs.all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo helloProg x).isSome) = true := by
  decide +kernel

/-- **The phase check at the code labels** with no phase. -/
theorem printPhP_chk :
    Spike.Lib.A64.PrintG.printPhOkF okPcH (fun _ => 0) (labC Spike.Lib.A64.HelloPh.lo helloProg) = true := by
  decide +kernel

/-- **`print`'s pcs**: its blocks from each label (the barrier and the
system call in `.2_write`'s fifteen). -/
def printRuns : List (Label × Nat × Nat) :=
  [("scc_rt_print", 0, 6), (".L9_scc_rt_print.0_entry", 0, 1), (".L9_scc_rt_print.1_loop", 0, 5),
    (".L9_scc_rt_print.2_write", 0, 15), (".L9_scc_rt_print.3_chk2", 0, 8), (".L9_scc_rt_print.4_chk3", 0, 5),
    (".L9_scc_rt_print.5_adv", 0, 9), (".L9_scc_rt_print.6_fail", 0, 2), (".L9_scc_rt_print.7_done", 0, 4)]

theorem printRuns_chk : runsNeChk helloProg printRuns abPtsA = true := by decide +kernel

/-- `wc_worker`'s return address from `print`, off the write abort's pcs. -/
theorem wcRet_chk :
    !(Spike.Lib.A64.WriteAb.abPcs (labC Spike.Lib.A64.HelloPh.lo helloProg)).contains
      (labC Spike.Lib.A64.HelloPh.lo helloProg ".L20_wc_worker.0_entry" + Int64.ofNat (4 * 21)) = true := by
  decide +kernel

/-! ## A single cell's node -/

/-- **A single cell's `NodeW` as its `NodeZA`**, the frame condition stable. -/
theorem NodeW.toZA1 {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {Z : Frag isaLSE2} {K : State → State → Prop} {n : ND} {d : Directive} (hF : FStable R F)
    (h : NodeW Z K exe endPc R F n) : NodeZA Z exe endPc R F n [d] :=
  fun s σ c he hn hd _ _ hD hJ k hk m hA' hD' => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨(h { s with st := (m, n.pc + Int64.ofNat (4 * 0)) } c
      ⟨he, hn, hd, Spike.Lib.A64.Flow.ofNat4_zero _, σ, hA', hF _ _ hD hD', hJ⟩).1, fun _ h => h⟩

/-! ## The instance's facts -/

section Inst

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
include hlab

omit [Kraken.Executable.ValidLayout exe] in
/-- The labels `printPLabs` at the code labels. -/
theorem printPLabs_eq : ∀ x ∈ printPLabs,
    (_root_.Executable.labels exe).label x = labC Spike.Lib.A64.HelloPh.lo helloProg x :=
  Spike.Lib.A64.HelloWf.lab_labCH hlab printPLabs_chk

omit [Kraken.Executable.ValidLayout exe] in
/-- **An off-site pc (`okPcH`) is off the exits and the transfer sites.** -/
theorem pcOffA_of_okPcH {q : Int64} (h : okPcH q.toBitVec.toNat = true) :
    PcOffA (_root_.Executable.labels exe).label q := by
  have hl := printPLabs_eq hlab
  simp only [okPcH, abPtsA, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e : ∀ {x : String}, x ∈ printPLabs → ¬ q.toBitVec.toNat = (labC Spike.Lib.A64.HelloPh.lo helloProg x).toBitVec.toNat →
      q ≠ (_root_.Executable.labels exe).label x := fun hx hn heq => hn (by rw [heq, hl _ hx])
  exact ⟨e (by decide) h1, e (by decide) h2, e (by decide) h3, e (by decide) h4, e (by decide) h5,
    e (by decide) h6, e (by decide) h7⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The phase check at the executable's labels.** -/
theorem printPhP :
    Spike.Lib.A64.PrintG.printPhOkF okPcH (fun _ => 0) (_root_.Executable.labels exe).label = true := by
  have hl := printPLabs_eq hlab
  have h := printPhP_chk
  unfold Spike.Lib.A64.PrintG.printPhOkF at h ⊢
  rw [hl _ (by decide), Spike.Lib.A64.StubW.printPhOk_congr (lab' := Spike.Lib.A64.StubW.fenceLab
    (labC Spike.Lib.A64.HelloPh.lo helloProg)) fun l hm => Spike.Lib.A64.StubW.fenceLab_congr
      (hl l (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm))))]
  exact h

variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hμ

omit [Kraken.Executable.ValidLayout exe] in
/-- **The instance**: no phase, no owned words, no outside move. -/
theorem instOkP :
    InstOk exe endPc helloProg (_root_.Executable.labels exe).label μ (fun _ => []) (fun _ => False)
      (fun _ _ => False) okPcH (fun _ => 0) kp where
  lays := hp
  endOk := hend
  labOk := rfl
  same := fun _ _ _ => ⟨rfl, Iff.rfl⟩
  off := fun _ h => ⟨pcOff_of hμ (pcOffA_of_okPcH hlab h), fun _ h => h⟩

omit hlab hp hend [Kraken.Executable.ValidLayout exe] in
/-- **`AbX` at a node from `AbSt` there**, its pcs in a run of `runs` off
the exits and the transfer sites (`hoff`, `hm`, `hc`, `he`), with the
thread pointer. -/
theorem nodeZA_abX_of {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {n : ND}
    {blk : List Directive} {runs : List (Label × Nat × Nat)} {l : Label} {c hi : Nat} (tp : UInt64)
    (h : NodeZA (fun s _ => Spike.Lib.A64ConsumerA.AbSt μ (Spike.Lib.A64.WriteAb.Ab
      (_root_.Executable.labels exe).label) s) exe endPc R F n blk)
    (hoff : Spike.Lib.A64WakeOff.RunsOffA (_root_.Executable.labels exe).label runs) (hm : (l, 0, hi) ∈ runs)
    (hc : c + blk.length ≤ hi) (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * c)) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F (n.withTp tp) blk :=
  Spike.Lib.LowerA64.BlkW.withTp (NodeZA.mono (NodeZA.and h
    (NodeZ.toA (Z := fun s _ => PcOffA (_root_.Executable.labels exe).label s.st.2)
      fun s _ _ j hj _ hs _ => by
        show PcOffA _ s.st.2; rw [hs]; exact pcOffA_add hoff hm (Nat.zero_le _) (by omega) he))
    fun _ _ h => AbX.of_off hμ h.1 h.2) tp

set_option hygiene false in
/-- A node of `print`: `nodeZA_abX_of` at `printRuns`' run of label `l`,
from `c`. -/
local macro "pnode " h:term:max l:term:max c:term:max hi:term:max : tactic =>
  `(tactic| exact nodeZA_abX_of hμ (l := $l) (c := $c) (hi := $hi) _ $h hoff (by decide) (by decide)
      (by (try dsimp only [PrintF.cN, ND.withTp, PrintF.FA.N, Spike.Lib.A64.PrintA.N, PrintF.pcSvc,
            Spike.Lib.A64.PrintA.pcSvc])
          first | (simp only [Int64.add_assoc]; rfl) | exact (Spike.Lib.A64.Flow.ofNat4_zero _).symm | rfl))

set_option maxHeartbeats 1600000 in
/-- **`AbX` at every node of `print` entered at `σC`** (`WcObl.hZP`'s
nodes): `PrintG.printAb`'s blocks and barrier, `PrintG.printSvcAb`'s system
call, at `instOkP`; the count below `2^63` (`hlen`), the return address off
the write abort's pcs (`hra`), in a region of print's frame. -/
theorem print_abX {R : Region} {F : MachineData → Prop} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {Pc Qc : AS → Nat → Ctl → Prop} {σC : AS}
    {fs : List TermRun.Frame} (hlen : σC.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hra : Int64.ofBitVec σC.regs.X30.toBitVec ∉ Spike.Lib.A64.WriteAb.abPcs (_root_.Executable.labels exe).label)
    (i : PrintF.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F
      (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i) (PrintF.FA.blkN i) := by
  have hI := instOkP hlab hp hend hμ
  have hW := Spike.Lib.A64.PrintG.printAb (x29 := σC.regs.X29.toBitVec) (ra := σC.regs.X30.toBitVec)
    (buf0 := σC.regs.X0.toBitVec) (len0 := σC.regs.X1.toBitVec.toNat) (P := Pc σC) (Q := Qc σC) (R := R) (F := F)
    hI SccCode.hello_print SccCode.hello_abort (printPhP hlab) hR hal hlo hhi hlen rfl hra
  have hS := Spike.Lib.A64.PrintG.printSvcAb (x29 := σC.regs.X29.toBitVec) (ra := σC.regs.X30.toBitVec)
    (buf0 := σC.regs.X0.toBitVec) (len0 := σC.regs.X1.toBitVec.toNat) (P := Pc σC) (Q := Qc σC) (R := R) (F := F)
    hI SccCode.hello_print SccCode.hello_abort (printPhP hlab) hlo hhi
  have hoff := runsOffA_of_chk hp printRuns_chk
  cases i
  case e => pnode hW.e "scc_rt_print" 0 6
  case n1 => pnode hW.n1 ".L9_scc_rt_print.0_entry" 0 1
  case loop => pnode hW.loop ".L9_scc_rt_print.1_loop" 0 5
  case n3 => pnode hW.n3 ".L9_scc_rt_print.1_loop" 4 5
  case fence =>
    have e : PrintF.FA.blkN .fence = [.instr ⟨.W64, .DMB .sy⟩] := Spike.Lib.A64.PrintG.bF_eq
    rw [e]
    pnode (NodeW.toZA1 hF hW.fence) ".L9_scc_rt_print.2_write" 0 15
  case write => pnode hW.write ".L9_scc_rt_print.2_write" 1 15
  case svc => pnode (NodeW.toZA1 hF hS) ".L9_scc_rt_print.2_write" 5 15
  case n5 => pnode hW.n5 ".L9_scc_rt_print.2_write" 6 15
  case n6 => pnode hW.n6 ".L9_scc_rt_print.2_write" 13 15
  case n7 => pnode hW.n7 ".L9_scc_rt_print.2_write" 14 15
  case chk2 => pnode hW.chk2 ".L9_scc_rt_print.3_chk2" 0 8
  case n9 => pnode hW.n9 ".L9_scc_rt_print.3_chk2" 6 8
  case n10 => pnode hW.n10 ".L9_scc_rt_print.3_chk2" 7 8
  case chk3 => pnode hW.chk3 ".L9_scc_rt_print.4_chk3" 0 5
  case n12 => pnode hW.n12 ".L9_scc_rt_print.4_chk3" 4 5
  case adv => pnode hW.adv ".L9_scc_rt_print.5_adv" 0 9
  case fail => pnode hW.fail ".L9_scc_rt_print.6_fail" 0 2
  case done => pnode hW.done ".L9_scc_rt_print.7_done" 0 4

omit hp hend hμ [Kraken.Executable.ValidLayout exe] in
/-- **`wc_worker`'s return address from `print`** (`Body.wkE`'s call, 21
instructions past `.0_entry`) is off the write abort's pcs. -/
theorem wcRet_abX {J : AS → Ctl → Prop} {Kc : AS → Ctl → Prop} {σC : AS} {c : Ctl}
    (hJ : (Body.wCall (_root_.Executable.labels exe).label J Kc).J σC c) :
    Int64.ofBitVec σC.regs.X30.toBitVec ∉ Spike.Lib.A64.WriteAb.abPcs (_root_.Executable.labels exe).label := by
  obtain ⟨⟨σ0, c0, -, rfl⟩, -⟩ := hJ
  have hl := printPLabs_eq hlab
  rw [Body.wkC_eq, Body.wkE_X30, Spike.Lib.int64_ofBitVec_toBitVec,
    Spike.Lib.A64.AllocG.abPcs_congr (lab' := labC Spike.Lib.A64.HelloPh.lo helloProg) fun l hm =>
      hl l (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hm))),
    hl _ (by decide)]
  have h := wcRet_chk
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  simpa using h

/-- **`WcObl.hZP` at `AbX`**: every node of `print` called from
`wc_worker`'s call node, the call's control giving a count below `2^63`
(`hK`). -/
theorem wcPrint_abX {J Kc : AS → Ctl → Prop} {Pc Qc : AS → Nat → Ctl → Prop} {fr : TermRun.Frame}
    (hK : ∀ σ c, Kc σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63) {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hF : FStable R F)
    {σC : AS} {c : Ctl} (hJ : (Body.wCall (_root_.Executable.labels exe).label J Kc).J σC c) (i : PrintF.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c [fr]) exe endPc R F
      (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i) (PrintF.FA.blkN i) :=
  print_abX hlab hp hend hμ hF hR hal hlo hhi (hK σC c hJ.2) (wcRet_abX hlab hJ) i

end Inst

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.instOkP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.instOkP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.print_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.print_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcPrint_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcPrint_abX
