/-
**`AbX` at the thread worker's nodes** (row 5i-hab1, P2,
AArch64; `A64HelloAbObl`'s recipe): `ZObl.hzT`, `hZEt`, `hZT` at
`X := AbX μ lab`, the twins of `Wk.thrPro_relH`, `thrHead_relH`,
`thrTail_relH` (`A64HelloRelZ`), with `blkW_abX`/`nodeW_abX` for their
covered blocks and the limit's load, and two single-cell node lemmas for
the atomic and `svc` cells (`nodeW_abX` takes neither).

- `nodeZA_cellP`: `nodeZA_cell` with the cell's pc.
- `ldr_leaf`, `stlr_leaf`, `swp_leaf`: the load's, the release store's,
  the swap's every leaf 4 bytes on (the private and the shared memory).
- `nodeZA_abX_cell`: `AbX` at a single cell other than an `svc` whose
  leaves are 4 bytes on (`stlr`, `swpal`).
- `nodeZA_abX_svc`: `AbX` at an `svc #0` (`WakeWf.nodeW_abSt_svc`'s
  argument: no instruction tree; the resumed states 4 bytes on).
- `proW_abX`: `AbX` at a stack-checked prologue of helloProg (`ProW`;
  `RelZ.proW_relZ`'s code facts).
- `thrPro_abX`, `thrHead_abX`, `thrTail_abX`: P2's fields.
-/
import Spike.Lib.A64HelloAbOblC

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt svcRet after exec_ldr exec_ldr_mapped exec_stlr exec_stlr_mapped exec_swp
  exec_swp_mapped)
open Spike.Lib.A64 (CodeAt)
open Scc.Sem (Marks TreeLeaf)
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND NodeW BlkW At svcDir ofNat4_succ ofNat4_zero code_of okBlk prologueIn chkHead chkBr
  frameSet chkHead_ok chkBr_ok frameSet_ok ProW proN1 proN2 proN3 ldrDir)
open Spike.Lib.A64.Flow.Worker (NodeZA)
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.A64WakeOff (RunsOffA PcOffA pcOffA_add)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloProg)

/-! ## The single cells -/

section Cells

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `nodeZA_cell` with the cell's pc. -/
theorem nodeZA_cellP {Z : Frag isaLSE2} {n : ND} {d : Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (h : ∀ s c, CellAt s d 4 → s.decls = {} → s.st.2 = n.pc → Z s c) : NodeZA Z exe endPc R F n [d] :=
  fun s σ c he hn hd _ _ _ _ k hk m _ _ => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨h _ c ((hcode { s with st := (m, n.pc + Int64.ofNat (4 * 0)) } he hn).cell (j := 0) rfl rfl rfl
      (by simp)) hd (ofNat4_zero _), fun _ h => h⟩

/-- **A load's leaves are 4 bytes on.** -/
theorem ldr_leaf {s : State} {t b : XReg} {i : Int64} (hc : CellAt s (ldrDir t b i) 4) (hd : s.decls = {}) :
    ∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  cases h : Mem.loadInt s.st.1.dmem (BitVec.ofInt 64 ((s.st.1.regs.getXReg b).toBitVec.toInt + i.toInt)) 8 with
  | none =>
    refine ⟨_, exec_ldr hc rfl h, fun s' hs' => ?_⟩
    rw [hd, EvTree.access_empty] at hs'
    obtain ⟨_, rfl⟩ := hs'
    rfl
  | some j =>
    refine ⟨_, exec_ldr_mapped hc rfl h, fun s' hs' => ?_⟩
    cases hs'
    rfl

/-- **A release store's leaves are 4 bytes on.** -/
theorem stlr_leaf {s : State} {src : RegOrZr .W64} {n : XReg}
    (hc : CellAt s (.instr ⟨.W64, .STLR .W64 src (.low (.reg n) .W64)⟩) 4) (hd : s.decls = {}) :
    ∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  cases h : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg n).toBitVec 8 with
  | none =>
    refine ⟨_, exec_stlr hc h, fun s' hs' => ?_⟩
    rw [hd, EvTree.access_empty] at hs'
    obtain ⟨_, rfl⟩ := hs'
    rfl
  | some j =>
    refine ⟨_, exec_stlr_mapped hc h, fun s' hs' => ?_⟩
    cases hs'
    rfl

/-- **A swap's leaves are 4 bytes on.** -/
theorem swp_leaf {s : State} {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt s (.instr ⟨.W64, .SWP k .W64 rs rt (.low (.reg n) .W64)⟩) 4) (hd : s.decls = {}) :
    ∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4 := by
  cases h : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg n).toBitVec 8 with
  | none =>
    refine ⟨_, exec_swp hc h, fun s' hs' => ?_⟩
    rw [hd, EvTree.access_empty] at hs'
    obtain ⟨_, _, rfl⟩ := hs'
    rfl
  | some j =>
    obtain ⟨_, hx⟩ := exec_swp_mapped hc h
    refine ⟨_, hx, fun s' hs' => ?_⟩
    cases hs'
    rfl

variable {μ : Marks}

/-- **`AbX` at a single cell other than an `svc`** whose leaves are 4 bytes
on (`hstep`), its next pc off the write abort's pcs (`h`), its pc off the
exits and the transfer sites by label (`hoff`). -/
theorem nodeZA_abX_cell (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {d : Directive} {l : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : abSiH (_root_.Executable.labels exe).label l k = true)
    (hsvc : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hstep : ∀ s : State, CellAt s d 4 → s.decls = {} →
      ∃ tree, isaLSE2.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n [d] := by
  refine nodeZA_cellP hcode fun s c hc hd hpc => ?_
  obtain ⟨tree, hex, hl⟩ := hstep s hc hd
  simp only [abSiH, he, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hq : PcOffA (_root_.Executable.labels exe).label s.st.2 := hpc ▸ hoff
  refine AbX.of_off hμ (AbSt.ofLeaves (pcOff_of hμ hq).noTake (Scc.Sem.A64.atSvc_false_of_cellAt hc hsvc)
    fun t ht => ?_) hq
  rw [hex] at ht
  cases ht
  exact Spike.Lib.A64Consumer.allInv_of_leaf tree fun s' hs' =>
    Spike.Lib.A64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h)

/-- **`AbX` at an `svc #0`**: no instruction tree (`abInstr` vacuous), the
resumed states 4 bytes on, off the write abort's pcs (`h`); its pc off the
exits and the transfer sites by label (`hoff`). -/
theorem nodeZA_abX_svc (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {l : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (h : abSiH (_root_.Executable.labels exe).label l k = true) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n [svcDir] := by
  refine nodeZA_cellP hcode fun s c hc _ hpc => ?_
  simp only [abSiH, he, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hq : PcOffA (_root_.Executable.labels exe).label s.st.2 := hpc ▸ hoff
  refine AbX.of_off hμ ⟨fun _ h' => ?_, fun _ _ call hdc s' hs' hab => ?_,
    fun _ a ha hpc' => ((pcOff_of hμ hq).noTake a ha hpc').elim⟩ hq
  · rw [show abi.atSys s = true from Scc.Sem.A64.atSvc_of_cellAt hc] at h'; cases h'
  · obtain ⟨r, -, rfl⟩ := (Scc.Sem.A64.mem_certSuccs_svc hc hdc).mp hs'
    exact (Spike.Lib.A64.WriteAb.not_ab_of_pc (show s.st.2 + Int64.ofNat 4 ∉ _ by rw [hpc]; exact h) hab).elim

end Cells

/-! ## The prologue -/

section Pro

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **`AbX` at a stack-checked prologue of helloProg** (`ProW`): its three
blocks by `blkW_abX`, the limit's load by `nodeW_abX`, their targets off
the write abort's pcs decided (`c0`–`c3`), the frame's set-up `ret`-free (`hnr`), the pcs from the stack check's
label on (`hrun`). -/
theorem proW_abX (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x)
    (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {fn sc entry : Label} {Z lim : Int64} {L : Label}
    {ps : List (XReg × Int64)} (hin : prologueIn helloProg fn sc entry Z lim L ps = true) {J : AS → Ctl → Prop}
    (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, Spike.Lib.offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hrun : runsNeChk helloProg [(sc, 0, 9 + ps.length)] abPtsA = true)
    (c0 : abOffHC sc 0 sc (chkHead Z) = true) (c1 : abSiHC sc 2 = true) (c2 : abOffHC sc 3 sc (chkBr L) = true)
    (c3 : abOffHC sc 5 sc (frameSet Z ps) = true) (hnr : Spike.Lib.A64Consumer.noRetBlk (frameSet Z ps) = true) :
    ProW (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z lim L ps J := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have hoff := runsOffA_of_chk hp hrun
  have hfl : (frameSet Z ps).length = 4 + ps.length := by
    simp [frameSet, Spike.Lib.A64.Flow.frSetup]; omega
  have he0 : (_root_.Executable.labels exe).label sc + Int64.ofNat (4 * 0) =
      (⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩ : ND).pc := by rw [e0, ofNat4_zero]
  have he1 : (_root_.Executable.labels exe).label sc + Int64.ofNat (4 * 2) =
      (proN1 ((_root_.Executable.labels exe).label fn) Z J).pc := by
    rw [e0]; simp only [proN1, ofNat4_succ, ofNat4_zero]
  have he2 : (_root_.Executable.labels exe).label sc + Int64.ofNat (4 * 3) =
      (proN2 ms ((_root_.Executable.labels exe).label fn) Z lim J).pc := by
    rw [e0]; simp only [proN2, ofNat4_succ, ofNat4_zero]
  have he3 : (_root_.Executable.labels exe).label sc + Int64.ofNat (4 * 5) =
      (proN3 ms ((_root_.Executable.labels exe).label fn) Z lim J).pc := by
    rw [e0]; simp only [proN3, ofNat4_succ, ofNat4_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact blkW_abX hμ (code_of hp hend b0 he0) (chkHead_ok (-Z.toInt) 0 Z) hR hal hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.head _) (Nat.le_refl 0)
        (by simp only [chkHead, List.length_cons, List.length_nil] at hj; omega) he0.symm)
      he0 (abOffHC_sound hlab c0)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false rfl j hj r hr).elim)
  · have hq := pcOffA_add (k := 0) hoff (List.Mem.head _) (Nat.zero_le 2) (by omega) he1.symm
    rw [ofNat4_zero] at hq
    refine nodeW_abX hμ hq he1 (abSiHC_sound hlab c1) fun s c hA => ?_
    obtain ⟨hs, hn, hd, hpc, -⟩ := id hA
    have hc : CellAt s (ldrDir .X10 .X10 lim) 4 :=
      (code_of hp hend b1 he1 s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    obtain ⟨tree, hex, hl⟩ := ldr_leaf hc hd
    exact ⟨_, tree, hc, nofun, hex, hl⟩
  · exact blkW_abX hμ (code_of hp hend b2 he2) (chkBr_ok (-Z.toInt) 0 Z L) hR hal hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.head _) (Nat.zero_le 3)
        (by simp only [chkBr, List.length_cons, List.length_nil] at hj; omega) he2.symm)
      he2 (abOffHC_sound hlab c2)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false rfl j hj r hr).elim)
  · exact blkW_abX hμ (code_of hp hend b3 he3) (frameSet_ok h16 hZ (by omega) (Int.le_refl 0) hps) hR hal hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.head _) (Nat.zero_le 5) (by rw [hfl] at hj; omega) he3.symm)
      he3 (abOffHC_sound hlab c3) (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false hnr j hj r hr).elim)

end Pro

/-! ## P2: the thread worker -/

section P2

/-- **The thread worker's pcs**: its tail from `.sp0` (nine instructions)
and its `.0_entry` block (seven). -/
def thrRuns : List (Label × Nat × Nat) :=
  [(HThrTail.pfx0 ++ ".sp0", 0, 9), (HThrTail.pfx0 ++ ".0_entry", 0, 7)]

theorem thrRuns_chk : runsNeChk helloProg thrRuns abPtsA = true := by decide +kernel

/-- The thread worker's prologue's pcs, from its stack check. -/
theorem thrProRuns_chk :
    runsNeChk helloProg [(HThrTail.pfx0 ++ ".stack_check", 0, 9 + thrPs.length)] abPtsA = true := by
  decide +kernel

/-! The thread worker's blocks' and cells' targets off the write abort's
pcs (decided at helloProg's code labels). -/

theorem thC_b0 : abOffHC (HThrTail.pfx0 ++ ".sp0") 0 (HThrTail.pfx0 ++ ".sp0") HThrTail.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thC_ex : abSiHC (HThrTail.pfx0 ++ ".sp0") 5 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thC_b1 : abOffHC (HThrTail.pfx0 ++ ".sp0") 6 (HThrTail.pfx0 ++ ".sp0") HThrTail.b1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thC_svc : abSiHC (HThrTail.pfx0 ++ ".sp0") 8 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thC_thE : abOffHC (HThrTail.pfx0 ++ ".0_entry") 0 (HThrTail.pfx0 ++ ".0_entry") HThrHead.thE = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thP_c0 : abOffHC (HThrTail.pfx0 ++ ".stack_check") 0 (HThrTail.pfx0 ++ ".stack_check") (chkHead 80) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thP_c1 : abSiHC (HThrTail.pfx0 ++ ".stack_check") 2 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thP_c2 : abOffHC (HThrTail.pfx0 ++ ".stack_check") 3 (HThrTail.pfx0 ++ ".stack_check")
    (chkBr (HThrTail.pfx0 ++ ".stack_grow")) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem thP_c3 : abOffHC (HThrTail.pfx0 ++ ".stack_check") 5 (HThrTail.pfx0 ++ ".stack_check")
    (frameSet 80 thrPs) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `scc_rt_thr_worker`'s prologue** (`ZObl.hzT`). -/
theorem thrPro_abX {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    ProW (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8 (HThrTail.pfx0 ++ ".stack_grow") thrPs J :=
  proW_abX hp hend hlab hμ hello_thrPro (by decide) (by decide) hR hal hlo hhi (by decide) thrProRuns_chk
    thP_c0 thP_c1 thP_c2 thP_c3 (by decide)

/-- **`AbX` at `scc_rt_thr_worker`'s head** (`ZObl.hZEt`). -/
theorem thrHead_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : HThrHead.TN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label J L i) (HThrHead.blkN i) := by
  have hoff := runsOffA_of_chk hp thrRuns_chk
  cases i
  · have he : (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".0_entry") + Int64.ofNat (4 * 0) =
        (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label J L .e).pc := ofNat4_zero _
    have hlen : HThrHead.thE.length = 7 := rfl
    exact blkW_abX (rl := HThrTail.pfx0 ++ ".0_entry") hμ (thECode hp hend) HThrHead.thE_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.tail _ (List.Mem.head _)) (Nat.le_refl 0)
        (by simp only [HThrHead.blkN, hlen] at hj; omega) he.symm)
      he (abOffHC_sound hlab thC_thE)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)
  · exact Spike.Lib.A64.Flow.Worker.Wake.RelZW.nodeZA_nil

/-- **`AbX` at `scc_rt_thr_worker`'s tail** (`ZObl.hZT`): its two blocks,
the `stlr` of the thread's `exited` word (`nodeZA_abX_cell`), the `exit`'s
`svc` (`nodeZA_abX_svc`). -/
theorem thrTail_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {c3 : Ctl} {tp : BitVec 64} (i : HThrTail.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp i) (HThrTail.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp)
  have hoff := runsOffA_of_chk hp thrRuns_chk
  have hm : (HThrTail.pfx0 ++ ".sp0", 0, 9) ∈ thrRuns := List.Mem.head _
  cases i
  · have he : (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") + Int64.ofNat (4 * 0) =
        (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp .sp0).pc := ofNat4_zero _
    have hlen : HThrTail.b0.length = 5 := rfl
    exact blkW_abX (rl := HThrTail.pfx0 ++ ".sp0") hμ hc.sp0 HThrTail.b0_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff hm (Nat.le_refl 0) (by simp only [HThrTail.blkN, hlen] at hj; omega) he.symm)
      he (abOffHC_sound hlab thC_b0)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)
  · have he : (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") + Int64.ofNat (4 * 5) =
        (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp .ex).pc := by
      simp only [HThrTail.N, ofNat4_succ, ofNat4_zero]
    have hq := pcOffA_add (k := 0) hoff hm (Nat.zero_le 5) (by omega) he.symm
    rw [ofNat4_zero] at hq
    exact nodeZA_abX_cell hμ hc.ex hq he (abSiHC_sound hlab thC_ex) (fun _ h => by cases h)
      fun _ hc hd => stlr_leaf hc hd
  · have he : (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") + Int64.ofNat (4 * 6) =
        (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp .n2).pc := by
      simp only [HThrTail.N, ofNat4_succ, ofNat4_zero]
    have hlen : HThrTail.b1.length = 2 := rfl
    exact blkW_abX (rl := HThrTail.pfx0 ++ ".sp0") hμ hc.n2 HThrTail.b1_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff hm (Nat.zero_le 6) (by simp only [HThrTail.blkN, hlen] at hj; omega) he.symm)
      he (abOffHC_sound hlab thC_b1)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)
  · have he : (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") + Int64.ofNat (4 * 8) =
        (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp .svc).pc := by
      simp only [HThrTail.N, ofNat4_succ, ofNat4_zero]
    have hq := pcOffA_add (k := 0) hoff hm (Nat.zero_le 8) (by omega) he.symm
    rw [ofNat4_zero] at hq
    exact nodeZA_abX_svc hμ hc.svc hq he (abSiHC_sound hlab thC_svc)

end P2

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.thrPro_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.thrPro_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.thrHead_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.thrHead_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.thrTail_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.thrTail_abX
