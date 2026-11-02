/-
**`AbX` at the thread worker's nodes** (x86-64; the twin of `Spike/Lib/A64HelloAbOblT.lean`, `X64HelloAbObl`'s
recipe): `ZObl.hzT`, `hZEt`, `hZT` (`X64HelloWorkerSegRP`) at `X := AbX μ lab`, the twins of
`RelZH.thrPro_relH`, `thrHead_relH`, `thrTail_relH` (`X64HelloRelZ`), with `blkW_abX`/`nodeW_abX` for their
covered blocks and the limit's load, and single-cell node lemmas for the load from `%fs`, the store and the
`syscall` cells.

- `cellZA_abXD`: `cellZA_abX` with the empty declarations at the cell (the memory accesses' trees).
- `movfs_leaf`, `st_leaf`: the load from `%fs`'s, the store's every leaf `z` bytes on.
- `nodeZA_abX_sys`: `AbX` at a `syscall` (no instruction tree; the resumed states 2 bytes on, also at an
  `arch_prctl`).
- `xProW_abX`: `AbX` at a stack-checked prologue of helloCells (`XProW`; `xProW_relW`'s code facts).
- `thrPro_abX`, `thrHead_abX`, `thrTail_abX`: the thread worker's fields.

Unlike AArch64 (a `ProW` from the stack check's label, 4-byte cells, an `stlr` and an `svc`), the prologue is an
`XProW` of five obligations from the function's label (the `pushq`/`movq` head before the stack check's label,
the `leaq`, the `%fs` load of the limit, the check, the frame), every cell is sized, the tail has five nodes (the
thread pointer's load from `%fs:0`, the `exited` word's plain `movq` store, the `syscall`), the region needs no
alignment, and the single cells' checks are `HelloWf.siAbH` at hello's code labels.

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants): none; the
AArch64 `nodeZA_cellP`, `ldr_leaf`, `stlr_leaf`, `swp_leaf`, `nodeZA_abX_cell` and `nodeZA_abX_svc` have no
x86-64 counterpart of their shape (`cellZA_abX`/`cellZA_abXD`, `movfs_leaf`, `st_leaf`, `nodeZA_abX_sys`).
-/
import Spike.Lib.X64HelloAbOblC

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt eaddr fsAddr exec_store_agrees exec_store_mapped exec_movfs_load
  exec_movfs_load_mapped)
open Scc.Sem (Marks TreeLeaf)
open Scc.Sem.X64 (abi)
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)
open Spike.Lib (Region offOk)
open Kraken.Promising.Lower.X64 (op64)
open Spike.Lib.X64 (ND NodeW CodeAt cellOff At okBlk mB agrees_of_decls fsDir stDir)
open Spike.Lib.X64.Flow (XProW xHead xLea xCmp xFr xProN1 xProN2 xProN3 xProN4 xHead_ok xLea_ok xCmp_ok xFr_ok
  prologueIn szSum ofNat_zero' ofNat_add')
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64WakeOff (RunsOffA PcOffA pcOffA_add pcOffA_at)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloCells)

/-! ## The single cells -/

section Cells

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A load from `%fs`'s leaves are `z` bytes on.** -/
theorem movfs_leaf {s : State} {z : Nat} {r : Reg64} {k : Int64} (hc : CellAt s (fsDir r k) z)
    (hd : s.decls = {}) :
    ∃ tree, isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  cases hm : Mem.loadInt s.st.1.dmem (fsAddr s z { base := none, idx := none, disp := .int64 k }) 8 with
  | none =>
    refine ⟨_, exec_movfs_load hc rfl hm, fun s' hs' => ?_⟩
    rw [hd, EvTree.access_empty] at hs'
    obtain ⟨_, rfl⟩ := hs'
    rfl
  | some j =>
    refine ⟨_, exec_movfs_load_mapped hc rfl hm, fun s' hs' => ?_⟩
    cases hs'
    rfl

/-- **A store's leaves are `z` bytes on.** -/
theorem st_leaf {s : State} {z : Nat} {b r : Reg64} {k : Int64} (hc : CellAt s (stDir b k r) z)
    (hd : s.decls = {}) :
    ∃ tree, isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s z (mB b k)) 8 with
  | none =>
    refine ⟨_, exec_store_agrees hc rfl hm (agrees_of_decls hd _ _), fun s' hs' => ?_⟩
    obtain ⟨_, rfl⟩ := hs'
    rfl
  | some j =>
    refine ⟨_, exec_store_mapped hc rfl hm, fun s' hs' => ?_⟩
    cases hs'
    rfl

variable {μ : Marks}

/-- **`AbX` at a single-cell node with the empty declarations**: `cellZA_abX`, the cell's leaves (`hstep`) from
the empty declarations (a memory access). -/
theorem cellZA_abXD (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame} {n : ND}
    {d : Directive} {z : Nat} {l : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (h : (_root_.Executable.labels exe).label l + Int64.ofNat k + Int64.ofNat z ∉
      Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label)
    (hsys : ∀ w w', d ≠ .instr (.regular w w' .syscall))
    (hstep : ∀ s : State, CellAt s d z → s.decls = {} →
      ∃ tree, isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n [(d, z)] := by
  intro s σ c he' hn hd _ _ _ _ j hj m _ _
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  refine ⟨?_, fun _ h => h⟩
  have hp0 : n.pc + Int64.ofNat (cellOff [(d, z)] 0) = n.pc := Spike.Lib.X64.Flow.Worker.cellOff_zero _ _
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff [(d, z)] 0)) } d z :=
    (hcode s he' hn).cell0 rfl rfl hp0
  obtain ⟨tree, hex, hl⟩ := hstep _ hc hd
  rw [he] at h
  have hq : PcOffA (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (cellOff [(d, z)] 0)) := by
    rw [hp0]; exact hoff
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.X64.WriteAb.not_ab_of_pc (by rw [hl s' hs']; simp only; rw [hp0]; exact h)
  refine AbX.of_off hμ (Spike.Lib.X64ConsumerA.AbSt.ofLeaves (pcOff_of hμ hq).noTake
    (Scc.Sem.X64.atSyscall_false_of_cellAt hc hsys) fun t ht => ?_) hq
  rw [hex] at ht; cases ht; exact Spike.Lib.X64Consumer.allInv_of_leaf tree hnab

/-- **`AbX` at a `syscall`**: no instruction tree (`abInstr` vacuous), every resumed state (also at an
`arch_prctl`) 2 bytes on, off the write abort's pcs (`h`); its pc off the exits and the transfer sites by label
(`hoff`). -/
theorem nodeZA_abX_sys (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame}
    {n : ND} {l : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(op64 .syscall, 2)])
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (h : (_root_.Executable.labels exe).label l + Int64.ofNat k + Int64.ofNat 2 ∉
      Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n
      [(op64 .syscall, 2)] := by
  intro s σ c he' hn _ _ _ _ _ j hj m _ _
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  refine ⟨?_, fun _ h => h⟩
  have hp0 : n.pc + Int64.ofNat (cellOff [(op64 .syscall, 2)] 0) = n.pc :=
    Spike.Lib.X64.Flow.Worker.cellOff_zero _ _
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff [(op64 .syscall, 2)] 0)) } (op64 .syscall) 2 :=
    (hcode s he' hn).cell0 rfl rfl hp0
  rw [he] at h
  have hq : PcOffA (_root_.Executable.labels exe).label
      (n.pc + Int64.ofNat (cellOff [(op64 .syscall, 2)] 0)) := by
    rw [hp0]; exact hoff
  have hnx : ∀ call s', s' ∈ Scc.Sem.Kernel.certSuccs abi
      { s with st := (m, n.pc + Int64.ofNat (cellOff [(op64 .syscall, 2)] 0)) } call →
      s'.st.2 = n.pc + Int64.ofNat 2 := by
    intro call s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [Scc.Sem.X64.certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | tail _ h => cases h
      | head => show _ + Int64.ofNat 2 = _; rw [hp0]; rfl
    · obtain ⟨r, -, rfl⟩ := (Scc.Sem.X64.mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      show _ + Int64.ofNat 2 = _
      rw [hp0]
  refine AbX.of_off hμ ⟨fun _ h' => ?_, fun _ _ call _ s' hs' hab => ?_,
    fun _ a ha hpc' => ((pcOff_of hμ hq).noTake a ha hpc').elim⟩ hq
  · rw [show abi.atSys _ = true from Scc.Sem.X64.atSyscall_of_cellAt hc] at h'; cases h'
  · exact (Spike.Lib.X64.WriteAb.not_ab_of_pc (hnx call s' hs' ▸ h) hab).elim

end Cells

/-! ## The prologue -/

section Pro

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- The head's pcs within its run. -/
theorem xHead_off : ∀ j < xHead.length, 0 + cellOff xHead j < 4 := by decide

/-- **`AbX` at a stack-checked prologue of helloCells** (`XProW`): its four blocks by `blkW_abX`, the limit's
load by `nodeW_abX` (`movfs_leaf`), their targets off the write abort's pcs decided (`c0`–`c4`), the frame's
set-up `ret`-free (`hnr`), the pcs from the function's label and the stack check's label on (`hrun`, the blocks'
pcs within the check's run `o1`–`o4`). -/
theorem xProW_abX (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x)
    (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {fn sc entry : Label} {Z lim : Int64} {L : Label}
    {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn helloCells fn sc entry Z lim L zl zf z1 z2 zs ps = true) {J : AS → Ctl → Prop}
    (hZ : 0 ≤ Z.toInt) (hR : R.OK) (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hrun : runsNeChk helloCells [(fn, 0, 4), (sc, 0, zl + zf + z1 + z2 + zs + szSum ps)] abPtsA = true)
    (o1 : ∀ j < (xLea Z zl).length, 0 + cellOff (xLea Z zl) j < zl + zf + z1 + z2 + zs + szSum ps)
    (o2 : zl + 0 < zl + zf + z1 + z2 + zs + szSum ps)
    (o3 : ∀ j < (xCmp L z1 z2).length, zl + zf + cellOff (xCmp L z1 z2) j < zl + zf + z1 + z2 + zs + szSum ps)
    (o4 : ∀ j < (xFr Z zs ps).length,
      zl + zf + z1 + z2 + cellOff (xFr Z zs ps) j < zl + zf + z1 + z2 + zs + szSum ps)
    (c0 : abOffHC fn 0 fn xHead = true) (c1 : abOffHC sc 0 sc (xLea Z zl) = true)
    (c2 : Spike.Lib.X64.HelloWf.siAbH sc zl zf = true) (c3 : abOffHC sc (zl + zf) sc (xCmp L z1 z2) = true)
    (c4 : abOffHC sc (zl + zf + z1 + z2) sc (xFr Z zs ps) = true)
    (hnl : Spike.Lib.X64Consumer.noRetBlk (xLea Z zl) = true)
    (hnc : Spike.Lib.X64Consumer.noRetBlk (xCmp L z1 z2) = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk (xFr Z zs ps) = true) :
    XProW (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z lim L zl zf z1 z2 zs ps J := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label fn + 1 + 3 = (_root_.Executable.labels exe).label sc := by
    rw [e0, Int64.add_assoc]; rfl
  have hoff := runsOffA_of_chk hp hrun
  have hmf : (fn, 0, 4) ∈ [(fn, 0, 4), (sc, 0, zl + zf + z1 + z2 + zs + szSum ps)] := List.Mem.head _
  have hms : (sc, 0, zl + zf + z1 + z2 + zs + szSum ps) ∈
      [(fn, 0, 4), (sc, 0, zl + zf + z1 + z2 + zs + szSum ps)] := List.Mem.tail _ (List.Mem.head _)
  have he0 : (_root_.Executable.labels exe).label fn + Int64.ofNat 0 = (_root_.Executable.labels exe).label fn :=
    ofNat_zero' _
  have he1 : (_root_.Executable.labels exe).label sc + Int64.ofNat 0 =
      (xProN1 ((_root_.Executable.labels exe).label fn) J).pc := by
    show _ = _ + 1 + 3; rw [h4, ofNat_zero']
  have he2 : (_root_.Executable.labels exe).label sc + Int64.ofNat zl =
      (xProN2 ((_root_.Executable.labels exe).label fn) zl Z J).pc := by
    show _ = _ + 1 + 3 + _; rw [h4]
  have he3 : (_root_.Executable.labels exe).label sc + Int64.ofNat (zl + zf) =
      (xProN3 ms ((_root_.Executable.labels exe).label fn) zl zf Z lim J).pc := by
    show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add']
  have he4 : (_root_.Executable.labels exe).label sc + Int64.ofNat (zl + zf + z1 + z2) =
      (xProN4 ms ((_root_.Executable.labels exe).label fn) zl zf z1 z2 Z lim J).pc := by
    show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add']
  exact {
    w0 := blkW_abX (l := fn) (k := 0) (rl := fn) hμ (code_field hp hend b0 he0)
      (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _)) hR hlo hhi
      (fun j hj => pcOffA_add hoff hmf (Nat.le_refl 0) (xHead_off j hj) he0.symm) he0 (abOffHC_sound hlab c0)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
    w1 := blkW_abX (l := sc) (k := 0) (rl := sc) hμ (code_field hp hend b1 he1)
      (xLea_ok (lo := -8 - Z.toInt) (hi := 0) Z zl) hR hlo hhi
      (fun j hj => pcOffA_add hoff hms (Nat.le_refl 0) (o1 j hj) he1.symm) he1 (abOffHC_sound hlab c1)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hnl j hj hr).elim)
    w2 := nodeW_abX hμ (pcOffA_at hoff hms (Nat.zero_le _) (by omega) he2.symm) he2
      (by
        simp only [abSiH, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
        exact Spike.Lib.X64.HelloWf.siAbH_sound hlab c2)
      fun s c hA => by
        obtain ⟨hs, hn, hd, hpc, -⟩ := id hA
        have hc : CellAt s (fsDir .r11 lim) zf := (code_field hp hend b2 he2 s hs hn).cell0 rfl rfl hpc
        obtain ⟨tree, hex, hl⟩ := movfs_leaf hc hd
        exact ⟨_, tree, hc, (fun w w' h => by unfold fsDir op64 at h; cases h), hex, hl⟩
    w3 := blkW_abX (l := sc) (k := zl + zf) (rl := sc) hμ (code_field hp hend b3 he3)
      (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ L z1 z2) hR hlo hhi
      (fun j hj => pcOffA_add hoff hms (Nat.zero_le _) (o3 j hj) he3.symm) he3 (abOffHC_sound hlab c3)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hnc j hj hr).elim)
    w4 := blkW_abX (l := sc) (k := zl + zf + z1 + z2) (rl := sc) hμ (code_field hp hend b4 he4)
      (xFr_ok (lo := -8 - Z.toInt) (hi := 0) Z zs ps hps) hR hlo hhi
      (fun j hj => pcOffA_add hoff hms (Nat.zero_le _) (o4 j hj) he4.symm) he4 (abOffHC_sound hlab c4)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false hnr j hj hr).elim) }

end Pro

/-! ## The thread worker -/

section Thr

/-- **The thread worker's pcs**: its tail from `.x13` (42 bytes) and its `.entry` block (29). -/
def thrRuns : List (Label × Nat × Nat) :=
  [(".Lscc_rt_thr_worker.x13", 0, 42), (".Lscc_rt_thr_worker.entry", 0, 29)]

theorem thrRuns_chk : runsNeChk helloCells thrRuns abPtsA = true := by decide +kernel

/-- The thread worker's prologue's pcs, from its label and its stack check. -/
theorem thrProRuns_chk :
    runsNeChk helloCells [("scc_rt_thr_worker", 0, 4), (".Lscc_rt_thr_worker.chk", 0, 5 + 9 + 3 + 2 + 4 +
      szSum thrPs)] abPtsA = true := by
  decide +kernel

/-! The thread worker's blocks' and cells' targets off the write abort's pcs (decided at helloCells' code
labels). -/

theorem thC_b0 : abOffHC ".Lscc_rt_thr_worker.x13" 9 ".Lscc_rt_thr_worker.x13" HThrTail.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thC_b1 : abOffHC ".Lscc_rt_thr_worker.x13" 28 ".Lscc_rt_thr_worker.x13" HThrTail.b1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thC_thE : abOffHC ".Lscc_rt_thr_worker.entry" 0 ".Lscc_rt_thr_worker.entry" HThrHead.thE = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thS_x13 : Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_thr_worker.x13" 0 9 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thS_ex : Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_thr_worker.x13" 24 4 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thS_sys : Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_thr_worker.x13" 40 2 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thP_c0 : abOffHC "scc_rt_thr_worker" 0 "scc_rt_thr_worker" xHead = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thP_c1 : abOffHC ".Lscc_rt_thr_worker.chk" 0 ".Lscc_rt_thr_worker.chk" (xLea 64 5) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thP_c2 : Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_thr_worker.chk" 5 9 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thP_c3 : abOffHC ".Lscc_rt_thr_worker.chk" (5 + 9) ".Lscc_rt_thr_worker.chk"
    (xCmp ".Lscc_rt_thr_worker.stk" 3 2) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem thP_c4 : abOffHC ".Lscc_rt_thr_worker.chk" (5 + 9 + 3 + 2) ".Lscc_rt_thr_worker.chk"
    (xFr 64 4 thrPs) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `scc_rt_thr_worker`'s prologue** (`ZObl.hzT`, frame 64). -/
theorem thrPro_abX {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -72)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    XProW (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 64 8 ".Lscc_rt_thr_worker.stk" 5 9 3 2 4 thrPs
      J :=
  xProW_abX hp hend hlab hμ hello_thrPro (by decide) hR
    (by have h64 : (64 : Int64).toInt = 64 := (by decide); omega) hhi (by decide) thrProRuns_chk
    (by decide) (by decide) (by decide) (by decide) thP_c0 thP_c1 thP_c2 thP_c3 thP_c4 (by decide) (by decide)
    (by decide)

/-- **`AbX` at `scc_rt_thr_worker`'s head** (`ZObl.hZEt`). -/
theorem thrHead_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : HThrHead.TN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (HThrHead.tN (_root_.Executable.labels exe).label J L i) (HThrHead.blkN i) := by
  have hoff := runsOffA_of_chk hp thrRuns_chk
  cases i
  · have he : (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.entry" + Int64.ofNat 0 =
        (HThrHead.tN (_root_.Executable.labels exe).label J L .e).pc := ofNat_zero' _
    exact blkW_abX (l := ".Lscc_rt_thr_worker.entry") (k := 0) (rl := ".Lscc_rt_thr_worker.entry") hμ
      (thECode hp hend) HThrHead.thE_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff (List.Mem.tail _ (List.Mem.head _)) (Nat.le_refl 0)
        (by revert j; decide) he.symm)
      he (abOffHC_sound hlab thC_thE)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-- **`AbX` at `scc_rt_thr_worker`'s tail** (`ZObl.hZT`), at its executing offsets: the load of the thread
pointer (`movfs_leaf`), its two blocks, the store of the thread's `exited` word (`st_leaf`), the `exit`'s
`syscall` (`nodeZA_abX_sys`). -/
theorem thrTail_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 8 ≤ R.hi)
    {c3 : Ctl} {tp sp0 : BitVec 64} (i : HThrTail.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 i) (HThrTail.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp) (sp := sp0)
  have hoff := runsOffA_of_chk hp thrRuns_chk
  have hm : (".Lscc_rt_thr_worker.x13", 0, 42) ∈ thrRuns := List.Mem.head _
  have hsi : ∀ {k z : Nat}, Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_thr_worker.x13" k z = true →
      (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13" + Int64.ofNat k + Int64.ofNat z ∉
        Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label :=
    fun h => Spike.Lib.X64.HelloWf.siAbH_sound hlab h
  cases i
  · exact cellZA_abXD (l := ".Lscc_rt_thr_worker.x13") (k := 0) hμ hc.x13
      (pcOffA_at hoff hm (Nat.le_refl 0) (by decide) (ofNat_zero' _).symm) (ofNat_zero' _) (hsi thS_x13)
      (fun w w' h => by unfold fsDir op64 at h; cases h) fun _ hc hd => movfs_leaf hc hd
  · exact blkW_abX (l := ".Lscc_rt_thr_worker.x13") (k := 9) (rl := ".Lscc_rt_thr_worker.x13") hμ hc.n1
      HThrTail.b0_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff hm (Nat.zero_le 9) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab thC_b0)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact cellZA_abXD (l := ".Lscc_rt_thr_worker.x13") (k := 24) hμ hc.ex
      (pcOffA_at hoff hm (Nat.zero_le 24) (by decide) rfl) rfl (hsi thS_ex)
      (fun w w' h => by unfold stDir Spike.Lib.X64.AI.toDir op64 at h; cases h) fun _ hc hd => st_leaf hc hd
  · exact blkW_abX (l := ".Lscc_rt_thr_worker.x13") (k := 28) (rl := ".Lscc_rt_thr_worker.x13") hμ hc.n2
      HThrTail.b1_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff hm (Nat.zero_le 28) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab thC_b1)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact nodeZA_abX_sys (n := HThrTail.NA (_root_.Executable.labels exe).label c3 tp sp0 .sys)
      (l := ".Lscc_rt_thr_worker.x13") (k := 40) hμ hc.sys
      (pcOffA_at hoff hm (Nat.zero_le 40) (by decide) rfl) rfl (hsi thS_sys)

end Thr

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.movfs_leaf'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.movfs_leaf

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.st_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.st_leaf

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.cellZA_abXD'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.cellZA_abXD

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.nodeZA_abX_sys'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.nodeZA_abX_sys

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.xHead_off' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.xHead_off

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.xProW_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.xProW_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrProRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrProRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thC_b0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thC_b0

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thC_b1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thC_b1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thC_thE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thC_thE

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thS_x13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thS_x13

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thS_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thS_ex

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thS_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thS_sys

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c0

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c2

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c3

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thP_c4

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrPro_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrPro_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrHead_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrHead_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrTail_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.thrTail_abX
