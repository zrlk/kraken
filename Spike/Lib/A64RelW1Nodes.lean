/-
**At most one write per path, a release write, at a node's states**
(AArch64): `RelZ`, the instruction's event tree is `RelW1 Arch.armv8`, at
the states of covered blocks (`blkZA_done`: they run to `.done`,
`blk_exec_done`) and at the single-instruction nodes of a runtime load
(`relZ_ldr`), a release store (`relZ_stlr`), an `acqRel` swap
(`relZ_swpal`) and a system call (`relZ_svc`, it faults), each with no
declarations (`decls = {}`; an address mapped in the private memory gives
no event). `nodeW_cell`, `nodeZA_cell`: such a fact of a single
instruction's cell at its node. `proW_relZ`: at a stack-checked prologue's
states (`ProW`).
-/
import Spike.Lib.A64CfgLW
import Spike.Lib.A64WakeNN
import Spike.Lib.RelW1

namespace Spike.Lib.A64.Flow.RelZ

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Spike.Lib.A64.Flow.Worker (NodeZA)

/-- **The instruction's event tree writes at most once on each path, a
release write.** -/
def RelZ : Frag isaLSE2 := fun s _ => ∀ e, isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e

theorem relZ_of_done {s : State} {c : Ctl} {s' : State} (h : isaLSE2.exec s = some (.done s')) : RelZ s c := by
  intro e he; rw [h] at he; cases he; exact .noW (.done _)

/-- **A runtime load** (`ldr Xt, [Xn, #i]`). -/
theorem relZ_ldr {s : State} {c : Ctl} {t b : XReg} {i : Int64} (hc : CellAt s (ldrDir t b i) 4)
    (hd : s.decls = {}) : RelZ s c := by
  cases h : Mem.loadInt s.st.1.dmem (BitVec.ofInt 64 ((s.st.1.regs.getXReg b).toBitVec.toInt + i.toInt)) 8 with
  | none =>
    intro e he
    rw [exec_ldr hc rfl h, hd, EvTree.access_empty] at he
    cases he
    exact .noW (.load fun _ => .done _)
  | some j => exact relZ_of_done (exec_ldr_mapped hc rfl h)

/-- **A release store** (`stlr Xt, [Xn]`). -/
theorem relZ_stlr {s : State} {c : Ctl} {src : RegOrZr .W64} {n : XReg}
    (hc : CellAt s (.instr ⟨.W64, .STLR .W64 src (.low (.reg n) .W64)⟩) 4) (hd : s.decls = {}) : RelZ s c := by
  cases h : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg n).toBitVec 8 with
  | none =>
    intro e he
    rw [exec_stlr hc h, hd, EvTree.access_empty] at he
    cases he
    exact .store EvTree.storeKind_rel_armv8 fun _ => .done _
  | some j => exact relZ_of_done (exec_stlr_mapped hc h)

/-- **An `acqRel` swap** (`swpal Xs, Xt, [Xn]`). -/
theorem relZ_swpal {s : State} {c : Ctl} {rs rt b : XReg} (hc : CellAt s (Park.swpDir .acqRel rs rt b) 4)
    (hd : s.decls = {}) : RelZ s c := by
  cases h : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg b).toBitVec 8 with
  | none =>
    intro e he
    rw [exec_swp hc h, hd, EvTree.access_empty] at he
    cases he
    exact .rmw EvTree.storeKind_rmw_acqRel_armv8 fun _ => .done _
  | some j =>
    obtain ⟨_, hx⟩ := exec_swp_mapped hc h
    exact relZ_of_done hx

/-- **A system call**: it faults. -/
theorem relZ_svc {s : State} {c : Ctl} (hc : CellAt s svcDir 4) : RelZ s c := by
  intro e he; rw [exec_svc hc] at he; cases he; exact .noW (.fault _)

section Nodes

variable {Z : Frag isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND}

/-- **A fact of a single instruction's cell at its node** (`NodeW`). -/
theorem nodeW_cell {d : Directive} (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (h : ∀ s c, CellAt s d 4 → s.decls = {} → Z s c) : NodeW Z (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨he, hn, hdc, hpc, _⟩ =>
    ⟨h s c ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)) hdc, fun _ h => h⟩

/-- **A fact of a single instruction's cell at its node** (`NodeZA`). -/
theorem nodeZA_cell {d : Directive} (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (h : ∀ s c, CellAt s d 4 → s.decls = {} → Z s c) : NodeZA Z exe endPc R F n [d] :=
  fun s σ c he hn hd _ _ _ _ k hk m _ _ => by
    have hk0 : k = 0 := by simp at hk; omega
    subst hk0
    exact ⟨h _ c ((hcode { s with st := (m, n.pc + Int64.ofNat (4 * 0)) } he hn).cell (j := 0) rfl rfl rfl
      (by simp)) hd, fun _ h => h⟩

/-- **A fact of every state that runs to `.done`, at a covered block's
states.** -/
theorem blkZA_done {lo hi : Int} {blk : List Directive} (hZ : ∀ s c s', isaLSE2.exec s = some (.done s') → Z s c)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    NodeZA Z exe endPc R F n blk :=
  fun s σ c he hn _ _ _ _ _ k hk m hA _ => by
    subst he
    obtain ⟨s', h⟩ := blk_exec_done hok hR hal hlo hhi (hcode s rfl hn) hk hA
    exact ⟨hZ _ c _ h, fun _ h => h⟩

end Nodes

/-- **`RelZ` at a stack-checked prologue's states** (`ProW`): its blocks are
covered, the limit's load a runtime load. -/
theorem proW_relZ {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} (hin : prologueIn prog fn sc entry Z lim L ps = true)
    {J : AS → Ctl → Prop} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, Spike.Lib.offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true) :
    ProW RelZ (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim L ps J := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  refine ⟨blkZA_done (fun _ _ _ h => relZ_of_done h) (chkHead_ok (-Z.toInt) 0 Z) hR hal hlo hhi
      (code_of hp hend b0 ?_),
    nodeW_cell (code_of hp hend b1 ?_) fun _ _ hc hd => relZ_ldr hc hd,
    blkZA_done (fun _ _ _ h => relZ_of_done h) (chkBr_ok (-Z.toInt) 0 Z L) hR hal hlo hhi (code_of hp hend b2 ?_),
    blkZA_done (fun _ _ _ h => relZ_of_done h) (frameSet_ok h16 hZ (by omega) (Int.le_refl 0) hps) hR hal hlo hhi
      (code_of hp hend b3 ?_)⟩
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [proN1, ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [proN2, ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [proN3, ofNat4_succ, ofNat4_zero]

end Spike.Lib.A64.Flow.RelZ
