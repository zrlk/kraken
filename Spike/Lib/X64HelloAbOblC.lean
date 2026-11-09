/-
**`AbX` at the child's stub** (x86-64; the twin of `Spike/Lib/A64HelloAbOblC.lean`, the pilot of
`X64HelloAbObl`'s recipe): `ZObl.hZc` at `X := AbX μ lab`, the twin of `RelZH.child_relH` (`X64HelloRelZ`) with
`blkW_abX` for its covered blocks.

- `cellZA_abX`: `AbX` at a single-cell node whose instruction is silent and steps `z` bytes on (the stub's
  `testq` and `xorl`, which `okBlk` does not cover).
- `stubRuns`, `stubRuns_chk`: the stub's pcs, off the exits and the transfer sites (decided on the listing).
- `child_abX`: `AbX` at the stub's four nodes.

Unlike AArch64 (two blocks: the `cbz` past the `clone` and the call block), the stub is four nodes: the `testq`
and the `je` at `.Lwc_main.x3 + 96`, `+ 99`, the `xorl %ebp, %ebp` row and the call block at `.child`; the two
rows are single cells (`cellZA_abX`, from `exec_test_rr` and `exec_fi`), the region needs `R.lo ≤ -128` and no
alignment, and the stub's single-cell checks are `HelloWf.siAbH` at hello's code labels.
-/
import Spike.Lib.X64HelloAbObl
import Spike.Lib.X64HelloRelZ
import Spike.Lib.X64RunsOff

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt)
open Scc.Sem (Marks TreeLeaf)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open Spike.Lib (Region)
open Spike.Lib.X64 (ND CodeAt cellOff)
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64WakeOff (RunsOffA PcOffA pcOffA_add pcOffA_at)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words cN childN cBlk childIn hello_childIn tsB jeB xbp chB jeB_ok
  chB_ok x25L chL)
open SccCode (helloCells)

/-- **`AbX` at a single-cell node**: the cell's instruction (`hcode`) is no `syscall` and every leaf of its tree
is `z` bytes on (`hstep`), that pc off the write abort's pcs (`h`), the node's pc off the exits and the transfer
sites by label (`hoff`). -/
theorem cellZA_abX {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    (hμ : MarksL μ (_root_.Executable.labels exe).label) {fs : List TermRun.Frame} {n : ND} {d : Directive}
    {z : Nat} {l : Label} {k : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (hoff : PcOffA (_root_.Executable.labels exe).label n.pc)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (h : (_root_.Executable.labels exe).label l + Int64.ofNat k + Int64.ofNat z ∉
      Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label)
    (hstep : ∀ s : State, CellAt s d z → (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧
      ∃ tree, isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n [(d, z)] := by
  intro s σ c he' hn _ _ _ _ _ j hj m _ _
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  refine ⟨?_, fun _ h => h⟩
  have hp0 : n.pc + Int64.ofNat (cellOff [(d, z)] 0) = n.pc := Spike.Lib.X64.Flow.Worker.cellOff_zero _ _
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff [(d, z)] 0)) } d z :=
    (hcode s he' hn).cell0 rfl rfl hp0
  obtain ⟨hd, tree, hex, hl⟩ := hstep _ hc
  rw [he] at h
  have hq : PcOffA (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (cellOff [(d, z)] 0)) := by
    rw [hp0]; exact hoff
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s' :=
    fun s' hs' => Spike.Lib.X64.WriteAb.not_ab_of_pc (by rw [hl s' hs']; simp only; rw [hp0]; exact h)
  refine AbX.of_off hμ (Spike.Lib.X64ConsumerA.AbSt.ofLeaves (pcOff_of hμ hq).noTake
    (Scc.Sem.X64.atSyscall_false_of_cellAt hc hd) fun t ht => ?_) hq
  rw [hex] at ht; cases ht; exact Spike.Lib.X64Consumer.allInv_of_leaf tree hnab

/-- **The child's stub's pcs**: the `testq` and the `je` past the `clone`, the `xorl` row and the call block. -/
def stubRuns : List (Label × Nat × Nat) :=
  [(x25L, 96, 101), (chL, 0, 22)]

theorem stubRuns_chk : runsNeChk helloCells stubRuns abPtsA = true := by decide +kernel

/-- The stub's blocks' targets off the write abort's pcs (decided at helloCells' code labels). -/
theorem chC_je : abOffHC x25L 99 chL jeB = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem chC_ch : abOffHC chL 2 chL chB = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- The stub's rows' next pcs off the write abort's pcs. -/
theorem chS_ts : Spike.Lib.X64.HelloWf.siAbH x25L 96 3 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem chS_xb : Spike.Lib.X64.HelloWf.siAbH chL 0 2 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- The `je`'s pcs within the stub's first run. -/
theorem jeB_off : ∀ j < jeB.length, 99 + cellOff jeB j < 101 := by decide

/-- The call block's pcs within the stub's second run. -/
theorem chB_off : ∀ j < chB.length, 2 + cellOff chB j < 22 := by decide

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **`AbX` at the child's stub** (`ZObl.hZc`). -/
theorem child_abX (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
    (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x)
    (hμ : MarksL μ (_root_.Executable.labels exe).label) {R : Region} {F : MachineData → Prop}
    (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64} (i : Child.CN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (cN (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i) := by
  have hin := hello_childIn
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt helloCells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hoff := runsOffA_of_chk hp stubRuns_chk
  have z0 : ∀ a : Int64, a + Int64.ofNat 0 = a := fun a => by
    rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  cases i
  · refine cellZA_abX (l := x25L) (k := 96) hμ (fun s he hn => code bts s he hn)
      (pcOffA_at hoff (List.Mem.head _) (Nat.le_refl _) (by decide) rfl) rfl
      (Spike.Lib.X64.HelloWf.siAbH_sound hlab chS_ts) fun s hc => ?_
    refine ⟨?_, _, Kraken.Promising.Lower.X64.exec_test_rr hc, ?_⟩
    · intro w w' h; cases h
    · rintro s' ⟨_, h⟩; subst h; rfl
  · exact blkW_abX (l := x25L) (k := 99) (rl := chL) hμ (code bje) jeB_ok hR (by omega) (by omega)
      (fun j hj => pcOffA_add hoff (List.Mem.head _) (by decide : 96 ≤ 99) (jeB_off j hj) rfl)
      rfl (abOffHC_sound hlab chC_je)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · refine cellZA_abX (l := chL) (k := 0) hμ
      (fun s he hn => (by simpa using code bxb s he hn : CodeAt s ((_root_.Executable.labels exe).label chL) xbp))
      (pcOffA_at hoff (List.Mem.tail _ (List.Mem.head _)) (Nat.le_refl _) (by decide) (z0 _).symm) (z0 _)
      (Spike.Lib.X64.HelloWf.siAbH_sound hlab chS_xb) fun s hc => ?_
    obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
    refine ⟨?_, t, hex, fun s' hs' => ?_⟩
    · intro w w' h; cases h
    · obtain ⟨_, h⟩ := Spike.Lib.X64.WakeWf.silentLeaf hst hs'; subst h; rfl
  · exact blkW_abX (l := chL) (k := 2) (rl := chL) hμ (code bch) chB_ok hR (by omega) (by omega)
      (fun j hj => pcOffA_add hoff (List.Mem.tail _ (List.Mem.head _)) (by decide : 0 ≤ 2) (chB_off j hj) rfl)
      rfl (abOffHC_sound hlab chC_ch)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.cellZA_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.cellZA_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.stubRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.stubRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.chC_je' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.chC_je

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.chC_ch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.chC_ch

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.chS_ts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.chS_ts

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.chS_xb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.chS_xb

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.jeB_off' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.jeB_off

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.chB_off' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.chB_off


/--
info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.child_abX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.child_abX
