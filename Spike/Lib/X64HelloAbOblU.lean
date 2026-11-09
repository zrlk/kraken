/-
**`AbX` at `wc_worker`'s tail and at `scc_rt_unpark`** (x86-64; the twin of `Spike/Lib/A64HelloAbOblU.lean`,
`X64HelloAbObl`'s recipe): `WcObl.hZW`, `hZU` (`X64HelloWorkerSegRP`) at `X := AbX μ lab`, the twins of
`RelZH.tail_relH`, `unpk_relH` (`X64HelloRelZ`).

Their `ret` blocks return to the ghost return address, which the write abort's check needs at a label:
`tail_abX` takes `hra` (the tail returns to `scc_rt_thr_worker`'s `.x13`), `unpk_abX` takes `hra` (`unpark`
returns to `wc_worker`'s `.x18`).

- `tlRuns`, `upRuns` and their `_chk`s, `tlC_*`, `tlS_st`, `upC_*`, `upS_*`: the decided checks.
- `xchg_leaf`: an `xchgq`'s leaves are its size on.
- `tail_abX`, `unpk_abX`: the tail's fields.

Unlike AArch64 (the tail from `.sp4` and `.sp6` in 4-byte instructions, the store an `stlr`, unpark's exchange a
`swpal` and its system call an `svc`, the return to the thread worker's `.sp0` and to `wc_worker`'s `.sp6`, a
16-aligned region from `0`), the tail's nodes are at their executing offsets (`HelloTail.NA`) in sized cells from
`.x17` and `.x18`, the store is a plain `movq` (`st_leaf`), the exchange the locked `xchgq` (`xchg_leaf`), the
system call a `syscall` (`nodeZA_abX_sys`), the returns go to `.x13` and `.x18`, and the regions reach `8` with no
alignment.
-/
import Spike.Lib.X64HelloAbOblW

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_xchg exec_xchg_mapped op64)
open Scc.Sem (Marks TreeLeaf)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region)
open Spike.Lib.X64 (ND mB xchgDir stDir)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64WakeOff (pcOffA_add pcOffA_at)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloCells)

/-! ## The decided checks -/

/-- **`wc_worker`'s tail's pcs**: from `.x17` (23 bytes: the block before the store, the store, the call's block)
and its epilogue `.x18` (5). -/
def tlRuns : List (Label × Nat × Nat) :=
  [(".Lwc_worker.x0", 0, 23), (".Lwc_worker.x1", 0, 5)]

theorem tlRuns_chk : runsNeChk helloCells tlRuns abPtsA = true := by decide +kernel

/-- **`scc_rt_unpark`'s pcs**: its entry block (12 bytes), from `.entry` (37: the block before the exchange, the
exchange, the test, the jump), from `.wake` (73: the arguments, the `syscall`, the return) and its `.done` block
(5). -/
def upRuns : List (Label × Nat × Nat) :=
  [("scc_rt_unpark", 0, 12), (".Lscc_rt_unpark.entry", 0, 37), (".Lscc_rt_unpark.wake", 0, 73),
    (".Lscc_rt_unpark.done", 0, 5)]

theorem upRuns_chk : runsNeChk helloCells upRuns abPtsA = true := by decide +kernel

theorem tlC_b0 : abOffHC ".Lwc_worker.x0" 0 ".Lwc_worker.x0" HelloTail.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem tlS_st : Spike.Lib.X64.HelloWf.siAbH ".Lwc_worker.x0" 11 3 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem tlC_b1 : abOffHC ".Lwc_worker.x0" 14 ".Lwc_worker.x0" HelloTail.b1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem tlC_b2 : abOffHC ".Lwc_worker.x1" 0 ".Lscc_rt_thr_worker.x0" HelloTail.b2 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b0 : abOffHC "scc_rt_unpark" 0 "scc_rt_unpark" Unpark.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b1 : abOffHC ".Lscc_rt_unpark.entry" 0 ".Lscc_rt_unpark.entry" Unpark.b1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upS_xchg : Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_unpark.entry" 11 4 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b2 : abOffHC ".Lscc_rt_unpark.entry" 15 ".Lscc_rt_unpark.entry" Unpark.b2 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b3 : abOffHC ".Lscc_rt_unpark.entry" 35 ".Lscc_rt_unpark.entry" Unpark.b3 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b4 : abOffHC ".Lscc_rt_unpark.wake" 0 ".Lscc_rt_unpark.wake" Unpark.b4 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upS_sys : Spike.Lib.X64.HelloWf.siAbH ".Lscc_rt_unpark.wake" 62 2 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b5 : abOffHC ".Lscc_rt_unpark.wake" 64 ".Lwc_worker.x1" Unpark.b5 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem upC_b6 : abOffHC ".Lscc_rt_unpark.done" 0 ".Lwc_worker.x1" Unpark.b6 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-! ## The exchange's leaves -/

/-- **An `xchgq`'s leaves are `z` bytes on.** -/
theorem xchg_leaf {s : State} {z : Nat} {b r : Reg64} {k : Int64} (hc : CellAt s (xchgDir b k r) z)
    (hd : s.decls = {}) :
    ∃ tree, isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s z (mB b k)) 8 with
  | none =>
    refine ⟨_, exec_xchg hc rfl hm, fun s' hs' => ?_⟩
    rw [hd, EvTree.access_empty] at hs'
    obtain ⟨_, rfl⟩ := hs'
    rfl
  | some j =>
    obtain ⟨_, h⟩ := exec_xchg_mapped hc rfl hm
    refine ⟨_, h, fun s' hs' => ?_⟩
    cases hs'
    rfl

/-! ## `wc_worker`'s tail, `scc_rt_unpark` -/

section U

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `wc_worker`'s tail nodes** (`WcObl.hZW`), at their executing offsets: the return address at
`scc_rt_thr_worker`'s `.x13` (`hra`). -/
theorem tail_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -96) (hhi : 8 ≤ R.hi)
    {c0 c1 c2 : Ctl} {A B rbp0 ra tp sp : BitVec 64}
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0")
    (i : HelloTail.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (HelloTail.NA (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp i) (HelloTail.blkN i) := by
  have hc := Labels.wkTailCode hp hend (c0 := c0) (c1 := c1) (c2 := c2) (A := A) (B := B) (rbp0 := rbp0)
    (ra := ra) (tp := tp) (sp := sp)
  have hoff := runsOffA_of_chk hp tlRuns_chk
  have m7 : (".Lwc_worker.x0", 0, 23) ∈ tlRuns := List.Mem.head _
  have m8 : (".Lwc_worker.x1", 0, 5) ∈ tlRuns := List.Mem.tail _ (List.Mem.head _)
  cases i
  · exact blkW_abX (l := ".Lwc_worker.x0") (k := 0) (rl := ".Lwc_worker.x0") hμ hc.e HelloTail.b0_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff m7 (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab tlC_b0)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact cellZA_abXD (l := ".Lwc_worker.x0") (k := 11) hμ hc.st
      (pcOffA_at hoff m7 (Nat.zero_le 11) (by decide) rfl) rfl
      (Spike.Lib.X64.HelloWf.siAbH_sound hlab tlS_st)
      (fun w w' h => by unfold stDir Spike.Lib.X64.AI.toDir op64 at h; cases h) fun _ hc hd => st_leaf hc hd
  · exact blkW_abX (l := ".Lwc_worker.x0") (k := 14) (rl := ".Lwc_worker.x0") hμ hc.n3 HelloTail.b1_ok hR hlo
      hhi (fun j hj => pcOffA_add hoff m7 (Nat.zero_le 14) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab tlC_b1)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)
  · exact blkW_abX (l := ".Lwc_worker.x1") (k := 0) (rl := ".Lscc_rt_thr_worker.x0") hμ hc.x18 HelloTail.b2_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m8 (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab tlC_b2)
      (Spike.Lib.X64Consumer.hret_of_run HelloTail.b2_ok fun σ c hJ => by
        obtain ⟨-, -, h0, -⟩ := hJ
        simp only [HelloTail.NA, HelloTail.blkN, HelloTail.b2_run]
        rw [h0]; exact hra)

/-- **`AbX` at `scc_rt_unpark`'s nodes** (`WcObl.hZU`): the return address at `wc_worker`'s `.x18` (`hra`). -/
theorem unpk_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c1 c2 : Ctl} {B rbp1 ra1 tp : BitVec 64}
    (hra : Int64.ofBitVec ra1 = (_root_.Executable.labels exe).label ".Lwc_worker.x1") (i : Unpark.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i) (Unpark.blkN i) := by
  have hc := Labels.unpkCode hp hend (c0 := c1) (c1 := c2) (B := B) (rbp0 := rbp1) (ra := ra1) (tp := tp)
  have hoff := runsOffA_of_chk hp upRuns_chk
  have m0 : ("scc_rt_unpark", 0, 12) ∈ upRuns := List.Mem.head _
  have m1 : (".Lscc_rt_unpark.entry", 0, 37) ∈ upRuns := List.Mem.tail _ (List.Mem.head _)
  have m2 : (".Lscc_rt_unpark.wake", 0, 73) ∈ upRuns := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have m3 : (".Lscc_rt_unpark.done", 0, 5) ∈ upRuns :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have hsi : ∀ {l : Label} {k z : Nat}, Spike.Lib.X64.HelloWf.siAbH l k z = true →
      (_root_.Executable.labels exe).label l + Int64.ofNat k + Int64.ofNat z ∉
        Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label :=
    fun h => Spike.Lib.X64.HelloWf.siAbH_sound hlab h
  cases i
  · exact blkW_abX (l := "scc_rt_unpark") (k := 0) (rl := "scc_rt_unpark") hμ hc.e Unpark.b0_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff m0 (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab upC_b0)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact blkW_abX (l := ".Lscc_rt_unpark.entry") (k := 0) (rl := ".Lscc_rt_unpark.entry") hμ hc.n1 Unpark.b1_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m1 (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab upC_b1)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact cellZA_abXD (l := ".Lscc_rt_unpark.entry") (k := 11) hμ hc.xchg
      (pcOffA_at hoff m1 (Nat.zero_le 11) (by decide) rfl) rfl (hsi upS_xchg)
      (fun w w' h => by unfold xchgDir op64 at h; cases h) fun _ hc hd => xchg_leaf hc hd
  · exact blkW_abX (l := ".Lscc_rt_unpark.entry") (k := 15) (rl := ".Lscc_rt_unpark.entry") hμ hc.n2 Unpark.b2_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m1 (Nat.zero_le 15) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab upC_b2)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact blkW_abX (l := ".Lscc_rt_unpark.entry") (k := 35) (rl := ".Lscc_rt_unpark.entry") hμ hc.n3 Unpark.b3_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m1 (Nat.zero_le 35) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab upC_b3)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact blkW_abX (l := ".Lscc_rt_unpark.wake") (k := 0) (rl := ".Lscc_rt_unpark.wake") hμ hc.wake Unpark.b4_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m2 (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab upC_b4)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · exact nodeZA_abX_sys (n := Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp .sys)
      (l := ".Lscc_rt_unpark.wake") (k := 62) hμ hc.sys
      (pcOffA_at hoff m2 (Nat.zero_le 62) (by decide) rfl) rfl (hsi upS_sys)
  · exact blkW_abX (l := ".Lscc_rt_unpark.wake") (k := 64) (rl := ".Lwc_worker.x1") hμ hc.n5 Unpark.b5_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m2 (Nat.zero_le 64) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab upC_b5)
      (Spike.Lib.X64Consumer.hret_of_run Unpark.b5_ok fun σ c hJ => by
        obtain ⟨-, -, h0, -⟩ := hJ
        simp only [Unpark.N, Unpark.blkN, Unpark.b5_run]
        rw [h0]; exact hra)
  · exact blkW_abX (l := ".Lscc_rt_unpark.done") (k := 0) (rl := ".Lwc_worker.x1") hμ hc.done Unpark.b6_ok
      hR hlo hhi (fun j hj => pcOffA_add hoff m3 (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab upC_b6)
      (Spike.Lib.X64Consumer.hret_of_run Unpark.b6_ok fun σ c hJ => by
        obtain ⟨-, -, h0, -⟩ := hJ
        simp only [Unpark.N, Unpark.blkN, Unpark.b6_run]
        rw [h0]; exact hra)

end U

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlC_b0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlC_b0

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlS_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlS_st

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlC_b1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlC_b1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlC_b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.tlC_b2

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b0

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upS_xchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upS_xchg

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b2

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b3

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b4

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upS_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upS_sys

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b5

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.upC_b6

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.xchg_leaf'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.xchg_leaf

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.tail_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.tail_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.unpk_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.unpk_abX
