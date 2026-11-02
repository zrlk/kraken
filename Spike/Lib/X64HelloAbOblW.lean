/-
**`AbX` at `wc_worker`'s head** (x86-64; the twin of `Spike/Lib/A64HelloAbOblW.lean`, `X64HelloAbObl`'s
recipe): `WcObl.hz`, `hZE`, `hZC` (`X64HelloWorkerSegRP`) at `X := AbX μ lab`, the twins of
`RelZH.wcPro_relH`, `wE_relH`, `wCall_relH` (`X64HelloRelZ`), generic in the invariants (`J`, `Pr`, `Kc`).

- `wcRuns`, `wcRuns_chk`, `wcProRuns_chk`, `wcC_*`, `wcS_mul`, `wcP_c0`–`wcP_c4`: the decided checks (pcs off
  the exits and the transfer sites; targets off the write abort's pcs).
- `wcPro_abX`, `wE_abX`, `wCall_abX`: the head's fields.

Unlike AArch64 (a `ProW` of frame 96, one `.0_entry` block of 21 instructions, the call node a `NodeW`, a
16-aligned region), the prologue is an `XProW` of frame 80 (`xProW_abX`), the `.entry` block is three nodes (the
block up to the multiply, the multiply `imulq` as a single cell leaving the flags undefined, the block after it;
`Body.wN`), the call node is a `NodeZA` over `print`'s entry block `Print.x0` with `%rsp` at `-96`, and the region
needs no alignment.
-/
import Spike.Lib.X64HelloAbOblT

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt)
open Scc.Sem (Marks)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region)
open Spike.Lib.X64 (ND)
open Spike.Lib.X64.Flow (XProW xHead xLea xCmp xFr szSum ofNat_zero')
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64WakeOff (pcOffA_add pcOffA_at)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloCells)

/-! ## The decided checks -/

/-- **`wc_worker`'s head's pcs**: its `.entry` block (87 bytes: the block up to the multiply, the multiply, the
block after it) and `scc_rt_print`'s entry block (16). -/
def wcRuns : List (Label × Nat × Nat) :=
  [(".Lwc_worker.entry", 0, 87), ("scc_rt_print", 0, 16)]

theorem wcRuns_chk : runsNeChk helloCells wcRuns abPtsA = true := by decide +kernel

/-- `wc_worker`'s prologue's pcs, from its label and its stack check. -/
theorem wcProRuns_chk :
    runsNeChk helloCells [("wc_worker", 0, 4), (".Lwc_worker.chk", 0, 5 + 9 + 3 + 6 + 4 + szSum Wk.wcPs)]
      abPtsA = true := by
  decide +kernel

theorem wcC_wkE1 : abOffHC ".Lwc_worker.entry" 0 ".Lwc_worker.entry" Body.wkE1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcC_wkE2 : abOffHC ".Lwc_worker.entry" 40 ".Lwc_worker.entry" Body.wkE2 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcS_mul : Spike.Lib.X64.HelloWf.siAbH ".Lwc_worker.entry" 36 4 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcC_pr : abOffHC "scc_rt_print" 0 "scc_rt_print" Spike.Lib.X64.Print.x0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcP_c0 : abOffHC "wc_worker" 0 "wc_worker" xHead = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcP_c1 : abOffHC ".Lwc_worker.chk" 0 ".Lwc_worker.chk" (xLea 80 5) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcP_c2 : Spike.Lib.X64.HelloWf.siAbH ".Lwc_worker.chk" 5 9 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcP_c3 : abOffHC ".Lwc_worker.chk" (5 + 9) ".Lwc_worker.chk" (xCmp ".Lwc_worker.stk" 3 6) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

theorem wcP_c4 : abOffHC ".Lwc_worker.chk" (5 + 9 + 3 + 6) ".Lwc_worker.chk" (xFr 80 4 Wk.wcPs) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-! ## `wc_worker`'s head -/

section W

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `wc_worker`'s prologue** (`WcObl.hz`, frame 80). -/
theorem wcPro_abX {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -88)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    XProW (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "wc_worker") 80 8 ".Lwc_worker.stk" 5 9 3 6 4 Wk.wcPs J :=
  xProW_abX hp hend hlab hμ Wk.hello_wcPro (by decide) hR
    (by have h80 : (80 : Int64).toInt = 80 := (by decide); omega) hhi (by decide) wcProRuns_chk
    (by decide) (by decide) (by decide) (by decide) wcP_c0 wcP_c1 wcP_c2 wcP_c3 wcP_c4 (by decide) (by decide)
    (by decide)

/-- **`AbX` at `wc_worker`'s `.entry` nodes** (`WcObl.hZE`): the block up to the multiply, the multiply (a single
cell, `exec_fi`), the block after it. -/
theorem wE_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE1 ∧
      NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label J Pr .mul) [(Body.wkMul.toDir, 4)] ∧
      NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label J Pr .e2) Body.wkE2 := by
  have hoff := runsOffA_of_chk hp wcRuns_chk
  have hm : (".Lwc_worker.entry", 0, 87) ∈ wcRuns := List.Mem.head _
  refine ⟨?_, ?_, ?_⟩
  · exact blkW_abX (l := ".Lwc_worker.entry") (k := 0) (rl := ".Lwc_worker.entry") hμ (Wk.wkE1Code hp hend)
      Body.wkE1_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff hm (Nat.le_refl 0) (by revert j; decide) (ofNat_zero' _).symm)
      (ofNat_zero' _) (abOffHC_sound hlab wcC_wkE1)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)
  · refine cellZA_abX (l := ".Lwc_worker.entry") (k := 36) hμ (Wk.wkMulCode hp hend)
      (pcOffA_at hoff hm (Nat.zero_le 36) (by decide) rfl) rfl
      (Spike.Lib.X64.HelloWf.siAbH_sound hlab wcS_mul) fun s hc => ?_
    obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi hc
    refine ⟨?_, t, hex, fun s' hs' => ?_⟩
    · intro w w' h; cases h
    · obtain ⟨_, h⟩ := Spike.Lib.X64.WakeWf.silentLeaf hst hs'; subst h; rfl
  · exact blkW_abX (l := ".Lwc_worker.entry") (k := 40) (rl := ".Lwc_worker.entry") hμ (Wk.wkE2Code hp hend)
      Body.wkE2_ok hR hlo hhi
      (fun j hj => pcOffA_add hoff hm (Nat.zero_le 40) (by revert j; decide) rfl)
      rfl (abOffHC_sound hlab wcC_wkE2)
      (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)

/-- **`AbX` at `wc_worker`'s call node** (`WcObl.hZC`): `scc_rt_print`'s entry block, `%rsp` at `-96`, in the
worker's region. -/
theorem wCall_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    {J Kc : AS → Ctl → Prop} :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label J Kc) Spike.Lib.X64.Print.x0 := by
  have hoff := runsOffA_of_chk hp wcRuns_chk
  exact blkW_abX (l := "scc_rt_print") (k := 0) (rl := "scc_rt_print") hμ
    (fun s he hn => (Wk.printCode hp hend (c0 := ⟨.ret .unit, [], none⟩) (rbp0 := 0) (ra := 0)).e s he hn)
    RelZH.x0_okW hR hlo hhi
    (fun j hj => pcOffA_add hoff (List.Mem.tail _ (List.Mem.head _)) (Nat.le_refl 0) (by revert j; decide)
      (ofNat_zero' _).symm)
    (ofNat_zero' _) (abOffHC_sound hlab wcC_pr)
    (fun _ _ _ j hj hr => (Spike.Lib.X64Consumer.noRet_false (by decide) j hj hr).elim)

end W

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcProRuns_chk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcProRuns_chk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcC_wkE1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcC_wkE1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcC_wkE2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcC_wkE2

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcS_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcS_mul

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcC_pr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcC_pr

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c0

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c1

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c2

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c3

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcP_c4

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcPro_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcPro_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wE_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wE_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wCall_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wCall_abX
