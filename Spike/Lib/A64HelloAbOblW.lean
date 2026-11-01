/-
**`AbX` at `wc_worker`'s head** (row 5i-hab1, P3,
AArch64; `A64HelloAbObl`'s recipe): `WcObl.hz`, `hZE`, `hZC` at
`X := AbX μ lab`, the twins of `Wk.wcPro_relH`, `wE_relH`, `wCall_relH`
(`A64HelloRelZ`), generic in the invariants (`J`, `Pr`, `Kc`).

- `wcRuns`, `wcRuns_chk`, `wcProRuns_chk`, `wcC_*`, `wcP_c0`–`wcP_c3`: the
  decided checks (pcs off the exits and the transfer sites; targets off
  the write abort's pcs).
- `wcPro_abX`, `wE_abX`, `wCall_abX`: P3's head fields.
-/
import Spike.Lib.A64HelloAbOblT

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND NodeW ofNat4_succ ofNat4_zero chkHead chkBr frameSet ProW)
open Spike.Lib.A64.Flow.Worker (NodeZA)
open Spike.Lib.A64WakeOff (pcOffA_add)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloProg)

/-! ## The decided checks -/

/-- **`wc_worker`'s head's pcs**: its `.0_entry` block (21 instructions)
and `scc_rt_print`'s entry block (six). -/
def wcRuns : List (Label × Nat × Nat) :=
  [(".L20_wc_worker.0_entry", 0, 21), ("scc_rt_print", 0, 6)]

theorem wcRuns_chk : runsNeChk helloProg wcRuns abPtsA = true := by decide +kernel

/-- `wc_worker`'s prologue's pcs, from its stack check. -/
theorem wcProRuns_chk :
    runsNeChk helloProg [(".L20_wc_worker.stack_check", 0, 9 + Wk.wcPs.length)] abPtsA = true := by
  decide +kernel

theorem wcC_wkE : abOffHC ".L20_wc_worker.0_entry" 0 ".L20_wc_worker.0_entry" Body.wkE = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem wcC_pr : abOffHC "scc_rt_print" 0 "scc_rt_print" A64.Print.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem wcP_c0 : abOffHC ".L20_wc_worker.stack_check" 0 ".L20_wc_worker.stack_check" (chkHead 96) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem wcP_c1 : abSiHC ".L20_wc_worker.stack_check" 2 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem wcP_c2 : abOffHC ".L20_wc_worker.stack_check" 3 ".L20_wc_worker.stack_check"
    (chkBr ".L20_wc_worker.stack_grow") = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem wcP_c3 : abOffHC ".L20_wc_worker.stack_check" 5 ".L20_wc_worker.stack_check"
    (frameSet 96 Wk.wcPs) = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-! ## P3: `wc_worker`'s head -/

section P3W

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `wc_worker`'s prologue** (`WcObl.hz`). -/
theorem wcPro_abX {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} :
    ProW (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "wc_worker") 96 8 ".L20_wc_worker.stack_grow" Wk.wcPs J :=
  proW_abX hp hend hlab hμ Wk.hello_wcPro (by decide) (by decide) hR hal hlo hhi (by decide) wcProRuns_chk
    wcP_c0 wcP_c1 wcP_c2 wcP_c3 (by decide)

/-- **`AbX` at `wc_worker`'s `.0_entry` block** (`WcObl.hZE`). -/
theorem wE_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE := by
  have hoff := runsOffA_of_chk hp wcRuns_chk
  have he : (_root_.Executable.labels exe).label ".L20_wc_worker.0_entry" + Int64.ofNat (4 * 0) =
      (Body.wN (_root_.Executable.labels exe).label J Pr .e).pc := ofNat4_zero _
  have hlen : Body.wkE.length = 21 := rfl
  exact blkW_abX (rl := ".L20_wc_worker.0_entry") hμ (Wk.wkECode hp hend) Body.wkE_ok hR hal hlo hhi
    (fun j hj => pcOffA_add hoff (List.Mem.head _) (Nat.le_refl 0) (by rw [hlen] at hj; omega) he.symm)
    he (abOffHC_sound hlab wcC_wkE)
    (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)

/-- **`AbX` at `wc_worker`'s call node** (`WcObl.hZC`): `scc_rt_print`'s
first instruction, `sp` at `-96`. -/
theorem wCall_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) {J Kc : AS → Ctl → Prop} :
    NodeW (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) (fun _ _ => False) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label J Kc) :=
  fun s c hs => by
    have hoff := runsOffA_of_chk hp wcRuns_chk
    have he : (_root_.Executable.labels exe).label "scc_rt_print" + Int64.ofNat (4 * 0) =
        (Body.wCall (_root_.Executable.labels exe).label J Kc).pc := ofNat4_zero _
    have hlen : A64.Print.b0.length = 6 := rfl
    have h : NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
        (Body.wCall (_root_.Executable.labels exe).label J Kc) A64.Print.b0 :=
      blkW_abX (rl := "scc_rt_print") hμ
        (fun s he hn => (Wk.printCode hp hend (c0 := c) (x29 := 0) (ra := 0)).e s he hn)
        Wk.b0_okW hR hal hlo hhi
        (fun j hj => pcOffA_add hoff (List.Mem.tail _ (List.Mem.head _)) (Nat.le_refl 0)
          (by rw [hlen] at hj; omega) he.symm)
        he (abOffHC_sound hlab wcC_pr)
        (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)
    exact Wk.NodeZA.toW0 h s c hs

end P3W

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcPro_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcPro_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wE_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wE_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wCall_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wCall_abX
