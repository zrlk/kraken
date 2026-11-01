/-
**`AbX` at `wc_worker`'s tail and at `scc_rt_unpark`** (row 5i-hab1, P3, AArch64; `A64HelloAbObl`'s recipe):
`WcObl.hZW`, `hZU`
at `X := AbX μ lab`, the twins of `Wk.tail_relH`, `unpk_relH`
(`A64HelloRelZ`).

Their `ret` blocks return to the ghost return address, which the write
abort's check needs at a label: `tail_abX` takes `hra` (the tail returns
to `scc_rt_thr_worker`'s `.sp0`), `unpk_abX` takes `hra` (`unpark`
returns to `wc_worker`'s `.sp6`).

- `tlRuns`, `upRuns` and their `_chk`s, `tlC_*`, `upC_*`: the decided
  checks.
- `tail_abX`, `unpk_abX`: P3's tail fields.
-/
import Spike.Lib.A64HelloAbOblW

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND ofNat4_succ ofNat4_zero)
open Spike.Lib.A64.Flow.Worker (NodeZA)
open Spike.Lib.A64WakeOff (pcOffA_add)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloProg)

/-! ## The decided checks -/

/-- **`wc_worker`'s tail's pcs**: from `.sp4` (five instructions) and
`.sp6` (four). -/
def tlRuns : List (Label × Nat × Nat) :=
  [(".L20_wc_worker.sp4", 0, 5), (".L20_wc_worker.sp6", 0, 4)]

theorem tlRuns_chk : runsNeChk helloProg tlRuns abPtsA = true := by decide +kernel

/-- **`scc_rt_unpark`'s pcs**: its entry block (five), from `.0_entry`
(ten), from `.1_wake` (seventeen), its `.2_done` block (four). -/
def upRuns : List (Label × Nat × Nat) :=
  [("scc_rt_unpark", 0, 5), (".L11_scc_rt_unpark.0_entry", 0, 10), (".L11_scc_rt_unpark.1_wake", 0, 17),
    (".L11_scc_rt_unpark.2_done", 0, 4)]

theorem upRuns_chk : runsNeChk helloProg upRuns abPtsA = true := by decide +kernel

theorem tlC_b0 : abOffHC ".L20_wc_worker.sp4" 0 ".L20_wc_worker.sp4" HelloTail.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem tlC_st : abSiHC ".L20_wc_worker.sp4" 2 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem tlC_b1 : abOffHC ".L20_wc_worker.sp4" 3 ".L20_wc_worker.sp4" HelloTail.b1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem tlC_b2 : abOffHC ".L20_wc_worker.sp4" 4 ".L20_wc_worker.sp4" HelloTail.b2 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem tlC_b3 : abOffHC ".L20_wc_worker.sp6" 0 (HThrTail.pfx0 ++ ".sp0") HelloTail.b3 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b0 : abOffHC "scc_rt_unpark" 0 "scc_rt_unpark" Unpark.b0 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b1 : abOffHC ".L11_scc_rt_unpark.0_entry" 0 ".L11_scc_rt_unpark.0_entry" Unpark.b1 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_swp : abSiHC ".L11_scc_rt_unpark.0_entry" 3 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b2 : abOffHC ".L11_scc_rt_unpark.0_entry" 4 ".L11_scc_rt_unpark.0_entry" Unpark.b2 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b3 : abOffHC ".L11_scc_rt_unpark.0_entry" 9 ".L11_scc_rt_unpark.0_entry" Unpark.b3 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b4 : abOffHC ".L11_scc_rt_unpark.1_wake" 0 ".L11_scc_rt_unpark.1_wake" Unpark.b4 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_svc : abSiHC ".L11_scc_rt_unpark.1_wake" 11 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b5 : abOffHC ".L11_scc_rt_unpark.1_wake" 12 ".L20_wc_worker.sp6" Unpark.b5 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

theorem upC_b6 : abOffHC ".L11_scc_rt_unpark.2_done" 0 ".L20_wc_worker.sp6" Unpark.b6 = true := by
  simp only [abOffHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-! ## P3: `wc_worker`'s tail, `scc_rt_unpark` -/

section P3U

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

set_option hygiene false in
/-- A covered `ret`-free block of `exe`'s at `lab l + 4 k` (`blkW_abX`):
its node, its code, its `okBlk`, its length, its run's membership, its
start, its check. -/
local macro "ab " nd:term:max cd:term:max ok:term:max len:term:max l:term:max k:term:max m:term:max
    hk:term:max c:term:max : tactic =>
  `(tactic| (
    have he : (_root_.Executable.labels exe).label $l + Int64.ofNat (4 * $k) = ($nd).pc := by
      simp only [HelloTail.N, HelloTail.pcBl, Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]
    exact blkW_abX (rl := $l) hμ $cd $ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff $m $hk (by have h' : j < $len := hj; omega) he.symm)
      he (abOffHC_sound hlab $c)
      (fun _ _ _ j hj r hr => (Spike.Lib.A64Consumer.noRet_false (by decide) j hj r hr).elim)))

/-- **`AbX` at `wc_worker`'s tail nodes** (`WcObl.hZW`): the return
address at `scc_rt_thr_worker`'s `.sp0` (`hra`). -/
theorem tail_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64}
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0"))
    (i : HelloTail.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i) (HelloTail.blkN i) := by
  have hc := Wk.tailCode hp hend (c0 := c0) (c1 := c1) (c2 := c2) (A := A) (B := B) (x29 := x29) (ra := ra)
    (tp := tp)
  have hoff := runsOffA_of_chk hp tlRuns_chk
  have m4 : (".L20_wc_worker.sp4", 0, 5) ∈ tlRuns := List.Mem.head _
  have m6 : (".L20_wc_worker.sp6", 0, 4) ∈ tlRuns := List.Mem.tail _ (List.Mem.head _)
  cases i
  · ab (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4) hc.sp4 HelloTail.b0_ok 2
      ".L20_wc_worker.sp4" 0 m4 (Nat.le_refl 0) tlC_b0
  · have he : (_root_.Executable.labels exe).label ".L20_wc_worker.sp4" + Int64.ofNat (4 * 2) =
        (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .st).pc := by
      simp only [HelloTail.N, ofNat4_succ, ofNat4_zero]
    have hq := pcOffA_add (k := 0) hoff m4 (Nat.zero_le 2) (by omega) he.symm
    rw [ofNat4_zero] at hq
    exact nodeZA_abX_cell hμ hc.st hq he (abSiHC_sound hlab tlC_st) (fun _ h => by cases h)
      fun _ hc hd => stlr_leaf hc hd
  · ab (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .n3) hc.n3 HelloTail.b1_ok 1
      ".L20_wc_worker.sp4" 3 m4 (Nat.zero_le 3) tlC_b1
  · ab (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .bl) hc.bl HelloTail.b2_ok 1
      ".L20_wc_worker.sp4" 4 m4 (Nat.zero_le 4) tlC_b2
  · exact Spike.Lib.A64.Flow.Worker.Wake.RelZW.nodeZA_nil
  · have he : (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" + Int64.ofNat (4 * 0) =
        (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6).pc := ofNat4_zero _
    exact blkW_abX hμ hc.sp6 HelloTail.b3_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff m6 (Nat.le_refl 0) (by have h' : j < 4 := hj; omega) he.symm)
      he (abOffHC_sound hlab tlC_b3)
      (Spike.Lib.A64Consumer.hret_of_run HelloTail.b3_ok fun σ c hJ => by
        obtain ⟨-, -, h8, -⟩ := hJ
        simp only [HelloTail.N, HelloTail.blkN]
        rw [HelloTail.b3_run]
        dsimp only
        rw [h8]; exact hra)

/-- **`AbX` at `scc_rt_unpark`'s nodes** (`WcObl.hZU`): the return address
at `wc_worker`'s `.sp6` (`hra`). -/
theorem unpk_abX {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c1 c2 : Ctl} {B x29 ra tp : BitVec 64}
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6") (i : Unpark.PN) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c []) exe endPc R F
      (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp i) (Unpark.blkN i) := by
  have hc := Labels.unpkCode hp hend (c0 := c1) (c1 := c2) (B := B) (x29 := x29) (ra := ra) (tp := tp)
  have hoff := runsOffA_of_chk hp upRuns_chk
  have m0 : ("scc_rt_unpark", 0, 5) ∈ upRuns := List.Mem.head _
  have m1 : (".L11_scc_rt_unpark.0_entry", 0, 10) ∈ upRuns := List.Mem.tail _ (List.Mem.head _)
  have m2 : (".L11_scc_rt_unpark.1_wake", 0, 17) ∈ upRuns :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have m3 : (".L11_scc_rt_unpark.2_done", 0, 4) ∈ upRuns :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  cases i
  · ab (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .e) hc.e Unpark.b0_ok 5
      "scc_rt_unpark" 0 m0 (Nat.le_refl 0) upC_b0
  · ab (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .n1) hc.n1 Unpark.b1_ok 3
      ".L11_scc_rt_unpark.0_entry" 0 m1 (Nat.le_refl 0) upC_b1
  · have he : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" + Int64.ofNat (4 * 3) =
        (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .swp).pc := by
      simp only [Unpark.N, ofNat4_succ, ofNat4_zero]
    have hq := pcOffA_add (k := 0) hoff m1 (Nat.zero_le 3) (by omega) he.symm
    rw [ofNat4_zero] at hq
    exact nodeZA_abX_cell hμ hc.swp hq he (abSiHC_sound hlab upC_swp) (fun _ h => by cases h)
      fun _ hc hd => swp_leaf hc hd
  · ab (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .n2) hc.n2 Unpark.b2_ok 5
      ".L11_scc_rt_unpark.0_entry" 4 m1 (Nat.zero_le 4) upC_b2
  · ab (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .n3) hc.n3 Unpark.b3_ok 1
      ".L11_scc_rt_unpark.0_entry" 9 m1 (Nat.zero_le 9) upC_b3
  · ab (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .wake) hc.wake Unpark.b4_ok 11
      ".L11_scc_rt_unpark.1_wake" 0 m2 (Nat.le_refl 0) upC_b4
  · have he : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.1_wake" + Int64.ofNat (4 * 11) =
        (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .svc).pc := by
      simp only [Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]
    have hq := pcOffA_add (k := 0) hoff m2 (Nat.zero_le 11) (by omega) he.symm
    rw [ofNat4_zero] at hq
    exact nodeZA_abX_svc hμ hc.svc hq he (abSiHC_sound hlab upC_svc)
  · have he : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.1_wake" + Int64.ofNat (4 * 12) =
        (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .n5).pc := by
      simp only [Unpark.N, Unpark.pcSvc, ofNat4_succ, ofNat4_zero]
    exact blkW_abX hμ hc.n5 Unpark.b5_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff m2 (Nat.zero_le 12) (by have h' : j < 5 := hj; omega) he.symm)
      he (abOffHC_sound hlab upC_b5)
      (Spike.Lib.A64Consumer.hret_of_run Unpark.b5_ok fun σ c hJ => by
        obtain ⟨-, -, h8, -⟩ := hJ
        simp only [Unpark.N, Unpark.blkN]
        rw [Unpark.b5_run]
        dsimp only
        rw [h8]; exact hra)
  · have he : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.2_done" + Int64.ofNat (4 * 0) =
        (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp .done).pc := ofNat4_zero _
    exact blkW_abX hμ hc.done Unpark.b6_ok hR hal hlo hhi
      (fun j hj => pcOffA_add hoff m3 (Nat.le_refl 0) (by have h' : j < 4 := hj; omega) he.symm)
      he (abOffHC_sound hlab upC_b6)
      (Spike.Lib.A64Consumer.hret_of_run Unpark.b6_ok fun σ c hJ => by
        obtain ⟨-, -, h8, -⟩ := hJ
        simp only [Unpark.N, Unpark.blkN]
        rw [Unpark.b6_run]
        dsimp only
        rw [h8]; exact hra)

end P3U

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.tail_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.tail_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.unpk_abX' depends on axioms: [propext, Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.unpk_abX
