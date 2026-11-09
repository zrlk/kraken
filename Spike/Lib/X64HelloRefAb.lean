/-
**The refusal path's threads abort pieces at hello's level 2** (x86-64; the twin of
`Spike/Lib/A64HelloRefAb.lean`, the hello twins of wake's `X64WakeRefAg`, `X64WakeRefAbW`, `X64WakeRefAbSt`,
`X64WakeRefNoWr`): four of `refOblH_of`'s component paths, at any layout running hello.w at the canonical base
(`hp`, `hlo`, `hΛ`, `hlab`), in `TOblH`'s region `R.callee (-136 - 8) (-24) 16` (`callee144`):

- `refAgH`: `AgH`, `abAgree2bH` at `abPTH` (the return address `raT` is `.x27`'s, `raT_x27H`);
- `refAbWH`: `AbWH`, `TPathW.ofAbPT` at `abPTH`;
- `refAbStH`: `AbStH`, `tpathW_abH` at the second `scc_rt_thread_init` instance's facts (`instOk2bPH`) and
  `ph2bH`'s phase facts on the path (`abortPhTH`);
- `refNoWrH`: `NoWrH`, `tpathW_hNH` (wake's `tpathW_hN` at hello's `instOkH`).

- `hendH`, `site_outH`, `exit_offH`: the end pc, the take site below `scc_rt_abort` and off the exit call.
- `callee_ofPreH`: `TOblH`'s region under `PreH`.
- `abPT_x27H`: `AbPT` at `.x27` in any region holding the path.

No absolute address appears in a statement here.

## Differences from the AArch64 version

- The callee's region is `[-24, 16)` with no alignment (`callee_ofPreH` has three conclusions); the return
  address is `.Lwc_main.x5` (`abPT_x27H`, AArch64: `abPT_sp15H` at `.L22_wc_main.sp15`).
- `tpathW_hNH` has seventeen nodes (the stub's `leaq` is one node, the calls are `syscall`s), as wake's
  `X64WakeRefNoWr.tpathW_hN`.
-/
import Spike.Lib.X64HelloRefPre
import Spike.Lib.X64HelloRefPh
import Spike.Lib.X64HelloRefAbT
import Spike.Lib.X64HelloStart
import Spike.Lib.X64WakeRefNoWr

namespace Spike.Lib.X64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FragS Arena)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakeWf (NoWrC)
open Spike.Lib.X64.Flow (ofNat_zero')
open Scc.Cert.Rt.X64 (codeT_eq code_field)
open Scc.Sem.X64 (codeLabel)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)

include hp in
/-- **The end pc** of a layout running hello.w. -/
theorem hendH : L.endPc = Scc.Cert.Rt.X64.endOf L.exe SccCode.helloCells L.pfx := by
  show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]

include hp hlo hlab in
/-- **The take site below `scc_rt_abort`** (`abPTH`'s `hsite`). -/
theorem site_outH : ∀ a, (Spike.Lib.X64.PhRec.μ L).site .take = some a →
    a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a := by
  rw [Spike.Lib.X64.HelloPh.siteH hp hlo hlab]
  rintro a ⟨⟩
  obtain ⟨e1, -⟩ := Spike.Lib.X64.HelloPh.ab_labsH hlab
  rw [e1, hlab _ 4200314 (by rw [← codeT_eq]; decide +kernel)]
  left; decide

include hp hlo hlab in
/-- **The take site off the threads stub's exit call** (`tpathW_abH`'s `htk`). -/
theorem exit_offH : ∀ a, (Spike.Lib.X64.PhRec.μ L).site .take = some a →
    (L.lab Spike.Lib.X64.Abort.threads.exit).toBitVec.toNat ≠ a := by
  rw [Spike.Lib.X64.HelloPh.siteH hp hlo hlab]
  rintro a ⟨⟩
  show (L.lab "scc_rt_abort_threads_exit").toBitVec.toNat ≠ _
  rw [hlab _ 4203002 (by rw [← codeT_eq]; decide +kernel), hlab _ 4200314 (by rw [← codeT_eq]; decide +kernel)]
  decide

omit hp hlo hlab in
/-- **`TOblH`'s region under `PreH`**: `OK`, with offsets `[-24, 16]`. -/
theorem callee_ofPreH {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word} {R : Region} {cP : Ctl}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64} (h : PreH L lbl l ws R cP sl cA me) :
    (R.callee (-136 - 8) (-24) 16).OK ∧ (R.callee (-136 - 8) (-24) 16).lo ≤ -24 ∧
      16 ≤ (R.callee (-136 - 8) (-24) 16).hi := by
  obtain ⟨-, -, -, -, hR, -, hlo', hhi, -⟩ := h
  exact callee144 hR (by omega) hhi

include hp hlo hlab in
/-- **`AbPT` at `.x27`** in any region holding the path. -/
theorem abPT_x27H {μ : Marks} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (hμ : μ = Spike.Lib.X64.PhRec.μ L) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    Spike.Lib.X64.WakePh.AbPT L μ L.endPc R F c0 (L.lab ".Lwc_main.x5").toBitVec := by
  subst hμ
  have hlays : Scc.Cert.Rt.X64.Lays L.exe SccCode.helloCells L.pfx := hp ▸ L.lays
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  exact Spike.Lib.X64.HelloPh.abPTH hlab hR hlo' hhi (site_outH hp hlo hlab)
    (Scc.Cert.Rt.X64.Abort.code_disp hlays (hendH hp) hsd.2)
    (Scc.Cert.Rt.X64.Abort.code_stubs hlays (hendH hp) SccCode.hello_abort .threads)

variable (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word)

include hp hlo hlab in
/-- **`AgH`**: `ownGH` agrees with `own2bH` along the path (`abAgree2bH` at `abPTH`). -/
theorem refAgH : AgH L lbl l ws := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_ofPreH hpre
  have h := Spike.Lib.X64.HelloPh.abAgree2bH (a := Spike.Lib.X64.Rt.Reserve.ntA L.lab) hlab
    (abPT_x27H hp hlo hlab (F := fun m => DFrame R m0 m ∧ CKept R (-136 - 8) (-24) 16 m1 m ∧
      Abs R ⟨-136, [(.rbp, 0)]⟩ m1 σC) (c0 := c0) rfl hR' hlo' hhi')
  rw [raT_x27H hlab]
  exact ⟨h.de, h.dt1, h.dj1, h.dt2, h.dj2, h.dt3, h.dj3, h.dt4, h.dj4, h.dt5, h.dg5, h.se, h.sn1, h.sn2,
    h.ssvc, h.sn5, h.sex⟩

include hp hlo hlab in
/-- **`AbWH`**: the path's states in `scc_rt_abort`'s code (`TPathW.ofAbPT` at `abPTH`). -/
theorem refAbWH : AbWH L lbl l ws := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_ofPreH hpre
  rw [raT_x27H hlab]
  exact TPathW.ofAbPT (abPT_x27H hp hlo hlab rfl hR' hlo' hhi')

include hp hlo hlab in
/-- **`AbStH`**: the write abort's phase kept along the path (`tpathW_abH` at `instOk2bPH`, `abortPhTH`). -/
theorem refAbStH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) : AbStH L lbl l ws := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_ofPreH hpre
  exact Spike.Lib.X64.HelloWf.tpathW_abH
    (Spike.Lib.X64.HelloPh.instOk2bPH hp hlo (Spike.Lib.X64.Rt.Reserve.ntA L.lab) (rS := ⟨0, 0⟩)
      (Spike.Lib.X64.HelloPh.siteH hp hlo hlab))
    (hp ▸ SccCode.hello_abort) (Spike.Lib.X64.HelloPh.abortPhTH hΛ hlab) hlab hR' hlo' hhi' (exit_offH hp hlo hlab)

include hp hlo hlab in
/-- **No write to the arena or the counter** at every node of the threads abort path, at any layout running
hello.w (wake's `X64WakeRefNoWr.tpathW_hN` at hello's `instOkH`). -/
theorem tpathW_hNH {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    {ar : Arena} {p : CoreTerm.Prog} {L0 : Lbl} {ls0 : Lsize} {Ctx : FragS isa} {fs : List TermRun.Frame}
    (a : BitVec 64) (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    TPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := Spike.Lib.X64.HelloPh.instOkH hp hlo a (fun _ => False) (Spike.Lib.X64.HelloPh.siteH hp hlo hlab)
    (rS := ⟨0, 0⟩)
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  have hst := hsd.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hd0)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.d0_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht1)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t1_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj1)
      rfl Spike.Lib.X64.Abort.Disp.j1_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht2)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj2)
      rfl Spike.Lib.X64.Abort.Disp.j2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht3)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t3_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj3)
      rfl Spike.Lib.X64.Abort.Disp.j3_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht4)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t4_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hj4)
      rfl Spike.Lib.X64.Abort.Disp.j4_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact ht5)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.t5_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hg5)
      (ofNat_zero' _) Spike.Lib.X64.Abort.Disp.g5_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx0)
      (ofNat_zero' _) Spike.Lib.X64.Abort.x0_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.AllocG.nodeW_noWr_si hI (by rw [hp]; exact hn1) rfl
      (ofNat_zero' _).symm)
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx1)
      rfl Spike.Lib.X64.Abort.x1Threads_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.WakeWf.nodeW_noWr_svc
      (code_field L.lays rfl (by rw [hp]; exact hsysIn) rfl))
  · exact Spike.Lib.X64.WakeWf.blkW_noWrC (Spike.Lib.X64.AllocG.blkW_noWr hI (by rw [hp]; exact hx2)
      rfl Spike.Lib.X64.Abort.x2_ok hR (by omega) (by omega))
  · exact Spike.Lib.X64.WakeWf.nodeW_noWrC (Spike.Lib.X64.WakeWf.nodeW_noWr_svc
      (code_field L.lays rfl (by rw [hp]; exact hx) (ofNat_zero' _)))

include hp hlo hlab in
/-- **`NoWrH`**: no write to the arena or the counter along the path (`tpathW_hNH`). -/
theorem refNoWrH (ar : Arena) (lsize : Lsize) (Ctx : FragS isa) : NoWrH L lbl l ws ar lsize Ctx := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hlo', hhi'⟩ := callee_ofPreH hpre
  exact tpathW_hNH hp hlo hlab (Spike.Lib.X64.Rt.Reserve.ntA L.lab) hR' hlo' hhi'

end Spike.Lib.X64.HelloPh.RefO

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refAgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refAgH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refAbWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refAbWH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refAbStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refAbStH

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refNoWrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refNoWrH
