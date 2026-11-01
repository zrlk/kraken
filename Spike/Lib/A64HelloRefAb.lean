/-
**The refusal path's threads abort pieces at hello's level 2** (AArch64; piece R3;
the hello twins of wake's `A64WakeRefAg`, `A64WakeRefAbW`, `A64WakeRefAbSt`, `A64WakeRefNoWr`): four of
`refOblH_of`'s component paths, at any layout running hello.w at the canonical base (`hp`, `hlo`, `hΛ`, `hlab`), in
`TOblH`'s region `R.callee (-144) (-48) 0` (`callee144`):

- `refAgH`: `AgH`, `abAgree2bH` at `abPTH` (the return address `raT` is `.sp15`'s, `raT_sp15H`);
- `refAbWH`: `AbWH`, `TPathW.ofAbPT` at `abPTH`;
- `refAbStH`: `AbStH`, `tpathW_abH` at the second `scc_rt_thread_init` instance's facts (`instOk2bPH`) and
  `ph2bH`'s phase facts on the path (`abortPhTH`);
- `refNoWrH`: `NoWrH`, `tpathW_hNH` (wake's `tpathW_hN` at hello's `instOkH`).

- `hendH`, `site_outH`, `exit_offH`: the end pc, the take site below `scc_rt_abort` and off the exit call.
- `callee_ofPreH`: `TOblH`'s region under `PreH`.

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefPre
import Spike.Lib.A64HelloRefPh
import Spike.Lib.A64HelloRefAbT
import Spike.Lib.A64HelloStart
import Spike.Lib.A64WakeRefNoWr

namespace Spike.Lib.A64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS Arena)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)
open Spike.Lib.A64.WakeWf (NoWrC blkW_noWrC nodeW_noWrC nodeW_noWr_svc)
open Spike.Lib.A64.AllocG (blkW_noWr nodeW_noWr_si)
open Scc.Cert.Rt.A64 (codeT_eq)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)

include hp in
/-- **The end pc** of a layout running hello.w. -/
theorem hendH : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.helloProg L.pfx := by
  show Scc.Cert.Rt.A64.endOf L.exe L.prog L.pfx = _; rw [hp]

include hp hlo hlab in
/-- **The take site below `scc_rt_abort`** (`abPTH`'s `hsite`). -/
theorem site_outH : ∀ a, (Spike.Lib.A64.PhRec.μ L).site .take = some a →
    a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a := by
  rw [siteH hp hlo hlab]
  rintro a ⟨⟩
  obtain ⟨e1, -⟩ := ab_labsH hlab
  rw [e1, hlab _ 2165976 (by rw [← codeT_eq]; decide +kernel)]
  left; decide

include hp hlo hlab in
/-- **The take site off the threads stub's exit call** (`tpathW_abH`'s `htk`). -/
theorem exit_offH : ∀ a, (Spike.Lib.A64.PhRec.μ L).site .take = some a →
    (L.lab Spike.Lib.A64.Abort.threads.exit).toBitVec.toNat ≠ a := by
  rw [siteH hp hlo hlab]
  rintro a ⟨⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e16⟩ := ab_labsH hlab
  show (L.lab "scc_rt_abort_threads_exit").toBitVec.toNat ≠ _
  rw [e16, hlab _ 2165976 (by rw [← codeT_eq]; decide +kernel)]
  decide

omit hp hlo hlab in
/-- **`TOblH`'s region under `PreH`**: `OK`, 16-aligned, with offsets `[-48, 0]`. -/
theorem callee_ofPreH {lbl : Lbl} {l : WeakMem.AllocLabel} {ws : List TermRun.Word} {R : Region} {cP : Ctl}
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {cA me : BitVec 64} (h : PreH L lbl l ws R cP sl cA me) :
    (R.callee (-144) (-48) 0).OK ∧ (R.callee (-144) (-48) 0).base.toNat % 16 = 0 ∧
      (R.callee (-144) (-48) 0).lo ≤ -48 ∧ 0 ≤ (R.callee (-144) (-48) 0).hi := by
  obtain ⟨-, -, -, -, hR, hal, hlo', hhi, -⟩ := h
  exact callee144 hR hal (by omega) hhi

include hp hlo hlab in
/-- **`AbPT` at `.sp15`** in any region holding the path. -/
theorem abPT_sp15H {μ : Marks} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (hμ : μ = Spike.Lib.A64.PhRec.μ L)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    Spike.Lib.A64.WakePh.AbPT L μ L.endPc R F c0 (L.lab ".L22_wc_main.sp15").toBitVec := by
  subst hμ
  have hlays : Scc.Cert.Rt.A64.Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  exact abPTH hlab hR hal hlo' hhi (site_outH hp hlo hlab)
    (Scc.Cert.Rt.A64.Abort.code_disp hlays (hendH hp) hsd.2)
    (Scc.Cert.Rt.A64.Abort.code_stubs hlays (hendH hp) SccCode.hello_abort .threads)

variable (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word)

include hp hlo hlab in
/-- **`AgH`**: `ownGH` agrees with `own2bH` along the path (`abAgree2bH` at `abPTH`). -/
theorem refAgH : AgH L lbl l ws := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hal', hlo', hhi'⟩ := callee_ofPreH hpre
  have h := abAgree2bH (a := Spike.Lib.A64.Rt.Reserve.ntA L.lab) hlab
    (abPT_sp15H hp hlo hlab (F := fun m => Spike.Lib.A64.Flow.DFrame R m0 m ∧
      Spike.Lib.A64.Flow.CKept R (-144) (-48) 0 m1 m ∧ Spike.Lib.A64.Flow.Abs R
        Spike.Lib.A64.Flow.Worker.Hello.Parent.oP m1 σC) (c0 := c0) rfl hR' hal' hlo' hhi')
  rw [raT_sp15H hlab]
  exact ⟨h.de, h.dt1, h.dj1, h.dt2, h.dj2, h.dt3, h.dj3, h.dt4, h.dj4, h.dt5, h.dg5, h.se, h.sn1, h.sn1b, h.sn2,
    h.ssvc, h.sn5, h.sex⟩

include hp hlo hlab in
/-- **`AbWH`**: the path's states in `scc_rt_abort`'s code (`TPathW.ofAbPT` at `abPTH`). -/
theorem refAbWH : AbWH L lbl l ws := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hal', hlo', hhi'⟩ := callee_ofPreH hpre
  rw [raT_sp15H hlab]
  exact TPathW.ofAbPT (abPT_sp15H hp hlo hlab rfl hR' hal' hlo' hhi')

include hp hlo hlab in
/-- **`AbStH`**: the write abort's phase kept along the path (`tpathW_abH` at `instOk2bPH`, `abortPhTH`). -/
theorem refAbStH (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) : AbStH L lbl l ws := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hal', hlo', hhi'⟩ := callee_ofPreH hpre
  exact Spike.Lib.A64.HelloWf.tpathW_abH
    (instOk2bPH hp hlo (Spike.Lib.A64.Rt.Reserve.ntA L.lab) (rS := ⟨0, 0⟩) (siteH hp hlo hlab))
    (hp ▸ SccCode.hello_abort) (abortPhTH hΛ hlab) hlab hR' hal' hlo' hhi' (exit_offH hp hlo hlab)

include hp hlo hlab in
/-- **No write to the arena or the counter** at every node of the threads abort path, at any layout running
hello.w (wake's `WakeRefNoWr.tpathW_hN` at hello's `instOkH`). -/
theorem tpathW_hNH {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    {ar : Arena} {p : CoreTerm.Prog} {L0 : Lbl} {ls0 : Lsize} {Ctx : FragS isaLSE2} {fs : List TermRun.Frame}
    (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    TPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkH hp hlo a (fun _ => False) (siteH hp hlo hlab) (rS := ⟨0, 0⟩)
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hcode := Scc.Cert.Rt.A64.Abort.code_stub (c0 := c0) L.lays rfl (hp ▸ hsd.1.2)
  have hst := hsd.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, -, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hd0) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.d0_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ ht1) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.t1_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hj1) (by simp only [DN.nd5, add4, add0])
      Spike.Lib.A64.Abort.Disp.j1_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ ht2) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.t2_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hj2) (by simp only [DN.nd5, add4, add0])
      Spike.Lib.A64.Abort.Disp.j2_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ ht3) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.t3_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hj3) (by simp only [DN.nd5, add4, add0])
      Spike.Lib.A64.Abort.Disp.j3_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ ht4) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.t4_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hj4) (by simp only [DN.nd5, add4, add0])
      Spike.Lib.A64.Abort.Disp.j4_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ ht5) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.t5_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hg5) (by simp only [DN.nd5, add0])
      Spike.Lib.A64.Abort.Disp.g5_ok hR hal (by omega) (by omega))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hb0) (by simp only [NT, add0])
      Spike.Lib.A64.Abort.b0_ok hR hal (by omega) (by omega))
  · exact nodeW_noWrC (nodeW_noWr_si (si := .adrp .X9 Spike.Lib.A64.Abort.threads.msg) hI (hp ▸ hn1) rfl
      (by simp only [NT, add0]))
  · exact nodeW_noWrC (nodeW_noWr_si (si := .addLo12 .X9 .X9 Spike.Lib.A64.Abort.threads.msg) hI (hp ▸ hn1b)
      rfl (by simp only [NT, add4, add0]))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hb1) (by simp only [NT, add4, add0])
      Spike.Lib.A64.Abort.b1Threads_ok hR hal (by omega) (by omega))
  · exact nodeW_noWrC (nodeW_noWr_svc (Scc.Cert.Rt.A64.Print.code_field L.lays rfl (hp ▸ hsvcIn)
      (by simp only [NT, Spike.Lib.A64.Abort.pcSvc, add4, add0])))
  · exact blkW_noWrC (blkW_noWr hI (hp ▸ hb2) (by simp only [NT, Spike.Lib.A64.Abort.pcSvc, add4, add0])
      Spike.Lib.A64.Abort.b2_ok hR hal (by omega) (by omega))
  · exact nodeW_noWrC (nodeW_noWr_svc fun s hs hn => by
      rw [Spike.Lib.A64.Abort.NT_pc]; exact hcode.ex s hs hn)

include hp hlo hlab in
/-- **`NoWrH`**: no write to the arena or the counter along the path (`tpathW_hNH`). -/
theorem refNoWrH (ar : Arena) (lsize : Lsize) (Ctx : FragS isaLSE2) : NoWrH L lbl l ws ar lsize Ctx := by
  intro R m0 cP sl cA me m1 σC c0 hpre _
  obtain ⟨hR', hal', hlo', hhi'⟩ := callee_ofPreH hpre
  exact tpathW_hNH hp hlo hlab (Spike.Lib.A64.Rt.Reserve.ntA L.lab) hR' hal' hlo' hhi'

end Spike.Lib.A64.HelloPh.RefO

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refAgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refAgH

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refAbWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refAbWH

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refAbStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refAbStH

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refNoWrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refNoWrH
