/-
**`RefNoWr`: no write to the arena or the counter along the threads abort
path** (AArch64, wake.w): the shape of `WakePh.hpathW_hN` on `TPathW`'s
eighteen nodes — the dispatcher's and the stub's blocks silent
(`AllocG.blkW_noWr`), the `adrp`/`add` nodes (`AllocG.nodeW_noWr_si`), the
`write` and exit calls (`WakeWf.nodeW_noWr_svc`) — in `TObl`'s region
(`callee_of_pre`).

- `tpathW_hN`: at any layout running wake.w.
- `refNoWr`: the piece.
-/
import Spike.Lib.A64WakeRefAbW
import Spike.Lib.A64WakeHAbStub

namespace Spike.Lib.WakeRefNoWr

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)
open Spike.Lib.A64.WakeWf (NoWrC blkW_noWrC nodeW_noWrC nodeW_noWr_svc)
open Spike.Lib.A64.AllocG (blkW_noWr nodeW_noWr_si)
open Spike.Lib.WakeRefTP (TPathW)
open Spike.Lib.WakeRefStub (RefNoWr)
open Spike.Lib.WakeRefAbW (callee_of_pre)

set_option linter.unusedSimpArgs false

/-- **No write to the arena or the counter** at every node of the threads
abort path, at any layout running wake.w. -/
theorem tpathW_hN {L : RuntimeLayout} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    {ar : Arena} {p : CoreTerm.Prog} {L0 : Spike.Lib.A64Consumer.Lbl} {ls0 : Spike.Lib.A64Consumer.Lsize}
    {Ctx : FragS isaLSE2} {fs : List TermRun.Frame} (a : BitVec 64) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    TPathW (NoWrC ar p L0 ls0 Ctx fs) (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := Spike.Lib.A64.WakePh.instOkW hp hlo a (fun _ => False)
    (Spike.Lib.A64.WakePh.siteW hp hlo hlab) (rS := ⟨0, 0⟩)
  have hsd := Spike.Lib.A64.WakePh.abortIn_wakeR
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

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`RefNoWr`**: `NoWrW` at every node of the threads abort path. -/
theorem refNoWr (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat) : RefNoWr hp i ls0 l b n := by
  intro R m0 cP cA mT m1 σC c0 hpre _
  obtain ⟨hR', hal'⟩ := callee_of_pre hp i hpre
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have e : (Ly).endPc = Spike.Lib.WakeSpawnR.endR hp i := by
    show Scc.Cert.Rt.A64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  rw [← e]
  exact tpathW_hN hprog (Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0)
    (Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee])

end Spike.Lib.WakeRefNoWr

/-- info: 'Spike.Lib.WakeRefNoWr.refNoWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefNoWr.refNoWr
