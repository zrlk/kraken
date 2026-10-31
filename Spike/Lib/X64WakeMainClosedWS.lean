/-
**main's invariant after its `clone` at wake's cells and source**
(x86-64): the x64 twin of `Spike/Lib/A64WakeMainClosedWS.lean`,
`X64WakeInst.main_closed_wakeWR` with its source facts discharged.

- the source path from main's control `cP` at `X64WakeM0.mTail` (past its
  spawn, `c` bound to the flag's word `w`, `hlP`): `hrun` by
  `X64WakeMainSrc.main_src_run` to `c0 := X64WakeMainSrc.waitC w` (at
  `X64WakeM0.wlBody`, `x := "d"`, `e := X64WakeM0.wlIf`, `cv := "c"`),
  `hterm`, `hev`, `hl`, `hwb` by `rfl`/`waitC_ev`, and `hcP`, `hcPf`,
  `hfvP`, `hc0`, `hfv0`, `hE`, `hfvE`, `hxc` by `X64WakeMainSrcW`'s
  computations; `htag` from `hin`.

`main_closed_ws` keeps the rest of `main_closed_wakeWR`'s hypotheses (the
clone's `h`/`hat`/`hRb`, the region and frames, `hlim`, `hT`, `hown`, `hS`,
`hpcode`, `hpentry`, `hexit`, `hwide`, `hmA`, `hmP`, `hmE`, `hms`), with
`c0`, `x`, `e`, `ty` instantiated.

**Deviations from A64.** No listing premise is discharged here: the x64
`seg_mainPostWR` already takes the runs off the exits (`wake_*Runs_offA`)
and the flag's runs (`wake_flagRuns`) from `hp`. One region `R` (no ghost
family `Rg`/`Fg`/`g0`, no `htls`, no `hal`), as in `X64WakeMainClosedW`;
`hat` is on main's post-spawn region `[-80, 40)` (`X64WakeMainHRD.MainSeg.hat`
widens the clone's `At` to it). The conclusion is `mainInv`'s body (no x64
`mainInv` yet).
-/
import Spike.Lib.X64WakeInstR
import Spike.Lib.X64WakeMainSrcW

namespace Spike.Lib.X64WakeMainClosedWS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.WakePh.WcClone (oW)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64.WakePh.MainPost (mainX2)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64WakeInst (mainWR RtOff)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (mTail wlBody wlIf)

/-- **main's invariant after its `clone` in wake's cells, from main's
control at `mTail`**: `main_closed_wakeWR` with the source facts computed
at `c0 := waitC w` (see the module doc). -/
theorem main_closed_ws {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isa}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    {R : Region} {F F0 : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64)
    (hRlo : R.lo = -80) (hRhi : R.hi = 40) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    {w : TermRun.Word} {tyP : Ty}
    /- main past its spawn: at `mTail`, `c` bound to the flag's word `w` -/
    (htP : cP.term = mTail) (hlP : TermRun.lookupE cP.env "c" = some (tyP, [w]))
    (hval : ValRep lbl w.val A.toNat) (hloc : LocRep lbl w.val A.toNat 0)
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hFR : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hF : FStable R F)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    {c0' : Ctl} {rbp0' ra' tp' : BitVec 64} (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hfp : fp = R.addr 48)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hexit : ∀ s c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
      At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s →
        MainExit Spike.Lib.X64WakeT1.wakeSrc ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ') wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') cP)
    (hmE : ∀ c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
      Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') c)
    (hms : RtOff lbl lsize ms) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧ ∃ inv : Frag isa,
      (∀ s c, inv s c → OutL Spike.Lib.X64WakeT1.wakeSrc lbl ms inv s c) ∧
      (∀ s c, inv s c → mainWR (_root_.Executable.labels exe).label exe Λ' lbl lsize s c) ∧
      inv (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hfE := Spike.Lib.X64WakeMainSrcW.main_src_wake (lbl := lbl) (A := A) (cP := cP) htP hlP hval
    (hin.imp fun _ h => h.1)
  obtain ⟨-, -, -, -, -, -, -, hcPf, hcP, hfvP, -, -, -, hE, hfvE, hxc⟩ := hfE
  have hc0 : (waitC w).term ≠ WakeMLive.wlRet := by
    simp [waitC, Spike.Lib.X64WakeMainSrc.waitBody, WakeMLive.wlRet]
  have hfv0 : ∀ y ∈ Scc.Sem.exprFv (waitC w).term, y = "c" := by
    simp [waitC, Spike.Lib.X64WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars,
      Scc.Sem.opAts]
  exact Spike.Lib.X64WakeInst.main_closed_wakeWR hp hend h hat hRb hRlo hRhi hR htop hr0 hrm hFR hF
    (Spike.Lib.X64WakeMainSrc.main_src_run htP hlP) hlim rfl (Spike.Lib.X64WakeMainSrc.waitC_ev w) hval
    (hin.imp fun _ h => h.1) hdm hK hT hown hS htp4 hpcode hpentry hfp hra hexit hwide hcP hfvP hlP hc0 hfv0
    (show TermRun.lookupE (waitC w).env "c" = some (.ptr .pub .int, [w]) by simp [waitC, TermRun.lookupE])
    hloc hE hfvE hxc hmA hmP hmE rfl hin hcPf hms

end Spike.Lib.X64WakeMainClosedWS

/-- info: 'Spike.Lib.X64WakeMainClosedWS.main_closed_ws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainClosedWS.main_closed_ws
