/-
**main's invariant after its `clone` at hello's listing and source**
(AArch64; the twin of `A64WakeMainClosedWS`): `A64HelloMainClosedW.main_closed_helloW`
with its source facts discharged at `helloSrc` (its listing facts, the runs
and the flag check, are decided on `helloProg` inside).

- the source path from main's control `cP` at `WakeM0.mTail` (past its
  spawn, `c` bound to the flag's word `w`, `hlP`): `hrun` by
  `HelloMainSrc.main_src_runH` to `c0 := WakeMainSrc.waitC w` (at
  `WakeM0.wlBody`, `x := "d"`, `e := WakeM0.wlIf`, `cv := "c"`), `hterm`,
  `hev`, `hl`, `hwb` by `rfl`/`waitC_ev`, and `hcP`, `hcPf`, `hfvP`, `hc0`,
  `hfv0`, `hE`, `hfvE`, `hxc` by `HelloMainSrc.main_src_wakeH`'s
  computations; `htag` from `hin`.

`main_closed_wsH` keeps the rest of `main_closed_helloW`'s hypotheses (the
clone's `h`/`hat`/`hRb`, the frames, `hS`, `htls`, `hexit`, `hwide`, `hmA`,
`hmP`, `hmE`), with `p := helloSrc`, `c0`, `x`, `e`, `ty` instantiated.
-/
import Spike.Lib.A64HelloMainClosedW
import Spike.Lib.HelloMainSrc

namespace Spike.Lib.A64HelloMainClosedWS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Spike.Lib.HelloPreA (cloneAtH ClonePreH)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainInv (mainInvP mainWRH)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (mTail wlBody wlIf)
open Spike.Lib.A64.HelloLabels (pfx)

/-- **main's invariant after its `clone` in hello's program, from main's
control at `mTail`**: `main_closed_helloW` at `helloSrc` with the source
facts computed at `c0 := waitC w` (see the module doc). -/
theorem main_closed_wsH {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat}
    {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 144)
    (hRlo : R.lo = -144) (hRhi : R.hi = 48) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    {w : TermRun.Word} {tyP : Ty}
    /- main past its spawn: at `mTail`, `c` bound to the flag's word `w` -/
    (htP : cP.term = mTail) (hlP : TermRun.lookupE cP.env "c" = some (tyP, [w]))
    (hval : ValRep lbl w.val A.toNat) (hloc : LocRep lbl w.val A.toNat 0)
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64} (g0 : γ)
    (hRg : Rg g0 = R) (hfp : fp g0 = x29)
    (hFg : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → Fg g0 m)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hRo : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -144) (hhi : ∀ g, 48 ≤ (Rg g).hi)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0)
    (htls : ∀ g,
      SegW (mainWRH (_root_.Executable.labels exe).label exe Λ' lbl lsize) (fun _ _ => False) helloSrc lbl ms
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx (waitC w) "d" wlIf (.ptr .pub .int)
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx (waitC w) "d" wlIf (.ptr .pub .int)
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1)
    (hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit helloSrc ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ') wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') cP)
    (hmE : ∀ c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
      (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') c) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      mainInvP helloSrc lbl ms (mainWRH (_root_.Executable.labels exe).label exe Λ' lbl lsize)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  obtain ⟨-, -, -, -, -, -, -, hcPf, hcP, hfvP, -, -, -, hE, hfvE, hxc⟩ :=
    Spike.Lib.HelloMainSrc.main_src_wakeH (lbl := lbl) (A := A) (cP := cP) htP hlP hval (hin.imp fun _ h => h.1)
  have hc0 : (waitC w).term ≠ WakeMLive.wlRet := by
    simp [waitC, Spike.Lib.WakeMainSrc.waitBody, WakeMLive.wlRet]
  have hfv0 : ∀ y ∈ Scc.Sem.exprFv (waitC w).term, y = "c" := by
    simp [waitC, Spike.Lib.WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]
  exact Spike.Lib.A64HelloMainClosedW.main_closed_helloW hp hend h hat hRb hRlo hRhi hR htop hr0 hrm g0 hRg hfp
    hFg hF hRo hal hlo hhi (Spike.Lib.HelloMainSrc.main_src_runH htP hlP) rfl (Spike.Lib.WakeMainSrc.waitC_ev w)
    hval (hin.imp fun _ h => h.1) hdm hK hS htp4 htls hra hexit hwide hcP hfvP hlP hc0 hfv0
    (by simp [waitC, TermRun.lookupE]) hloc hE hfvE hxc hmA hmP hmE rfl hin hcPf

end Spike.Lib.A64HelloMainClosedWS

/-- info: 'Spike.Lib.A64HelloMainClosedWS.main_closed_wsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainClosedWS.main_closed_wsH
