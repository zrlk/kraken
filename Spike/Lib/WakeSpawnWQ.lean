/-
**The spawn obligation's worker half with `hPC` discharged** (AArch64): `WakeSpawnW.spawn_workerPost` with its `PreChild`
premise (`hPC`) proved at wake's instance, at the owned-words map
`ownG L (ntA L.lab)` and a TCB request `q` with `Q2 q` (main's second
`scc_rt_alloc_tcb`: `tcb2Q g c0`, `WakeTcbArea.q2_mk`).

`hPC` is `WakeTcbArea.hPC_q2`: the TCB's words (`tcbArea_q2`, from the
layout facts `hpin2`, `hinit2`, the memory relation and `GhOK`, the latter
by `WakeWorkerR.ghOK_of_clone` from `ClonePre`'s `ValRep` of `c`), the
owned words at the clone's `svc` (`WcSp4.ownG_clone`: `scc_rt_nthreads` at
`1`, `scc_rt_stack_next` at `32768`), and `x3 = tcbOf L.lab q` from `X`.

Open (premises of `spawn_workerPostQ`): those of `spawn_workerPost` but
`hPC`; the instance facts `hprog`, `hlo`, `hpin2`, `hinit2` (decided at the
concrete layout); and `hXq`: every `X` state at the clone's `svc` with
`x3` the TCB (`WcSp4.wcNS`'s `X3 = t`, `t = tcbOf L.lab (tcb2Q g c0)` by
`Tcb2Call.tcb2Q_tcbOf`; the segment end).
-/
import Spike.Lib.WakeSpawnW
import Spike.Lib.WakeTcbArea
import Spike.Lib.A64WakeWcSp4
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeSpawnWQ

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.Handover
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.A64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.WakeInst (Gh wakeMs)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.WakeOkW (recW)
open Spike.Lib.A64.Flow (DFrame)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Wake.Child (kidC childR pfxM)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.WakePh (ownG)
open Spike.Lib.WakeTcbArea (Q2)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **The worker half of the spawn, `hPC` discharged**: as
`spawn_workerPost` at `own := ownG L (ntA L.lab)` and a `Q2` request `q`,
the `PreChild` premise replaced by `X`'s pc (the clone's `svc`) and `x3`. -/
theorem spawn_workerPostQ {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}
    {Λ0 : Scc.Sem.Layout} (hpl : PlaceW pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hwide : Scc.Cert.WideA64.ExeWide exe)
    /- the instance's facts (decided at the concrete layout) -/
    (hprog : o.prog = wakeProg) (hlo : (RuntimeLayout.ofPlaceW hpl i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hpl i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hpl i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hpl i), 8⟩ = 0)
    {q : TcbGG} (hq : Q2 q)
    {r0 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}
    (h : WakePreA.ClonePre pfxM (RuntimeLayout.ofPlaceW hpl i).Λ r0 (r1Of (RuntimeLayout.ofPlaceW hpl i).lab)
      X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    /- (the segment's end `wcNS`) the clone's `svc`, `x3` the TCB -/
    (hXq : ∀ st, X st → st.st.2 = WakePreA.cloneAt pfxM (RuntimeLayout.ofPlaceW hpl i).exe ∧
      (st.st.1.regs.getXReg .X3).toBitVec = tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q) :
    ∃ (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      ∀ {T S : Nat} {lsize : WeakMem.AllocLabel → Nat} {pT : Loc}
        {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
        (s1 : TermRun.TTh) (Ty : Ty) (w1 w2 : TermRun.Word),
        /- (`SpawnPre.inv1.mem`; `newLoc_in`) -/
        MemRelP (RuntimeLayout.ofPlaceW hpl i).Λ lbl lsize ts tm sm tp tq sp → 0 < lsize l → 0 < S →
        /- the spawned source thread at `kidC` with `c`'s word and main's id -/
        s1.term = wkTail → s1.env = [("a", Ty, [w1, w2])] → w1.val = .loc ⟨l, 0⟩ 0 → w2.val = mainTidW →
        /- main's permit word and the second TCB's `+ 24` word in the child's frame -/
        (∀ th : Thread isaLSE2, t.1.threads = #[th] →
          StOk (wakeMs hpl i (recW T S lbl lsize l pT w1))
              (DFrame (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
                (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)
                  (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64) 1#64 ∧
          (BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64).toNat % 4 = 0 ∧
          StOk (wakeMs hpl i (recW T S lbl lsize l pT w1))
              (DFrame (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
                (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)
                  (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat + 24#64) 1#64) →
        ∃ hg : GhOK (RuntimeLayout.ofPlaceW hpl i).Λ (recW T S lbl lsize l pT w1),
          ∀ th : Thread isaLSE2, t.1.threads = #[th] →
            (WakeWorkerR.wakeDR hpl i (GhOK (RuntimeLayout.ofPlaceW hpl i).Λ) exe endPc kp).Wi
              ⟨recW T S lbl lsize l pT w1, hg⟩
              (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st
              (Ctl.of s1) := by
  obtain ⟨th0, l, hs, hc, hk⟩ := WakeSpawnW.spawn_workerPost hpl i hp hend hwide h hX
  obtain ⟨-, th0', -, cA, -, l', -, hs', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hc', -, -,
    hvc, -⟩ := h
  have e0 : th0' = th0 := by rw [hs] at hs'; exact (List.singleton_inj.mp (congrArg Array.toList hs')).symm
  subst e0
  clear hs'
  have el : l' = l := by
    rw [hc] at hc'
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at hc'
    have := congrArg Promises.TVal.val hc'
    simp only [TermRun.cst, Promises.TVal.mk0] at this
    cases this; rfl
  subst el
  have hlab : ∀ l x, Scc.Cert.Link.A64.codeOf Spike.Lib.A64.WakePh.lo wakeProg l = some x →
      (RuntimeLayout.ofPlaceW hpl i).lab l = Int64.ofNat x := fun l x hx =>
    PlaceW.hlab_ofPlaceW hpl i l x (by rw [hlo, hprog]; exact hx)
  refine ⟨th0', l', hs, hc, fun {T S lsize pT ts tm sm tp tq sp} s1 Ty w1 w2 hm hin hS hterm henv hw1 hjw hSt => ?_⟩
  have hg : GhOK (RuntimeLayout.ofPlaceW hpl i).Λ (recW T S lbl lsize l' pT w1) :=
    WakeWorkerR.ghOK_of_clone hm (WakeQ.hwf_ofPlaceOK hpl i) hvc hw1 hin hS
  have hPC := WakeTcbArea.hPC_q2 hpl i hpin2 hinit2 (recW T S lbl lsize l' pT w1) hm hg hq
    (own := ownG (RuntimeLayout.ofPlaceW hpl i) (ntA (RuntimeLayout.ofPlaceW hpl i).lab)) (X := X)
    (fun st hx => by
      obtain ⟨hpc, h3⟩ := hXq st hx
      have hw := Spike.Lib.A64.WakePh.WcSp4.ownG_clone hlab (L := RuntimeLayout.ofPlaceW hpl i)
        (a := ntA (RuntimeLayout.ofPlaceW hpl i).lab) (s := st) (by unfold pcOf; rw [hpc]; rfl)
      refine ⟨h3, hw.2, ?_⟩
      rw [(RuntimeLayout.ofPlaceW hpl i).lab_next]; exact hw.1)
  exact hk s1 Ty w1 w2 hPC hm hin hS hterm henv hw1 hjw hSt

/-- info: 'Spike.Lib.WakeSpawnWQ.spawn_workerPostQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_workerPostQ

end Spike.Lib.WakeSpawnWQ
