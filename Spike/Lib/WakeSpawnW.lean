/-
**The spawn obligation's worker half at the instance** (AArch64): at main's clone (`ClonePre` at the instance's layout, `r1` the
second take's range), the record built there (`WakeOkW.recW`, `c`'s label
`l` from `ClonePre`) satisfies `GhOK` and the child after the handover is
in `WakeWorkerR.wakeDR`'s invariant at the spawned source thread's control
(`spawn_of`'s `hwork`, first conjunct; `WakeStart.post_startW`'s
`D.Wi w t1.st (Ctl.of s1)`). The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

Assembled from `WakeChildXI.childSeg_XI` (at `lbl' := g.lbl`,
`cSf := g.cS`; its `hflag` from `GhOK`), `WakeWorkerR.wkPR_of`,
`wakeDR_entry`, `WorkerSide.clonePre_childWide` and
`WakeWorkerR.ghOK_of_clone`; the argument words' `ValRep` are
`ClonePre`'s (the child's `cA`, `meW` main's `x9`, `x10`).

Open (premises of `spawn_workerPost`): `ClonePre`, `hX`, the executable
wide (`hwide`); `hPC` and the per-thread `StOk` facts (`hSt`: main's
permit word `meW + 16` at value 1, 4-aligned, the second TCB's `+ 24` at
value 1); the spawned source thread (`hterm`, `henv`, `hw1`, `hjw`: `spawnKid`'s
term and environment, the argument words bumped); the memory
relation `hm` (`SpawnPre.inv1.mem`), `hin`, `hS`.
-/
import Spike.Lib.WakeWorkerR
import Spike.Lib.WakeChildXI
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeSpawnW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.Handover
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.A64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.WakeInst (Gh wakeMs)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.WakeOkW (recW)
open Spike.Lib.A64.Flow (DFrame)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Wake.Child (kidC childR pfxM)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64Consumer (Own)

/-- **The worker half of the spawn**: `c`'s label `l` at the clone; for the
record `recW T S lbl lsize l pT w1` (`GhOK` by `ghOK_of_clone`), the child of
any thread of `t` is in `wakeDR`'s invariant at `Ctl.of s1`. -/
theorem spawn_workerPost {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}
    {Λ0 : Scc.Sem.Layout} (hpl : PlaceW pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hwide : Scc.Cert.WideA64.ExeWide exe)
    {r0 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}
    (h : WakePreA.ClonePre pfxM (RuntimeLayout.ofPlaceW hpl i).Λ r0 (r1Of (RuntimeLayout.ofPlaceW hpl i).lab)
      X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {}) :
    ∃ (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      ∀ {T S : Nat} {lsize : WeakMem.AllocLabel → Nat} {pT : Loc} {own : Own} {q : TcbGG}
        {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
        (s1 : TermRun.TTh) (Ty : Ty) (w1 w2 : TermRun.Word),
        /- main's runtime facts at the clone -/
        (∀ st, X st → PreChild (wakeMs hpl i (recW T S lbl lsize l pT w1)) own (RuntimeLayout.ofPlaceW hpl i).lab q st) →
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
  have h' := h
  obtain ⟨th, th0, -, cA, meW, l, hth, hs, -, -, -, -, -, -, h9, h10, -, -, -, -, -, -, -, -, -, -, hc, -, -,
    hvc, hvm⟩ := h'
  refine ⟨th0, l, hs, hc, fun {T S lsize pT own q ts tm sm tp tq sp} s1 Ty w1 w2 hPC hm hin hS hterm henv hw1 hjw hSt => ?_⟩
  have hg : GhOK (RuntimeLayout.ofPlaceW hpl i).Λ (recW T S lbl lsize l pT w1) :=
    WakeWorkerR.ghOK_of_clone hm (WakeQ.hwf_ofPlaceOK hpl i) hvc hw1 hin hS
  refine ⟨hg, fun th1 hth1 => ?_⟩
  have e1 : th1 = th := by rw [hth] at hth1; exact (List.singleton_inj.mp (congrArg Array.toList hth1)).symm
  subst e1
  -- the flag's word is shared (`GhOK`)
  have hflag : ∀ x, wordAddr (recW T S lbl lsize l pT w1).lbl (recW T S lbl lsize l pT w1).cS = some x →
      Consumer1.LocIn (RuntimeLayout.ofPlaceW hpl i).Λ.shared (wordLoc x) := by
    obtain ⟨b, hb, -, hT⟩ := hg.2.2.2.1
    intro x hx
    simp only [wordAddr, hb, Option.map_some, Option.some.injEq] at hx
    rw [← hx, ← hT]; exact hg.2.2.2.2
  obtain ⟨th', cA', meW', -, -, hth', h9', h10', -, hk⟩ :=
    WakeChildXI.childSeg_XI hpl i (recW T S lbl lsize l pT w1) hp hend (Λw := (RuntimeLayout.ofPlaceW hpl i).Λ)
      (lbl' := lbl) (cSf := ⟨l, 0⟩) h hX hPC hflag Ty
  have e2 : th' = th1 := by rw [hth] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
  subst e2
  have ecA : cA' = cA := h9'.symm.trans h9
  have emW : meW' = meW := h10'.symm.trans h10
  subst ecA emW
  obtain ⟨hS1, hS2, hS3⟩ := hSt th' hth
  rw [h10'] at hS1 hS2
  have hv1 : ValRep lbl w1.val cA' := by rw [hw1]; exact hvc
  have hv2 : ValRep lbl w2.val meW' := by rw [hjw]; exact hvm
  obtain ⟨hAt, hseg⟩ := hk w1 w2
  have hseg' := hseg hv1 ⟨_, hw1⟩ hv2 hS1 hS2 hS3 hw1 hv1 hv2
  have hC : Ctl.of s1 = kidC Ty w1 w2 := by
    unfold Ctl.of; rw [hterm, henv]; rfl
  obtain ⟨thw, hthw, hw⟩ := WorkerSide.clonePre_childWide h hX hwide
  have e3 : thw = th' := by rw [hth] at hthw; exact (List.singleton_inj.mp (congrArg Array.toList hthw)).symm
  subst e3
  rw [hC]
  exact WakeWorkerR.wakeDR_entry hpl i _ exe endPc kp ⟨recW T S lbl lsize l pT w1, hg⟩ _ _
    (WakeWorkerR.wkPR_of hpl i _ exe endPc kp hseg' hAt) (hw _ _ _)

/-- info: 'Spike.Lib.WakeSpawnW.spawn_workerPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_workerPost

end Spike.Lib.WakeSpawnW
