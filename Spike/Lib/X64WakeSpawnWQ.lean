/-
**The spawn's worker half at wake's instance on x86-64** (in the manner of
`Spike/Lib/WakeSpawnWQ.lean`): `X64WakeSpawnW.spawn_workerPost` with its
`PreChild` premise (`hPC`) proved at wake's instance, at main's owned-words
map `ownGXW L (ntA L.lab)` and a TCB request `q` with `Q2 q` (main's second
`scc_rt_alloc_tcb`: `tcb2Q g c0`, `X64WakeTcbArea.q2_mk`).

`hPC` is `X64WakeTcbArea.hPC_q2`: the TCB's words (`tcbArea_q2`, from the
layout facts `hpin2`, `hinit2`, the memory relation and `GhOK`, the latter
by `X64WakeWorkerR.ghOK_of_clone` from `ClonePre`'s `ValRep` of `c`), the
owned words at the clone's `syscall` (`WcSp4.ownG_clone`:
`scc_rt_nthreads` at `1`, `scc_rt_stack_next` at `32768`, in `ownG`'s part
of `ownGXW`), and `%r8 = tcbOf L.lab q` from `X`.

**Unlike AArch64** (forced by the x64 shape):
- main's owned words are `ownGXW` (`ownG` with main's and the worker's TCB
  words appended), not `ownG`; the two counters are in its `ownG` prefix.
- The TCB register is `%r8` (the `clone` stub's `tls`), not `x3`.
- `spawn_workerPost` discharges the child's stores itself, so this lemma
  carries no `hSt`; it carries `spawn_workerPost`'s `hcm` instead.

Open (premises of `spawn_workerPostQ`): those of `spawn_workerPost` but
`hPC` and `Q2 q` (here the instance's `hq`); the instance facts `hprog`,
`hlo`, `hpin2`, `hinit2` (decided at the concrete layout); and `hXq`: every
`X` state at the clone's `syscall` with `%r8` the TCB (the segment's end,
`t = tcbOf L.lab (tcb2Q g c0)` by `Tcb2Call.tcb2Q_tcbOf`).
-/
import Spike.Lib.X64WakeSpawnW
import Spike.Lib.X64WakeTcbArea
import Spike.Lib.X64WakeWcSp4
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeSpawnWQ

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakeW1 Spike.Lib.Handover
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64WakeInst (Gh wakeMs)
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64WakeOkW (recW)
open Spike.Lib.X64.WakePh (tcb2 tcbM ownGXW)
open Spike.Lib.X64WakeTcbArea (Q2)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (wakeCells)

/-- **The worker half of the spawn, `hPC` discharged**: as
`spawn_workerPost` at `own := ownGXW L (ntA L.lab)` and a `Q2` request `q`,
the `PreChild` premise replaced by `X`'s pc (the clone's `syscall`) and
`%r8`. -/
theorem spawn_workerPostQ {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ0 : Scc.Sem.Layout} (hpl : PlaceWX pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hA13 : Scc.Cert.Spawn.X64.a13data (RuntimeLayout.ofPlaceWX hpl i).Λ o.prog o.secs = true)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe wakeCells kp) (hend : endPc = endOf exe wakeCells kp)
    (hwide : Scc.Cert.WideX64.ExeWide exe)
    /- the instance's facts (decided at the concrete layout) -/
    (hprog : o.prog = wakeCells) (hlo : (RuntimeLayout.ofPlaceWX hpl i).Λ.code.lo = Spike.Lib.X64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceWX hpl i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceWX hpl i).Λ.pinned.lo + (RuntimeLayout.ofPlaceWX hpl i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (RuntimeLayout.ofPlaceWX hpl i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (RuntimeLayout.ofPlaceWX hpl i), 8⟩ = 0)
    {q : TcbGG} (hq : Q2 q)
    {r0 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}
    (h : X64WakePreA.ClonePre (RuntimeLayout.ofPlaceWX hpl i).Λ r0 (r1Of (RuntimeLayout.ofPlaceWX hpl i).lab)
      X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    /- (the segment's end) the clone's `syscall`, `%r8` the TCB -/
    (hXq : ∀ st, X st → st.st.2 = X64WakePreA.cloneAt (RuntimeLayout.ofPlaceWX hpl i).exe ∧
      st.st.1.regs.get64 .r8 = tcbOf (RuntimeLayout.ofPlaceWX hpl i).lab q) :
    ∃ (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      ∀ {T S : Nat} {lsize : WeakMem.AllocLabel → Nat} {pT : Loc}
        {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
        (s1 : TermRun.TTh) (Ty : Ty) (w1 w2 : TermRun.Word),
        /- (`SpawnPre.inv1.mem`; `newLoc_in`; G3) -/
        MemRelP (RuntimeLayout.ofPlaceWX hpl i).Λ lbl lsize ts tm sm tp tq sp → 0 < lsize l → 0 < S →
        /- the spawned source thread at `kidC` with `c`'s word and main's id -/
        s1.term = wkTail → s1.env = [("a", Ty, [w1, w2])] → w1.val = .loc ⟨l, 0⟩ 0 → w2.val = mainTidW →
        /- `c`'s cell in the heap, main's id word main's TCB -/
        (∀ th : Thread isa, t.1.threads = #[th] →
          (RuntimeLayout.ofPlaceWX hpl i).Λ.heap.contains (th.st.st.1.regs.get64 .r12).toNat ∧
          BitVec.ofNat 64 (th.st.st.1.regs.get64 .rbx).toNat = tcbM (RuntimeLayout.ofPlaceWX hpl i)) →
        ∃ hg : GhOK (RuntimeLayout.ofPlaceWX hpl i).Λ (recW T S lbl lsize l pT w1),
          ∀ th : Thread isa, t.1.threads = #[th] →
            (X64WakeWorkerR.wakeDR hpl i (tcbM (RuntimeLayout.ofPlaceWX hpl i))
                (tcb2 (RuntimeLayout.ofPlaceWX hpl i)) (GhOK (RuntimeLayout.ofPlaceWX hpl i).Λ)
                exe endPc kp).Wi
              ⟨recW T S lbl lsize l pT w1, hg⟩
              (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceWX hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceWX hpl i).lab).size)
                (tcbOf (RuntimeLayout.ofPlaceWX hpl i).lab q).toNat).st
              (Ctl.of s1) := by
  obtain ⟨th0, l, hs, hc, hk⟩ := X64WakeSpawnW.spawn_workerPost hpl i hA13 hpin2 hp hend hwide h hX
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
  have hlab : ∀ l x, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some x →
      (RuntimeLayout.ofPlaceWX hpl i).lab l = Int64.ofNat x := fun l x hx =>
    PlaceWX.hlab_ofPlaceWX hpl i l x (by rw [hlo, hprog]; exact hx)
  refine ⟨th0', l', hs, hc, fun {T S lsize pT ts tm sm tp tq sp} s1 Ty w1 w2 hm hin hS hterm henv hw1 hjw
    hcm => ?_⟩
  have hg : GhOK (RuntimeLayout.ofPlaceWX hpl i).Λ (recW T S lbl lsize l' pT w1) :=
    X64WakeWorkerR.ghOK_of_clone hm (X64WakeQ.hwf_ofPlaceOK hpl i) hvc hw1 hin hS
  have hPC := X64WakeTcbArea.hPC_q2 hpl i hpin2 hinit2 (recW T S lbl lsize l' pT w1) hm hg hq
    (own := fun st => ownGXW (RuntimeLayout.ofPlaceWX hpl i) (ntA (RuntimeLayout.ofPlaceWX hpl i).lab) st)
    (X := X)
    (fun st hx => by
      obtain ⟨hpc, h8⟩ := hXq st hx
      have hw := Spike.Lib.X64.WakePh.WcSp4.ownG_clone hlab (L := RuntimeLayout.ofPlaceWX hpl i)
        (a := ntA (RuntimeLayout.ofPlaceWX hpl i).lab) (s := st) (by unfold pcOf; rw [hpc]; rfl)
      refine ⟨h8, List.mem_append_left _ (List.mem_append_left _ hw.2), ?_⟩
      rw [(RuntimeLayout.ofPlaceWX hpl i).lab_next]
      exact List.mem_append_left _ (List.mem_append_left _ hw.1))
  exact hk s1 Ty w1 w2 hPC hq hm hin hS hterm henv hw1 hjw hcm

/-- info: 'Spike.Lib.X64WakeSpawnWQ.spawn_workerPostQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_workerPostQ

end Spike.Lib.X64WakeSpawnWQ
