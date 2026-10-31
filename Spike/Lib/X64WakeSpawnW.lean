/-
**The spawn's worker half on x86-64** (in the manner of
`Spike/Lib/WakeSpawnW.lean`): at main's `clone` (`ClonePre`), the record
`X64WakeOkW.recW T S lbl lsize l pT w1` (`c`'s label `l` from `ClonePre`)
satisfies `GhOK` and the child after the handover is in
`X64WakeWorkerR.wakeDR`'s invariant (at `T := tcbM L`, `W := tcb2 L`) at
the spawned source thread's control.

Assembled from `X64WakeChildXI.childSeg_XI` (at `lbl' := lbl`,
`cSf := ⟨l, 0⟩`, `Λw := L.Λ`; its `hflag` from `GhOK`),
`X64WakeWorkerR.wkPR_of`, `wakeDR_entry`, `WorkerSide.clonePre_childWide`
and `X64WakeWorkerR.ghOK_of_clone`; the argument words' `ValRep` are
`ClonePre`'s (the child's `cA` in `%r12`, `meW` main's id in `%rbx`).

Discharged here (A64 carries them as the premise `hSt`): the child's runtime
accesses, by `X64WakeChildSt` in the child's frame (the handed range
`r1Of` from `ClonePre`'s `held`, in the pool by its `Owned`):
- `hS`/`htp4`: main's permit word `meW + 16 = pinA + 24` (`childSt_I`,
  `childSt_al`), given `meW = tcbM L` (`hme`);
- `hT`, `hown`: the worker's TCB word `tcb2 L` loaded (`childLd_I`) and
  owned (`childOwn_I`);
- `hSx`: the second TCB's `tcb2 + 24 = pinA + 128` (`childSt_I`);
- `htpW`: the clone's `tls` is `tcb2 L` (`X64WakeTcbArea.tcbOf_q2` at `Q2 q`).

**Unlike AArch64** (forced by the x64 shape):
- The worker's memory side is `msW hpl i (tcbM L) (tcb2 L) g`, so the
  invariant is `wakeDR`'s at those two TCB words, and the child reads and
  owns its TCB self word (`hT`, `hown`).
- The child's segment needs `c`'s cell in the heap and main's id word at
  `tcbM L` (`hcm`, per thread); AArch64's needs neither.
- The child's stores are discharged here, not carried (`hSt`), given
  `hpin2` and the request `Q2 q`.

Open (premises of `spawn_workerPost`): `ClonePre`, `hX`, the executable
wide (`hwide`), `hA13`, `hpin2` (concrete layout); `hPC` (main's runtime
facts at the clone; `X64WakeTcbArea.hPC_q2`), `Q2 q` (`q2_mk`); the
spawned source thread (`hterm`, `henv`, `hw1`, `hjw`); the memory relation
`hm` (`SpawnPre.inv1.mem`), `hin`, `hS` (as on AArch64); `hcm` (`c`'s cell
in the heap, main's id word `tcbM L`: the spawn's memory relation).
-/
import Spike.Lib.X64WakeWorkerR
import Spike.Lib.X64WakeChildXI
import Spike.Lib.X64WakeChildSt
import Spike.Lib.X64WakeTcbArea
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeSpawnW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakeW1 Spike.Lib.Handover
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.X64WakeInst (Gh wakeMs)
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64WakeOkW (recW)
open Spike.Lib.X64.WakePh (tcb2 tcbM)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64Consumer (Own)

/-- **The worker half of the spawn**: `c`'s label `l` at the clone; for the
record `recW T S lbl lsize l pT w1` (`GhOK` by `ghOK_of_clone`), the child of
any thread of `t` is in `wakeDR`'s invariant at `Ctl.of s1`. -/
theorem spawn_workerPost {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ0 : Scc.Sem.Layout} (hpl : PlaceWX pcfg Λ0 o)
    (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hA13 : Scc.Cert.Spawn.X64.a13data (RuntimeLayout.ofPlaceWX hpl i).Λ o.prog o.secs = true)
    (hpin2 : (RuntimeLayout.ofPlaceWX hpl i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceWX hpl i).Λ.pinned.lo + (RuntimeLayout.ofPlaceWX hpl i).Λ.pinned.size)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hwide : Scc.Cert.WideX64.ExeWide exe)
    {r0 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}
    (h : X64WakePreA.ClonePre (RuntimeLayout.ofPlaceWX hpl i).Λ r0 (r1Of (RuntimeLayout.ofPlaceWX hpl i).lab)
      X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {}) :
    ∃ (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      ∀ {T S : Nat} {lsize : WeakMem.AllocLabel → Nat} {pT : Loc} {own : Own} {q : TcbGG}
        {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
        (s1 : TermRun.TTh) (Ty : Ty) (w1 w2 : TermRun.Word),
        /- main's runtime facts at the clone (`X64WakeTcbArea.hPC_q2`) -/
        (∀ st, X st → PreChild (wakeMs hpl i (recW T S lbl lsize l pT w1)) own
          (RuntimeLayout.ofPlaceWX hpl i).lab q st) →
        /- the second TCB request (`X64WakeTcbArea.q2_mk`) -/
        X64WakeTcbArea.Q2 q →
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
  have h' := h
  obtain ⟨th, th0, _, cA, meW, l, hth, hs, _, _, _, _, _, _, h12, hbx, hheld, _, _, hO1, _, _, _, _, _, _, hc,
    _, _, hvc, hvm⟩ := h'
  refine ⟨th0, l, hs, hc, fun {T S lsize pT own q ts tm sm tp tq sp} s1 Ty w1 w2 hPC hq hm hin hS hterm henv
    hw1 hjw hcm => ?_⟩
  have hg : GhOK (RuntimeLayout.ofPlaceWX hpl i).Λ (recW T S lbl lsize l pT w1) :=
    X64WakeWorkerR.ghOK_of_clone hm (X64WakeQ.hwf_ofPlaceOK hpl i) hvc hw1 hin hS
  refine ⟨hg, fun th1 hth1 => ?_⟩
  have e1 : th1 = th := by rw [hth] at hth1; exact (List.singleton_inj.mp (congrArg Array.toList hth1)).symm
  subst e1
  -- the flag's word is shared (`GhOK`)
  have hflag : ∀ x, wordAddr (recW T S lbl lsize l pT w1).lbl (⟨l, 0⟩ : WeakMem.Address) = some x →
      Consumer1.LocIn (RuntimeLayout.ofPlaceWX hpl i).Λ.shared (wordLoc x) := by
    obtain ⟨b, hb, -, hT⟩ := hg.2.2.2.1
    intro x hx
    simp only [recW] at hb hT
    simp only [recW, wordAddr, hb, Option.map_some, Option.some.injEq] at hx
    rw [← hx, ← hT]; exact hg.2.2.2.2
  -- the clone's `tls` is the second TCB
  have htpW : BitVec.ofNat 64 (tcbOf (RuntimeLayout.ofPlaceWX hpl i).lab q).toNat =
      tcb2 (RuntimeLayout.ofPlaceWX hpl i) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, X64WakeTcbArea.tcbOf_q2 hpl i hq]
  obtain ⟨th', cA', meW', -, -, hth', h12', hbx', -, hk⟩ :=
    X64WakeChildXI.childSeg_XI hpl i (tcbM (RuntimeLayout.ofPlaceWX hpl i)) (recW T S lbl lsize l pT w1) hA13
      hp hend (Λw := (RuntimeLayout.ofPlaceWX hpl i).Λ) (lbl' := lbl) (cSf := ⟨l, 0⟩) h hX hPC hflag htpW rfl Ty
  have e2 : th' = th1 := by rw [hth] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
  subst e2
  have ecA : cA' = cA := h12'.symm.trans h12
  have emW : meW' = meW := hbx'.symm.trans hbx
  subst ecA emW
  -- the handed range, in the pool
  have hh : handed t.2 0 ((r1Of (RuntimeLayout.ofPlaceWX hpl i).lab).lo +
      (r1Of (RuntimeLayout.ofPlaceWX hpl i).lab).size) = some (0, r1Of (RuntimeLayout.ofPlaceWX hpl i).lab) := by
    simp [handed, hheld]
  have hsub := hO1.1
  have hsz : (r1Of (RuntimeLayout.ofPlaceWX hpl i).lab).size = 16384 := rfl
  obtain ⟨hheap, hme⟩ := hcm th' hth
  rw [hbx'] at hme
  rw [h12'] at hheap
  have hv1 : ValRep lbl w1.val cA' := by rw [hw1]; exact hvc
  have hv2 : ValRep lbl w2.val meW' := by rw [hjw]; exact hvm
  have e24 : BitVec.ofNat 64 meW' + 16#64 = (RuntimeLayout.ofPlaceWX hpl i).pinA + 24#64 := by
    rw [hme, tcbM, BitVec.add_assoc]; rfl
  have e128 : tcb2 (RuntimeLayout.ofPlaceWX hpl i) + 24#64 = (RuntimeLayout.ofPlaceWX hpl i).pinA + 128#64 := by
    rw [tcb2, BitVec.add_assoc]; rfl
  have hS1 := X64WakeChildSt.childSt_I hpl i (T := tcbM (RuntimeLayout.ofPlaceWX hpl i))
    (W := tcb2 (RuntimeLayout.ofPlaceWX hpl i)) rfl rfl (recW T S lbl lsize l pT w1) hm hpin2
    (a := BitVec.ofNat 64 meW' + 16#64) (.inl e24) (th := th')
    (tls := (tcbOf (RuntimeLayout.ofPlaceWX hpl i).lab q).toNat)
    hh hsub hsz
  have hS3 := X64WakeChildSt.childSt_I hpl i (T := tcbM (RuntimeLayout.ofPlaceWX hpl i))
    (W := tcb2 (RuntimeLayout.ofPlaceWX hpl i)) rfl rfl (recW T S lbl lsize l pT w1) hm hpin2
    (a := tcb2 (RuntimeLayout.ofPlaceWX hpl i) + 24#64) (.inr e128) (th := th')
    (tls := (tcbOf (RuntimeLayout.ofPlaceWX hpl i).lab q).toNat) hh hsub hsz
  have hT := X64WakeChildSt.childLd_I hpl i (tcbM (RuntimeLayout.ofPlaceWX hpl i)) rfl
    (recW T S lbl lsize l pT w1) hm hpin2 (th := th') (tls := (tcbOf (RuntimeLayout.ofPlaceWX hpl i).lab q).toNat)
    hh hsub hsz
  have hal : (BitVec.ofNat 64 meW' + 16#64).toNat % 4 = 0 := by
    rw [e24]; exact X64WakeChildSt.childSt_al hpl i
  obtain ⟨hAt, hseg⟩ := hk w1 w2
  have hseg' := hseg hv1 ⟨_, hw1⟩ hv2 hS1 hal hT
    (X64WakeChildSt.childOwn_I hpl i _ _ _ exe endPc _) hS3 hw1 hv1 hv2 hheap hme
  have hC : Ctl.of s1 = Spike.Lib.X64.Flow.Worker.Wake.Child.kidC Ty w1 w2 := by
    unfold Ctl.of; rw [hterm, henv]; rfl
  obtain ⟨thw, hthw, hw⟩ := WorkerSide.clonePre_childWide h hX hwide
  have e3 : thw = th' := by rw [hth] at hthw; exact (List.singleton_inj.mp (congrArg Array.toList hthw)).symm
  subst e3
  rw [hC]
  exact X64WakeWorkerR.wakeDR_entry hpl i _ _ _ exe endPc kp ⟨recW T S lbl lsize l pT w1, hg⟩ _ _
    (X64WakeWorkerR.wkPR_of hpl i _ _ _ exe endPc kp hseg' hAt) (hw _ _ _)

/-- info: 'Spike.Lib.X64WakeSpawnW.spawn_workerPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_workerPost

end Spike.Lib.X64WakeSpawnW
