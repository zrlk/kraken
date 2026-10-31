/-
**The certification core of the allocation-capable consumer**
(`Spike/Lib/A64ConsumerA.lean`): promises are to shared regions
(`promSharedA`, `promSharedS` with the arena).

`PreCoreJA` is `PreCoreJ` with `PreJA`'s arena clauses (the allocation
invariant at the source's heap use, `FreshInv`, `CtrOff`, the hold
`HoldInvA`); it is kept along the thread's certification runs
(`core_stepA`, `core_stepS` with the arena and `instr_stepA`'s rows on the
messages exempting the outstanding promises; `core_sysA`; `core_siteA`).

- `PreCoreJA`, `PreCoreJA.msgs`, `pre_coreA`, `pre_core_promiseA`: the core.
- `core_localA`, `core_landA`: a frame run lands in the core.
- `core_stepA`, `core_sysA`, `core_siteA`, `core_insA`: the steps (over
  `NodesA … ab`; `core_sysAX`: a system call off the output `write`).
- `promSharedA`: `PromSharedA` from the node obligations (`…T`, `…H`:
  over `TakeSiteS`, `HeldPathS`, `PreSAH`); `promSharedAX`:
  over `NodesA … ab`, the output `write`'s certification steps by a
  hypothesis.
-/
import Spike.Lib.A64ConsumerAStep
import Spike.Lib.A64ConsumerAPub

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.CtrRows (CtrW)

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)}
  {Cl : State → Prop}

/-- **The core of `PreJA`** for a thread `th` and a memory `mem`
(`PreCoreJ` with the arena), over a fragment `J`. -/
def PreCoreJA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (J : InvS)
    (ar : Arena) (th : Thread isaLSE2) (mem : Memory) (s : TermRun.Cfg) : Prop :=
  ∃ (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    J lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧ HoldInvA ar lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd mem.last ∧ Inv1 Λ lbl lsize ts th mem s.mem ∧ OwnMsgs mem ∧
    MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ (∀ q ∈ mem.init, InitIn Λ q.1) ∧ MemFits mem ∧
    MsgsExcept (fun m => G m.loc m.val) th.prom mem ∧ (∀ l, G l (mem.initVal l)) ∧
    ExtRows.OwnOk (own th.st th0.stack) mem th.prom ∧
    AllocInvAt Λ lbl lsize th mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) ⟨th0.term, th0.env, hd⟩ ∧
    AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc ∧ CtrOff ar lbl lsize ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- `PreCoreJA`'s message clauses, as `stepG_of` takes them. -/
theorem PreCoreJA.msgs {J : InvS} {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    (h : PreCoreJA Λ P p G own J ar th mem s) :
    MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ MsgsExcept (fun m => G m.loc m.val) th.prom mem := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hsh, -, -, hgm, -⟩ := h
  exact ⟨hsh, hgm⟩

/-- **`PreJA` gives `PreCoreJA`** of its one thread and the memory. -/
theorem pre_coreA {J : InvS} {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    {th : Thread isaLSE2} (h : PreJA Λ P p G own J rS Tk μ ar t s) (hth : t.1.threads = #[th]) :
    PreCoreJA Λ P p G own J ar th t.1.mem s := by
  obtain ⟨th', th0, -, lbl, lsize, ts, -, -, hd, hth', -, -, -, -, -, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown,
    hmi, hfi, hgi, hoo, hai, hfr, hco, hre⟩ := h
  obtain rfl : th = th' := (get_one hth (show t.1.threads[0]? = some th' by rw [hth']; rfl)).2
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, MsgsExcept.of_all hmi.1 _, hmi.2,
    hfi, MemInv.msgsExcept hgi _, hgi.1, hoo, hai, hfr, hco, hre⟩

/-- **`PreSA` followed by a certified promise gives `PreCoreJA`** of the
promising thread and the memory with the promise (`pre_core_promiseS` with
the arena, `AllocInvAt.promise`). -/
theorem pre_core_promiseA {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2}
    {w : Msg} (h : PreSA Λ P p G own I rS Tk μ ar t s) (hth : t.1.threads = #[th]) (hwt : w.tid = 0)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1) :
    PreCoreJA Λ P p G own I ar (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1 s := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := pre_coreA h hth
  have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩,
    hinv.promise_cert_on (soloWide8CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc, ownMsgs_append hwt hown,
    msgsExcept_promise hsh w, hini,
    ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
    msgsExcept_promise hgm w,
    hgi, ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hai.promise w rfl,
    hfr, hco, hre⟩

/-- **A frame run lands in `PreCoreJA`** over any fragment `J`
(`pre_localJA` without the kernel state). -/
theorem core_localA (hP : HookOK P p) {J : InvS} {mem : Memory} {s : TermRun.Cfg}
    {u : Thread isaLSE2} {th0 : TermRun.TTh} {lbl : Lbl} {lsize : Lsize} {ts : Nat → Option Nat} {c' : Ctl}
    {fs' : List TermRun.Frame} {hd : Option (Nat × TermRun.Word)}
    (hs0 : s.ths = #[th0]) (hσ : th0.σs = []) (hp : th0.promises = []) (hJ : J lbl lsize u.st c' fs')
    (hw : WideSt u.st) (hb : u.Bnd mem.last) (hinv : Inv1 Λ lbl lsize ts u mem s.mem) (hown : OwnMsgs mem)
    (hsh : MsgsExcept (fun m => LocIn Λ.shared m.loc) u.prom mem) (hini : ∀ q ∈ mem.init, InitIn Λ q.1)
    (hfi : MemFits mem) (hgm : MsgsExcept (fun m => G m.loc m.val) u.prom mem) (hgi : ∀ l, G l (mem.initVal l))
    (hoo : ExtRows.OwnOk (own u.st fs') mem u.prom)
    (hai : AllocInvAt Λ lbl lsize u mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c')
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hre : ∃ tr, (SrcSem.source P p).Reach tr s)
    (hhi : HoldInvA ar lbl lsize s.mem hd) (hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a)
    (hcr' : fs' = [] → ∀ a, c'.term ≠ .ret a) (hr : FrameRun p (⟨th0.term, th0.env, hd⟩, th0.stack) (c', fs')) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own J ar u mem s' := by
  have hrun := frun_one hP hr hs0 rfl rfl hσ rfl hp hcr hcr'
  obtain ⟨tr, hre⟩ := hre
  exact ⟨_, hrun, { th0 with term := c'.term, env := c'.env, stack := fs' }, lbl, lsize, ts, c'.hold, rfl, hσ, hp,
    hJ, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    by rw [heapUse_one (th' := { th0 with term := c'.term, env := c'.env, stack := fs' }) hs0 rfl rfl]; exact hai,
    by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr, hco, _, reach_run hre hrun⟩

/-- **A landing over `PendA` in the core**: the pending frame run taken
(`core_land` with the arena). -/
theorem core_landA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl) {th : Thread isaLSE2}
    {mem : Memory} {s s₂ : TermRun.Cfg} (hrun : (SrcSem.source P p).Run s [] s₂)
    (h : PreCoreJA Λ P p G own (PendA p I) ar th mem s₂) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar th mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, ⟨hnr, c₂, fs₂, hr, hI⟩, hhi, hw, hb, hinv, hown, hsh, hini,
    hfi, hgm, hgi, hoo, hai, hfr, hco, hre⟩ := h
  obtain ⟨s', hr', h'⟩ := core_localA (J := I) (own := own) hP hs0 hσ hp hI hw hb hinv hown hsh hini hfi hgm hgi
    (by rw [hN.ownRun _ _ _ _ _ _ _ hr (.inr hI)]; exact hoo) (allocInvAt_frameRun hai hr) hfr hco hre hhi hnr
    (fun h0 => hN.noRet _ _ _ _ (h0 ▸ hI)) hr
  exact ⟨s', run_trans0 hrun hr', h'⟩

/-- **An instruction step off a system call and off the take site keeps
`PreCoreJA`** (`core_stepS` with the arena; `instr_stepA`'s rows), matched
by a source run with no event. -/
theorem core_stepA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg} {outs : List (Except String (Outcome isaLSE2))}
    {o : Outcome isaLSE2} (h : PreCoreJA Λ P p G own I ar th mem s) (hns : abi.atSys th.st = false)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a)
    (hso : stepOne Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, tr, hreach⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, hr0, hown_eq, hout⟩ := hN.rowNS hI hnt hns
  have hI1 : IRun p I lbl lsize th.st c₁ fs₁ := IRun.trans hI hr0
  have hoo₁ : ExtRows.OwnOk (own th.st fs₁) mem th.prom := by rw [hown_eq]; exact hoo
  have hsrc : (fs₁ = [] → ∀ a, c₁.term ≠ .ret a) →
      (SrcSem.source P p).Run s [] { s with ths := #[thAt th0 c₁ fs₁] } :=
    fun hr1 => frun_one hP hr0 hs0 rfl rfl hσ rfl hp hcr hr1
  obtain ⟨tree0, hex0⟩ := Option.isSome_iff_exists.mp (Out.exec_isSome rfl hns hout)
  have hw' : WideSt o.thread.st :=
    wideInv _ _ _ hw ((Kernel.certExec_of_not_atSys abi hns).trans hex0) (ExtThread.stepOne_treeLeaf hex0 hso ho)
  have hb' := (stepOne_bnd _ hso ho hb).1
  have hinit : o.mem.init = mem.init := (stepOne_dord _ hso ho).2.2.1.1
  have hfi' : MemFits o.mem := by
    refine ⟨fits_stepOne Arch.armv8 (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
      hso ho hfi.1, ?_⟩
    unfold InitFits; rw [hinit]; exact hfi.2
  have hini' : ∀ q ∈ o.mem.init, InitIn Λ q.1 := by rw [hinit]; exact hini
  have hgi' : ∀ l, G l (o.mem.initVal l) := by intro l; unfold Memory.initVal; rw [hinit]; exact hgi l
  have hoo' : ExtRows.OwnOk (own o.thread.st fs₁) o.mem o.thread.prom :=
    ownOk_step hex0 (hN.ownInstr _ _ _ _ _ hI1 hns tree0 hex0) hinv.coh hinv.mem.tq_nodup
      (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo₁
  have hown' := ownMsgs_step hso ho hown
  have hai1 := allocInvAt_frameRun hai hr0
  have hhi1 : HoldInvA ar lbl lsize s.mem c₁.hold := holdInvA_frameRun hr0 hhi
  have hnd : th.prom.Nodup := hinv.mem.tq_nodup
  have hpl : ∀ q ∈ th.prom, q ≤ mem.last := fun q hq => (hinv.mem.tq_le q hq).2
  have hheap1 : heapUse { s with ths := #[thAt th0 c₁ fs₁] } = heapUse s := heapUse_one hs0 rfl rfl
  have hfr1 : AllocInv.FreshInv lbl ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).lbase
      ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).n 0 (thAt th0 c₁ fs₁).nalloc :=
    freshInv_one hs0 rfl rfl rfl rfl hfr
  rcases hout.unpubL with ⟨kf, sf, cp, cf, hef, -, hps, hrL, hxf⟩ | hout
  · -- the fence with the source's publication: the source publishes, then runs locally
    obtain ⟨hm, hpr, hst, hinv'⟩ := ExtRows.inv1_fence hinv hef hso ho
    have hX : PendA p I lbl lsize o.thread.st cf fs₁ := hst ▸ hxf
    have hnr : fs₁ = [] → ∀ a, cp.term ≠ .ret a := fun h => noRet_of_run hrL (hX.noRet h)
    have hrun1 := hsrc fun _ => hps.not_ret
    obtain ⟨th', hstep, hte, hen, hp', hσ', hsk, hna, htl⟩ := src_publish_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp hps rfl rfl hnr
    have hrun := run_trans0 hrun1 (run_one hstep)
    obtain ⟨-, hcp⟩ := hps.landing
    have hrL' : FrameRun p (⟨th'.term, th'.env, none⟩, th'.stack) (cf, fs₁) := by
      rw [hte, hen, hsk, ← hcp]; exact FrameRun.ofLocal hrL fs₁
    have hai2 : AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) cf :=
      allocInvAt_frameRun ((allocInvAt_out hai1 hnd (.inl ⟨hm, hpr⟩)).retarget
        (hai1.idle_of_term hps.notAlloc) fun w h => by rw [hcp] at h; cases h) (FrameRun.ofLocal hrL fs₁)
    have hs2 : ({ ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg) with
        ths := (#[thAt th0 c₁ fs₁] : Array TermRun.TTh).set! 0 th' } : TermRun.Cfg).ths = #[th'] := by simp
    obtain ⟨s₃, hrun3, hpre⟩ := core_localA (J := PendA p I) (own := own) (th0 := th') (hd := none) hP hs2
      (hσ'.trans hσ) hp' hX hw' hb' hinv' hown' (by rw [hm, hpr]; exact hsh) hini' hfi'
      (by rw [hm, hpr]; exact hgm) hgi' hoo' (by
        rw [HeapPres.heapUse_set (s := { s with ths := #[thAt th0 c₁ fs₁] })
          (s' := { ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg) with
            ths := (#[thAt th0 c₁ fs₁] : Array TermRun.TTh).set! 0 th' }) (th' := th') (i := 0) rfl rfl rfl hna htl,
          hheap1]
        exact hai2)
      (freshInv_one hs0 hs2 rfl rfl hna hfr) hco ⟨_, reach_run hreach hrun⟩ (.inl trivial)
      (fun h a => by rw [hte]; exact hnr (hsk.symm.trans h) a) hX.noRet hrL'
    exact core_landA hP hN (run_trans0 hrun hrun3) hpre
  -- no publication: the row is one under the memory side with none
  obtain ⟨ex, ha⟩ := hai1.arenaOK
  by_cases hwc : Writes th mem o ar.ctrLoc
  · -- the counter's add: the source stutters into the hold of the old count
    obtain ⟨k, op, g, x, τ, e, n, hex, hrt, hmp, hs, hh0, hop, hX⟩ :=
      hN.ctrRow _ _ _ _ _ hI1 hns th mem outs o rfl hso ho hwc
    obtain ⟨old, ⟨trc, hlat, hrd'⟩, hown0, hland, hinv', hcw⟩ :=
      CtrRows.ctrRmw_row (I := isaLSE2) (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off)
        (mcl := ar.cells) (mown := fun st => own st fs₁)
        (Y := fun old s' => PendA p I lbl lsize s'
          { c₁ with hold := some (ar.ctr, TermRun.cst (.num (old.setWidth 64).toNat)) } fs₁)
        hinv hso ho hgm hgi hoo₁ hex
        (show (msOfA0 Λ μ rd G own ar I lbl lsize fs₁).rt (BitVec.ofNat 64 ar.ctr).toNat from hrt) hop
        hX
    obtain ⟨hold64, hai'⟩ := allocInvAt_ctrS hok hai1 hh0 hnd hpl hlat hrd' hs.toTrue hcw
    have hle : (old.setWidth 64).toNat ≤ ar.cells := by rw [hold64]; exact ha.hu_le
    have hlo : Spike.Lib.AllocLo.LoOf ar.heap ar.cells lbl lsize (old.setWidth 64).toNat := by
      rw [hold64]; exact Spike.Lib.AllocLo.loOf_of_arenaOK ha
    have hX' := hland hle hlo
    rw [hold64] at hX'
    have hGold := msgsExcept_read_tlatestP hgm hgi hlat hrd'
    have hGnew := (hX old hGold hown0 hle hlo).1
    have hmg : MsgsExcept (fun m => LocIn Λ.shared m.loc) o.thread.prom o.mem ∧
        MsgsExcept (fun m => G m.loc m.val) o.thread.prom o.mem := by
      rcases hcw with ⟨q, -, hg, -, hm, hpr⟩ | ⟨hm, hpr⟩
      · rw [hm, hpr]; exact ⟨msgsExcept_erase hsh hg (hmp.2 rfl), msgsExcept_erase hgm hg hGnew⟩
      · rw [hm, hpr]
        exact ⟨msgsExcept_append hsh (w := ⟨wordLoc ar.ctr, _, 0⟩) (hmp.2 rfl),
          msgsExcept_append hgm (w := ⟨wordLoc ar.ctr, _, 0⟩) hGnew⟩
    have hrun1 := hsrc fun _ => hs.not_ret
    refine core_landA hP hN hrun1 ⟨thAt th0 c₁ fs₁, lbl, lsize, ts, some (ar.ctr, TermRun.cst (.num (heapUse s))),
      rfl, hσ, hp, hX', .inr ⟨_, rfl⟩, hw', hb', hinv', hown', hmg.1, hini', hfi', hmg.2, hgi', hoo', ?_, hfr1, hco,
      _, reach_run hreach hrun1⟩
    rw [hheap1]; exact hai'
  by_cases hNS : NewStM p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) th.st c₁
  · -- the box's initialising store: the source allocates the box at the fresh label at the heap use
    obtain ⟨lbl', lsize', ts', th', sm, L, V, hrun2, hJ, hσ', hp', hst', hcrJ, hinv'', hai'', hfr'', hco', hL, hG,
      hwr⟩ := newSt_src hP hN hsafe hGpl hok hs0 hσ hp hinv hai1 hfr hco hreach (hsrc fun _ => hNS.not_ret) hso ho hNS
    have hmg : MsgsExcept (fun m => LocIn Λ.shared m.loc) o.thread.prom o.mem ∧
        MsgsExcept (fun m => G m.loc m.val) o.thread.prom o.mem := by
      rcases hwr with ⟨hm, hpr⟩ | ⟨q, -, hg, hm, hpr⟩
      · rw [hm, hpr]
        exact ⟨msgsExcept_append hsh (w := ⟨L, V, 0⟩) hL, msgsExcept_append hgm (w := ⟨L, V, 0⟩) hG⟩
      · rw [hm, hpr]
        exact ⟨msgsExcept_erase hsh hg hL, msgsExcept_erase hgm hg hG⟩
    obtain ⟨s₃, hrun3, hpre⟩ := core_localA (J := I) (own := own) (s := { s with mem := sm, ths := #[th'] })
      (th0 := th') (hd := none) (c' := ⟨th'.term, th'.env, none⟩) (fs' := th'.stack) hP rfl hσ' hp' hJ hw' hb'
      hinv'' hown' hmg.1 hini' hfi' hmg.2 hgi' (by rw [hst']; exact hoo') hai'' hfr'' hco'
      ⟨_, reach_run hreach hrun2⟩ (.inl trivial) hcrJ hcrJ (.refl _)
    exact ⟨s₃, run_trans0 hrun2 hrun3, hpre⟩
  -- not the box's store: the row is one with no box rows (the counter's add at a box refuted)
  have hout0 : Out p lbl (msOfA0 Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁)
      th.st c₁ := by
    rcases hout.unnew with h | ⟨k, op, g, n, τ, hex, hrt, hop, hX⟩ | h
    · exact absurd h hNS
    · obtain ⟨_, -, -, -, -, hcw⟩ := CtrRows.ctrRmw_row (I := isaLSE2) (mh := ar.heap) (mc := ar.ctr)
        (mu := ar.units) (mo := ar.off) (mcl := ar.cells) (mown := fun st => own st fs₁) (Y := fun _ _ => True)
        hinv hso ho hgm hgi hoo₁ hex
        (show (msOfA0 Λ μ rd G own ar I lbl lsize fs₁).rt (BitVec.ofNat 64 ar.ctr).toNat from hrt) hop
        fun old h1 h2 h3 h4 => ⟨hX old h1 h2 h3 h4, trivial⟩
      exact absurd (writes_of_ctrW hcw) hwc
    · exact h
  -- not the counter's add: the write is one the arena allows
  have hmw := CtrRows.out_memW (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
    hinv hso ho hns (A64Ext.wide8_exec hw hns) hgm hgi hoo₁ hout0
  have hai' : AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c₁ := by
    refine allocInvAt_out hai1 hnd ?_
    rcases hmw with hm | ⟨L, V, -, hwr, -⟩
    · exact .inl hm
    · have hW : Writes th mem o L := ⟨V, hwr⟩
      exact .inr ⟨L, hW, fun he => hwc (he ▸ hW),
        (hN.arena _ _ _ _ _ hI1 hns th mem outs o L rfl hso ho hW).resolve_right hNS⟩
  have hmg : MsgsExcept (fun m => LocIn Λ.shared m.loc) o.thread.prom o.mem ∧
      MsgsExcept (fun m => G m.loc m.val) o.thread.prom o.mem := by
    rcases hmw with ⟨hm, hpr⟩ | ⟨L, V, hL8, hwr, hL⟩
    · exact ⟨msgsExcept_of_eq hsh hm hpr, msgsExcept_of_eq hgm hm hpr⟩
    have hLw := ExtRows.loc_wordLoc hL8
    have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
    have hPm : LocIn Λ.shared L ∧ G L V := by
      rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
        ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨hLc, -, -, -, -⟩
      · exact ⟨hmp.2 rfl, hGV⟩
      · obtain ⟨k, m, hkm, hl⟩ := hsafe.cell₁ (reach_run hreach (hsrc fun _ a' h => by rw [ht] at h; cases h))
          hI1 (.inr ⟨b, ht⟩) hev hsa
        obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
        rw [hl] at hoff
        rw [hsa] at hv
        have hwa := wordAddr_of_valRep_loc0 hv
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h8] at hi
          exact shared_of_wordAddr hinv.mem hwa hoff i hi
        · rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
      · obtain ⟨k, m, hkm, hl⟩ := hsafe.xchg₁ (reach_run hreach (hsrc fun _ => xchgSite_not_ret hxs)) hI1 hxs
        obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
        rw [hl] at hoff
        have hwa := wordAddr_of_valRep_loc0 hA
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h8] at hi
          exact shared_of_wordAddr hinv.mem hwa hoff i hi
        · rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
      · subst hLc; exact (hwc ⟨V, hwr⟩).elim
    rcases hwr with ⟨hm, hpr⟩ | ⟨q, -, hg, hm, hpr⟩
    · rw [hm, hpr]
      exact ⟨msgsExcept_append hsh (w := ⟨L, V, 0⟩) hPm.1, msgsExcept_append hgm (w := ⟨L, V, 0⟩) hPm.2⟩
    · rw [hm, hpr]
      exact ⟨msgsExcept_erase hsh hg hPm.1, msgsExcept_erase hgm hg hPm.2⟩
  obtain ⟨hsh', hgm'⟩ := hmg
  have hU : ∀ {x : TermRun.Cfg} {c : Ctl}, heapUse x = heapUse { s with ths := #[thAt th0 c₁ fs₁] } →
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c →
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse x) c :=
    fun he h => by rw [he, hheap1]; exact h
  rcases CtrRows.out_localW (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
      hinv hso ho hns (A64Ext.wide8_exec hw hns) hgm hgi hoo₁ hout0 with
    ⟨c', hr, hX, hinv'⟩ |
    ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
    ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
    ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
    ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcw⟩ |
    ⟨s', A, x, a, τ, e, ta, ws, k, wold, old, us, hst, ht, hev, hk', hh0, hold, hA, hcl, hus, hX, hm, hinv'⟩
  · -- a local run: the row's run and the landing's pending run
    have hr1 := hr0.trans (FrameRun.ofLocal hr fs₁)
    obtain ⟨s', hrun, hpre⟩ := core_localA (J := PendA p I) (own := own) hP hs0 hσ hp hX hw' hb' hinv' hown' hsh'
      hini' hfi' hgm' hgi' hoo' (allocInvAt_frameRun hai' (FrameRun.ofLocal hr fs₁)) hfr hco ⟨tr, hreach⟩ hhi hcr
      hX.noRet hr1
    exact core_landA hP hN hrun hpre
  · -- the load row
    have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
    obtain ⟨jl, hjl⟩ := exists_sLatest (hsafe.cell₁ (reach_run hreach hrun1) hI1 (.inl ht) hev hsa)
    rw [hsa] at hv
    rw [← wordLoc_toNat] at hex
    obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho (wordAddr_of_valRep_loc0 hv) hjl
    obtain ⟨-, k, v, hgv, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
    obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow (wordAddr_of_valRep_loc0 hv)
      (SLatestP.nil_iff.mpr hjl) htl hrd'
    have hX' := hX v ⟨m.val, m.view, jl⟩ (hrd _ _ _ _ _ _ _ (reach_run hreach hrun1) rfl hp hm hrep)
      (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
    obtain ⟨th', hstep, hte, hen, hp', hσ', hst', hna', htl'⟩ := src_load_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp ht hev hsa
      (hN.cell _ _ _ _ _ hI1 x a e ty w (.inl ht) hev) hjl hm hX'.noRet
    have hrun := run_trans0 hrun1 (run_one hstep)
    refine core_landA hP hN hrun ⟨th', lbl, lsize, ts, none, rfl, hσ'.trans hσ, hp', ?_, .inl trivial, hw', hb',
      hinv', hown', hsh', hini', hfi', hgm', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
      reach_run hreach hrun⟩
    · show PendA p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
      rw [hte, hen, hst', hgv]; exact hX'
    · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
      rw [hst']; exact hoo'
    · refine hU (HeapPres.heapUse_set (s := { s with ths := #[thAt th0 c₁ fs₁] }) (i := 0) rfl rfl rfl hna' htl') ?_
      exact hai'.retarget (hai'.idle_of_term (notAlloc_let ht (fun _ _ h => by cases h) fun _ _ h => by cases h))
        fun w h => by cases h
  · -- the store row
    have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
    obtain ⟨k, m, hkm, hml⟩ := hsafe.cell₁ (reach_run hreach hrun1) hI1 (.inr ⟨b, ht⟩) hev hsa
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst', hna', htl'⟩ := src_store_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp ht hev hsa
      (hN.cell _ _ _ _ _ hI1 x a e ty w (.inr ⟨b, ht⟩) hev) hevb hX.noRet
    rw [hsa] at hv
    rw [← wordLoc_toNat] at hex
    obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wb.val, mv⟩) _ hex hso ho (wordAddr_of_valRep_loc0 hv) hoff hvb
    have hrun := run_trans0 hrun1 (run_one hstep)
    refine core_landA hP hN hrun ⟨th', lbl, lsize, _, none, rfl, hσ'.trans hσ, hp', ?_, .inl trivial, hw', hb',
      hinv', hown', hsh', hini', hfi', hgm', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
      reach_run hreach hrun⟩
    · show PendA p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
      rw [hte, hen, hst', hst'']; exact hX
    · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
      rw [hst']; exact hoo'
    · refine hU (heapUse_store (s := { s with ths := #[thAt th0 c₁ fs₁] }) rfl hkm hml hna' htl') ?_
      exact hai'.retarget (hai'.idle_of_term (notAlloc_let ht (fun _ _ h => by cases h) fun _ _ h => by cases h))
        fun w h => by cases h
  · -- the load of an exchange: the source stutters after the row's run, holding the latest word
    have hrun1 := hsrc fun _ => xchgSite_not_ret hxs
    obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach hrun1) hI1 hxs
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    obtain ⟨jl, hjl⟩ := exists_sLatest ⟨k, m0, hkm, hml⟩
    have hwa := wordAddr_of_valRep_loc0 hA
    rw [← wordLoc_toNat] at hex
    obtain ⟨-, -, hinv', -⟩ := hinv.load hwf _ hex hso ho hwa hjl
    obtain ⟨-, k', r, hgr, htl, hrd'⟩ := stepOne_load_tlatestP _ hex hso ho hinv.coh
    obtain ⟨m, hm, hrep⟩ := hinv.mem.latestP_read hwf hinv.narrow hwa (SLatestP.nil_iff.mpr hjl) htl hrd'
    have hX' := hX r ⟨m.val, m.view, jl⟩ (hrd _ _ _ _ _ _ _ (reach_run hreach hrun1) rfl hp hm hrep)
      (valRep_setWidth_of_fits hrep (read?_fits hfi.1 hfi.2 hrd'))
    have hAc := ctr_ne_of_wordAddr hco hwa hoff
    refine core_landA hP hN hrun1 ⟨thAt th0 c₁ fs₁, lbl, lsize, ts, some (A.toNat, ⟨m.val, m.view, jl⟩), rfl, hσ,
      hp, ?_, .inl ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv', hown', hsh', hini', hfi', hgm', hgi', hoo',
      ?_, hfr1, hco, _, reach_run hreach hrun1⟩
    · rw [hgr]; exact hX'
    · rw [hheap1]
      exact hai'.retarget (fun w h => by rw [hh0] at h; cases h) fun w h => hAc (Prod.mk.inj (Option.some.inj h)).1
  · -- the store of an exchange: the source exchange after the row's run, reading the held word
    have hrun1 := hsrc fun _ => xchgSite_not_ret hxs
    obtain ⟨k, m0, hkm, hml⟩ := hsafe.xchg₁ (reach_run hreach hrun1) hI1 hxs
    obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m0 (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
    rw [hml] at hoff
    have hwa := wordAddr_of_valRep_loc0 hA
    have hAc := ctr_ne_of_wordAddr hco hwa hoff
    rw [hh0] at hhi1
    rcases hhi1 with ⟨sa', jl, m, hwa', hoff', hjl, hm, rfl⟩ | ⟨w, hw0⟩
    rotate_left
    · exact absurd (Prod.mk.inj (Option.some.inj hw0)).1 hAc
    have hsa' : sa' = sa := hinv.mem.wordAddr_inj hwa' hwa hoff' hoff
    subst sa'
    obtain ⟨th', mv, hstep, hte, hen, hp', hσ', hst', hna', htl'⟩ := src_swap_stepS (p := p)
      (c := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) hP rfl hp hxs hev hjl hm
      (xchgSite_not_ret hxs) hX.noRet
    rw [← wordLoc_toNat] at hex
    obtain ⟨hst'', q, hinv'⟩ := hinv.store (m := ⟨sa, wv.val, mv⟩) _ hex hso ho hwa hoff hvb
    have hrun := run_trans0 hrun1 (run_one hstep)
    refine core_landA hP hN hrun ⟨th', lbl, lsize, _, none, rfl, hσ'.trans hσ, hp', ?_, .inl trivial, hw', hb',
      hinv', hown', hsh', hini', hfi', hgm', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
      reach_run hreach hrun⟩
    · show PendA p I lbl lsize o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack
      rw [hte, hen, hst', hst'']; exact hX
    · show ExtRows.OwnOk (own o.thread.st th'.stack) _ _
      rw [hst']; exact hoo'
    · refine hU (HeapPres.heapUse_swap (s := { s with ths := #[thAt th0 c₁ fs₁] }) rfl hjl hna' htl') ?_
      exact hai'.retarget (fun w h => hAc (by rw [hh0] at h; exact (Prod.mk.inj (Option.some.inj h)).1))
        fun w h => by cases h
  · exact absurd (writes_of_ctrW hcw) hwc
  · -- the allocation's last instruction: the source allocates at the fresh label at the heap use
    subst hst
    have hrun1 := hsrc fun _ a' h => by rw [ht] at h; cases h
    have h1 : ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).ths[0]? = some (thAt th0 c₁ fs₁) := rfl
    obtain ⟨hland, hJ⟩ := hX _ (if (AllocSrc.newBufZero (TermRun.close [] τ)).isSome then k else 0)
      (hfr1 _ (Nat.le_refl _))
    have hai1' : AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off
        (heapUse ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg)) c₁ := by rw [hheap1]; exact hai'
    have hfit : k * TermRun.nWords us + 1 ≤ ar.cells :=
      (hland : HeapLand.AllocLand ar.heap ar.cells A.toNat (k * TermRun.nWords us)).2.2
    obtain ⟨hoff, -, hoffit⟩ := hok.off k τ us hus hfit
    obtain ⟨hold', th', hstep, hte, hen, hp', hσ', hst', hna', hheap', hinv'', hai'', hfr''⟩ :=
      HeapLand.alloc_rowS (kn := P.k) (arch := P.arch) (p := p) (c' := ⟨e, [], none⟩) hai1' hinv' h1 rfl rfl hσ
        hfr1 (TermRun.Cfg.lt_n (by simp)) ht hev hk' hh0 hold hcl hus (hok.units k τ us hus hfit)
        hoff hoffit (hN.zero _ _ _ _ _ hI1 x a τ e ht) rfl (hsafe.box _ _ (reach_run hreach hrun1))
    have hσ0 : (thAt th0 c₁ fs₁).σs = [] := hσ
    rw [hσ0] at hen
    rw [hA, hold'] at hJ hland
    have hcrJ : th'.stack = [] → ∀ a, th'.term ≠ .ret a := fun h0' => by
      have hf : fs₁ = [] := by rw [hst'] at h0'; exact h0'
      subst hf
      rw [hte]; exact hN.noRet _ _ _ _ hJ
    have hx : mainExit ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg) = [] :=
      mainExit_of_not_ret h1 fun a' h => by
        have h' : c₁.term = .ret a' := h
        rw [ht] at h'; cases h'
    have hstep' := src_step_of_threadSteps hP hstep (by simp) (hp'.trans hp) hx (mainExit_of_pair (by simp) hcrJ)
    have hrun2 := run_trans0 hrun1 (run_one hstep')
    have hV : ∀ {x : TermRun.Cfg} {u : Nat} {c : Ctl} {lb : Lbl} {ls : Lsize}, heapUse x = u →
        AllocInvAt Λ lb ls o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off u c →
        AllocInvAt Λ lb ls o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse x) c :=
      fun he h => he ▸ h
    obtain ⟨s₃, hrun3, hpre⟩ := core_localA (J := I) (own := own) (s := { s with mem := _, ths := #[th'] })
      (th0 := th') (hd := none) (c' := ⟨th'.term, th'.env, none⟩) (fs' := th'.stack) hP rfl (hσ'.trans hσ)
      (hp'.trans hp) (by rw [hte, hen, hst']; exact hJ) hw' hb' hinv'' hown' hsh' hini' hfi' hgm' hgi'
      (by rw [hst']; exact hoo') (hV hheap' (hai''.retarget (fun w h => by cases h) fun w h => by cases h))
      (by rw [hna']; exact hfr'') (ctrOff_alloc hok hco hland) ⟨_, reach_run hreach hrun2⟩ (.inl trivial)
      hcrJ hcrJ (.refl _)
    exact ⟨s₃, run_trans0 hrun2 hrun3, hpre⟩

/-- **A certification step at a system call other than the output `write`
keeps `PreCoreJA`**, for rows under any `msOfAX … ab` (`core_sysA`;
`NodesA.sysRowX`): the row's frame run, then the local run to the
successor, the promises and the memory kept. -/
theorem core_sysAX (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowX hT hI hs hnw
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **A certification step at a `clone` has no successful outcome**
(`soloExec` leaves no state there; `Handover.prom_nil_of_clone`'s
argument, for one step). -/
theorem certSem_step_clone_none {th : Thread isaLSE2} {mem : Memory} {x : Kernel.KState}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {st tl : Nat}
    (hsi : Kernel.siteAt abi μ th.st = none) (hs : abi.atSys th.st = true)
    (hd : Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.clone st tl))
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) :
    .ok o ∉ outs := by
  intro ho
  obtain ⟨tree, st', c', hex, hr, -, -⟩ := stepOneWith_runOut Arch.armv8 hso ho
  have hex' : (Kernel.certSem abi Arch.armv8 μ x 0).exec th.st = some (Kernel.leaves []) := by
    change Kernel.soloExec abi Arch.armv8 μ x 0 th.st = _
    simp only [Kernel.soloExec, hsi, hs, ite_true, hd]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, -⟩ := (Lower.run_choose_iff Arch.armv8 0 _).mp hr
  exact i.elim0

/-- **A certification step at a system call off the output `write` and off
`Cl` keeps `PreCoreJA`**, for rows under any `msOfAX … ab` and `NodesA … Cl`
(`core_sysAX` with `NodesA.sysRowXC`). -/
theorem core_sysAXC (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hcl' : ¬ Cl th.st)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowXC hT hI hs hnw hcl'
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **A certification step at a system call keeps `PreCoreJA`**
(`core_sysS` with the arena): the row's frame run, then the local run to the
successor, the promises and the memory kept. -/
theorem core_sysA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRow hT hI hs
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **The certification step at a transfer site keeps `PreCoreJA`**
(`core_siteS` with the arena; the take's local run keeps the promises and
the memory). -/
theorem core_siteA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st ≠ none)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  have ha : μ.site .take = some (pcOf th.st) := Classical.byContradiction fun hne =>
    hsi (Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hne h, fun h => hN.noSite _ _ _ _ _ hI _ h rfl⟩)
  have hsa : Kernel.siteAt abi μ th.st = some .take := by
    unfold Kernel.siteAt; exact ite_eq_left ha
  obtain ⟨-, ⟨sz, hcn⟩, hsys, hsr, -, -, -, hrun⟩ := hT.site _ _ _ _ _ hI _ ha rfl
  obtain ⟨hot, hom⟩ := Kernel.certSem_step_take_out hsa hsys (A64.deps_of_atNop (atNop_of_cellAt hcn)) hso ho
  rw [hsr] at hot
  rw [hot, hom]
  obtain ⟨c', fs', hr1, hI', -⟩ := hrun x.pmem
  exact core_localA (J := I) hP hs0 hσ hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hsh hini hfi hgm hgi
    (by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
        rw [hN.ownRun _ _ _ _ _ _ _ hr1 (.inr hI'), hN.ownTake _ _ _ _ _ hI _ ha rfl]; exact hoo)
    (allocInvAt_prom (allocInvAt_frameRun hai hr1) rfl) hfr hco hre hhi hcr
    (fun h0' => by
      have h0'' : fs' = [] := h0'
      rw [h0''] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **Every instruction step off a system call and off the transfer sites
keeps `PreCoreJA`** (the form of `stepG_of`'s `hins`), by `core_stepA`. -/
theorem core_insA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK) :
    ∀ th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = false → stepOne Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
      ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  intro th mem s outs o h hsi hns hso ho
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc =>
    (Kernel.siteAt_eq_none_iff.mp hsi).1 (by rw [ha, ← hpc]; rfl)
  obtain ⟨s', -, h'⟩ := core_stepA hP hN hsafe hrd hwf hGpl hok h hns hnt hso ho
  exact ⟨s', h'⟩

/-- **`PromSharedA` from the node obligations**, for rows under any
`msOfAX … ab` (`promSharedS` with the arena), the certification steps at the
output `write` keeping the core by `hwr`: `PreCoreJA` is the certification
run's invariant (`A64PromShared.stepG_of`), and a certified promise from `PreSA` lands in it
(`pre_core_promiseA`). -/
theorem promSharedAX (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.armv8 μ k 0).step Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedA Λ P p G own I rS Tk μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (A64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · exact (core_sysAX hP hN hT h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hso ho).imp fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteA hP hN hT h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseA hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PromSharedA` from the node obligations under `NodesA … ab Cl`**
(`promSharedAX`), every `Cl` state at a `clone` (`hClc`): there the
certification step has no outcome (`certSem_step_clone_none`); elsewhere
`core_sysAXC`. -/
theorem promSharedAXC (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.armv8 μ k 0).step Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedA Λ P p G own I rS Tk μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (A64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · by_cases hcl : Cl th.st
          · obtain ⟨st, tl, hd⟩ := hClc _ hcl
            exact absurd ho (certSem_step_clone_none hsi hs hd hso)
          · exact (core_sysAXC hP hN hT h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hcl hso ho).imp
              fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteA hP hN hT h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseA hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PromSharedA` from the node obligations** (`promSharedS` with the
arena): `promSharedAX` at `ab = none`, every system call's row by
`core_sysA`. -/
theorem promSharedA (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) :
    PromSharedA Λ P p G own I rS Tk μ ar :=
  promSharedAX hP hN hsafe hrd hwf hGpl hok hT fun _ _ _ _ _ _ h hsi hs _ hso ho =>
    (core_sysA hP hN hT h hsi hs hso ho).imp fun _ h => h.2

/-- **`PreJA` gives `PreCoreJA`** of its one thread and the memory. Over `HeldPathS`. -/
theorem pre_coreAH {J : InvS} {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    {th : Thread isaLSE2} (h : PreJAH Λ P p G own J H μ ar t s) (hth : t.1.threads = #[th]) :
    PreCoreJA Λ P p G own J ar th t.1.mem s := by
  obtain ⟨th', th0, -, lbl, lsize, ts, -, -, hd, hth', -, -, -, -, -, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown,
    hmi, hfi, hgi, hoo, hai, hfr, hco, hre⟩ := h
  obtain rfl : th = th' := (get_one hth (show t.1.threads[0]? = some th' by rw [hth']; rfl)).2
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, MsgsExcept.of_all hmi.1 _, hmi.2,
    hfi, MemInv.msgsExcept hgi _, hgi.1, hoo, hai, hfr, hco, hre⟩

/-- **`PreSA` followed by a certified promise gives `PreCoreJA`** of the
promising thread and the memory with the promise (`pre_core_promiseS` with
the arena, `AllocInvAt.promise`). Over `HeldPathS`. -/
theorem pre_core_promiseAH {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2}
    {w : Msg} (h : PreSAH Λ P p G own I H μ ar t s) (hth : t.1.threads = #[th]) (hwt : w.tid = 0)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1) :
    PreCoreJA Λ P p G own I ar (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1 s := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := pre_coreAH h hth
  have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩,
    hinv.promise_cert_on (soloWide8CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc, ownMsgs_append hwt hown,
    msgsExcept_promise hsh w, hini,
    ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
    msgsExcept_promise hgm w,
    hgi, ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hai.promise w rfl,
    hfr, hco, hre⟩

/-- **A certification step at a system call other than the output `write`
keeps `PreCoreJA`**, for rows under any `msOfAX … ab` (`core_sysA`;
`NodesA.sysRowX`): the row's frame run, then the local run to the
successor, the promises and the memory kept. Over `TakeSiteS`. -/
theorem core_sysAXT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hT : TakeSiteS p μ I) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowXT hT hI hs hnw
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **A certification step at a system call off the output `write` and off
`Cl` keeps `PreCoreJA`**, for rows under any `msOfAX … ab` and `NodesA … Cl`
(`core_sysAX` with `NodesA.sysRowXC`). Over `TakeSiteS`. -/
theorem core_sysAXCT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hcl' : ¬ Cl th.st)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowXCT hT hI hs hnw hcl'
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **A certification step at a system call keeps `PreCoreJA`**
(`core_sysS` with the arena): the row's frame run, then the local run to the
successor, the promises and the memory kept. Over `TakeSiteS`. -/
theorem core_sysAT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I)
    (hT : TakeSiteS p μ I) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowT hT hI hs
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **The certification step at a transfer site keeps `PreCoreJA`**
(`core_siteS` with the arena; the take's local run keeps the promises and
the memory). Over `TakeSiteS`. -/
theorem core_siteAT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {th : Thread isaLSE2} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st ≠ none)
    (hso : (Kernel.certSem abi Arch.armv8 μ x 0).step Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  have ha : μ.site .take = some (pcOf th.st) := Classical.byContradiction fun hne =>
    hsi (Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hne h, fun h => hN.noSite _ _ _ _ _ hI _ h rfl⟩)
  have hsa : Kernel.siteAt abi μ th.st = some .take := by
    unfold Kernel.siteAt; exact ite_eq_left ha
  obtain ⟨⟨sz, hcn⟩, hsys, hrun⟩ := hT.site _ _ _ _ _ hI _ ha rfl
  obtain ⟨hot, hom⟩ := Kernel.certSem_step_take_out hsa hsys (A64.deps_of_atNop (atNop_of_cellAt hcn)) hso ho
  rw [hot, hom]
  obtain ⟨c', fs', hr1, hI'⟩ := hrun x.pmem
  exact core_localA (J := I) hP hs0 hσ hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hsh hini hfi hgm hgi
    (by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
        rw [hN.ownRun _ _ _ _ _ _ _ hr1 (.inr hI'), hN.ownTake _ _ _ _ _ hI _ ha rfl]; exact hoo)
    (allocInvAt_prom (allocInvAt_frameRun hai hr1) rfl) hfr hco hre hhi hcr
    (fun h0' => by
      have h0'' : fs' = [] := h0'
      rw [h0''] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **`PromSharedA` from the node obligations**, for rows under any
`msOfAX … ab` (`promSharedS` with the arena), the certification steps at the
output `write` keeping the core by `hwr`: `PreCoreJA` is the certification
run's invariant (`A64PromShared.stepG_of`), and a certified promise from `PreSA` lands in it
(`pre_core_promiseA`). Over `HeldPathS`. -/
theorem promSharedAXH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.armv8 μ k 0).step Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedAH Λ P p G own I H μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (A64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · exact (core_sysAXT hP hN hT.toTakeSiteS h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hso ho).imp fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteAT hP hN hT.toTakeSiteS h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseAH hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PromSharedA` from the node obligations under `NodesA … ab Cl`**
(`promSharedAX`), every `Cl` state at a `clone` (`hClc`): there the
certification step has no outcome (`certSem_step_clone_none`); elsewhere
`core_sysAXC`. Over `HeldPathS`. -/
theorem promSharedAXCH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.armv8 μ k 0).step Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedAH Λ P p G own I H μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (A64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · by_cases hcl : Cl th.st
          · obtain ⟨st, tl, hd⟩ := hClc _ hcl
            exact absurd ho (certSem_step_clone_none hsi hs hd hso)
          · exact (core_sysAXCT hP hN hT.toTakeSiteS h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hcl hso ho).imp
              fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteAT hP hN hT.toTakeSiteS h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseAH hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PromSharedA` from the node obligations** (`promSharedS` with the
arena): `promSharedAX` at `ab = none`, every system call's row by
`core_sysA`. Over `HeldPathS`. -/
theorem promSharedAH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) :
    PromSharedAH Λ P p G own I H μ ar :=
  promSharedAXH hP hN hsafe hrd hwf hGpl hok hT fun _ _ _ _ _ _ h hsi hs _ hso ho =>
    (core_sysAT hP hN hT.toTakeSiteS h hsi hs hso ho).imp fun _ h => h.2


end Spike.Lib.A64ConsumerA
