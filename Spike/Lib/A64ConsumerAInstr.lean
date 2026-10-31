/-
**An instruction step of the allocation-capable consumer**
(`Spike/Lib/A64ConsumerA.lean`): from `PreJA`, an instruction outcome off
the take site and off a system call is matched by a source run landing in
`RSA` (`instr_stepA`, `pre_stepS`'s instruction case with the arena).

The row is the counter's add when the outcome writes the counter word
(`NodesA.ctrRow`: `CtrRow`, `CtrRows.ctrRmw_row`; the source stutters into
the hold of the old count, the heap use, `allocInvAt_ctrS`, at a buffer or
a box). At the box's initialising store (`NewStM`) the source allocates the
box at the fresh label at the heap use (`newSt_src`,
`HeapLandN.new_rowA`). Otherwise it is `NodesA.row`'s with no box rows
(`Out.unnew`), not the counter's add (`CtrRows.out_localW`,
`CtrRows.out_memW`), its write one the arena allows (`NodesA.arena`,
`allocInvAt_out`); the rows as in `pre_stepS`, and the allocation's last
instruction (`Out.alloc`): the source allocates at the fresh label at the
heap use (`HeapLand.alloc_rowS`), landing in the fragment with the label
placed (`msOfA`'s `xa`).

- `TakePathS.ownedA`, `heapUse_store`, `ctr_ne_of_wordAddr`, `ctrOff_alloc`: helpers.
- `newSt_src`: the box's store, source side.
- `instr_stepA`: the instruction case; `instr_stepAH` over `HeldPathS`.
-/
import Spike.Lib.A64ConsumerAMem
import Spike.Lib.A64ConsumerAPub
import Spike.Lib.A64ConsumerASys
import Scc.Sem.FixInv
import Spike.Lib.HeapLandN

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.CtrRows (CtrW)

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena}

/-- A pair with a pending run into the fragment has its state owned when
taken (`TakePathS.owned`, over `PendA`). -/
theorem _root_.Spike.Lib.A64ConsumerS.TakePathS.ownedA {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : PendA p I lbl lsize s c fs) (hk : Tk s) :
    Owned Λ rS s := by
  obtain ⟨c', fs', h'⟩ := h.inv; exact hT.owned _ _ _ _ _ h' hk

/-- **The source store keeps the heap use**: the message pushed at a
location the memory has, the thread's allocation count and box label kept
(`HeapPres.heapUse_push_old`). -/
theorem heapUse_store {s : TermRun.Cfg} {th th' : TermRun.TTh} (hi : s.ths[0]? = some th) {sa : WeakMem.Address}
    {k : Nat} {m : WeakMem.Msg} (hkm : s.mem[k]? = some m) (hml : m.loc = sa) {v : WeakMem.Val} {mv : Nat}
    (hn : th'.nalloc = th.nalloc) (ht : th'.tidLbl = th.tidLbl) :
    heapUse { s with mem := s.mem.push ⟨sa, v, mv⟩, ths := s.ths.set! 0 th' } = heapUse s := by
  refine HeapPres.heapUse_push_old rfl ⟨m, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm), hml⟩ ?_
    (BoxCount.boxCount_set hi rfl ht)
  have : allocCount { s with mem := s.mem.push ⟨sa, v, mv⟩, ths := s.ths.set! 0 th' } =
      allocCount { s with ths := s.ths.set! 0 th' } := rfl
  rw [this, HeapPres.allocCount_set hi hn]

/-- **A placed word is not the counter** (`CtrOff`). -/
theorem ctr_ne_of_wordAddr {lbl : Lbl} {lsize : Lsize} (hco : CtrOff ar lbl lsize) {sa : WeakMem.Address}
    {a : Nat} (ha : wordAddr lbl sa = some a) (ho : sa.offset < lsize sa.label) : a ≠ ar.ctr := by
  rintro rfl
  obtain ⟨b, hb, hc⟩ := lrange_contains_of_wordAddr ha ho
  exact hco _ _ hb hc

/-- **The counter word stays off every placed label** when an allocation
places a label `l` at a base `b` the arena fits (`AllocLand`): the new range
lies in the arena, the counter off it (`Arena.OK.ctr_out`). -/
theorem ctrOff_alloc (hok : ar.OK) {lbl : Lbl} {lsize : Lsize} (hco : CtrOff ar lbl lsize) {l : WeakMem.AllocLabel}
    {b n : Nat} (hl : HeapLand.AllocLand ar.heap ar.cells b n) :
    CtrOff ar (fun l' => if l' = l then some b else lbl l') (fun l' => if l' = l then n else lsize l') := by
  intro l' b' hb' hc
  by_cases he : l' = l
  · subst he
    simp only [↓reduceIte, Option.some.injEq] at hb'
    subst hb'
    obtain ⟨hlo, hhi, -⟩ := hl
    have := hok.ctr_out
    simp only [lrange, Range.contains, ↓reduceIte] at hc
    omega
  · simp only [he, ite_false] at hb'
    refine hco l' b' hb' ?_
    simpa only [lrange, he, ite_false] using hc

/-- The outcome's write of the counter's add is a write of the counter word
(`Writes`). -/
theorem writes_of_ctrW {th : Thread isaLSE2} {tm : Memory} {o : Outcome isaLSE2} {new : Val}
    (h : CtrW th tm o 0 ar.ctr new) : Writes th tm o ar.ctrLoc := by
  rcases h with ⟨q, hq, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · exact ⟨new, .inr ⟨q, hq, hg, hm, hp⟩⟩
  · exact ⟨new, .inl ⟨hm, hp⟩⟩

/-- **The box's initialising store, source side** (`NewStM` at the row's
pair, `HeapLandN.new_rowA`): after the row's frame run, the source allocates
the box at the fresh label at the heap use; the landing's fragment holds with
the label placed (`msOfA`'s `xa`), `Inv1`, `AllocInvAt` idle at the new heap
use, `FreshInv` and `CtrOff` with the label placed, and the outcome's write
is the box word, shared and in `G`, appended or fulfilling a promise. -/
theorem newSt_src {ab : Option (State → Prop)} {Cl : State → Prop} (hP : HookOK P p)
    (hN : NodesA Λ p μ rd G own ar I ab Cl) (hsafe : SrcSafeS P p I)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {s : TermRun.Cfg} {th0 : TermRun.TTh} {th : Thread isaLSE2} {mem : Memory} {lbl : Lbl} {lsize : Lsize}
    {ts : Nat → Option Nat} {c₁ : Ctl} {fs₁ : List TermRun.Frame} {tr : List Ev}
    (hs0 : s.ths = #[th0]) (hσ : th0.σs = []) (hp : th0.promises = [])
    (hinv : Inv1 Λ lbl lsize ts th mem s.mem)
    (hai1 : AllocInvAt Λ lbl lsize th mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c₁)
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hreach : (SrcSem.source P p).Reach tr s)
    (hrun1 : (SrcSem.source P p).Run s [] { s with ths := #[thAt th0 c₁ fs₁] })
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 th 0 mem = some outs) (ho : .ok o ∈ outs)
    (hNS : NewStM p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) th.st c₁) :
    ∃ (lbl' : Lbl) (lsize' : Lsize) (ts' : Nat → Option Nat) (th' : TermRun.TTh) (sm : WeakMem.Memory) (L : Loc)
      (V : Val),
      (SrcSem.source P p).Run s [] { s with mem := sm, ths := #[th'] } ∧
      I lbl' lsize' o.thread.st ⟨th'.term, th'.env, none⟩ th'.stack ∧
      th'.σs = [] ∧ th'.promises = [] ∧ th'.stack = fs₁ ∧ (th'.stack = [] → ∀ a, th'.term ≠ .ret a) ∧
      Inv1 Λ lbl' lsize' ts' o.thread o.mem sm ∧
      AllocInvAt Λ lbl' lsize' o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off
        (heapUse ({ s with mem := sm, ths := #[th'] } : TermRun.Cfg)) ⟨th'.term, th'.env, none⟩ ∧
      AllocInv.FreshInv lbl' ({ s with mem := sm, ths := #[th'] } : TermRun.Cfg).lbase
        ({ s with mem := sm, ths := #[th'] } : TermRun.Cfg).n 0 th'.nalloc ∧
      CtrOff ar lbl' lsize' ∧ LocIn Λ.shared L ∧ G L V ∧
      ((o.mem = (mem.append ⟨L, V, 0⟩).1 ∧ o.thread.prom = th.prom) ∨
        ∃ q ∈ th.prom, mem.get? q = some ⟨L, V, 0⟩ ∧ o.mem = mem ∧ o.thread.prom = th.prom.erase q) := by
  obtain ⟨kr, A, V, s', x, a, ty, e, w, wold, old, -, hex, hmp, ⟨_, ht⟩, hev, hu, hv, hh, hold, hAeq, hcl, hX⟩ := hNS
  have hh' : c₁.hold = some (ar.ctr, wold) := hh
  have hAeq' : A.toNat = ar.heap + 16 * old + ar.off 1 ty := hAeq
  have hcl' : old + ar.units 1 ty ≤ ar.cells := hcl
  have hX' : ∀ l, lbl l = none → HeapLand.AllocLand ar.heap ar.cells A.toNat 1 ∧
      I (fun l' => if l' = l then some A.toNat else lbl l') (fun l' => if l' = l then 1 else lsize l') s'
        ⟨e, (x, .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c₁.env, none⟩ fs₁ := hX
  have hL0 : LocIn Λ.shared ⟨A, 8⟩ := hmp.2 rfl
  have hheap1 : heapUse { s with ths := #[thAt th0 c₁ fs₁] } = heapUse s := heapUse_one hs0 rfl rfl
  have hfr1 : AllocInv.FreshInv lbl ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).lbase
      ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).n 0 (thAt th0 c₁ fs₁).nalloc :=
    freshInv_one hs0 rfl rfl rfl rfl hfr
  obtain ⟨hland, hJ⟩ := hX' _ (hfr1 _ (Nat.le_refl _))
  have h1w : TermRun.nWords [.one] = 1 := rfl
  have fit1 : 1 * TermRun.nWords [.one] + 1 ≤ ar.cells := by have := hland.2.2; rw [h1w]; omega
  have hus : TermRun.accs (TermRun.close [] ty) = some [.one] := by rw [Spike.Lib.close_nil]; exact hu
  have hun : ar.units 1 ty = 2 := by rw [hok.units 1 ty [.one] hus fit1, h1w]
  obtain ⟨hoff, -, hoffit⟩ := hok.off 1 ty [.one] hus fit1
  have hfit : ar.off 1 ty + 8 * 1 ≤ 16 * ar.units 1 ty := by rw [h1w] at hoffit; omega
  have hb : wordLoc (ar.heap + 16 * old + ar.off 1 ty) ≠ wordLoc ar.ctr := by
    rw [← hAeq', wordLoc_toNat]
    intro heq
    have h2 := congrArg (fun L : Loc => L.addr.toNat) heq
    simp only [wordLoc, BitVec.toNat_ofNat] at h2
    rw [Nat.mod_eq_of_lt hok.ctr_lt] at h2
    have := hok.ctr_out
    have := hland.1
    have := hland.2.1
    omega
  have hexA := hex
  rw [← wordLoc_toNat A] at hexA
  have hexec := hexA
  rw [hAeq'] at hexec
  have hpl : ∀ q ∈ th.prom, q ≤ mem.last := fun q hq => (hinv.mem.tq_le q hq).2
  obtain ⟨-, hwr⟩ := stepOne_store_cases Arch.armv8 hexA hso ho hpl
  obtain ⟨hold', mv, th', hstep, hte, hen, hp', hσ', hst', hna', htl', hst_o, hheap', ⟨q, hinv''⟩, hai'', hfr''⟩ :=
    HeapLandN.new_rowA (kn := P.k) (arch := P.arch) (p := p) (c' := (⟨e, [], none⟩ : Ctl))
      (s := { s with ths := #[thAt th0 c₁ fs₁] }) (th := thAt th0 c₁ fs₁) (by rw [hheap1]; exact hai1) hinv rfl rfl
      rfl hfr1 (TermRun.Cfg.lt_n (by simp)) ht hev hu hp hh' hold hcl' hun hoff hfit
      (hsafe.box _ _ (reach_run hreach hrun1)) Arch.armv8 hexec hso ho hpl hb hv rfl
  have hG : G (wordLoc A.toNat) V := by
    refine hGpl _ V (heapData_of_wordAddr hinv''.mem
      (sa := ⟨TermRun.freshLabel ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).lbase
        ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg).n 0 (thAt th0 c₁ fs₁).nalloc, 0⟩) ?_ ?_)
    · simp [Scc.Sem.wordAddr, hAeq', hold']
    · simp
  rw [hAeq', hold'] at hJ hland
  have hcrJ : th'.stack = [] → ∀ a, th'.term ≠ .ret a := fun h0' => by
    have hf : fs₁ = [] := by rw [hst'] at h0'; exact h0'
    subst hf
    rw [hte]; exact hN.noRet _ _ _ _ hJ
  have hx : mainExit ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg) = [] :=
    mainExit_of_not_ret rfl fun a' h => by
      have h' : c₁.term = .ret a' := h
      rw [ht] at h'; cases h'
  have hstep' := src_step_of_threadSteps hP hstep (by simp) hp' hx (mainExit_of_pair (by simp) hcrJ)
  refine ⟨_, _, _, th', _, wordLoc A.toNat, V, run_trans0 hrun1 (run_one hstep'), ?_, hσ'.trans hσ, hp', hst',
    hcrJ, hinv'', ?_, ?_, ctrOff_alloc hok hco hland, by rw [wordLoc_toNat]; exact hL0, hG, ?_⟩
  · rw [hst_o, hte, hen, hst']; exact hJ
  · rw [show heapUse ({ s with mem := _, ths := #[th'] } : TermRun.Cfg) = _ from hheap']
    exact hai''.retarget (fun w h => by cases h) fun w h => by cases h
  · rw [hna']; exact hfr''
  · rcases hwr with ⟨q, hq, hg, -, hm, hpr⟩ | ⟨hm, hpr⟩
    · exact .inr ⟨q, hq, hg, hm, hpr⟩
    · exact .inl ⟨hm, hpr⟩

/-- info: 'Spike.Lib.A64ConsumerA.newSt_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms newSt_src

/-- **An instruction step from `PreJA`** (`pre_stepS`'s instruction case
with the arena): the outcome `o` of the instruction at a pair of the
fragment off the take site and off a system call is matched by a source run
landing in `RSA`. -/
theorem instr_stepA {ab : Option (State → Prop)} {Cl : State → Prop} (hP : HookOK P p)
    (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) (hrd : SrcRd P p rd)
    (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} {th0 : TermRun.TTh} {lbl : Lbl} {lsize : Lsize}
    {ts : Nat → Option Nat} {hl : List (Nat × Range)} {pm : _root_.Mem 64} {hd : Option (Nat × TermRun.Word)}
    {E : Entry} {tr : List Ev}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : HeldOk Λ rS Tk th.st hl) (hs0 : s.ths = #[th0]) (hσ : th0.σs = []) (hp : th0.promises = [])
    (hI : I lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack) (hhi : HoldInvA ar lbl lsize s.mem hd)
    (hw : WideSt th.st) (hb : th.Bnd t.1.mem.last) (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem)
    (hown : OwnMsgs t.1.mem) (hmi : MemIn Λ t.1.mem) (hfi : MemFits t.1.mem) (hgi : MemInv G t.1.mem)
    (hoo : ExtRows.OwnOk (own th.st th0.stack) t.1.mem th.prom)
    (hai : AllocInvAt Λ lbl lsize th t.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s)
      ⟨th0.term, th0.env, hd⟩)
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hreach : (SrcSem.source P p).Reach tr s)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a) (hns : abi.atSys th.st = false)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 th 0 t.1.mem = some outs) (ho : .ok o ∈ outs) (hw' : WideSt o.thread.st)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧
      RSA Λ P p G own I rS Tk μ ar (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  have hth' := withThread_one (u := o.thread) (mem := o.mem) hth
  have hsn := siteAt_noneA hN hI hnt
  have hi := (stepOne_allInv Arch.armv8 hso ho (hT.instr _ _ _ _ _ hI hsn hns) ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  have hb' := (stepOne_bnd _ hso ho hb).1
  have hfi' : MemFits o.mem := by
    refine ⟨fits_stepOne Arch.armv8 (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
      hso ho hfi.1, ?_⟩
    unfold InitFits; rw [(stepOne_dord _ hso ho).2.2.1.1]; exact hfi.2
  have hown' := ownMsgs_step hso ho hown
  obtain ⟨c₁, fs₁, hr0, hown_eq, hout⟩ := hN.rowNS hI hnt hns
  have hI1 : IRun p I lbl lsize th.st c₁ fs₁ := IRun.trans hI hr0
  have hoo₁ : ExtRows.OwnOk (own th.st fs₁) t.1.mem th.prom := by rw [hown_eq]; exact hoo
  have hsrc : (fs₁ = [] → ∀ a, c₁.term ≠ .ret a) →
      (SrcSem.source P p).Run s [] { s with ths := #[thAt th0 c₁ fs₁] } :=
    fun hr1 => frun_one hP hr0 hs0 rfl rfl hσ rfl hp hcr hr1
  have hai1 := allocInvAt_frameRun hai hr0
  have hhi1 : HoldInvA ar lbl lsize s.mem c₁.hold := holdInvA_frameRun hr0 hhi
  have hnd : th.prom.Nodup := hinv.mem.tq_nodup
  have hpl : ∀ q ∈ th.prom, q ≤ t.1.mem.last := fun q hq => (hinv.mem.tq_le q hq).2
  have hoo' : ExtRows.OwnOk (own o.thread.st fs₁) o.mem o.thread.prom := by
    obtain ⟨tree, hex⟩ := Option.isSome_iff_exists.mp (Out.exec_isSome rfl hns hout)
    exact ownOk_step hex (hN.ownInstr _ _ _ _ _ hI1 hns tree hex) hinv.coh hinv.mem.tq_nodup
      (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo₁
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
    have hmi' : MemIn Λ o.mem := by rw [hm]; exact hmi
    have hfi'' : MemFits o.mem := by rw [hm]; exact hfi
    have hgi' : MemInv G o.mem := by rw [hm]; exact hgi
    obtain ⟨s₃, hrun3, hpre⟩ := pre_localJA (J := PendA p I) (t' := (t.1.withThread 0 o.thread o.mem, t.2))
      (th0 := th') (hd := none) hP hth' hk hz (hh.of_iff hi (hT.ownedA hX)) hc hs2 (hσ'.trans hσ) hp' hX hw' hb' hinv' hown' hmi'
      hfi'' hgi' hoo' (by
        rw [HeapPres.heapUse_set (s := { s with ths := #[thAt th0 c₁ fs₁] })
          (s' := { ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg) with
            ths := (#[thAt th0 c₁ fs₁] : Array TermRun.TTh).set! 0 th' }) (th' := th') (i := 0) rfl rfl rfl hna htl,
          hheap1]
        exact hai2)
      (freshInv_one hs0 hs2 rfl rfl hna hfr) hco ⟨_, reach_run hreach hrun⟩ (.inl trivial)
      (fun h a => by rw [hte]; exact hnr (hsk.symm.trans h) a) hX.noRet hrL'
    exact pend_landA hP hN (run_trans0 hrun hrun3) hpre
  -- no publication: the row is one under the memory side with none
  obtain ⟨ex, ha⟩ := hai1.arenaOK
  have hGm := MemInv.msgsExcept hgi th.prom
  by_cases hwc : Writes th t.1.mem o ar.ctrLoc
  · -- the counter's add: the source stutters into the hold of the old count
    obtain ⟨k, op, g, x, τ, e, n, hex, hrt, hmp, hs, hh0, hop, hX⟩ :=
      hN.ctrRow _ _ _ _ _ hI1 hns th t.1.mem outs o rfl hso ho hwc
    obtain ⟨old, ⟨trc, hlat, hrd'⟩, hown0, hland, hinv', hcw⟩ :=
      CtrRows.ctrRmw_row (I := isaLSE2) (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
        (mown := fun st => own st fs₁)
        (Y := fun old s' => PendA p I lbl lsize s'
          { c₁ with hold := some (ar.ctr, TermRun.cst (.num (old.setWidth 64).toNat)) } fs₁)
        hinv hso ho hGm hgi.1 hoo₁ hex
        (show (msOfA0 Λ μ rd G own ar I lbl lsize fs₁).rt (BitVec.ofNat 64 ar.ctr).toNat from hrt) hop
        hX
    obtain ⟨hold64, hai'⟩ := allocInvAt_ctrS hok hai1 hh0 hnd hpl hlat hrd' hs.toTrue hcw
    have hle : (old.setWidth 64).toNat ≤ ar.cells := by rw [hold64]; exact ha.hu_le
    have hlo : Spike.Lib.AllocLo.LoOf ar.heap ar.cells lbl lsize (old.setWidth 64).toNat := by
      rw [hold64]; exact Spike.Lib.AllocLo.loOf_of_arenaOK ha
    have hX' := hland hle hlo
    rw [hold64] at hX'
    have hGold := msgsExcept_read_tlatestP hGm hgi.1 hlat hrd'
    have hGnew := (hX old hGold hown0 hle hlo).1
    have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
      rcases hcw with ⟨-, -, -, -, hm, -⟩ | ⟨hm, -⟩
      · rw [hm]; exact ⟨hmi, hgi⟩
      · rw [hm]; exact ⟨memIn_append (hmp.2 rfl) hmi, hgi.append hGnew⟩
    have hrun1 := hsrc fun _ => hs.not_ret
    refine pend_landA hP hN hrun1 ⟨o.thread, thAt th0 c₁ fs₁, 0, lbl, lsize, ts, hl, pm,
      some (ar.ctr, TermRun.cst (.num (heapUse s))), hth', ⟨E, hk⟩, hz, hh.of_iff hi (hT.ownedA hX'), .inl rfl,
      hc, rfl, hσ, hp, hX', .inr ⟨_, rfl⟩, hw', hb', hinv', hown', hmg.1, hfi', hmg.2, hoo', ?_, hfr1, hco, _,
      reach_run hreach hrun1⟩
    rw [hheap1]; exact hai'
  by_cases hNS : NewStM p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) th.st c₁
  · -- the box's initialising store: the source allocates the box at the fresh label at the heap use
    obtain ⟨lbl', lsize', ts', th', sm, L, V, hrun2, hJ, hσ', hp', hst', hcrJ, hinv'', hai'', hfr'', hco', hL, hG,
      hwr⟩ := newSt_src hP hN hsafe hGpl hok hs0 hσ hp hinv hai1 hfr hco hreach (hsrc fun _ => hNS.not_ret) hso ho hNS
    have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
      rcases hwr with ⟨hm, -⟩ | ⟨-, -, -, hm, -⟩
      · rw [hm]; exact ⟨memIn_append (w := ⟨L, V, 0⟩) hL hmi, hgi.append hG⟩
      · rw [hm]; exact ⟨hmi, hgi⟩
    obtain ⟨s₃, hrun3, hpre⟩ := pre_localJA (J := I) (t' := (t.1.withThread 0 o.thread o.mem, t.2))
      (s := { s with mem := sm, ths := #[th'] })
      (th0 := th') (hd := none) (c' := ⟨th'.term, th'.env, none⟩) (fs' := th'.stack) hP hth' hk hz
      (hh.of_iff hi (hT.owned _ _ _ _ _ hJ)) hc rfl hσ' hp' hJ hw' hb' hinv'' hown' hmg.1 hfi' hmg.2
      (by rw [hst']; exact hoo') hai'' hfr'' hco' ⟨_, reach_run hreach hrun2⟩ (.inl trivial) hcrJ hcrJ (.refl _)
    exact ⟨s₃, run_trans0 hrun2 hrun3, .inl hpre⟩
  -- not the box's store: the row is one with no box rows (the counter's add at a box refuted)
  have hout0 : Out p lbl (msOfA0 Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁)
      th.st c₁ := by
    rcases hout.unnew with h | ⟨k, op, g, n, τ, hex, hrt, hop, hX⟩ | h
    · exact absurd h hNS
    · obtain ⟨_, -, -, -, -, hcw⟩ := CtrRows.ctrRmw_row (I := isaLSE2) (mh := ar.heap) (mc := ar.ctr)
        (mu := ar.units) (mo := ar.off) (mcl := ar.cells) (mown := fun st => own st fs₁) (Y := fun _ _ => True)
        hinv hso ho hGm hgi.1 hoo₁ hex
        (show (msOfA0 Λ μ rd G own ar I lbl lsize fs₁).rt (BitVec.ofNat 64 ar.ctr).toNat from hrt) hop
        fun old h1 h2 h3 h4 => ⟨hX old h1 h2 h3 h4, trivial⟩
      exact absurd (writes_of_ctrW hcw) hwc
    · exact h
  -- not the counter's add: the write is one the arena allows
  have hmw := CtrRows.out_memW (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
    hinv hso ho hns (A64Ext.wide8_exec hw hns) hGm hgi.1 hoo₁ hout0
  have hai' : AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c₁ := by
    refine allocInvAt_out hai1 hnd ?_
    rcases hmw with hm | ⟨L, V, -, hwr, -⟩
    · exact .inl hm
    · have hW : Writes th t.1.mem o L := ⟨V, hwr⟩
      exact .inr ⟨L, hW, fun he => hwc (he ▸ hW),
        (hN.arena _ _ _ _ _ hI1 hns th t.1.mem outs o L rfl hso ho hW).resolve_right hNS⟩
  have hsrc1 : ∀ (hr1 : fs₁ = [] → ∀ a, c₁.term ≠ .ret a),
      (SrcSem.source P p).Reach (tr ++ []) { s with ths := #[thAt th0 c₁ fs₁] } :=
    fun hr1 => reach_run hreach (hsrc hr1)
  have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
    rcases hmw with ⟨hm, -⟩ | ⟨L, V, hL8, hwr, hL⟩
    · rw [hm]; exact ⟨hmi, hgi⟩
    rcases hwr with ⟨hm, hp'⟩ | ⟨-, -, -, hm, -⟩
    rotate_left
    · rw [hm]; exact ⟨hmi, hgi⟩
    rw [hm]
    have hLw := ExtRows.loc_wordLoc hL8
    have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
    rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
      ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨hLc, -, -, -, -⟩
    · exact ⟨memIn_append (hmp.2 rfl) hmi, hgi.append hGV⟩
    · obtain ⟨k, m, hkm, hml⟩ := hsafe.cell₁ (hsrc1 fun _ a' h => by rw [ht] at h; cases h)
        hI1 (.inr ⟨b, ht⟩) hev hsa
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      rw [hsa] at hv
      have hwa := wordAddr_of_valRep_loc0 hv
      refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
      · rw [h8] at hi
        exact shared_of_wordAddr hinv.mem hwa hoff i hi
      · show G L V
        rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
    · obtain ⟨k, m, hkm, hml⟩ := hsafe.xchg₁ (hsrc1 fun _ => xchgSite_not_ret hxs) hI1 hxs
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      have hwa := wordAddr_of_valRep_loc0 hA
      refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
      · rw [h8] at hi
        exact shared_of_wordAddr hinv.mem hwa hoff i hi
      · show G L V
        rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
    · subst hLc; exact absurd ⟨V, .inl ⟨hm, hp'⟩⟩ hwc
  obtain ⟨hmi', hgi'⟩ := hmg
  have hU : ∀ {x : TermRun.Cfg} {c : Ctl}, heapUse x = heapUse { s with ths := #[thAt th0 c₁ fs₁] } →
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c →
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse x) c :=
    fun he h => by rw [he, hheap1]; exact h
  rcases CtrRows.out_localW (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
      hinv hso ho hns (A64Ext.wide8_exec hw hns) hGm hgi.1 hoo₁ hout0 with
    ⟨c', hr, hX, hinv'⟩ |
    ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
    ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
    ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
    ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcw⟩ |
    ⟨s', A, x, a, τ, e, ta, ws, k, wold, old, us, hst, ht, hev, hk', hh0, hold, hA, hcl, hus, hX, hm, hinv'⟩
  · -- a local run: the row's run and the landing's pending run
    have hr1 := hr0.trans (FrameRun.ofLocal hr fs₁)
    obtain ⟨s', hrun, hpre⟩ := pre_localJA (J := PendA p I) (t' := (t.1.withThread 0 o.thread o.mem, t.2)) hP hth'
      hk hz (hh.of_iff hi (hT.ownedA hX)) hc hs0 hσ hp hX hw' hb' hinv' hown' hmi' hfi' hgi' hoo'
      (allocInvAt_frameRun hai' (FrameRun.ofLocal hr fs₁)) hfr hco ⟨tr, hreach⟩ hhi hcr hX.noRet hr1
    exact pend_landA hP hN hrun hpre
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
    refine pend_landA hP hN hrun ⟨o.thread, th', 0, lbl, lsize, ts, hl, pm, none, hth', ⟨E, hk⟩, hz,
      hh.of_iff hi (hT.ownedA (by rw [hgv]; exact hX')), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, .inl trivial,
      hw', hb', hinv', hown', hmi', hfi', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
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
    refine pend_landA hP hN hrun ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
      hh.of_iff hi (hT.ownedA (by rw [hst'']; exact hX)), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, .inl trivial,
      hw', hb', hinv', hown', hmi', hfi', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
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
    refine pend_landA hP hN hrun1 ⟨o.thread, thAt th0 c₁ fs₁, 0, lbl, lsize, ts, hl, pm,
      some (A.toNat, ⟨m.val, m.view, jl⟩), hth', ⟨E, hk⟩, hz, hh.of_iff hi (hT.ownedA (by rw [hgr]; exact hX')),
      .inl rfl, hc, rfl, hσ, hp, ?_, .inl ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv',
      hown', hmi', hfi', hgi', hoo', ?_, hfr1, hco, _, reach_run hreach hrun1⟩
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
    refine pend_landA hP hN hrun ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
      hh.of_iff hi (hT.ownedA (by rw [hst'']; exact hX)), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, .inl trivial,
      hw', hb', hinv', hown', hmi', hfi', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
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
    obtain ⟨s₃, hrun3, hpre⟩ := pre_localJA (J := I) (t' := (t.1.withThread 0 o.thread o.mem, t.2))
      (s := { s with mem := _, ths := #[th'] })
      (th0 := th') (hd := none) (c' := ⟨th'.term, th'.env, none⟩) (fs' := th'.stack) hP hth' hk hz
      (hh.of_iff hi (hT.owned _ _ _ _ _ hJ)) hc rfl (hσ'.trans hσ) (hp'.trans hp)
      (by rw [hte, hen, hst']; exact hJ) hw' hb' hinv'' hown' hmi' hfi' hgi' (by rw [hst']; exact hoo')
      (hV hheap' (hai''.retarget (fun w h => by cases h) fun w h => by cases h))
      (by rw [hna']; exact hfr'') (ctrOff_alloc hok hco hland) ⟨_, reach_run hreach hrun2⟩ (.inl trivial)
      hcrJ hcrJ (.refl _)
    exact ⟨s₃, run_trans0 hrun2 hrun3, .inl hpre⟩

/-- **An instruction step from `PreJAH`**, the ranges held by `H`
(`instr_stepA` over `HeldPathS`; `H` kept by `HeldPathS.instr` at the
landing in the fragment, given by `PendA.inv`): the outcome `o` of the instruction at a pair of the
fragment off the take site and off a system call is matched by a source run
landing in `RSAH`. -/
theorem instr_stepAH {ab : Option (State → Prop)} {Cl : State → Prop} (hP : HookOK P p)
    (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) (hrd : SrcRd P p rd)
    (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} {th0 : TermRun.TTh} {lbl : Lbl} {lsize : Lsize}
    {ts : Nat → Option Nat} {hl : List (Nat × Range)} {pm : _root_.Mem 64} {hd : Option (Nat × TermRun.Word)}
    {E : Entry} {tr : List Ev}
    (hth : t.1.threads = #[th]) (hk : t.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : H th.st hl) (hs0 : s.ths = #[th0]) (hσ : th0.σs = []) (hp : th0.promises = [])
    (hI : I lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack) (hhi : HoldInvA ar lbl lsize s.mem hd)
    (hw : WideSt th.st) (hb : th.Bnd t.1.mem.last) (hinv : Inv1 Λ lbl lsize ts th t.1.mem s.mem)
    (hown : OwnMsgs t.1.mem) (hmi : MemIn Λ t.1.mem) (hfi : MemFits t.1.mem) (hgi : MemInv G t.1.mem)
    (hoo : ExtRows.OwnOk (own th.st th0.stack) t.1.mem th.prom)
    (hai : AllocInvAt Λ lbl lsize th t.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s)
      ⟨th0.term, th0.env, hd⟩)
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hreach : (SrcSem.source P p).Reach tr s)
    (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a) (hns : abi.atSys th.st = false)
    {outs : List (Except String (Outcome isaLSE2))} {o : Outcome isaLSE2}
    (hso : stepOne Arch.armv8 th 0 t.1.mem = some outs) (ho : .ok o ∈ outs) (hw' : WideSt o.thread.st)
    (hc : CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 o.thread o.mem) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧
      RSAH Λ P p G own I H μ ar (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  have hth' := withThread_one (u := o.thread) (mem := o.mem) hth
  have hsn := siteAt_noneA hN hI hnt
  have hi := (stepOne_allInv Arch.armv8 hso ho (hT.instr _ _ _ _ _ _ hI hh hw hsn hns)
    ⟨fun _ => trivial, fun _ _ => trivial⟩).1
  have hHA : ∀ {c : Ctl} {fs : List TermRun.Frame}, PendA p I lbl lsize o.thread.st c fs → H o.thread.st hl :=
    fun h => by obtain ⟨c', fs', h'⟩ := h.inv; exact hi _ _ _ _ h'
  have hb' := (stepOne_bnd _ hso ho hb).1
  have hfi' : MemFits o.mem := by
    refine ⟨fits_stepOne Arch.armv8 (fun _ he => certExec_fit hw ((Kernel.certExec_of_not_atSys abi hns).trans he))
      hso ho hfi.1, ?_⟩
    unfold InitFits; rw [(stepOne_dord _ hso ho).2.2.1.1]; exact hfi.2
  have hown' := ownMsgs_step hso ho hown
  obtain ⟨c₁, fs₁, hr0, hown_eq, hout⟩ := hN.rowNS hI hnt hns
  have hI1 : IRun p I lbl lsize th.st c₁ fs₁ := IRun.trans hI hr0
  have hoo₁ : ExtRows.OwnOk (own th.st fs₁) t.1.mem th.prom := by rw [hown_eq]; exact hoo
  have hsrc : (fs₁ = [] → ∀ a, c₁.term ≠ .ret a) →
      (SrcSem.source P p).Run s [] { s with ths := #[thAt th0 c₁ fs₁] } :=
    fun hr1 => frun_one hP hr0 hs0 rfl rfl hσ rfl hp hcr hr1
  have hai1 := allocInvAt_frameRun hai hr0
  have hhi1 : HoldInvA ar lbl lsize s.mem c₁.hold := holdInvA_frameRun hr0 hhi
  have hnd : th.prom.Nodup := hinv.mem.tq_nodup
  have hpl : ∀ q ∈ th.prom, q ≤ t.1.mem.last := fun q hq => (hinv.mem.tq_le q hq).2
  have hoo' : ExtRows.OwnOk (own o.thread.st fs₁) o.mem o.thread.prom := by
    obtain ⟨tree, hex⟩ := Option.isSome_iff_exists.mp (Out.exec_isSome rfl hns hout)
    exact ownOk_step hex (hN.ownInstr _ _ _ _ _ hI1 hns tree hex) hinv.coh hinv.mem.tq_nodup
      (fun p hp => (hinv.mem.tq_le p hp).2) hso ho hoo₁
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
    have hmi' : MemIn Λ o.mem := by rw [hm]; exact hmi
    have hfi'' : MemFits o.mem := by rw [hm]; exact hfi
    have hgi' : MemInv G o.mem := by rw [hm]; exact hgi
    obtain ⟨s₃, hrun3, hpre⟩ := pre_localJAH (J := PendA p I) (t' := (t.1.withThread 0 o.thread o.mem, t.2))
      (th0 := th') (hd := none) hP hth' hk hz (hHA hX) hc hs2 (hσ'.trans hσ) hp' hX hw' hb' hinv' hown' hmi'
      hfi'' hgi' hoo' (by
        rw [HeapPres.heapUse_set (s := { s with ths := #[thAt th0 c₁ fs₁] })
          (s' := { ({ s with ths := #[thAt th0 c₁ fs₁] } : TermRun.Cfg) with
            ths := (#[thAt th0 c₁ fs₁] : Array TermRun.TTh).set! 0 th' }) (th' := th') (i := 0) rfl rfl rfl hna htl,
          hheap1]
        exact hai2)
      (freshInv_one hs0 hs2 rfl rfl hna hfr) hco ⟨_, reach_run hreach hrun⟩ (.inl trivial)
      (fun h a => by rw [hte]; exact hnr (hsk.symm.trans h) a) hX.noRet hrL'
    exact pend_landAH hP hN (run_trans0 hrun hrun3) hpre
  -- no publication: the row is one under the memory side with none
  obtain ⟨ex, ha⟩ := hai1.arenaOK
  have hGm := MemInv.msgsExcept hgi th.prom
  by_cases hwc : Writes th t.1.mem o ar.ctrLoc
  · -- the counter's add: the source stutters into the hold of the old count
    obtain ⟨k, op, g, x, τ, e, n, hex, hrt, hmp, hs, hh0, hop, hX⟩ :=
      hN.ctrRow _ _ _ _ _ hI1 hns th t.1.mem outs o rfl hso ho hwc
    obtain ⟨old, ⟨trc, hlat, hrd'⟩, hown0, hland, hinv', hcw⟩ :=
      CtrRows.ctrRmw_row (I := isaLSE2) (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
        (mown := fun st => own st fs₁)
        (Y := fun old s' => PendA p I lbl lsize s'
          { c₁ with hold := some (ar.ctr, TermRun.cst (.num (old.setWidth 64).toNat)) } fs₁)
        hinv hso ho hGm hgi.1 hoo₁ hex
        (show (msOfA0 Λ μ rd G own ar I lbl lsize fs₁).rt (BitVec.ofNat 64 ar.ctr).toNat from hrt) hop
        hX
    obtain ⟨hold64, hai'⟩ := allocInvAt_ctrS hok hai1 hh0 hnd hpl hlat hrd' hs.toTrue hcw
    have hle : (old.setWidth 64).toNat ≤ ar.cells := by rw [hold64]; exact ha.hu_le
    have hlo : Spike.Lib.AllocLo.LoOf ar.heap ar.cells lbl lsize (old.setWidth 64).toNat := by
      rw [hold64]; exact Spike.Lib.AllocLo.loOf_of_arenaOK ha
    have hX' := hland hle hlo
    rw [hold64] at hX'
    have hGold := msgsExcept_read_tlatestP hGm hgi.1 hlat hrd'
    have hGnew := (hX old hGold hown0 hle hlo).1
    have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
      rcases hcw with ⟨-, -, -, -, hm, -⟩ | ⟨hm, -⟩
      · rw [hm]; exact ⟨hmi, hgi⟩
      · rw [hm]; exact ⟨memIn_append (hmp.2 rfl) hmi, hgi.append hGnew⟩
    have hrun1 := hsrc fun _ => hs.not_ret
    refine pend_landAH hP hN hrun1 ⟨o.thread, thAt th0 c₁ fs₁, 0, lbl, lsize, ts, hl, pm,
      some (ar.ctr, TermRun.cst (.num (heapUse s))), hth', ⟨E, hk⟩, hz, (hHA hX'), .inl rfl,
      hc, rfl, hσ, hp, hX', .inr ⟨_, rfl⟩, hw', hb', hinv', hown', hmg.1, hfi', hmg.2, hoo', ?_, hfr1, hco, _,
      reach_run hreach hrun1⟩
    rw [hheap1]; exact hai'
  by_cases hNS : NewStM p lbl (msOfA Λ μ rd G own ar I lbl lsize fs₁) th.st c₁
  · -- the box's initialising store: the source allocates the box at the fresh label at the heap use
    obtain ⟨lbl', lsize', ts', th', sm, L, V, hrun2, hJ, hσ', hp', hst', hcrJ, hinv'', hai'', hfr'', hco', hL, hG,
      hwr⟩ := newSt_src hP hN hsafe hGpl hok hs0 hσ hp hinv hai1 hfr hco hreach (hsrc fun _ => hNS.not_ret) hso ho hNS
    have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
      rcases hwr with ⟨hm, -⟩ | ⟨-, -, -, hm, -⟩
      · rw [hm]; exact ⟨memIn_append (w := ⟨L, V, 0⟩) hL hmi, hgi.append hG⟩
      · rw [hm]; exact ⟨hmi, hgi⟩
    obtain ⟨s₃, hrun3, hpre⟩ := pre_localJAH (J := I) (t' := (t.1.withThread 0 o.thread o.mem, t.2))
      (s := { s with mem := sm, ths := #[th'] })
      (th0 := th') (hd := none) (c' := ⟨th'.term, th'.env, none⟩) (fs' := th'.stack) hP hth' hk hz
      (hi _ _ _ _ hJ) hc rfl hσ' hp' hJ hw' hb' hinv'' hown' hmg.1 hfi' hmg.2
      (by rw [hst']; exact hoo') hai'' hfr'' hco' ⟨_, reach_run hreach hrun2⟩ (.inl trivial) hcrJ hcrJ (.refl _)
    exact ⟨s₃, run_trans0 hrun2 hrun3, .inl hpre⟩
  -- not the box's store: the row is one with no box rows (the counter's add at a box refuted)
  have hout0 : Out p lbl (msOfA0 Λ μ rd G own ar I lbl lsize fs₁) (fun s' c' => PendA p I lbl lsize s' c' fs₁)
      th.st c₁ := by
    rcases hout.unnew with h | ⟨k, op, g, n, τ, hex, hrt, hop, hX⟩ | h
    · exact absurd h hNS
    · obtain ⟨_, -, -, -, -, hcw⟩ := CtrRows.ctrRmw_row (I := isaLSE2) (mh := ar.heap) (mc := ar.ctr)
        (mu := ar.units) (mo := ar.off) (mcl := ar.cells) (mown := fun st => own st fs₁) (Y := fun _ _ => True)
        hinv hso ho hGm hgi.1 hoo₁ hex
        (show (msOfA0 Λ μ rd G own ar I lbl lsize fs₁).rt (BitVec.ofNat 64 ar.ctr).toNat from hrt) hop
        fun old h1 h2 h3 h4 => ⟨hX old h1 h2 h3 h4, trivial⟩
      exact absurd (writes_of_ctrW hcw) hwc
    · exact h
  -- not the counter's add: the write is one the arena allows
  have hmw := CtrRows.out_memW (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
    hinv hso ho hns (A64Ext.wide8_exec hw hns) hGm hgi.1 hoo₁ hout0
  have hai' : AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c₁ := by
    refine allocInvAt_out hai1 hnd ?_
    rcases hmw with hm | ⟨L, V, -, hwr, -⟩
    · exact .inl hm
    · have hW : Writes th t.1.mem o L := ⟨V, hwr⟩
      exact .inr ⟨L, hW, fun he => hwc (he ▸ hW),
        (hN.arena _ _ _ _ _ hI1 hns th t.1.mem outs o L rfl hso ho hW).resolve_right hNS⟩
  have hsrc1 : ∀ (hr1 : fs₁ = [] → ∀ a, c₁.term ≠ .ret a),
      (SrcSem.source P p).Reach (tr ++ []) { s with ths := #[thAt th0 c₁ fs₁] } :=
    fun hr1 => reach_run hreach (hsrc hr1)
  have hmg : MemIn Λ o.mem ∧ MemInv G o.mem := by
    rcases hmw with ⟨hm, -⟩ | ⟨L, V, hL8, hwr, hL⟩
    · rw [hm]; exact ⟨hmi, hgi⟩
    rcases hwr with ⟨hm, hp'⟩ | ⟨-, -, -, hm, -⟩
    rotate_left
    · rw [hm]; exact ⟨hmi, hgi⟩
    rw [hm]
    have hLw := ExtRows.loc_wordLoc hL8
    have h8 : Kernel.locBytes L = 8 := by simp [Kernel.locBytes, hL8]
    rcases hL with ⟨-, hmp, hGV⟩ | ⟨x, a, b, e, ty, w, sa, ht, hev, hv, hsa⟩ |
      ⟨x, sa, u, v, e, hxs, hA⟩ | ⟨hLc, -, -, -, -⟩
    · exact ⟨memIn_append (hmp.2 rfl) hmi, hgi.append hGV⟩
    · obtain ⟨k, m, hkm, hml⟩ := hsafe.cell₁ (hsrc1 fun _ a' h => by rw [ht] at h; cases h)
        hI1 (.inr ⟨b, ht⟩) hev hsa
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      rw [hsa] at hv
      have hwa := wordAddr_of_valRep_loc0 hv
      refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
      · rw [h8] at hi
        exact shared_of_wordAddr hinv.mem hwa hoff i hi
      · show G L V
        rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
    · obtain ⟨k, m, hkm, hml⟩ := hsafe.xchg₁ (hsrc1 fun _ => xchgSite_not_ret hxs) hI1 hxs
      obtain ⟨-, -, hoff⟩ := hinv.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hkm))
      rw [hml] at hoff
      have hwa := wordAddr_of_valRep_loc0 hA
      refine ⟨memIn_append (fun i hi => ?_) hmi, hgi.append ?_⟩
      · rw [h8] at hi
        exact shared_of_wordAddr hinv.mem hwa hoff i hi
      · show G L V
        rw [hLw]; exact hGpl _ V (heapData_of_wordAddr hinv.mem hwa hoff)
    · subst hLc; exact absurd ⟨V, .inl ⟨hm, hp'⟩⟩ hwc
  obtain ⟨hmi', hgi'⟩ := hmg
  have hU : ∀ {x : TermRun.Cfg} {c : Ctl}, heapUse x = heapUse { s with ths := #[thAt th0 c₁ fs₁] } →
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c →
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse x) c :=
    fun he h => by rw [he, hheap1]; exact h
  rcases CtrRows.out_localW (mh := ar.heap) (mc := ar.ctr) (mu := ar.units) (mo := ar.off) (mcl := ar.cells)
      hinv hso ho hns (A64Ext.wide8_exec hw hns) hGm hgi.1 hoo₁ hout0 with
    ⟨c', hr, hX, hinv'⟩ |
    ⟨kl, A, g, x, a, e, ty, w, sa, hex, ht, hev, hv, hsa, hX⟩ |
    ⟨kr, A, V, s', x, a, b, e, ty, tb, w, wb, sa, hex, ht, hev, hv, hsa, hevb, hvb, hX⟩ |
    ⟨kl, A, g, x, sa, u, v, e, hex, hxs, hA, hh0, hX⟩ |
    ⟨kr, A, V, s', x, sa, u, v, e, tv, wv, wold, hex, hxs, hA, hh0, hev, hvb, hX⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcw⟩ |
    ⟨s', A, x, a, τ, e, ta, ws, k, wold, old, us, hst, ht, hev, hk', hh0, hold, hA, hcl, hus, hX, hm, hinv'⟩
  · -- a local run: the row's run and the landing's pending run
    have hr1 := hr0.trans (FrameRun.ofLocal hr fs₁)
    obtain ⟨s', hrun, hpre⟩ := pre_localJAH (J := PendA p I) (t' := (t.1.withThread 0 o.thread o.mem, t.2)) hP hth'
      hk hz ((hHA hX)) hc hs0 hσ hp hX hw' hb' hinv' hown' hmi' hfi' hgi' hoo'
      (allocInvAt_frameRun hai' (FrameRun.ofLocal hr fs₁)) hfr hco ⟨tr, hreach⟩ hhi hcr hX.noRet hr1
    exact pend_landAH hP hN hrun hpre
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
    refine pend_landAH hP hN hrun ⟨o.thread, th', 0, lbl, lsize, ts, hl, pm, none, hth', ⟨E, hk⟩, hz,
      (hHA (by rw [hgv]; exact hX')), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, .inl trivial,
      hw', hb', hinv', hown', hmi', hfi', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
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
    refine pend_landAH hP hN hrun ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
      (hHA (by rw [hst'']; exact hX)), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, .inl trivial,
      hw', hb', hinv', hown', hmi', hfi', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
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
    refine pend_landAH hP hN hrun1 ⟨o.thread, thAt th0 c₁ fs₁, 0, lbl, lsize, ts, hl, pm,
      some (A.toNat, ⟨m.val, m.view, jl⟩), hth', ⟨E, hk⟩, hz, (hHA (by rw [hgr]; exact hX')),
      .inl rfl, hc, rfl, hσ, hp, ?_, .inl ⟨sa, jl, m, hwa, hoff, hjl, hm, rfl⟩, hw', hb', hinv',
      hown', hmi', hfi', hgi', hoo', ?_, hfr1, hco, _, reach_run hreach hrun1⟩
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
    refine pend_landAH hP hN hrun ⟨o.thread, th', 0, lbl, lsize, _, hl, pm, none, hth', ⟨E, hk⟩, hz,
      (hHA (by rw [hst'']; exact hX)), .inl rfl, hc, rfl, hσ'.trans hσ, hp', ?_, .inl trivial,
      hw', hb', hinv', hown', hmi', hfi', hgi', ?_, ?_, freshInv_one hs0 rfl rfl rfl hna' hfr, hco, _,
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
    obtain ⟨s₃, hrun3, hpre⟩ := pre_localJAH (J := I) (t' := (t.1.withThread 0 o.thread o.mem, t.2))
      (s := { s with mem := _, ths := #[th'] })
      (th0 := th') (hd := none) (c' := ⟨th'.term, th'.env, none⟩) (fs' := th'.stack) hP hth' hk hz
      ((hi _ _ _ _ hJ)) hc rfl (hσ'.trans hσ) (hp'.trans hp)
      (by rw [hte, hen, hst']; exact hJ) hw' hb' hinv'' hown' hmi' hfi' hgi' (by rw [hst']; exact hoo')
      (hV hheap' (hai''.retarget (fun w h => by cases h) fun w h => by cases h))
      (by rw [hna']; exact hfr'') (ctrOff_alloc hok hco hland) ⟨_, reach_run hreach hrun2⟩ (.inl trivial)
      hcrJ hcrJ (.refl _)
    exact ⟨s₃, run_trans0 hrun2 hrun3, .inl hpre⟩


end Spike.Lib.A64ConsumerA
