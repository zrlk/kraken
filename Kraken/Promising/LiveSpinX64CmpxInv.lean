/-
**Stage 3: the operational invariant of the x64
`lock cmpxchg` spinlock** over promise-free `Arch.tso` runs of any number of
verbatim workers (`CmpxAbs.cmpxImageV`) on a valid layout. The x64 twin of
`LiveSpinCasInv.lean`.

A thread *holds* the lock (`Holder`) between its successful `lock cmpxchg`
and its `movl $0,(lock)`: at the `jne` with `ZF` set, or at positions 5–8.
`InvX`:

- every thread keeps its image, end address and private memory (`Static`;
  the operands are absolute, so no register is static), has no outstanding
  promise, sits at a position of `spPcs`, and has `%eax`'s low word `0` at
  its `movl $1,%ecx` and its `lock cmpxchg` (`TInv`);
- **if the lock's value is not `0`, some thread holds it** (`held`).

A `lock cmpxchg` that writes makes its thread a holder (`ZF` set), a failing
one writes nothing (`op = none`), and the only other write to the lock is the
holder's release store of `0`.
-/
import Kraken.Promising.LiveSpinX64CmpxTrees
import Kraken.Promising.LiveSpinX64
import Kraken.Promising.LiveTsoRmw
import Kraken.Promising.CertifyX64
import Kraken.Promising.LiveSpinCommon

namespace Kraken.Promising.Live.SpinX64CmpxInv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.TsoRmw Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC StartStateCV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-- The lock's location. -/
abbrev LkL : Loc := ⟨symC "lock", 4⟩

/-- The counter's location. -/
abbrev CtL : Loc := ⟨symC "counter", 4⟩

/-! ## The per-thread invariant -/

/-- What a worker state never changes: its image, declarations, end address
and private memory at the two words. -/
structure Static (s : isa.State) : Prop where
  exe : s.exe = layout cmpxImageV
  decls : s.decls = {}
  endPc : s.endPc = pcA 10
  dl : Mem.loadInt s.st.1.dmem (symC "lock") 4 = none
  dc : Mem.loadInt s.st.1.dmem (symC "counter") 4 = none

omit hv in
theorem Static.goto {s : isa.State} (h : Static s) (md : MachineData) (pc : Int64) (hd : md.dmem = s.st.1.dmem) :
    Static (SpinX64CmpxTrees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, hd ▸ h.dl, hd ▸ h.dc⟩

/-- The register fact at each position: `%eax`'s low word `0` before the
`lock cmpxchg`. -/
def PcInv (s : MachineData) : Nat → Prop
  | 2 => eax s = 0#32
  | 3 => eax s = 0#32
  | _ => True

/-- **The per-thread invariant.** -/
structure TInv (t : Thread isa) : Prop where
  st : Static t.st
  prom : t.prom = []
  pc : ∃ i ∈ spPcs, t.st.st.2 = pcA i ∧ PcInv t.st.st.1 i

/-- A thread holds the lock: past a successful `lock cmpxchg`, before its
release. -/
def Holder (t : Thread isa) : Prop :=
  (t.st.st.2 = pcA 4 ∧ t.st.st.1.status.zf = true) ∨ t.st.st.2 ∈ [5, 6, 7, 8].map pcA

theorem Static.at {s : isa.State} (h : Static s) {i : Nat} (hi : i ∈ spPcs) (h10 : i ≠ 10)
    (hpc : s.st.2 = pcA i) : At s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h10 (addrOf_inj hi (by decide) e)⟩

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {t : Thread isa} (h : Static t.st) (hpc : t.st.st.2 = pcA 10)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A t tid mem = none := by
  have : isa.exec t.st = none := by
    show X64.exec t.st = none
    unfold X64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

/-! ## The steps, position by position -/

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static t.st) (hp : t.prom = [])
  (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

theorem s1 (hpc : t.st.st.2 = pcA 1) :
    oc.mem = mem ∧ (∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = 0#32 ∧
      oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 2)) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  obtain ⟨h1, ⟨i, h2⟩, h3, h4⟩ := spec_choose _ _ (exec_xor _ (hS.at (by decide) (by decide) hpc)) hs ho
  refine ⟨h1, ⟨_, ?_, ?_, h2⟩, h3, h4⟩ <;> rfl

theorem s2 (hpc : t.st.st.2 = pcA 2) :
    oc.mem = mem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st
      { t.st.st.1 with regs := t.st.st.1.regs.set64 .rcx 1#64 } (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_movc _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s3 (hpc : t.st.st.2 = pcA 3) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ ∃ tr old,
      oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 4) ∧
      mem.read? LkL tr = some old ∧
      (mem.lastWrite LkL ≤ t.views.getCoh LkL → old = mem.finalVal LkL) ∧ oc.thread.prom = [] ∧
      (∃ ν, TraceEv.read LkL tr old ν ∈ oc.log) ∧
      (∀ l', t.views.getCoh l' ≤ oc.thread.views.getCoh l') ∧
      ((BitVec.setWidth 32 old ≠ eax t.st.st.1 ∧ md.status.zf = false ∧ oc.mem = mem) ∨
       (BitVec.setWidth 32 old = eax t.st.st.1 ∧ md.status.zf = true ∧
         ∃ v, oc.mem = (mem.append { loc := LkL, val := v, tid }).1)) := by
  obtain ⟨g, hg, hex⟩ := exec_cmpxchg _ (hS.at (by decide) (by decide) hpc) hS.dl
  obtain ⟨tr, old, hst, hrd, hlw, hpr, hlog, hco, hcase⟩ := spec_rmwo_tso _ _ rfl hp hex hs ho
  refine ⟨g old, (hg old).1, tr, old, hst, hrd, hlw, hpr, hlog, hco, ?_⟩
  have hz := (hg old).2
  rcases hcase with ⟨h1, h2⟩ | ⟨new, h1, -, h3, -⟩
  · have hne : BitVec.setWidth 32 old ≠ eax t.st.st.1 := fun e => by simp [e] at h1
    refine .inl ⟨hne, ?_, h2⟩
    cases e : (g old).status.zf
    · rfl
    · exact absurd (hz.mp e) hne
  · by_cases e : BitVec.setWidth 32 old = eax t.st.st.1
    · exact .inr ⟨e, hz.mpr e, _, h3⟩
    · simp [e] at h1

theorem s4 (hpc : t.st.st.2 = pcA 4) :
    oc.mem = mem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st t.st.st.1
      (if t.st.st.1.status.zf then pcA 5 else pcA 1) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_jne _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s5 (hpc : t.st.st.2 = pcA 5) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 6) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom := by
  obtain ⟨g, hg, hex⟩ := exec_ldc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨ts, v, h1, -, -, h4, h5, -⟩ := spec_load _ _ hex hs ho
  exact ⟨g v, hg v, h1, h4, h5⟩

theorem s6 (hpc : t.st.st.2 = pcA 6) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 7) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom := by
  obtain ⟨md, hd, hex⟩ := exec_add _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, -⟩ := spec_done _ _ hex hs ho
  exact ⟨md, hd, h2, h1, h3⟩

include hp in
theorem s7 (hpc : t.st.st.2 = pcA 7) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 8) ∧
      (∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1) ∧ oc.thread.prom = [] := by
  obtain ⟨v, md, hd, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
  exact ⟨md, hd, h2, ⟨v, h1⟩, h3⟩

include hp in
theorem s8 (hpc : t.st.st.2 = pcA 8) :
    oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1 ∧
      oc.thread.st = SpinX64CmpxTrees.goto t.st t.st.st.1 (pcA 9) ∧ oc.thread.prom = [] :=
  spec_store _ _ hp (exec_unlock _ (hS.at (by decide) (by decide) hpc) hS.dl) hs ho

theorem s9 (hpc : t.st.st.2 = pcA 9) :
    oc.mem = mem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st t.st.st.1 (pcA 10) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_jmp _ (hS.at (by decide) (by decide) hpc)) hs ho

end Steps

/-! ## One thread's step -/

theorem TInv.pcinv {t : Thread isa} (h : TInv t) {i : Nat} (hi : i ∈ spPcs) (hpc : t.st.st.2 = pcA i) :
    PcInv t.st.st.1 i := by
  obtain ⟨j, hj, hpc', hinv⟩ := h.pc
  rw [hpc] at hpc'
  rwa [addrOf_inj hi hj hpc']

omit hv in
/-- A holder sits at position 4, 5, 6, 7 or 8. -/
theorem Holder.pos {t : Thread isa} (h : Holder t) : ∃ p ∈ [4, 5, 6, 7, 8], t.st.st.2 = pcA p := by
  rcases h with ⟨h, -⟩ | h
  · exact ⟨4, by decide, h⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact ⟨5, by decide, h⟩
    · exact ⟨6, by decide, h⟩
    · exact ⟨7, by decide, h⟩
    · exact ⟨8, by decide, h⟩

omit hv in
theorem holder_of_pc {t : Thread isa} {p : Nat} (hp : p ∈ [5, 6, 7, 8]) (hpc : t.st.st.2 = pcA p) : Holder t :=
  .inr (by rw [hpc]; exact List.mem_map_of_mem hp)

/-- Not a holder at position `i ∈ spPcs`: at a position other than 5–8, and
not at 4 with `ZF` set. -/
theorem not_holder_of_pc {t : Thread isa} {i : Nat} (hi : i ∈ spPcs) (hpc : t.st.st.2 = pcA i)
    (h5 : i ∉ [5, 6, 7, 8]) (h4 : i = 4 → t.st.st.1.status.zf = false) : ¬ Holder t := by
  rintro (⟨h, hz⟩ | h)
  · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
    rw [h4 rfl] at hz; cases hz
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;>
    · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
      exact h5 (by decide)

/-- What one step of a thread does. -/
inductive StepRes (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; a holder stays a holder. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1)
      (ht : TInv oc.thread) (hh : Holder t → Holder oc.thread)
  /-- A `lock cmpxchg` that writes: the thread now holds the lock. -/
  | acq (v : Val) (hm : oc.mem = (mem.append { loc := LkL, val := v, tid }).1)
      (ht : TInv oc.thread) (hh : Holder oc.thread)
  /-- The holder's release: the lock written `0`. -/
  | rel (hm : oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1)
      (ht : TInv oc.thread) (hh : Holder t) (hpc : oc.thread.st.st.2 = pcA 9)

local macro "tinv" hS:ident hst:ident hd:term "," hp:term "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ $hd, $hp, $j, by decide, by rw [$hst:ident], ?_⟩)

/-- **One thread's step**, by position. -/
theorem thread_step {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv t)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) : StepRes tid t mem oc := by
  obtain ⟨i, hi, hpc, hinv⟩ := h.pc
  have hS := h.st
  have hi' := hi
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  have nh : ∀ (j : Nat), j ∈ spPcs → (j = 4 → False) → j ∉ [5, 6, 7, 8] → t.st.st.2 = pcA j → ¬ Holder t :=
    fun j hj h4 h5 hpc => not_holder_of_pc hj hpc h5 fun e => (h4 e).elim
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, ⟨md, hd, hz, hst⟩, hp, -⟩ := s1 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 2)
      (fun hh => absurd hh (nh 1 hi (by omega) (by decide) hpc))
    rw [hst]; exact hz
  · obtain ⟨hm, hst, hp, -⟩ := s2 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 3)
      (fun hh => absurd hh (nh 2 hi (by omega) (by decide) hpc))
    rw [hst]; exact hinv
  · obtain ⟨md, hd, tr, old, hst, -, -, hp, -, -, hcase⟩ := s3 hS h.prom hs ho hpc
    rcases hcase with ⟨-, hz, hm⟩ | ⟨-, hz, v, hm⟩
    · refine .quiet (.inl hm) (tinv hS hst hd, hp, 4) (fun hh => absurd hh (nh 3 hi (by omega) (by decide) hpc))
      rw [hst]; trivial
    · refine .acq _ hm (tinv hS hst hd, hp, 4) (.inl ⟨by rw [hst], by rw [hst]; exact hz⟩)
      rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s4 hS hs ho hpc
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      refine .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 5)
        (fun _ => holder_of_pc (p := 5) (by decide) (by rw [hst]))
      rw [hst]; trivial
    · rw [ite_eq_right hz] at hst
      refine .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 1)
        (fun hh => absurd hh (not_holder_of_pc hi hpc (by decide) fun _ => by simpa using hz))
      rw [hst]; trivial
  · obtain ⟨md, hd, hst, hm, hp⟩ := s5 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 6)
      (fun _ => holder_of_pc (p := 6) (by decide) (by rw [hst]))
    rw [hst]; trivial
  · obtain ⟨md, hd, hst, hm, hp⟩ := s6 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 7)
      (fun _ => holder_of_pc (p := 7) (by decide) (by rw [hst]))
    rw [hst]; trivial
  · obtain ⟨md, hd, hst, hm, hp⟩ := s7 hS h.prom hs ho hpc
    refine .quiet (.inr hm) (tinv hS hst hd, hp, 8) (fun _ => holder_of_pc (p := 8) (by decide) (by rw [hst]))
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp⟩ := s8 hS h.prom hs ho hpc
    refine .rel hm (tinv hS hst rfl, hp, 9) (holder_of_pc (p := 8) (by decide) hpc) (by rw [hst])
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s9 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 10)
      (fun hh => absurd hh (nh 9 hi (by omega) (by decide) hpc))
    rw [hst]; trivial
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant**: every thread satisfies `TInv`, and a non-zero lock
has a holder. -/
structure InvX (cfg : Config isa) : Prop where
  hlc : LkL ≠ CtL
  bnd : cfg.Bnd
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv t
  held : cfg.mem.finalVal LkL ≠ 0 → ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Holder t

/-- **An instruction step keeps the invariant**; the lock's last write stays,
or the stepping thread holds after the step, or held before it. -/
theorem step_inv {tid : Nat} {cfg cfg' : Config isa}
    (h : InvX cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.tso tid cfg cfg') :
    InvX cfg' ∧ (cfg'.mem.lastWrite LkL = cfg.mem.lastWrite LkL ∨
      (∃ t', cfg'.threads[tid]? = some t' ∧ Holder t') ∨ (∃ t, cfg.threads[tid]? = some t ∧ Holder t)) := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hthr : ∀ (i : Nat) u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u →
      TInv oc.thread → TInv u := fun i u hu hT => by
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact h.thr i u hu
  cases thread_step (h.thr tid t ht) hs ho with
  | quiet hm hT hh =>
    have hfin : oc.mem.finalVal LkL = cfg.mem.finalVal LkL ∧ oc.mem.lastWrite LkL = cfg.mem.lastWrite LkL := by
      rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
      · exact ⟨rfl, rfl⟩
      · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem { loc := CtL, val := v, tid } (Ne.symm h.hlc)
        exact ⟨a1, a2⟩
    refine ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, fun hne => ?_⟩, .inl hfin.2⟩
    obtain ⟨i, u, hu, hh'⟩ := h.held (by rw [← hfin.1]; exact hne)
    by_cases e : i = tid
    · subst e; rw [ht] at hu; cases hu
      exact ⟨i, oc.thread, wt_tid ht, hh hh'⟩
    · exact ⟨i, u, by rw [wt_ne ht e]; exact hu, hh'⟩
  | acq v hm hT hh =>
    exact ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, fun _ => ⟨tid, oc.thread, wt_tid ht, hh⟩⟩,
      .inr (.inl ⟨oc.thread, wt_tid ht, hh⟩)⟩
  | rel hm hT hh _ =>
    refine ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, fun hne => absurd ?_ hne⟩, .inr (.inr ⟨t, ht, hh⟩)⟩
    show oc.mem.finalVal LkL = 0
    rw [hm, finalVal_append]; simp

/-- **The invariant holds initially.** -/
theorem inv_init {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) : InvX (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  refine ⟨loc_ne hs.hlc, Config.init_bnd _ _, ?_, fun hne => absurd ?_ hne⟩
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    refine ⟨⟨hs.exe, hs.decls, by show s.endPc = _; rw [hs.endPc, hs.exe]; exact label_done,
      X64.EnvG.SpinPublicG.split_dl hs.split, X64.EnvG.SpinPublicG.split_dc hs.split⟩, rfl,
      1, by decide, by show s.st.2 = _; rw [hs.pc, hs.exe]; exact label_worker, trivial⟩
  · have := hs.hL0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]

/-- **The invariant along a promise-free trace from a start configuration.** -/
theorem trace_inv {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) (tr : TraceS Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hpf : PromiseFree Arch.tso tr.cfg) :
    ∀ i, InvX (tr.cfg i) :=
  SpinCommon.trace_inv_of hpf (P := InvX) (h0 ▸ inv_init hs) fun _ _ h hi hm =>
    (step_inv h (h.bnd.succ hm) hi).1

end Kraken.Promising.Live.SpinX64CmpxInv
