/-
**Stage 3: the operational invariant of the AArch64
CAS spinlock** over promise-free runs of any number of workers
`casTtasWorker` on a valid layout.

A thread *holds* the lock (`Holder`) between its successful `CASA` and its
`STLR`: at the `CBZ` with `W2 = 0`, or at positions 11–14. `InvC`:

- every thread keeps its program, addresses and private memory, has no
  outstanding promise, sits at a position of `spPcs`, and has `W2 = 0` at
  its `CASA` (`TInvC`);
- **if the lock's value is not `0`, some thread holds it** (`held`).

No mutual exclusion and no atomicity are needed: a `CASA` that writes makes
its thread a holder (it read `W2 = 0`), and the only other write to the lock
is the holder's `STLR`, which writes `0`.

`step_inv`: an instruction step keeps `InvC`; the lock's last write changes
only at a step after which the thread holds, or by a thread that held. The
per-position step lemmas (`s1` … `s15`) are reused by `LiveSpinCasPF.lean`.
-/
import Kraken.Promising.LiveSpinCasTrees
import Kraken.Promising.LiveSpinStep
import Kraken.Promising.LiveTicketInv
import Kraken.Promising.LiveSpin

namespace Kraken.Promising.Live.SpinCasInv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-! ## The per-thread invariant -/

/-- What a worker state never changes: its program, end address, address
registers and private memory at the two words. -/
structure Static (l c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout casTtasWorker
  decls : s.decls = {}
  endPc : s.endPc = pcA 17
  x0 : s.st.1.regs.X0.toBitVec = l
  x1 : s.st.1.regs.X1.toBitVec = c
  dl : Mem.loadInt s.st.1.dmem l 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

omit hv in
theorem Static.goto {l c : BitVec 64} {s : isa.State} (h : Static l c s) (md : MachineData) (pc : Int64)
    (h0 : md.regs.X0 = s.st.1.regs.X0) (h1 : md.regs.X1 = s.st.1.regs.X1) (hd : md.dmem = s.st.1.dmem) :
    Static l c (SpinCasTrees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, h0 ▸ h.x0, h1 ▸ h.x1, hd ▸ h.dl, hd ▸ h.dc⟩

/-- The register fact at each position: `W2 = 0` at the `CASA`. -/
def PcInv (s : MachineData) : Nat → Prop
  | 4 => w32 s.regs.X2 = 0#32
  | _ => True

/-- **The per-thread invariant.** -/
structure TInv (l c : BitVec 64) (t : Thread isa) : Prop where
  st : Static l c t.st
  prom : t.prom = []
  pc : ∃ i ∈ spPcs, t.st.st.2 = pcA i ∧ PcInv t.st.st.1 i

/-- A thread holds the lock: past a successful `CASA`, before its `STLR`. -/
def Holder (t : Thread isa) : Prop :=
  (t.st.st.2 = pcA 5 ∧ w32 t.st.st.1.regs.X2 = 0#32) ∨ t.st.st.2 ∈ [11, 12, 13, 14].map pcA

theorem Static.at {l c : BitVec 64} {s : isa.State} (h : Static l c s) {i : Nat} (hi : i ∈ spPcs)
    (h17 : i ≠ 17) (hpc : s.st.2 = pcA i) : At s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h17 (addrOf_inj hi (by decide) e)⟩

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {l c : BitVec 64} {t : Thread isa} (h : Static l c t.st) (hpc : t.st.st.2 = pcA 17)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A t tid mem = none := by
  have : isa.exec t.st = none := by
    show AArch64.exec t.st = none
    unfold AArch64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

/-! ## The steps, position by position -/

section Steps

variable {l c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static l c t.st) (hp : t.prom = [])
  (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

theorem s1 (hpc : t.st.st.2 = pcA 1) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st
      { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X3 1#64 } (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_mov3 _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s3 (hpc : t.st.st.2 = pcA 3) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st
      { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 0#64 } (pcA 4) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_mov2 _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s4 (hpc : t.st.st.2 = pcA 4) :
    ∃ tr old, oc.thread.st = SpinCasTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) }
        (pcA 5) ∧
      mem.read? (L4 l) tr = some old ∧
      (mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l) → old = mem.finalVal (L4 l)) ∧ oc.thread.prom = [] ∧
      ((BitVec.setWidth 32 old ≠ w32 t.st.st.1.regs.X2 ∧ oc.mem = mem) ∨
       (BitVec.setWidth 32 old = w32 t.st.st.1.regs.X2 ∧
         oc.mem = (mem.append { loc := L4 l, val := BitVec.setWidth 128 (w32 t.st.st.1.regs.X3), tid }).1)) := by
  obtain ⟨tr, old, hst, hrd, hlw, hpr, hcase⟩ :=
    spec_rmwo _ _ rfl hp (exec_casa _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho
  refine ⟨tr, old, hst, hrd, hlw, hpr, ?_⟩
  rcases hcase with ⟨h1, h2, -⟩ | ⟨new, h1, -, h3⟩
  · refine .inl ⟨fun e => ?_, h2⟩
    simp [e] at h1
  · by_cases e : BitVec.setWidth 32 old = w32 t.st.st.1.regs.X2
    · simp only [e, ↓reduceIte, Option.some.injEq] at h1
      exact .inr ⟨e, h1 ▸ h3⟩
    · simp [e] at h1

theorem s5 (hpc : t.st.st.2 = pcA 5) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st t.st.st.1
      (if w32 t.st.st.1.regs.X2 = 0#32 then pcA 11 else pcA 7) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_cbz _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s7 (hpc : t.st.st.2 = pcA 7) :
    ∃ ts v, oc.thread.st = SpinCasTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 8) ∧
      mem.read? (L4 l) ts = some v ∧ (mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l) → v = mem.finalVal (L4 l)) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ (∃ ν, TraceEv.read (L4 l) ts v ν ∈ oc.log) ∧
      ∀ l', t.views.getCoh l' ≤ oc.thread.views.getCoh l' := by
  have hex := exec_ldr_l _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl
  obtain ⟨ts, v, h1, h2, h3, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨ts, v, h1, h2, h3, h4, h5, h6, spec_load_coh _ _ hex hs ho⟩

theorem s8 (hpc : t.st.st.2 = pcA 8) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st t.st.st.1
      (if w32 t.st.st.1.regs.X2 = 0#32 then pcA 9 else pcA 7) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_cbnz _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s9 (hpc : t.st.st.2 = pcA 9) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st t.st.st.1 (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_b_try _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s11 (hpc : t.st.st.2 = pcA 11) :
    ∃ ts v, oc.thread.st = SpinCasTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 12) ∧
      mem.read? (L4 c) ts = some v ∧ oc.mem = mem ∧ oc.thread.prom = t.prom := by
  obtain ⟨ts, v, h1, h2, -, h4, h5, -⟩ :=
    spec_load _ _ (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc) hs ho
  exact ⟨ts, v, h1, h2, h4, h5⟩

theorem s12 (hpc : t.st.st.2 = pcA 12) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (t.st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      (pcA 13) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s13 (hpc : t.st.st.2 = pcA 13) :
    oc.mem = (mem.append { loc := L4 c, val := (BitVec.setWidth 128
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec)), tid }).1 ∧
      oc.thread.st = SpinCasTrees.goto t.st t.st.st.1 (pcA 14) ∧ oc.thread.prom = [] :=
  spec_store _ _ hp (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc) hs ho

include hp in
theorem s14 (hpc : t.st.st.2 = pcA 14) :
    oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1 ∧
      oc.thread.st = SpinCasTrees.goto t.st t.st.st.1 (pcA 15) ∧ oc.thread.prom = [] :=
  spec_store _ _ hp (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho

theorem s15 (hpc : t.st.st.2 = pcA 15) :
    oc.mem = mem ∧ oc.thread.st = SpinCasTrees.goto t.st t.st.st.1 (pcA 17) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_b_done _ (hS.at (by decide) (by decide) hpc)) hs ho

end Steps

/-! ## One thread's step -/

theorem TInv.pcinv {l c : BitVec 64} {t : Thread isa} (h : TInv l c t) {i : Nat}
    (hi : i ∈ spPcs) (hpc : t.st.st.2 = pcA i) : PcInv t.st.st.1 i := by
  obtain ⟨j, hj, hpc', hinv⟩ := h.pc
  rw [hpc] at hpc'
  rwa [addrOf_inj hi hj hpc']

omit hv in
/-- A holder sits at position 5, 11, 12, 13 or 14. -/
theorem Holder.pos {t : Thread isa} (h : Holder t) :
    ∃ p ∈ [5, 11, 12, 13, 14], t.st.st.2 = pcA p := by
  rcases h with ⟨h, -⟩ | h
  · exact ⟨5, by decide, h⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact ⟨11, by decide, h⟩
    · exact ⟨12, by decide, h⟩
    · exact ⟨13, by decide, h⟩
    · exact ⟨14, by decide, h⟩

omit hv in
theorem holder_of_pc {t : Thread isa} {p : Nat} (hp : p ∈ [11, 12, 13, 14]) (hpc : t.st.st.2 = pcA p) :
    Holder t :=
  .inr (by rw [hpc]; exact List.mem_map_of_mem hp)

/-- Not a holder at position `i ∈ spPcs`: at a position other than 11–14, and
not at 5 with `W2 = 0`. -/
theorem not_holder_of_pc {t : Thread isa} {i : Nat} (hi : i ∈ spPcs) (hpc : t.st.st.2 = pcA i)
    (h11 : i ∉ [11, 12, 13, 14]) (h5 : i = 5 → w32 t.st.st.1.regs.X2 ≠ 0#32) : ¬ Holder t := by
  rintro (⟨h, hz⟩ | h)
  · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
    exact h5 rfl hz
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;>
    · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
      exact h11 (by decide)

/-- What one step of a thread does. -/
inductive StepRes (l c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; a holder stays a holder. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (ht : TInv l c oc.thread) (hh : Holder t → Holder oc.thread)
  /-- A `CASA` that writes: the thread now holds the lock. -/
  | acq (v : Val) (hm : oc.mem = (mem.append { loc := L4 l, val := v, tid }).1)
      (ht : TInv l c oc.thread) (hh : Holder oc.thread)
  /-- The holder's `STLR`: the lock written `0`. -/
  | rel (hm : oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1)
      (ht : TInv l c oc.thread) (hh : Holder t) (hpc : oc.thread.st.st.2 = pcA 15)

local macro "tinv" hS:ident hst:ident hp:term "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ rfl rfl rfl, $hp, $j, by decide, by rw [$hst:ident] <;> rfl, ?_⟩)

/-- **One thread's step**, by position. -/
theorem thread_step {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv l c t)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : StepRes l c tid t mem oc := by
  obtain ⟨i, hi, hpc, hinv⟩ := h.pc
  have hS := h.st
  have hi' := hi
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  have nh : ∀ (j : Nat), j ∈ spPcs → (j = 5 → False) → j ∉ [11, 12, 13, 14] → t.st.st.2 = pcA j → ¬ Holder t :=
    fun j hj h5 h11 hpc => not_holder_of_pc hj hpc h11 fun e => (h5 e).elim
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, hst, hp, -⟩ := s1 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 3) (fun hh => absurd hh (nh 1 hi (by omega) (by decide) hpc))
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s3 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 4) (fun hh => absurd hh (nh 3 hi (by omega) (by decide) hpc))
    rw [hst]; show w32 (t.st.st.1.regs.setXReg .X2 0#64).X2 = 0#32; rfl
  · obtain ⟨tr, old, hst, -, -, hp, hcase⟩ := s4 hS h.prom hs ho hpc
    have hz : w32 t.st.st.1.regs.X2 = 0#32 := hinv
    rcases hcase with ⟨hne, hm⟩ | ⟨heq, hm⟩
    · refine .quiet (.inl hm) (tinv hS hst hp, 5) (fun hh => absurd hh (nh 4 hi (by omega) (by decide) hpc))
      rw [hst]; trivial
    · refine .acq _ hm (tinv hS hst hp, 5) (.inl ⟨by rw [hst], ?_⟩)
      · rw [hst]; trivial
      · rw [hst]; show BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) = 0#32
        rw [← hz, ← heq]; simp
  · obtain ⟨hm, hst, hp, -⟩ := s5 hS hs ho hpc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 11) (fun _ => holder_of_pc (p := 11) (by decide) (by rw [hst]))
      rw [hst]; trivial
    · rw [ite_eq_right hz] at hst
      refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 7)
        (fun hh => absurd hh (not_holder_of_pc hi hpc (by decide) fun _ => hz))
      rw [hst]; trivial
  · obtain ⟨ts, v, hst, -, -, hm, hp, -⟩ := s7 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 8) (fun hh => absurd hh (nh 7 hi (by omega) (by decide) hpc))
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s8 hS hs ho hpc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 9) (fun hh => absurd hh (nh 8 hi (by omega) (by decide) hpc))
      rw [hst]; trivial
    · rw [ite_eq_right hz] at hst
      refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 7) (fun hh => absurd hh (nh 8 hi (by omega) (by decide) hpc))
      rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s9 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 3) (fun hh => absurd hh (nh 9 hi (by omega) (by decide) hpc))
    rw [hst]; trivial
  · obtain ⟨ts, v, hst, -, hm, hp⟩ := s11 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 12) (fun _ => holder_of_pc (p := 12) (by decide) (by rw [hst]))
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s12 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 13) (fun _ => holder_of_pc (p := 13) (by decide) (by rw [hst]))
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp⟩ := s13 hS h.prom hs ho hpc
    refine .quiet (.inr ⟨_, hm⟩) (tinv hS hst hp, 14) (fun _ => holder_of_pc (p := 14) (by decide) (by rw [hst]))
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp⟩ := s14 hS h.prom hs ho hpc
    refine .rel hm (tinv hS hst hp, 15) (holder_of_pc (p := 14) (by decide) hpc) (by rw [hst])
    rw [hst]; trivial
  · obtain ⟨hm, hst, hp, -⟩ := s15 hS hs ho hpc
    refine .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 17) (fun hh => absurd hh (nh 15 hi (by omega) (by decide) hpc))
    rw [hst]; trivial
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant**: every thread satisfies `TInv`, and a non-zero lock
has a holder. -/
structure InvC (l c : BitVec 64) (cfg : Config isa) : Prop where
  hlc : L4 l ≠ L4 c
  bnd : cfg.Bnd
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv l c t
  held : cfg.mem.finalVal (L4 l) ≠ 0 → ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Holder t

/-- **An instruction step keeps the invariant**; the lock's last write stays,
or the stepping thread holds after the step, or held before it. -/
theorem step_inv {l c : BitVec 64} {tid : Nat} {cfg cfg' : Config isa}
    (h : InvC l c cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.armv8 tid cfg cfg') :
    InvC l c cfg' ∧ (cfg'.mem.lastWrite (L4 l) = cfg.mem.lastWrite (L4 l) ∨
      (∃ t', cfg'.threads[tid]? = some t' ∧ Holder t') ∨ (∃ t, cfg.threads[tid]? = some t ∧ Holder t)) := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hthr : ∀ (i : Nat) u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u →
      TInv l c oc.thread → TInv l c u := fun i u hu hT => by
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact h.thr i u hu
  cases thread_step (h.thr tid t ht) hs ho with
  | quiet hm hT hh =>
    have hfin : oc.mem.finalVal (L4 l) = cfg.mem.finalVal (L4 l) ∧
        oc.mem.lastWrite (L4 l) = cfg.mem.lastWrite (L4 l) := by
      rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
      · exact ⟨rfl, rfl⟩
      · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hlc)
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
    show oc.mem.finalVal (L4 l) = 0
    rw [hm, finalVal_append]; simp

/-- **The invariant holds initially.** -/
theorem inv_init {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) : InvC l c (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  refine ⟨loc_ne hs.hlc, Config.init_bnd _ _, ?_, fun hne => absurd ?_ hne⟩
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    exact ⟨⟨hs.exe, hs.decls, hs.endPc, hs.x0, hs.x1, hs.dl, hs.dc⟩, rfl,
      1, by decide, hs.pc.trans addrOf_0, trivial⟩
  · have := hs.hL0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]

/-- **The invariant along a promise-free trace from a start configuration.** -/
theorem trace_inv {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) (tr : TraceS Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hpf : PromiseFree Arch.armv8 tr.cfg) :
    ∀ i, InvC l c (tr.cfg i) :=
  SpinCommon.trace_inv_of hpf (P := InvC l c) (h0 ▸ inv_init hs) fun _ _ h hi hm =>
    (step_inv h (h.bnd.succ hm) hi).1

end Kraken.Promising.Live.SpinCasInv
