/-
**Stage 3: the operational invariant of the AArch64
SWP spinlocks** over promise-free runs of any number of workers of a program
`P` with `SwpCode P` (`swpWorker`, `swplWorker`) on a valid layout.

A thread *holds* the lock (`Holder`) between a `SWPA` that read `0` and its
release: at the `CBZ` with `W2 = 0`, or at positions 10–13. `InvS`:

- every thread keeps its program, addresses and private memory, has no
  outstanding promise, and sits at a position of `swPcs` (`TInv`);
- every thread's own writes to the lock are at or below its coherence view
  of the lock (`own`), so its `SWPA` reads the lock's last write
  (`SpinSwpStep.spec_swp`);
- **if the lock's value is not `0`, some thread holds it** (`held`).

A `SWPA` reads the final value `v`. If the low word of `v` is `0` the thread
holds the lock afterwards; otherwise `v ≠ 0`, so some *other* thread holds
it before the step and still does after, whatever the swap wrote. The only
other writes to the lock are releases, which write `0`.

`step_inv`: an instruction step keeps `InvS`; the lock's last write changes
only at a step after which the stepping thread holds, or when some thread
holds before it. The per-position step lemmas (`s1` … `s14`) are reused by
`LiveSpinSwpPF.lean`.
-/
import Kraken.Promising.LiveSpinSwpTrees
import Kraken.Promising.LiveSpinSwpStep
import Kraken.Promising.LiveSpinSwp
import Kraken.Promising.LiveTicketInv

namespace Kraken.Promising.Live.SpinSwpInv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SpinSwpStep
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.SwpTrees (goto)

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)] (hC : SwpCode P)

set_option hygiene false in
local notation "pcA" => (layout P).addrOf

/-- The low word of an `X` register. -/
abbrev w32 (r : UInt64) : BitVec 32 := BitVec.setWidth 32 r.toBitVec

/-! ## The per-thread invariant -/

/-- What a worker state never changes. -/
structure Static (P : Program) (l c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout P
  decls : s.decls = {}
  endPc : s.endPc = (layout P).addrOf 16
  x0 : s.st.1.regs.X0.toBitVec = l
  x1 : s.st.1.regs.X1.toBitVec = c
  dl : Mem.loadInt s.st.1.dmem l 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

theorem Static.goto {l c : BitVec 64} {s : isa.State} (h : Static P l c s) (md : MachineData) (pc : Int64)
    (h0 : md.regs.X0 = s.st.1.regs.X0) (h1 : md.regs.X1 = s.st.1.regs.X1) (hd : md.dmem = s.st.1.dmem) :
    Static P l c (goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, h0 ▸ h.x0, h1 ▸ h.x1, hd ▸ h.dl, hd ▸ h.dc⟩

/-- **The per-thread invariant.** -/
structure TInv (P : Program) (l c : BitVec 64) (t : Thread isa) : Prop where
  st : Static P l c t.st
  prom : t.prom = []
  pc : ∃ i ∈ swPcs, t.st.st.2 = (layout P).addrOf i

/-- A thread holds the lock: past a `SWPA` that read `0`, before its release. -/
def Holder (P : Program) (t : Thread isa) : Prop :=
  (t.st.st.2 = (layout P).addrOf 4 ∧ w32 t.st.st.1.regs.X2 = 0#32) ∨
    t.st.st.2 ∈ [10, 11, 12, 13].map (layout P).addrOf

include hC in
theorem Static.at {l c : BitVec 64} {s : isa.State} (h : Static P l c s) {i : Nat} (hi : i ∈ swPcs)
    (h16 : i ≠ 16) (hpc : s.st.2 = pcA i) : AtG P s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h16 (hC.inj hi (by decide) e)⟩

/-- At the end address the worker has halted. -/
theorem stepOne_end {l c : BitVec 64} {t : Thread isa} (h : Static P l c t.st) (hpc : t.st.st.2 = pcA 16)
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
  (hS : Static P l c t.st) (hp : t.prom = [])
  (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hC hS hs ho

/-- The coherence views after a step that keeps them. -/
abbrev CohMono (t : Thread isa) (oc : Outcome isa) : Prop := ∀ l', t.views.getCoh l' ≤ oc.thread.views.getCoh l'

omit hC hS hs ho in
theorem cohMono_of_eq {t : Thread isa} {oc : Outcome isa} (h : oc.thread.views.coh = t.views.coh) : CohMono t oc :=
  fun l' => Nat.le_of_eq (getCoh_congr h l').symm

theorem s1 (hpc : t.st.st.2 = pcA 1) :
    oc.mem = mem ∧ oc.thread.st = goto t.st { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X3 1#64 } (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (hC.mov _ (hS.at hC (by decide) (by decide) hpc)) hs ho

include hp in
theorem s3 (hpc : t.st.st.2 = pcA 3) (hown : OwnLe mem tid (L4 l) (t.views.getCoh (L4 l))) :
    oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 (mem.finalVal (L4 l)))) }
        (pcA 4) ∧
      oc.mem = (mem.append { loc := L4 l, val := BitVec.setWidth 128 (w32 t.st.st.1.regs.X3), tid }).1 ∧
      oc.thread.prom = [] ∧ CohMono t oc ∧ mem.last + 1 ≤ oc.thread.views.getCoh (L4 l) :=
  spec_swp _ _ rfl hp (hC.swpa _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho hown

theorem s4 (hpc : t.st.st.2 = pcA 4) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1 (if w32 t.st.st.1.regs.X2 = 0#32 then pcA 10 else pcA 6) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (hC.cbz _ (hS.at hC (by decide) (by decide) hpc)) hs ho

theorem s6 (hpc : t.st.st.2 = pcA 6) :
    ∃ ts v, oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 7) ∧
      (mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l) → v = mem.finalVal (L4 l)) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ (∃ ν, TraceEv.read (L4 l) ts v ν ∈ oc.log) ∧ CohMono t oc := by
  have hex := hC.ldr _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl
  obtain ⟨ts, v, h1, -, h3, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨ts, v, h1, h3, h4, h5, h6, spec_load_coh _ _ hex hs ho⟩

theorem s7 (hpc : t.st.st.2 = pcA 7) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1 (if w32 t.st.st.1.regs.X2 = 0#32 then pcA 8 else pcA 6) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (hC.cbnz _ (hS.at hC (by decide) (by decide) hpc)) hs ho

theorem s8 (hpc : t.st.st.2 = pcA 8) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1 (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (hC.btry _ (hS.at hC (by decide) (by decide) hpc)) hs ho

theorem s10 (hpc : t.st.st.2 = pcA 10) :
    ∃ v : Val, oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 11) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ CohMono t oc := by
  have hex := hC.ldrc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc
  obtain ⟨ts, v, h1, -, -, h4, h5, -⟩ := spec_load _ _ hex hs ho
  exact ⟨v, h1, h4, h5, spec_load_coh _ _ hex hs ho⟩

theorem s11 (hpc : t.st.st.2 = pcA 11) :
    oc.mem = mem ∧ oc.thread.st = goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (t.st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      (pcA 12) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (hC.add _ (hS.at hC (by decide) (by decide) hpc)) hs ho

include hp in
theorem s12 (hpc : t.st.st.2 = pcA 12) :
    oc.mem = (mem.append { loc := L4 c, val := (BitVec.setWidth 128
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec)), tid }).1 ∧
      oc.thread.st = goto t.st t.st.st.1 (pcA 13) ∧ oc.thread.prom = [] ∧ CohMono t oc := by
  have hex := hC.strc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc
  obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
  exact ⟨h1, h2, h3, (spec_store_coh _ _ hp hex hs ho).1⟩

include hp in
/-- The release (a store, or an RMW reading the final value): it writes `0`. -/
theorem s13 (hpc : t.st.st.2 = pcA 13) (hown : OwnLe mem tid (L4 l) (t.views.getCoh (L4 l))) :
    oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1 ∧
      (∃ md, oc.thread.st = goto t.st md (pcA 14) ∧ md.regs.X0 = t.st.st.1.regs.X0 ∧
        md.regs.X1 = t.st.st.1.regs.X1 ∧ md.dmem = t.st.st.1.dmem) ∧
      oc.thread.prom = [] ∧ CohMono t oc ∧ mem.last + 1 ≤ oc.thread.views.getCoh (L4 l) := by
  rcases hC.rel _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl with hex | ⟨k, hex⟩
  · obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
    obtain ⟨h4, h5⟩ := spec_store_coh _ _ hp hex hs ho
    exact ⟨h1, ⟨_, h2, rfl, rfl, rfl⟩, h3, h4, h5⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := spec_swp _ _ (g := fun _ => 0#128) rfl hp hex hs ho hown
    exact ⟨h2, ⟨_, h1, rfl, rfl, rfl⟩, h3, h4, h5⟩

theorem s14 (hpc : t.st.st.2 = pcA 14) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1 (pcA 16) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (hC.bdone _ (hS.at hC (by decide) (by decide) hpc)) hs ho

end Steps

/-! ## One thread's step -/

include hC in
/-- A holder sits at position 4, 10, 11, 12 or 13. -/
theorem Holder.pos {t : Thread isa} (h : Holder P t) : ∃ p ∈ [4, 10, 11, 12, 13], t.st.st.2 = pcA p := by
  rcases h with ⟨h, -⟩ | h
  · exact ⟨4, by decide, h⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact ⟨10, by decide, h⟩
    · exact ⟨11, by decide, h⟩
    · exact ⟨12, by decide, h⟩
    · exact ⟨13, by decide, h⟩

theorem holder_of_pc {t : Thread isa} {p : Nat} (hp : p ∈ [10, 11, 12, 13]) (hpc : t.st.st.2 = pcA p) :
    Holder P t :=
  .inr (by rw [hpc]; exact List.mem_map_of_mem hp)

include hC in
/-- Not a holder at position `i ∈ swPcs`: at a position other than 10–13,
and not at 4 with `W2 = 0`. -/
theorem not_holder_of_pc {t : Thread isa} {i : Nat} (hi : i ∈ swPcs) (hpc : t.st.st.2 = pcA i)
    (h10 : i ∉ [10, 11, 12, 13]) (h4 : i = 4 → w32 t.st.st.1.regs.X2 ≠ 0#32) : ¬ Holder P t := by
  rintro (⟨h, hz⟩ | h)
  · obtain rfl := hC.inj hi (by decide) (hpc.symm.trans h)
    exact h4 rfl hz
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;>
    · obtain rfl := hC.inj hi (by decide) (hpc.symm.trans h)
      exact h10 (by decide)

/-- What one step of a thread does. -/
inductive StepRes (P : Program) (l c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) :
    Prop
  /-- The lock is not written; a holder stays a holder. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (ht : TInv P l c oc.thread) (hh : Holder P t → Holder P oc.thread) (hco : CohMono t oc)
  /-- The lock is written (a `SWPA` or the release): the coherence view of
  the lock reaches the new message. -/
  | write (v : Val) (hm : oc.mem = (mem.append { loc := L4 l, val := v, tid }).1)
      (ht : TInv P l c oc.thread) (hco : CohMono t oc) (hlc : mem.last + 1 ≤ oc.thread.views.getCoh (L4 l))
      (hcase : (Holder P oc.thread ∧ ¬ Holder P t) ∨ (mem.finalVal (L4 l) ≠ 0 ∧ ¬ Holder P t) ∨
        (v = 0 ∧ Holder P t ∧ oc.thread.st.st.2 = pcA 14))

local macro "tinv" hS:ident hst:ident hp:term "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ rfl rfl rfl, $hp, $j, by decide, by rw [$hst:ident]⟩)

include hC in
/-- **One thread's step**, by position. -/
theorem thread_step {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv P l c t)
    (hown : OwnLe mem tid (L4 l) (t.views.getCoh (L4 l)))
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : StepRes P l c tid t mem oc := by
  obtain ⟨i, hi, hpc⟩ := h.pc
  have hS := h.st
  have hi' := hi
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  have nh : ∀ (j : Nat), j ∈ swPcs → (j = 4 → False) → j ∉ [10, 11, 12, 13] → t.st.st.2 = pcA j →
      ¬ Holder P t :=
    fun j hj h4 h10 hpc => not_holder_of_pc hC hj hpc h10 fun e => (h4 e).elim
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, hst, hp, hco⟩ := s1 hC hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 3)
      (fun hh => absurd hh (nh 1 hi (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · obtain ⟨hst, hm, hp, hco, hlc⟩ := s3 hC hS h.prom hs ho hpc hown
    have hnh := nh 3 hi (by omega) (by decide) hpc
    refine .write _ hm (tinv hS hst hp, 4) hco hlc ?_
    by_cases hz : w32 oc.thread.st.st.1.regs.X2 = 0#32
    · exact .inl ⟨.inl ⟨by rw [hst], hz⟩, hnh⟩
    · refine .inr (.inl ⟨fun e => hz ?_, hnh⟩)
      rw [hst]; show BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (mem.finalVal (L4 l)))) = 0#32
      rw [e]; rfl
  · obtain ⟨hm, hst, hp, hco⟩ := s4 hC hS hs ho hpc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 10)
        (fun _ => holder_of_pc (p := 10) (by decide) (by rw [hst])) (cohMono_of_eq hco)
    · rw [ite_eq_right hz] at hst
      exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 6)
        (fun hh => absurd hh (not_holder_of_pc hC hi hpc (by decide) fun _ => hz)) (cohMono_of_eq hco)
  · obtain ⟨ts, v, hst, -, hm, hp, -, hco⟩ := s6 hC hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 7)
      (fun hh => absurd hh (nh 6 hi (by omega) (by decide) hpc)) hco
  · obtain ⟨hm, hst, hp, hco⟩ := s7 hC hS hs ho hpc
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 8)
        (fun hh => absurd hh (nh 7 hi (by omega) (by decide) hpc)) (cohMono_of_eq hco)
    · rw [ite_eq_right hz] at hst
      exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 6)
        (fun hh => absurd hh (nh 7 hi (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · obtain ⟨hm, hst, hp, hco⟩ := s8 hC hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 3)
      (fun hh => absurd hh (nh 8 hi (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · obtain ⟨v, hst, hm, hp, hco⟩ := s10 hC hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 11)
      (fun _ => holder_of_pc (p := 11) (by decide) (by rw [hst])) hco
  · obtain ⟨hm, hst, hp, hco⟩ := s11 hC hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 12)
      (fun _ => holder_of_pc (p := 12) (by decide) (by rw [hst])) (cohMono_of_eq hco)
  · obtain ⟨hm, hst, hp, hco⟩ := s12 hC hS h.prom hs ho hpc
    exact .quiet (.inr ⟨_, hm⟩) (tinv hS hst hp, 13)
      (fun _ => holder_of_pc (p := 13) (by decide) (by rw [hst])) hco
  · obtain ⟨hm, ⟨md, hst, h0, h1, hd⟩, hp, hco, hlc⟩ := s13 hC hS h.prom hs ho hpc hown
    exact .write _ hm ⟨by rw [hst]; exact hS.goto _ _ h0 h1 hd, hp, 14, by decide, by rw [hst]⟩ hco hlc
      (.inr (.inr ⟨rfl, holder_of_pc (p := 13) (by decide) hpc, by rw [hst]⟩))
  · obtain ⟨hm, hst, hp, hco⟩ := s14 hC hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst (hp.trans h.prom), 16)
      (fun hh => absurd hh (nh 14 hi (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant**: every thread satisfies `TInv`, its own lock writes
are at or below its coherence view of the lock, and a non-zero lock has a
holder. -/
structure InvS (P : Program) (l c : BitVec 64) (cfg : Config isa) : Prop where
  hlc : L4 l ≠ L4 c
  bnd : cfg.Bnd
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv P l c t
  own : ∀ (i : Nat) t, cfg.threads[i]? = some t → OwnLe cfg.mem i (L4 l) (t.views.getCoh (L4 l))
  held : cfg.mem.finalVal (L4 l) ≠ 0 → ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Holder P t

include hC in
/-- **An instruction step keeps the invariant**; the lock's last write stays,
or the stepping thread holds after the step, or some thread holds before it. -/
theorem step_inv {l c : BitVec 64} {tid : Nat} {cfg cfg' : Config isa}
    (h : InvS P l c cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.armv8 tid cfg cfg') :
    InvS P l c cfg' ∧ (cfg'.mem.lastWrite (L4 l) = cfg.mem.lastWrite (L4 l) ∨
      (∃ t', cfg'.threads[tid]? = some t' ∧ Holder P t') ∨
      (∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Holder P t)) := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hthr : ∀ (i : Nat) u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u →
      TInv P l c oc.thread → TInv P l c u := fun i u hu hT => by
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact h.thr i u hu
  -- `OwnLe` after the step, from the new memory's shape
  have hown : (∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u →
        OwnLe oc.mem i (L4 l) (u.views.getCoh (L4 l))) →
      OwnLe oc.mem tid (L4 l) (oc.thread.views.getCoh (L4 l)) →
      ∀ (i : Nat) u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u →
        OwnLe (cfg.withThread tid oc.thread oc.mem).mem i (L4 l) (u.views.getCoh (L4 l)) := by
    intro hother hself i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨hne, hu⟩
    · exact hself
    · exact hother i u hne hu
  have hother : ∀ (w : Msg), w.tid = tid → oc.mem = (cfg.mem.append w).1 →
      ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → OwnLe oc.mem i (L4 l) (u.views.getCoh (L4 l)) :=
    fun w hw hm i u hne hu => hm ▸ (h.own i u hu).append_other (.inr (by rw [hw]; exact Ne.symm hne))
  have hown0 := h.own tid t ht
  have hheld : ∀ (i : Nat) u, cfg.threads[i]? = some u → Holder P u → i ≠ tid →
      ∃ i : Nat, ∃ u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u ∧ Holder P u :=
    fun i u hu hh hne => ⟨i, u, by rw [wt_ne ht hne]; exact hu, hh⟩
  cases thread_step hC (h.thr tid t ht) hown0 hs ho with
  | quiet hm hT hh hco =>
    have hfin : oc.mem.finalVal (L4 l) = cfg.mem.finalVal (L4 l) ∧
        oc.mem.lastWrite (L4 l) = cfg.mem.lastWrite (L4 l) ∧
        OwnLe oc.mem tid (L4 l) (oc.thread.views.getCoh (L4 l)) ∧
        ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → OwnLe oc.mem i (L4 l) (u.views.getCoh (L4 l)) := by
      rcases hm with hm | ⟨v, hm⟩
      · rw [hm]
        exact ⟨rfl, rfl, hown0.mono (hco _), fun i u _ hu => h.own i u hu⟩
      · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hlc)
        refine ⟨by rw [hm]; exact a1, by rw [hm]; exact a2, ?_, hother _ rfl hm⟩
        rw [hm]; exact (hown0.append_other (.inl (Ne.symm h.hlc))).mono (hco _)
    refine ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, hown hfin.2.2.2 hfin.2.2.1, fun hne => ?_⟩, .inl hfin.2.1⟩
    obtain ⟨i, u, hu, hh'⟩ := h.held (by rw [← hfin.1]; exact hne)
    by_cases e : i = tid
    · subst e; rw [ht] at hu; cases hu
      exact ⟨i, oc.thread, wt_tid ht, hh hh'⟩
    · exact hheld i u hu hh' e
  | write v hm hT hco hlc hcase =>
    have hself := hm ▸ hown0.append_self (hco _) hlc { loc := L4 l, val := v, tid }
    refine ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, hown (hother _ rfl hm) hself, ?_⟩, ?_⟩
    · rcases hcase with ⟨hh, -⟩ | ⟨hnz, hnh⟩ | ⟨rfl, -, -⟩
      · exact fun _ => ⟨tid, oc.thread, wt_tid ht, hh⟩
      · obtain ⟨i, u, hu, hh'⟩ := h.held hnz
        exact fun _ => hheld i u hu hh' fun e => hnh (by subst e; rw [ht] at hu; cases hu; exact hh')
      · intro hne; apply absurd _ hne
        show oc.mem.finalVal (L4 l) = 0
        rw [hm, finalVal_append]; simp
    · rcases hcase with ⟨hh, -⟩ | ⟨hnz, -⟩ | ⟨-, hh, -⟩
      · exact .inr (.inl ⟨oc.thread, wt_tid ht, hh⟩)
      · exact .inr (.inr (h.held hnz))
      · exact .inr (.inr ⟨tid, t, ht, hh⟩)

include hC in
/-- **The invariant holds initially.** -/
theorem inv_init {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG (SpinSwp.StartG P) l c states initMem) : InvS P l c (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  refine ⟨loc_ne hs.hlc, Config.init_bnd _ _, ?_, ?_, fun hne => absurd ?_ hne⟩
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    exact ⟨⟨hs.exe, hs.decls, hs.endPc, hs.x0, hs.x1, hs.dl, hs.dc⟩, rfl, 1, by decide, hs.pc.trans hC.a0⟩
  · intro i t _ ts w hw
    simp [Config.init, Memory.get?] at hw
  · have := hs.hL0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]

include hC in
/-- **The invariant along a promise-free trace from a start configuration.** -/
theorem trace_inv {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG (SpinSwp.StartG P) l c states initMem) (tr : TraceS Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hpf : PromiseFree Arch.armv8 tr.cfg) :
    ∀ i, InvS P l c (tr.cfg i) :=
  SpinCommon.trace_inv_of hpf (P := InvS P l c) (h0 ▸ inv_init hC hs) fun _ _ h hi hm =>
    (step_inv hC h (h.bnd.succ hm) hi).1

end Kraken.Promising.Live.SpinSwpInv
