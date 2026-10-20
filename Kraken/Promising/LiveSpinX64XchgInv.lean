/-
**Stage 3: the operational invariant of the x64
`xchg` spinlock** over promise-free `Arch.tso` runs of any number of verbatim
workers (`SpinAbs.spinImageV`) on a valid layout. The twin of
`LiveSpinX64CmpxInv.lean`, with the swap-lock liveness proof's `OwnLe` part
(`LiveSpinSwpInv.lean`): a failing `xchg` still writes.

A thread *holds* the lock (`Holder`) between its successful `xchgl` and its
`movl $0,(lock)`: at the first `testl` with `%eax`'s low word `0`, at the
second `jne` with `ZF` set, or at positions 8–11. `InvX`:

- every thread keeps its image, end address and private memory (`Static`;
  the operands are absolute, so no register is static), has no outstanding
  promise, and sits at a position of `spPcs` (`TInv`);
- **every thread's own lock messages are at or below its coherence view of
  the lock** (`own`, `SpinSwpStep.OwnLe`); hence every `xchgl` reads the
  lock's last write (`TsoRmw.spec_rmwo_tso`'s last clause);
- **if the lock's value is not `0`, some thread holds it** (`held`).

Why `held` is kept: an `xchgl` reads the final value; if its low word is
`0`, the thread becomes a holder; otherwise the final value is not `0`, so
another thread holds the lock and still does, whatever the swap writes. The
only other write to the lock is the holder's release store of `0`.
-/
import Kraken.Promising.LiveSpinX64XchgTrees
import Kraken.Promising.LiveSpinX64Xchg
import Kraken.Promising.LiveTsoRmw
import Kraken.Promising.LiveSpinSwpStep
import Kraken.Promising.CertifyX64
import Kraken.Promising.LiveSpinCommon

namespace Kraken.Promising.Live.SpinX64XchgInv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.TsoRmw Kraken.Promising.Live.SpinX64Step Kraken.Promising.Live.SpinSwpStep
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV symV StartStateV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-- The lock's location. -/
abbrev LkL : Loc := ⟨symV "lock", 4⟩

/-- The counter's location. -/
abbrev CtL : Loc := ⟨symV "counter", 4⟩

/-! ## The per-thread invariant -/

/-- What a worker state never changes: its image, declarations, end address
and private memory at the two words. -/
structure Static (s : isa.State) : Prop where
  exe : s.exe = layout spinImageV
  decls : s.decls = {}
  endPc : s.endPc = pcA 13
  dl : Mem.loadInt s.st.1.dmem (symV "lock") 4 = none
  dc : Mem.loadInt s.st.1.dmem (symV "counter") 4 = none

omit hv in
theorem Static.goto {s : isa.State} (h : Static s) (md : MachineData) (pc : Int64) (hd : md.dmem = s.st.1.dmem) :
    Static (SpinX64XchgTrees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, hd ▸ h.dl, hd ▸ h.dc⟩

/-- **The per-thread invariant.** -/
structure TInv (t : Thread isa) : Prop where
  st : Static t.st
  prom : t.prom = []
  pc : ∃ i ∈ spPcs, t.st.st.2 = pcA i

/-- A thread holds the lock: past a successful `xchgl`, before its release. -/
def Holder (t : Thread isa) : Prop :=
  (t.st.st.2 = pcA 6 ∧ eax t.st.st.1 = 0#32) ∨ (t.st.st.2 = pcA 7 ∧ t.st.st.1.status.zf = true) ∨
    t.st.st.2 ∈ [8, 9, 10, 11].map pcA

theorem Static.at {s : isa.State} (h : Static s) {i : Nat} (hi : i ∈ spPcs) (h13 : i ≠ 13)
    (hpc : s.st.2 = pcA i) : At s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h13 (addrOf_inj hi (by decide) e)⟩

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {t : Thread isa} (h : Static t.st) (hpc : t.st.st.2 = pcA 13)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A t tid mem = none := by
  have : isa.exec t.st = none := by
    show X64.exec t.st = none
    unfold X64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

/-- The coherence views after a step that keeps them. -/
abbrev CohMono (t : Thread isa) (oc : Outcome isa) : Prop := ∀ l', t.views.getCoh l' ≤ oc.thread.views.getCoh l'

theorem cohMono_of_eq {t : Thread isa} {oc : Outcome isa} (h : oc.thread.views.coh = t.views.coh) : CohMono t oc :=
  fun l' => Nat.le_of_eq (getCoh_congr h l').symm

/-! ## The steps, position by position -/

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static t.st) (hp : t.prom = [])
  (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- `movl (lock),%eax`: a logged load of the lock (the last write's value
with an up-to-date coherence view). -/
theorem s1 (hpc : t.st.st.2 = pcA 1) :
    ∃ ts v md, md.dmem = t.st.st.1.dmem ∧ eax md = BitVec.setWidth 32 v ∧
      oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA 2) ∧
      (mem.lastWrite LkL ≤ t.views.getCoh LkL → v = mem.finalVal LkL) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ (∃ ν, TraceEv.read LkL ts v ν ∈ oc.log) ∧ CohMono t oc := by
  obtain ⟨g, hg, hex⟩ := exec_ldl _ (hS.at (by decide) (by decide) hpc) hS.dl
  obtain ⟨ts, v, h1, -, h3, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨ts, v, g v, (hg v).1, (hg v).2, h1, h3, h4, h5, h6, spec_load_coh _ _ hex hs ho⟩

/-- `testl %eax,%eax` (positions 2 and 6). -/
theorem s_test {i : Nat} (hi : i = 2 ∨ i = 6) (hpc : t.st.st.2 = pcA i) :
    ∃ md, md.dmem = t.st.st.1.dmem ∧ (md.status.zf = true ↔ eax t.st.st.1 = 0#32) ∧
      oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA (i + 1)) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  have hi' : i ∈ spPcs := by rcases hi with rfl | rfl <;> decide
  obtain ⟨g, hg, hex⟩ := exec_test _ hi (hS.at hi' (by omega) hpc)
  obtain ⟨h1, ⟨j, h2⟩, h3, h4⟩ := spec_choose _ _ hex hs ho
  exact ⟨g j, (hg j).1, (hg j).2, h2, h1, h3, h4⟩

/-- `jne worker` (positions 3 and 7). -/
theorem s_jne {i : Nat} (hi : i = 3 ∨ i = 7) (hpc : t.st.st.2 = pcA i) :
    oc.mem = mem ∧ oc.thread.st = SpinX64XchgTrees.goto t.st t.st.st.1
      (if t.st.st.1.status.zf then pcA (i + 1) else pcA 1) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  have hi' : i ∈ spPcs := by rcases hi with rfl | rfl <;> decide
  exact spec_done _ _ (exec_jne _ hi (hS.at hi' (by omega) hpc)) hs ho

theorem s4 (hpc : t.st.st.2 = pcA 4) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA 5) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  obtain ⟨md, hd, hex⟩ := exec_mov1 _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, h4⟩ := spec_done _ _ hex hs ho
  exact ⟨md, hd, h2, h1, h3, h4⟩

include hp in
/-- `xchgl %eax,(lock)`: with `OwnLe`, it reads the final value of the lock
into `%eax`, appends its write, and raises its coherence view of the lock to
the new message. -/
theorem s5 (hpc : t.st.st.2 = pcA 5) (hown : OwnLe mem tid LkL (t.views.getCoh LkL)) :
    ∃ md, md.dmem = t.st.st.1.dmem ∧ eax md = BitVec.setWidth 32 (mem.finalVal LkL) ∧
      oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA 6) ∧
      oc.mem = (mem.append { loc := LkL, val := BitVec.setWidth 128 (eax t.st.st.1), tid }).1 ∧
      oc.thread.prom = [] ∧ CohMono t oc ∧ mem.last + 1 ≤ oc.thread.views.getCoh LkL := by
  obtain ⟨g, hg, hex⟩ := exec_xchg _ (hS.at (by decide) (by decide) hpc) hS.dl
  obtain ⟨tr, old, hst, -, -, hpr, -, hco, hcase⟩ := spec_rmwo_tso _ _ rfl hp hex hs ho
  rcases hcase with ⟨h1, -⟩ | ⟨new, h1, -, hm, hlc, hold⟩
  · cases h1
  · cases h1
    have hold := hold hown
    subst hold
    exact ⟨g _, (hg _).1, (hg _).2, hst, hm, hpr, hco, hlc⟩

theorem s8 (hpc : t.st.st.2 = pcA 8) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA 9) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ CohMono t oc := by
  obtain ⟨g, hg, hex⟩ := exec_ldc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨ts, v, h1, -, -, h4, h5, -⟩ := spec_load _ _ hex hs ho
  exact ⟨g v, hg v, h1, h4, h5, spec_load_coh _ _ hex hs ho⟩

theorem s9 (hpc : t.st.st.2 = pcA 9) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA 10) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  obtain ⟨md, hd, hex⟩ := exec_add _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, h4⟩ := spec_done _ _ hex hs ho
  exact ⟨md, hd, h2, h1, h3, h4⟩

include hp in
theorem s10 (hpc : t.st.st.2 = pcA 10) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64XchgTrees.goto t.st md (pcA 11) ∧
      (∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1) ∧ oc.thread.prom = [] ∧ CohMono t oc := by
  obtain ⟨v, md, hd, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
  exact ⟨md, hd, h2, ⟨v, h1⟩, h3, (TsoRmw.spec_store_coh _ _ hp hex hs ho).1⟩

include hp in
/-- The release: a plain store of `0`. -/
theorem s11 (hpc : t.st.st.2 = pcA 11) :
    oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1 ∧
      oc.thread.st = SpinX64XchgTrees.goto t.st t.st.st.1 (pcA 12) ∧ oc.thread.prom = [] ∧
      CohMono t oc ∧ mem.last + 1 ≤ oc.thread.views.getCoh LkL := by
  have hex := exec_unlock _ (hS.at (by decide) (by decide) hpc) hS.dl
  obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
  obtain ⟨h4, h5⟩ := TsoRmw.spec_store_coh _ _ hp hex hs ho
  exact ⟨h1, h2, h3, h4, h5⟩

theorem s12 (hpc : t.st.st.2 = pcA 12) :
    oc.mem = mem ∧ oc.thread.st = SpinX64XchgTrees.goto t.st t.st.st.1 (pcA 13) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_jmp _ (hS.at (by decide) (by decide) hpc)) hs ho

end Steps

/-! ## One thread's step -/

omit hv in
/-- A holder sits at position 6, 7, 8, 9, 10 or 11. -/
theorem Holder.pos {t : Thread isa} (h : Holder t) : ∃ p ∈ [6, 7, 8, 9, 10, 11], t.st.st.2 = pcA p := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact ⟨6, by decide, h⟩
  · exact ⟨7, by decide, h⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h
    · exact ⟨8, by decide, h⟩
    · exact ⟨9, by decide, h⟩
    · exact ⟨10, by decide, h⟩
    · exact ⟨11, by decide, h⟩

omit hv in
theorem holder_of_pc {t : Thread isa} {p : Nat} (hp : p ∈ [8, 9, 10, 11]) (hpc : t.st.st.2 = pcA p) : Holder t :=
  .inr (.inr (by rw [hpc]; exact List.mem_map_of_mem hp))

/-- Not a holder at position `i ∈ spPcs`: at a position other than 8–11, not
at 6 with `%eax`'s low word `0`, and not at 7 with `ZF` set. -/
theorem not_holder_of_pc {t : Thread isa} {i : Nat} (hi : i ∈ spPcs) (hpc : t.st.st.2 = pcA i)
    (h8 : i ∉ [8, 9, 10, 11]) (h6 : i = 6 → eax t.st.st.1 ≠ 0#32) (h7 : i = 7 → t.st.st.1.status.zf = false) :
    ¬ Holder t := by
  rintro (⟨h, hz⟩ | ⟨h, hz⟩ | h)
  · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
    exact h6 rfl hz
  · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
    rw [h7 rfl] at hz; cases hz
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;>
    · obtain rfl := addrOf_inj hi (by decide) (hpc.symm.trans h)
      exact h8 (by decide)

/-- What one step of a thread does. -/
inductive StepRes (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; a holder stays a holder. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1)
      (ht : TInv oc.thread) (hh : Holder t → Holder oc.thread) (hco : CohMono t oc)
  /-- The lock is written (an `xchgl` or the release): the coherence view of
  the lock reaches the new message. -/
  | write (v : Val) (hm : oc.mem = (mem.append { loc := LkL, val := v, tid }).1)
      (ht : TInv oc.thread) (hco : CohMono t oc) (hlc : mem.last + 1 ≤ oc.thread.views.getCoh LkL)
      (hcase : (Holder oc.thread ∧ ¬ Holder t) ∨ (mem.finalVal LkL ≠ 0 ∧ ¬ Holder t) ∨
        (v = 0 ∧ Holder t ∧ oc.thread.st.st.2 = pcA 12))

local macro "tinv" hS:ident hst:ident hd:term "," hp:term "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ $hd, $hp, $j, by decide, by rw [$hst:ident]⟩)

/-- **One thread's step**, by position. -/
theorem thread_step {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv t)
    (hown : OwnLe mem tid LkL (t.views.getCoh LkL))
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) : StepRes tid t mem oc := by
  obtain ⟨i, hi, hpc⟩ := h.pc
  have hS := h.st
  have hi' := hi
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  have nh : ∀ (j : Nat), j ∈ spPcs → (j = 6 → False) → (j = 7 → False) → j ∉ [8, 9, 10, 11] →
      t.st.st.2 = pcA j → ¬ Holder t :=
    fun j hj h6 h7 h8 hpc => not_holder_of_pc hj hpc h8 (fun e => (h6 e).elim) fun e => (h7 e).elim
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨ts, v, md, hd, -, hst, -, hm, hp, -, hco⟩ := s1 hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 2)
      (fun hh => absurd hh (nh 1 hi (by omega) (by omega) (by decide) hpc)) hco
  · obtain ⟨md, hd, -, hst, hm, hp, hco⟩ := s_test hS hs ho (.inl rfl) hpc
    exact .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 3)
      (fun hh => absurd hh (nh 2 hi (by omega) (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · obtain ⟨hm, hst, hp, hco⟩ := s_jne hS hs ho (.inl rfl) hpc
    have hnh := nh 3 hi (by omega) (by omega) (by decide) hpc
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      exact .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 4) (fun hh => absurd hh hnh) (cohMono_of_eq hco)
    · rw [ite_eq_right hz] at hst
      exact .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 1) (fun hh => absurd hh hnh) (cohMono_of_eq hco)
  · obtain ⟨md, hd, hst, hm, hp, hco⟩ := s4 hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 5)
      (fun hh => absurd hh (nh 4 hi (by omega) (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · obtain ⟨md, hd, hz, hst, hm, hp, hco, hlc⟩ := s5 hS h.prom hs ho hpc hown
    have hnh := nh 5 hi (by omega) (by omega) (by decide) hpc
    refine .write _ hm (tinv hS hst hd, hp, 6) hco hlc ?_
    by_cases h0 : BitVec.setWidth 32 (mem.finalVal LkL) = 0#32
    · exact .inl ⟨.inl ⟨by rw [hst], by rw [hst]; exact hz.trans h0⟩, hnh⟩
    · exact .inr (.inl ⟨fun e => h0 (by rw [e]; rfl), hnh⟩)
  · obtain ⟨md, hd, hz, hst, hm, hp, hco⟩ := s_test hS hs ho (.inr rfl) hpc
    refine .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 7) (fun hh => ?_) (cohMono_of_eq hco)
    rcases hh with ⟨-, he⟩ | ⟨h7, -⟩ | h8
    · exact .inr (.inl ⟨by rw [hst], by rw [hst]; exact hz.mpr he⟩)
    · exact absurd (addrOf_inj (by decide) (by decide) (hpc.symm.trans h7)) (by decide)
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h8
      rcases h8 with h | h | h | h <;>
        exact absurd (addrOf_inj (by decide) (by decide) (hpc.symm.trans h)) (by decide)
  · obtain ⟨hm, hst, hp, hco⟩ := s_jne hS hs ho (.inr rfl) hpc
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      exact .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 8)
        (fun _ => holder_of_pc (p := 8) (by decide) (by rw [hst])) (cohMono_of_eq hco)
    · rw [ite_eq_right hz] at hst
      exact .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 1)
        (fun hh => absurd hh (not_holder_of_pc hi hpc (by decide) (by omega) fun _ => by simpa using hz))
        (cohMono_of_eq hco)
  · obtain ⟨md, hd, hst, hm, hp, hco⟩ := s8 hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 9)
      (fun _ => holder_of_pc (p := 9) (by decide) (by rw [hst])) hco
  · obtain ⟨md, hd, hst, hm, hp, hco⟩ := s9 hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst hd, (hp.trans h.prom), 10)
      (fun _ => holder_of_pc (p := 10) (by decide) (by rw [hst])) (cohMono_of_eq hco)
  · obtain ⟨md, hd, hst, hm, hp, hco⟩ := s10 hS h.prom hs ho hpc
    exact .quiet (.inr hm) (tinv hS hst hd, hp, 11)
      (fun _ => holder_of_pc (p := 11) (by decide) (by rw [hst])) hco
  · obtain ⟨hm, hst, hp, hco, hlc⟩ := s11 hS h.prom hs ho hpc
    exact .write _ hm (tinv hS hst rfl, hp, 12) hco hlc
      (.inr (.inr ⟨rfl, holder_of_pc (p := 11) (by decide) hpc, by rw [hst]⟩))
  · obtain ⟨hm, hst, hp, hco⟩ := s12 hS hs ho hpc
    exact .quiet (.inl hm) (tinv hS hst rfl, (hp.trans h.prom), 13)
      (fun hh => absurd hh (nh 12 hi (by omega) (by omega) (by decide) hpc)) (cohMono_of_eq hco)
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant**: every thread satisfies `TInv`, its own lock writes
are at or below its coherence view of the lock, and a non-zero lock has a
holder. -/
structure InvX (cfg : Config isa) : Prop where
  hlc : LkL ≠ CtL
  bnd : cfg.Bnd
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv t
  own : ∀ (i : Nat) t, cfg.threads[i]? = some t → OwnLe cfg.mem i LkL (t.views.getCoh LkL)
  held : cfg.mem.finalVal LkL ≠ 0 → ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Holder t

/-- **An instruction step keeps the invariant**; the lock's last write stays,
or the stepping thread holds after the step, or some thread holds before it. -/
theorem step_inv {tid : Nat} {cfg cfg' : Config isa}
    (h : InvX cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.tso tid cfg cfg') :
    InvX cfg' ∧ (cfg'.mem.lastWrite LkL = cfg.mem.lastWrite LkL ∨
      (∃ t', cfg'.threads[tid]? = some t' ∧ Holder t') ∨
      (∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Holder t)) := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hthr : ∀ (i : Nat) u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u →
      TInv oc.thread → TInv u := fun i u hu hT => by
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact h.thr i u hu
  -- `OwnLe` after the step, from the new memory's shape
  have hown : (∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u →
        OwnLe oc.mem i LkL (u.views.getCoh LkL)) →
      OwnLe oc.mem tid LkL (oc.thread.views.getCoh LkL) →
      ∀ (i : Nat) u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u →
        OwnLe (cfg.withThread tid oc.thread oc.mem).mem i LkL (u.views.getCoh LkL) := by
    intro hother hself i u hu
    rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨hne, hu⟩
    · exact hself
    · exact hother i u hne hu
  have hother : ∀ (w : Msg), w.tid = tid → oc.mem = (cfg.mem.append w).1 →
      ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → OwnLe oc.mem i LkL (u.views.getCoh LkL) :=
    fun w hw hm i u hne hu => hm ▸ (h.own i u hu).append_other (.inr (by rw [hw]; exact Ne.symm hne))
  have hown0 := h.own tid t ht
  have hheld : ∀ (i : Nat) u, cfg.threads[i]? = some u → Holder u → i ≠ tid →
      ∃ i : Nat, ∃ u, (cfg.withThread tid oc.thread oc.mem).threads[i]? = some u ∧ Holder u :=
    fun i u hu hh hne => ⟨i, u, by rw [wt_ne ht hne]; exact hu, hh⟩
  cases thread_step (h.thr tid t ht) hown0 hs ho with
  | quiet hm hT hh hco =>
    have hfin : oc.mem.finalVal LkL = cfg.mem.finalVal LkL ∧
        oc.mem.lastWrite LkL = cfg.mem.lastWrite LkL ∧
        OwnLe oc.mem tid LkL (oc.thread.views.getCoh LkL) ∧
        ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → OwnLe oc.mem i LkL (u.views.getCoh LkL) := by
      rcases hm with hm | ⟨v, hm⟩
      · rw [hm]
        exact ⟨rfl, rfl, hown0.mono (hco _), fun i u _ hu => h.own i u hu⟩
      · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem { loc := CtL, val := v, tid } (Ne.symm h.hlc)
        refine ⟨by rw [hm]; exact a1, by rw [hm]; exact a2, ?_, hother _ rfl hm⟩
        rw [hm]; exact (hown0.append_other (.inl (Ne.symm h.hlc))).mono (hco _)
    refine ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, hown hfin.2.2.2 hfin.2.2.1, fun hne => ?_⟩, .inl hfin.2.1⟩
    obtain ⟨i, u, hu, hh'⟩ := h.held (by rw [← hfin.1]; exact hne)
    by_cases e : i = tid
    · subst e; rw [ht] at hu; cases hu
      exact ⟨i, oc.thread, wt_tid ht, hh hh'⟩
    · exact hheld i u hu hh' e
  | write v hm hT hco hlc hcase =>
    have hself := hm ▸ hown0.append_self (hco _) hlc { loc := LkL, val := v, tid }
    refine ⟨⟨h.hlc, hb, fun i u hu => hthr i u hu hT, hown (hother _ rfl hm) hself, ?_⟩, ?_⟩
    · rcases hcase with ⟨hh, -⟩ | ⟨hnz, hnh⟩ | ⟨rfl, -, -⟩
      · exact fun _ => ⟨tid, oc.thread, wt_tid ht, hh⟩
      · obtain ⟨i, u, hu, hh'⟩ := h.held hnz
        exact fun _ => hheld i u hu hh' fun e => hnh (by subst e; rw [ht] at hu; cases hu; exact hh')
      · intro hne; apply absurd _ hne
        show oc.mem.finalVal LkL = 0
        rw [hm, finalVal_append]; simp
    · rcases hcase with ⟨hh, -⟩ | ⟨hnz, -⟩ | ⟨-, hh, -⟩
      · exact .inr (.inl ⟨oc.thread, wt_tid ht, hh⟩)
      · exact .inr (.inr (h.held hnz))
      · exact .inr (.inr ⟨tid, t, ht, hh⟩)

/-- **The invariant holds initially.** -/
theorem inv_init {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64Xchg.XchgStart states initMem) : InvX (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  refine ⟨loc_ne hs.hlc, Config.init_bnd _ _, ?_, ?_, fun hne => absurd ?_ hne⟩
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    exact ⟨⟨hs.exe, hs.decls, by show s.endPc = _; rw [hs.endPc, hs.exe]; exact label_done,
      X64.EnvG.SpinPublicG.split_dl hs.split, X64.EnvG.SpinPublicG.split_dc hs.split⟩, rfl,
      1, by decide, by show s.st.2 = _; rw [hs.pc, hs.exe]; exact label_worker⟩
  · intro i t _ ts w hw
    simp [Config.init, Memory.get?] at hw
  · have := hs.hL0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]

/-- **The invariant along a promise-free trace from a start configuration.** -/
theorem trace_inv {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64Xchg.XchgStart states initMem) (tr : TraceS Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hpf : PromiseFree Arch.tso tr.cfg) :
    ∀ i, InvX (tr.cfg i) :=
  SpinCommon.trace_inv_of hpf (P := InvX) (h0 ▸ inv_init hs) fun _ _ h hi hm =>
    (step_inv h (h.bnd.succ hm) hi).1

end Kraken.Promising.Live.SpinX64XchgInv
