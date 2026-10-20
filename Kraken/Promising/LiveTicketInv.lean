/-
**Stage 3, O1: the operational invariant of the ticket
lock** over promise-free runs of `N` workers `tkWorker` on a valid layout.

The quantities: `xc`, the value of `next` (`x`; the number of tickets
taken), and `m`, the value of `owner` (`o`; the ticket now served). A thread
past its `LDADDA` holds the ticket `tk t`, the low word of `X3`. `InvW`:

- the last write to `next` is `xc`, to `owner` is `m`, every value of
  `owner` in memory is at most `m`, and `m ≤ xc ≤ N`;
- every write to `next` is by a thread holding a ticket;
- the tickets are pairwise distinct and are exactly `0, …, xc - 1`;
- every thread keeps its program, addresses and private memory, has no
  outstanding promise, and its registers satisfy `PcInv m` at its pc:
  a waiter holds a ticket `≥ m`, the thread in the critical section holds
  `m`, a thread past its `STLR` holds a ticket `< m`.

`step_inv`: an instruction step keeps `InvW`, `m` grows by one exactly at the
`STLR` of the thread holding `m`, and otherwise stays.

The per-position step lemmas (`s1` … `s12`) describe each instruction's
outcomes; the liveness proof (`LiveTicketPF.lean`) reuses them.
-/
import Kraken.Promising.LiveTicketTrees
import Kraken.Promising.LiveTicketStep
import Kraken.Promising.LiveTicket
import Kraken.Promising.LiveTicketGlobal

namespace Kraken.Promising.Live.TicketInv

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketStep
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

/-! ## Words -/

/-- The low word of a register, as a number. -/
def wn (r : UInt64) : Nat := r.toNat % 2 ^ 32

theorem wn_ofBitVec (v : BitVec 64) : wn (UInt64.ofBitVec v) = v.toNat % 2 ^ 32 := rfl

theorem toNat_w32 (r : UInt64) : (w32 r).toNat = wn r := by
  simp [w32, wn, BitVec.toNat_setWidth]

theorem w32_eq_iff (a b : UInt64) : w32 a = w32 b ↔ wn a = wn b := by
  rw [← toNat_w32, ← toNat_w32]
  exact ⟨fun h => h ▸ rfl, fun h => BitVec.eq_of_toNat_eq h⟩

/-- A 32-bit value widened to a register, as a number (shared by
`TicketSolo.wn_setWidth` and `TicketLoopHolder.wn_setWidth'`). -/
theorem wn_setWidth32 (v : BitVec 128) : wn (UInt64.ofBitVec (BitVec.setWidth 64 (BitVec.setWidth 32 v))) =
    v.toNat % 2 ^ 32 := by
  simp [wn, BitVec.toNat_setWidth] <;> omega

/-- The low word of a register, widened (shared by
`TicketSolo.val_setWidth` and `TicketLoopHolder.val_setWidth'`). -/
theorem val_setWidth32 (r : UInt64) : (BitVec.setWidth 128 (BitVec.setWidth 32 r.toBitVec)).toNat = wn r := by
  simp [wn, BitVec.toNat_setWidth] <;> omega

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkWorker).addrOf

/-- The location of a 4-byte word. -/
abbrev L4 (a : BitVec 64) : Loc := ⟨a, 4⟩

/-! ## The per-thread invariant -/

/-- What a worker state never changes: its program, end address, address
registers and private memory at the three words. -/
structure Static (x o c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout tkWorker
  decls : s.decls = {}
  endPc : s.endPc = pcA 14
  x0 : s.st.1.regs.X0.toBitVec = x
  x1 : s.st.1.regs.X1.toBitVec = o
  x2 : s.st.1.regs.X2.toBitVec = c
  dx : Mem.loadInt s.st.1.dmem x 4 = none
  dO : Mem.loadInt s.st.1.dmem o 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

omit hv in
theorem Static.goto {x o c : BitVec 64} {s : isa.State} (h : Static x o c s) (md : MachineData) (pc : Int64)
    (h0 : md.regs.X0 = s.st.1.regs.X0) (h1 : md.regs.X1 = s.st.1.regs.X1) (h2 : md.regs.X2 = s.st.1.regs.X2)
    (hd : md.dmem = s.st.1.dmem) : Static x o c (TicketTrees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, h0 ▸ h.x0, h1 ▸ h.x1, h2 ▸ h.x2, hd ▸ h.dx, hd ▸ h.dO, hd ▸ h.dc⟩

/-- The register facts at each pc position, for the ticket now served `m`. -/
def PcInv (m : Nat) (s : MachineData) : Nat → Prop
  | 1 => True
  | 2 => wn s.regs.X6 = 1
  | 4 => m ≤ wn s.regs.X3
  | 5 => m ≤ wn s.regs.X3 ∧ wn s.regs.X4 ≤ m
  | 6 => m ≤ wn s.regs.X3 ∧ (s.status.z = true → wn s.regs.X3 = m)
  | 7 | 8 | 9 | 10 => wn s.regs.X3 = m
  | 11 => wn s.regs.X3 = m ∧ wn s.regs.X4 = m + 1
  | 12 | 14 => wn s.regs.X3 < m
  | _ => False

/-- **The per-thread invariant.** -/
structure TInv (x o c : BitVec 64) (m : Nat) (t : Thread isa) : Prop where
  st : Static x o c t.st
  prom : t.prom = []
  pc : ∃ i ∈ tkPcs, t.st.st.2 = pcA i ∧ PcInv m t.st.st.1 i

/-- A thread holds a ticket: it is past its `LDADDA`. -/
def Ticketed (t : Thread isa) : Prop := t.st.st.2 ≠ pcA 1 ∧ t.st.st.2 ≠ pcA 2

/-- The ticket of a thread. -/
def tk (t : Thread isa) : Nat := wn t.st.st.1.regs.X3

theorem Static.at {x o c : BitVec 64} {s : isa.State} (h : Static x o c s) {i : Nat} (hi : i ∈ tkPcs)
    (h14 : i ≠ 14) (hpc : s.st.2 = pcA i) : At s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h14 (addrOf_inj hi (by decide) e)⟩

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {x o c : BitVec 64} {t : Thread isa} (h : Static x o c t.st) (hpc : t.st.st.2 = pcA 14)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A t tid mem = none := by
  have : isa.exec t.st = none := by
    show AArch64.exec t.st = none
    unfold AArch64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

/-! ## The steps, position by position -/

section Steps

variable {x o c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static x o c t.st) (hp : t.prom = [])
  (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

theorem s1 (hpc : t.st.st.2 = pcA 1) :
    oc.mem = mem ∧ oc.thread.st = TicketTrees.goto t.st
      { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X6 1#64 } (pcA 2) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s2 (hpc : t.st.st.2 = pcA 2) :
    ∃ tr old, oc.thread.st = TicketTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) } (pcA 4) ∧
      mem.read? (L4 x) tr = some old ∧ mem.atomic (L4 x) tid tr (mem.last + 1) = true ∧
      oc.mem = (mem.append { loc := L4 x, val := (BitVec.setWidth 128
        (BitVec.setWidth 32 old + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)), tid }).1 ∧
      oc.thread.prom = [] :=
  spec_rmw _ _ rfl hp (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho

theorem s4 (hpc : t.st.st.2 = pcA 4) :
    ∃ ts v, oc.thread.st = TicketTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 5) ∧
      mem.read? (L4 o) ts = some v ∧ (mem.lastWrite (L4 o) ≤ t.views.getCoh (L4 o) → v = mem.finalVal (L4 o)) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ ∃ ν, TraceEv.read (L4 o) ts v ν ∈ oc.log :=
  spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho

theorem s5 (hpc : t.st.st.2 = pcA 5) :
    ∃ sf : StatusFlags, oc.thread.st = TicketTrees.goto t.st { t.st.st.1 with status := sf } (pcA 6) ∧
      (sf.z = true ↔ wn t.st.st.1.regs.X4 = wn t.st.st.1.regs.X3) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  obtain ⟨sf, hex, hz⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, h4⟩ := spec_done _ _ hex hs ho
  exact ⟨sf, h2, hz.trans (w32_eq_iff _ _), h1, h3, h4⟩

theorem s6 (hpc : t.st.st.2 = pcA 6) :
    oc.mem = mem ∧ oc.thread.st = TicketTrees.goto t.st t.st.st.1
      (if t.st.st.1.status.z = true then pcA 7 else pcA 4) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s7 (hpc : t.st.st.2 = pcA 7) :
    ∃ ts v, oc.thread.st = TicketTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 8) ∧
      mem.read? (L4 c) ts = some v ∧ oc.mem = mem ∧ oc.thread.prom = t.prom := by
  obtain ⟨ts, v, h1, h2, -, h4, h5, -⟩ :=
    spec_load _ _ (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
  exact ⟨ts, v, h1, h2, h4, h5⟩

theorem s8 (hpc : t.st.st.2 = pcA 8) :
    oc.mem = mem ∧ oc.thread.st = TicketTrees.goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (t.st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      (pcA 9) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s9 (hpc : t.st.st.2 = pcA 9) :
    oc.mem = (mem.append { loc := L4 c, val := (BitVec.setWidth 128
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec)), tid }).1 ∧
      oc.thread.st = TicketTrees.goto t.st t.st.st.1 (pcA 10) ∧ oc.thread.prom = [] :=
  spec_store _ _ hp (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho

theorem s10 (hpc : t.st.st.2 = pcA 10) :
    oc.mem = mem ∧ oc.thread.st = TicketTrees.goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (t.st.st.1.regs.X3.toBitVec.take 32 + 1#32)) }
      (pcA 11) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s11 (hpc : t.st.st.2 = pcA 11) :
    oc.mem = (mem.append { loc := L4 o, val := (BitVec.setWidth 128
      (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec)), tid }).1 ∧
      oc.thread.st = TicketTrees.goto t.st t.st.st.1 (pcA 12) ∧ oc.thread.prom = [] :=
  spec_store _ _ hp (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho

theorem s12 (hpc : t.st.st.2 = pcA 12) :
    oc.mem = mem ∧ oc.thread.st = TicketTrees.goto t.st t.st.st.1 (pcA 14) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_b_done _ (hS.at (by decide) (by decide) hpc)) hs ho

end Steps

/-! ## One thread's step -/

theorem TInv.pcinv {x o c : BitVec 64} {m : Nat} {t : Thread isa} (h : TInv x o c m t) {i : Nat}
    (hi : i ∈ tkPcs) (hpc : t.st.st.2 = pcA i) : PcInv m t.st.st.1 i := by
  obtain ⟨j, hj, hpc', hinv⟩ := h.pc
  rw [hpc] at hpc'
  rwa [addrOf_inj hi hj hpc']

theorem ticketed_at {t : Thread isa} {i : Nat} (hpc : t.st.st.2 = pcA i) (hi : i ∈ tkPcs) (h1 : i ≠ 1)
    (h2 : i ≠ 2) : Ticketed t :=
  ⟨fun e => h1 (addrOf_inj hi (by decide) (hpc.symm.trans e)),
    fun e => h2 (addrOf_inj hi (by decide) (hpc.symm.trans e))⟩

/-- What one step of a thread does to the invariant's quantities. -/
inductive StepRes (x o c : BitVec 64) (m xc tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) :
    Prop
  /-- No ticket taken, `owner` not written. -/
  | same (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (ht : TInv x o c m oc.thread) (htk : Ticketed oc.thread ↔ Ticketed t)
      (hk : Ticketed t → tk oc.thread = tk t)
  /-- `LDADDA`: the ticket `xc` taken. -/
  | tkt (v : Val) (hv : v.toNat = xc + 1) (hm : oc.mem = (mem.append { loc := L4 x, val := v, tid }).1)
      (ht : TInv x o c m oc.thread) (h0 : ¬ Ticketed t) (h1 : Ticketed oc.thread) (hk : tk oc.thread = xc)
  /-- `STLR`: `owner := m + 1` by the holder of `m`. -/
  | rel (v : Val) (hv : v.toNat = m + 1) (hm : oc.mem = (mem.append { loc := L4 o, val := v, tid }).1)
      (ht : TInv x o c (m + 1) oc.thread) (h0 : Ticketed t) (h1 : Ticketed oc.thread) (hk0 : tk t = m)
      (hk : tk oc.thread = m)

local macro "tinv" hS:ident hst:ident hp:term "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hS).goto _ _ rfl rfl rfl rfl, $hp, $j, by decide, by rw [$hst:ident] <;> rfl, ?_⟩)

/-- **One thread's step**, by position. -/
theorem thread_step {x o c : BitVec 64} {m xc tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv x o c m t)
    (hxc : xc + 1 < 2 ^ 32) (hmxc : m ≤ xc) (hfx : (mem.finalVal (L4 x)).toNat = xc)
    (hown : ∀ ts w, mem.get? ts = some w → w.loc = L4 x → w.tid = tid → Ticketed t)
    (hov : ∀ ts v, mem.read? (L4 o) ts = some v → v.toNat ≤ m)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : StepRes x o c m xc tid t mem oc := by
  obtain ⟨i, hi, hpc, hinv⟩ := h.pc
  have hS := h.st
  have hT : ∀ j, t.st.st.2 = pcA j → j ∈ tkPcs → j ≠ 1 → j ≠ 2 → Ticketed t :=
    fun j hj hjm h1 h2 => ticketed_at hj hjm h1 h2
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, hst, hp, -⟩ := s1 hS hs ho hpc
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 2) ⟨fun h' => absurd (by rw [hst] <;> rfl) h'.2,
      fun h' => absurd hpc h'.1⟩ (fun h' => absurd hpc h'.1)
    rw [hst]; rfl
  · obtain ⟨tr, old, hst, hrd, hat, hm, hp⟩ := s2 hS h.prom hs ho hpc
    obtain ⟨-, rfl⟩ := atomic_lastWrite mem (L4 x) tid hrd hat
      (fun ts w hw hl he => absurd hpc (hown ts w hw hl he).2)
    have h6 : wn t.st.st.1.regs.X6 = 1 := hinv
    have hk : tk oc.thread = xc := by
      unfold tk; rw [hst, ← hfx]; show (BitVec.setWidth 64 (BitVec.setWidth 32 _)).toNat % 2 ^ 32 = _
      simp [BitVec.toNat_setWidth]; omega
    refine .tkt _ ?_ hm (tinv hS hst hp, 4) (fun h' => h'.2 hpc)
      (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide)) hk
    · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hfx]
      simp only [wn] at h6
      have : t.st.st.1.regs.X6.toBitVec.toNat % 2 ^ 32 = 1 := h6
      rw [this, Nat.mod_eq_of_lt (by omega : xc < 2 ^ 32)]
      omega
    · show m ≤ tk oc.thread
      omega
  · obtain ⟨ts, v, hst, hrd, -, hm, hp, -⟩ := s4 hS hs ho hpc
    have hv := hov ts v hrd
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 5)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 4 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]
    refine ⟨hinv, ?_⟩
    show (BitVec.setWidth 64 (BitVec.setWidth 32 v)).toNat % 2 ^ 32 ≤ m
    simp only [BitVec.toNat_setWidth]; omega
  · obtain ⟨sf, hst, hz, hm, hp, -⟩ := s5 hS hs ho hpc
    obtain ⟨h1, h2⟩ := (hinv : m ≤ wn t.st.st.1.regs.X3 ∧ wn t.st.st.1.regs.X4 ≤ m)
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 6)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 5 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]
    show m ≤ wn t.st.st.1.regs.X3 ∧ (sf.z = true → wn t.st.st.1.regs.X3 = m)
    exact ⟨h1, fun hz' => by have := hz.mp hz'; omega⟩
  · obtain ⟨hm, hst, hp, -⟩ := s6 hS hs ho hpc
    obtain ⟨h1, h2⟩ := (hinv : m ≤ wn t.st.st.1.regs.X3 ∧ (t.st.st.1.status.z = true → wn t.st.st.1.regs.X3 = m))
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 7)
        (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
          (hT 6 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
      rw [hst]; exact h2 hz
    · rw [ite_eq_right hz] at hst
      refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 4)
        (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
          (hT 6 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
      rw [hst]; exact h1
  · obtain ⟨ts, v, hst, -, hm, hp⟩ := s7 hS hs ho hpc
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 8)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 7 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]; exact hinv
  · obtain ⟨hm, hst, hp, -⟩ := s8 hS hs ho hpc
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 9)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 8 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]; exact hinv
  · obtain ⟨hm, hst, hp⟩ := s9 hS h.prom hs ho hpc
    refine .same (.inr ⟨_, hm⟩) (tinv hS hst hp, 10)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 9 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]; exact hinv
  · obtain ⟨hm, hst, hp, -⟩ := s10 hS hs ho hpc
    have h3 : wn t.st.st.1.regs.X3 = m := hinv
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 11)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 10 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]
    refine ⟨h3, ?_⟩
    show (BitVec.setWidth 64 (t.st.st.1.regs.X3.toBitVec.take 32 + 1#32)).toNat % 2 ^ 32 = m + 1
    simp only [wn] at h3
    have : t.st.st.1.regs.X3.toBitVec.toNat % 2 ^ 32 = m := h3
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.take, BitVec.extractLsb'_toNat,
      Nat.shiftRight_zero, this, BitVec.toNat_ofNat]
    omega
  · obtain ⟨hm, hst, hp⟩ := s11 hS h.prom hs ho hpc
    obtain ⟨h3, h4⟩ := (hinv : wn t.st.st.1.regs.X3 = m ∧ wn t.st.st.1.regs.X4 = m + 1)
    refine .rel _ ?_ hm (tinv hS hst hp, 12) (hT 11 hpc (by decide) (by decide) (by decide))
      (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide)) h3 (by unfold tk; rw [hst]; exact h3)
    · rw [← h4]; simp [BitVec.toNat_setWidth, wn]; omega
    · rw [hst]; show wn t.st.st.1.regs.X3 < m + 1; omega
  · obtain ⟨hm, hst, hp, -⟩ := s12 hS hs ho hpc
    refine .same (.inl hm) (tinv hS hst (hp.trans h.prom), 14)
      (iff_of_true (ticketed_at (by rw [hst] <;> rfl) (by decide) (by decide) (by decide))
        (hT 12 hpc (by decide) (by decide) (by decide))) (fun _ => by unfold tk; rw [hst] <;> rfl)
    rw [hst]; exact hinv
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant** of a configuration with `xc` tickets taken and ticket
`m` served. -/
structure InvW (N : Nat) (x o c : BitVec 64) (xc m : Nat) (cfg : Config isa) : Prop where
  size : cfg.threads.size = N
  N32 : N + 1 < 2 ^ 32
  hxo : L4 x ≠ L4 o
  hxc : L4 x ≠ L4 c
  hoc : L4 o ≠ L4 c
  bnd : cfg.Bnd
  fx : (cfg.mem.finalVal (L4 x)).toNat = xc
  fo : (cfg.mem.finalVal (L4 o)).toNat = m
  ov : ∀ ts v, cfg.mem.read? (L4 o) ts = some v → v.toNat ≤ m
  mxc : m ≤ xc
  xcN : xc ≤ N
  xmsg : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x → ∃ tw, cfg.threads[w.tid]? = some tw ∧ Ticketed tw
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv x o c m t
  tkLt : ∀ (i : Nat) t, cfg.threads[i]? = some t → Ticketed t → tk t < xc
  tkInj : ∀ (i j : Nat) ti tj, cfg.threads[i]? = some ti → cfg.threads[j]? = some tj → Ticketed ti → Ticketed tj →
    tk ti = tk tj → i = j
  tkSurj : ∀ k < xc, ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Ticketed t ∧ tk t = k

/-- Pigeonhole: an injection of `[0, a)` into `[0, n)` has `a ≤ n`. (The
instance-free `SpinCommon.pigeon`.) -/
theorem pigeon : ∀ (n a : Nat) (f : Nat → Nat), (∀ k < a, f k < n) →
    (∀ i j, i < a → j < a → f i = f j → i = j) → a ≤ n :=
  SpinCommon.pigeon

/-! `wt_get`, `wt_tid`, `wt_ne`, `mem_frame` and `loc_ne` are the
ISA-generic, instance-free `SpinStep` lemmas (`LiveSpinStep.lean`), stated
here with this file's section instance as before. -/

theorem wt_get {cfg : Config isa} {tid j : Nat} {t t' u : Thread isa} {mem' : Memory}
    (ht : cfg.threads[tid]? = some t) (h : (cfg.withThread tid t' mem').threads[j]? = some u) :
    (j = tid ∧ u = t') ∨ (j ≠ tid ∧ cfg.threads[j]? = some u) :=
  SpinStep.wt_get ht h

theorem wt_tid {cfg : Config isa} {tid : Nat} {t t' : Thread isa} {mem' : Memory}
    (ht : cfg.threads[tid]? = some t) : (cfg.withThread tid t' mem').threads[tid]? = some t' :=
  SpinStep.wt_tid ht

theorem wt_ne {cfg : Config isa} {tid j : Nat} {t t' : Thread isa} {mem' : Memory}
    (ht : cfg.threads[tid]? = some t) (hj : j ≠ tid) :
    (cfg.withThread tid t' mem').threads[j]? = cfg.threads[j]? :=
  SpinStep.wt_ne ht hj

/-- An append to another location: the memory facts about `l'` unchanged. -/
theorem mem_frame (mem : Memory) (w : Msg) {l' : Loc} (hl : w.loc ≠ l') :
    (mem.append w).1.finalVal l' = mem.finalVal l' ∧ (mem.append w).1.lastWrite l' = mem.lastWrite l' ∧
    (∀ ts v, (mem.append w).1.read? l' ts = some v → mem.read? l' ts = some v) ∧
    (∀ ts w', (mem.append w).1.get? ts = some w' → w'.loc = l' → mem.get? ts = some w') :=
  SpinStep.mem_frame mem w hl

/-- A waiter of the old invariant is a waiter of the next `m`, if it does not
hold `m`. -/
theorem PcInv.bump {m : Nat} {s : MachineData} {i : Nat} (hp : PcInv m s i) (hi : i ∈ tkPcs)
    (hne : i ≠ 1 → i ≠ 2 → wn s.regs.X3 ≠ m) : PcInv (m + 1) s i := by
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [PcInv] at hp ⊢ <;> first | exact hp | trivial |
      (have := hne (by decide) (by decide); first | omega | exact ⟨by omega, fun hz => absurd (hp.2 hz) this⟩)

section Pres

variable {N xc m tid : Nat} {x o c : BitVec 64} {cfg : Config isa} {t t' : Thread isa} {mem' : Memory}
  (h : InvW N x o c xc m cfg) (ht : cfg.threads[tid]? = some t) (hb : (cfg.withThread tid t' mem').Bnd)

include h ht hb

omit hb in
/-- The ticket facts after a step that keeps the thread's ticket. -/
theorem tk_frame (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hm4 : ∀ ts w, mem'.get? ts = some w → w.loc = L4 x → cfg.mem.get? ts = some w) :
    let cfg' := cfg.withThread tid t' mem'
    (∀ ts w, cfg'.mem.get? ts = some w → w.loc = L4 x → ∃ tw, cfg'.threads[w.tid]? = some tw ∧ Ticketed tw) ∧
    (∀ (i : Nat) u, cfg'.threads[i]? = some u → Ticketed u → tk u < xc) ∧
    (∀ (i j : Nat) ti tj, cfg'.threads[i]? = some ti → cfg'.threads[j]? = some tj → Ticketed ti → Ticketed tj →
      tk ti = tk tj → i = j) ∧
    (∀ k < xc, ∃ i : Nat, ∃ u, cfg'.threads[i]? = some u ∧ Ticketed u ∧ tk u = k) :=
  have f := TicketGlobal.TkFacts.frame (Ticketed := Ticketed) (tk := tk) ⟨h.xmsg, h.tkLt, h.tkInj, h.tkSurj⟩ ht
    htk hk hm4
  ⟨f.xmsg, f.tkLt, f.tkInj, f.tkSurj⟩

/-- A step that takes no ticket and does not write `owner`. -/
theorem inv_same (hT : TInv x o c m t') (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hm : mem' = cfg.mem ∨ ∃ v, mem' = (cfg.mem.append { loc := L4 c, val := v, tid }).1) :
    InvW N x o c xc m (cfg.withThread tid t' mem') := by
  have hmem : mem'.finalVal (L4 x) = cfg.mem.finalVal (L4 x) ∧ mem'.finalVal (L4 o) = cfg.mem.finalVal (L4 o) ∧
      (∀ ts v, mem'.read? (L4 o) ts = some v → cfg.mem.read? (L4 o) ts = some v) ∧
      (∀ ts w, mem'.get? ts = some w → w.loc = L4 x → cfg.mem.get? ts = some w) := by
    rcases hm with rfl | ⟨v, rfl⟩
    · exact ⟨rfl, rfl, fun _ _ h => h, fun _ _ h _ => h⟩
    · obtain ⟨a1, -, -, a4⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hxc)
      obtain ⟨b1, -, b3, -⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hoc)
      exact ⟨a1, b1, b3, a4⟩
  obtain ⟨m1, m2, m3, m4⟩ := hmem
  obtain ⟨f1, f2, f3, f4⟩ := tk_frame h ht htk hk m4
  refine ⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, m1 ▸ h.fx, m2 ▸ h.fo,
    fun ts v hr => h.ov ts v (m3 ts v hr), h.mxc, h.xcN, f1, ?_, f2, f3, f4⟩
  intro i u hu
  rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
  · exact hT
  · exact h.thr i u hu

/-- `LDADDA`: the ticket `xc` taken. -/
theorem inv_tkt (v : Val) (hv : v.toNat = xc + 1) (hm : mem' = (cfg.mem.append { loc := L4 x, val := v, tid }).1)
    (hT : TInv x o c m t') (h0 : ¬ Ticketed t) (h1 : Ticketed t') (hk : tk t' = xc) :
    InvW N x o c (xc + 1) m (cfg.withThread tid t' mem') := by
  subst hm
  obtain ⟨b1, -, b3, -⟩ := mem_frame cfg.mem { loc := L4 x, val := v, tid } h.hxo
  obtain ⟨hN, f⟩ := TicketGlobal.TkFacts.take (Ticketed := Ticketed) (tk := tk) ⟨h.xmsg, h.tkLt, h.tkInj, h.tkSurj⟩
    ht v h0 h1 hk
  refine ⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, ?_, b1 ▸ h.fo,
    fun ts v hr => h.ov ts v (b3 ts v hr), by have := h.mxc; omega, h.size ▸ hN, f.xmsg, ?_, f.tkLt, f.tkInj, f.tkSurj⟩
  · show BitVec.toNat ((cfg.mem.append { loc := L4 x, val := v, tid }).1.finalVal (L4 x)) = xc + 1
    rw [finalVal_append]; simpa using hv
  · intro i u hu
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact h.thr i u hu

/-- `STLR`: the holder of `m` serves `m + 1`. -/
theorem inv_rel (v : Val) (hv : v.toNat = m + 1) (hm : mem' = (cfg.mem.append { loc := L4 o, val := v, tid }).1)
    (hT : TInv x o c (m + 1) t') (h0 : Ticketed t) (h1 : Ticketed t') (hk0 : tk t = m) (hk : tk t' = m) :
    InvW N x o c xc (m + 1) (cfg.withThread tid t' mem') := by
  subst hm
  obtain ⟨a1, -, -, a4⟩ := mem_frame cfg.mem { loc := L4 o, val := v, tid } (Ne.symm h.hxo)
  obtain ⟨f1, f2, f3, f4⟩ := tk_frame h ht (iff_of_true h1 h0) (fun _ => hk.trans hk0.symm) a4
  refine ⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, a1 ▸ h.fx, ?_, ?_,
    by have := h.tkLt tid t ht h0; omega, h.xcN, f1, ?_, f2, f3, f4⟩
  · show BitVec.toNat ((cfg.mem.append { loc := L4 o, val := v, tid }).1.finalVal (L4 o)) = m + 1
    rw [finalVal_append]; simpa using hv
  · intro ts v' hr
    rcases read?_append_eq_some cfg.mem _ hr with hr | ⟨-, -, rfl⟩
    · have := h.ov ts v' hr; omega
    · exact Nat.le_of_eq hv
  · intro i u hu
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨hi, hu⟩
    · exact hT
    · obtain ⟨hS, hp, j, hj, hpc, hinv⟩ := h.thr i u hu
      exact ⟨hS, hp, j, hj, hpc, hinv.bump hj fun j1 j2 e =>
        hi (h.tkInj i tid u t hu ht (ticketed_at hpc hj j1 j2) h0 (e.trans hk0.symm))⟩

end Pres

/-! ## Steps and traces -/

/-- **An instruction step keeps the invariant**: either `owner` is untouched
(last write and value), or the holder of `m` released, serving `m + 1`. -/
theorem step_inv {N xc m tid : Nat} {x o c : BitVec 64} {cfg cfg' : Config isa}
    (h : InvW N x o c xc m cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.armv8 tid cfg cfg') :
    (∃ xc', InvW N x o c xc' m cfg' ∧ cfg'.mem.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
      InvW N x o c xc (m + 1) cfg' := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hxc : xc + 1 < 2 ^ 32 := by have := h.xcN; have := h.N32; omega
  have hown : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x → w.tid = tid → Ticketed t :=
    fun ts w hw hl e => by
      obtain ⟨tw, h1, h2⟩ := h.xmsg ts w hw hl
      rw [e, ht] at h1; cases h1; exact h2
  cases thread_step (h.thr tid t ht) hxc h.mxc h.fx hown h.ov hs ho with
  | same hm hT htk hk =>
    refine .inl ⟨xc, inv_same h ht hb hT htk hk hm, ?_⟩
    show oc.mem.lastWrite _ = _
    rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
    exact (mem_frame _ _ (Ne.symm h.hoc)).2.1
  | tkt v hv hm hT h0 h1 hk =>
    refine .inl ⟨xc + 1, inv_tkt h ht hb v hv hm hT h0 h1 hk, ?_⟩
    show oc.mem.lastWrite _ = _
    rw [hm]; exact (mem_frame _ _ h.hxo).2.1
  | rel v hv hm hT h0 h1 hk0 hk => exact .inr (inv_rel h ht hb v hv hm hT h0 h1 hk0 hk)

theorem loc_ne {a b : BitVec 64} (h : Decls.overlaps a 4 b 4 = false) : L4 a ≠ L4 b :=
  SpinStep.loc_ne h

/-- **The invariant holds initially.** -/
theorem inv_init {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) : InvW N x o c 0 0 (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  have hnt : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t → ¬ Ticketed t :=
    fun i t h ht => by
      obtain ⟨s, hm, rfl⟩ := hthr i t h
      exact ht.1 ((hs.hst s hm).pc.trans addrOf_0)
  refine ⟨by simp [Config.init, hs.hN], hs.hN32, loc_ne hs.hxo, loc_ne hs.hxc, loc_ne hs.hoc, Config.init_bnd _ _,
    ?_, ?_, ?_, Nat.le_refl _, Nat.zero_le _, ?_, ?_, fun i t h ht => absurd ht (hnt i t h),
    fun i _ _ _ h _ ht _ _ => absurd ht (hnt i _ h), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · have := hs.hX0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · have := hs.hO0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · intro ts v h
    have := hs.hO0
    simp only [Memory.read?, Memory.get?, Config.init] at h this
    split at h
    · cases h; simp [this]
    · simp at h
  · intro ts w h; simp [Memory.get?, Config.init] at h
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    exact ⟨⟨hs.exe, hs.decls, hs.endPc, hs.x0, hs.x1, hs.x2, hs.dx, hs.dO, hs.dc⟩, rfl,
      1, by decide, hs.pc.trans addrOf_0, trivial⟩

/-- **The invariant along a promise-free trace from a start configuration.** -/
theorem trace_inv {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) (tr : TraceS Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hpf : PromiseFree Arch.armv8 tr.cfg) :
    ∀ i, ∃ xc m, InvW N x o c xc m (tr.cfg i) :=
  SpinCommon.trace_inv_of hpf (P := fun cf => ∃ xc m, InvW N x o c xc m cf) ⟨0, 0, h0 ▸ inv_init hs⟩
    fun _ _ ⟨xc, m, h⟩ hi hm => (step_inv h (h.bnd.succ hm) hi).elim (fun ⟨xc', h', _⟩ => ⟨xc', m, h'⟩)
      fun h' => ⟨xc, m + 1, h'⟩

end Kraken.Promising.Live.TicketInv
