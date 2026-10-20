/-
**Stage 3, O1: the operational invariant of the x64
ticket lock with an unlocked release** (`ticketlock2.kl`, verbatim) over
promise-free `Arch.tso` runs of `N` workers on a valid layout of
`tk2ImageV`. An adapted copy of `LiveX64TicketInv.lean` (ticketlock3);
The global part (`InvW` minus `PcInv`/`CInv`/`uniq`, `tk_frame`, the
pigeonhole in `inv_tkt`) is the same for every ticket lock.

The quantities: `xc`, the value of `next`, and `m`, the value of `owner`. A
thread past its `lock xaddl` holds the ticket `tk t`, `%eax`'s low word.
The release `incl (owner)` is a plain load and a plain store, not an RMW: it
writes the value *it reads* plus one. So, beyond ticketlock3's `InvW`:

- **owner values strictly increase** (`uniq`): the only message of `owner`
  with value `m` is its last write. With `ov` (every value `≤ m`) a waiter
  that reads `m` has read the last write;
- **the holder has seen the last owner write** (`CInv`): a thread that has
  not yet released has no forwarding entry of `owner` (it never wrote it), so
  its spin read raises its coherence view of `owner` to the timestamp read
  (`Ticket2X64Step.spec_load_fwd`); once it has read `m` (`cmpl` with
  `%ecx = m`, `jne` with `ZF`, positions 7–10) that view is at the last
  write of `owner`, which nobody else writes while it holds the lock. So its
  `incl` reads `m` and writes `m + 1` (`thread_step`, position 10).

`CInv` depends on memory only through the last write of `owner` (`lw`).
`step_inv`: an instruction step keeps `InvW`; `m` grows by one exactly at the
release of the thread holding `m`, and otherwise stays with its last write.
-/
import Kraken.Promising.LiveX64Ticket2Trees
import Kraken.Promising.LiveX64Ticket2
import Kraken.Promising.LiveX64Ticket2Step
import Kraken.Promising.LiveX64TicketInv

namespace Kraken.Promising.Live.Ticket2X64Inv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.Ticket2X64Trees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.TsoRmw Kraken.Promising.Live.Ticket2X64Step
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV symTk2 StartStateTk2)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk2ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk2ImageV).addrOf

/-- The location of `next`. -/
abbrev XL : Loc := ⟨symTk2 "next", 4⟩
/-- The location of `owner`. -/
abbrev OL : Loc := ⟨symTk2 "owner", 4⟩
/-- The location of the counter. -/
abbrev CL : Loc := ⟨symTk2 "counter", 4⟩

/-! ## The per-thread invariant -/

/-- What a worker state never changes: its image, declarations, end address
and private memory at the three words. -/
structure Static (s : isa.State) : Prop where
  exe : s.exe = layout tk2ImageV
  decls : s.decls = {}
  endPc : s.endPc = pcA 13
  dx : Mem.loadInt s.st.1.dmem (symTk2 "next") 4 = none
  dO : Mem.loadInt s.st.1.dmem (symTk2 "owner") 4 = none
  dc : Mem.loadInt s.st.1.dmem (symTk2 "counter") 4 = none

omit hv in
theorem Static.goto {s : isa.State} (h : Static s) (md : MachineData) (pc : Int64) (hd : md.dmem = s.st.1.dmem) :
    Static (Ticket2X64Trees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, hd ▸ h.dx, hd ▸ h.dO, hd ▸ h.dc⟩

/-- The register facts at each pc position, for the ticket now served `m`
(`%eax`: the ticket; `%ecx`: the value read from `owner`). -/
def PcInv (m : Nat) (s : MachineData) : Nat → Prop
  | 1 => True
  | 2 => (eax s).toNat = 1
  | 4 => m ≤ (eax s).toNat
  | 5 => m ≤ (eax s).toNat ∧ (ecx s).toNat ≤ m
  | 6 => m ≤ (eax s).toNat ∧ (s.status.zf = true → (eax s).toNat = m ∧ (ecx s).toNat = m)
  | 7 | 8 | 9 | 10 => (eax s).toNat = m
  | 11 | 13 => (eax s).toNat < m
  | _ => False

/-- The view facts at each pc position, for the ticket now served `m` and the
last write `lw` of `owner`: no forwarding entry of `owner` before the
critical section, and a coherence view of `owner` at `lw` once `m` was read. -/
def CInv (m lw : Nat) (t : Thread isa) : Nat → Prop
  | 1 | 2 | 4 => t.views.getFwd OL = none
  | 5 => t.views.getFwd OL = none ∧ ((ecx t.st.st.1).toNat = m → lw ≤ t.views.getCoh OL)
  | 6 => t.views.getFwd OL = none ∧ (t.st.st.1.status.zf = true → lw ≤ t.views.getCoh OL)
  | 7 | 8 | 9 | 10 => lw ≤ t.views.getCoh OL
  | _ => True

/-- **The per-thread invariant.** -/
structure TInv (m lw : Nat) (t : Thread isa) : Prop where
  st : Static t.st
  prom : t.prom = []
  pc : ∃ i ∈ tkPcs, t.st.st.2 = pcA i ∧ PcInv m t.st.st.1 i ∧ CInv m lw t i

/-- A thread holds a ticket: it is past its `lock xaddl`. -/
def Ticketed (t : Thread isa) : Prop := t.st.st.2 ≠ pcA 1 ∧ t.st.st.2 ≠ pcA 2

/-- The ticket of a thread. -/
def tk (t : Thread isa) : Nat := (eax t.st.st.1).toNat

theorem Static.at {s : isa.State} (h : Static s) {i : Nat} (hi : i ∈ tkPcs) (h13 : i ≠ 13)
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

theorem ticketed_at {t : Thread isa} {i : Nat} (hpc : t.st.st.2 = pcA i) (hi : i ∈ tkPcs) (h1 : i ≠ 1)
    (h2 : i ≠ 2) : Ticketed t :=
  ⟨fun e => h1 (addrOf_inj hi (by decide) (hpc.symm.trans e)),
    fun e => h2 (addrOf_inj hi (by decide) (hpc.symm.trans e))⟩

theorem ticketed_goto {t : Thread isa} {s : isa.State} {md : MachineData} {j : Nat}
    (hst : t.st = Ticket2X64Trees.goto s md (pcA j)) (hj : j ∈ tkPcs) (h1 : j ≠ 1) (h2 : j ≠ 2) : Ticketed t :=
  ticketed_at (by rw [hst]) hj h1 h2

omit hv in
theorem tk_goto {t : Thread isa} {s : isa.State} {md : MachineData} {pc : Int64}
    (hst : t.st = Ticket2X64Trees.goto s md pc) : tk t = (eax md).toNat := by
  unfold tk; rw [hst]

omit layout hv in
/-- Formerly a copy of `LiveX64TicketPF.getCoh_eq`; `SpinSwpStep.getCoh_congr`. -/
theorem getCoh_eq {t t' : Thread isa} (h : t'.views.coh = t.views.coh) (l : Loc) :
    t'.views.getCoh l = t.views.getCoh l :=
  SpinSwpStep.getCoh_congr h l

theorem TInv.inv {m lw : Nat} {t : Thread isa} (h : TInv m lw t) {i : Nat} (hi : i ∈ tkPcs)
    (hpc : t.st.st.2 = pcA i) : PcInv m t.st.st.1 i ∧ CInv m lw t i := by
  obtain ⟨j, hj, hpc', hinv, hc⟩ := h.pc
  rw [hpc] at hpc'
  rw [addrOf_inj hi hj hpc']; exact ⟨hinv, hc⟩

/-! ## The steps, position by position -/

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static t.st) (hp : t.prom = [])
  (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

theorem s1 (hpc : t.st.st.2 = pcA 1) :
    oc.mem = mem ∧ (∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = 1#32 ∧
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 2)) ∧ oc.thread.prom = t.prom ∧
      oc.thread.views.getFwd OL = t.views.getFwd OL := by
  obtain ⟨md, hd, he, hex⟩ := exec_mov1 _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, -⟩ := spec_done _ _ hex hs ho
  exact ⟨h1, ⟨md, hd, he, h2⟩, h3, spec_done_fwd _ _ hex hs ho _⟩

include hp in
theorem s2 (hpc : t.st.st.2 = pcA 2) (hxo : XL ≠ OL) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ ∃ tr old, eax md = BitVec.setWidth 32 old ∧
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 4) ∧
      mem.read? XL tr = some old ∧ mem.atomic XL tid tr (mem.last + 1) = true ∧
      oc.mem = (mem.append
        { loc := XL, val := BitVec.setWidth 128 (BitVec.setWidth 32 old + eax t.st.st.1), tid }).1 ∧
      oc.thread.prom = [] ∧ oc.thread.views.getFwd OL = t.views.getFwd OL := by
  obtain ⟨g, hg, hex⟩ := exec_xadd _ (hS.at (by decide) (by decide) hpc) hS.dx
  obtain ⟨tr, old, h1, h2, h3, h4, h5⟩ := spec_rmw_tso _ _ rfl hp hex hs ho
  exact ⟨g old, (hg old).1, tr, old, (hg old).2, h1, h2, h3, h4, h5,
    spec_rmw_tso_fwd _ _ rfl hex hs ho (Ne.symm hxo)⟩

theorem s4 (hpc : t.st.st.2 = pcA 4) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ∃ ts v,
      ecx md = BitVec.setWidth 32 v ∧ oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 5) ∧
      mem.read? OL ts = some v ∧ (mem.lastWrite OL ≤ t.views.getCoh OL → v = mem.finalVal OL) ∧
      (t.views.getFwd OL = none → ts ≤ oc.thread.views.getCoh OL) ∧
      oc.thread.views.getFwd OL = t.views.getFwd OL ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ ∃ ν, TraceEv.read OL ts v ν ∈ oc.log := by
  obtain ⟨g, hg, hex⟩ := exec_ldo _ (hS.at (by decide) (by decide) hpc) hS.dO
  obtain ⟨ts, v, h1, h2, h3, h4, -, h6, h7, h8, h9⟩ := spec_load_fwd _ _ hex hs ho
  exact ⟨g v, (hg v).1, (hg v).2.1, ts, v, (hg v).2.2, h1, h2, h3, h4, h6 _, h7, h8, h9⟩

theorem s5 (hpc : t.st.st.2 = pcA 5) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ecx md = ecx t.st.st.1 ∧
      (md.status.zf = true ↔ ecx t.st.st.1 = eax t.st.st.1) ∧
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 6) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh ∧
      oc.thread.views.getFwd OL = t.views.getFwd OL := by
  obtain ⟨md, h1, h2, h3, h4, hex⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨md, h1, h2, h3, h4, k2, k1, k3, k4, spec_done_fwd _ _ hex hs ho _⟩

theorem s6 (hpc : t.st.st.2 = pcA 6) :
    oc.mem = mem ∧ oc.thread.st = Ticket2X64Trees.goto t.st t.st.st.1
      (if t.st.st.1.status.zf then pcA 7 else pcA 4) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh ∧
      oc.thread.views.getFwd OL = t.views.getFwd OL := by
  have hex := exec_jne _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨k1, k2, k3, k4, spec_done_fwd _ _ hex hs ho _⟩

theorem s7 (hpc : t.st.st.2 = pcA 7) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 8) ∧ oc.mem = mem ∧ oc.thread.prom = t.prom ∧
      t.views.getCoh OL ≤ oc.thread.views.getCoh OL := by
  obtain ⟨g, hg, hex⟩ := exec_ldc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨ts, v, h1, -, -, h4, h5, -⟩ := spec_load _ _ hex hs ho
  exact ⟨g v, (hg v).1, (hg v).2.1, h1, h4, h5, spec_load_coh _ _ hex hs ho _⟩

theorem s8 (hpc : t.st.st.2 = pcA 8) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 9) ∧ oc.mem = mem ∧ oc.thread.prom = t.prom ∧
      t.views.getCoh OL ≤ oc.thread.views.getCoh OL := by
  obtain ⟨md, h1, h2, -, hex⟩ := exec_addd _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, -⟩ := spec_done _ _ hex hs ho
  exact ⟨md, h1, h2, k2, k1, k3, Nat.le_of_eq (spec_done_coh _ _ hex hs ho _).symm⟩

include hp in
theorem s9 (hpc : t.st.st.2 = pcA 9) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 10) ∧
      (∃ v, oc.mem = (mem.append { loc := CL, val := v, tid }).1) ∧ oc.thread.prom = [] ∧
      t.views.getCoh OL ≤ oc.thread.views.getCoh OL := by
  obtain ⟨v, md, h1, h2, -, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨k1, k2, k3⟩ := spec_store _ _ hp hex hs ho
  exact ⟨md, h1, h2, k2, ⟨v, k1⟩, k3, (spec_store_coh _ _ hp hex hs ho).1 _⟩

include hp in
/-- The release `incl (owner)`: it reads some `v` (the last write's, if the
coherence view of `owner` is at it) and appends `v + 1`. -/
theorem s10 (hpc : t.st.st.2 = pcA 10) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ∃ v,
      oc.thread.st = Ticket2X64Trees.goto t.st md (pcA 11) ∧
      (mem.lastWrite OL ≤ t.views.getCoh OL → v = mem.finalVal OL) ∧
      oc.mem = (mem.append { loc := OL, val := BitVec.setWidth 128 (BitVec.setWidth 32 v + 1), tid }).1 ∧
      oc.thread.prom = [] := by
  obtain ⟨g, hg, hex⟩ := exec_inc _ (hS.at (by decide) (by decide) hpc) hS.dO
  obtain ⟨ts, v, h1, -, h3, h4, h5⟩ := spec_ldst _ _ hp hex hs ho
  exact ⟨g v, (hg v).1, (hg v).2, v, h1, h3, h4, h5⟩

theorem s11 (hpc : t.st.st.2 = pcA 11) :
    oc.mem = mem ∧ oc.thread.st = Ticket2X64Trees.goto t.st t.st.st.1 (pcA 13) ∧
      oc.thread.prom = t.prom :=
  let ⟨h1, h2, h3, _⟩ := spec_done _ _ (exec_jmp _ (hS.at (by decide) (by decide) hpc)) hs ho
  ⟨h1, h2, h3⟩

end Steps

/-! ## One thread's step -/

/-- What one step of a thread does to the invariant's quantities. -/
inductive StepRes (m xc tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- No ticket taken, `owner` not written. -/
  | same (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := CL, val := v, tid }).1)
      (ht : TInv m (mem.lastWrite OL) oc.thread) (htk : Ticketed oc.thread ↔ Ticketed t)
      (hk : Ticketed t → tk oc.thread = tk t)
  /-- `lock xaddl`: the ticket `xc` taken. -/
  | tkt (v : Val) (hv : v.toNat = xc + 1) (hm : oc.mem = (mem.append { loc := XL, val := v, tid }).1)
      (ht : TInv m (mem.lastWrite OL) oc.thread) (h0 : ¬ Ticketed t) (h1 : Ticketed oc.thread)
      (hk : tk oc.thread = xc)
  /-- The release: `owner := m + 1` by the holder of `m`. -/
  | rel (v : Val) (hv : v.toNat = m + 1) (hm : oc.mem = (mem.append { loc := OL, val := v, tid }).1)
      (ht : ∀ lw, TInv (m + 1) lw oc.thread) (h0 : Ticketed t) (h1 : Ticketed oc.thread) (hk0 : tk t = m)
      (hk : tk oc.thread = m)

/-- **One thread's step**, by position. -/
theorem thread_step {m xc tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv m (mem.lastWrite OL) t)
    (hxc : xc + 1 < 2 ^ 32) (hmxc : m ≤ xc) (hfx : (mem.finalVal XL).toNat = xc)
    (hfo : (mem.finalVal OL).toNat = m) (hxo : XL ≠ OL)
    (hown : ∀ ts w, mem.get? ts = some w → w.loc = XL → w.tid = tid → Ticketed t)
    (hov : ∀ ts v, mem.read? OL ts = some v → v.toNat ≤ m)
    (huniq : ∀ ts v, mem.read? OL ts = some v → v.toNat = m → ts = mem.lastWrite OL)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) : StepRes m xc tid t mem oc := by
  obtain ⟨i, hi, hpc, hinv, hci⟩ := h.pc
  have hS := h.st
  have hT : ∀ j, t.st.st.2 = pcA j → j ∈ tkPcs → j ≠ 1 → j ≠ 2 → Ticketed t :=
    fun j hj hjm h1 h2 => ticketed_at hj hjm h1 h2
  have hTI : ∀ {j : Nat} {u : Thread isa} {md : MachineData}, u.st = Ticket2X64Trees.goto t.st md (pcA j) →
      md.dmem = t.st.st.1.dmem → u.prom = [] → j ∈ tkPcs → PcInv m md j → CInv m (mem.lastWrite OL) u j →
      TInv m (mem.lastWrite OL) u := fun {j u md} hst hd hp hj h1 h2 =>
    ⟨by rw [hst]; exact hS.goto md _ hd, hp, j, hj, by rw [hst], by rw [hst]; exact h1, h2⟩
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, ⟨md, hd, he, hst⟩, hp, hf⟩ := s1 hS hs ho hpc
    refine .same (.inl hm) (hTI (j := 2) hst hd (hp.trans h.prom) (by decide) ?_ ?_)
      ⟨fun h' => absurd (by rw [hst]) h'.2, fun h' => absurd hpc h'.1⟩ (fun h' => absurd hpc h'.1)
    · show (eax md).toNat = 1; rw [he]; rfl
    · show _ = none; rw [hf]; exact hci
  · obtain ⟨md, hd, tr, old, he, hst, hrd, hat, hm, hp, hf⟩ := s2 hS h.prom hs ho hpc hxo
    obtain ⟨-, rfl⟩ := atomic_lastWrite mem XL tid hrd hat
      (fun ts w hw hl he => absurd hpc (hown ts w hw hl he).2)
    have h6 : (eax t.st.st.1).toNat = 1 := hinv
    have hk : tk oc.thread = xc := by
      rw [tk_goto hst, he, BitVec.toNat_setWidth, hfx]; exact Nat.mod_eq_of_lt (by omega)
    refine .tkt _ ?_ hm (hTI (j := 4) hst hd hp (by decide) ?_ ?_) (fun h' => h'.2 hpc)
      (ticketed_goto hst (by decide) (by decide) (by decide)) hk
    · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hfx, h6]
      rw [Nat.mod_eq_of_lt (by omega : xc < 2 ^ 32)]
      omega
    · show m ≤ (eax md).toNat
      rw [← tk_goto hst]; omega
    · show _ = none; rw [hf]; exact hci
  · obtain ⟨md, hd, he, ts, v, hc, hst, hrd, -, hcoh, hf, hm, hp, -⟩ := s4 hS hs ho hpc
    have hv := hov ts v hrd
    have hfn : t.views.getFwd OL = none := hci
    refine .same (.inl hm) (hTI (j := 5) hst hd (hp.trans h.prom) (by decide) ?_ ?_)
      (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
        (hT 4 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst, he]; rfl)
    · refine ⟨by rw [he]; exact hinv, ?_⟩
      show (ecx md).toNat ≤ m
      rw [hc, BitVec.toNat_setWidth]; exact Nat.le_trans (Nat.mod_le _ _) hv
    · refine ⟨by rw [hf]; exact hfn, fun hcm => ?_⟩
      have hvm : v.toNat = m := by
        have hlt : v.toNat < 2 ^ 32 := by omega
        rw [show (ecx oc.thread.st.st.1) = ecx md by rw [hst], hc, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt hlt] at hcm
        exact hcm
      rw [← huniq ts v hrd hvm]; exact hcoh hfn
  · obtain ⟨md, hd, he, hc, hz, hst, hm, hp, hcoh, hf⟩ := s5 hS hs ho hpc
    obtain ⟨h1, h2⟩ := (hinv : m ≤ (eax t.st.st.1).toNat ∧ (ecx t.st.st.1).toNat ≤ m)
    obtain ⟨hfn, hc5⟩ := (hci : t.views.getFwd OL = none ∧
      ((ecx t.st.st.1).toNat = m → mem.lastWrite OL ≤ t.views.getCoh OL))
    have hz' : md.status.zf = true → (eax md).toNat = m ∧ (ecx md).toNat = m := by
      rw [he, hc]
      intro hz'
      have := congrArg BitVec.toNat (hz.mp hz')
      omega
    refine .same (.inl hm) (hTI (j := 6) hst hd (hp.trans h.prom) (by decide) ?_ ?_)
      (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
        (hT 5 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst, he]; rfl)
    · exact ⟨by rw [he]; exact h1, hz'⟩
    · refine ⟨by rw [hf]; exact hfn, fun hzz => ?_⟩
      rw [show oc.thread.st.st.1 = md by rw [hst]] at hzz
      rw [getCoh_eq hcoh]
      exact hc5 (by rw [← hc]; exact (hz' hzz).2)
  · obtain ⟨hm, hst, hp, hcoh, hf⟩ := s6 hS hs ho hpc
    obtain ⟨h1, h2⟩ := (hinv : m ≤ (eax t.st.st.1).toNat ∧
      (t.st.st.1.status.zf = true → (eax t.st.st.1).toNat = m ∧ (ecx t.st.st.1).toNat = m))
    obtain ⟨hfn, hc6⟩ := (hci : t.views.getFwd OL = none ∧
      (t.st.st.1.status.zf = true → mem.lastWrite OL ≤ t.views.getCoh OL))
    by_cases hz : t.st.st.1.status.zf = true
    · rw [ite_eq_left hz] at hst
      refine .same (.inl hm) (hTI (j := 7) hst rfl (hp.trans h.prom) (by decide) (h2 hz).1 ?_)
        (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
          (hT 6 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst]; rfl)
      show _ ≤ _; rw [getCoh_eq hcoh]; exact hc6 hz
    · rw [ite_eq_right hz] at hst
      refine .same (.inl hm) (hTI (j := 4) hst rfl (hp.trans h.prom) (by decide) h1 ?_)
        (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
          (hT 6 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst]; rfl)
      show _ = none; rw [hf]; exact hfn
  · obtain ⟨md, hd, he, hst, hm, hp, hcoh⟩ := s7 hS hs ho hpc
    refine .same (.inl hm) (hTI (j := 8) hst hd (hp.trans h.prom) (by decide) ?_ ?_)
      (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
        (hT 7 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst, he]; rfl)
    · show (eax md).toNat = m; rw [he]; exact hinv
    · exact Nat.le_trans (hci : mem.lastWrite OL ≤ _) hcoh
  · obtain ⟨md, hd, he, hst, hm, hp, hcoh⟩ := s8 hS hs ho hpc
    refine .same (.inl hm) (hTI (j := 9) hst hd (hp.trans h.prom) (by decide) ?_ ?_)
      (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
        (hT 8 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst, he]; rfl)
    · show (eax md).toNat = m; rw [he]; exact hinv
    · exact Nat.le_trans (hci : mem.lastWrite OL ≤ _) hcoh
  · obtain ⟨md, hd, he, hst, hm, hp, hcoh⟩ := s9 hS h.prom hs ho hpc
    refine .same (.inr hm) (hTI (j := 10) hst hd hp (by decide) ?_ ?_)
      (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
        (hT 9 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst, he]; rfl)
    · show (eax md).toNat = m; rw [he]; exact hinv
    · exact Nat.le_trans (hci : mem.lastWrite OL ≤ _) hcoh
  · obtain ⟨md, hd, he, v, hst, hv, hm, hp⟩ := s10 hS h.prom hs ho hpc
    have hvm := hv hci
    have h3 : (eax t.st.st.1).toNat = m := hinv
    have hmN : m + 1 < 2 ^ 32 := by omega
    refine .rel _ ?_ hm (fun lw => ⟨by rw [hst]; exact hS.goto md _ hd, hp, 11, by decide, by rw [hst],
        by rw [hst]; show (eax md).toNat < m + 1; rw [he]; omega, trivial⟩)
      (hT 10 hpc (by decide) (by decide) (by decide))
      (ticketed_goto hst (by decide) (by decide) (by decide)) h3 (by rw [tk_goto hst, he]; exact h3)
    rw [hvm]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hfo]
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [h1, Nat.mod_eq_of_lt (by omega : m < 2 ^ 32), Nat.mod_eq_of_lt hmN, Nat.mod_eq_of_lt (by omega)]
  · obtain ⟨hm, hst, hp⟩ := s11 hS hs ho hpc
    refine .same (.inl hm) (hTI (j := 13) hst rfl (hp.trans h.prom) (by decide) hinv trivial)
      (iff_of_true (ticketed_goto hst (by decide) (by decide) (by decide))
        (hT 11 hpc (by decide) (by decide) (by decide))) (fun _ => by rw [tk_goto hst]; rfl)
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant** of a configuration with `xc` tickets taken and ticket
`m` served. -/
structure InvW (N : Nat) (xc m : Nat) (cfg : Config isa) : Prop where
  size : cfg.threads.size = N
  N32 : N + 1 < 2 ^ 32
  hxo : XL ≠ OL
  hxc : XL ≠ CL
  hoc : OL ≠ CL
  bnd : cfg.Bnd
  fx : (cfg.mem.finalVal XL).toNat = xc
  fo : (cfg.mem.finalVal OL).toNat = m
  ov : ∀ ts v, cfg.mem.read? OL ts = some v → v.toNat ≤ m
  uniq : ∀ ts v, cfg.mem.read? OL ts = some v → v.toNat = m → ts = cfg.mem.lastWrite OL
  mxc : m ≤ xc
  xcN : xc ≤ N
  xmsg : ∀ ts w, cfg.mem.get? ts = some w → w.loc = XL → ∃ tw, cfg.threads[w.tid]? = some tw ∧ Ticketed tw
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv m (cfg.mem.lastWrite OL) t
  tkLt : ∀ (i : Nat) t, cfg.threads[i]? = some t → Ticketed t → tk t < xc
  tkInj : ∀ (i j : Nat) ti tj, cfg.threads[i]? = some ti → cfg.threads[j]? = some tj → Ticketed ti → Ticketed tj →
    tk ti = tk tj → i = j
  tkSurj : ∀ k < xc, ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Ticketed t ∧ tk t = k

/-- A waiter of the old invariant is a waiter of the next `m`, if it does not
hold `m`; its view facts hold at any last write. -/
theorem TInv.bump {m lw lw' : Nat} {t : Thread isa} (h : TInv m lw t)
    (hne : Ticketed t → tk t ≠ m) : TInv (m + 1) lw' t := by
  obtain ⟨hS, hp, i, hi, hpc, hinv, hc⟩ := h
  have hne' : i ≠ 1 → i ≠ 2 → (eax t.st.st.1).toNat ≠ m := fun h1 h2 => hne (ticketed_at hpc hi h1 h2)
  refine ⟨hS, hp, i, hi, hpc, ?_, ?_⟩
  · simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [PcInv] at hinv ⊢ <;> first | exact hinv | trivial |
        (have := hne' (by decide) (by decide); first | omega |
          exact ⟨by omega, fun hz => absurd (hinv.2 hz).1 this⟩)
  · simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [CInv, PcInv] at hc hinv ⊢
    all_goals first
      | exact hc
      | trivial
      | exact ⟨hc.1, fun h' => absurd hinv.2 (by omega)⟩
      | exact ⟨hc.1, fun hz => absurd (hinv.2 hz).1 (hne' (by decide) (by decide))⟩
      | exact absurd hinv (hne' (by decide) (by decide))

section Pres

variable {N xc m tid : Nat} {cfg : Config isa} {t t' : Thread isa} {mem' : Memory}
  (h : InvW N xc m cfg) (ht : cfg.threads[tid]? = some t) (hb : (cfg.withThread tid t' mem').Bnd)

include h ht hb

omit hb in
/-- The ticket facts after a step that keeps the thread's ticket. -/
theorem tk_frame (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hm4 : ∀ ts w, mem'.get? ts = some w → w.loc = XL → cfg.mem.get? ts = some w) :
    let cfg' := cfg.withThread tid t' mem'
    (∀ ts w, cfg'.mem.get? ts = some w → w.loc = XL → ∃ tw, cfg'.threads[w.tid]? = some tw ∧ Ticketed tw) ∧
    (∀ (i : Nat) u, cfg'.threads[i]? = some u → Ticketed u → tk u < xc) ∧
    (∀ (i j : Nat) ti tj, cfg'.threads[i]? = some ti → cfg'.threads[j]? = some tj → Ticketed ti → Ticketed tj →
      tk ti = tk tj → i = j) ∧
    (∀ k < xc, ∃ i : Nat, ∃ u, cfg'.threads[i]? = some u ∧ Ticketed u ∧ tk u = k) :=
  have f := TicketGlobal.TkFacts.frame (Ticketed := Ticketed) (tk := tk) ⟨h.xmsg, h.tkLt, h.tkInj, h.tkSurj⟩ ht
    htk hk hm4
  ⟨f.xmsg, f.tkLt, f.tkInj, f.tkSurj⟩

/-- A step that takes no ticket and does not write `owner`. -/
theorem inv_same (hT : TInv m (cfg.mem.lastWrite OL) t') (htk : Ticketed t' ↔ Ticketed t)
    (hk : Ticketed t → tk t' = tk t)
    (hm : mem' = cfg.mem ∨ ∃ v, mem' = (cfg.mem.append { loc := CL, val := v, tid }).1) :
    InvW N xc m (cfg.withThread tid t' mem') := by
  have hmem : mem'.finalVal XL = cfg.mem.finalVal XL ∧ mem'.finalVal OL = cfg.mem.finalVal OL ∧
      mem'.lastWrite OL = cfg.mem.lastWrite OL ∧
      (∀ ts v, mem'.read? OL ts = some v → cfg.mem.read? OL ts = some v) ∧
      (∀ ts w, mem'.get? ts = some w → w.loc = XL → cfg.mem.get? ts = some w) := by
    rcases hm with rfl | ⟨v, rfl⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ h => h, fun _ _ h _ => h⟩
    · obtain ⟨a1, -, -, a4⟩ := mem_frame cfg.mem { loc := CL, val := v, tid } (Ne.symm h.hxc)
      obtain ⟨b1, b2, b3, -⟩ := mem_frame cfg.mem { loc := CL, val := v, tid } (Ne.symm h.hoc)
      exact ⟨a1, b1, b2, b3, a4⟩
  obtain ⟨m1, m2, m5, m3, m4⟩ := hmem
  obtain ⟨f1, f2, f3, f4⟩ := tk_frame h ht htk hk m4
  refine ⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, m1 ▸ h.fx, m2 ▸ h.fo,
    fun ts v hr => h.ov ts v (m3 ts v hr), fun ts v hr hv => m5 ▸ h.uniq ts v (m3 ts v hr) hv,
    h.mxc, h.xcN, f1, ?_, f2, f3, f4⟩
  intro i u hu
  show TInv m (mem'.lastWrite OL) u
  rw [m5]
  rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
  · exact hT
  · exact h.thr i u hu

/-- `lock xaddl`: the ticket `xc` taken. -/
theorem inv_tkt (v : Val) (hv : v.toNat = xc + 1) (hm : mem' = (cfg.mem.append { loc := XL, val := v, tid }).1)
    (hT : TInv m (cfg.mem.lastWrite OL) t') (h0 : ¬ Ticketed t) (h1 : Ticketed t') (hk : tk t' = xc) :
    InvW N (xc + 1) m (cfg.withThread tid t' mem') := by
  subst hm
  obtain ⟨b1, b2, b3, -⟩ := mem_frame cfg.mem { loc := XL, val := v, tid } h.hxo
  obtain ⟨hN, f⟩ := TicketGlobal.TkFacts.take (Ticketed := Ticketed) (tk := tk) ⟨h.xmsg, h.tkLt, h.tkInj, h.tkSurj⟩
    ht v h0 h1 hk
  refine ⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, ?_, b1 ▸ h.fo,
    fun ts v hr => h.ov ts v (b3 ts v hr), fun ts v hr hv => b2 ▸ h.uniq ts v (b3 ts v hr) hv,
    by have := h.mxc; omega, h.size ▸ hN, f.xmsg, ?_, f.tkLt, f.tkInj, f.tkSurj⟩
  · show BitVec.toNat ((cfg.mem.append { loc := XL, val := v, tid }).1.finalVal XL) = xc + 1
    rw [finalVal_append]; simpa using hv
  · intro i u hu
    show TInv m ((cfg.mem.append _).1.lastWrite OL) u
    rw [b2]
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact h.thr i u hu

/-- The release: the holder of `m` serves `m + 1`. -/
theorem inv_rel (v : Val) (hv : v.toNat = m + 1) (hm : mem' = (cfg.mem.append { loc := OL, val := v, tid }).1)
    (hT : ∀ lw, TInv (m + 1) lw t') (h0 : Ticketed t) (h1 : Ticketed t') (hk0 : tk t = m) (hk : tk t' = m) :
    InvW N xc (m + 1) (cfg.withThread tid t' mem') := by
  subst hm
  obtain ⟨a1, -, -, a4⟩ := mem_frame cfg.mem { loc := OL, val := v, tid } (Ne.symm h.hxo)
  obtain ⟨f1, f2, f3, f4⟩ := tk_frame h ht (iff_of_true h1 h0) (fun _ => hk.trans hk0.symm) a4
  have hlw : (cfg.mem.append { loc := OL, val := v, tid }).1.lastWrite OL = cfg.mem.last + 1 := by
    rw [Memory.lastWrite_append, ite_eq_left rfl]
  refine ⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, a1 ▸ h.fx, ?_, ?_, ?_,
    by have := h.tkLt tid t ht h0; omega, h.xcN, f1, ?_, f2, f3, f4⟩
  · show BitVec.toNat ((cfg.mem.append { loc := OL, val := v, tid }).1.finalVal OL) = m + 1
    rw [finalVal_append]; simpa using hv
  · intro ts v' hr
    rcases read?_append_eq_some cfg.mem _ hr with hr | ⟨-, -, rfl⟩
    · have := h.ov ts v' hr; omega
    · exact Nat.le_of_eq hv
  · intro ts v' hr hv'
    show ts = (cfg.mem.append _).1.lastWrite OL
    rw [hlw]
    rcases read?_append_eq_some cfg.mem _ hr with hr | ⟨e, -, -⟩
    · have := h.ov ts v' hr; omega
    · exact e
  · intro i u hu
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨hi, hu⟩
    · exact hT _
    · exact (h.thr i u hu).bump fun hku e =>
        hi (h.tkInj i tid u t hu ht hku h0 (e.trans hk0.symm))

end Pres

/-! ## Steps and traces -/

/-- **An instruction step keeps the invariant**: either `owner` is untouched
(last write and value), or the holder of `m` released, serving `m + 1`. -/
theorem step_inv {N xc m tid : Nat} {cfg cfg' : Config isa}
    (h : InvW N xc m cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.tso tid cfg cfg') :
    (∃ xc', InvW N xc' m cfg' ∧ cfg'.mem.lastWrite OL = cfg.mem.lastWrite OL) ∨
      InvW N xc (m + 1) cfg' := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hxc : xc + 1 < 2 ^ 32 := by have := h.xcN; have := h.N32; omega
  have hown : ∀ ts w, cfg.mem.get? ts = some w → w.loc = XL → w.tid = tid → Ticketed t :=
    fun ts w hw hl e => by
      obtain ⟨tw, h1, h2⟩ := h.xmsg ts w hw hl
      rw [e, ht] at h1; cases h1; exact h2
  cases thread_step (h.thr tid t ht) hxc h.mxc h.fx h.fo h.hxo hown h.ov h.uniq hs ho with
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

/-- **The invariant holds initially.** -/
theorem inv_init {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket2X64.Tk2StartX N states initMem) : InvW N 0 0 (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  have hpc : ∀ s ∈ states, s.st.2 = pcA 1 := fun s hm => by
    rw [(hs.hst s hm).pc, (hs.hst s hm).exe]; exact label_worker
  have hnt : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t → ¬ Ticketed t :=
    fun i t h ht => by
      obtain ⟨s, hm, rfl⟩ := hthr i t h
      exact ht.1 (hpc s hm)
  have hrd : ∀ ts v, (Config.init states initMem : Config isa).mem.read? OL ts = some v → ts = 0 ∧ v.toNat = 0 := by
    intro ts v h
    have := hs.hO0
    simp only [Memory.read?, Memory.get?, Config.init] at h this
    split at h
    · cases h; exact ⟨by assumption, by simp [this]⟩
    · simp at h
  refine ⟨by simp [Config.init, hs.hN], hs.hN32, loc_ne hs.hxo, loc_ne hs.hxc, loc_ne hs.hoc, Config.init_bnd _ _,
    ?_, ?_, fun ts v h => Nat.le_of_eq (hrd ts v h).2, ?_, Nat.le_refl _, Nat.zero_le _, ?_, ?_,
    fun i t h ht => absurd ht (hnt i t h), fun i _ _ _ h _ ht _ _ => absurd ht (hnt i _ h),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · have := hs.hX0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · have := hs.hO0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · intro ts v h _
    rw [(hrd ts v h).1]
    exact (Nat.eq_zero_of_le_zero (Memory.lastWrite_le _ _)).symm
  · intro ts w h; simp [Memory.get?, Config.init] at h
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hst := hs.hst s hm
    obtain ⟨d1, d2, d3⟩ := hst.frame
    exact ⟨⟨hst.exe, hst.decls, by show s.endPc = _; rw [hst.endPc, hst.exe]; exact label_done, d1, d2, d3⟩, rfl,
      1, by decide, hpc s hm, trivial, rfl⟩

/-- **The invariant along a promise-free trace from a start configuration.** -/
theorem trace_inv {fuel N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket2X64.Tk2StartX N states initMem) (tr : TraceS Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (hpf : PromiseFree Arch.tso tr.cfg) :
    ∀ i, ∃ xc m, InvW N xc m (tr.cfg i) :=
  SpinCommon.trace_inv_of hpf (P := fun cf => ∃ xc m, InvW N xc m cf) ⟨0, 0, h0 ▸ inv_init hs⟩
    fun _ _ ⟨xc, m, h⟩ hi hm => (step_inv h (h.bnd.succ hm) hi).elim (fun ⟨xc', h', _⟩ => ⟨xc', m, h'⟩)
      fun h' => ⟨xc, m + 1, h'⟩

end Kraken.Promising.Live.Ticket2X64Inv
