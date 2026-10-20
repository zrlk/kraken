/-
**Stage 4 (repeated acquisition): the operational invariant of the
repeated-acquire ticket lock** over promise-free runs of `N` workers
`tkLoopWorker` running `k` rounds, on a valid layout.

The quantities: `xc`, the value of `next` (`x`; the number of tickets taken),
and `m`, the value of `owner` (`o`; the ticket now served). A thread at
positions 6–13 (from its `LDADDA` to its `STLR`, `tkHeld`) holds the ticket
`tk t`, the low word of `X3`; `taken k t` counts the tickets the thread has
taken so far (`k - X7`, plus one between its `LDADDA` and its `SUB`).
`InvL`:

- the last write to `next` is `xc`, to `owner` is `m`, every value of `owner`
  in memory is at most `m`, `m ≤ xc`, and `xc` is the sum of `taken` (so
  `xc ≤ N * k`: `InvL.xcle`, and the tickets never wrap);
- every thread keeps its program, addresses and private memory, has no
  outstanding promise, at most `k` rounds left, `X6 = 1` past its `MOV`, and
  its registers satisfy `PcInv m` at its pc (a waiter holds a ticket `≥ m`,
  the thread in the critical section holds `m`);
- every thread's own writes to `next` are at or below its coherence view of
  `next` (`own`), so its `LDADDA` reads the last write
  (`SpinSwpStep.spec_swp`) even after earlier rounds;
- the held tickets are pairwise distinct, below `xc`, and every ticket in
  `[m, xc)` is held.

`step_inv`: an instruction step keeps `InvL`; `m` grows by one exactly at the
`STLR` of the thread holding `m`, and otherwise stays with its last write.
The per-position step lemmas (`s1` … `s15`) are reused by
`LiveTicketLoopPF.lean`.
-/
import Kraken.Promising.LiveTicketLoopStatic
import Kraken.Promising.LiveSpinSwpStep
import Kraken.Promising.LiveSpinCommon
import Kraken.Promising.LiveTicketInv

namespace Kraken.Promising.Live.TicketLoopInv

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep Kraken.Promising.Live.SpinSwpStep
open Kraken.Promising.Live.TicketInv (wn L4 toNat_w32 w32_eq_iff mem_frame loc_ne)
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.Live.Term (tsum tsum_withThread_add tsum_le)
open Kraken.Promising.SLR.A64Trees (goto)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-! ## Positions, tickets, rounds -/

/-- The positions holding a ticket: from the `LDADDA` to the `STLR`. -/
def tkHeld : List Nat := [6, 7, 8, 9, 10, 11, 12, 13]

/-- The positions of a round after its `LDADDA` and before its `SUB`. -/
def tkBusy : List Nat := [6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- A thread holds a ticket: it is at one of the positions `tkHeld`. -/
def Ticketed (t : Thread isa) : Prop := ∃ i ∈ tkHeld, t.st.st.2 = pcA i

/-- The ticket of a thread. -/
def tk (t : Thread isa) : Nat := wn t.st.st.1.regs.X3

open Classical in
/-- The number of tickets thread `t` has taken in a run of `k` rounds: the
completed rounds `k - X7`, plus one between its `LDADDA` and its `SUB`. -/
noncomputable def taken (k : Nat) (t : Thread isa) : Nat :=
  k - wn t.st.st.1.regs.X7 + if ∃ i ∈ tkBusy, t.st.st.2 = pcA i then 1 else 0

theorem held_sub : ∀ j ∈ tkHeld, j ∈ tkLoopPcs := by decide

theorem busy_sub : ∀ j ∈ tkBusy, j ∈ tkLoopPcs := by decide

theorem ticketed_iff {t : Thread isa} {i : Nat} (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) :
    Ticketed t ↔ i ∈ tkHeld :=
  ⟨fun ⟨j, hj, e⟩ => by rwa [addrOf_inj hi (held_sub j hj) (hpc.symm.trans e)], fun h => ⟨i, h, hpc⟩⟩

theorem busy_iff {t : Thread isa} {i : Nat} (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) :
    (∃ j ∈ tkBusy, t.st.st.2 = pcA j) ↔ i ∈ tkBusy :=
  ⟨fun ⟨j, hj, e⟩ => by rwa [addrOf_inj hi (busy_sub j hj) (hpc.symm.trans e)], fun h => ⟨i, h, hpc⟩⟩

theorem taken_at {k : Nat} {t : Thread isa} {i : Nat} (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) :
    taken k t = k - wn t.st.st.1.regs.X7 + if i ∈ tkBusy then 1 else 0 := by
  unfold taken
  simp only [busy_iff hi hpc]

/-! ## The per-thread invariant -/

/-- The register facts at each pc position, for the ticket now served `m`. -/
def PcInv (m : Nat) (s : MachineData) : Nat → Prop
  | 1 | 3 | 15 | 17 => True
  | 4 | 14 => wn s.regs.X7 ≠ 0
  | 6 => wn s.regs.X7 ≠ 0 ∧ m ≤ wn s.regs.X3
  | 7 => wn s.regs.X7 ≠ 0 ∧ m ≤ wn s.regs.X3 ∧ wn s.regs.X4 ≤ m
  | 8 => wn s.regs.X7 ≠ 0 ∧ m ≤ wn s.regs.X3 ∧ (s.status.z = true → wn s.regs.X3 = m)
  | 9 | 10 | 11 | 12 => wn s.regs.X7 ≠ 0 ∧ wn s.regs.X3 = m
  | 13 => wn s.regs.X7 ≠ 0 ∧ wn s.regs.X3 = m ∧ wn s.regs.X4 = m + 1
  | _ => False

/-- **The per-thread invariant** (`k` rounds, ticket `m` served). -/
structure TInv (k : Nat) (x o c : BitVec 64) (m : Nat) (t : Thread isa) : Prop where
  st : Static x o c t.st
  prom : t.prom = []
  k7 : wn t.st.st.1.regs.X7 ≤ k
  x6 : t.st.st.2 = pcA 1 ∨ wn t.st.st.1.regs.X6 = 1
  pc : ∃ i ∈ tkLoopPcs, t.st.st.2 = pcA i ∧ PcInv m t.st.st.1 i

theorem PcInv.x7 {m : Nat} {s : MachineData} {i : Nat} (hp : PcInv m s i) (hi : i ∈ tkLoopPcs)
    (hb : i ∈ tkBusy) : wn s.regs.X7 ≠ 0 := by
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hb (by decide) | exact hp | exact hp.1

theorem TInv.pcinv {k : Nat} {x o c : BitVec 64} {m : Nat} {t : Thread isa} (h : TInv k x o c m t) {i : Nat}
    (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) : PcInv m t.st.st.1 i := by
  obtain ⟨j, hj, hpc', hinv⟩ := h.pc
  rw [hpc] at hpc'
  rwa [addrOf_inj hi hj hpc']

theorem TInv.x6' {k : Nat} {x o c : BitVec 64} {m : Nat} {t : Thread isa} (h : TInv k x o c m t) {i : Nat}
    (hi : i ∈ tkLoopPcs) (hpc : t.st.st.2 = pcA i) (h1 : i ≠ 1) : wn t.st.st.1.regs.X6 = 1 :=
  h.x6.resolve_left fun e => h1 (addrOf_inj hi (by decide) (hpc.symm.trans e))

/-- A thread has taken at most `k` tickets. -/
theorem taken_le {k : Nat} {x o c : BitVec 64} {m : Nat} {t : Thread isa} (h : TInv k x o c m t) :
    taken k t ≤ k := by
  obtain ⟨i, hi, hpc, hinv⟩ := h.pc
  rw [taken_at hi hpc]
  have := h.k7
  split
  · have := hinv.x7 hi ‹_›; omega
  · omega

/-- A step that keeps `X3` and moves between positions both holding or both
not holding a ticket keeps the ticket facts. -/
theorem same_tk {t t' : Thread isa} {i j : Nat} (hi : i ∈ tkLoopPcs) (hj : j ∈ tkLoopPcs)
    (hpc : t.st.st.2 = pcA i) (hpc' : t'.st.st.2 = pcA j) (h3 : t'.st.st.1.regs.X3 = t.st.st.1.regs.X3)
    (hij : i ∈ tkHeld ↔ j ∈ tkHeld) : (Ticketed t' ↔ Ticketed t) ∧ (Ticketed t → tk t' = tk t) :=
  ⟨by rw [ticketed_iff hj hpc', ticketed_iff hi hpc, hij], fun _ => by unfold tk; rw [h3]⟩

/-- A step that keeps `X7` and moves between positions both busy or both not
busy keeps `taken`. -/
theorem same_taken {k : Nat} {t t' : Thread isa} {i j : Nat} (hi : i ∈ tkLoopPcs) (hj : j ∈ tkLoopPcs)
    (hpc : t.st.st.2 = pcA i) (hpc' : t'.st.st.2 = pcA j) (h7 : t'.st.st.1.regs.X7 = t.st.st.1.regs.X7)
    (hij : i ∈ tkBusy ↔ j ∈ tkBusy) : taken k t' = taken k t := by
  rw [taken_at hj hpc', taken_at hi hpc, h7]
  by_cases h : i ∈ tkBusy
  · simp only [h, hij.mp h, ite_true]
  · simp only [h, mt hij.mpr h, ite_false]

/-! ## The steps, position by position -/

/-- The coherence views never go down across a step. -/
abbrev CohMono (t t' : Thread isa) : Prop := ∀ l', t.views.getCoh l' ≤ t'.views.getCoh l'

theorem cohMono_of_eq {t t' : Thread isa} (h : t'.views.coh = t.views.coh) : CohMono t t' :=
  fun l' => Nat.le_of_eq (getCoh_congr h l').symm

section Steps

variable {x o c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static x o c t.st) (hp : t.prom = [])
  (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

theorem s1 (hpc : t.st.st.2 = pcA 1) :
    oc.mem = mem ∧ oc.thread.st = goto t.st
      { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X6 1#64 } (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s3 (hpc : t.st.st.2 = pcA 3) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1
      (if w32 t.st.st.1.regs.X7 = 0#32 then pcA 17 else pcA 4) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_cbz _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
/-- `LDADDA`: with `OwnLe`, it reads the final value of `next`. -/
theorem s4 (hpc : t.st.st.2 = pcA 4) (hown : OwnLe mem tid (L4 x) (t.views.getCoh (L4 x))) :
    oc.thread.st = goto t.st
        { t.st.st.1 with
          regs := t.st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 (BitVec.setWidth 32 (mem.finalVal (L4 x)))) }
        (pcA 6) ∧
      oc.mem = (mem.append { loc := L4 x, val := (BitVec.setWidth 128
        (BitVec.setWidth 32 (mem.finalVal (L4 x)) + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)), tid }).1 ∧
      oc.thread.prom = [] ∧ CohMono t oc.thread ∧ mem.last + 1 ≤ oc.thread.views.getCoh (L4 x) :=
  spec_swp _ _ rfl hp (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho hown

theorem s6 (hpc : t.st.st.2 = pcA 6) :
    ∃ ts v, oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 7) ∧
      mem.read? (L4 o) ts = some v ∧ (mem.lastWrite (L4 o) ≤ t.views.getCoh (L4 o) → v = mem.finalVal (L4 o)) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ (∃ ν, TraceEv.read (L4 o) ts v ν ∈ oc.log) ∧
      CohMono t oc.thread := by
  have hex := exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO
  obtain ⟨ts, v, h1, h2, h3, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨ts, v, h1, h2, h3, h4, h5, h6, spec_load_coh _ _ hex hs ho⟩

theorem s7 (hpc : t.st.st.2 = pcA 7) :
    ∃ sf : StatusFlags, oc.thread.st = goto t.st { t.st.st.1 with status := sf } (pcA 8) ∧
      (sf.z = true ↔ wn t.st.st.1.regs.X4 = wn t.st.st.1.regs.X3) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh := by
  obtain ⟨sf, hex, hz⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, h4⟩ := spec_done _ _ hex hs ho
  exact ⟨sf, h2, hz.trans (w32_eq_iff _ _), h1, h3, h4⟩

theorem s8 (hpc : t.st.st.2 = pcA 8) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1
      (if t.st.st.1.status.z = true then pcA 9 else pcA 6) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s9 (hpc : t.st.st.2 = pcA 9) :
    ∃ v : Val, oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcA 10) ∧
      oc.mem = mem ∧ oc.thread.prom = t.prom ∧ CohMono t oc.thread := by
  have hex := exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc
  obtain ⟨ts, v, h1, -, -, h4, h5, -⟩ := spec_load _ _ hex hs ho
  exact ⟨v, h1, h4, h5, spec_load_coh _ _ hex hs ho⟩

theorem s10 (hpc : t.st.st.2 = pcA 10) :
    oc.mem = mem ∧ oc.thread.st = goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (t.st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      (pcA 11) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s11 (hpc : t.st.st.2 = pcA 11) :
    oc.mem = (mem.append { loc := L4 c, val := (BitVec.setWidth 128
      (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec)), tid }).1 ∧
      oc.thread.st = goto t.st t.st.st.1 (pcA 12) ∧ oc.thread.prom = [] ∧ CohMono t oc.thread := by
  have hex := exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc
  obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
  exact ⟨h1, h2, h3, (spec_store_coh _ _ hp hex hs ho).1⟩

theorem s12 (hpc : t.st.st.2 = pcA 12) :
    oc.mem = mem ∧ oc.thread.st = goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 (t.st.st.1.regs.X3.toBitVec.take 32 + 1#32)) }
      (pcA 13) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho

include hp in
theorem s13 (hpc : t.st.st.2 = pcA 13) :
    oc.mem = (mem.append { loc := L4 o, val := (BitVec.setWidth 128
      (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec)), tid }).1 ∧
      oc.thread.st = goto t.st t.st.st.1 (pcA 14) ∧ oc.thread.prom = [] ∧ CohMono t oc.thread := by
  have hex := exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO
  obtain ⟨h1, h2, h3⟩ := spec_store _ _ hp hex hs ho
  exact ⟨h1, h2, h3, (spec_store_coh _ _ hp hex hs ho).1⟩

theorem s14 (hpc : t.st.st.2 = pcA 14) :
    oc.mem = mem ∧ oc.thread.st = goto t.st
      { t.st.st.1 with
        regs := t.st.st.1.regs.setXReg .X7 (BitVec.setWidth 64 (t.st.st.1.regs.X7.toBitVec.take 32 - 1#32)) }
      (pcA 15) ∧ oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_sub _ (hS.at (by decide) (by decide) hpc)) hs ho

theorem s15 (hpc : t.st.st.2 = pcA 15) :
    oc.mem = mem ∧ oc.thread.st = goto t.st t.st.st.1 (pcA 3) ∧
      oc.thread.prom = t.prom ∧ oc.thread.views.coh = t.views.coh :=
  spec_done _ _ (exec_b_round _ (hS.at (by decide) (by decide) hpc)) hs ho

end Steps

/-! ## Word arithmetic -/

theorem w32_zero_iff (r : UInt64) : w32 r = 0#32 ↔ wn r = 0 := by
  rw [← toNat_w32]
  exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩

theorem wn_sub1 (r : UInt64) (h : wn r ≠ 0) :
    (BitVec.setWidth 64 (r.toBitVec.take 32 - 1#32)).toNat % 2 ^ 32 = wn r - 1 := by
  have h' : r.toBitVec.toNat % 2 ^ 32 ≠ 0 := h
  have hlt : r.toBitVec.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  simp only [wn, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.take, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, BitVec.toNat_ofNat]
  show _ = r.toBitVec.toNat % 2 ^ 32 - 1
  omega

theorem wn_add1 (r : UInt64) (m : Nat) (h : wn r = m) (hm : m + 1 < 2 ^ 32) :
    (BitVec.setWidth 64 (r.toBitVec.take 32 + 1#32)).toNat % 2 ^ 32 = m + 1 := by
  have h' : r.toBitVec.toNat % 2 ^ 32 = m := h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.take, BitVec.extractLsb'_toNat,
    Nat.shiftRight_zero, h', BitVec.toNat_ofNat]
  omega

/-! ## One thread's step -/

/-- What one step of a thread does to the invariant's quantities. -/
inductive StepRes (k : Nat) (x o c : BitVec 64) (m xc tid : Nat) (t : Thread isa) (mem : Memory)
    (oc : Outcome isa) : Prop
  /-- No ticket taken, `owner` not written. -/
  | same (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (ht : TInv k x o c m oc.thread) (htk : Ticketed oc.thread ↔ Ticketed t)
      (hk : Ticketed t → tk oc.thread = tk t) (hn : taken k oc.thread = taken k t) (hco : CohMono t oc.thread)
  /-- `LDADDA`: the ticket `xc` taken. -/
  | tkt (v : Val) (hv : v.toNat = xc + 1) (hm : oc.mem = (mem.append { loc := L4 x, val := v, tid }).1)
      (ht : TInv k x o c m oc.thread) (h0 : ¬ Ticketed t) (h1 : Ticketed oc.thread) (hk : tk oc.thread = xc)
      (hn : taken k oc.thread = taken k t + 1) (hco : CohMono t oc.thread)
      (hlc : mem.last + 1 ≤ oc.thread.views.getCoh (L4 x))
  /-- `STLR`: `owner := m + 1` by the holder of `m`. -/
  | rel (v : Val) (hv : v.toNat = m + 1) (hm : oc.mem = (mem.append { loc := L4 o, val := v, tid }).1)
      (ht : TInv k x o c (m + 1) oc.thread) (h0 : Ticketed t) (h1 : ¬ Ticketed oc.thread) (hk0 : tk t = m)
      (hn : taken k oc.thread = taken k t) (hco : CohMono t oc.thread)

/-- The per-thread invariant after a step that keeps `X6` and `X7`. -/
local macro "tinv" h:ident hst:ident hp:term "," h6:term "," j:num : term =>
  `(⟨by rw [$hst:ident]; exact ($h).st.goto _ _ rfl rfl rfl rfl, $hp, by rw [$hst:ident]; exact ($h).k7,
    .inr (by rw [$hst:ident]; exact $h6), $j, by decide, by rw [$hst:ident] <;> rfl, ?_⟩)

set_option hygiene false in
/-- The ticket and `taken` facts of a step between positions `i` and `j` that
keeps `X3` and `X7`. -/
local macro "same" hpc:ident hst:ident i:num j:num : tactic =>
  `(tactic| (
    have hpc' : oc.thread.st.st.2 = pcA $j := by rw [$hst:ident] <;> rfl
    obtain ⟨htk, hk⟩ := same_tk (i := $i) (j := $j) (by decide) (by decide) $hpc hpc' (by rw [$hst:ident] <;> rfl)
      (by decide)
    have hn := same_taken (k := k) (i := $i) (j := $j) (by decide) (by decide) $hpc hpc'
      (by rw [$hst:ident] <;> rfl) (by decide)))

set_option maxHeartbeats 800000 in
/-- **One thread's step**, by position. -/
theorem thread_step {k : Nat} {x o c : BitVec 64} {m xc tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TInv k x o c m t)
    (hxc : xc + 1 < 2 ^ 32) (hmxc : m ≤ xc) (hfx : (mem.finalVal (L4 x)).toNat = xc)
    (hown : OwnLe mem tid (L4 x) (t.views.getCoh (L4 x)))
    (hov : ∀ ts v, mem.read? (L4 o) ts = some v → v.toNat ≤ m)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    StepRes k x o c m xc tid t mem oc := by
  obtain ⟨i, hi, hpc, hinv⟩ := h.pc
  have hS := h.st
  have hi' := hi
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `MOV W6, #1`
    obtain ⟨hm, hst, hp, hco⟩ := s1 hS hs ho hpc
    same hpc hst 1 3
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), (rfl : wn (UInt64.ofBitVec 1#64) = 1), 3) htk hk hn
      (cohMono_of_eq hco)
    trivial
  · -- 3: `CBZ W7, done`
    obtain ⟨hm, hst, hp, hco⟩ := s3 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    by_cases hz : w32 t.st.st.1.regs.X7 = 0#32
    · rw [ite_eq_left hz] at hst
      same hpc hst 3 17
      refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 17) htk hk hn (cohMono_of_eq hco)
      trivial
    · rw [ite_eq_right hz] at hst
      same hpc hst 3 4
      refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 4) htk hk hn (cohMono_of_eq hco)
      rw [hst]; exact fun e => hz ((w32_zero_iff _).mpr e)
  · -- 4: `LDADDA`
    obtain ⟨hst, hm, hp, hco, hlc⟩ := s4 hS h.prom hs ho hpc hown
    have h6 := h.x6' hi hpc (by decide)
    have h7 : wn t.st.st.1.regs.X7 ≠ 0 := hinv
    have hpc' : oc.thread.st.st.2 = pcA 6 := by rw [hst] <;> rfl
    have hk : tk oc.thread = xc := by
      unfold tk; rw [hst, ← hfx]; show (BitVec.setWidth 64 (BitVec.setWidth 32 _)).toNat % 2 ^ 32 = _
      simp [BitVec.toNat_setWidth]; omega
    refine .tkt _ ?_ hm (tinv h hst hp, h6, 6) (fun h' => absurd ((ticketed_iff hi hpc).mp h') (by decide))
      ((ticketed_iff (by decide) hpc').mpr (by decide)) hk ?_ hco hlc
    · simp only [BitVec.toNat_setWidth, BitVec.toNat_add, hfx]
      simp only [wn] at h6
      have : t.st.st.1.regs.X6.toBitVec.toNat % 2 ^ 32 = 1 := h6
      rw [this, Nat.mod_eq_of_lt (by omega : xc < 2 ^ 32)]
      omega
    · show wn oc.thread.st.st.1.regs.X7 ≠ 0 ∧ m ≤ tk oc.thread
      refine ⟨?_, by omega⟩
      rw [hst]; exact h7
    · rw [taken_at (by decide) hpc', taken_at hi hpc, hst]
      simp only [show (6 : Nat) ∈ tkBusy from by decide, show ¬ (4 : Nat) ∈ tkBusy from by decide, ite_true,
        ite_false]
      rfl
  · -- 6: `LDAR W4, [X1]`
    obtain ⟨ts, v, hst, hrd, -, hm, hp, -, hco⟩ := s6 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    have hv := hov ts v hrd
    same hpc hst 6 7
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 7) htk hk hn hco
    rw [hst]
    refine ⟨hinv.1, hinv.2, ?_⟩
    show (BitVec.setWidth 64 (BitVec.setWidth 32 v)).toNat % 2 ^ 32 ≤ m
    simp only [BitVec.toNat_setWidth]; omega
  · -- 7: `CMP W4, W3`
    obtain ⟨sf, hst, hz, hm, hp, hco⟩ := s7 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    obtain ⟨h1, h2, h3⟩ := (hinv : wn t.st.st.1.regs.X7 ≠ 0 ∧ m ≤ wn t.st.st.1.regs.X3 ∧ wn t.st.st.1.regs.X4 ≤ m)
    same hpc hst 7 8
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 8) htk hk hn (cohMono_of_eq hco)
    rw [hst]
    show wn t.st.st.1.regs.X7 ≠ 0 ∧ m ≤ wn t.st.st.1.regs.X3 ∧ (sf.z = true → wn t.st.st.1.regs.X3 = m)
    exact ⟨h1, h2, fun hz' => by have := hz.mp hz'; omega⟩
  · -- 8: `B.NE spin`
    obtain ⟨hm, hst, hp, hco⟩ := s8 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    obtain ⟨h1, h2, h3⟩ := (hinv : wn t.st.st.1.regs.X7 ≠ 0 ∧ m ≤ wn t.st.st.1.regs.X3 ∧
      (t.st.st.1.status.z = true → wn t.st.st.1.regs.X3 = m))
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      same hpc hst 8 9
      refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 9) htk hk hn (cohMono_of_eq hco)
      rw [hst]; exact ⟨h1, h3 hz⟩
    · rw [ite_eq_right hz] at hst
      same hpc hst 8 6
      refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 6) htk hk hn (cohMono_of_eq hco)
      rw [hst]; exact ⟨h1, h2⟩
  · -- 9: `LDR W5, [X2]`
    obtain ⟨v, hst, hm, hp, hco⟩ := s9 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    same hpc hst 9 10
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 10) htk hk hn hco
    rw [hst]; exact hinv
  · -- 10: `ADD W5, W5, #1`
    obtain ⟨hm, hst, hp, hco⟩ := s10 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    same hpc hst 10 11
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 11) htk hk hn (cohMono_of_eq hco)
    rw [hst]; exact hinv
  · -- 11: `STR W5, [X2]`
    obtain ⟨hm, hst, hp, hco⟩ := s11 hS h.prom hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    same hpc hst 11 12
    refine .same (.inr ⟨_, hm⟩) (tinv h hst hp, h6, 12) htk hk hn hco
    rw [hst]; exact hinv
  · -- 12: `ADD W4, W3, #1`
    obtain ⟨hm, hst, hp, hco⟩ := s12 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    obtain ⟨h1, h3⟩ := (hinv : wn t.st.st.1.regs.X7 ≠ 0 ∧ wn t.st.st.1.regs.X3 = m)
    same hpc hst 12 13
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 13) htk hk hn (cohMono_of_eq hco)
    rw [hst]
    exact ⟨h1, h3, wn_add1 _ m h3 (by omega)⟩
  · -- 13: `STLR W4, [X1]`
    obtain ⟨hm, hst, hp, hco⟩ := s13 hS h.prom hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    obtain ⟨h1, h3, h4⟩ := (hinv : wn t.st.st.1.regs.X7 ≠ 0 ∧ wn t.st.st.1.regs.X3 = m ∧
      wn t.st.st.1.regs.X4 = m + 1)
    have hpc' : oc.thread.st.st.2 = pcA 14 := by rw [hst] <;> rfl
    refine .rel _ ?_ hm (tinv h hst hp, h6, 14) ((ticketed_iff hi hpc).mpr (by decide))
      (fun h' => absurd ((ticketed_iff (by decide) hpc').mp h') (by decide)) h3
      (same_taken (k := k) hi (by decide) hpc hpc' (by rw [hst] <;> rfl) (by decide)) hco
    · rw [← h4]; simp [BitVec.toNat_setWidth, wn]; omega
    · rw [hst]; exact h1
  · -- 14: `SUB W7, W7, #1`
    obtain ⟨hm, hst, hp, hco⟩ := s14 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    have h7 : wn t.st.st.1.regs.X7 ≠ 0 := hinv
    have hpc' : oc.thread.st.st.2 = pcA 15 := by rw [hst] <;> rfl
    have h7' : wn oc.thread.st.st.1.regs.X7 = wn t.st.st.1.regs.X7 - 1 := by
      rw [hst]; exact wn_sub1 _ h7
    obtain ⟨htk, hk⟩ : (Ticketed oc.thread ↔ Ticketed t) ∧ (Ticketed t → tk oc.thread = tk t) :=
      ⟨by rw [ticketed_iff (by decide) hpc', ticketed_iff hi hpc]; decide,
        fun h' => absurd ((ticketed_iff hi hpc).mp h') (by decide)⟩
    have hk7 := h.k7
    refine .same (.inl hm) ⟨by rw [hst]; exact hS.goto _ _ rfl rfl rfl rfl, hp.trans h.prom, by omega,
      .inr (by rw [hst]; exact h6), 15, by decide, hpc', trivial⟩ htk hk ?_ (cohMono_of_eq hco)
    rw [taken_at (by decide) hpc', taken_at hi hpc, h7']
    simp only [show ¬ (15 : Nat) ∈ tkBusy from by decide, show (14 : Nat) ∈ tkBusy from by decide, ite_true,
      ite_false]
    omega
  · -- 15: `B round`
    obtain ⟨hm, hst, hp, hco⟩ := s15 hS hs ho hpc
    have h6 := h.x6' hi hpc (by decide)
    same hpc hst 15 3
    refine .same (.inl hm) (tinv h hst (hp.trans h.prom), h6, 3) htk hk hn (cohMono_of_eq hco)
    trivial
  · rw [stepOne_end hS hpc] at hs; cases hs

/-! ## The global invariant -/

/-- **The invariant** of a configuration of `N` workers running `k` rounds,
with `xc` tickets taken and ticket `m` served. -/
structure InvL (k N : Nat) (x o c : BitVec 64) (xc m : Nat) (cfg : Config isa) : Prop where
  size : cfg.threads.size = N
  Nk32 : N * k + 1 < 2 ^ 32
  hxo : L4 x ≠ L4 o
  hxc : L4 x ≠ L4 c
  hoc : L4 o ≠ L4 c
  bnd : cfg.Bnd
  fx : (cfg.mem.finalVal (L4 x)).toNat = xc
  fo : (cfg.mem.finalVal (L4 o)).toNat = m
  ov : ∀ ts v, cfg.mem.read? (L4 o) ts = some v → v.toNat ≤ m
  mxc : m ≤ xc
  xs : tsum cfg (fun _ t => taken k t) = xc
  thr : ∀ (i : Nat) t, cfg.threads[i]? = some t → TInv k x o c m t
  own : ∀ (i : Nat) t, cfg.threads[i]? = some t → OwnLe cfg.mem i (L4 x) (t.views.getCoh (L4 x))
  tkLt : ∀ (i : Nat) t, cfg.threads[i]? = some t → Ticketed t → tk t < xc
  tkInj : ∀ (i j : Nat) ti tj, cfg.threads[i]? = some ti → cfg.threads[j]? = some tj → Ticketed ti → Ticketed tj →
    tk ti = tk tj → i = j
  tkSurj : ∀ v, m ≤ v → v < xc → ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Ticketed t ∧ tk t = v

/-- At most `N * k` tickets are ever taken. -/
theorem InvL.xcle {k N : Nat} {x o c : BitVec 64} {xc m : Nat} {cfg : Config isa} (h : InvL k N x o c xc m cfg) :
    xc ≤ N * k := by
  rw [← h.xs, ← h.size]; exact tsum_le fun i u hu => taken_le (h.thr i u hu)

/-- A waiter of the old invariant is a waiter of the next `m`, if it does not
hold `m`. -/
theorem PcInv.bump {m : Nat} {s : MachineData} {i : Nat} (hp : PcInv m s i) (hi : i ∈ tkLoopPcs)
    (hne : i ∈ tkHeld → wn s.regs.X3 ≠ m) : PcInv (m + 1) s i := by
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [PcInv] at hp ⊢) <;> first | exact hp | trivial |
      (have := hne (by decide); first | omega | exact ⟨hp.1, by omega, fun hz => absurd (hp.2.2 hz) this⟩)

section Pres

variable {k N xc m tid : Nat} {x o c : BitVec 64} {cfg : Config isa} {t t' : Thread isa} {mem' : Memory}
  (h : InvL k N x o c xc m cfg) (ht : cfg.threads[tid]? = some t) (hb : (cfg.withThread tid t' mem').Bnd)

include h ht

theorem xs_step {d : Nat} (hn : taken k t' = taken k t + d) :
    tsum (cfg.withThread tid t' mem') (fun _ u => taken k u) = xc + d := by
  have := tsum_withThread_add (mem' := mem') (t' := t') ht (F := fun _ u => taken k u) (F' := fun _ u => taken k u)
    fun _ _ _ _ => rfl
  have := h.xs; omega

theorem thr_step (hT : TInv k x o c m t') :
    ∀ (i : Nat) u, (cfg.withThread tid t' mem').threads[i]? = some u → TInv k x o c m u := fun i u hu => by
  rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
  · exact hT
  · exact h.thr i u hu

theorem own_step (hself : OwnLe mem' tid (L4 x) (t'.views.getCoh (L4 x)))
    (hother : ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → OwnLe mem' i (L4 x) (u.views.getCoh (L4 x))) :
    ∀ (i : Nat) u, (cfg.withThread tid t' mem').threads[i]? = some u →
      OwnLe (cfg.withThread tid t' mem').mem i (L4 x) (u.views.getCoh (L4 x)) := fun i u hu => by
  rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨hne, hu⟩
  · exact hself
  · exact hother i u hne hu

include hb

/-- A step that takes no ticket and does not write `owner`. -/
theorem inv_same (hT : TInv k x o c m t') (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hn : taken k t' = taken k t) (hco : CohMono t t')
    (hm : mem' = cfg.mem ∨ ∃ v, mem' = (cfg.mem.append { loc := L4 c, val := v, tid }).1) :
    InvL k N x o c xc m (cfg.withThread tid t' mem') := by
  have hmem : mem'.finalVal (L4 x) = cfg.mem.finalVal (L4 x) ∧ mem'.finalVal (L4 o) = cfg.mem.finalVal (L4 o) ∧
      (∀ ts v, mem'.read? (L4 o) ts = some v → cfg.mem.read? (L4 o) ts = some v) ∧
      OwnLe mem' tid (L4 x) (t'.views.getCoh (L4 x)) ∧
      ∀ (i : Nat) u, i ≠ tid → cfg.threads[i]? = some u → OwnLe mem' i (L4 x) (u.views.getCoh (L4 x)) := by
    rcases hm with rfl | ⟨v, rfl⟩
    · exact ⟨rfl, rfl, fun _ _ h => h, (h.own tid t ht).mono (hco _), fun i u _ hu => h.own i u hu⟩
    · obtain ⟨a1, -, -, -⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hxc)
      obtain ⟨b1, -, b3, -⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hoc)
      exact ⟨a1, b1, b3, ((h.own tid t ht).append_other (.inl (Ne.symm h.hxc))).mono (hco _),
        fun i u _ hu => (h.own i u hu).append_other (.inl (Ne.symm h.hxc))⟩
  obtain ⟨m1, m2, m3, m4, m5⟩ := hmem
  refine ⟨by simp [Config.withThread, h.size], h.Nk32, h.hxo, h.hxc, h.hoc, hb, m1 ▸ h.fx, m2 ▸ h.fo,
    fun ts v hr => h.ov ts v (m3 ts v hr), h.mxc, xs_step (d := 0) h ht hn, thr_step h ht hT,
    own_step h ht m4 m5, ?_, ?_, ?_⟩
  · intro i u hu hk'
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · rw [hk (htk.mp hk')]; exact h.tkLt tid t ht (htk.mp hk')
    · exact h.tkLt i u hu hk'
  · intro i j ti tj hi hj hti htj e
    rcases wt_get ht hi with ⟨rfl, rfl⟩ | ⟨-, hi2⟩ <;> rcases wt_get ht hj with ⟨rfl, rfl⟩ | ⟨-, hj2⟩
    · rfl
    · exact h.tkInj _ _ _ _ ht hj2 (htk.mp hti) htj (by rw [← hk (htk.mp hti)]; exact e)
    · exact h.tkInj _ _ _ _ hi2 ht hti (htk.mp htj) (by rw [← hk (htk.mp htj)]; exact e)
    · exact h.tkInj _ _ _ _ hi2 hj2 hti htj e
  · intro v hv1 hv2
    obtain ⟨i, u, hu, h1, h2⟩ := h.tkSurj v hv1 hv2
    by_cases e : i = tid
    · subst e; rw [ht] at hu; cases hu
      exact ⟨i, t', wt_tid ht, htk.mpr h1, by rw [hk h1]; exact h2⟩
    · exact ⟨i, u, by rw [wt_ne ht e]; exact hu, h1, h2⟩

/-- `LDADDA`: the ticket `xc` taken. -/
theorem inv_tkt (v : Val) (hv : v.toNat = xc + 1) (hm : mem' = (cfg.mem.append { loc := L4 x, val := v, tid }).1)
    (hT : TInv k x o c m t') (h0 : ¬ Ticketed t) (h1 : Ticketed t') (hk : tk t' = xc)
    (hn : taken k t' = taken k t + 1) (hco : CohMono t t') (hlc : cfg.mem.last + 1 ≤ t'.views.getCoh (L4 x)) :
    InvL k N x o c (xc + 1) m (cfg.withThread tid t' mem') := by
  subst hm
  obtain ⟨b1, -, b3, -⟩ := mem_frame cfg.mem { loc := L4 x, val := v, tid } h.hxo
  have hother : ∀ i u, cfg.threads[i]? = some u → Ticketed u → i ≠ tid := fun i u hu hu' e => by
    subst e; rw [ht] at hu; cases hu; exact h0 hu'
  refine ⟨by simp [Config.withThread, h.size], h.Nk32, h.hxo, h.hxc, h.hoc, hb, ?_, b1 ▸ h.fo,
    fun ts v hr => h.ov ts v (b3 ts v hr), by have := h.mxc; omega, xs_step h ht hn, thr_step h ht hT,
    own_step h ht ((h.own tid t ht).append_self (hco _) hlc _)
      (fun i u hne hu => (h.own i u hu).append_other (.inr (Ne.symm hne))), ?_, ?_, ?_⟩
  · show BitVec.toNat ((cfg.mem.append { loc := L4 x, val := v, tid }).1.finalVal (L4 x)) = xc + 1
    rw [finalVal_append]; simpa using hv
  · intro i u hu hk'
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · omega
    · have := h.tkLt i u hu hk'; omega
  · intro i j ti tj hi hj hti htj e
    rcases wt_get ht hi with ⟨rfl, rfl⟩ | ⟨-, hi2⟩ <;> rcases wt_get ht hj with ⟨rfl, rfl⟩ | ⟨-, hj2⟩
    · rfl
    · have := h.tkLt _ _ hj2 htj; omega
    · have := h.tkLt _ _ hi2 hti; omega
    · exact h.tkInj _ _ _ _ hi2 hj2 hti htj e
  · intro w hw1 hw2
    by_cases e : w = xc
    · exact ⟨tid, t', wt_tid ht, h1, hk.trans e.symm⟩
    · obtain ⟨i, u, hu, h1', h2⟩ := h.tkSurj w hw1 (by omega)
      exact ⟨i, u, by rw [wt_ne ht (hother i u hu h1')]; exact hu, h1', h2⟩

/-- `STLR`: the holder of `m` serves `m + 1`. -/
theorem inv_rel (v : Val) (hv : v.toNat = m + 1) (hm : mem' = (cfg.mem.append { loc := L4 o, val := v, tid }).1)
    (hT : TInv k x o c (m + 1) t') (h0 : Ticketed t) (h1 : ¬ Ticketed t') (hk0 : tk t = m)
    (hn : taken k t' = taken k t) (hco : CohMono t t') :
    InvL k N x o c xc (m + 1) (cfg.withThread tid t' mem') := by
  subst hm
  obtain ⟨a1, -, -, -⟩ := mem_frame cfg.mem { loc := L4 o, val := v, tid } (Ne.symm h.hxo)
  have hlt := h.tkLt tid t ht h0
  refine ⟨by simp [Config.withThread, h.size], h.Nk32, h.hxo, h.hxc, h.hoc, hb, a1 ▸ h.fx, ?_, ?_,
    by omega, xs_step (d := 0) h ht hn, ?_,
    own_step h ht (((h.own tid t ht).append_other (.inl (Ne.symm h.hxo))).mono (hco _))
      (fun i u _ hu => (h.own i u hu).append_other (.inl (Ne.symm h.hxo))), ?_, ?_, ?_⟩
  · show BitVec.toNat ((cfg.mem.append { loc := L4 o, val := v, tid }).1.finalVal (L4 o)) = m + 1
    rw [finalVal_append]; simpa using hv
  · intro ts v' hr
    rcases read?_append_eq_some cfg.mem _ hr with hr | ⟨-, -, rfl⟩
    · have := h.ov ts v' hr; omega
    · exact Nat.le_of_eq hv
  · intro i u hu
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨hi, hu⟩
    · exact hT
    · obtain ⟨hS, hp, h7, h6, j, hj, hpc, hinv⟩ := h.thr i u hu
      exact ⟨hS, hp, h7, h6, j, hj, hpc, hinv.bump hj fun jh e =>
        hi (h.tkInj i tid u t hu ht ((ticketed_iff hj hpc).mpr jh) h0 (e.trans hk0.symm))⟩
  · intro i u hu hk'
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · exact absurd hk' h1
    · exact h.tkLt i u hu hk'
  · intro i j ti tj hi hj hti htj e
    rcases wt_get ht hi with ⟨rfl, rfl⟩ | ⟨-, hi2⟩ <;> rcases wt_get ht hj with ⟨rfl, rfl⟩ | ⟨-, hj2⟩
    · rfl
    · exact absurd hti h1
    · exact absurd htj h1
    · exact h.tkInj _ _ _ _ hi2 hj2 hti htj e
  · intro w hw1 hw2
    obtain ⟨i, u, hu, h1', h2⟩ := h.tkSurj w (by omega) hw2
    have hne : i ≠ tid := fun e => by subst e; rw [ht] at hu; cases hu; omega
    exact ⟨i, u, by rw [wt_ne ht hne]; exact hu, h1', h2⟩

end Pres

/-! ## Steps and traces -/

/-- **An instruction step keeps the invariant**: either `owner` is untouched
(last write and value), or the holder of `m` released, serving `m + 1`. -/
theorem step_inv {k N xc m tid : Nat} {x o c : BitVec 64} {cfg cfg' : Config isa}
    (h : InvL k N x o c xc m cfg) (hb : cfg'.Bnd) (hi : InstrBy Arch.armv8 tid cfg cfg') :
    (∃ xc', InvL k N x o c xc' m cfg' ∧ cfg'.mem.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
      InvL k N x o c xc (m + 1) cfg' := by
  obtain ⟨t, outs, oc, ht, hs, ho, rfl⟩ := hi
  have hxc : xc + 1 < 2 ^ 32 := by have := h.xcle; have := h.Nk32; omega
  cases thread_step (h.thr tid t ht) hxc h.mxc h.fx (h.own tid t ht) h.ov hs ho with
  | same hm hT htk hk hn hco =>
    refine .inl ⟨xc, inv_same h ht hb hT htk hk hn hco hm, ?_⟩
    show oc.mem.lastWrite _ = _
    rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
    exact (mem_frame _ _ (Ne.symm h.hoc)).2.1
  | tkt v hv hm hT h0 h1 hk hn hco hlc =>
    refine .inl ⟨xc + 1, inv_tkt h ht hb v hv hm hT h0 h1 hk hn hco hlc, ?_⟩
    show oc.mem.lastWrite _ = _
    rw [hm]; exact (mem_frame _ _ h.hxo).2.1
  | rel v hv hm hT h0 h1 hk0 hn hco => exact .inr (inv_rel h ht hb v hv hm hT h0 h1 hk0 hn hco)

/-- **The invariant holds initially.** -/
theorem inv_init {k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) : InvL k N x o c 0 0 (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  have hpc1 : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      t.st.st.2 = pcA 1 := fun i t h => by
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    exact (hs.hst s hm).pc.trans addrOf_0
  have hnt : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t → ¬ Ticketed t :=
    fun i t h ht => absurd ((ticketed_iff (by decide) (hpc1 i t h)).mp ht) (by decide)
  have hN : (Config.init states initMem : Config isa).threads.size = N := by simp [Config.init, hs.hN]
  refine ⟨hN, by have := hs.hNk32; omega, loc_ne hs.hxo, loc_ne hs.hxc, loc_ne hs.hoc, Config.init_bnd _ _,
    ?_, ?_, ?_, Nat.le_refl _, ?_, ?_, ?_, fun i t h ht => absurd ht (hnt i t h),
    fun i _ _ _ h _ ht _ _ => absurd ht (hnt i _ h), fun _ h1 h2 => absurd h2 (by omega)⟩
  · have := hs.hX0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · have := hs.hO0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · intro ts v h
    have := hs.hO0
    simp only [Memory.read?, Memory.get?, Config.init] at h this
    split at h
    · cases h; simp [this]
    · simp at h
  · have := tsum_le (c := (Config.init states initMem : Config isa)) (F := fun _ t => taken k t) (M := 0)
      fun i u hu => by
        obtain ⟨s, hm, rfl⟩ := hthr i u hu
        rw [taken_at (by decide) (hpc1 i _ hu)]
        have h7 := (hs.hst s hm).x7
        show k - wn s.st.1.regs.X7 + (if 1 ∈ tkBusy then 1 else 0) ≤ 0
        rw [h7]; simp [tkBusy]
    omega
  · intro i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    exact ⟨⟨hs.exe, hs.decls, hs.endPc, hs.x0, hs.x1, hs.x2, hs.dx, hs.dO, hs.dc⟩, rfl, Nat.le_of_eq hs.x7,
      .inl (hs.pc.trans addrOf_0), 1, by decide, hs.pc.trans addrOf_0, trivial⟩
  · intro i t _ ts w hw
    simp [Config.init, Memory.get?] at hw

end Kraken.Promising.Live.TicketLoopInv
