/-
**Stage 3: one step of the x64 ticket-lock worker
with any promise set** (`ticketlock3.kl`, `tk3ImageV`, `Arch.tso`).

- `q1`–`q12`: what an instruction step at each position does, for any
  promise set and memory: the next state (`TicketX64Trees.goto`), the register
  results the proof reads, and memory/promises (`spec_done`, `spec_load`,
  `SemShape.spec_store_p`, `X64SemShape.spec_rmw_p_tso`). Every later file
  consumes these instead of re-reading the trees.
- `SInv` (`Static` and a pc in `tkPcs`), kept by every instruction step,
  which drops at most one promise (`step_sinv`), hence `dropBounded_of_sinv`
  (`DropBounded Arch.tso 1`): the x64 counterpart of `LiveTicketDrop`.
- `nextPc`, `pos_step`: the position after a step.
-/
import Kraken.Promising.LiveX64Sem
import Kraken.Promising.LiveX64SemShape
import Kraken.Promising.LiveX64TicketInv

namespace Kraken.Promising.Live.X64SemStep

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketX64Trees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.X64SemShape
open Kraken.Promising.Live.TicketX64Inv (XL OL CL Static Ticketed tk ticketed_at stepOne_end)
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV symTk)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk3ImageV).addrOf

/-- The disjunction of `spec_store_p`/`spec_rmw_p_tso` for a write of `v` to
`l` by `tid` (`tr`: the RMW's read; `rel`: the write is a release). -/
def WriteP (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) (l : Loc) (v : Val) : Prop :=
  (oc.mem = (mem.append { loc := l, val := v, tid }).1 ∧
    oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
  (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := v, tid } ∧ t.views.getCoh l < ts ∧
    t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld)

theorem WriteP.len {tid : Nat} {t : Thread isa} {mem : Memory} {oc : Outcome isa} {l : Loc} {v : Val}
    (h : WriteP tid t mem oc l v) : t.prom.length ≤ oc.thread.prom.length + 1 := by
  rcases h with ⟨-, hp, -⟩ | ⟨ts, -, -, -, -, -, hp, -⟩ <;> rw [hp, List.length_erase] <;> split <;>
    (try simp) <;> omega

/-- The value `lock xaddl` writes to `next`: the old low word plus `%eax`'s. -/
abbrev xv (old : Val) (e : BitVec 32) : Val := BitVec.setWidth 128 (BitVec.setWidth 32 old + e)

omit layout hv in
/-- `xv` adding one, as a number (the layout-free core of
`X64SemSolo.xv_toNat` / `X64Sem2Solo.xv_toNat`). -/
theorem toNat_xv (old : Val) (e : BitVec 32) (he : e.toNat = 1) :
    (xv old e).toNat = (old.toNat % 2 ^ 32 + 1) % 2 ^ 32 := by
  simp only [xv, BitVec.toNat_setWidth, BitVec.toNat_add, he]; omega

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
  {oc : Outcome isa} (hS : Static t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The facts of a step that keeps memory and promises. -/
abbrev Q (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop :=
  oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.vwOld = t.views.vwOld

theorem q1 (hpc : t.st.st.2 = pcA 1) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = 1#32 ∧ oc.thread.st = goto t.st md (pcA 2) := by
  obtain ⟨md, hd, he, hex⟩ := exec_mov1 _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨h1, h2, h3, -⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨h1, h3, spec_done_vw _ _ hex hs ho⟩, md, hd, he, h2⟩

theorem q2 (hpc : t.st.st.2 = pcA 2) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ ∃ tr old, eax md = BitVec.setWidth 32 old ∧
      oc.thread.st = goto t.st md (pcA 4) ∧ mem.read? XL tr = some old ∧
      ((oc.mem = (mem.append { loc := XL, val := xv old (eax t.st.st.1), tid }).1 ∧
        oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld ∧
        mem.atomic XL tid tr (mem.last + 1) = true) ∨
      (∃ ts ∈ t.prom,
        mem.get? ts = some { loc := XL, val := xv old (eax t.st.st.1), tid } ∧
        t.views.getCoh XL < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧
        t.views.vwOld ≤ oc.thread.views.vwOld ∧ tr < ts ∧ mem.atomic XL tid tr ts = true)) := by
  obtain ⟨g, hg, hex⟩ := exec_xadd _ (hS.at (by decide) (by decide) hpc) hS.dx
  obtain ⟨tr, old, h1, h2, h3⟩ := spec_rmw_p_tso _ _ rfl hex hs ho
  refine ⟨g old, (hg old).1, tr, old, (hg old).2, h1, h2, ?_⟩
  rcases h3 with ⟨a, b, c, d⟩ | h
  · exact .inl ⟨a, b, c rfl, d⟩
  · exact .inr h

theorem q4 (hpc : t.st.st.2 = pcA 4) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ∃ ts v,
      ecx md = BitVec.setWidth 32 v ∧ oc.thread.st = goto t.st md (pcA 5) ∧
      mem.read? OL ts = some v ∧ (mem.lastWrite OL ≤ t.views.getCoh OL → v = mem.finalVal OL) ∧
      ∃ ν, TraceEv.read OL ts v ν ∈ oc.log := by
  obtain ⟨g, hg, hex⟩ := exec_ldo _ (hS.at (by decide) (by decide) hpc) hS.dO
  obtain ⟨ts, v, h1, h2, h3, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨⟨h4, h5, spec_load_vw _ _ hex hs ho⟩, g v, (hg v).1, (hg v).2.1, ts, v, (hg v).2.2, h1, h2, h3, h6⟩

theorem q5 (hpc : t.st.st.2 = pcA 5) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ecx md = ecx t.st.st.1 ∧
      (md.status.zf = true ↔ ecx t.st.st.1 = eax t.st.st.1) ∧ oc.thread.st = goto t.st md (pcA 6) ∧
      oc.thread.views.coh = t.views.coh := by
  obtain ⟨md, h1, h2, h3, h4, hex⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, md, h1, h2, h3, h4, k2, k4⟩

theorem q6 (hpc : t.st.st.2 = pcA 6) : Q t mem oc ∧
    oc.thread.st = goto t.st t.st.st.1 (if t.st.st.1.status.zf then pcA 7 else pcA 4) ∧
      oc.thread.views.coh = t.views.coh := by
  have hex := exec_jne _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, k2, k4⟩

theorem q7 (hpc : t.st.st.2 = pcA 7) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ecx md = ecx t.st.st.1 ∧
      oc.thread.st = goto t.st md (pcA 8) := by
  obtain ⟨g, hg, hex⟩ := exec_ldc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨ts, v, h1, -, -, h4, h5, -⟩ := spec_load _ _ hex hs ho
  exact ⟨⟨h4, h5, spec_load_vw _ _ hex hs ho⟩, g v, (hg v).1, (hg v).2.1, (hg v).2.2, h1⟩

theorem q8 (hpc : t.st.st.2 = pcA 8) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ecx md = ecx t.st.st.1 ∧
      oc.thread.st = goto t.st md (pcA 9) := by
  obtain ⟨md, h1, h2, h3, hex⟩ := exec_addd _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, -⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, md, h1, h2, h3, k2⟩

theorem q9 (hpc : t.st.st.2 = pcA 9) :
    ∃ (v : Val) (md : MachineData), md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ecx md = ecx t.st.st.1 ∧
      oc.thread.st = goto t.st md (pcA 10) ∧ WriteP tid t mem oc CL v := by
  obtain ⟨v, md, h1, h2, h3, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨k1, k2⟩ := spec_store_p _ _ hex hs ho
  refine ⟨v, md, h1, h2, h3, k1, ?_⟩
  rcases k2 with ⟨a, b, c⟩ | ⟨ts, hts, a, b, c, d, e, f⟩
  · exact .inl ⟨a, b, c rfl⟩
  · exact .inr ⟨ts, hts, a, b, c rfl, d, e, f⟩

theorem q10 (hpc : t.st.st.2 = pcA 10) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ eax md = eax t.st.st.1 ∧ ecx md = ecx t.st.st.1 + 1#32 ∧
      oc.thread.st = goto t.st md (pcA 11) := by
  obtain ⟨md, h1, h2, h3, hex⟩ := exec_addc _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, -⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, md, h1, h2, h3, k2⟩

theorem q11 (hpc : t.st.st.2 = pcA 11) :
    oc.thread.st = goto t.st t.st.st.1 (pcA 12) ∧ WriteP tid t mem oc OL (BitVec.setWidth 128 (ecx t.st.st.1)) := by
  obtain ⟨k1, k2⟩ := spec_store_p _ _ (exec_rel _ (hS.at (by decide) (by decide) hpc) hS.dO) hs ho
  refine ⟨k1, ?_⟩
  rcases k2 with ⟨a, b, c⟩ | ⟨ts, hts, a, b, c, d, e, f⟩
  · exact .inl ⟨a, b, c rfl⟩
  · exact .inr ⟨ts, hts, a, b, c rfl, d, e, f⟩

theorem q12 (hpc : t.st.st.2 = pcA 12) : Q t mem oc ∧
    oc.thread.st = goto t.st t.st.st.1 (pcA 14) ∧ oc.thread.views.coh = t.views.coh := by
  have hex := exec_jmp _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, k2, k4⟩

end Steps

/-! ## The promise-agnostic thread invariant -/

/-- **The promise-agnostic per-thread invariant**: `Static` and a pc in
`tkPcs`. -/
structure SInv (s : isa.State) : Prop where
  st : Static s
  pc : ∃ i ∈ tkPcs, s.st.2 = pcA i

theorem SInv.goto {s : isa.State} (h : Static s) {md : MachineData} (hd : md.dmem = s.st.1.dmem) {j : Nat}
    (hj : j ∈ tkPcs) : SInv (goto s md (pcA j)) :=
  ⟨h.goto md _ hd, j, hj, rfl⟩

/-- The position after the instruction at position `p` (`z`: `ZF`). -/
def nextPc (z : Bool) : Nat → Nat
  | 1 => 2 | 2 => 4 | 4 => 5 | 5 => 6 | 6 => if z then 7 else 4 | 7 => 8 | 8 => 9 | 9 => 10 | 10 => 11
  | 11 => 12 | _ => 14

/-- **One instruction step keeps `SInv`, moves to `nextPc`, and drops at most
one promise**, for any promise set and memory. -/
theorem step_sinv {t : Thread isa} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {oc : Outcome isa} (h : SInv t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 ∧
      ∀ p ∈ tkPcs, t.st.st.2 = pcA p → oc.thread.st.st.2 = pcA (nextPc t.st.st.1.status.zf p) := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  have nx : ∀ j, oc.thread.st.st.2 = pcA j → j = nextPc t.st.st.1.status.zf i →
      ∀ p ∈ tkPcs, t.st.st.2 = pcA p → oc.thread.st.st.2 = pcA (nextPc t.st.st.1.status.zf p) :=
    fun j hj e p hp hp' => by rw [← addrOf_inj hi hp (hpc.symm.trans hp'), ← e]; exact hj
  have hle : ∀ {a b : Nat}, a = b → a ≤ b + 1 := fun e => by omega
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, hst⟩ := q1 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 2 (by rw [hst]) rfl⟩
  · obtain ⟨md, hd, tr, old, -, hst, -, hw⟩ := q2 hS hs ho hpc
    refine ⟨hst ▸ SInv.goto hS hd (by decide), ?_, nx 4 (by rw [hst]) rfl⟩
    rcases hw with ⟨-, hp, -⟩ | ⟨ts, -, -, -, -, hp, -⟩ <;> rw [hp, List.length_erase] <;> split <;>
      (try simp) <;> omega
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, ts, v, -, hst, -⟩ := q4 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 5 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, -, -, hst, -⟩ := q5 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 6 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, hst, -⟩ := q6 hS hs ho hpc
    by_cases hz : t.st.st.1.status.zf = true
    · rw [ite_eq_left hz] at hst
      exact ⟨hst ▸ SInv.goto hS rfl (by decide), hle (by rw [hp]), nx 7 (by rw [hst]) (by simp [nextPc, hz])⟩
    · rw [ite_eq_right hz] at hst
      exact ⟨hst ▸ SInv.goto hS rfl (by decide), hle (by rw [hp]), nx 4 (by rw [hst]) (by simp [nextPc, hz])⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, -, hst⟩ := q7 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 8 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, -, hst⟩ := q8 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 9 (by rw [hst]) rfl⟩
  · obtain ⟨v, md, hd, -, -, hst, hw⟩ := q9 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hw.len, nx 10 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, -, hst⟩ := q10 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 11 (by rw [hst]) rfl⟩
  · obtain ⟨hst, hw⟩ := q11 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS rfl (by decide), hw.len, nx 12 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, hst, -⟩ := q12 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS rfl (by decide), hle (by rw [hp]), nx 14 (by rw [hst]) rfl⟩
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {tid : Nat} {p q : Thread isa × Memory} (h : ThreadNP Arch.tso tid p q) (hp : SInv p.1.st) :
    SInv q.1.st :=
  ThreadNP.stateInv SInv (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {tid : Nat} {t : Thread isa} (h : SInv t.st) : DropBounded Arch.tso 1 tid t :=
  dropBounded_of_stateInv SInv (fun h hs ho => ⟨(step_sinv h hs ho).1, (step_sinv h hs ho).2.1⟩) h

end Kraken.Promising.Live.X64SemStep
