/-
**Stage 4: one step of the x64 `treiber2.kl` worker
with any promise set** (`treiber2ImageV`, `Arch.tso`). The
`LiveX64SemStep.lean` recipe on the cells of `LiveTermX64Treiber2Trees`.

- `Static`: the image, no declarations, the end address `pcT 16` and an empty
  private memory at every 8-byte word (`StartWV.d8`); every cell keeps it.
- `q2`–`q14`: what an instruction step at each position does, for any
  promise set and memory: the next state, the register results, and
  memory/promises (`spec_done`, `spec_load`, `SemShape.spec_store_p`,
  `SpinX64SemShape.spec_rmwo_p_tso`, `SpinX64Step.spec_choose`).
- `SInv` (`Static` and a pc in `tPcs`), kept by every instruction step,
  which drops at most one promise (`step_sinv`), hence `dropBounded_of_sinv`;
  `x64t2_tsoCertInv`: every cell makes no non-temporal store and at most one
  write, so `SInv` is a `TsoCertInv` (the no-stuck proofs' TSO consistency applies).
-/
import Kraken.Promising.LiveTermX64Treiber2Trees
import Kraken.Promising.LiveSpinX64SemShape
import Kraken.Promising.LiveNoStuckTso

namespace Kraken.Promising.Live.TermX64Treiber2Step

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.TermX64Treiber2Trees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.SpinX64SemShape Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.Live.NoStuck
open Kraken.Promising.X64.EnvG.Treiber2X (treiber2ImageV symT2 labT2)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiber2ImageV)]

set_option hygiene false in
local notation "pcT" => (layout treiber2ImageV).addrOf

/-- The location of `top`. -/
abbrev TopL : Loc := ⟨symT2 "top", 8⟩

/-- The link word of the node at `a`. -/
abbrev LinkL (a : BitVec 64) : Loc := ⟨a, 8⟩

/-- What a worker state never changes: its image, declarations, end address
and (empty) private memory. -/
structure Static (s : isa.State) : Prop where
  exe : s.exe = layout treiber2ImageV
  decls : s.decls = {}
  endPc : s.endPc = pcT 16
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none

omit hv in
theorem Static.goto {s : isa.State} (h : Static s) (md : MachineData) (pc : Int64) (hd : md.dmem = s.st.1.dmem) :
    Static (TermX64Treiber2Trees.goto s md pc) :=
  ⟨h.exe, h.decls, h.endPc, hd ▸ h.d8⟩

theorem Static.at {s : isa.State} (h : Static s) {i : Nat} (hi : i ∈ tPcs) (h16 : i ≠ 16)
    (hpc : s.st.2 = pcT i) : At s i :=
  ⟨h.exe, h.decls, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]; exact fun e => h16 (addrOf_inj hi (by decide) e)⟩

omit hv in
/-- At the end address the worker has halted. -/
theorem stepOne_end {t : Thread isa} (h : Static t.st) (hpc : t.st.st.2 = pcT 16)
    (A : Arch) (tid : Nat) (mem : Memory) : stepOne A t tid mem = none := by
  have : isa.exec t.st = none := by
    show X64.exec t.st = none
    unfold X64.exec
    rw [hpc, h.endPc]
    simp
  simp [stepOne, this]

/-- The disjunction of `spec_store_p`/`spec_rmwo_p_tso` for a write of `v` to
`l` by `tid`: an append, or the fulfilment of an outstanding promise above
the coherence view and `vwOld`. -/
def WriteP (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) (l : Loc) (v : Val) : Prop :=
  (oc.mem = (mem.append { loc := l, val := v, tid }).1 ∧
    oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
  (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := v, tid } ∧ t.views.getCoh l < ts ∧
    t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld)

omit layout hv in
theorem WriteP.len {tid : Nat} {t : Thread isa} {mem : Memory} {oc : Outcome isa} {l : Loc} {v : Val}
    (h : WriteP tid t mem oc l v) : t.prom.length ≤ oc.thread.prom.length + 1 := by
  rcases h with ⟨-, hp, -⟩ | ⟨ts, -, -, -, -, -, hp, -⟩ <;> rw [hp, List.length_erase] <;> split <;>
    (try simp) <;> omega

/-- The facts of a step that keeps memory and promises. -/
abbrev Q (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop :=
  oc.mem = mem ∧ oc.thread.prom = t.prom ∧ oc.thread.views.vwOld = t.views.vwOld

/-- The effect of `lock cmpxchgq %R,(top)` reading `old` at `tr`: no write
(the comparison failed), or one write of `new` (`WriteP`, atomic with `tr`). -/
def CasP (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) (tr : Time) (old : Val)
    (cmp : BitVec 64) (new : Val) : Prop :=
  (BitVec.setWidth 64 old ≠ cmp ∧ Q t mem oc) ∨
  (BitVec.setWidth 64 old = cmp ∧ WriteP tid t mem oc TopL new ∧
    ((oc.mem = (mem.append { loc := TopL, val := new, tid }).1 ∧ mem.atomic TopL tid tr (mem.last + 1) = true) ∨
     (∃ ts ∈ t.prom, mem.get? ts = some { loc := TopL, val := new, tid } ∧ oc.mem = mem ∧ tr < ts ∧
       mem.atomic TopL tid tr ts = true)))

omit hv in
theorem CasP.len {tid : Nat} {t : Thread isa} {mem : Memory} {oc : Outcome isa} {tr : Time} {old new : Val}
    {cmp : BitVec 64}
    (h : CasP tid t mem oc tr old cmp new) : t.prom.length ≤ oc.thread.prom.length + 1 := by
  rcases h with ⟨-, -, hp, -⟩ | ⟨-, hw, -⟩
  · rw [hp]; omega
  · exact hw.len

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
  {oc : Outcome isa} (hS : Static t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- `movq (top),%rax` (positions 2 and 7). -/
theorem qld {i : Nat} (hi : i = 2 ∨ i = 7) (hpc : t.st.st.2 = pcT i) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ md.regs.get64 .rbx = t.st.st.1.regs.get64 .rbx ∧
      ∃ ts v, md.regs.get64 .rax = BitVec.setWidth 64 v ∧ oc.thread.st = goto t.st md (pcT (i + 1)) ∧
      mem.read? TopL ts = some v ∧ (mem.lastWrite TopL ≤ t.views.getCoh TopL → v = mem.finalVal TopL) ∧
      ∃ ν, TraceEv.read TopL ts v ν ∈ oc.log := by
  obtain ⟨g, hg, hex⟩ := exec_ldtop _ hi (hS.at (by rcases hi with rfl | rfl <;> decide)
    (by rcases hi with rfl | rfl <;> decide) hpc) (hS.d8 _)
  obtain ⟨ts, v, h1, h2, h3, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨⟨h4, h5, spec_load_vw _ _ hex hs ho⟩, g v, (hg v).1, (hg v).2.2, ts, v, (hg v).2.1, h1, h2, h3, h6⟩

/-- `movq %rax,(%rbx)` (position 3). -/
theorem q3 (hpc : t.st.st.2 = pcT 3) :
    oc.thread.st = goto t.st t.st.st.1 (pcT 4) ∧
      WriteP tid t mem oc (LinkL (t.st.st.1.regs.get64 .rbx)) (BitVec.setWidth 128 (t.st.st.1.regs.get64 .rax)) := by
  obtain ⟨k1, k2⟩ := spec_store_p _ _ (exec_stlink _ (hS.at (by decide) (by decide) hpc) (hS.d8 _)) hs ho
  refine ⟨k1, ?_⟩
  rcases k2 with ⟨a, b, c⟩ | ⟨ts, hts, a, b, c, d, e, f⟩
  · exact .inl ⟨a, b, c rfl⟩
  · exact .inr ⟨ts, hts, a, b, c rfl, d, e, f⟩

/-- `lock cmpxchgq %R,(top)` (positions 4 with `%rbx`, 11 with `%rcx`). -/
theorem qcas {i : Nat} {r : Reg64} (hi : (i = 4 ∧ r = .rbx) ∨ (i = 11 ∧ r = .rcx)) (hpc : t.st.st.2 = pcT i) :
    ∃ tr old md, md.dmem = t.st.st.1.dmem ∧
      (md.status.zf = true ↔ BitVec.setWidth 64 old = t.st.st.1.regs.get64 .rax) ∧
      md.regs.get64 .rax = BitVec.setWidth 64 old ∧ md.regs.get64 .rbx = t.st.st.1.regs.get64 .rbx ∧
      oc.thread.st = goto t.st md (pcT (i + 1)) ∧ mem.read? TopL tr = some old ∧
      (mem.lastWrite TopL ≤ t.views.getCoh TopL → old = mem.finalVal TopL) ∧
      CasP tid t mem oc tr old (t.st.st.1.regs.get64 .rax)
        (BitVec.setWidth 128 (t.st.st.1.regs.get64 r)) := by
  have hi' : i ∈ tPcs ∧ i ≠ 16 := by rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  obtain ⟨g, hg, hex⟩ := exec_cas _ hi (hS.at hi'.1 hi'.2 hpc) (hS.d8 _)
  obtain ⟨tr, old, h1, h2, h3, h4⟩ := spec_rmwo_p_tso _ _ rfl hex hs ho
  refine ⟨tr, old, g old, (hg old).1, (hg old).2.1, (hg old).2.2.1, (hg old).2.2.2, h1, h2, h3, ?_⟩
  rcases h4 with ⟨hop, a, b, c⟩ | ⟨new, hop, h⟩
  · refine .inl ⟨fun e => ?_, a, b, c⟩
    simp [e] at hop
  · have he : BitVec.setWidth 64 old = t.st.st.1.regs.get64 .rax := by
      by_cases e : BitVec.setWidth 64 old = t.st.st.1.regs.get64 .rax
      · exact e
      · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at hop; cases hop
    simp only [he, ↓reduceIte, Option.some.injEq] at hop
    subst hop
    refine .inr ⟨he, ?_, ?_⟩
    · rcases h with ⟨a, b, c, -, -, -⟩ | ⟨ts, hts, a, b, c, d, e, f, -⟩
      · exact .inl ⟨a, b, c rfl⟩
      · exact .inr ⟨ts, hts, a, b, c rfl, d, e, f⟩
    · rcases h with ⟨a, -, -, -, -, d⟩ | ⟨ts, hts, a, -, -, b, -, -, -, c, d⟩
      · exact .inl ⟨a, d⟩
      · exact .inr ⟨ts, hts, a, b, c, d⟩

/-- `jne push` (position 5). -/
theorem q5 (hpc : t.st.st.2 = pcT 5) : Q t mem oc ∧
    oc.thread.st = goto t.st t.st.st.1 (if t.st.st.1.status.zf then pcT 7 else pcT 2) ∧
      oc.thread.views.coh = t.views.coh := by
  have hex := exec_jne5 _ (hS.at (by decide) (by decide) hpc)
  rw [addrOf_6] at hex
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, k2, k4⟩

/-- `testq %rax,%rax` (position 8). -/
theorem q8 (hpc : t.st.st.2 = pcT 8) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ md.regs = t.st.st.1.regs ∧
      (md.status.zf = true ↔ t.st.st.1.regs.get64 .rax = 0#64) ∧ oc.thread.st = goto t.st md (pcT 9) ∧
      oc.thread.views.coh = t.views.coh := by
  have hex := exec_test _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, ⟨i, k2⟩, k3, k4⟩ := spec_choose _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_choose_vw _ _ hex hs ho⟩,
    ({ t.st.st.1 with status := StatusFlags.from_result (t.st.st.1.regs.get64 .rax) ⟨false, i.val == 1, false⟩ } :
      MachineData), rfl, rfl, test_zf _ _, k2, k4⟩

/-- `je pop` (position 9). -/
theorem q9 (hpc : t.st.st.2 = pcT 9) : Q t mem oc ∧
    oc.thread.st = goto t.st t.st.st.1 (if t.st.st.1.status.zf then pcT 7 else pcT 10) ∧
      oc.thread.views.coh = t.views.coh := by
  have hex := exec_je _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, k2, k4⟩

/-- `movq (%rax),%rcx` (position 10). -/
theorem q10 (hpc : t.st.st.2 = pcT 10) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ md.regs.get64 .rax = t.st.st.1.regs.get64 .rax ∧
      md.regs.get64 .rbx = t.st.st.1.regs.get64 .rbx ∧ ∃ ts v, md.regs.get64 .rcx = BitVec.setWidth 64 v ∧
      oc.thread.st = goto t.st md (pcT 11) ∧ mem.read? (LinkL (t.st.st.1.regs.get64 .rax)) ts = some v ∧
      ∃ ν, TraceEv.read (LinkL (t.st.st.1.regs.get64 .rax)) ts v ν ∈ oc.log := by
  obtain ⟨g, hg, hex⟩ := exec_ldlink _ (hS.at (by decide) (by decide) hpc) (hS.d8 _)
  obtain ⟨ts, v, h1, h2, -, h4, h5, h6⟩ := spec_load _ _ hex hs ho
  exact ⟨⟨h4, h5, spec_load_vw _ _ hex hs ho⟩, g v, (hg v).1, (hg v).2.1, (hg v).2.2.1, ts, v, (hg v).2.2.2,
    h1, h2, h6⟩

/-- `jne pop` (position 12). -/
theorem q12 (hpc : t.st.st.2 = pcT 12) : Q t mem oc ∧
    oc.thread.st = goto t.st t.st.st.1 (if t.st.st.1.status.zf then pcT 13 else pcT 7) ∧
      oc.thread.views.coh = t.views.coh := by
  have hex := exec_jne12 _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, k2, k4⟩

/-- `movq %rax,%r12` (position 13). -/
theorem q13 (hpc : t.st.st.2 = pcT 13) : Q t mem oc ∧
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ md.regs.get64 .r12 = t.st.st.1.regs.get64 .rax ∧
      oc.thread.st = goto t.st md (pcT 14) ∧ oc.thread.views.coh = t.views.coh := by
  obtain ⟨md, h1, h2, hex⟩ := exec_mov13 _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, md, h1, h2, k2, k4⟩

/-- `jmp done` (position 14). -/
theorem q14 (hpc : t.st.st.2 = pcT 14) : Q t mem oc ∧
    oc.thread.st = goto t.st t.st.st.1 (pcT 16) ∧ oc.thread.views.coh = t.views.coh := by
  have hex := exec_jmp _ (hS.at (by decide) (by decide) hpc)
  obtain ⟨k1, k2, k3, k4⟩ := spec_done _ _ hex hs ho
  exact ⟨⟨k1, k3, spec_done_vw _ _ hex hs ho⟩, k2, k4⟩

end Steps

/-! ## The promise-agnostic thread invariant -/

/-- **The promise-agnostic per-thread invariant**: `Static` and a pc in
`tPcs`. -/
structure SInv (s : isa.State) : Prop where
  st : Static s
  pc : ∃ i ∈ tPcs, s.st.2 = pcT i

omit hv in
theorem SInv.goto {s : isa.State} (h : Static s) {md : MachineData} (hd : md.dmem = s.st.1.dmem) {j : Nat}
    (hj : j ∈ tPcs) : SInv (TermX64Treiber2Trees.goto s md (pcT j)) :=
  ⟨h.goto md _ hd, j, hj, rfl⟩

/-- The position after the instruction at position `p` (`z`: `ZF`). -/
def nextPc (z : Bool) : Nat → Nat
  | 2 => 3 | 3 => 4 | 4 => 5 | 5 => if z then 7 else 2 | 7 => 8 | 8 => 9 | 9 => if z then 7 else 10
  | 10 => 11 | 11 => 12 | 12 => if z then 13 else 7 | 13 => 14 | _ => 16

/-- **One instruction step keeps `SInv`, moves to `nextPc` (positions whose
next position depends on a flag set by the step itself, `4`, `8` and `11`,
excepted: they move to `5`, `9` and `12`), and drops at most one promise**,
for any promise set and memory. -/
theorem step_sinv {t : Thread isa} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {oc : Outcome isa} (h : SInv t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 ∧
      ∀ p ∈ tPcs, t.st.st.2 = pcT p → oc.thread.st.st.2 = pcT (nextPc t.st.st.1.status.zf p) := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  have nx : ∀ j, oc.thread.st.st.2 = pcT j → j = nextPc t.st.st.1.status.zf i →
      ∀ p ∈ tPcs, t.st.st.2 = pcT p → oc.thread.st.st.2 = pcT (nextPc t.st.st.1.status.zf p) :=
    fun j hj e p hp hp' => by rw [← addrOf_inj hi hp (hpc.symm.trans hp'), ← e]; exact hj
  have hle : ∀ {a b : Nat}, a = b → a ≤ b + 1 := fun e => by omega
  have hz3 : ∀ (z : Bool) (a b : Nat), a ∈ tPcs → b ∈ tPcs →
      oc.thread.st = TermX64Treiber2Trees.goto t.st t.st.st.1 (if z then pcT a else pcT b) →
      oc.thread.st.st.2 = pcT (if z then a else b) ∧ SInv oc.thread.st := by
    intro z a b ha hb hst
    cases z
    · exact ⟨by rw [hst]; rfl, hst ▸ SInv.goto hS rfl hb⟩
    · exact ⟨by rw [hst]; rfl, hst ▸ SInv.goto hS rfl ha⟩
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, ts, v, -, hst, -⟩ := qld hS hs ho (.inl rfl) hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 3 (by rw [hst]) rfl⟩
  · obtain ⟨hst, hw⟩ := q3 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS rfl (by decide), hw.len, nx 4 (by rw [hst]) rfl⟩
  · obtain ⟨tr, old, md, hd, -, -, -, hst, -, -, hw⟩ := qcas hS hs ho (.inl ⟨rfl, rfl⟩) hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hw.len, nx 5 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, hst, -⟩ := q5 hS hs ho hpc
    obtain ⟨e, hI⟩ := hz3 _ 7 2 (by decide) (by decide) hst
    exact ⟨hI, hle (by rw [hp]), nx _ e (by simp only [nextPc])⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, ts, v, -, hst, -⟩ := qld hS hs ho (.inr rfl) hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 8 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, -, hst, -⟩ := q8 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 9 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, hst, -⟩ := q9 hS hs ho hpc
    obtain ⟨e, hI⟩ := hz3 _ 7 10 (by decide) (by decide) hst
    exact ⟨hI, hle (by rw [hp]), nx _ e (by simp only [nextPc])⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, -, ts, v, -, hst, -⟩ := q10 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 11 (by rw [hst]) rfl⟩
  · obtain ⟨tr, old, md, hd, -, -, -, hst, -, -, hw⟩ := qcas hS hs ho (.inr ⟨rfl, rfl⟩) hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hw.len, nx 12 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, hst, -⟩ := q12 hS hs ho hpc
    obtain ⟨e, hI⟩ := hz3 _ 13 7 (by decide) (by decide) hst
    exact ⟨hI, hle (by rw [hp]), nx _ e (by simp only [nextPc])⟩
  · obtain ⟨⟨-, hp, -⟩, md, hd, -, hst, -⟩ := q13 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS hd (by decide), hle (by rw [hp]), nx 14 (by rw [hst]) rfl⟩
  · obtain ⟨⟨-, hp, -⟩, hst, -⟩ := q14 hS hs ho hpc
    exact ⟨hst ▸ SInv.goto hS rfl (by decide), hle (by rw [hp]), nx 16 (by rw [hst]) rfl⟩
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {tid : Nat} {p q : Thread isa × Memory} (h : ThreadNP Arch.tso tid p q) (hp : SInv p.1.st) :
    SInv q.1.st :=
  ThreadNP.stateInv SInv (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {tid : Nat} {t : Thread isa} (h : SInv t.st) : DropBounded Arch.tso 1 tid t :=
  dropBounded_of_stateInv SInv (fun h hs ho => ⟨(step_sinv h hs ho).1, (step_sinv h hs ho).2.1⟩) h

/-! ## `SInv` is a `TsoCertInv` -/

/-- Close `tree.NoNT Arch.tso ∧ tree.OneWrite` for a concrete cell tree. -/
local macro "treeok" : tactic => `(tactic|
  exact ⟨by simp [EvTree.NoNT, Arch.storeKind, Arch.tso, Arch.rmwKind, RmwKind.storeKind],
    by simp [EvTree.OneWrite, EvTree.NoWrite]⟩)

omit layout hv in
/-- A halted start thread has no tree (`NoStuck.stepOne_none_exec`, which
lives in `LiveNoStuckX64.lean`). -/
private theorem stepOne_none_exec {s : isa.State} {A : Arch} {tid : Nat} {mem : Memory}
    (h : stepOne A (Thread.init s) tid mem = none) {tree : EvTree isa.State} (hex : isa.exec s = some tree) : False := by
  unfold stepOne at h
  rw [show (Thread.init s).st = s from rfl, hex] at h
  cases h

/-- Every cell of the worker makes no non-temporal store and at most one
write. -/
theorem x64t2_tree {s : isa.State} (hS : SInv s) {tree : EvTree isa.State} (hex : isa.exec s = some tree) :
    tree.NoNT Arch.tso ∧ tree.OneWrite := by
  obtain ⟨hSt, p, hpp, hpc⟩ := hS
  simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, he⟩ := exec_ldtop _ (.inl rfl) (hSt.at (by decide) (by decide) hpc) (hSt.d8 _)
    rw [he] at hex; cases hex; treeok
  · rw [exec_stlink _ (hSt.at (by decide) (by decide) hpc) (hSt.d8 _)] at hex; cases hex; treeok
  · obtain ⟨g, -, he⟩ := exec_cas _ (.inl ⟨rfl, rfl⟩) (hSt.at (by decide) (by decide) hpc) (hSt.d8 _)
    rw [he] at hex; cases hex; treeok
  · rw [exec_jne5 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · obtain ⟨g, -, he⟩ := exec_ldtop _ (.inr rfl) (hSt.at (by decide) (by decide) hpc) (hSt.d8 _)
    rw [he] at hex; cases hex; treeok
  · rw [exec_test _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · rw [exec_je _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · obtain ⟨g, -, he⟩ := exec_ldlink _ (hSt.at (by decide) (by decide) hpc) (hSt.d8 _)
    rw [he] at hex; cases hex; treeok
  · obtain ⟨g, -, he⟩ := exec_cas _ (.inr ⟨rfl, rfl⟩) (hSt.at (by decide) (by decide) hpc) (hSt.d8 _)
    rw [he] at hex; cases hex; treeok
  · rw [exec_jne12 _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · obtain ⟨md, -, -, he⟩ := exec_mov13 _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · exact (stepOne_none_exec (stepOne_end (t := Thread.init s) hSt hpc Arch.tso 0
      (Config.init ([] : List isa.State) []).mem) hex).elim

/-- **The worker's `SInv` is a `TsoCertInv`.** -/
theorem x64t2_tsoCertInv : TsoCertInv isa SInv :=
  ⟨fun _ hS _ hex => (x64t2_tree hS hex).1, fun _ hS _ hex => (x64t2_tree hS hex).2,
    fun hS hs ho => (step_sinv hS hs ho).1⟩

end Kraken.Promising.Live.TermX64Treiber2Step
