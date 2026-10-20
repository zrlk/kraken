/-
**Stage 3: the event trees of the AArch64 SWP
spinlock workers** `swpWorker` (`spinlock_swp2.kl`: `SWPA` lock, `STLR`
unlock) and `swplWorker` (`spinlock_swpl2.kl`: `SWPA` lock, `SWPL` unlock),
on valid layouts.

The two programs differ only at position 13, the release:
```
 0 worker:              8   b try
 1   mov w3, #1         9 cs:
 2 try:                10   ldr w5, [x1]
 3   swpa w3, w2, [x0] 11   add w5, w5, #1
 4   cbz w2, cs        12   str w5, [x1]
 5 spin:               13   stlr wzr, [x0]   |   swpl wzr, w2, [x0]
 6   ldr w2, [x0]      14   b done
 7   cbnz w2, spin     15 done:
```
`SwpCode P` collects what the liveness proof needs of a program `P` of this
shape: the cell trees at the pc positions `swPcs` and their distinct
addresses; the release (`RelTree`) is a release store of `0` or an RMW that
always writes `0`. `swpCode` is `SwpCode swpWorker`, from the existing cell
trees `SLR/SwpTrees.lean`; `swplCode` is `SwpCode swplWorker`, from the cell
trees below (the `SwpTrees.lean` recipe).
-/
import Kraken.Promising.SLR.SwpTrees
import Kraken.Promising.SLR.EnvG.SwplLockSmoke
import Kraken.Promising.LiveSpinCasTrees

namespace Kraken.Promising.Live.SpinSwpTrees

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)
open Kraken.Promising.SLR.SwpTrees (goto)
open Kraken.Promising.Live.SpinCasTrees (isInstr)

variable [layout : _root_.Layout]

/-! ## The shape -/

/-- The context of a cell of program `P` (as `SLR.SwpTrees.At`). -/
structure AtG (P : Program) (st : State) (i : Nat) : Prop where
  exe : st.exe = layout P
  decls : st.decls = {}
  pc : st.st.2 = (layout P).addrOf i
  ne : (st.st.2 == st.endPc) = false

/-- The positions a worker's pc takes (each label at the address of the next
instruction; 16 is the end of the text). -/
def swPcs : List Nat := [1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 16]

/-- The release at position 13: a release store of `0`, or an RMW that
always writes `0` (the old value into `X2`). -/
def RelTree (st : State) (l : BitVec 64) (pc : Int64) : Prop :=
  isa.exec st = some (.store .rel false ⟨l, 4⟩ 0#128 fun _ => .done (goto st st.st.1 pc)) ∨
  ∃ k, isa.exec st = some (.rmw k false ⟨l, 4⟩ (fun _ => some 0#128) fun v => .done (goto st
    { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } pc))

/-- **What the liveness proof needs of an SWP-spinlock program `P`.** -/
structure SwpCode (P : Program) : Prop where
  a0 : (layout P).addrOf 0 = (layout P).addrOf 1
  a2 : (layout P).addrOf 2 = (layout P).addrOf 3
  a5 : (layout P).addrOf 5 = (layout P).addrOf 6
  a9 : (layout P).addrOf 9 = (layout P).addrOf 10
  inj : ∀ {i j : Nat}, i ∈ swPcs → j ∈ swPcs → (layout P).addrOf i = (layout P).addrOf j → i = j
  mov : ∀ st, AtG P st 1 → isa.exec st = some (.done (goto st
    { st.st.1 with regs := st.st.1.regs.setXReg .X3 1#64 } ((layout P).addrOf 3)))
  swpa : ∀ st (l : BitVec 64), AtG P st 3 → st.st.1.regs.X0.toBitVec = l → Mem.loadInt st.st.1.dmem l 4 = none →
    isa.exec st = some (.rmw .acq false ⟨l, 4⟩
      (fun _ => some (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec)))
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout P).addrOf 4)))
  cbz : ∀ st, AtG P st 4 → isa.exec st = some (.done (goto st st.st.1
    (if BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 then (layout P).addrOf 10 else (layout P).addrOf 6)))
  ldr : ∀ st (l : BitVec 64), AtG P st 6 → st.st.1.regs.X0.toBitVec = l → Mem.loadInt st.st.1.dmem l 4 = none →
    isa.exec st = some (.load .plain false ⟨l, 4⟩ fun v => .done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
      ((layout P).addrOf 7)))
  cbnz : ∀ st, AtG P st 7 → isa.exec st = some (.done (goto st st.st.1
    (if BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 then (layout P).addrOf 8 else (layout P).addrOf 6)))
  btry : ∀ st, AtG P st 8 → isa.exec st = some (.done (goto st st.st.1 ((layout P).addrOf 3)))
  ldrc : ∀ st (c : BitVec 64), AtG P st 10 → st.st.1.regs.X1.toBitVec = c → Mem.loadInt st.st.1.dmem c 4 = none →
    isa.exec st = some (.load .plain false ⟨c, 4⟩ fun v => .done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
      ((layout P).addrOf 11)))
  add : ∀ st, AtG P st 11 → isa.exec st = some (.done (goto st
    { st.st.1 with
      regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
    ((layout P).addrOf 12)))
  strc : ∀ st (c : BitVec 64), AtG P st 12 → st.st.1.regs.X1.toBitVec = c → Mem.loadInt st.st.1.dmem c 4 = none →
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X5.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout P).addrOf 13)))
  rel : ∀ st (l : BitVec 64), AtG P st 13 → st.st.1.regs.X0.toBitVec = l → Mem.loadInt st.st.1.dmem l 4 = none →
    RelTree st l ((layout P).addrOf 14)
  bdone : ∀ st, AtG P st 14 → isa.exec st = some (.done (goto st st.st.1 ((layout P).addrOf 16)))

/-! ## Distinct addresses, generically -/

private theorem layout_getElem (p : Program) (i : Nat) :
    (layout p).2[i]? = (p[i]?).map (fun d => (d, Kraken.Layout.size Directive i)) := by
  rw [Layout.apply_snd, Layout.frag_getElem?, Nat.zero_add]

/-- The address past an instruction differs from every address at or before it
(`SLR.A64Trees.addrOf_ne_succ` at `SpinCasTrees.isInstr`). -/
theorem addrOf_ne_succ (P : Program) [Executable.ValidLayout (layout P)] {k n : Nat} (hk : k ≤ n)
    (h : P[n]?.map isInstr = some true) : (layout P).addrOf k ≠ (layout P).addrOf (n + 1) :=
  SLR.A64Trees.addrOf_ne_succ P isInstr (fun _ => rfl) hk h

/-- **Distinct addresses from a canonical representative**: positions `ps`
whose representatives (`canon`, at the same address) are increasing and each
preceded by an instruction have distinct addresses
(`SLR.A64Trees.addrOf_inj_gen` at `SpinCasTrees.isInstr`). -/
theorem addrOf_inj_gen (P : Program) [Executable.ValidLayout (layout P)] (ps : List Nat) (canon : Nat → Nat)
    (hcan : ∀ i ∈ ps, (layout P).addrOf (canon i) = (layout P).addrOf i)
    (hc : ∀ i ∈ ps, ∀ j ∈ ps, i < j → canon i < canon j ∧ 1 ≤ canon j ∧ P[canon j - 1]?.map isInstr = some true)
    {i j : Nat} (hi : i ∈ ps) (hj : j ∈ ps) (h : (layout P).addrOf i = (layout P).addrOf j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen P isInstr (fun _ => rfl) ps canon hcan hc hi hj h

/-- The representative of a pc position: the label before it. -/
def canon (i : Nat) : Nat :=
  if i = 3 then 2 else if i = 6 then 5 else if i = 10 then 9 else if i = 16 then 15 else i

/-! ## `swpWorker` -/

section Swp

variable [hv : Executable.ValidLayout (layout swpWorker)]

theorem swp_lbl (i : Nat) (l : Label) (h : swpWorker[i]? = some (Directive.label l)) :
    (layout swpWorker).addrOf i = (layout swpWorker).addrOf (i + 1) :=
  (SLR.SwpTrees.addrOf_label h).symm

theorem swp_addrOf_canon (i : Nat) (_ : i ∈ swPcs) :
    (layout swpWorker).addrOf (canon i) = (layout swpWorker).addrOf i := by
  unfold canon
  split
  · subst_vars; exact swp_lbl 2 "try" rfl
  split
  · subst_vars; exact swp_lbl 5 "spin" rfl
  split
  · subst_vars; exact swp_lbl 9 "cs" rfl
  split
  · subst_vars; exact swp_lbl 15 "done" rfl
  rfl

omit hv in
theorem toAt {st : State} {i : Nat} (h : AtG swpWorker st i) : SLR.SwpTrees.At st i := ⟨h.exe, h.decls, h.pc, h.ne⟩

/-- **The SWPA/STLR worker has the shape.** -/
theorem swpCode : SwpCode swpWorker where
  a0 := swp_lbl 0 "worker" rfl
  a2 := swp_lbl 2 "try" rfl
  a5 := swp_lbl 5 "spin" rfl
  a9 := swp_lbl 9 "cs" rfl
  inj hi hj h := addrOf_inj_gen swpWorker swPcs canon swp_addrOf_canon (by decide) hi hj h
  mov st h := by rw [← swp_lbl 2 "try" rfl]; exact SLR.SwpTrees.exec_mov st (toAt h)
  swpa st l h hx hd := SLR.SwpTrees.exec_swpa st (toAt h) hx hd
  cbz st h := by rw [← swp_lbl 5 "spin" rfl]; exact SLR.SwpTrees.exec_cbz st (toAt h)
  ldr st l h hx hd := SLR.SwpTrees.exec_ldr_spin st (toAt h) hx hd
  cbnz st h := SLR.SwpTrees.exec_cbnz st (toAt h)
  btry st h := SLR.SwpTrees.exec_b_try st (toAt h)
  ldrc st c h hx hd := SLR.SwpTrees.exec_ldr_c st (toAt h) hx hd
  add st h := SLR.SwpTrees.exec_add st (toAt h)
  strc st c h hx hd := SLR.SwpTrees.exec_str_c st (toAt h) hx hd
  rel st l h hx hd := .inl (SLR.SwpTrees.exec_stlr st (toAt h) hx hd)
  bdone st h := SLR.SwpTrees.exec_b_done st (toAt h)

end Swp

/-! ## `swplWorker`: the cell trees -/

section Swpl

variable [hv : Executable.ValidLayout (layout swplWorker)]

omit hv in
theorem swpl_addrOf_step {i : Nat} (hi : i < swplWorker.length) :
    (layout swplWorker).addrOf (i + 1) = (layout swplWorker).addrOf i + .ofNat (Kraken.Layout.size Directive i) :=
  SLR.A64Trees.addrOf_step hi

theorem swpl_lbl (i : Nat) (l : Label) (hp : swplWorker[i]? = some (Directive.label l)) :
    (layout swplWorker).addrOf i = (layout swplWorker).addrOf (i + 1) :=
  (SLR.A64Trees.addrOf_label hp).symm

theorem swpl_label_try : (_root_.Executable.labels (layout swplWorker)).label "try" = (layout swplWorker).addrOf 3 := by
  rw [Program.label_addrOf_drop (i := 2) (by decide) (by decide) (by decide)]; exact swpl_lbl 2 "try" rfl

theorem swpl_label_spin : (_root_.Executable.labels (layout swplWorker)).label "spin" = (layout swplWorker).addrOf 6 := by
  rw [Program.label_addrOf_drop (i := 5) (by decide) (by decide) (by decide)]; exact swpl_lbl 5 "spin" rfl

theorem swpl_label_cs : (_root_.Executable.labels (layout swplWorker)).label "cs" = (layout swplWorker).addrOf 10 := by
  rw [Program.label_addrOf_drop (i := 9) (by decide) (by decide) (by decide)]; exact swpl_lbl 9 "cs" rfl

theorem swpl_label_done : (_root_.Executable.labels (layout swplWorker)).label "done" = (layout swplWorker).addrOf 16 := by
  rw [Program.label_addrOf_drop (i := 15) (by decide) (by decide) (by decide)]; exact swpl_lbl 15 "done" rfl

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : AtG swplWorker st i) (hi : i < swplWorker.length) :
    (layout swplWorker).addrOf (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact swpl_addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAt` and unfold it. -/
local macro "cell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i swplWorker [swplWorker] [swpl_label_try, swpl_label_spin, swpl_label_cs, swpl_label_done] [goto, $ts,*])

theorem swpl_mov (st : State) (h : AtG swplWorker st 1) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 1#64 } ((layout swplWorker).addrOf 3))) := by
  rw [← swpl_lbl 2 "try" rfl, next_pc h (by decide)]
  cell h 1 []

theorem swpl_swpa (st : State) (h : AtG swplWorker st 3) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.rmw .acq false ⟨l, 4⟩
      (fun _ => some (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec)))
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swplWorker).addrOf 4))) := by
  rw [next_pc h (by decide)]
  cell h 3 [hx0, hdm]

theorem swpl_cbz (st : State) (h : AtG swplWorker st 4) :
    isa.exec st = some (.done (goto st st.st.1
      (if BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 then (layout swplWorker).addrOf 10
        else (layout swplWorker).addrOf 6))) := by
  rw [← swpl_lbl 5 "spin" rfl, next_pc h (by decide)]
  by_cases hz : BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 <;> cell h 4 [hz]

theorem swpl_ldr (st : State) (h : AtG swplWorker st 6) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.load .plain false ⟨l, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swplWorker).addrOf 7))) := by
  rw [next_pc h (by decide)]
  cell h 6 [hx0, hdm]

theorem swpl_cbnz (st : State) (h : AtG swplWorker st 7) :
    isa.exec st = some (.done (goto st st.st.1
      (if BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 then (layout swplWorker).addrOf 8
        else (layout swplWorker).addrOf 6))) := by
  rw [next_pc h (by decide)]
  by_cases hz : BitVec.setWidth 32 st.st.1.regs.X2.toBitVec = 0#32 <;> cell h 7 [hz]

theorem swpl_btry (st : State) (h : AtG swplWorker st 8) :
    isa.exec st = some (.done (goto st st.st.1 ((layout swplWorker).addrOf 3))) := by
  cell h 8 []

theorem swpl_ldrc (st : State) (h : AtG swplWorker st 10) {c : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.load .plain false ⟨c, 4⟩
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swplWorker).addrOf 11))) := by
  rw [next_pc h (by decide)]
  cell h 10 [hx1, hdc]

theorem swpl_add (st : State) (h : AtG swplWorker st 11) :
    isa.exec st = some (.done (goto st
      { st.st.1 with
        regs := st.st.1.regs.setXReg .X5 (BitVec.setWidth 64 (st.st.1.regs.X5.toBitVec.take 32 + 1#32)) }
      ((layout swplWorker).addrOf 12))) := by
  rw [next_pc h (by decide)]
  cell h 11 []

theorem swpl_strc (st : State) (h : AtG swplWorker st 12) {c : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = c) (hdc : Mem.loadInt st.st.1.dmem c 4 = none) :
    isa.exec st = some (.store .plain false ⟨c, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X5.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout swplWorker).addrOf 13))) := by
  rw [next_pc h (by decide)]
  cell h 12 [hx1, hdc]

/-- `swpl wzr, w2, [x0]` (position 13): a release-only swap writing `0`. -/
theorem swpl_rel (st : State) (h : AtG swplWorker st 13) {l : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none) :
    isa.exec st = some (.rmw .rel false ⟨l, 4⟩ (fun _ => some 0#128)
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) }
        ((layout swplWorker).addrOf 14))) := by
  rw [next_pc h (by decide)]
  cell h 13 [hx0, hdm]

theorem swpl_bdone (st : State) (h : AtG swplWorker st 14) :
    isa.exec st = some (.done (goto st st.st.1 ((layout swplWorker).addrOf 16))) := by
  cell h 14 []

theorem swpl_addrOf_canon (i : Nat) (_ : i ∈ swPcs) :
    (layout swplWorker).addrOf (canon i) = (layout swplWorker).addrOf i := by
  unfold canon
  split
  · subst_vars; exact swpl_lbl 2 "try" rfl
  split
  · subst_vars; exact swpl_lbl 5 "spin" rfl
  split
  · subst_vars; exact swpl_lbl 9 "cs" rfl
  split
  · subst_vars; exact swpl_lbl 15 "done" rfl
  rfl

/-- **The SWPA/SWPL worker has the shape.** -/
theorem swplCode : SwpCode swplWorker where
  a0 := swpl_lbl 0 "worker" rfl
  a2 := swpl_lbl 2 "try" rfl
  a5 := swpl_lbl 5 "spin" rfl
  a9 := swpl_lbl 9 "cs" rfl
  inj hi hj h := addrOf_inj_gen swplWorker swPcs canon swpl_addrOf_canon (by decide) hi hj h
  mov := swpl_mov
  swpa st l h hx hd := swpl_swpa st h hx hd
  cbz := swpl_cbz
  ldr st l h hx hd := swpl_ldr st h hx hd
  cbnz := swpl_cbnz
  btry := swpl_btry
  ldrc st c h hx hd := swpl_ldrc st h hx hd
  add := swpl_add
  strc st c h hx hd := swpl_strc st h hx hd
  rel st l h hx hd := .inr ⟨_, swpl_rel st h hx hd⟩
  bdone := swpl_bdone

end Swpl

end Kraken.Promising.Live.SpinSwpTrees
