/-
The per-construct judgement on x64 (`isa`, TSO), for the code `scc` emits.

`scc`'s x64 emitter keeps every IR register in its own 8-byte frame slot
below `%rbp`, at `-8(k+1)(%rbp)` (`Scc/Emit/X64.lean`: `Frame.slotOff` and
`Frame.slot`, lines 112–119), loading operands into scratch registers and
storing results back (`ld`/`st`, lines 188–196; the operand forms `mem`,
`om`, `xm` of `Scc/Emit/X64Print.lean`, lines 195–204). Acquire loads and
release stores are plain `mov`s under TSO. The three constructs, for a
64-bit access at displacement `0` with register operands (the sequences are
copied here as data, `Spike.Lib` does not import the emitter):

* `store rel` (`emitInst`, `.store`, lines 325–333): `mov op(%rbp), %rcx;
  mov ov(%rbp), %rax; mov %rax, 0(%rcx)` (`storeSeq`);
* `load acq` (`.load`, lines 312–324): `mov op(%rbp), %rcx;
  mov 0(%rcx), %rax; mov %rax, od(%rbp)` (`loadSeq`);
* the checked `+` (`.addChk`, lines 299–303): `mov oa(%rbp), %rax;
  mov ob(%rbp), %rcx; add %rcx, %rax; jc .L<fn>.ovf; mov %rax, od(%rbp)`
  (`addSeq`), the abort label being the function's `ovf` stub (lines
  433–437).

Each instruction is a cell of its assembled size (the sizes are parameters,
the assembler's in a real layout, `Scc.Cert.Sizes`), so the `j`-th directive
of a sequence is the cell at `pc` plus the sizes of the ones before it
(`CodeAt`).

The fragments (`Slots`) are those of `Spike.Lib.A64` with `%rbp` for `sp`
and the frame below it: each placed source variable's slot holds a word
that represents it, slots are inside the frame and distinct, and every
address a source location represents is outside the frame, unmapped in
private memory and declared as an 8-byte location. With
`Scc.Sem.X64.privLoad` the private load (`Slots.privLoad`).

The theorems (`seg_store`, `seg_load`, `seg_add`) are `Seg` judgements from
the entry of each sequence to its exit, the checked `+` with two exits (the
fall-through, and the abort label with the source thread `OvfReady` and
unchanged). The code and the abort label's address are hypotheses.
-/
import Spike.Lib.Src
import Kraken.Promising.Lower.EventsX64Inf
import Kraken.Promising.Lower.CodeSegX64
import Scc.Sem.TargetX64

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-! ## Addresses -/

/-- The address of the slot at offset `o` from `bp` (as `o(%rbp)` computes
it). -/
def slotA (bp : BitVec 64) (o : Int64) : BitVec 64 := BitVec.ofInt 64 (bp.toInt + o.toInt)

/-- `o(%rbp)` (`mem .rbp o`). -/
abbrev mRbp (o : Int64) : AddrExpr := { base := some (.reg .rbp), idx := none, disp := .int64 o }

/-- `0(%rcx)` (`mem .rcx 0`). -/
abbrev mRcx : AddrExpr := { base := some (.reg .rcx), idx := none, disp := .int64 (Int64.ofInt 0) }

/-- `o(%rbp)` is the slot address (`eaddr_reg_disp`). -/
theorem eaddr_rbp (st : State) (sz : Nat) (o : Int64) :
    eaddr st sz (mRbp o) = slotA (st.st.1.regs.get64 .rbp) o :=
  eaddr_reg_disp st sz .rbp o

/-- `0(%rcx)` is `%rcx` (`eaddr_reg`). -/
theorem eaddr_rcx (st : State) (sz : Nat) : eaddr st sz mRcx = st.st.1.regs.get64 .rcx :=
  eaddr_reg st sz .rcx

/-! ## Private memory -/

/-- A load of the 8 bytes a store wrote reads them back. -/
theorem loadInt_storeInt8_same (m : DataMem) (a x : BitVec 64) :
    (m.storeInt a 8 x.toInt).loadInt a 8 = some (x.toNat : Int) := by
  rw [Mem.loadInt_storeInt _ _ _ _ (by decide), ofBytes_toBytes]
  congr 1
  simp only [Int.take, BitVec.toInt_eq_toNat_bmod]
  rw [show 8 * 8 = 64 from rfl, show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from rfl, Int.bmod_emod]
  exact Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)

/-- A store of 8 bytes leaves 8 bytes elsewhere alone. -/
theorem loadInt_storeInt8_disj (m : DataMem) (a b : BitVec 64) (v : Int) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hb : b.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.storeInt a 8 v).loadInt b 8 = m.loadInt b 8 := by
  have hs : (b - a).toNat = (b.toNat + (2 ^ 64 - a.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; congr 1; omega
  apply Mem.loadInt_storeInt_of_above <;> rw [hs]
  · rcases h with h | h
    · rw [show b.toNat + (2 ^ 64 - a.toNat) = (b.toNat - a.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rcases h with h | h
    · rw [show b.toNat + (2 ^ 64 - a.toNat) = (b.toNat - a.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-! ## Code segments -/

/-- The byte offset of cell `j` of a sized code segment: the sizes of the
cells before it. -/
def cellOff (cs : List (Directive × Nat)) (j : Nat) : Nat := ((cs.take j).map (·.2)).sum

/-- **The code segment `cs` at `pc`** of `st`'s executable: each directive
`d` of `cs` with its size `z` is the cell of `z` bytes at its address, `pc`
plus the sizes of the cells before it (`cellOff`), in any machine data. The
sizes are the assembler's (`Scc.Cert.Sizes`); the generator writes them
next to each block. -/
def CodeAt (st : State) (pc : Int64) (cs : List (Directive × Nat)) : Prop :=
  ∀ j d z, cs[j]? = some (d, z) → CellAt { st with st := (st.st.1, pc + Int64.ofNat (cellOff cs j)) } d z

/-- **A code segment from the layout**: a label-free run of sized cells that
Kraken's `codeAt` finds at `pc` (`cellAt_segment`). -/
theorem CodeAt.of_codeAt {st : State} {pc : Int64} {cs rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe)
    (hend : st.endPc = st.exe.1 + .ofNat (st.exe.2.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe pc = cs ++ rest) (hcs : ∀ c ∈ cs, c.1.isLabel = false) :
    CodeAt st pc cs :=
  fun _ _ _ hd => cellAt_segment hv hend h hcs hd st.st.1

theorem CodeAt.cell {st st' : State} {pc : Int64} {cs : List (Directive × Nat)} (h : CodeAt st pc cs) {j : Nat}
    {d : Directive} {z : Nat} (hd : cs[j]? = some (d, z)) (he : st'.exe = st.exe) (hn : st'.endPc = st.endPc)
    (hp : st'.st.2 = pc + Int64.ofNat (cellOff cs j)) : CellAt st' d z := by
  obtain ⟨hv, hne, hcode⟩ := h j d z hd
  refine ⟨he ▸ hv, ?_, ?_⟩
  · rw [hn, hp]; exact hne
  · rw [he, hp]; exact hcode

/-- The first cell of a code segment, at its pc. -/
theorem CodeAt.cell0 {st st' : State} {pc : Int64} {d : Directive} {z : Nat} {cs : List (Directive × Nat)}
    (h : CodeAt st pc ((d, z) :: cs)) (he : st'.exe = st.exe) (hn : st'.endPc = st.endPc) (hp : st'.st.2 = pc) :
    CellAt st' d z :=
  h.cell (j := 0) rfl he hn (by rw [hp, cellOff, List.take_zero]; simp)

theorem CodeAt.after {st : State} {pc : Int64} {cs : List (Directive × Nat)} (h : CodeAt st pc cs) (sz : Nat)
    (m : MachineData) : CodeAt (after st sz m) pc cs := by
  intro j d z hd
  obtain ⟨h1, h2, h3⟩ := h j d z hd
  exact ⟨h1, h2, h3⟩

theorem CodeAt.jump {st : State} {pc : Int64} {cs : List (Directive × Nat)} (h : CodeAt st pc cs)
    (m : MachineData) (q : Int64) : CodeAt (jumpTo st m q) pc cs := by
  intro j d z hd
  obtain ⟨h1, h2, h3⟩ := h j d z hd
  exact ⟨h1, h2, h3⟩

/-- Two byte offsets from `pc` are one. -/
theorem pc_add (pc : Int64) (a b : Nat) : pc + Int64.ofNat a + Int64.ofNat b = pc + Int64.ofNat (a + b) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add]

theorem toNat_setWidth128 (x : BitVec 64) : (x.setWidth 128).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide))]

/-! ## Frames and slots -/

/-- A thread's frame: its `%rbp` and size in bytes (the slots below
`%rbp`). -/
structure Frame where
  bp : BitVec 64
  size : Nat

/-- A well-formed frame: not wrapping below `0`. -/
structure Frame.OK (F : Frame) : Prop where
  fit : F.size ≤ F.bp.toNat

/-- A slot offset of the frame: 8-aligned, below `%rbp` and inside the
frame. -/
def Frame.Off (F : Frame) (o : Int64) : Prop := o.toInt % 8 = 0 ∧ -(F.size : Int) ≤ o.toInt ∧ o.toInt + 8 ≤ 0

theorem slotA_toNat {F : Frame} (hF : F.OK) {o : Int64} (ho : F.Off o) :
    ((slotA F.bp o).toNat : Int) = F.bp.toNat + o.toInt := by
  have := hF.fit
  have hb := F.bp.isLt
  obtain ⟨-, h0, h1⟩ := ho
  unfold slotA
  rw [BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem slot_sep {F : Frame} (hF : F.OK) {o o' : Int64} (ho : F.Off o) (ho' : F.Off o') (hne : o ≠ o') :
    (slotA F.bp o).toNat + 8 ≤ (slotA F.bp o').toNat ∨ (slotA F.bp o').toNat + 8 ≤ (slotA F.bp o).toNat := by
  have h1 := slotA_toNat hF ho
  have h2 := slotA_toNat hF ho'
  have hne' : o.toInt ≠ o'.toInt := fun h => hne (Int64.toInt_inj.mp h)
  obtain ⟨a0, -, -⟩ := ho
  obtain ⟨b0, -, -⟩ := ho'
  omega

theorem slot_fit {F : Frame} (hF : F.OK) {o : Int64} (ho : F.Off o) : (slotA F.bp o).toNat + 8 ≤ 2 ^ 64 := by
  have h1 := slotA_toNat hF ho
  have hb := F.bp.isLt
  obtain ⟨-, -, h2⟩ := ho
  omega

/-- A source word is an untagged location (the address word of an access). -/
def IsLoc (w : TermRun.Word) : Prop := ∃ l, w.val = .loc l 0

/-- **The slot fragment** of thread state `st` and source environment `env`,
for the frame `F` and the placement `slot`: see the module docstring. -/
structure Slots (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (st : State)
    (env : TermRun.Env) : Prop where
  ok : F.OK
  bp : st.st.1.regs.get64 .rbp = F.bp
  off : ∀ x o, slot x = some o → F.Off o
  inj : ∀ x y o, slot x = some o → slot y = some o → x = y
  rep : ∀ x o, slot x = some o → ∃ ty w j, TermRun.lookupE env x = some (ty, [w]) ∧
    Mem.loadInt st.st.1.dmem (slotA F.bp o) 8 = some j ∧ ValRep lbl w.val (BitVec.ofInt 64 j).toNat
  mapped : ∀ o, F.Off o → (Mem.loadInt st.st.1.dmem (slotA F.bp o) 8).isSome
  heap : ∀ w (a : BitVec 64), IsLoc w → ValRep lbl w.val a.toNat → Mem.loadInt st.st.1.dmem a 8 = none ∧
    st.decls.AgreesAt a 8 ∧ a.toNat + 8 ≤ 2 ^ 64 ∧ (a.toNat + 8 + F.size ≤ F.bp.toNat ∨ F.bp.toNat ≤ a.toNat)

/-- The slots are what the statement's `Place.slot` reads, through
`Scc.Sem.X64.privLoad`. -/
theorem Slots.privLoad {lbl : WeakMem.AllocLabel → Option Nat} {F : Frame} {slot : String → Option Int64}
    {st : State} {env : TermRun.Env} (h : Slots lbl F slot st env) {x : String} {o : Int64}
    (hx : slot x = some o) : ∃ ty w v, TermRun.lookupE env x = some (ty, [w]) ∧
      Scc.Sem.X64.privLoad st (slotA F.bp o) = some v ∧ ValRep lbl w.val v.toNat := by
  obtain ⟨ty, w, j, hl, hj, hv⟩ := h.rep x o hx
  exact ⟨ty, w, _, hl, by simp [Scc.Sem.X64.privLoad, hj], hv⟩

namespace Slots

variable {lbl : WeakMem.AllocLabel → Option Nat} {F : Frame} {slot : String → Option Int64} {st st' : State}
  {env : TermRun.Env}

/-- **Register framing**: a state with the same private memory, `%rbp` and
declarations has the same slots. -/
theorem regs (h : Slots lbl F slot st env) (hd : st'.st.1.dmem = st.st.1.dmem)
    (hbp : st'.st.1.regs.get64 .rbp = st.st.1.regs.get64 .rbp) (hdc : st'.decls = st.decls) :
    Slots lbl F slot st' env where
  ok := h.ok
  bp := hbp ▸ h.bp
  off := h.off
  inj := h.inj
  rep := hd ▸ h.rep
  mapped := hd ▸ h.mapped
  heap := hd ▸ hdc ▸ h.heap

/-- Binding a variable with no words (`unit`), unplaced. -/
theorem bind_unit (h : Slots lbl F slot st env) (u : String) :
    Slots lbl F (fun y => if y = u then none else slot y) st ((u, .unit, []) :: env) where
  ok := h.ok
  bp := h.bp
  off x o hx := by
    by_cases hxu : x = u
    · simp [hxu] at hx
    · simp only [hxu, ↓reduceIte] at hx; exact h.off x o hx
  inj x y o hx hy := by
    by_cases hxu : x = u
    · simp [hxu] at hx
    by_cases hyu : y = u
    · simp [hyu] at hy
    simp only [hxu, hyu, ↓reduceIte] at hx hy
    exact h.inj x y o hx hy
  rep x o hx := by
    by_cases hxu : x = u
    · simp [hxu] at hx
    · simp only [hxu, ↓reduceIte] at hx
      obtain ⟨ty, w, j, hl, hj, hv⟩ := h.rep x o hx
      have hne : (u == x) = false := by simp [Ne.symm hxu]
      exact ⟨ty, w, j, by simp [TermRun.lookupE, List.find?, hne] at hl ⊢; exact hl, hj, hv⟩
  mapped := h.mapped
  heap := h.heap

/-- **Storing a variable's word into a free slot**: after the private store
of `V` to slot `od`, the variable `x` bound first in the environment (to a
word `V` represents) is placed at `od`. -/
theorem store (h : Slots lbl F slot st env) {x : String} {od : Int64} (hod : F.Off od)
    (hfree : ∀ y, slot y = some od → y = x) {ty : Ty} {w : TermRun.Word} {V : BitVec 64}
    (hv : ValRep lbl w.val V.toNat) (hd : st'.st.1.dmem = Mem.storeInt st.st.1.dmem (slotA F.bp od) 8 V.toInt)
    (hbp : st'.st.1.regs.get64 .rbp = st.st.1.regs.get64 .rbp) (hdc : st'.decls = st.decls) :
    Slots lbl F (fun y => if y = x then some od else slot y) st' ((x, ty, [w]) :: env) where
  ok := h.ok
  bp := hbp ▸ h.bp
  off y o hy := by
    by_cases hyx : y = x
    · simp only [hyx, ↓reduceIte, Option.some.injEq] at hy; exact hy ▸ hod
    · simp only [hyx, ↓reduceIte] at hy; exact h.off y o hy
  inj y z o hy hz := by
    by_cases hyx : y = x <;> by_cases hzx : z = x
    · rw [hyx, hzx]
    · simp only [hyx, hzx, ↓reduceIte, Option.some.injEq] at hy hz
      subst hy; exact absurd (hfree z hz) hzx
    · simp only [hyx, hzx, ↓reduceIte, Option.some.injEq] at hy hz
      subst hz; exact absurd (hfree y hy) hyx
    · simp only [hyx, hzx, ↓reduceIte] at hy hz; exact h.inj y z o hy hz
  rep y o hy := by
    rw [hd]
    by_cases hyx : y = x
    · simp only [hyx, ↓reduceIte, Option.some.injEq] at hy
      subst hy hyx
      refine ⟨ty, w, V.toNat, by simp [TermRun.lookupE], loadInt_storeInt8_same _ _ _, ?_⟩
      simpa using hv
    · simp only [hyx, ↓reduceIte] at hy
      obtain ⟨ty', w', j, hl, hj, hv'⟩ := h.rep y o hy
      have hne : (x == y) = false := by simp [Ne.symm hyx]
      have hoo : od ≠ o := by rintro rfl; exact hyx (hfree y hy)
      refine ⟨ty', w', j, by simp [TermRun.lookupE, List.find?, hne] at hl ⊢; exact hl, ?_, hv'⟩
      rw [loadInt_storeInt8_disj _ _ _ _ (slot_fit h.ok hod) (slot_fit h.ok (h.off y o hy))
        (slot_sep h.ok hod (h.off y o hy) hoo)]
      exact hj
  mapped o ho := by
    rw [hd]
    by_cases hoo : od = o
    · subst hoo; rw [loadInt_storeInt8_same]; rfl
    · rw [loadInt_storeInt8_disj _ _ _ _ (slot_fit h.ok hod) (slot_fit h.ok ho) (slot_sep h.ok hod ho hoo)]
      exact h.mapped o ho
  heap w a hl hv := by
    obtain ⟨h1, h2, h3, h4⟩ := h.heap w a hl hv
    refine ⟨?_, hdc ▸ h2, h3, h4⟩
    rw [hd, loadInt_storeInt8_disj _ _ _ _ (slot_fit h.ok hod) h3 ?_]
    · exact h1
    · have := slotA_toNat h.ok hod
      obtain ⟨-, h0, h5⟩ := hod
      omega

end Slots

/-! ## The emitted sequences -/

/-- `mov o(%rbp), %r` (`ld fr (.reg x) r`). -/
abbrev dLd (r : Reg64) (o : Int64) : Directive := op64 (.mov (.reg (.low r .W64)) (.mem (mRbp o)))

/-- `mov %r, o(%rbp)` (`st fr r d`). -/
abbrev dSt (r : Reg64) (o : Int64) : Directive := op64 (.mov (.mem (mRbp o)) (.reg (.low r .W64)))

/-- `mov 0(%rcx), %rax` (the 64-bit `.load`). -/
abbrev dLdH : Directive := op64 (.mov (.reg (.low .rax .W64)) (.mem mRcx))

/-- `mov %rax, 0(%rcx)` (the 64-bit `.store`). -/
abbrev dStH : Directive := op64 (.mov (.mem mRcx) (.reg (.low .rax .W64)))

/-- `add %rcx, %rax` (`.addChk`). -/
abbrev dAdd : Directive := op64 (.add (.reg (.low .rax .W64)) (.reg (.low .rcx .W64)))

/-- `jc L` (`.addChk`: carry set, the unsigned sum does not fit). -/
abbrev dJc (L : String) : Directive := op64 (.jcc .c L)

/-- `store rel` of the variable in slot `ov` through the pointer in slot
`op`, the cells of sizes `z0`, `z1`, `z2`. -/
def storeSeq (ov op : Int64) (z0 z1 z2 : Nat) : List (Directive × Nat) :=
  [(dLd .rcx op, z0), (dLd .rax ov, z1), (dStH, z2)]

/-- `load acq` through the pointer in slot `op` into slot `od`, the cells
of sizes `z0`, `z1`, `z2`. -/
def loadSeq (op od : Int64) (z0 z1 z2 : Nat) : List (Directive × Nat) :=
  [(dLd .rcx op, z0), (dLdH, z1), (dSt .rax od, z2)]

/-- The checked `+` of slots `oa` and `ob` into slot `od`, with the abort
edge to `L`, the cells of sizes `z0` … `z4`. -/
def addSeq (oa ob : Int64) (L : String) (od : Int64) (z0 z1 z2 z3 z4 : Nat) : List (Directive × Nat) :=
  [(dLd .rax oa, z0), (dLd .rcx ob, z1), (dAdd, z2), (dJc L, z3), (dSt .rax od, z4)]

/-! ## One instruction on slots -/

section Rows

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {F : Frame}
  {slot : String → Option Int64}

/-- **A slot load** `mov o(%rbp), %r` of a placed variable: no event, the
source stutters, `%r` holds a word representing the variable. -/
theorem out_ld {X : Frag isa} {s : State} {c : Ctl} {env : TermRun.Env} {r : Reg64} {o : Int64}
    {x : String} {z : Nat} (hc : CellAt s (dLd r o) z) (hS : Slots lbl F slot s env) (hx : slot x = some o)
    (hX : ∀ ty w j, TermRun.lookupE env x = some (ty, [w]) → ValRep lbl w.val (BitVec.ofInt 64 j).toNat →
      X (after s z { s.st.1 with regs := s.st.1.regs.set (.low r .W64) (BitVec.ofInt 64 j) }) c) :
    Out p lbl ms X s c := by
  obtain ⟨ty, w, j, hl, hj, hv⟩ := hS.rep x o hx
  exact .silent _ c (exec_load_mapped hc (by rw [eaddr_rbp, hS.bp]) hj) (.refl c) (hX ty w j hl hv)

/-- **A slot store** `mov %r, o(%rbp)` into the frame: no event, the source
stutters. -/
theorem out_st {X : Frag isa} {s : State} {c : Ctl} {env : TermRun.Env} {r : Reg64} {od : Int64}
    {z : Nat} (hc : CellAt s (dSt r od) z) (hS : Slots lbl F slot s env) (hod : F.Off od)
    (hX : X (after s z { s.st.1 with dmem := (Mem.storeInt s.st.1.dmem (slotA F.bp od) 8
      (s.st.1.regs.get (.low r .W64)).toInt) }) c) :
    Out p lbl ms X s c := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hS.mapped od hod)
  exact .silent _ c (exec_store_mapped hc (by rw [eaddr_rbp, hS.bp]) hj) (.refl c) hX

end Rows

/-! ## `store rel` -/

section Store

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of `store rel`. -/
def storeTerm (u pv vv : String) (e : Expr) : Expr := .let_ u (.store true (.var pv) (.var vv) none) e

/-- **Entry of `store rel`.** -/
def StoreIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (u pv vv : String) (e : Expr) (ov op : Int64) (z0 z1 z2 : Nat) (env0 : TermRun.Env) : Frag isa := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (storeSeq ov op z0 z1 z2) ∧ c = ⟨storeTerm u pv vv e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Exit of `store rel`**: the source at `e` with `u` bound to unit. -/
def StoreOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (u : String) (e : Expr) (ov op : Int64) (z0 z1 z2 : Nat) (env0 : TermRun.Env) : Frag isa := fun s c =>
  s.st.2 = pc + Int64.ofNat (z0 + z1 + z2) ∧ CodeAt s pc (storeSeq ov op z0 z1 z2) ∧
    c = ⟨e, (u, .unit, []) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = u then none else slot y) s ((u, .unit, []) :: env0)

/-- **`store rel` simulates the source's release store**: two slot loads
(the source stutters), then the plain `mov` to the heap, the source's
store. -/
theorem seg_store {pc : Int64} {u pv vv : String} {e : Expr} {ov op : Int64} {z0 z1 z2 : Nat}
    {env0 : TermRun.Env}
    (hv : slot vv = some ov) (hp : slot pv = some op) {tp tv : Ty} {wp wv : TermRun.Word}
    (hlp : TermRun.lookupE env0 pv = some (tp, [wp])) (hlv : TermRun.lookupE env0 vv = some (tv, [wv]))
    (hloc : IsLoc wp) :
    Seg p lbl ms (StoreIn lbl F slot pc u pv vv e ov op z0 z1 z2 env0)
      (StoreOut lbl F slot pc u e ov op z0 z1 z2 env0) := by
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0) ∧
      CodeAt s pc (storeSeq ov op z0 z1 z2) ∧
      c = ⟨storeTerm u pv vv e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl wp.val (s.st.1.regs.get64 .rcx).toNat) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0 + z1) ∧
      CodeAt s pc (storeSeq ov op z0 z1 z2) ∧
      c = ⟨storeTerm u pv vv e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl wp.val (s.st.1.regs.get64 .rcx).toNat ∧
      ValRep lbl wv.val (s.st.1.regs.get (.low .rax .W64)).toNat) (Seg.step ?_) (Seg.step ?_))
  · rintro s c ⟨hpc, hcode, rfl, hS⟩
    refine out_ld (hcode.cell0 rfl rfl hpc) hS hp
      fun ty w j hl hval => ?_
    rw [hlp] at hl
    cases hl
    exact ⟨by simp [hpc], hcode.after _ _, rfl, hS.regs rfl (by simp) rfl, by simpa using hval⟩
  · rintro s c ⟨hpc, hcode, rfl, hS, hx⟩
    refine out_ld (hcode.cell (j := 1) rfl rfl rfl
      (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])) hS hv fun ty w j hl hval => ?_
    rw [hlv] at hl
    cases hl
    exact ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, rfl,
      hS.regs rfl (by simp) rfl, by simpa using hx, by simpa using hval⟩
  · rintro s c ⟨hpc, hcode, rfl, hS, hx, hy⟩
    have hc := hcode.cell (j := 2) rfl rfl rfl (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])
    obtain ⟨hdm, hag, -, -⟩ := hS.heap wp _ hloc hx
    refine .store .plain _ _ _ u (.var pv) (.var vv) e tp tv wp wv (exec_store_agrees hc (eaddr_rcx _ _) hdm hag)
      rfl (by simpa [TermRun.evalAt] using hlp) hx (by simpa [TermRun.evalAt] using hlv)
      (by rw [toNat_setWidth128]; exact hy) ?_ hloc
    exact ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, rfl,
      (hS.regs (st' := after s z2 s.st.1) rfl rfl rfl).bind_unit u⟩

end Store

/-! ## `load acq` -/

section Load

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of `load acq`. -/
def loadTerm (x pv : String) (e : Expr) : Expr := .let_ x (.load true (.var pv)) e

/-- **Entry of `load acq`.** -/
def LoadIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x pv : String) (e : Expr) (op od : Int64) (z0 z1 z2 : Nat) (env0 : TermRun.Env) : Frag isa := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (loadSeq op od z0 z1 z2) ∧ c = ⟨loadTerm x pv e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Exit of `load acq`**: the source at `e` with `x` bound to the word
read, placed at slot `od`. -/
def LoadOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x : String) (e : Expr) (op od : Int64) (z0 z1 z2 : Nat) (env0 : TermRun.Env) : Frag isa := fun s c =>
  s.st.2 = pc + Int64.ofNat (z0 + z1 + z2) ∧ CodeAt s pc (loadSeq op od z0 z1 z2) ∧
    ∃ ty w, c = ⟨e, (x, ty, [w]) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = x then some od else slot y) s ((x, ty, [w]) :: env0)

/-- **`load acq` simulates the source's acquire load**: a slot load (the
source stutters), the plain `mov` from the heap (the source's load, for
every value read), a slot store of the result (the source stutters). -/
theorem seg_load {pc : Int64} {x pv : String} {e : Expr} {op od : Int64} {z0 z1 z2 : Nat} {env0 : TermRun.Env}
    (hp : slot pv = some op) {tp : Ty} {wp : TermRun.Word} (hlp : TermRun.lookupE env0 pv = some (tp, [wp]))
    (hloc : IsLoc wp) (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (LoadIn lbl F slot pc x pv e op od z0 z1 z2 env0)
      (LoadOut lbl F slot pc x e op od z0 z1 z2 env0) := by
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0) ∧
      CodeAt s pc (loadSeq op od z0 z1 z2) ∧
      c = ⟨loadTerm x pv e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl wp.val (s.st.1.regs.get64 .rcx).toNat) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0 + z1) ∧
      CodeAt s pc (loadSeq op od z0 z1 z2) ∧
      ∃ ty w, c = ⟨e, (x, ty, [w]) :: env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl w.val (s.st.1.regs.get (.low .rax .W64)).toNat) (Seg.step ?_) (Seg.step ?_))
  · rintro s c ⟨hpc, hcode, rfl, hS⟩
    refine out_ld (hcode.cell0 rfl rfl hpc) hS hp
      fun ty w j hl hval => ?_
    rw [hlp] at hl
    cases hl
    exact ⟨by simp [hpc], hcode.after _ _, rfl, hS.regs rfl (by simp) rfl, by simpa using hval⟩
  · rintro s c ⟨hpc, hcode, rfl, hS, hx⟩
    have hc := hcode.cell (j := 1) rfl rfl rfl (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])
    obtain ⟨hdm, hag, -, -⟩ := hS.heap wp _ hloc hx
    refine .load .plain _ _ x (.var pv) e tp wp (exec_load_agrees hc (eaddr_rcx _ _) hdm hag) rfl
      (by simpa [TermRun.evalAt] using hlp) hx (fun v w' _ hval => ?_) hloc
    refine ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, loadTy tp, w', rfl,
      hS.regs rfl (by simp) rfl, ?_⟩
    rw [show ((s.st.1.regs.set (.low .rax .W64) (v.setWidth 64)).get (.low .rax .W64)) = v.setWidth 64 by simp]
    exact hval
  · rintro s c ⟨hpc, hcode, ty, w, rfl, hS, hx⟩
    refine out_st (hcode.cell (j := 2) rfl rfl rfl
      (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])) hS hod ?_
    exact ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, ty, w, rfl,
      hS.store hod hfree hx rfl rfl rfl⟩

end Load

/-! ## The checked `+` -/

section Add

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of the checked `+`. -/
def addTerm (x a b : String) (e : Expr) : Expr := .let_ x (.add (.var a) (.var b)) e

/-- **Entry of the checked `+`**: also the abort label `L` at `lpc`. -/
def AddIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x a b : String) (e : Expr) (oa ob : Int64) (L : String) (od lpc : Int64) (z0 z1 z2 z3 z4 : Nat)
    (env0 : TermRun.Env) :
    Frag isa := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧ labelAddr s L = lpc ∧
    c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Normal exit of the checked `+`**: the source at `e` with `x` bound to
the sum `w`, placed at slot `od`. -/
def AddOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x : String) (e : Expr) (oa ob : Int64) (L : String) (od lpc : Int64) (z0 z1 z2 z3 z4 : Nat)
    (env0 : TermRun.Env) (w : TermRun.Word) : Frag isa := fun s c =>
  s.st.2 = pc + Int64.ofNat (z0 + z1 + z2 + z3 + z4) ∧ CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧
    labelAddr s L = lpc ∧
    c = ⟨e, (x, .int, [w]) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = x then some od else slot y) s ((x, .int, [w]) :: env0)

/-- **Abort exit of the checked `+`**: at the abort label, the source
unchanged and about to overflow (`OvfReady`). -/
def AddAbort (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x a b : String) (e : Expr) (oa ob : Int64) (L : String) (od lpc : Int64) (z0 z1 z2 z3 z4 : Nat)
    (env0 : TermRun.Env) :
    Frag isa := fun s c =>
  s.st.2 = lpc ∧ CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧ c = ⟨addTerm x a b e, env0, none⟩ ∧ OvfReady c ∧
    Slots lbl F slot s env0

/-- **The checked `+` simulates the source's `+`, or aborts justifiably**:
two slot loads and the `add` (the source stutters); at `jc`, without carry
the source adds (one local step) and the slot store follows (the source
stutters); with carry the thread is at the abort label and the source
thread, unchanged, is `OvfReady`. The operands are numbers. -/
theorem seg_add {pc : Int64} {x a b : String} {e : Expr} {oa ob : Int64} {L : String} {od lpc : Int64}
    {z0 z1 z2 z3 z4 : Nat} {env0 : TermRun.Env} (ha : slot a = some oa) (hb : slot b = some ob) {ta tb : Ty}
    {wa wb : TermRun.Word}
    {n m : Nat} (hla : TermRun.lookupE env0 a = some (ta, [wa])) (hlb : TermRun.lookupE env0 b = some (tb, [wb]))
    (hna : wa.val = .num n) (hnb : wb.val = .num m) (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (AddIn lbl F slot pc x a b e oa ob L od lpc z0 z1 z2 z3 z4 env0)
      (fun s c => AddOut lbl F slot pc x e oa ob L od lpc z0 z1 z2 z3 z4 env0 (TermRun.addW wa wb) s c ∨
        AddAbort lbl F slot pc x a b e oa ob L od lpc z0 z1 z2 z3 z4 env0 s c) := by
  have hea : TermRun.evalAt env0 (.var a) = some (ta, [wa]) := by simpa [TermRun.evalAt] using hla
  have heb : TermRun.evalAt env0 (.var b) = some (tb, [wb]) := by simpa [TermRun.evalAt] using hlb
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0) ∧
      CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧ labelAddr s L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.get (.low .rax .W64)).toNat = n) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0 + z1) ∧
      CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧ labelAddr s L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.get (.low .rax .W64)).toNat = n ∧
      (s.st.1.regs.get (.low .rcx .W64)).toNat = m) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0 + z1 + z2) ∧
      CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧ labelAddr s L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.status.cf = true → 2 ^ 64 ≤ n + m) ∧
      (s.st.1.status.cf = false → (s.st.1.regs.get (.low .rax .W64)).toNat = n + m)) (Seg.step ?_)
    (Seg.seq_left (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat (z0 + z1 + z2 + z3) ∧
      CodeAt s pc (addSeq oa ob L od z0 z1 z2 z3 z4) ∧ labelAddr s L = lpc ∧
      c = ⟨e, (x, .int, [TermRun.addW wa wb]) :: env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.get (.low .rax .W64)).toNat = n + m) (Seg.step ?_) (Seg.step ?_))))
  · rintro s c ⟨hpc, hcode, hL, rfl, hS⟩
    refine out_ld (hcode.cell0 rfl rfl hpc) hS ha
      fun ty w j hl hval => ?_
    rw [hla] at hl
    cases hl
    rw [hna] at hval
    exact ⟨by simp [hpc], hcode.after _ _, hL, rfl, hS.regs rfl (by simp) rfl, by simpa using hval.2⟩
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, hx⟩
    refine out_ld (hcode.cell (j := 1) rfl rfl rfl
      (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])) hS hb fun ty w j hl hval => ?_
    rw [hlb] at hl
    cases hl
    rw [hnb] at hval
    exact ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, hL, rfl,
      hS.regs rfl (by simp) rfl, by simpa using hx, by simpa using hval.2⟩
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, hx, hy⟩
    have hc := hcode.cell (j := 2) rfl rfl rfl (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])
    refine .silent _ _ (exec_add_flags hc) (.refl _) ?_
    have hn : (s.st.1.regs.get (.low .rax .W64)).toNat < 2 ^ 64 := BitVec.isLt _
    have hm : (s.st.1.regs.get (.low .rcx .W64)).toNat < 2 ^ 64 := BitVec.isLt _
    refine ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, hL, rfl,
      hS.regs rfl (by simp) rfl, fun hcar => ?_, fun hcar => ?_⟩
    · simp only [addFlags_cf, decide_eq_true_eq] at hcar
      omega
    · simp only [addFlags_cf, decide_eq_false_iff_not, Nat.not_le] at hcar
      have hx' : s.st.1.regs.rax.toNat = n := by simpa using hx
      have hy' : s.st.1.regs.rcx.toNat = m := by simpa using hy
      have := s.st.1.regs.rax.toNat_lt
      have := s.st.1.regs.rcx.toNat_lt
      simp [BitVec.toNat_add]
      omega
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, hcar, hsum⟩
    have hc := hcode.cell (j := 3) rfl rfl rfl (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])
    cases hc' : s.st.1.status.cf
    · refine .silent _ _ (exec_jcc hc) (.single (localStep_add rfl hea heb)) (.inl ?_)
      have h9 := hsum hc'
      refine ⟨?_, hcode.jump _ _, hL, rfl, hS.regs rfl rfl rfl, by simpa using h9⟩
      simp only [CondCode.interp, hc', Bool.false_eq_true, ↓reduceIte, hpc]
      exact pc_add pc _ _
    · refine .silent _ _ (exec_jcc hc) (.refl _) (.inr ?_)
      refine ⟨?_, hcode.jump _ _, rfl, ⟨x, .var a, .var b, e, ta, tb, wa, wb, n, m, rfl, hea, heb, hna, hnb,
        hcar hc'⟩, hS.regs rfl rfl rfl⟩
      simp only [CondCode.interp, hc', ↓reduceIte, hL]
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, h9⟩
    refine out_st (hcode.cell (j := 4) rfl rfl rfl
      (by rw [hpc]; simp [cellOff, storeSeq, loadSeq, addSeq, Nat.add_assoc])) hS hod ?_
    have hv : ValRep lbl (TermRun.addW wa wb).val (s.st.1.regs.get (.low .rax .W64)).toNat := by
      have hlt : (s.st.1.regs.get (.low .rax .W64)).toNat < 2 ^ 64 := BitVec.isLt _
      have h9' : s.st.1.regs.rax.toNat = n + m := by simpa using h9
      have := s.st.1.regs.rax.toNat_lt
      simp [TermRun.addW, hna, hnb, TermRun.cst, Promises.TVal.mk0, ValRep, h9']
      omega
    exact ⟨by simp only [after, hpc] <;> exact pc_add pc _ _, hcode.after _ _, hL, rfl,
      hS.store hod hfree hv rfl rfl rfl⟩

end Add

end Spike.Lib.X64
