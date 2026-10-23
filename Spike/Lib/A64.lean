/-
The per-construct judgement on AArch64 (`isaLSE2`), for the code `scc`
emits.

`scc`'s AArch64 emitter keeps every IR register in its own 8-byte frame slot
at `[sp, #8·i]` and computes in the scratch registers `x9`/`x10`
(`Scc/Emit/A64.lean`: `FnCtx.getReg`/`FnCtx.setReg`, lines 373–378, over
`ldrOff`/`strOff`, lines 183–194). The three constructs, for a 64-bit
access at displacement `0` with register operands (the sequences are copied
here as data, `Spike.Lib` does not import the emitter):

* `store rel` (`FromIR.inst`, `.store`, lines 540–551; `FnCtx.getAddr`,
  lines 386–388; `storeRel`, lines 235–236): `ldr x9, [sp, #ov]; ldr x10, [sp, #op]; stlr x9, [x10]`
  (`storeSeq`);
* `load acq` (`.load`, lines 531–539): `ldr x10, [sp, #op];
  ldar x9, [x10]; str x9, [sp, #od]` (`loadSeq`);
* the checked `+` (`.addChk`, lines 522–524; `addChecked`, lines 148–149):
  `ldr x9, [sp, #oa]; ldr x10, [sp, #ob]; adds x9, x9, x10;
  b.cs <abort_overflow>; str x9, [sp, #od]` (`addSeq`), the abort label
  being the function's `abort_overflow` stub (`abortStub`, lines 684–686,
  placed at line 708).

The fragments (`Slots`): the thread's frame (`Frame`: `sp` and the frame
size) is 16-aligned and mapped in private memory, each placed source
variable's slot holds a word that represents it (`ValRep`), slots are
inside the frame and distinct, and every heap or static address a source
location represents is outside the frame, unmapped in private memory and
declared as an 8-byte location (so the accesses `stlr`/`ldar` make are
single shared events). This is the `env_rep` component of
`Scc.Sem.Components` for `Place.slot`, with `Scc.Sem.A64.privLoad` the
private load (`Slots.privLoad`).

The theorems (`seg_store`, `seg_load`, `seg_add`) are `Seg` judgements from
the entry of each sequence to its exit, the checked `+` with two exits: the
fall-through, and the abort label with the source thread `OvfReady` and
unchanged (the input of `abortJustified_overflow`).

The code is a hypothesis (`CodeAt`: each directive of the sequence is the
cell at its address), as is the abort label's address.
-/
import Spike.Lib.Src
import Kraken.Promising.Lower.EventsA64Inf
import Kraken.Promising.Lower.CodeSegA64
import Scc.Sem.TargetA64

namespace Spike.Lib.A64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

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

/-- **The code segment `ds` at `pc`** of `st`'s executable: each directive of
`ds` is the 4-byte cell at its address (any machine data). -/
def CodeAt (st : State) (pc : Int64) (ds : List Directive) : Prop :=
  ∀ j d, ds[j]? = some d → CellAt { st with st := (st.st.1, pc + Int64.ofNat (4 * j)) } d 4

/-- **A code segment from the layout**: a label-free run that Kraken's
`codeAt` finds at `pc`, each directive 4 bytes (`cellAt_segment4`). -/
theorem CodeAt.of_codeAt {st : State} {pc : Int64} {ds : List Directive} {rest : List (Directive × Nat)}
    (hv : Kraken.Executable.ValidLayout st.exe)
    (hend : st.endPc = st.exe.1 + .ofNat (st.exe.2.map (·.2)).sum)
    (h : Kraken.Executable.codeAt st.exe pc = ds.map (·, 4) ++ rest) (hds : ∀ d ∈ ds, d.isLabel = false) :
    CodeAt st pc ds :=
  fun _ _ hd => cellAt_segment4 hv hend h hds hd _

/-- A cell of a code segment, at a state with the same executable at the
cell's address. -/
theorem CodeAt.cell {st st' : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds) {j : Nat}
    {d : Directive} (hd : ds[j]? = some d) (he : st'.exe = st.exe) (hn : st'.endPc = st.endPc)
    (hp : st'.st.2 = pc + Int64.ofNat (4 * j)) : CellAt st' d 4 := by
  obtain ⟨hv, hne, hcode⟩ := h j d hd
  refine ⟨he ▸ hv, ?_, ?_⟩
  · rw [hn, hp]; exact hne
  · rw [he, hp]; exact hcode

/-- A step keeps the executable, hence the code segment. -/
theorem CodeAt.after {st : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds) (sz : Nat)
    (m : MachineData) : CodeAt (after st sz m) pc ds := by
  intro j d hd
  obtain ⟨h1, h2, h3⟩ := h j d hd
  exact ⟨h1, h2, h3⟩

/-- A jump keeps the code segment. -/
theorem CodeAt.jump {st : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds) (m : MachineData)
    (q : Int64) : CodeAt (jumpTo st m q) pc ds := by
  intro j d hd
  obtain ⟨h1, h2, h3⟩ := h j d hd
  exact ⟨h1, h2, h3⟩

/-! ## Frames and slots -/

/-- A thread's frame: its `sp` and size in bytes. -/
structure Frame where
  sp : BitVec 64
  size : Nat

/-- A well-formed frame: 16-aligned, not wrapping. -/
structure Frame.OK (F : Frame) : Prop where
  align : F.sp % 16#64 = 0#64
  fit : F.sp.toNat + F.size ≤ 2 ^ 64

/-- A slot offset of the frame: 8-aligned and inside it. -/
def Frame.Off (F : Frame) (o : Int64) : Prop := 0 ≤ o.toInt ∧ o.toInt % 8 = 0 ∧ o.toInt + 8 ≤ F.size

/-- The address of the slot at offset `o` (as `ldr`/`str` compute it). -/
def slotA (sp : BitVec 64) (o : Int64) : BitVec 64 := BitVec.ofInt 64 (sp.toInt + o.toInt)

theorem slotA_toNat {F : Frame} (hF : F.OK) {o : Int64} (ho : F.Off o) :
    (slotA F.sp o).toNat = F.sp.toNat + o.toInt.toNat := by
  have := hF.fit
  obtain ⟨h0, -, h1⟩ := ho
  unfold slotA
  rw [BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- Distinct slots do not overlap. -/
theorem slot_sep {F : Frame} (hF : F.OK) {o o' : Int64} (ho : F.Off o) (ho' : F.Off o') (hne : o ≠ o') :
    (slotA F.sp o).toNat + 8 ≤ (slotA F.sp o').toNat ∨ (slotA F.sp o').toNat + 8 ≤ (slotA F.sp o).toNat := by
  rw [slotA_toNat hF ho, slotA_toNat hF ho']
  have hne' : o.toInt ≠ o'.toInt := fun h => hne (Int64.toInt_inj.mp h)
  obtain ⟨a0, a1, -⟩ := ho
  obtain ⟨b0, b1, -⟩ := ho'
  omega

theorem slot_fit {F : Frame} (hF : F.OK) {o : Int64} (ho : F.Off o) : (slotA F.sp o).toNat + 8 ≤ 2 ^ 64 := by
  rw [slotA_toNat hF ho]
  have := hF.fit
  obtain ⟨h0, -, h1⟩ := ho
  omega

/-- A source word is an untagged location (the address word of an access). -/
def IsLoc (w : TermRun.Word) : Prop := ∃ l, w.val = .loc l 0

/-- **The slot fragment** of thread state `st` and source environment
`env`, for the frame `F` and the placement `slot` (variable ↦ slot offset):
see the module docstring. -/
structure Slots (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (st : State)
    (env : TermRun.Env) : Prop where
  ok : F.OK
  sp : st.st.1.regs.SP.toBitVec = F.sp
  off : ∀ x o, slot x = some o → F.Off o
  inj : ∀ x y o, slot x = some o → slot y = some o → x = y
  rep : ∀ x o, slot x = some o → ∃ ty w j, TermRun.lookupE env x = some (ty, [w]) ∧
    Mem.loadInt st.st.1.dmem (slotA F.sp o) 8 = some j ∧ ValRep lbl w.val (BitVec.ofInt 64 j).toNat
  mapped : ∀ o, F.Off o → (Mem.loadInt st.st.1.dmem (slotA F.sp o) 8).isSome
  heap : ∀ w (a : BitVec 64), IsLoc w → ValRep lbl w.val a.toNat → Mem.loadInt st.st.1.dmem a 8 = none ∧
    st.decls.AgreesAt a 8 ∧ a.toNat + 8 ≤ 2 ^ 64 ∧ (a.toNat + 8 ≤ F.sp.toNat ∨ F.sp.toNat + F.size ≤ a.toNat)

/-- The slots are what the statement's `Place.slot` reads: each placed
variable's slot address loads, through `Scc.Sem.A64.privLoad`, a word that
represents it. -/
theorem Slots.privLoad {lbl : WeakMem.AllocLabel → Option Nat} {F : Frame} {slot : String → Option Int64}
    {st : State} {env : TermRun.Env} (h : Slots lbl F slot st env) {x : String} {o : Int64}
    (hx : slot x = some o) : ∃ ty w v, TermRun.lookupE env x = some (ty, [w]) ∧
      Scc.Sem.A64.privLoad st (slotA F.sp o) = some v ∧ ValRep lbl w.val v.toNat := by
  obtain ⟨ty, w, j, hl, hj, hv⟩ := h.rep x o hx
  exact ⟨ty, w, _, hl, by simp [Scc.Sem.A64.privLoad, hj], hv⟩

namespace Slots

variable {lbl : WeakMem.AllocLabel → Option Nat} {F : Frame} {slot : String → Option Int64} {st st' : State}
  {env : TermRun.Env}

/-- **Register framing**: a state with the same private memory, `sp` and
declarations has the same slots. -/
theorem regs (h : Slots lbl F slot st env) (hd : st'.st.1.dmem = st.st.1.dmem)
    (hsp : st'.st.1.regs.SP = st.st.1.regs.SP) (hdc : st'.decls = st.decls) : Slots lbl F slot st' env where
  ok := h.ok
  sp := hsp ▸ h.sp
  off := h.off
  inj := h.inj
  rep := hd ▸ h.rep
  mapped := hd ▸ h.mapped
  heap := hd ▸ hdc ▸ h.heap

/-- Binding a variable with no words (`unit`), unplaced. -/
theorem bind_unit (h : Slots lbl F slot st env) (u : String) :
    Slots lbl F (fun y => if y = u then none else slot y) st ((u, .unit, []) :: env) where
  ok := h.ok
  sp := h.sp
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

/-- Binding an unplaced variable (`slot x = none`) to any words. -/
theorem bind_fresh (h : Slots lbl F slot st env) {x : String} (hx : slot x = none) (ty : Ty) (ws : List TermRun.Word) :
    Slots lbl F slot st ((x, ty, ws) :: env) where
  ok := h.ok
  sp := h.sp
  off := h.off
  inj := h.inj
  rep y o hy := by
    have hyx : y ≠ x := by rintro rfl; rw [hx] at hy; cases hy
    obtain ⟨ty', w, j, hl, hj, hv⟩ := h.rep y o hy
    have hne : (x == y) = false := by simp [Ne.symm hyx]
    exact ⟨ty', w, j, by simp [TermRun.lookupE, List.find?, hne] at hl ⊢; exact hl, hj, hv⟩
  mapped := h.mapped
  heap := h.heap

/-- **Storing a variable's word into a free slot**: after the private store
of `V` to slot `od`, the variable `x` bound first in the environment (to a
word `V` represents) is placed at `od`. -/
theorem store (h : Slots lbl F slot st env) {x : String} {od : Int64} (hod : F.Off od)
    (hfree : ∀ y, slot y = some od → y = x) {ty : Ty} {w : TermRun.Word} {V : BitVec 64}
    (hv : ValRep lbl w.val V.toNat) (hd : st'.st.1.dmem = Mem.storeInt st.st.1.dmem (slotA F.sp od) 8 V.toInt)
    (hsp : st'.st.1.regs.SP = st.st.1.regs.SP) (hdc : st'.decls = st.decls) :
    Slots lbl F (fun y => if y = x then some od else slot y) st' ((x, ty, [w]) :: env) where
  ok := h.ok
  sp := hsp ▸ h.sp
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
    · rw [slotA_toNat h.ok hod]
      obtain ⟨h0, -, h5⟩ := hod
      omega

end Slots

/-! ## The emitted sequences -/

/-- `ldr Xt, [sp, #o]` (`ldrOff .W64 t spW64 o`, scaled form). -/
abbrev dLdr (t : XReg) (o : Int64) : Directive :=
  .instr ⟨.W64, .LDR (.low (.reg t) .W64) (.addr ⟨.SP, .imm ⟨.int64 o, none⟩⟩)⟩

/-- `str Xt, [sp, #o]` (`strOff .W64 t spW64 o`, scaled form). -/
abbrev dStr (t : XReg) (o : Int64) : Directive :=
  .instr ⟨.W64, .STR (.low (.reg t) .W64) ⟨.SP, .imm ⟨.int64 o, none⟩⟩⟩

/-- `stlr x9, [x10]` (`storeRel .W64 .X9 .X10`). -/
abbrev dStlr : Directive := .instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩

/-- `ldar x9, [x10]` (the `.acq` load of `FromIR.inst`). -/
abbrev dLdar : Directive := .instr ⟨.W64, .LDAR .acq false .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩

/-- `adds x9, x9, x10` (`addChecked`). -/
abbrev dAdds : Directive :=
  .instr ⟨.W64, .ADDS_s (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) ⟨.low (.reg .X10) .W64, 0, .LSL⟩⟩

/-- `b.cs L` (`addChecked`: carry set, the unsigned sum does not fit). -/
abbrev dBcs (L : String) : Directive := .instr ⟨.W64, .B_cond .CS (.label L)⟩

/-- `store rel` of the variable in slot `ov` through the pointer in slot
`op`. -/
def storeSeq (ov op : Int64) : List Directive := [dLdr .X9 ov, dLdr .X10 op, dStlr]

/-- `load acq` through the pointer in slot `op` into slot `od`. -/
def loadSeq (op od : Int64) : List Directive := [dLdr .X10 op, dLdar, dStr .X9 od]

/-- The checked `+` of slots `oa` and `ob` into slot `od`, with the abort
edge to `L`. -/
def addSeq (oa ob : Int64) (L : String) (od : Int64) : List Directive :=
  [dLdr .X9 oa, dLdr .X10 ob, dAdds, dBcs L, dStr .X9 od]

/-! ## One instruction on slots -/

theorem pc_step (pc : Int64) {a b : Nat} (h : Int64.ofNat a + Int64.ofNat 4 = Int64.ofNat b) :
    pc + Int64.ofNat a + Int64.ofNat 4 = pc + Int64.ofNat b := by
  rw [Int64.add_assoc, h]

theorem pc_zero (pc : Int64) : pc = pc + Int64.ofNat (4 * 0) := by
  rw [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero]

theorem toNat_setWidth128 (x : BitVec 64) : (x.setWidth 128).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide))]

section Rows

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- **A slot load** `ldr Xt, [sp, #o]` of a placed variable: no event, the
source stutters, `Xt` holds a word representing the variable. -/
theorem out_ldr {X : Frag isaLSE2} {s : State} {c : Ctl} {env : TermRun.Env} {t : XReg} {o : Int64}
    {x : String} (hc : CellAt s (dLdr t o) 4) (hS : Slots lbl F slot s env) (hx : slot x = some o)
    (hX : ∀ ty w j, TermRun.lookupE env x = some (ty, [w]) → ValRep lbl w.val (BitVec.ofInt 64 j).toNat →
      X (after s 4 { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (BitVec.ofInt 64 j) }) c) :
    Out p lbl ms X s c := by
  obtain ⟨ty, w, j, hl, hj, hv⟩ := hS.rep x o hx
  exact .silent _ c (exec_ldr_sp hc (by rw [hS.sp]; exact hS.ok.align) (by rw [hS.sp]; rfl) hj) (.refl c)
    (hX ty w j hl hv)

/-- **A slot store** `str Xt, [sp, #o]` into the frame: no event, the source
stutters. -/
theorem out_str {X : Frag isaLSE2} {s : State} {c : Ctl} {env : TermRun.Env} {t : XReg} {od : Int64}
    (hc : CellAt s (dStr t od) 4) (hS : Slots lbl F slot s env) (hod : F.Off od)
    (hX : X (after s 4 { s.st.1 with dmem := (Mem.storeInt s.st.1.dmem (slotA F.sp od) 8
      (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).toInt) }) c) :
    Out p lbl ms X s c := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hS.mapped od hod)
  exact .silent _ c (exec_str_sp hc (by rw [hS.sp]; exact hS.ok.align) (by rw [hS.sp]; rfl) hj) (.refl c) hX

end Rows

/-! ## `store rel` -/

section Store

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of `store rel`. -/
def storeTerm (u pv vv : String) (e : Expr) : Expr := .let_ u (.store true (.var pv) (.var vv) none) e

/-- **Entry of `store rel`**: at `pc`, the sequence there, the source at
`let u = store rel pv vv in e` with environment `env0`, the slots. -/
def StoreIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (u pv vv : String) (e : Expr) (ov op : Int64) (env0 : TermRun.Env) : Frag isaLSE2 := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (storeSeq ov op) ∧ c = ⟨storeTerm u pv vv e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Exit of `store rel`**: after the sequence, the source at `e` with `u`
bound to unit (unplaced). -/
def StoreOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (u : String) (e : Expr) (ov op : Int64) (env0 : TermRun.Env) : Frag isaLSE2 := fun s c =>
  s.st.2 = pc + Int64.ofNat 12 ∧ CodeAt s pc (storeSeq ov op) ∧ c = ⟨e, (u, .unit, []) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = u then none else slot y) s ((u, .unit, []) :: env0)

/-- **`store rel` simulates the source's release store**: two slot loads
(the source stutters), then the `stlr`, the source's store. -/
theorem seg_store {pc : Int64} {u pv vv : String} {e : Expr} {ov op : Int64} {env0 : TermRun.Env}
    (hv : slot vv = some ov) (hp : slot pv = some op) {tp tv : Ty} {wp wv : TermRun.Word}
    (hlp : TermRun.lookupE env0 pv = some (tp, [wp])) (hlv : TermRun.lookupE env0 vv = some (tv, [wv]))
    (hloc : IsLoc wp) :
    Seg p lbl ms (StoreIn lbl F slot pc u pv vv e ov op env0) (StoreOut lbl F slot pc u e ov op env0) := by
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 4 ∧ CodeAt s pc (storeSeq ov op) ∧
      c = ⟨storeTerm u pv vv e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl wv.val (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 8 ∧ CodeAt s pc (storeSeq ov op) ∧
      c = ⟨storeTerm u pv vv e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl wv.val (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat ∧
      ValRep lbl wp.val (s.st.1.regs.getXReg .X10).toBitVec.toNat) (Seg.step ?_) (Seg.step ?_))
  · rintro s c ⟨hpc, hcode, rfl, hS⟩
    refine out_ldr (hcode.cell (j := 0) rfl rfl rfl (by rw [hpc]; exact pc_zero pc)) hS hv
      fun ty w j hl hval => ?_
    rw [hlv] at hl
    cases hl
    exact ⟨by simp [hpc], hcode.after _ _, rfl, hS.regs rfl (by simp) rfl, by simpa using hval⟩
  · rintro s c ⟨hpc, hcode, rfl, hS, hx9⟩
    refine out_ldr (hcode.cell (j := 1) rfl rfl rfl (by rw [hpc]; try rfl)) hS hp fun ty w j hl hval => ?_
    rw [hlp] at hl
    cases hl
    exact ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, rfl, hS.regs rfl (by simp) rfl,
      by simpa using hx9, by simpa using hval⟩
  · rintro s c ⟨hpc, hcode, rfl, hS, hx9, hx10⟩
    have hc := hcode.cell (j := 2) rfl rfl rfl (by rw [hpc]; try rfl)
    obtain ⟨hdm, hag, -, -⟩ := hS.heap wp _ hloc hx10
    refine .store .rel _ _ _ u (.var pv) (.var vv) e tp tv wp wv (exec_stlr_agrees hc hdm hag) rfl
      (by simpa [TermRun.evalAt] using hlp) hx10 (by simpa [TermRun.evalAt] using hlv)
      (by rw [toNat_setWidth128]; exact hx9) ?_ hloc
    exact ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, rfl,
      (hS.regs (st' := after s 4 s.st.1) rfl rfl rfl).bind_unit u⟩

end Store

/-! ## `load acq` -/

section Load

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of `load acq`. -/
def loadTerm (x pv : String) (e : Expr) : Expr := .let_ x (.load true (.var pv)) e

/-- **Entry of `load acq`.** -/
def LoadIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x pv : String) (e : Expr) (op od : Int64) (env0 : TermRun.Env) : Frag isaLSE2 := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (loadSeq op od) ∧ c = ⟨loadTerm x pv e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Exit of `load acq`**: the source at `e` with `x` bound to the word
read, placed at slot `od`. -/
def LoadOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x : String) (e : Expr) (op od : Int64) (env0 : TermRun.Env) : Frag isaLSE2 := fun s c =>
  s.st.2 = pc + Int64.ofNat 12 ∧ CodeAt s pc (loadSeq op od) ∧ ∃ ty w, c = ⟨e, (x, ty, [w]) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = x then some od else slot y) s ((x, ty, [w]) :: env0)

/-- **`load acq` simulates the source's acquire load**: a slot load (the
source stutters), the `ldar` (the source's load, for every value read), a
slot store of the result (the source stutters). The destination slot is
free (no other variable is placed there). -/
theorem seg_load {pc : Int64} {x pv : String} {e : Expr} {op od : Int64} {env0 : TermRun.Env}
    (hp : slot pv = some op) {tp : Ty} {wp : TermRun.Word} (hlp : TermRun.lookupE env0 pv = some (tp, [wp]))
    (hloc : IsLoc wp) (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (LoadIn lbl F slot pc x pv e op od env0) (LoadOut lbl F slot pc x e op od env0) := by
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 4 ∧ CodeAt s pc (loadSeq op od) ∧
      c = ⟨loadTerm x pv e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl wp.val (s.st.1.regs.getXReg .X10).toBitVec.toNat) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 8 ∧ CodeAt s pc (loadSeq op od) ∧
      ∃ ty w, c = ⟨e, (x, ty, [w]) :: env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      ValRep lbl w.val (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat) (Seg.step ?_) (Seg.step ?_))
  · rintro s c ⟨hpc, hcode, rfl, hS⟩
    refine out_ldr (hcode.cell (j := 0) rfl rfl rfl (by rw [hpc]; exact pc_zero pc)) hS hp
      fun ty w j hl hval => ?_
    rw [hlp] at hl
    cases hl
    exact ⟨by simp [hpc], hcode.after _ _, rfl, hS.regs rfl (by simp) rfl, by simpa using hval⟩
  · rintro s c ⟨hpc, hcode, rfl, hS, hx10⟩
    have hc := hcode.cell (j := 1) rfl rfl rfl (by rw [hpc]; try rfl)
    obtain ⟨hdm, hag, -, -⟩ := hS.heap wp _ hloc hx10
    refine .load .acq _ _ x (.var pv) e tp wp (exec_ldar_agrees hc hdm hag) rfl
      (by simpa [TermRun.evalAt] using hlp) hx10 (fun v w' _ hval => ?_) hloc
    refine ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, loadTy tp, w', rfl,
      hS.regs rfl (by simp) rfl, ?_⟩
    rw [show ((s.st.1.regs.setRegOrZr (.low (.reg .X9) .W64) (v.setWidth 64)).getRegOrZr
        (.low (.reg .X9) .W64)) = v.setWidth 64 by simp]
    exact hval
  · rintro s c ⟨hpc, hcode, ty, w, rfl, hS, hx9⟩
    refine out_str (hcode.cell (j := 2) rfl rfl rfl (by rw [hpc]; try rfl)) hS hod ?_
    exact ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, ty, w, rfl,
      hS.store hod hfree hx9 rfl rfl rfl⟩

end Load


/-! ## The checked `+` -/

section Add

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- The source term of the checked `+`. -/
def addTerm (x a b : String) (e : Expr) : Expr := .let_ x (.add (.var a) (.var b)) e

/-- **Entry of the checked `+`**: also the abort label `L` at `lpc`. -/
def AddIn (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x a b : String) (e : Expr) (oa ob : Int64) (L : String) (od lpc : Int64) (env0 : TermRun.Env) :
    Frag isaLSE2 := fun s c =>
  s.st.2 = pc ∧ CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
    c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0

/-- **Normal exit of the checked `+`**: the source at `e` with `x` bound to
the sum `w`, placed at slot `od`. -/
def AddOut (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x : String) (e : Expr) (oa ob : Int64) (L : String) (od lpc : Int64) (env0 : TermRun.Env)
    (w : TermRun.Word) : Frag isaLSE2 := fun s c =>
  s.st.2 = pc + Int64.ofNat 20 ∧ CodeAt s pc (addSeq oa ob L od) ∧
    (_root_.Executable.labels s.exe).label L = lpc ∧ c = ⟨e, (x, .int, [w]) :: env0, none⟩ ∧
    Slots lbl F (fun y => if y = x then some od else slot y) s ((x, .int, [w]) :: env0)

/-- **Abort exit of the checked `+`**: at the abort label, the source
unchanged and about to overflow (`OvfReady`). -/
def AddAbort (lbl : WeakMem.AllocLabel → Option Nat) (F : Frame) (slot : String → Option Int64) (pc : Int64)
    (x a b : String) (e : Expr) (oa ob : Int64) (L : String) (od lpc : Int64) (env0 : TermRun.Env) :
    Frag isaLSE2 := fun s c =>
  s.st.2 = lpc ∧ CodeAt s pc (addSeq oa ob L od) ∧ c = ⟨addTerm x a b e, env0, none⟩ ∧ OvfReady c ∧
    Slots lbl F slot s env0

/-- **The checked `+` simulates the source's `+`, or aborts justifiably**:
two slot loads and the `adds` (the source stutters); at `b.cs`, without
carry the source adds (one local step) and the slot store follows (the
source stutters); with carry the thread is at the abort label and the
source thread, unchanged, is `OvfReady`. The operands are numbers (an
`undef` operand has no counterpart: see the finding). -/
theorem seg_add {pc : Int64} {x a b : String} {e : Expr} {oa ob : Int64} {L : String} {od lpc : Int64}
    {env0 : TermRun.Env} (ha : slot a = some oa) (hb : slot b = some ob) {ta tb : Ty} {wa wb : TermRun.Word}
    {n m : Nat} (hla : TermRun.lookupE env0 a = some (ta, [wa])) (hlb : TermRun.lookupE env0 b = some (tb, [wb]))
    (hna : wa.val = .num n) (hnb : wb.val = .num m) (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    Seg p lbl ms (AddIn lbl F slot pc x a b e oa ob L od lpc env0)
      (fun s c => AddOut lbl F slot pc x e oa ob L od lpc env0 (TermRun.addW wa wb) s c ∨
        AddAbort lbl F slot pc x a b e oa ob L od lpc env0 s c) := by
  have hea : TermRun.evalAt env0 (.var a) = some (ta, [wa]) := by simpa [TermRun.evalAt] using hla
  have heb : TermRun.evalAt env0 (.var b) = some (tb, [wb]) := by simpa [TermRun.evalAt] using hlb
  refine Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 4 ∧
      CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat = n) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 8 ∧
      CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat = n ∧
      (s.st.1.regs.getRegOrZr (.low (.reg .X10) .W64)).toNat = m) (Seg.step ?_)
    (Seg.seq (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 12 ∧
      CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
      c = ⟨addTerm x a b e, env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.status.c = true → 2 ^ 64 ≤ n + m) ∧
      (s.st.1.status.c = false → (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat = n + m)) (Seg.step ?_)
    (Seg.seq_left (Q := fun (s : State) (c : Ctl) => s.st.2 = pc + Int64.ofNat 16 ∧
      CodeAt s pc (addSeq oa ob L od) ∧ (_root_.Executable.labels s.exe).label L = lpc ∧
      c = ⟨e, (x, .int, [TermRun.addW wa wb]) :: env0, none⟩ ∧ Slots lbl F slot s env0 ∧
      (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat = n + m) (Seg.step ?_) (Seg.step ?_))))
  · rintro s c ⟨hpc, hcode, hL, rfl, hS⟩
    refine out_ldr (hcode.cell (j := 0) rfl rfl rfl (by rw [hpc]; exact pc_zero pc)) hS ha
      fun ty w j hl hval => ?_
    rw [hla] at hl
    cases hl
    rw [hna] at hval
    exact ⟨by simp [hpc], hcode.after _ _, hL, rfl, hS.regs rfl (by simp) rfl, by simpa using hval.2⟩
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, hx9⟩
    refine out_ldr (hcode.cell (j := 1) rfl rfl rfl (by rw [hpc]; try rfl)) hS hb fun ty w j hl hval => ?_
    rw [hlb] at hl
    cases hl
    rw [hnb] at hval
    exact ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, hL, rfl,
      hS.regs rfl (by simp) rfl, by simpa using hx9, by simpa using hval.2⟩
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, hx9, hx10⟩
    have hc := hcode.cell (j := 2) rfl rfl rfl (by rw [hpc]; try rfl)
    refine .silent _ _ (exec_adds_s hc) (.refl _) ?_
    have hn := s.st.1.regs.X9.toNat_lt
    have hm := s.st.1.regs.X10.toNat_lt
    have hx9' : s.st.1.regs.X9.toNat = n := by simpa using hx9
    have hx10' : s.st.1.regs.X10.toNat = m := by simpa using hx10
    refine ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, hL, rfl,
      hS.regs rfl (by simp) rfl, fun hcar => ?_, fun hcar => ?_⟩
    · simp [StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, ShiftRegExpr.interp, BitVec.toNat_add,
        hx9', hx10'] at hcar
      omega
    · simp [StatusFlags.adds, StatusFlags.from_result, BitVec.unsigned, ShiftRegExpr.interp, BitVec.toNat_add,
        hx9', hx10'] at hcar ⊢
      omega
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, hcar, hsum⟩
    have hc := hcode.cell (j := 3) rfl rfl rfl (by rw [hpc]; try rfl)
    have hbt : branchTarget s 4 (.label L) = lpc := by
      simp [branchTarget, ConstExpr.evalBranchTarget, ConstExpr.interp, hL]
    cases hc' : s.st.1.status.c
    · refine .silent _ _ (exec_bcond hc) (.single (localStep_add rfl hea heb)) (.inl ?_)
      have h9 := hsum hc'
      have hlt := (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).isLt
      refine ⟨?_, hcode.jump _ _, hL, rfl, hS.regs rfl rfl rfl, by simpa using h9⟩
      simp only [jumpTo, CondCode.interp, hc', Bool.false_eq_true, ↓reduceIte, hpc]
      exact pc_step pc (by decide)
    · refine .silent _ _ (exec_bcond hc) (.refl _) (.inr ?_)
      refine ⟨?_, hcode.jump _ _, rfl, ⟨x, .var a, .var b, e, ta, tb, wa, wb, n, m, rfl, hea, heb, hna, hnb,
        hcar hc'⟩, hS.regs rfl rfl rfl⟩
      simp only [jumpTo, CondCode.interp, hc', ↓reduceIte, hbt]
  · rintro s c ⟨hpc, hcode, hL, rfl, hS, h9⟩
    refine out_str (hcode.cell (j := 4) rfl rfl rfl (by rw [hpc]; try rfl)) hS hod ?_
    have hlt := s.st.1.regs.X9.toNat_lt
    have h9' : s.st.1.regs.X9.toNat = n + m := by simpa using h9
    have hv : ValRep lbl (TermRun.addW wa wb).val (s.st.1.regs.getRegOrZr (.low (.reg .X9) .W64)).toNat := by
      simp [TermRun.addW, hna, hnb, TermRun.cst, Promises.TVal.mk0, ValRep, h9']
      omega
    exact ⟨by simp only [after, hpc] <;> exact pc_step pc (by decide), hcode.after _ _, hL, rfl,
      hS.store hod hfree hv rfl rfl rfl⟩

end Add

end Spike.Lib.A64
