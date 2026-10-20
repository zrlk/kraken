/-
**The event trees of the whole `treiber_pp.kl` image**
`treiberImageA` (`EnvG/A64WholeTreiberVCGen.lean`) under the promising
interpretation of AArch64, on a valid layout, **with any declarations**
(`LiveTermTreiber2Trees.lean`'s recipe, through `exec_eq_of_codeAtD`, the
declarations-agnostic `AArch64.exec_eq_of_codeAt`).

```
 0 pusher:                  12 popper:
 1   STR W9,[X1]            13   LDAR X2,[X0]
 2 push:                    14   CBZ X2,popper
 3   LDAR X2,[X0]           15   LDR X4,[X2,#8]
 4   STR X2,[X1,#8]         16   MOV X3,X2
 5   MOV X3,X2              17   CASAL X3,X4,[X0]
 6   CASAL X3,X1,[X0]       18   CMP X3,X2
 7   CMP X3,X2              19   B.NE popper
 8   B.NE push              20   MOV X10,X2
 9   B pdone                21   LDR W11,[X2]
10 pdone:                   22   B qdone
11   NOP                    23 qdone:
```

`top = X0`, the pusher's node `= X1`. A label shares the address of the next
cell (`0 ↦ 1`, `2 ↦ 3`, `10 ↦ 11`, `12 ↦ 13`, `23 ↦ 24`, the end of the
text). The accesses at fixed words (`top`, the node's data and link words)
are stated for declarations that resolve them to themselves
(`Decls.AgreesAt`); the popper's accesses through `X2` are stated through
`EvTree.access` (they may fault under declarations that do not resolve them).
-/
import Kraken.Promising.SLR.EnvG.A64WholeTreiberPublic
import Kraken.Promising.SLR.A64Trees
import Kraken.Promising.LiveTermTreiber2Trees
import Kraken.Promising.LiveTermTreiber2Rank
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.Promising.Live.TreiberPpA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.Treiber (treiberImageA treiberImageA_wf)
open Kraken.Promising.SLR.A64Trees (goto)

/-- `AArch64.exec_eq_of_codeAt` with any declarations. -/
theorem exec_eq_of_codeAtD {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    (he : st.exe = e) (hne : (st.st.2 == st.endPc) = false) {d : Directive} {sz : Nat}
    {rest : List (Directive × Nat)} (hcode : e.codeAt st.st.2 = (d, sz) :: rest) :
    isa.exec st = some ((toEv st.decls (@Directive.interp (_root_.Executable.labels e) d st.st.1
      (.mk st.st.2 (st.st.2 + .ofNat sz)) (fun s' => .done (s', st.st.2 + .ofNat sz))
      (fun pc s' => .done (s', pc)))).map fun s => { st with st := s }) := by
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hcode hat hne ⊢
  subst he
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false, hne, Bool.false_eq_true, ↓reduceIte]
  congr 2
  unfold Executable.step
  letI := Executable.labels exe
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiberImageA)]

set_option hygiene false in
local notation "pcT" => (layout treiberImageA).addrOf

/-- The context of a cell (any declarations). -/
structure AtD (st : State) (i : Nat) : Prop where
  exe : st.exe = layout treiberImageA
  pc : st.st.2 = pcT i
  ne : (st.st.2 == st.endPc) = false

theorem addrOf_label {i : Nat} {l : Label} (hp : treiberImageA[i]? = some (Directive.label l)) :
    pcT (i + 1) = pcT i :=
  SLR.A64Trees.addrOf_label hp

set_option maxRecDepth 8192

theorem label_push : (_root_.Executable.labels (layout treiberImageA)).label "push" = pcT 3 := by
  rw [Program.label_addrOf_drop treiberImageA_wf.nodup (i := 2) (by decide) (by decide)]
  exact (addrOf_label (i := 2) (l := "push") rfl).symm

theorem label_pdone : (_root_.Executable.labels (layout treiberImageA)).label "pdone" = pcT 11 := by
  rw [Program.label_addrOf_drop treiberImageA_wf.nodup (i := 10) (by decide) (by decide)]
  exact (addrOf_label (i := 10) (l := "pdone") rfl).symm

theorem label_pusher : (_root_.Executable.labels (layout treiberImageA)).label "pusher" = pcT 1 := by
  rw [Program.label_addrOf_drop treiberImageA_wf.nodup (i := 0) (by decide) (by decide)]
  exact (addrOf_label (i := 0) (l := "pusher") rfl).symm

theorem label_popper : (_root_.Executable.labels (layout treiberImageA)).label "popper" = pcT 13 := by
  rw [Program.label_addrOf_drop treiberImageA_wf.nodup (i := 12) (by decide) (by decide)]
  exact (addrOf_label (i := 12) (l := "popper") rfl).symm

theorem label_qdone : (_root_.Executable.labels (layout treiberImageA)).label "qdone" = pcT 24 := by
  rw [Program.label_addrOf_drop treiberImageA_wf.nodup (i := 23) (by decide) (by decide)]
  exact (addrOf_label (i := 23) (l := "qdone") rfl).symm

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : AtD st i) (hi : i < treiberImageA.length) :
    pcT (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact SLR.A64Trees.addrOf_step hi

/-- Read the cell at position `i` through `exec_eq_of_codeAtD` and unfold it. -/
local macro "cellD" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := treiberImageA) (i := $i)
    (d := (treiberImageA)[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : (treiberImageA)[$i] = d at hc
  simp only [treiberImageA, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAtD ($h).exe ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp, label_push, label_pdone, label_popper, label_qdone]
  simp [toEv, RegOrSp.interpBase, MachineData.rmwK, MachineData.loadK,
    MachineData.storeK, MachineData.load, MachineData.store, EvTree.map,
    AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore, AddrExpr.checkSPAlignment,
    AddrExpr.eval, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, RegOrZr.base, RegOrZr.isZr, Reg64s.getXReg, goto, EvTree.access_empty, $ts,*]))


open TermTreiber2Trees (ofInt_add8)

/-- `str w9, [x1]` (position 1): a plain store of the data word. -/
theorem exec_str1 (st : State) (h : AtD st 1) {n : BitVec 64} (hag : st.decls.AgreesAt n 4)
    (hx1 : st.st.1.regs.X1.toBitVec = n) (hdm : Mem.loadInt st.st.1.dmem n 4 = none) :
    isa.exec st = some (.store .plain false ⟨n, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X9.toBitVec))
      fun _ => .done (goto st st.st.1 (pcT 3))) := by
  rw [addrOf_label (i := 2) (l := "push") (by decide), next_pc h (by decide)]
  cellD h 1 [hx1, hdm, EvTree.access_of_agreesAt hag]

/-- `ldar x2, [x0]` (positions 3 and 13): a load of `top` into `X2`. -/
theorem exec_ldar (i : Nat) (hi : i = 3 ∨ i = 13) (st : State) (h : AtD st i) {t : BitVec 64}
    (hag : st.decls.AgreesAt t 8) (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ k : LoadKind, isa.exec st = some (.load k false ⟨t, 8⟩
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 v) }
        (pcT (i + 1)))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]; cellD h 3 [hx0, hdm, EvTree.access_of_agreesAt hag]
  · rw [next_pc h (by decide)]; cellD h 13 [hx0, hdm, EvTree.access_of_agreesAt hag]

/-- `str x2, [x1, #8]` (position 4): a plain store of the link. -/
theorem exec_str4 (st : State) (h : AtD st 4) {n : BitVec 64} (hag : st.decls.AgreesAt (n + 8#64) 8)
    (hx1 : st.st.1.regs.X1.toBitVec = n) (hdm : Mem.loadInt st.st.1.dmem (n + 8#64) 8 = none) :
    isa.exec st = some (.store .plain false ⟨n + 8, 8⟩ (BitVec.setWidth 128 st.st.1.regs.X2.toBitVec)
      fun _ => .done (goto st st.st.1 (pcT 5))) := by
  rw [next_pc h (by decide)]
  cellD h 4 [hx1, ofInt_add8, hdm, EvTree.access_of_agreesAt hag]

/-- `mov x3, x2` (positions 5 and 16). -/
theorem exec_mov (i : Nat) (hi : i = 5 ∨ i = 16) (st : State) (h : AtD st i) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X3 st.st.1.regs.X2.toBitVec } (pcT (i + 1)))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]; cellD h 5 []
  · rw [next_pc h (by decide)]; cellD h 16 []

/-- `casal x3, xS, [x0]` (positions 6, `xS = x1`, and 17, `xS = x4`): an RMW
of `top` that writes `xS` iff the old value is `X3`; `X3` receives the old
value. -/
theorem exec_casal (i : Nat) (hi : i = 6 ∨ i = 17) (st : State) (h : AtD st i) {t : BitVec 64}
    (hag : st.decls.AgreesAt t 8) (hx0 : st.st.1.regs.X0.toBitVec = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ k : RmwKind, isa.exec st = some (.rmw k false ⟨t, 8⟩
      (fun old => if BitVec.setWidth 64 old = st.st.1.regs.X3.toBitVec then
          some (BitVec.setWidth 128 (if i = 6 then st.st.1.regs.X1 else st.st.1.regs.X4).toBitVec) else none)
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X3 (BitVec.setWidth 64 v) }
        (pcT (i + 1)))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]; cellD h 6 [hx0, hdm, EvTree.access_of_agreesAt hag]
  · rw [next_pc h (by decide)]; cellD h 17 [hx0, hdm, EvTree.access_of_agreesAt hag]

/-- `cmp x3, x2` (positions 7 and 18): silent, sets the flags; `Z` iff
`X3 = X2`. -/
theorem exec_cmp (i : Nat) (hi : i = 7 ∨ i = 18) (st : State) (h : AtD st i) :
    ∃ s : StatusFlags, isa.exec st = some (.done (goto st { st.st.1 with status := s } (pcT (i + 1))))
      ∧ (s.z = true ↔ st.st.1.regs.X3.toBitVec = st.st.1.regs.X2.toBitVec) := by
  refine ⟨?s, ?e, ?z⟩
  case e =>
    rcases hi with rfl | rfl
    · rw [next_pc h (by decide)]; cellD h 7 []; try rfl
    · rw [next_pc h (by decide)]; cellD h 18 []; try rfl
  case z =>
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
    exact iff_of_eq (congrArg _ (BitVec.zero_add _))

/-- `b.ne push` (position 8). -/
theorem exec_bne8 (st : State) (h : AtD st 8) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.z = true then pcT 9 else pcT 3))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.z = true <;> cellD h 8 [hz]

/-- `b pdone` (position 9). -/
theorem exec_b9 (st : State) (h : AtD st 9) : isa.exec st = some (.done (goto st st.st.1 (pcT 11))) := by
  cellD h 9 []

/-- `cbz x2, popper` (position 14). -/
theorem exec_cbz14 (st : State) (h : AtD st 14) :
    isa.exec st = some (.done (goto st st.st.1
      (if st.st.1.regs.X2.toBitVec = 0#64 then pcT 13 else pcT 15))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.regs.X2.toBitVec = 0#64 <;> cellD h 14 [hz]

/-- `ldr x4, [x2, #8]` (position 15): from the thread's private memory if it
holds the word, else a plain load of the link of the node read, through the
declarations. -/
theorem exec_ldr15 (st : State) (h : AtD st 15) :
    (∃ v4 : BitVec 64, isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X4 v4 } (pcT 16)))) ∨
    isa.exec st = some (EvTree.access st.decls (st.st.1.regs.X2.toBitVec + 8) 8 fun l => .load .plain false l
      fun v => .done (goto st { st.st.1 with regs := st.st.1.regs.setXReg .X4 (BitVec.setWidth 64 v) } (pcT 16))) := by
  rw [next_pc h (by decide)]
  cases hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.X2.toBitVec + 8#64) 8 with
  | none =>
    refine .inr ?_
    cellD h 15 [ofInt_add8, hdm]
    congr 1; unfold EvTree.access; split <;> rfl
  | some i =>
    refine .inl ⟨BitVec.ofInt 64 i, ?_⟩
    cellD h 15 [ofInt_add8, hdm]

/-- `b.ne popper` (position 19). -/
theorem exec_bne19 (st : State) (h : AtD st 19) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.z = true then pcT 20 else pcT 13))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.z = true <;> cellD h 19 [hz]

/-- `mov x10, x2` (position 20). -/
theorem exec_mov20 (st : State) (h : AtD st 20) :
    isa.exec st = some (.done (goto st
      { st.st.1 with regs := st.st.1.regs.setXReg .X10 st.st.1.regs.X2.toBitVec } (pcT 21))) := by
  rw [next_pc h (by decide)]
  cellD h 20 []

/-- `ldr w11, [x2]` (position 21): a plain load of the popped node's data,
through the declarations. -/
theorem exec_ldr21 (st : State) (h : AtD st 21) (hdm : Mem.loadInt st.st.1.dmem st.st.1.regs.X2.toBitVec 4 = none) :
    isa.exec st = some (EvTree.access st.decls st.st.1.regs.X2.toBitVec 4 fun l => .load .plain false l
      fun v => .done (goto st
        { st.st.1 with regs := st.st.1.regs.setXReg .X11 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } (pcT 22))) := by
  rw [next_pc h (by decide)]
  cellD h 21 [hdm]
  congr 1; unfold EvTree.access; split <;> rfl

/-- `b qdone` (position 22). -/
theorem exec_b22 (st : State) (h : AtD st 22) : isa.exec st = some (.done (goto st st.st.1 (pcT 24))) := by
  cellD h 22 []

/-! ## Positions -/

/-- The positions a thread's pc takes (each label at the address of the next
cell; `11` and `24` are the ends). -/
def tPcs : List Nat := [1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24]

/-- The address-distinct representative of a position: the label before it. -/
def canon (i : Nat) : Nat :=
  if i = 3 then 2 else if i = 11 then 10 else if i = 13 then 12 else if i = 24 then 23 else i

theorem addrOf_canon (i : Nat) : pcT (canon i) = pcT i := by
  unfold canon
  split
  · subst_vars; exact (addrOf_label (i := 2) (l := "push") (by decide)).symm
  split
  · subst_vars; exact (addrOf_label (i := 10) (l := "pdone") (by decide)).symm
  split
  · subst_vars; exact (addrOf_label (i := 12) (l := "popper") (by decide)).symm
  split
  · subst_vars; exact (addrOf_label (i := 23) (l := "qdone") (by decide)).symm
  rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tPcs) (hj : j ∈ tPcs) (h : pcT i = pcT j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen _ TermTreiber2.isInstr (fun _ => rfl) tPcs canon (fun i _ => addrOf_canon i)
    (by decide) hi hj h

/-- The position of an address (`0` off the positions). -/
def posOf (pc : Int64) : Nat := (tPcs.find? fun i => decide (pcT i = pc)).getD 0

theorem posOf_pcT {i : Nat} (hi : i ∈ tPcs) : posOf (pcT i) = i := by
  unfold posOf
  cases h : tPcs.find? (fun j => decide (pcT j = pcT i)) with
  | none => exact absurd (by simpa using List.find?_eq_none.mp h i hi) (fun h' : ¬ pcT i = pcT i => h' rfl)
  | some j =>
    have := List.find?_some h
    simp only [decide_eq_true_eq] at this
    exact addrOf_inj (List.mem_of_find?_eq_some h) hi this

end Kraken.Promising.Live.TreiberPpA64
