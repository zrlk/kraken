/-
**The event trees of the whole x64 `treiber_pp.kl`
image** `treiberImageV` (`EnvG/X64TreiberAbsVCGen.lean`: the `.kl`'s `code`
block verbatim, then the runner's data trailer) under the promising
interpretation of x64, on a valid layout, **with any declarations** (the
x64 twin of `LiveTreiberPpA64Trees.lean`, through `exec_eq_of_codeAtD`, the
declarations-agnostic `X64.exec_eq_of_codeAt`).

```
 0 pusher:                       10 popper:
 1   movl $1,(%rbx)              11   movq (%rdi),%rax
 2 push:                         12   testq %rax,%rax
 3   movq (%rdi),%rax            13   je popper
 4   movq %rax,8(%rbx)           14   movq 8(%rax),%rcx
 5   lock cmpxchgq %rbx,(%rdi)   15   lock cmpxchgq %rcx,(%rdi)
 6   jne push                    16   jne popper
 7   jmp pdone                   17   movq %rax,%r10
 8 pdone:                        18   movl (%rax),%r11d
 9   nop                         19   jmp qdone
                                 20 qdone:
                                 21.. the data trailer (`top`, `n1`)
```

`top = %rdi`, the pusher's node `= %rbx`. A label shares the address of the
next cell (`0 ↦ 1`, `2 ↦ 3`, `8 ↦ 9`, `10 ↦ 11`, `20 ↦ 21`). The accesses at
fixed words (`top`, the node's data and link words) are stated for
declarations that resolve them to themselves (`Decls.AgreesAt`); the
popper's accesses through `%rax` are stated through `EvTree.access` (they may
fault under declarations that do not resolve them). Each cell is stated up to
the register results the liveness argument does not read (`testq` leaves
`AF` undefined: a `.choose`).
-/
import Kraken.Promising.SLR.EnvG.X64TreiberAbsRunner
import Kraken.Promising.SLR.X64Trees
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.Promising.Live.TreiberPpX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.X64.EnvG.TreiberAbs (treiberImageV treiberCodeV treiberDataV treiberImageV_wf)

/-- `X64.exec_eq_of_codeAt` with any declarations. -/
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

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiberImageV)]

set_option hygiene false in
local notation "pcT" => (layout treiberImageV).addrOf

/-- The state `st` moved to machine data `m` at address `pc`. -/
abbrev goto (st : State) (m : MachineData) (pc : Int64) : State :=
  { st with st := (m, pc) }

/-- The context of a cell (any declarations). -/
structure AtD (st : State) (i : Nat) : Prop where
  exe : st.exe = layout treiberImageV
  pc : st.st.2 = pcT i
  ne : (st.st.2 == st.endPc) = false

theorem addrOf_label {i : Nat} {l : Label} (hp : treiberImageV[i]? = some (Directive.label l)) :
    pcT (i + 1) = pcT i :=
  SLR.X64Trees.addrOf_label hp

set_option maxRecDepth 8192

theorem label_at {x : Label} (i : Nat) (hd : treiberImageV.drop i = Program.fromLabel treiberImageV x := by decide)
    (hne : Program.fromLabel treiberImageV x ≠ [] := by decide) (hl : treiberImageV[i]? = some (.label x) := by decide) :
    (_root_.Executable.labels (layout treiberImageV)).label x = pcT (i + 1) :=
  (Program.label_addrOf_drop treiberImageV_wf.nodup hd hne).trans (addrOf_label hl).symm

theorem label_pusher : (_root_.Executable.labels (layout treiberImageV)).label "pusher" = pcT 1 := label_at 0
theorem label_push : (_root_.Executable.labels (layout treiberImageV)).label "push" = pcT 3 := label_at 2
theorem label_pdone : (_root_.Executable.labels (layout treiberImageV)).label "pdone" = pcT 9 := label_at 8
theorem label_popper : (_root_.Executable.labels (layout treiberImageV)).label "popper" = pcT 11 := label_at 10
theorem label_qdone : (_root_.Executable.labels (layout treiberImageV)).label "qdone" = pcT 21 := label_at 20

omit hv in
private theorem next_pc {st : State} {i : Nat} (h : AtD st i) (hi : i < treiberImageV.length) :
    pcT (i + 1) = st.st.2 + .ofNat (Kraken.Layout.size Directive i) := by
  rw [h.pc]; exact SLR.X64Trees.addrOf_step hi

omit layout hv in
/-- A relative jump lands on its target. -/
private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

omit layout hv in
theorem ofInt_add8 (n : BitVec 64) : BitVec.ofInt 64 (n.toInt + 8) = n + 8 := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_add, BitVec.toInt_ofInt]

/-- Read the cell at position `i` through `exec_eq_of_codeAtD` and unfold it. -/
local macro "cellD" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := treiberImageV) (i := $i)
    (d := (treiberImageV)[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : (treiberImageV)[$i] = d at hc
  simp only [treiberImageV, treiberCodeV, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAtD ($h).exe ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp]
  simp [toEv, EvTree.map, EvTree.access_empty, Operand.interp, RegOrMem.interp, MachineData.set,
    MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw, AddrExpr.interp,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.take,
    label_push, label_pdone, label_popper, label_qdone, int64_add_sub, $ts,*]))

/-- `movl $1,(%rbx)` (position 1): a plain store of the data word. -/
theorem exec_st1 (st : State) (h : AtD st 1) {n : BitVec 64} (hag : st.decls.AgreesAt n 4)
    (hrbx : st.st.1.regs.get64 .rbx = n) (hdm : Mem.loadInt st.st.1.dmem n 4 = none) :
    isa.exec st = some (.store .plain false ⟨n, 4⟩ 1 fun _ => .done (goto st st.st.1 (pcT 3))) := by
  rw [addrOf_label (i := 2) (l := "push") (by decide), next_pc h (by decide)]
  cellD h 1 [hrbx, hdm, EvTree.access_of_agreesAt hag]

/-- What a cell keeps: the private memory, `%rdi` and `%rbx`. -/
structure Keeps (md md' : MachineData) : Prop where
  dmem : md'.dmem = md.dmem
  rdi : md'.regs.get64 .rdi = md.regs.get64 .rdi
  rbx : md'.regs.get64 .rbx = md.regs.get64 .rbx

omit layout hv in
theorem Keeps.refl (md : MachineData) : Keeps md md := ⟨rfl, rfl, rfl⟩

/-- `movq (%rdi),%rax` (positions 3 and 11): a plain load of `top` into
`%rax`. -/
theorem exec_ld (i : Nat) (hi : i = 3 ∨ i = 11) (st : State) (h : AtD st i) {t : BitVec 64}
    (hag : st.decls.AgreesAt t 8) (hrdi : st.st.1.regs.get64 .rdi = t) (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ g : Val → MachineData, (∀ v, Keeps st.st.1 (g v) ∧ (g v).regs.get64 .rax = BitVec.setWidth 64 v) ∧
      isa.exec st = some (.load .plain false ⟨t, 8⟩ fun v => .done (goto st (g v) (pcT (i + 1)))) := by
  rcases hi with rfl | rfl
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cellD h 3 [hrdi, hdm, EvTree.access_of_agreesAt hag]; rfl⟩
    intro v; refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cellD h 11 [hrdi, hdm, EvTree.access_of_agreesAt hag]; rfl⟩
    intro v; refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp

/-- `movq %rax,8(%rbx)` (position 4): a plain store of the link. -/
theorem exec_st4 (st : State) (h : AtD st 4) {n : BitVec 64} (hag : st.decls.AgreesAt (n + 8#64) 8)
    (hrbx : st.st.1.regs.get64 .rbx = n) (hdm : Mem.loadInt st.st.1.dmem (n + 8#64) 8 = none) :
    isa.exec st = some (.store .plain false ⟨n + 8#64, 8⟩ (BitVec.setWidth 128 (st.st.1.regs.get64 .rax))
      fun _ => .done (goto st st.st.1 (pcT 5))) := by
  rw [next_pc h (by decide)]
  cellD h 4 [hrbx, ofInt_add8, hdm, EvTree.access_of_agreesAt hag]

/-- `lock cmpxchgq %R,(%rdi)` (positions 5 with `%rbx`, 15 with `%rcx`): a
locked (`acqRel`) RMW of `top` that writes `%R` iff the old value is `%rax`;
afterwards `ZF` iff it was, and `%rax` holds the old value. -/
theorem exec_cas (i : Nat) {r : Reg64} (hi : (i = 5 ∧ r = .rbx) ∨ (i = 15 ∧ r = .rcx)) (st : State) (h : AtD st i)
    {t : BitVec 64} (hag : st.decls.AgreesAt t 8) (hrdi : st.st.1.regs.get64 .rdi = t)
    (hdm : Mem.loadInt st.st.1.dmem t 8 = none) :
    ∃ g : Val → MachineData, (∀ v, Keeps st.st.1 (g v) ∧
        ((g v).status.zf = true ↔ BitVec.setWidth 64 v = st.st.1.regs.get64 .rax) ∧
        (g v).regs.get64 .rax = BitVec.setWidth 64 v) ∧
      isa.exec st = some (.rmw .acqRel false ⟨t, 8⟩
        (fun old => if BitVec.setWidth 64 old = st.st.1.regs.get64 .rax then
          some (BitVec.setWidth 128 (st.st.1.regs.get64 r)) else none)
        fun v => .done (goto st (g v) (pcT (i + 1)))) := by
  have hr : st.st.1.regs.get64 .rax = st.st.1.regs.rax.toBitVec := rfl
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cellD h 5 [hrdi, hdm, EvTree.access_of_agreesAt hag]; exact ⟨rfl, funext fun v => rfl⟩⟩
    intro v
    have hk : ∀ r' : Reg64, r' ≠ .rax → ∀ md : MachineData, (if BitVec.setWidth 64 v = st.st.1.regs.rax.toBitVec then md
        else { md with regs := md.regs.set64 .rax (BitVec.setWidth 64 v) }).regs.get64 r' = md.regs.get64 r' := by
      intro r' hr' md; split
      · rfl
      · cases r' <;> first | exact absurd rfl hr' | rfl
    refine ⟨⟨by split <;> rfl, ?_, ?_⟩, ?_, ?_⟩
    · exact hk .rdi (by decide) _
    · exact hk .rbx (by decide) _
    · change (st.st.1.regs.get64 .rax - BitVec.setWidth 64 v == 0#64) = true ↔ _
      simp only [beq_iff_eq]
      constructor <;> intro e <;> bv_omega
    · by_cases e : BitVec.setWidth 64 v = st.st.1.regs.get64 .rax
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ e))]; exact e.symm
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ e))]; simp
  · rw [next_pc h (by decide)]
    refine ⟨_, ?_, by cellD h 15 [hrdi, hdm, EvTree.access_of_agreesAt hag]; exact ⟨rfl, funext fun v => rfl⟩⟩
    intro v
    have hk : ∀ r' : Reg64, r' ≠ .rax → ∀ md : MachineData, (if BitVec.setWidth 64 v = st.st.1.regs.rax.toBitVec then md
        else { md with regs := md.regs.set64 .rax (BitVec.setWidth 64 v) }).regs.get64 r' = md.regs.get64 r' := by
      intro r' hr' md; split
      · rfl
      · cases r' <;> first | exact absurd rfl hr' | rfl
    refine ⟨⟨by split <;> rfl, ?_, ?_⟩, ?_, ?_⟩
    · exact hk .rdi (by decide) _
    · exact hk .rbx (by decide) _
    · change (st.st.1.regs.get64 .rax - BitVec.setWidth 64 v == 0#64) = true ↔ _
      simp only [beq_iff_eq]
      constructor <;> intro e <;> bv_omega
    · by_cases e : BitVec.setWidth 64 v = st.st.1.regs.get64 .rax
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hr ▸ e))]; exact e.symm
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (hr ▸ e))]; simp

/-- `jne push` (position 6): back to `push` unless `ZF`. -/
theorem exec_jne6 (st : State) (h : AtD st 6) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcT 7 else pcT 3))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cellD h 6 [hz]

/-- `jmp pdone` (position 7). -/
theorem exec_jmp7 (st : State) (h : AtD st 7) : isa.exec st = some (.done (goto st st.st.1 (pcT 9))) := by
  cellD h 7 []

/-- `testq %rax,%rax` (position 12): `ZF` iff `%rax = 0`. -/
theorem exec_test (st : State) (h : AtD st 12) :
    ∃ f : Fin 2 → MachineData, (∀ i, Keeps st.st.1 (f i) ∧ (f i).regs.get64 .rax = st.st.1.regs.get64 .rax ∧
        ((f i).status.zf = true ↔ st.st.1.regs.get64 .rax = 0#64)) ∧
      isa.exec st = some (.choose 2 fun i => .done (goto st (f i) (pcT 13))) := by
  rw [next_pc h (by decide)]
  refine ⟨?f, ?p, ?e⟩
  case e => cellD h 12 []; rfl
  intro i
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, ?_⟩
  change (st.st.1.regs.get64 .rax == 0#64) = true ↔ _
  simp only [beq_iff_eq]

/-- `je popper` (position 13): back to `popper` if `ZF`. -/
theorem exec_je13 (st : State) (h : AtD st 13) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcT 11 else pcT 14))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cellD h 13 [hz]

/-- `movq 8(%rax),%rcx` (position 14): a plain load of the link of the node
read, through the declarations. -/
theorem exec_ld14 (st : State) (h : AtD st 14)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.get64 .rax + 8#64) 8 = none) :
    ∃ g : Val → MachineData, (∀ v, Keeps st.st.1 (g v) ∧ (g v).regs.get64 .rax = st.st.1.regs.get64 .rax) ∧
      isa.exec st = some (EvTree.access st.decls (st.st.1.regs.get64 .rax + 8#64) 8 fun l =>
        .load .plain false l fun v => .done (goto st (g v) (pcT 15))) := by
  rw [next_pc h (by decide)]
  refine ⟨?f, ?p, ?e⟩
  case e =>
    have hdm' : Mem.loadInt st.st.1.dmem (st.st.1.regs.rax.toBitVec + 8#64) 8 = none := hdm
    cellD h 14 [ofInt_add8, hdm']
    unfold EvTree.access; split <;> rfl
  intro v
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp

/-- `jne popper` (position 16): back to `popper` unless `ZF`. -/
theorem exec_jne16 (st : State) (h : AtD st 16) :
    isa.exec st = some (.done (goto st st.st.1 (if st.st.1.status.zf then pcT 17 else pcT 11))) := by
  rw [next_pc h (by decide)]
  by_cases hz : st.st.1.status.zf <;> cellD h 16 [hz]

/-- `movq %rax,%r10` (position 17). -/
theorem exec_mov17 (st : State) (h : AtD st 17) :
    ∃ md : MachineData, Keeps st.st.1 md ∧ md.regs.get64 .rax = st.st.1.regs.get64 .rax ∧
      isa.exec st = some (.done (goto st md (pcT 18))) := by
  rw [next_pc h (by decide)]
  refine ⟨?f, ?p, ?q, ?e⟩
  case e => cellD h 17 []; rfl
  · exact ⟨rfl, by simp, by simp⟩
  · simp

/-- `movl (%rax),%r11d` (position 18): a plain load of the popped node's
data, through the declarations. -/
theorem exec_ld18 (st : State) (h : AtD st 18) (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.get64 .rax) 4 = none) :
    ∃ g : Val → MachineData, (∀ v, Keeps st.st.1 (g v) ∧ (g v).regs.get64 .rax = st.st.1.regs.get64 .rax) ∧
      isa.exec st = some (EvTree.access st.decls (st.st.1.regs.get64 .rax) 4 fun l =>
        .load .plain false l fun v => .done (goto st (g v) (pcT 19))) := by
  rw [next_pc h (by decide)]
  refine ⟨?f, ?p, ?e⟩
  case e =>
    have hdm' : Mem.loadInt st.st.1.dmem st.st.1.regs.rax.toBitVec 4 = none := hdm
    cellD h 18 [hdm']
    unfold EvTree.access; split <;> rfl
  intro v
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp

/-- `jmp qdone` (position 19). -/
theorem exec_jmp19 (st : State) (h : AtD st 19) : isa.exec st = some (.done (goto st st.st.1 (pcT 21))) := by
  cellD h 19 []

/-! ## Positions -/

/-- Is a directive an instruction (not a label)? -/
def isInstr : Directive → Bool
  | .label _ => false
  | _ => true

/-- The positions a thread's pc takes (each label at the address of the next
cell; `9` and `21` are the ends). -/
def tPcs : List Nat := [1, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21]

/-- The address-distinct representative of a position: the label before it. -/
def canon (i : Nat) : Nat :=
  if i = 3 then 2 else if i = 9 then 8 else if i = 11 then 10 else if i = 21 then 20 else i

theorem addrOf_canon (i : Nat) : pcT (canon i) = pcT i := by
  unfold canon
  split
  · subst_vars; exact (addrOf_label (i := 2) (l := "push") (by decide)).symm
  split
  · subst_vars; exact (addrOf_label (i := 8) (l := "pdone") (by decide)).symm
  split
  · subst_vars; exact (addrOf_label (i := 10) (l := "popper") (by decide)).symm
  split
  · subst_vars; exact (addrOf_label (i := 20) (l := "qdone") (by decide)).symm
  rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_inj {i j : Nat} (hi : i ∈ tPcs) (hj : j ∈ tPcs) (h : pcT i = pcT j) : i = j :=
  SLR.X64Trees.addrOf_inj_gen _ isInstr (fun _ => rfl) tPcs canon (fun i _ => addrOf_canon i) (by decide) hi hj h

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

end Kraken.Promising.Live.TreiberPpX64
