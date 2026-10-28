module

public import Kraken.X64.WP.Host

/-!
# A host for a literal program

`Host` collects assumptions about the assembler and the linker. A theorem
stated under `[Host]` would be vacuous if no host existed for its program;
`Host.ofChecks` builds one for a literal program and a literal layout from
checks that `decide` evaluates: one check per directive (`Host.cellOk`), the
uniqueness of labels, and a bound that keeps every address below `2 ^ 63`.
-/

public section

/-- The check of the directive at index `i` under `layout`: a label takes no space, an
instruction takes some, an `.align a` ends at a multiple of `a`, a data cell takes
exactly its bytes and is not empty. -/
@[expose] def Host.cellOk (prog : Program) (layout : Layout) (i : Nat) : Bool :=
  match prog[i]? with
  | some (.label _) => layout.size i == 0
  | some (.instr ins) => 0 < layout.size i &&
      match ins with
      | .regular _ _ (.nopalign a _) => isAligned a ((layout.apply prog).addrOf (i + 1)).toBitVec
      | _ => true
  | some (.byteArray bs) => layout.size i == bs.size && 0 < bs.size
  | some (.word w _) => layout.size i == w.bytes
  | none => true

theorem Directive.inert_label (l : Label) : (Directive.label l).Inert := by
  intro _ s p next jmp post
  rfl

/-- Beyond its last directive, an executable's offset stays at its size. -/
theorem Kraken.Executable.sizeBefore_le_length {e : Kraken.Executable Directive} (j : Nat) :
    e.sizeBefore j ≤ e.sizeBefore e.program.length := by
  rcases Nat.le_total j e.program.length with h | h
  · exact e.sizeBefore_mono h
  · simp only [Kraken.Executable.sizeBefore, List.take_of_length_le h, List.take_length, Nat.le_refl]

/-- Without wrap-around, the address of a directive is the start plus its offset. -/
theorem Kraken.Executable.toNat_addrOf {e : Kraken.Executable Directive} (j : Nat)
    (h : e.startAddr.toBitVec.toNat + e.sizeBefore e.program.length < 2 ^ 63) :
    (e.addrOf j).toBitVec.toNat = e.startAddr.toBitVec.toNat + e.sizeBefore j := by
  have := e.sizeBefore_le_length j
  simp only [Kraken.Executable.addrOf, Int64.toBitVec_add, Int64.toBitVec_ofNat', BitVec.toNat_add,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := e.sizeBefore j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A host for the literal program `prog` under the literal layout `layout`. -/
@[expose, instance_reducible] def Host.ofChecks (prog : Program) (layout : Layout)
    (h_nodup : (Program.labels prog).Nodup)
    (h_cells : ∀ i < prog.length, Host.cellOk prog layout i = true)
    (h_fit : layout.start.toBitVec.toNat + (layout.apply prog).sizeBefore prog.length < 2 ^ 63) :
    Host where
  prog := prog
  layout := layout
  labels_nodup := h_nodup
  label_size i l h := by
    have := h_cells i (List.getElem?_eq_some_iff.mp h).1
    simp only [Host.cellOk, h, beq_iff_eq] at this
    exact this
  instr_size_pos i ins h _ := by
    have := h_cells i (List.getElem?_eq_some_iff.mp h).1
    simp only [Host.cellOk, h, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  instr_addr_ne i _ _ := by
    have hlen : (layout.apply prog).program.length = prog.length := List.length_mapIdx
    have ha := Kraken.Executable.toNat_addrOf (e := layout.apply prog) i (by rw [hlen]; exact h_fit)
    have hle := (layout.apply prog).sizeBefore_le_length i
    have hs : (layout.apply prog).startAddr = layout.start := rfl
    rw [hlen] at hle
    rw [hs] at ha
    intro heq
    rw [heq] at ha
    have : (-1 : Int64).toBitVec.toNat = 2 ^ 64 - 1 := rfl
    omega
  zero_inert i d h hz := by
    have := h_cells i (List.getElem?_eq_some_iff.mp h).1
    cases d with
    | label l => intro _ s p next jmp post; rfl
    | instr ins =>
      simp only [Host.cellOk, h, Bool.and_eq_true, decide_eq_true_eq] at this
      omega
    | byteArray bs =>
      simp only [Host.cellOk, h, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      omega
    | word w e =>
      simp only [Host.cellOk, h, beq_iff_eq] at this
      cases w <;> simp_all
  addr_determines_offset j k h := by
    have hlen : (layout.apply prog).program.length = prog.length := List.length_mapIdx
    have hj := Kraken.Executable.toNat_addrOf (e := layout.apply prog) j (by rw [hlen]; exact h_fit)
    have hk := Kraken.Executable.toNat_addrOf (e := layout.apply prog) k (by rw [hlen]; exact h_fit)
    rw [h] at hj
    omega
  byteArray_size i bs h := by
    have := h_cells i (List.getElem?_eq_some_iff.mp h).1
    simp only [Host.cellOk, h, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  word_size i w e h := by
    have := h_cells i (List.getElem?_eq_some_iff.mp h).1
    simp only [Host.cellOk, h, beq_iff_eq] at this
    exact this
  align i asz osz a pad h := by
    have := h_cells i (List.getElem?_eq_some_iff.mp h).1
    simp only [Host.cellOk, h, Bool.and_eq_true] at this
    exact this.2

end
