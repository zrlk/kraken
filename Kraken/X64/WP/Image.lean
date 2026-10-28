module

public import Kraken.X64.WP.Host
public import Kraken.SeparationMem
import all Kraken.SeparationMem

/-!
# The loaded image

The data cells of the host program (`.byte` runs, placed by the layout like
every other directive) are the program's image in data memory. `Host.Image`
says that all of them are loaded: each cell's bytes sit at its address,
separated from each other. A theorem about code that reads constants states
`d.dmem =⋆ Host.Image ⋆ R` once instead of listing each constant.

The lemmas below carve the cell after one label out of the image
(`Host.Image.split`) and feed the `Mem.Contains`/`Mem.Bytes` lemmas that the
instruction rules and `grind` use (`Host.Image.contains`,
`Host.Image.loadInt_eq`, `Host.Image.loadInt_isSome`). All of them take the
position of the cell in an embedded fragment, so `Host.dataCells` is never
computed.
-/

public section

/-- The bytes of the data word `.word w e` at index `i` of the host program: the value of
`e`, with `.` read as the word's own address range, little-endian in `w.bytes` bytes. The
assembler rejects a value that does not fit, so the truncation never applies to a word
it accepted. -/
@[expose] def Host.wordBytes [Host] (i : Nat) (w : Width) (e : ConstExpr) : List UInt8 :=
  Int.toBytes w.bytes (e.interp ⟨Host.addrOf i, Host.addrOf (i + 1)⟩).toInt

/-- The data cells of the host program, address and bytes, in program order: the `.byte`
cells and the data words. -/
@[expose] def Host.dataCells [Host] : List (BitVec 64 × List UInt8) :=
  (List.range Host.prog.length).filterMap fun i =>
    match Host.prog[i]? with
    | some (Directive.byteArray bs) => some ((Host.addrOf i).toBitVec, bs.data.toList)
    | some (Directive.word w e) => some ((Host.addrOf i).toBitVec, Host.wordBytes i w e)
    | _ => none

/-- The image is loaded: every data cell of the host program holds its bytes. -/
@[expose] def Host.Image [Host] : DataMem → Prop := Mem.Cells Host.dataCells

/-- The cell right after the label `l` holds `bs`. The bytes are an argument so that a
specification can state them literally; `Host.Image.split` justifies the literal. -/
@[expose] def Host.ImageAt [Host] (l : Label) (bs : List UInt8) : DataMem → Prop :=
  Mem.Bytes (label l).toBitVec bs

/-- The image without the cell `bs` after the label `l`. -/
@[expose] def Host.ImageExcept [Host] (l : Label) (bs : List UInt8) : DataMem → Prop :=
  Mem.Cells (Host.dataCells.erase ((label l).toBitVec, bs))

variable [Host]

theorem Host.mem_dataCells {i : Nat} {bs : ByteArray} (h : Host.prog[i]? = some (.byteArray bs)) :
    ((Host.addrOf i).toBitVec, bs.data.toList) ∈ Host.dataCells := by
  refine List.mem_filterMap.mpr ⟨i, List.mem_range.mpr ?_, by rw [h]⟩
  exact (List.getElem?_eq_some_iff.mp h).1

/-- The cell after the label `l` of an embedded fragment is a cell of the image. -/
theorem Host.dataCells_mem {p : Program} {k i : Nat} {l : Label} {bs : ByteArray}
    (hp : p.IsInfixAt Host.prog k) (hl : p[i]? = some (.label l))
    (hb : p[i + 1]? = some (.byteArray bs)) :
    ((label l).toBitVec, bs.data.toList) ∈ Host.dataCells := by
  rw [Host.label_succ_addr hp hl]
  exact Host.mem_dataCells (by rw [← Host.getElem?_of_isInfixAt hp hb, Nat.add_assoc])

/-- Carve the cell after the label `l` out of the image. -/
theorem Host.Image.split {p : Program} {k i : Nat} {l : Label} {bs : ByteArray}
    (hp : p.IsInfixAt Host.prog k) (hl : p[i]? = some (.label l))
    (hb : p[i + 1]? = some (.byteArray bs)) (F : DataMem → Prop) :
    Host.Image ⋆ F = Host.ImageAt l bs.data.toList ⋆ (Host.ImageExcept l bs.data.toList ⋆ F) :=
  Mem.Cells_erase_sep (Host.dataCells_mem hp hl hb) F

/-- The image holds the bytes of the cell after every data label. -/
theorem Host.Image.contains {m : DataMem} {F : DataMem → Prop} (h : m =⋆ Host.Image ⋆ F)
    {p : Program} {k i : Nat} {l : Label} {bs : ByteArray}
    (hp : p.IsInfixAt Host.prog k) (hl : p[i]? = some (.label l))
    (hb : p[i + 1]? = some (.byteArray bs)) (hw : bs.size ≤ 2 ^ 64) :
    Mem.Contains m (label l).toBitVec bs.data.toList :=
  Mem.Cells.contains h (Host.dataCells_mem hp hl hb) (by rw [Array.length_toList]; exact hw)

/-- A load of the whole cell after `l` reads its bytes. -/
theorem Host.Image.loadInt_eq {m : DataMem} {F : DataMem → Prop} (h : m =⋆ Host.Image ⋆ F)
    {p : Program} {k i : Nat} {l : Label} {bs : ByteArray}
    (hp : p.IsInfixAt Host.prog k) (hl : p[i]? = some (.label l))
    (hb : p[i + 1]? = some (.byteArray bs)) {n : Nat} (hn : bs.size = n) (hw : n ≤ 2 ^ 64) :
    Mem.loadInt m (label l).toBitVec n = some (Int.ofBytes bs.data.toList) :=
  (Host.Image.contains h hp hl hb (hn ▸ hw)).loadInt_eq (by rw [Array.length_toList]; exact hn)

/-- A load inside the cell after `l` succeeds. -/
theorem Host.Image.loadInt_isSome {m : DataMem} {F : DataMem → Prop} (h : m =⋆ Host.Image ⋆ F)
    {p : Program} {k i : Nat} {l : Label} {bs : ByteArray}
    (hp : p.IsInfixAt Host.prog k) (hl : p[i]? = some (.label l))
    (hb : p[i + 1]? = some (.byteArray bs)) {o n : Nat} (hin : o + n ≤ bs.size)
    (hw : bs.size ≤ 2 ^ 64) :
    (Mem.loadInt m ((label l).toBitVec + BitVec.ofNat 64 o) n).isSome = true := by
  rw [Host.Image, Mem.Cells_erase_sep (Host.dataCells_mem hp hl hb), Mem.Bytes] at h
  have hlen : bs.data.toList.length = bs.size := Array.length_toList
  rw [Mem.loadInt_slice h ?_ (by omega)]
  · rfl
  · rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
    have := Nat.mod_le o (2 ^ 64)
    omega

/-! ### Data words -/

theorem Host.mem_dataCells_word {i : Nat} {w : Width} {e : ConstExpr}
    (h : Host.prog[i]? = some (.word w e)) :
    ((Host.addrOf i).toBitVec, Host.wordBytes i w e) ∈ Host.dataCells := by
  refine List.mem_filterMap.mpr ⟨i, List.mem_range.mpr ?_, by rw [h]⟩
  exact (List.getElem?_eq_some_iff.mp h).1

omit [Host] in
theorem Width.bytes_le_eight (w : Width) : w.bytes ≤ 8 := by
  cases w <;> decide

/-- A load of a data word reads its bytes. -/
theorem Host.Image.loadInt_word {m : DataMem} {F : DataMem → Prop} (h : m =⋆ Host.Image ⋆ F)
    {i : Nat} {w : Width} {e : ConstExpr} (hi : Host.prog[i]? = some (.word w e)) :
    Mem.loadInt m (Host.addrOf i).toBitVec w.bytes = some (Int.ofBytes (Host.wordBytes i w e)) := by
  have hlen : (Host.wordBytes i w e).length = w.bytes := Int.toBytes_length _ _
  have hw := Width.bytes_le_eight w
  exact (Mem.Cells.contains h (Host.mem_dataCells_word hi) (by omega)).loadInt_eq hlen

/-- A run of `n` data words of width `w` from index `k` occupies `n * w.bytes` bytes. -/
theorem Host.addrOf_words {k n : Nat} {w : Width}
    (hw : ∀ j < n, ∃ e, Host.prog[k + j]? = some (.word w e)) :
    Host.addrOf (k + n) = Host.addrOf k + .ofNat (n * w.bytes) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨e, he⟩ := hw n (by omega)
    rw [← Nat.add_assoc, Host.addrOf_succ he, Host.word_size _ w e he,
      ih fun j hj => hw j (by omega), Int64.add_assoc, ← Int64.ofNat_add, Nat.succ_mul]

/-- An entry `.long t - b` of a table that starts at the label `b`: the `j`-th word after
`b` reads back as the signed 32-bit offset of `t` from `b`, if the offset fits. -/
theorem Host.word_value {m : DataMem} {F : DataMem → Prop} (h : m =⋆ Host.Image ⋆ F)
    {p : Program} {k i j : Nat} {b t : Label}
    (hp : p.IsInfixAt Host.prog k) (hb : p[i]? = some (.label b))
    (hpre : ∀ j' < j, ∃ e, p[i + 1 + j']? = some (.word .W32 e))
    (hj : p[i + 1 + j]? = some (.word .W32 (.sub (.label t) (.label b))))
    (hrange : -2 ^ 31 ≤ (label t - label b).toInt ∧ (label t - label b).toInt < 2 ^ 31) :
    ∃ v, Mem.loadInt m ((label b).toBitVec + BitVec.ofNat 64 (4 * j)) 4 = some v
      ∧ (BitVec.ofInt 32 v).signExtend 64 + (label b).toBitVec = (label t).toBitVec := by
  have hP : Host.prog[k + i + 1 + j]? = some (.word .W32 (.sub (.label t) (.label b))) := by
    rw [← Host.getElem?_of_isInfixAt hp hj]; congr 1; omega
  have haddr : (Host.addrOf (k + i + 1 + j)).toBitVec = (label b).toBitVec + BitVec.ofNat 64 (4 * j) := by
    rw [Host.addrOf_words (w := .W32) (fun j' hj' => by
        obtain ⟨e, he⟩ := hpre j' hj'
        exact ⟨e, by rw [← Host.getElem?_of_isInfixAt hp he]; congr 1; omega⟩),
      ← Host.label_succ_addr hp hb, Int64.toBitVec_add, Nat.mul_comm]
    rfl
  refine ⟨_, haddr ▸ Host.Image.loadInt_word h hP, ?_⟩
  simp only [Host.wordBytes, ConstExpr.interp]
  rw [BitVec.ofInt_ofBytes_toBytes 32 4 rfl]
  have hse : (BitVec.ofInt 32 (label t - label b).toInt).signExtend 64 = (label t - label b).toBitVec := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt,
      Int.bmod_eq_of_le (by omega) (by omega)]
    rfl
  rw [hse, Int64.toBitVec_sub, BitVec.sub_add_cancel]

end
