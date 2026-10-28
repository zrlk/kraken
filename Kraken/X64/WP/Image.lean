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

/-- The data cells of the host program, address and bytes, in program order. -/
@[expose] def Host.dataCells [Host] : List (BitVec 64 × List UInt8) :=
  (List.range Host.prog.length).filterMap fun i =>
    match Host.prog[i]? with
    | some (Directive.byteArray bs) => some ((Host.addrOf i).toBitVec, bs.data.toList)
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

end
