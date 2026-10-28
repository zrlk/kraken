module

public import Kraken.X64.WP.Image
import all Kraken.SeparationMem

/-!
# Writable data

An object file keeps mutable globals in `.data` (initialised) and `.bss`
(zero, written `.zero n`). Kraken programs have no sections; a data cell is
writable when the label in front of it is listed in `Host.Writable.rw`.

The image splits into its read-only and its writable cells:
`Host.Image ⋆ F = Host.ImageRO ⋆ (Host.ImageRW ⋆ F)`
(`Host.Image_eq_ro_rw`). The read-only part is the static frame's share of a
contract (`Program.WP.StaticPreRO`); a procedure that writes a global takes the
global's cell out of `Host.ImageRW` (`Host.ImageRW.split`) and states its new
bytes in its postcondition.

The image describes data memory as the loader leaves it, so `Host.ImageRW`
holds only at the start of a run; after a write, a postcondition states the
written cell with its new bytes beside `Host.ImageRWExcept`.
-/

public section

/-- The labels whose data cells are writable (`.data`, `.bss`). -/
class Host.Writable [Host] where
  rw : List Label

/-- By default, no data is writable. -/
@[instance_reducible] instance (priority := low) Host.Writable.none [Host] : Host.Writable := ⟨[]⟩

/-- Whether a data cell is writable: its address is that of a writable label. -/
@[expose] def Host.isRW [Host] [Host.Writable] (c : BitVec 64 × List UInt8) : Bool :=
  Host.Writable.rw.any fun l => (label l).toBitVec == c.1

/-- The writable cells of the image. -/
@[expose] def Host.ImageRW [Host] [Host.Writable] : DataMem → Prop :=
  Mem.Cells (Host.dataCells.filter Host.isRW)

/-- The read-only cells of the image. -/
@[expose] def Host.ImageRO [Host] [Host.Writable] : DataMem → Prop :=
  Mem.Cells (Host.dataCells.filter fun c => !Host.isRW c)

/-- The writable cells without the cell `bs` after the label `l`. -/
@[expose] def Host.ImageRWExcept [Host] [Host.Writable] (l : Label) (bs : List UInt8) :
    DataMem → Prop :=
  Mem.Cells ((Host.dataCells.filter Host.isRW).erase ((label l).toBitVec, bs))

variable [Host]

/-- Overwrite a cell of `n` bytes with the `n` bytes of `v`. -/
theorem Host.ImageAt.storeInt {m : DataMem} {F : DataMem → Prop} {l : Label} {bs : List UInt8}
    {n : Nat} (h : m =⋆ Host.ImageAt l bs ⋆ F) (hn : bs.length = n) (v : Int) :
    Mem.storeInt m (label l).toBitVec n v =⋆ Host.ImageAt l (Int.toBytes n v) ⋆ F :=
  Mem.storeInt_sep _ n bs F m ⟨h, hn⟩ v

/-- A load of the whole cell after `l` reads its bytes. -/
theorem Host.ImageAt.loadInt {m : DataMem} {F : DataMem → Prop} {l : Label} {bs : List UInt8}
    {n : Nat} (h : m =⋆ Host.ImageAt l bs ⋆ F) (hn : bs.length = n) (hw : n ≤ 2 ^ 64) :
    Mem.loadInt m (label l).toBitVec n = some (Int.ofBytes bs) :=
  Mem.loadInt_sep bs _ n F m h hn hw

/-- With no writable label, the read-only cells are the whole image. -/
theorem Host.ImageRO_none :
    @Host.ImageRO _ Host.Writable.none = Host.Image := by
  show Mem.Cells (Host.dataCells.filter fun c =>
    !(([] : List Label).any fun l => (label l).toBitVec == c.1)) = Mem.Cells Host.dataCells
  simp only [List.any_nil, Bool.not_false]
  rw [List.filter_eq_self.mpr fun _ _ => rfl]

variable [Host.Writable]

/-- The image is its read-only cells and its writable cells. -/
theorem Host.Image_eq_ro_rw (F : DataMem → Prop) :
    Host.Image ⋆ F = Host.ImageRO ⋆ (Host.ImageRW ⋆ F) := by
  rw [Host.Image, Host.ImageRO, Host.ImageRW, ← Mem.Cells_append_sep]
  exact Mem.Cells_perm_sep ((List.filter_append_perm _ _).symm.trans List.perm_append_comm) F

/-- A cell of the image after a writable label is a writable cell. -/
theorem Host.mem_rwCells {l : Label} {bs : List UInt8}
    (hc : ((label l).toBitVec, bs) ∈ Host.dataCells) (hl : l ∈ Host.Writable.rw) :
    ((label l).toBitVec, bs) ∈ Host.dataCells.filter Host.isRW :=
  List.mem_filter.mpr ⟨hc, List.any_eq_true.mpr ⟨l, hl, beq_self_eq_true _⟩⟩

/-- Carve the writable cell after the label `l` out of the writable image. -/
theorem Host.ImageRW.split {l : Label} {bs : List UInt8}
    (hc : ((label l).toBitVec, bs) ∈ Host.dataCells) (hl : l ∈ Host.Writable.rw)
    (F : DataMem → Prop) :
    Host.ImageRW ⋆ F = Host.ImageAt l bs ⋆ (Host.ImageRWExcept l bs ⋆ F) :=
  Mem.Cells_erase_sep (Host.mem_rwCells hc hl) F


end
