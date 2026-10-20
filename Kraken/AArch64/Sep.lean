import Kraken.AArch64.Semantics
import Kraken.Attribute
import Kraken.SeparationMem

open Std
open Std.ExtHashMap
open List

@[kspec]
theorem store_sep (s : MachineData) (addr : BitVec 64) (w : MemWidth) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    have mem' := Mem.storeInt s.dmem addr w.bytes v.toInt
    MachineData.store s addr v ret =
      require_write_access addr w (fun _ =>
        ret { s with dmem := mem' }) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.store, h_load]

@[kspec]
theorem load_sep (s : MachineData) (addr : BitVec 64) (w : MemWidth) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.load s addr w ret =
      require_read_access addr w (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.load,
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]

/-! The kinded accesses of the acquire/release, exclusive and atomic instructions
(`MachineData.loadK`/`storeK`/`rmwK`) on owned memory: their single-threaded
meaning, which is that of `load`/`store`. A store-exclusive may fail (`undefined
Bool`), and a read-modify-write writes only when `op` returns a value. Plain and
exclusive stores have separate lemmas, so that no `if` on the literal `xcl` is
left for `kstep` to reduce. -/

@[kspec]
theorem loadK_sep (s : MachineData) (k : Kraken.LoadKind) (xcl : Bool) (addr : BitVec 64)
    (w : MemWidth) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.loadK s k xcl addr w ret =
      require_read_access addr w (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.loadK,
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]

@[kspec]
theorem storeK_sep (s : MachineData) (k : Kraken.StoreKind) (addr : BitVec 64)
    (w : MemWidth) (v : w.type) (ret : Bool → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    have mem' := Mem.storeInt s.dmem addr w.bytes v.toInt
    MachineData.storeK s k false addr v ret =
      require_write_access addr w (fun _ => ret true { s with dmem := mem' }) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.storeK, h_load]
  rfl

/-- A store-exclusive: the outcome `ok` is `undefined`; the store happens only on
success. (A `match`, not an `if`, so that `kstep` reduces it once `ok` is
known, e.g. after `cases ok`.) -/
@[kspec]
theorem storeK_xcl_sep (s : MachineData) (k : Kraken.StoreKind) (addr : BitVec 64)
    (w : MemWidth) (v : w.type) (ret : Bool → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    have mem' := Mem.storeInt s.dmem addr w.bytes v.toInt
    MachineData.storeK s k true addr v ret =
      require_write_access addr w (fun _ =>
        undefined (α := Bool) (fun ok =>
          match ok with
          | true => ret true { s with dmem := mem' }
          | false => ret false s)) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.storeK, h_load, ite_true]
  congr; funext _; congr; funext ok; cases ok <;> rfl

@[kspec]
theorem rmwK_sep (s : MachineData) (k : Kraken.RmwKind) (noRet : Bool) (addr : BitVec 64) (w : MemWidth)
    (op : w.type → Option w.type) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.rmwK s k noRet addr w op ret =
      require_read_access addr w (fun _ => require_write_access addr w (fun _ =>
        match op (.ofInt w.bits (Int.ofBytes bs)) with
        | some new =>
          ret (.ofInt w.bits (Int.ofBytes bs)) { s with dmem := Mem.storeInt s.dmem addr w.bytes new.toInt }
        | none => ret (.ofInt w.bits (Int.ofBytes bs)) s)) := by
  have h_load : Mem.loadInt s.dmem addr w.bytes = some (Int.ofBytes bs) :=
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)
  simp only [MachineData.rmwK, h_load]
  rfl
