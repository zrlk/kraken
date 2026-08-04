import Kraken.X64.Semantics
import Kraken.SeparationMem

open Std
open Std.ExtHashMap
open List

@[kspec]
theorem store_sep (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type) (ret : MachineData → Effects)
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
theorem load_sep (s : MachineData) (addr : BitVec 64) (w : Width) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.load s addr w ret =
      require_read_access addr w (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.load,
    Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]

@[kspec]
theorem loadAvx_sep (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.loadAvx s addr w ret false =
      require_read_access addr .W64 (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.loadAvx, isAligned]
  simp only [Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]
  -- Use reflexivity to evaluate the definitional equality and close the goal!
  rfl

@[kspec]
theorem storeAvx_sep (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes) :
    MachineData.storeAvx s addr v ret false =
      require_write_access addr .W64 (fun _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }) := by
  simp only [MachineData.storeAvx, isAligned]
  simp only [Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]
  rfl

@[kspec]
theorem loadAvx_sep_aligned (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes)
    (h_align : isAligned w.bytes addr = true) :
    MachineData.loadAvx s addr w ret true =
      require_read_access addr .W64 (fun _ => ret (.ofInt w.bits (Int.ofBytes bs)) s) := by
  simp only [MachineData.loadAvx, h_align, Bool.and_false, if_false]
  simp only [Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]
  rfl

@[kspec]
theorem storeAvx_sep_aligned (s : MachineData) (addr : BitVec 64) (w : AvxWidth) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R)
    (h_len : bs.length = w.bytes)
    (h_align : isAligned w.bytes addr = true) :
    MachineData.storeAvx s addr v ret true =
      require_write_access addr .W64 (fun _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }) := by
  simp only [MachineData.storeAvx, h_align, Bool.and_false, if_false]
  simp only [Mem.loadInt_sep bs addr w.bytes R s.dmem h_mem h_len (by cases w <;> decide)]
  rfl
