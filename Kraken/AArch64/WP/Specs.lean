/-
The AArch64 register, flag and address API the machine-founded wp discharges
against, in the style of x64's `Kraken/Specs.lean` (written for AArch64, not
copied): register reads by name and over writes (`getXReg`/`setXReg`, the
`RegOrZr`/`RegOrSp` views with `XZR` reading zero and dropping writes, `W`
writes zero-extending), the `MachineData` record projections, the `NZCV` flags
`StatusFlags.from_result`/`adds`/`subs` compute, the condition codes, and the
addresses `AddrExpr.eval` computes (base plus immediate, pre- and post-index
writeback, register offset with extend and shift).
-/
import Kraken.AArch64.OmniSemantics
import Kraken.GrindFold
import Std.Tactic.Do

/-! ## `.unsigned`/`.signed`/`.take` reductions -/

@[grind hom] theorem BitVec.unsigned_hom {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl
@[simp] theorem BitVec.unsigned_eq {w} (x : BitVec w) : x.unsigned = (x.toNat : Int) := rfl
@[simp] theorem BitVec.signed_eq {w} (x : BitVec w) : x.signed = x.toInt := rfl

/-- Taking all the bits of a value is the value. -/
@[simp, grind =] theorem BitVec.take_self {w} (x : BitVec w) : x.take w = x := by
  simp [BitVec.take]

/-- Taking the low bits of a value is truncating it. -/
@[grind =] theorem BitVec.take_eq_setWidth {w} (x : BitVec w) (n : Nat) :
    x.take n = x.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

/-! ## Immediates

An immediate reaches a VC as the payload of an `Int64` literal, through
`Int64.toInt`. -/

@[simp, grind =] theorem BitVec.ofInt_toInt_int64 (c : Int64) :
    BitVec.ofInt 64 c.toInt = c.toBitVec := by
  rw [show c.toInt = c.toBitVec.toInt from rfl, BitVec.ofInt_toInt]

/-- A 32-bit operation reads the low half of an immediate. -/
@[simp, grind =] theorem BitVec.ofInt32_toInt_int64 (c : Int64) :
    BitVec.ofInt 32 c.toInt = c.toBitVec.setWidth 32 := by
  rw [show c.toInt = c.toBitVec.toInt from rfl]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, ← BitVec.signExtend_eq_setWidth_of_le _ (by decide : 32 ≤ 64)]
  simp [BitVec.toInt_signExtend]

@[grind =] theorem Int64.toBitVec_lit (n : Nat) :
    (OfNat.ofNat n : Int64).toBitVec = BitVec.ofNat 64 n := rfl

/-- An immediate's payload as a `BitVec` literal (`no_index` lets it match the
numeral). `MachineWP` registers it with `grind`'s normalizer, as x64 does. -/
theorem Int64.toBitVec_ofNat_norm (n : Nat) :
    (no_index (OfNat.ofNat n : Int64)).toBitVec = BitVec.ofNat 64 n := rfl

/-- A negative immediate, likewise: the parser writes it as the negation of a
literal. -/
theorem Int64.toBitVec_neg_ofNat_norm (n : Nat) :
    (-(no_index (OfNat.ofNat n : Int64))).toBitVec
      = BitVec.ofNat 64 (2 ^ 64 - n % 2 ^ 64) := by
  rw [Int64.toBitVec_neg, Int64.toBitVec_ofNat_norm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]

@[simp, grind =] theorem ConstExpr.interp_int64 [Labels] (i : Int64) (p : Std.Rco Int64) :
    (ConstExpr.int64 i).interp p = i := rfl

@[simp, grind =] theorem ConstExpr.interp_label [Labels] (l : Label) (p : Std.Rco Int64) :
    (ConstExpr.label l).interp p = Labels.label l := rfl

/-! ## Register identity as a number

A read-over-write condition between two register literals is decided by
comparing their indices, as x64's `Reg64.idx`. It is `wpIdx`, not `idx`:
`Kraken.AArch64.Deps` has a `Fin 31`-valued `XReg.idx`, and the two must be
importable together (`Kraken.Promising.SeqLinkAArch64Step`). -/

def XReg.wpIdx : XReg → Nat
  |  .X0 =>  0 |  .X1 =>  1 |  .X2 =>  2 |  .X3 =>  3 |  .X4 =>  4 |  .X5 =>  5
  |  .X6 =>  6 |  .X7 =>  7 |  .X8 =>  8 |  .X9 =>  9 | .X10 => 10 | .X11 => 11
  | .X12 => 12 | .X13 => 13 | .X14 => 14 | .X15 => 15 | .X16 => 16 | .X17 => 17
  | .X18 => 18 | .X19 => 19 | .X20 => 20 | .X21 => 21 | .X22 => 22 | .X23 => 23
  | .X24 => 24 | .X25 => 25 | .X26 => 26 | .X27 => 27 | .X28 => 28 | .X29 => 29
  | .X30 => 30

theorem XReg.eq_eq_idx_eq (r r' : XReg) : (r = r') = (r.wpIdx = r'.wpIdx) := by
  cases r <;> cases r' <;> simp [XReg.wpIdx]

/-! ## Register read-over-write API

A register is read through `getXReg` (a `UInt64` field) and written through
`setXReg` (a `BitVec 64`). The views `getRegOrZr`/`getRegOrSp` and
`setRegOrZr`/`setRegOrSp` the instructions use reduce to these at a register
literal: `XZR` reads zero and drops writes, a `W` read is the low half, and a
`W` write zero-extends into the `X` register. -/

@[simp, grind =] theorem Reg64s.getXReg_setXReg (s : Reg64s) (r r' : XReg) (v : BitVec 64) :
    (s.setXReg r v).getXReg r' = if r' = r then .ofBitVec v else s.getXReg r' := by
  cases r <;> cases r' <;> rfl

@[simp, grind =] theorem Reg64s.setXReg_setXReg (s : Reg64s) (r : XReg) (v w : BitVec 64) :
    (s.setXReg r v).setXReg r w = s.setXReg r w := by
  cases r <;> rfl

@[simp, grind =] theorem Reg64s.setXReg_getXReg (s : Reg64s) (r : XReg) :
    s.setXReg r (s.getXReg r).toBitVec = s := by
  cases r <;> simp [Reg64s.setXReg, Reg64s.getXReg]

@[simp, grind =] theorem Reg64s.getRegOrZr_X (s : Reg64s) (r : XReg) :
    s.getRegOrZr (.low (.reg r) .W64) = (s.getXReg r).toBitVec := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base]

@[simp, grind =] theorem Reg64s.getRegOrZr_W (s : Reg64s) (r : XReg) :
    s.getRegOrZr (.low (.reg r) .W32) = (s.getXReg r).toBitVec.setWidth 32 := by
  simp [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take_eq_setWidth]

@[simp, grind =] theorem Reg64s.getRegOrZr_XZR (s : Reg64s) (w : RegWidth) :
    s.getRegOrZr (.low .XZR w) = 0 := by
  cases w <;> rfl

@[simp, grind =] theorem Reg64s.getRegOrSp_X (s : Reg64s) (r : XReg) :
    s.getRegOrSp (.low (.reg r) .W64) = (s.getXReg r).toBitVec := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base]

@[simp, grind =] theorem Reg64s.getRegOrSp_W (s : Reg64s) (r : XReg) :
    s.getRegOrSp (.low (.reg r) .W32) = (s.getXReg r).toBitVec.setWidth 32 := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take_eq_setWidth]

@[simp, grind =] theorem Reg64s.getRegOrSp_SP (s : Reg64s) :
    s.getRegOrSp (.low .SP .W64) = s.SP.toBitVec := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base]

@[simp, grind =] theorem Reg64s.getRegOrSp_WSP (s : Reg64s) :
    s.getRegOrSp (.low .SP .W32) = s.SP.toBitVec.setWidth 32 := by
  simp [Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, BitVec.take_eq_setWidth]

@[simp, grind =] theorem Reg64s.setRegOrZr_X (s : Reg64s) (r : XReg) (v : BitVec 64) :
    s.setRegOrZr (.low (.reg r) .W64) v = s.setXReg r v := rfl

/-- A `W` write zero-extends into the `X` register. -/
@[simp, grind =] theorem Reg64s.setRegOrZr_W (s : Reg64s) (r : XReg) (v : BitVec 32) :
    s.setRegOrZr (.low (.reg r) .W32) v = s.setXReg r (v.setWidth 64) := rfl

/-- A write to the zero register is dropped. -/
@[simp, grind =] theorem Reg64s.setRegOrZr_XZR (s : Reg64s) (w : RegWidth) (v : w.type) :
    s.setRegOrZr (.low .XZR w) v = s := by
  cases w <;> rfl

@[simp, grind =] theorem Reg64s.setRegOrSp_X (s : Reg64s) (r : XReg) (v : BitVec 64) :
    s.setRegOrSp (.low (.reg r) .W64) v = s.setXReg r v := rfl

@[simp, grind =] theorem Reg64s.setRegOrSp_W (s : Reg64s) (r : XReg) (v : BitVec 32) :
    s.setRegOrSp (.low (.reg r) .W32) v = s.setXReg r (v.setWidth 64) := rfl

@[simp, grind =] theorem Reg64s.setRegOrSp_SP (s : Reg64s) (v : BitVec 64) :
    s.setRegOrSp (.low .SP .W64) v = { s with SP := .ofBitVec v } := rfl

@[simp, grind =] theorem Reg64s.setRegOrSp_WSP (s : Reg64s) (v : BitVec 32) :
    s.setRegOrSp (.low .SP .W32) v = { s with SP := .ofBitVec (v.setWidth 64) } := rfl

@[simp, grind =] theorem Reg64s.getXReg_set_SP (s : Reg64s) (r : XReg) (v : UInt64) :
    ({ s with SP := v } : Reg64s).getXReg r = s.getXReg r := by
  cases r <;> rfl

/-! ## The `MachineData` record -/

@[simp] theorem MachineData.regs_mk (r st d) : (MachineData.mk r st d).regs = r := rfl
@[simp] theorem MachineData.status_mk (r st d) : (MachineData.mk r st d).status = st := rfl
@[simp] theorem MachineData.dmem_mk (r st d) : (MachineData.mk r st d).dmem = d := rfl

/-! ## Machine words in `grind`'s arithmetic -/

@[grind =] theorem UInt64.toNat_payload (x : UInt64) : x.toBitVec.toNat = x.toNat := rfl

@[grind .] theorem UInt64.lt_size (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt

attribute [grind =] BitVec.ofInt_toInt BitVec.toNat_setWidth

@[grind =] theorem BitVec.setWidth_64_64 (x : BitVec 64) :
    BitVec.setWidth 64 x = x := BitVec.setWidth_eq x

/-! ## Flags

`StatusFlags.from_result` computes `N` and `Z` from the result and takes `C`
and `V` as given; `adds`/`subs` supply the carry and overflow of an addition
and a subtraction. Simp unfolds the three (they are `@[simp]` definitions);
`grind` reads them through the projections below. -/

@[simp, grind =] theorem StatusFlags.n_from_result {w} (r : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result r f).n = r.msb := rfl

@[simp, grind =] theorem StatusFlags.z_from_result {w} (r : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result r f).z = (r == BitVec.zero w) := rfl

@[simp, grind =] theorem StatusFlags.c_from_result {w} (r : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result r f).c = f.c := rfl

@[simp, grind =] theorem StatusFlags.v_from_result {w} (r : BitVec w)
    (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result r f).v = f.v := rfl

@[simp] theorem StatusFlags.from_result.Remaining.c_mk (c v : Bool) :
    (StatusFlags.from_result.Remaining.mk c v).c = c := rfl

@[simp] theorem StatusFlags.from_result.Remaining.v_mk (c v : Bool) :
    (StatusFlags.from_result.Remaining.mk c v).v = v := rfl

@[grind =] theorem StatusFlags.adds_eq {w} (r a b : BitVec w) :
    StatusFlags.adds r a b = StatusFlags.from_result r
      { c := r.unsigned != a.unsigned + b.unsigned, v := r.signed != a.signed + b.signed } := rfl

@[grind =] theorem StatusFlags.subs_eq {w} (r a b : BitVec w) :
    StatusFlags.subs r a b = StatusFlags.from_result r
      { c := r.unsigned == a.unsigned - b.unsigned, v := r.signed != a.signed - b.signed } := rfl

@[simp, grind =] theorem StatusFlags.n_ofNat (k : Nat) : (StatusFlags.ofNat k).n = ((k &&& 8) != 0) := rfl
@[simp, grind =] theorem StatusFlags.z_ofNat (k : Nat) : (StatusFlags.ofNat k).z = ((k &&& 4) != 0) := rfl
@[simp, grind =] theorem StatusFlags.c_ofNat (k : Nat) : (StatusFlags.ofNat k).c = ((k &&& 2) != 0) := rfl
@[simp, grind =] theorem StatusFlags.v_ofNat (k : Nat) : (StatusFlags.ofNat k).v = ((k &&& 1) != 0) := rfl

@[simp] theorem StatusFlags.n_mk (n z c v : Bool) : (StatusFlags.mk n z c v).n = n := rfl
@[simp] theorem StatusFlags.z_mk (n z c v : Bool) : (StatusFlags.mk n z c v).z = z := rfl
@[simp] theorem StatusFlags.c_mk (n z c v : Bool) : (StatusFlags.mk n z c v).c = c := rfl
@[simp] theorem StatusFlags.v_mk (n z c v : Bool) : (StatusFlags.mk n z c v).v = v := rfl

/-! ## Condition-code reductions, one lemma per code -/

@[simp, grind =] theorem CondCode.interp_EQ (s : StatusFlags) : CondCode.EQ.interp s = s.z := rfl
@[simp, grind =] theorem CondCode.interp_NE (s : StatusFlags) : CondCode.NE.interp s = !s.z := rfl
@[simp, grind =] theorem CondCode.interp_CS (s : StatusFlags) : CondCode.CS.interp s = s.c := rfl
@[simp, grind =] theorem CondCode.interp_CC (s : StatusFlags) : CondCode.CC.interp s = !s.c := rfl
@[simp, grind =] theorem CondCode.interp_MI (s : StatusFlags) : CondCode.MI.interp s = s.n := rfl
@[simp, grind =] theorem CondCode.interp_PL (s : StatusFlags) : CondCode.PL.interp s = !s.n := rfl
@[simp, grind =] theorem CondCode.interp_VS (s : StatusFlags) : CondCode.VS.interp s = s.v := rfl
@[simp, grind =] theorem CondCode.interp_VC (s : StatusFlags) : CondCode.VC.interp s = !s.v := rfl
@[simp, grind =] theorem CondCode.interp_HI (s : StatusFlags) :
    CondCode.HI.interp s = (s.c && !s.z) := rfl
@[simp, grind =] theorem CondCode.interp_LS (s : StatusFlags) :
    CondCode.LS.interp s = (!s.c || s.z) := rfl
@[simp, grind =] theorem CondCode.interp_GE (s : StatusFlags) :
    CondCode.GE.interp s = (s.n == s.v) := rfl
@[simp, grind =] theorem CondCode.interp_LT (s : StatusFlags) :
    CondCode.LT.interp s = (s.n != s.v) := rfl
@[simp, grind =] theorem CondCode.interp_GT (s : StatusFlags) :
    CondCode.GT.interp s = (!s.z && s.n == s.v) := rfl
@[simp, grind =] theorem CondCode.interp_LE (s : StatusFlags) :
    CondCode.LE.interp s = (s.z || s.n != s.v) := rfl
@[simp, grind =] theorem CondCode.interp_AL (s : StatusFlags) : CondCode.AL.interp s = true := rfl
@[simp, grind =] theorem CondCode.interp_NV (s : StatusFlags) : CondCode.NV.interp s = true := rfl

/-! ## Addresses

`AddrExpr.eval` returns the address of an access and the state after any base
writeback. With an immediate offset the address is the base plus the offset
(offset and pre-index) or the base (post-index), and pre- and post-index write
the base plus the offset back to the base register. With a register offset the
address is the base plus the extended, shifted index register. -/

/-- `[Xn|SP, #imm]`: the base plus the offset, no writeback. -/
@[simp, grind =] theorem AddrExpr.eval_imm [Labels] (b : RegOrSp .W64) (i : ConstExpr)
    (s : MachineData) (p : Std.Rco Int64) :
    AddrExpr.eval ⟨b, .imm ⟨i, none⟩⟩ s p
      = (s.regs.getRegOrSp b + (i.interp p).toBitVec, s) := by
  simp only [AddrExpr.eval, BitVec.signed_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt_int64]

/-- `[Xn|SP, #imm]!`: the base plus the offset, written back. -/
@[simp, grind =] theorem AddrExpr.eval_pre [Labels] (b : RegOrSp .W64) (i : ConstExpr)
    (s : MachineData) (p : Std.Rco Int64) :
    AddrExpr.eval ⟨b, .imm ⟨i, some .Pre⟩⟩ s p
      = (s.regs.getRegOrSp b + (i.interp p).toBitVec,
         { s with regs := s.regs.setRegOrSp b (s.regs.getRegOrSp b + (i.interp p).toBitVec) }) := by
  simp only [AddrExpr.eval, BitVec.signed_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt_int64]

/-- `[Xn|SP], #imm`: the base, then the base plus the offset written back. -/
@[simp, grind =] theorem AddrExpr.eval_post [Labels] (b : RegOrSp .W64) (i : ConstExpr)
    (s : MachineData) (p : Std.Rco Int64) :
    AddrExpr.eval ⟨b, .imm ⟨i, some .Post⟩⟩ s p
      = (s.regs.getRegOrSp b,
         { s with regs := s.regs.setRegOrSp b (s.regs.getRegOrSp b + (i.interp p).toBitVec) }) := by
  simp only [AddrExpr.eval, BitVec.signed_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt_int64]

/-- `[Xn|SP, Rm, <extend> #amount]`: the base plus the index register's value. -/
@[simp, grind =] theorem AddrExpr.eval_reg [Labels] (b : RegOrSp .W64) (r : MemExtRegExpr)
    (s : MachineData) (p : Std.Rco Int64) :
    AddrExpr.eval ⟨b, .reg r⟩ s p
      = (s.regs.getRegOrSp b + BitVec.ofInt 64 (r.interp s.regs p), s) := by
  simp only [AddrExpr.eval, BitVec.signed_eq]
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt]

/-- The shift amount of an index register. -/
@[simp] def MemExtendAmount.toNat : MemExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3

/-- A left shift commutes with wrapping an integer to a width. -/
theorem BitVec.ofInt_shiftLeft (n k : Nat) (i : Int) :
    BitVec.ofInt n (i <<< k) = BitVec.ofInt n i <<< k := by
  rw [Int.shiftLeft_eq, BitVec.ofInt_mul, BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, show ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) by simp,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]

/-- `Rm, LSL #k` (`UXTX`/`SXTX`): the 64-bit index register shifted. -/
@[simp, grind =] theorem MemExtRegExpr.interp_X (r : XReg) (t : MemExtendType)
    (a : MemExtendAmount) (ht : t = .UXTX ∨ t = .SXTX) (s : Reg64s) (p : Std.Rco Int64) :
    BitVec.ofInt 64 (MemExtRegExpr.interp ⟨⟨.W64, .low (.reg r) .W64⟩, ⟨t, a⟩⟩ s p)
      = (s.getXReg r).toBitVec <<< a.toNat := by
  rcases ht with rfl | rfl <;> cases a <;>
    simp [MemExtRegExpr.interp, BitVec.apply_mem_extend, BitVec.ofInt_shiftLeft]

/-- `Wm, UXTW #k`: the 32-bit index register zero-extended, shifted. -/
@[simp, grind =] theorem MemExtRegExpr.interp_UXTW (r : XReg) (a : MemExtendAmount)
    (s : Reg64s) (p : Std.Rco Int64) :
    BitVec.ofInt 64 (MemExtRegExpr.interp ⟨⟨.W32, .low (.reg r) .W32⟩, ⟨.UXTW, a⟩⟩ s p)
      = ((s.getXReg r).toBitVec.setWidth 32).setWidth 64 <<< a.toNat := by
  cases a <;> simp only [MemExtRegExpr.interp, BitVec.apply_mem_extend, BitVec.ofInt_shiftLeft,
    BitVec.unsigned_eq, BitVec.ofInt_natCast, BitVec.ofNat_toNat, Reg64s.getRegOrZr_W,
    BitVec.take_eq_setWidth, MemExtendAmount.toNat, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    BitVec.setWidth_eq, BitVec.shiftLeft_zero]

/-- `Wm, SXTW #k`: the 32-bit index register sign-extended, shifted. -/
@[simp, grind =] theorem MemExtRegExpr.interp_SXTW (r : XReg) (a : MemExtendAmount)
    (s : Reg64s) (p : Std.Rco Int64) :
    BitVec.ofInt 64 (MemExtRegExpr.interp ⟨⟨.W32, .low (.reg r) .W32⟩, ⟨.SXTW, a⟩⟩ s p)
      = ((s.getXReg r).toBitVec.setWidth 32).signExtend 64 <<< a.toNat := by
  cases a <;> simp [MemExtRegExpr.interp, BitVec.apply_mem_extend, BitVec.ofInt_shiftLeft,
    BitVec.take_eq_setWidth, BitVec.signExtend]

/-! ## Reading a named register, one lemma per field -/

@[simp, grind =] theorem Reg64s.getXReg_X0 (s : Reg64s) : s.getXReg .X0 = s.X0 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X1 (s : Reg64s) : s.getXReg .X1 = s.X1 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X2 (s : Reg64s) : s.getXReg .X2 = s.X2 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X3 (s : Reg64s) : s.getXReg .X3 = s.X3 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X4 (s : Reg64s) : s.getXReg .X4 = s.X4 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X5 (s : Reg64s) : s.getXReg .X5 = s.X5 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X6 (s : Reg64s) : s.getXReg .X6 = s.X6 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X7 (s : Reg64s) : s.getXReg .X7 = s.X7 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X8 (s : Reg64s) : s.getXReg .X8 = s.X8 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X9 (s : Reg64s) : s.getXReg .X9 = s.X9 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X10 (s : Reg64s) : s.getXReg .X10 = s.X10 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X11 (s : Reg64s) : s.getXReg .X11 = s.X11 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X12 (s : Reg64s) : s.getXReg .X12 = s.X12 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X13 (s : Reg64s) : s.getXReg .X13 = s.X13 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X14 (s : Reg64s) : s.getXReg .X14 = s.X14 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X15 (s : Reg64s) : s.getXReg .X15 = s.X15 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X16 (s : Reg64s) : s.getXReg .X16 = s.X16 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X17 (s : Reg64s) : s.getXReg .X17 = s.X17 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X18 (s : Reg64s) : s.getXReg .X18 = s.X18 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X19 (s : Reg64s) : s.getXReg .X19 = s.X19 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X20 (s : Reg64s) : s.getXReg .X20 = s.X20 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X21 (s : Reg64s) : s.getXReg .X21 = s.X21 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X22 (s : Reg64s) : s.getXReg .X22 = s.X22 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X23 (s : Reg64s) : s.getXReg .X23 = s.X23 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X24 (s : Reg64s) : s.getXReg .X24 = s.X24 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X25 (s : Reg64s) : s.getXReg .X25 = s.X25 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X26 (s : Reg64s) : s.getXReg .X26 = s.X26 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X27 (s : Reg64s) : s.getXReg .X27 = s.X27 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X28 (s : Reg64s) : s.getXReg .X28 = s.X28 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X29 (s : Reg64s) : s.getXReg .X29 = s.X29 := rfl
@[simp, grind =] theorem Reg64s.getXReg_X30 (s : Reg64s) : s.getXReg .X30 = s.X30 := rfl

/-! ## Per-register field reads over `setXReg`, one lemma per field -/

@[simp, grind =] theorem Reg64s.X0_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X0 = if r = .X0 then .ofBitVec v else s.X0 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X1_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X1 = if r = .X1 then .ofBitVec v else s.X1 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X2_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X2 = if r = .X2 then .ofBitVec v else s.X2 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X3_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X3 = if r = .X3 then .ofBitVec v else s.X3 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X4_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X4 = if r = .X4 then .ofBitVec v else s.X4 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X5_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X5 = if r = .X5 then .ofBitVec v else s.X5 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X6_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X6 = if r = .X6 then .ofBitVec v else s.X6 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X7_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X7 = if r = .X7 then .ofBitVec v else s.X7 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X8_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X8 = if r = .X8 then .ofBitVec v else s.X8 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X9_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X9 = if r = .X9 then .ofBitVec v else s.X9 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X10_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X10 = if r = .X10 then .ofBitVec v else s.X10 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X11_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X11 = if r = .X11 then .ofBitVec v else s.X11 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X12_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X12 = if r = .X12 then .ofBitVec v else s.X12 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X13_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X13 = if r = .X13 then .ofBitVec v else s.X13 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X14_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X14 = if r = .X14 then .ofBitVec v else s.X14 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X15_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X15 = if r = .X15 then .ofBitVec v else s.X15 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X16_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X16 = if r = .X16 then .ofBitVec v else s.X16 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X17_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X17 = if r = .X17 then .ofBitVec v else s.X17 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X18_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X18 = if r = .X18 then .ofBitVec v else s.X18 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X19_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X19 = if r = .X19 then .ofBitVec v else s.X19 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X20_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X20 = if r = .X20 then .ofBitVec v else s.X20 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X21_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X21 = if r = .X21 then .ofBitVec v else s.X21 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X22_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X22 = if r = .X22 then .ofBitVec v else s.X22 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X23_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X23 = if r = .X23 then .ofBitVec v else s.X23 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X24_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X24 = if r = .X24 then .ofBitVec v else s.X24 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X25_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X25 = if r = .X25 then .ofBitVec v else s.X25 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X26_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X26 = if r = .X26 then .ofBitVec v else s.X26 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X27_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X27 = if r = .X27 then .ofBitVec v else s.X27 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X28_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X28 = if r = .X28 then .ofBitVec v else s.X28 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X29_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X29 = if r = .X29 then .ofBitVec v else s.X29 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.X30_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).X30 = if r = .X30 then .ofBitVec v else s.X30 := by
  cases r <;> rfl
@[simp, grind =] theorem Reg64s.SP_setXReg (s : Reg64s) (r : XReg) (v : BitVec 64) :
    (s.setXReg r v).SP = s.SP := by
  cases r <;> rfl

/-! ## Tests -/

-- A `W` write zero-extends; the other registers keep their values.
example (s : Reg64s) :
    (s.setRegOrZr (.low (.reg .X0) .W32) 0xFFFFFFFF#32).X0 = 0xFFFFFFFF
      ∧ (s.setRegOrZr (.low (.reg .X0) .W32) 0xFFFFFFFF#32).X1 = s.X1 := by
  simp

-- `XZR` reads zero and drops writes; `SP` is apart from the `X` registers.
example (s : Reg64s) (v : BitVec 64) :
    s.getRegOrZr (.low .XZR .W64) = 0 ∧ s.setRegOrZr (.low .XZR .W64) v = s
      ∧ (s.setRegOrSp (.low .SP .W64) v).X3 = s.X3 := by
  simp

-- Pre-index writeback: the address and the new base are the base plus the offset.
example [Labels] (s : MachineData) :
    (AddrExpr.eval ⟨.low (.reg .X1) .W64, .imm ⟨.int64 16, some .Pre⟩⟩ s ⟨0, 4⟩).1
      = s.regs.X1.toBitVec + 16#64
    ∧ (AddrExpr.eval ⟨.low (.reg .X1) .W64, .imm ⟨.int64 16, some .Pre⟩⟩ s ⟨0, 4⟩).2.regs.X1
      = .ofBitVec (s.regs.X1.toBitVec + 16#64) := by
  simp

-- Register offset `[X1, X2, LSL #3]`.
example [Labels] (s : MachineData) :
    (AddrExpr.eval ⟨.low (.reg .X1) .W64,
        .reg ⟨⟨.W64, .low (.reg .X2) .W64⟩, ⟨.UXTX, .E3⟩⟩⟩ s ⟨0, 4⟩).1
      = s.regs.X1.toBitVec + s.regs.X2.toBitVec <<< 3 := by
  simp

-- The flags of `SUBS` on equal operands: `Z` and `C` set, so `EQ` and `HS` hold.
example (a : BitVec 64) :
    CondCode.EQ.interp (StatusFlags.subs (a - a) a a)
      ∧ CondCode.CS.interp (StatusFlags.subs (a - a) a a) := by
  simp
