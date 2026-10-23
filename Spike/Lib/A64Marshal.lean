/-
**A `print` call's marshalling** (AArch64), for any frame offsets and label.

`Scc/Lower/Term.lean`'s `callBlock` lowers `print(b, o, m, n)` (the slice
`b[o..]` of `m` words, at most `n` bytes) to: the slice's first byte
`x0 = b + lo32(o)` (`mshlPtr`), the byte count `x1 = min(n, 8·m)` unsigned
(`mshlLen`, a `subs`/`csel lo` select), then `bl L`. With the arguments in
the frame's cells (`ob oo om on`) and the four temporaries the emitter
spills (`tl ts tc tk`), the 21 instructions are `mshlBlk`; `mshlBlk_run` is
their closed form (the cells `mshlSlot`, `x30` the return address, the
registers off `x0 x1 x9..x12 x30` kept), `mshlBlk_ok` their coverage and
`mshlBlk_hit` the landing at the callee's entry. Only the register form of
`o` is covered (an immediate offset is lowered differently).
-/
import Spike.Lib.A64Prologue
open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

namespace Spike.Lib.A64.Flow

set_option linter.unusedSimpArgs false

/-- `ldr Xr, [sp, #n]`. -/
def ldS (r : XReg) (n : Int64) : Directive := RW.dir r (.slot n)

/-- The marshalling: argument cells `ob oo om on`, temporaries `tl ts tc tk`, callee `L`. -/
def mshlBlk (ob oo om on tl ts tc tk : Int64) (L : Label) : List Directive :=
  [ldS .X9 oo, .instr ⟨.W64, .UBFM (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) 0 31⟩, spStr .X9 tl,
   ldS .X9 ob, ldS .X10 tl,
   .instr ⟨.W64, .ADD_s (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) ⟨.low (.reg .X10) .W64, 0, .LSL⟩⟩,
   spStr .X9 ts,
   ldS .X9 om, RW.dir .X10 (.imm 8),
   .instr ⟨.W64, .MADD (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) (.low (.reg .X10) .W64) (.low .XZR .W64)⟩,
   spStr .X9 tc,
   ldS .X9 on, ldS .X10 tc,
   .instr ⟨.W64, .SUBS_s (.low .XZR .W64) (.low (.reg .X9) .W64) ⟨.low (.reg .X10) .W64, 0, .LSL⟩⟩,
   ldS .X11 on, ldS .X12 tc,
   .instr ⟨.W64, .CSEL (.low (.reg .X9) .W64) (.low (.reg .X11) .W64) (.low (.reg .X12) .W64) .CC⟩,
   spStr .X9 tk,
   ldS .X0 ts, ldS .X1 tk, .instr ⟨.W64, .BL (.label L)⟩]

/-- `mshlBlk` is what Kraken's parser makes of `scc`'s `print` calls. -/
example : mshlBlk 0 8 16 24 40 48 56 64 "scc_rt_print" = parseAArch64("ldr x9, [sp, #8]
ubfm x9, x9, #0, #31
str x9, [sp, #40]
ldr x9, [sp]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #24]
ldr x10, [sp, #56]
subs xzr, x9, x10
ldr x11, [sp, #24]
ldr x12, [sp, #56]
csel x9, x11, x12, lo
str x9, [sp, #64]
ldr x0, [sp, #48]
ldr x1, [sp, #64]
bl scc_rt_print") := by decide

/-- The slice's first byte: the buffer's address plus the low 32 bits of the offset word. -/
def mshlPtr (b o : BitVec 64) : BitVec 64 := b + (o.setWidth 32).setWidth 64

/-- The byte count: `min(n, 8·m)` (unsigned). -/
def mshlLen (m n : BitVec 64) : BitVec 64 := if n.toNat < (m * 8#64).toNat then n else m * 8#64

/-- The cells after the block: the temporaries stored. -/
def mshlSlot (sp : Int) (sl : Int → BitVec 64) (ob oo om on tl ts tc tk : Int64) : Int → BitVec 64 :=
  upd (upd (upd (upd sl (sp + tl.toInt) (((sl (sp + oo.toInt)).setWidth 32).setWidth 64))
    (sp + ts.toInt) (mshlPtr (sl (sp + ob.toInt)) (sl (sp + oo.toInt))))
    (sp + tc.toInt) (sl (sp + om.toInt) * 8#64))
    (sp + tk.toInt) (mshlLen (sl (sp + om.toInt)) (sl (sp + on.toInt)))

/-- The `subs`/`csel lo` select's condition: no borrow iff not below. -/
theorem mshl_cond (n m : Nat) (hn : n < 18446744073709551616) :
    ((((18446744073709551616 - m * 8 % 18446744073709551616 : Nat) : Int) + (n : Int)) % 18446744073709551616 =
        (n : Int) - (m : Int) * 8 % 18446744073709551616) ↔ ¬ n < m * 8 % 18446744073709551616 := by
  omega

/-- **The marshalling's run**: the pc at `L`, `sp` unchanged, the
temporaries stored, `x0`/`x1` the slice's address and byte count, `x30` the
return address, and the other registers kept. -/
theorem mshlBlk_run (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) {ob oo om on tl ts tc tk : Int64}
    (L : Label) (h1 : ob.toInt ≠ tl.toInt) (h2 : om.toInt ≠ tl.toInt) (h3 : om.toInt ≠ ts.toInt)
    (h4 : on.toInt ≠ tl.toInt) (h5 : on.toInt ≠ ts.toInt) (h6 : on.toInt ≠ tc.toInt)
    (h7 : ts.toInt ≠ tc.toInt) (h8 : ts.toInt ≠ tk.toInt) :
    (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).pc = lab L ∧
    (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).so = ⟨sp, []⟩ ∧
    (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).σ.slot =
      mshlSlot sp σ.slot ob oo om on tl ts tc tk ∧
    (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.X0.toBitVec =
      mshlPtr (σ.slot (sp + ob.toInt)) (σ.slot (sp + oo.toInt)) ∧
    (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.X1.toBitVec =
      mshlLen (σ.slot (sp + om.toInt)) (σ.slot (sp + on.toInt)) ∧
    (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.X30.toBitVec =
      BitVec.ofInt 64 (pc.toInt + 84) ∧
    ∀ r, r ∉ [XReg.X0, .X1, .X9, .X10, .X11, .X12, .X30] →
      (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩).σ.regs.getXReg r = σ.regs.getXReg r := by
  simp [mshlBlk, ldS, spStr, RW.dir, RW.val, AI.toDir, arun, Reg64s.getRegOrZr_X, dstep, classify, RegOnly, AI.so,
    AI.step, AI.tgt, soReg, regRes, Operation.interp, ConstExpr.interp, SO.set, SO.get, lk, upd_apply,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst,
    Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8, h1, h2, h3, h4,
    h5, h6, h7, h8, mshlSlot, mshlPtr, mshlLen, BitVec.take_eq_setWidth]
  have hn := (σ.slot (sp + on.toInt)).isLt
  have hm := (σ.slot (sp + om.toInt)).isLt
  have h30 : BitVec.ofInt 64 ((pc.toInt + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 +
      4 + 4).bmod 18446744073709551616) = BitVec.ofInt 64 (pc.toInt + 84) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    rw [Int.bmod_emod]
    congr 2
    omega
  simp only [h30]
  have hc := mshl_cond (σ.slot (sp + on.toInt)).toNat (σ.slot (sp + om.toInt)).toNat hn
  simp only [hc, ite_not, true_and]
  intro r h0 h1 h9 h10 h11 h12 h30'
  simp [h0, h1, h9, h10, h11, h12, h30']


/-- **The marshalling is covered**, its eight cells inside the region. -/
theorem mshlBlk_ok {lo hi sp : Int} (h16 : sp % 16 = 0) {ob oo om on tl ts tc tk : Int64} (L : Label)
    (hob : offOk lo hi (sp + ob.toInt) = true) (hoo : offOk lo hi (sp + oo.toInt) = true)
    (hom : offOk lo hi (sp + om.toInt) = true) (hon : offOk lo hi (sp + on.toInt) = true)
    (htl : offOk lo hi (sp + tl.toInt) = true) (hts : offOk lo hi (sp + ts.toInt) = true)
    (htc : offOk lo hi (sp + tc.toInt) = true) (htk : offOk lo hi (sp + tk.toInt) = true) :
    okBlk lo hi ⟨sp, []⟩ (mshlBlk ob oo om on tl ts tc tk L) = true := by
  simp [mshlBlk, ldS, spStr, RW.dir, AI.toDir, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB,
    SO.write, SO.kill, SO.killZ, rm, h16, hob, hoo, hom, hon, htl, hts, htc, htk]

/-- **The marshalling lands** at a node at `L` whose obligation holds of the run's closed form. -/
theorem mshlBlk_hit (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) {ob oo om on tl ts tc tk : Int64}
    (L : Label) (h1 : ob.toInt ≠ tl.toInt) (h2 : om.toInt ≠ tl.toInt) (h3 : om.toInt ≠ ts.toInt)
    (h4 : on.toInt ≠ tl.toInt) (h5 : on.toInt ≠ ts.toInt) (h6 : on.toInt ≠ tc.toInt)
    (h7 : ts.toInt ≠ tc.toInt) (h8 : ts.toInt ≠ tk.toInt) {x : ND} {c : Ctl} (hpc : x.pc = lab L)
    (ho : x.o = ⟨sp, []⟩)
    (hJ : ∀ σ' : AS, σ'.slot = mshlSlot sp σ.slot ob oo om on tl ts tc tk →
      σ'.regs.X0.toBitVec = mshlPtr (σ.slot (sp + ob.toInt)) (σ.slot (sp + oo.toInt)) →
      σ'.regs.X1.toBitVec = mshlLen (σ.slot (sp + om.toInt)) (σ.slot (sp + on.toInt)) →
      σ'.regs.X30.toBitVec = BitVec.ofInt 64 (pc.toInt + 84) →
      (∀ r, r ∉ [XReg.X0, .X1, .X9, .X10, .X11, .X12, .X30] → σ'.regs.getXReg r = σ.regs.getXReg r) →
      x.J σ' c) :
    Hit x (arun lab (mshlBlk ob oo om on tl ts tc tk L) ⟨pc, ⟨sp, []⟩, σ⟩) c := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := mshlBlk_run lab pc sp σ L h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨by rw [hpc, e1], by rw [ho, e2]; simp [SO.le], hJ _ e3 e4 e5 e6 e7⟩

end Spike.Lib.A64.Flow
