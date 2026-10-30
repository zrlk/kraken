/-
**`scc_rt_thread_reserve` on AArch64, block by block**: the walks of the
thread counter's reservation along its one feasible path (the counter's
old value `n` with `n + 1 ≤ 1023`, so the bound's abort is not taken), the
named entry and exit predicates of its segment, and the pc of its write
outside the frame (`Runtime.threadReserveF`, A13's `reserveGrps`).

    scc_rt_thread_reserve:                  frame of 48, x29/x30 at 32/40
      .0_entry: x9 = &scc_rt_nthreads; [sp] = x9            (label pair, rArg)
                n = ldaddal [scc_rt_nthreads], 1            (rmwPc)
                [sp+8] = n; [sp+16] = n + 1
                if n + 1 > 1023 goto full                   (rBnd: not taken)
      .2_ok:    x0 = n + 1; ret                             (rRet)

- **The specification**: `Pre g` at the entry (`sp`, `x29`, `x30` the
  ghosts) and `Post g n` at `g.ra` (`x0 = n + 1`). The ghost `n` is the own
  word `scc_rt_nthreads` at the add; it holds `n + 1` after `rmwPc`.
- **The frame** (`Fr0` … `Fr2`), **the walks** (`rPro_walk` … `rRet_walk`)
  and **the code** (`reserveIn`), as `A64Ret0AllocTcb`'s.
-/
import Spike.Lib.A64Ret0AllocTcb

namespace Spike.Lib.A64.Flow.Reserve

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

open Spike.Lib.A64.Alloc (subs_c subs_z subs_hi adrp_lo12)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap)
open Spike.Lib.A64.Flow.Ret0.AllocTcb (labStep labStep_spec)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame. -/
abbrev oI : SO := ⟨-48, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩

/-- The prologue: a frame of 48, `x29`/`x30` saved at 32/40. -/
def rPro : List Directive := parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32")

/-- The add's operands: the counter's address saved, `x9 = 1`, `x10` the address. -/
def rArg : List Directive := parseAArch64("str x9, [sp]
movz x9, #1
ldr x10, [sp]")

/-- The old value and `n + 1` saved; past `maxThreads` goes to the abort. -/
def rBnd : List Directive := parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #1023
subs xzr, x9, x10
b.hi .L4_scc_rt_thread_reserve.1_full")

/-- On to `.2_ok`. -/
def rJ : List Directive := parseAArch64("b .L4_scc_rt_thread_reserve.2_ok")

/-- The result `n + 1` and the epilogue. -/
def rRet : List Directive := parseAArch64("ldr x0, [sp, #16]
ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

block_spec rPro (-48) 0 oE rPro
block_spec rArg (-48) 0 oI rArg
block_spec rBnd (-48) 0 oI rBnd
block_spec rJ (-48) 0 oI rJ
block_spec rRet (-48) 0 oI rRet

/-! ## The specification -/

/-- **The ghosts of a call**: `sp`, `x29` and `x30` at entry. -/
structure G where
  /-- `sp` at entry. -/
  sp : BitVec 64
  /-- `x29` at entry. -/
  fp : BitVec 64
  /-- The return address. -/
  ra : BitVec 64

/-- **Entry**: `sp`, `x29`, `x30` the ghosts'. -/
def Pre (g : G) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra

/-- **Exit** (at `g.ra`): `sp`, `x29`, `x30` restored, `x0 = n + 1`, the
new thread's id. `scc_rt_nthreads` holds `n + 1`. -/
def Post (g : G) (n : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = n + 1#64

/-- The frame: `sp` down by 48, the saved `x29`/`x30`. -/
def Fr0 (g : G) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp - 48#64 ∧ σ.slot (-16) = g.fp ∧ σ.slot (-8) = g.ra

/-- The frame after the counter's address `P`. -/
def Fr1 (g : G) (P : BitVec 64) (σ : AS) : Prop := Fr0 g σ ∧ σ.slot (-48) = P

/-- The frame after the bound: the old value and `n + 1`. -/
def Fr2 (g : G) (P n : BitVec 64) (σ : AS) : Prop :=
  Fr1 g P σ ∧ σ.slot (-40) = n ∧ σ.slot (-32) = n + 1#64

/-! ## The walks -/

/-- **The prologue**: from the entry to `.0_entry`, the frame set up. -/
theorem rPro_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} (h : Pre g σ) :
    (arun lab rPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat (4 * 4) ∧
    (arun lab rPro ⟨pc, oE, σ⟩).so = ⟨-48, [(.X29, -16)]⟩ ∧ Fr0 g (arun lab rPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [rPro_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0, Spike.Lib.upd_apply, h1, h2, h3]

/-- **The add's operands**: `x9 = 1`, `x10` the counter's address `P` (in
`x9` before), `P` saved. -/
theorem rArg_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {P : BitVec 64} (h : Fr0 g σ)
    (hP : σ.regs.X9.toBitVec = P) :
    (arun lab rArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 3) ∧
    (arun lab rArg ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g P (arun lab rArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab rArg ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = 1#64 ∧
    (arun lab rArg ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = P := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [rArg_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, hP]

/-- **The bound is not crossed** when the old value `n` (in `x11`) has
`n + 1 ≤ 1023`. -/
theorem rBnd_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {P n : BitVec 64} (h : Fr1 g P σ)
    (h11 : σ.regs.X11.toBitVec = n) (hn : n.toNat + 1 ≤ 1023) :
    (arun lab rBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 9) ∧
    (arun lab rBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr2 g P n (arun lab rBnd ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  have hc : ¬ ((StatusFlags.subs (n + 1#64 - 1023#64) (n + 1#64) 1023#64).c = true ∧
      (StatusFlags.subs (n + 1#64 - 1023#64) (n + 1#64) 1023#64).z = false) := by
    rw [subs_hi, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [rBnd_run, h11, ite_eq_right_iff.mpr (fun h => absurd h hc)]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h11]

/-- **The return**: to `g.ra` with `x0 = n + 1`, the frame popped. -/
theorem rRet_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {P n : BitVec 64} (h : Fr2 g P n σ) :
    (arun lab rRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab rRet ⟨pc, oI, σ⟩).so = oE ∧ Post g n (arun lab rRet ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5, h6⟩ := h
  rw [rRet_run]
  refine ⟨by rw [h3], rfl, ?_⟩
  simp [Post, h1, h2, h3, h6, BitVec.sub_add_cancel]

/-- A label's address keeps `Fr0`. -/
theorem labStep_fr0 (lab : Label → Int64) (L : Label) {g : G} {σ : AS} (h : Fr0 g σ) : Fr0 g (labStep lab L σ) := by
  obtain ⟨-, h2, h3, -⟩ := labStep_spec lab L σ
  simpa [Fr0, h2, h3] using h

/-! ## The code -/

/-- `scc_rt_thread_reserve`'s label. -/
abbrev fnL : Label := "scc_rt_thread_reserve"
/-- Its entry label. -/
abbrev entryL : Label := ".L4_scc_rt_thread_reserve.0_entry"
/-- The return's label. -/
abbrev okL : Label := ".L4_scc_rt_thread_reserve.2_ok"
/-- The abort's label. -/
abbrev fullL : Label := ".L4_scc_rt_thread_reserve.1_full"

/-- The counter's add `ldaddal x9, x11, [x10]`. -/
abbrev rmwDir : Directive := ldopDir .ADD .acqRel .X9 .X11 .X10

/-- **The pc of the own word's write** (`scc_rt_nthreads`' add). -/
abbrev rmwPc (lab : Label → Int64) : Int64 := lab entryL + Int64.ofNat (4 * 5)

/-- **`scc_rt_thread_reserve`'s code in `prog`**: its blocks, its single
instructions and the fall-through into `.0_entry`. -/
def reserveIn (prog : List Directive) : Bool :=
  labelGap prog fnL entryL 4 && blockAt prog fnL 0 rPro &&
  blockAt prog entryL 0 [(SI.adrp .X9 "scc_rt_nthreads").toDir] &&
  blockAt prog entryL 1 [(SI.addLo12 .X9 .X9 "scc_rt_nthreads").toDir] && blockAt prog entryL 2 rArg &&
  blockAt prog entryL 5 [rmwDir] && blockAt prog entryL 6 rBnd && blockAt prog entryL 15 rJ &&
  blockAt prog okL 0 rRet

/-- The blocks are A13's (`Scc.Cert.Spawn.A64.reserveGrps`), so `a13code`
gives `reserveIn` (`Spike/Lib/Rt/A64RtReserve.lean`). -/
example : rArg ++ [rmwDir] ++ rBnd = parseAArch64("str x9, [sp]
movz x9, #1
ldr x10, [sp]
ldaddal x9, x11, [x10]
str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
add x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #1023
subs xzr, x9, x10
b.hi .L4_scc_rt_thread_reserve.1_full") := by decide

end Spike.Lib.A64.Flow.Reserve
