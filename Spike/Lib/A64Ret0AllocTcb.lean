/-
**`scc_rt_alloc_tcb` in `ret0.w` on AArch64, block by block**: the walks
of the runtime's TCB allocator along its one feasible path when
`scc_rt_start` calls it with the header `2307` and `k = 1`, the named entry
and exit predicates of its segment (S2), and the pcs of its writes outside
the frame. The nodes at its single instructions (the label addresses, the
counter's add, the header's store) are the composition's; each walk takes
the facts they establish as hypotheses.

    scc_rt_alloc_tcb(h = x0, k = x1):        frame of 192, x29/x30 at 176/184
      .0_entry: if k ≥ 2^28 goto full                       (atChk: not taken)
      .1_len:   d = (k·(((h >> 8) & 16383) + m) + 1)·8,     (atLen: d = 80)
                m = (h >> 22) & 16383                       (m = 0)
                old = ldaddal [scc_rt_pinned_next], d       (rmwPc)
                if old + d > 2^17 goto full                 (atBnd: not taken)
      .3_ok:    str (h | k << 36), [pinned + old + 8·k·m]   (hdrPc)
                x0 = pinned + old + 8·k·m + 8; ret          (atRet)

- **The specification**: `Pre g n0` at the entry (`sp`, `x29`, `x30` the
  ghosts `g`, `x0 = hdr0`, `x1 = 1`) and `Post g n0 pinned` at `g.ra` (`x0 =
  pinned + n0 + 8`). The ghost `n0` is the own word `scc_rt_pinned_next` on
  entry; it holds `n0 + tcbLen` after `rmwPc`, so the add's old value is
  `n0`. The header `hdr0 ||| 1 << 36` is stored at `pinned + n0` at
  `hdrPc`.
- **The frame** (`Fr0` … `Fr3`): the saved registers, the arguments and the
  intermediate values the later blocks read, offsets from the entry's `sp`.
- **The walks** (`atPro_walk` … `atRet_walk`): each block's run from its
  frame predicate to the next, with its pc, offsets and branch (`atChk`
  and `atBnd` fall through); `labStep_spec` is the label address pair.
- **The code** (`allocTcbIn`, `ret0_allocTcbIn`): every block and single
  instruction at its label and index in `ret0Prog`, decided by the kernel.
-/
import Spike.Lib.A64Alloc
import Spike.Lib.A64Ret0Code
import Scc.Cert.Rt.LayoutA64

namespace Spike.Lib.A64.Flow.Ret0.AllocTcb

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

open Spike.Lib.A64.Alloc (subs_c subs_z subs_hi adrp_lo12)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in the frame. -/
abbrev oI : SO := ⟨-192, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩

/-- The prologue: a frame of 192, `x29`/`x30` saved at 176/184, `h`/`k` at 0/8. -/
def atPro : List Directive := parseAArch64("sub sp, sp, #192
str x29, [sp, #176]
str x30, [sp, #184]
add x29, sp, #176
str x0, [sp]
str x1, [sp, #8]")

/-- `k ≥ 2^28` goes to the abort. -/
def atChk : List Directive := parseAArch64("ldr x9, [sp, #8]
movz x10, #4096, lsl #16
subs xzr, x9, x10
b.hs .L3_scc_rt_alloc_tcb.2_full")

/-- On to `.1_len`. -/
def atJ1 : List Directive := parseAArch64("b .L3_scc_rt_alloc_tcb.1_len")

/-- The TCB's length in bytes, `d = (k·(len + m) + 1)·8` (at `[sp, #72]`). -/
def atLen : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #8
lsrv x9, x9, x10
str x9, [sp, #16]
ldr x9, [sp, #16]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #24]
ldr x9, [sp]
movz x10, #22
lsrv x9, x9, x10
str x9, [sp, #32]
ldr x9, [sp, #32]
movz x10, #16383
and x9, x9, x10
str x9, [sp, #40]
ldr x9, [sp, #24]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #8]
ldr x10, [sp, #48]
madd x9, x9, x10, xzr
str x9, [sp, #56]
ldr x9, [sp, #56]
movz x10, #1
add x9, x9, x10
str x9, [sp, #64]
ldr x9, [sp, #64]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #72]")

/-- The add's operands: `x9 = d`, `x10` the counter's address. -/
def atArg : List Directive := parseAArch64("str x9, [sp, #80]
ldr x9, [sp, #72]
ldr x10, [sp, #80]")

/-- The counter's old value saved; past the pinned area (`2^17` bytes) goes to the abort. -/
def atBnd : List Directive := parseAArch64("str x11, [sp, #88]
ldr x9, [sp, #88]
ldr x10, [sp, #72]
add x9, x9, x10
str x9, [sp, #96]
ldr x9, [sp, #96]
movz x10, #2, lsl #16
subs xzr, x9, x10
b.hi .L3_scc_rt_alloc_tcb.2_full")

/-- On to `.3_ok`. -/
def atJ2 : List Directive := parseAArch64("b .L3_scc_rt_alloc_tcb.3_ok")

/-- The header `h | k << 36` and its address `pinned + old + 8·k·m`. -/
def atOk : List Directive := parseAArch64("str x9, [sp, #104]
ldr x9, [sp, #104]
ldr x10, [sp, #88]
add x9, x9, x10
str x9, [sp, #112]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
madd x9, x9, x10, xzr
str x9, [sp, #120]
ldr x9, [sp, #120]
movz x10, #3
lslv x9, x9, x10
str x9, [sp, #128]
ldr x9, [sp, #8]
movz x10, #36
lslv x9, x9, x10
str x9, [sp, #136]
ldr x9, [sp]
ldr x10, [sp, #136]
orr x9, x9, x10
str x9, [sp, #144]
ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #152]
ldr x9, [sp, #144]
ldr x10, [sp, #152]")

/-- `x0` one word past the header; the epilogue and the return. -/
def atRet : List Directive := parseAArch64("ldr x9, [sp, #112]
ldr x10, [sp, #128]
add x9, x9, x10
str x9, [sp, #160]
ldr x9, [sp, #160]
movz x10, #8
add x9, x9, x10
str x9, [sp, #168]
ldr x0, [sp, #168]
ldr x29, [sp, #176]
ldr x30, [sp, #184]
add sp, sp, #192
ret")

block_spec atPro (-192) 0 oE atPro
block_spec atChk (-192) 0 oI atChk
block_spec atJ1 (-192) 0 oI atJ1
block_spec atLen (-192) 0 oI atLen
block_spec atArg (-192) 0 oI atArg
block_spec atBnd (-192) 0 oI atBnd
block_spec atJ2 (-192) 0 oI atJ2
block_spec atOk (-192) 0 oI atOk
block_spec atRet (-192) 0 oI atRet

/-! ## The specification -/

/-- **The ghosts of a call**: `sp`, `x29` and `x30` at entry. -/
structure G where
  /-- `sp` at entry. -/
  sp : BitVec 64
  /-- `x29` at entry. -/
  fp : BitVec 64
  /-- The return address. -/
  ra : BitVec 64

/-- The header `scc_rt_start` passes. -/
abbrev hdr0 : BitVec 64 := 2307#64

/-- The TCB's length in bytes the code computes for `hdr0` and `k = 1`. -/
abbrev tcbLen : BitVec 64 := 80#64

/-- **Entry**: `sp`, `x29`, `x30` the ghosts', `x0 = 2307`, `x1 = 1`. The
own word `scc_rt_pinned_next` holds `n0` (the map's, not the state's). -/
def Pre (g : G) (_n0 : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = hdr0 ∧ σ.regs.X1.toBitVec = 1#64

/-- **Exit** (at `g.ra`): `sp`, `x29`, `x30` restored, `x0` one word past
the header at `pinned + n0`. `scc_rt_pinned_next` holds `n0 + tcbLen`. -/
def Post (g : G) (n0 pinned : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = pinned + n0 + 8#64

/-- The frame: `sp` down by 192, the saved `x29`/`x30` and the arguments. -/
def Fr0 (g : G) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp - 192#64 ∧ σ.slot (-16) = g.fp ∧ σ.slot (-8) = g.ra ∧
  σ.slot (-192) = hdr0 ∧ σ.slot (-184) = 1#64

/-- The frame after the length: `d` and the header's field `m = 0`. -/
def Fr1 (g : G) (σ : AS) : Prop := Fr0 g σ ∧ σ.slot (-120) = tcbLen ∧ σ.slot (-152) = 0#64

/-- The frame after the add: the counter's old value `n0`. -/
def Fr2 (g : G) (n0 : BitVec 64) (σ : AS) : Prop := Fr1 g σ ∧ σ.slot (-104) = n0

/-- The frame at the header's store: its address and the result's parts. -/
def Fr3 (g : G) (n0 pinned : BitVec 64) (σ : AS) : Prop :=
  Fr2 g n0 σ ∧ σ.slot (-80) = pinned + n0 ∧ σ.slot (-64) = 0#64

/-! ## The walks -/

/-- **The prologue**: from the entry to `.0_entry` (six instructions on),
the frame set up. -/
theorem atPro_walk (lab : Label → Int64) (pc : Int64) {g : G} {n0 : BitVec 64} {σ : AS} (h : Pre g n0 σ) :
    (arun lab atPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat (4 * 6) ∧
    (arun lab atPro ⟨pc, oE, σ⟩).so = ⟨-192, [(.X29, -16)]⟩ ∧ Fr0 g (arun lab atPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [atPro_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5]

/-- **The size check is not taken** (`k = 1`). -/
theorem atChk_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr0 g σ) :
    (arun lab atChk ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 4) ∧
    (arun lab atChk ⟨pc, oI, σ⟩).so = oI ∧ Fr0 g (arun lab atChk ⟨pc, oI, σ⟩).σ := by
  have h5 := h.2.2.2.2
  rw [atChk_run, subs_c, h5]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, h⟩

/-- **The length**: `d = tcbLen`, `m = 0`. -/
theorem atLen_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} (h : Fr0 g σ) :
    (arun lab atLen ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 32) ∧
    (arun lab atLen ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g (arun lab atLen ⟨pc, oI, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [atLen_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5]
  decide

/-- **The add's operands**: `x9 = tcbLen`, `x10` the counter's address `P`
(in `x9` before). -/
theorem atArg_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {P : BitVec 64} (h : Fr1 g σ)
    (hP : σ.regs.X9.toBitVec = P) :
    (arun lab atArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 3) ∧
    (arun lab atArg ⟨pc, oI, σ⟩).so = oI ∧ Fr1 g (arun lab atArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = tcbLen ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = P := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := h
  rw [atArg_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, hP]

/-- **The bound is not crossed** when the counter's old value `n0` (in
`x11`) has room for `tcbLen` more bytes below `2^17`. -/
theorem atBnd_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {n0 : BitVec 64} (h : Fr1 g σ)
    (h11 : σ.regs.X11.toBitVec = n0) (hn : n0.toNat + 80 ≤ 131072) :
    (arun lab atBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 9) ∧
    (arun lab atBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr2 g n0 (arun lab atBnd ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := h
  have hc : ¬ ((StatusFlags.subs (n0 + tcbLen - 131072#64) (n0 + tcbLen) 131072#64).c = true ∧
      (StatusFlags.subs (n0 + tcbLen - 131072#64) (n0 + tcbLen) 131072#64).z = false) := by
    rw [subs_hi, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [atBnd_run, h11, h6, ite_eq_right_iff.mpr (fun h => absurd h hc)]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h11]

/-- **The header and its address**: `x9 = hdr0 | 1 << 36`, `x10 = Q + n0`
(`Q`, the pinned area's address, in `x9` before). -/
theorem atOk_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr2 g n0 σ)
    (hQ : σ.regs.X9.toBitVec = Q) :
    (arun lab atOk ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 27) ∧
    (arun lab atOk ⟨pc, oI, σ⟩).so = oI ∧ Fr3 g n0 Q (arun lab atOk ⟨pc, oI, σ⟩).σ ∧
    (arun lab atOk ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = hdr0 ||| 1#64 <<< 36 ∧
    (arun lab atOk ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = Q + n0 := by
  obtain ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, h8⟩ := h
  rw [atOk_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr3, Fr2, Fr1, Fr0, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h8, hQ]
  decide

/-- **The return**: to `g.ra` with `x0 = Q + n0 + 8`, the frame popped. -/
theorem atRet_walk (lab : Label → Int64) (pc : Int64) {g : G} {σ : AS} {n0 Q : BitVec 64} (h : Fr3 g n0 Q σ) :
    (arun lab atRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab atRet ⟨pc, oI, σ⟩).so = oE ∧ Post g n0 Q (arun lab atRet ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, h8⟩, h9, h10⟩ := h
  rw [atRet_run]
  refine ⟨by rw [h3], rfl, ?_⟩
  simp [Post, h1, h2, h3, h9, h10, BitVec.sub_add_cancel]

/-! ## A label's address -/

/-- **`adrp x9, L; add x9, x9, :lo12:L`**: the state after it. -/
def labStep (lab : Label → Int64) (L : Label) (σ : AS) : AS :=
  (SI.addLo12 .X9 .X9 L).step lab ((SI.adrp .X9 L).step lab σ)

/-- A label's address leaves `x9` the address, the cells and `sp` as they were. -/
theorem labStep_spec (lab : Label → Int64) (L : Label) (σ : AS) :
    (labStep lab L σ).regs.X9.toBitVec = (lab L).toBitVec ∧ (labStep lab L σ).slot = σ.slot ∧
    (labStep lab L σ).regs.SP = σ.regs.SP ∧ (labStep lab L σ).regs.X11 = σ.regs.X11 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  have h := adrp_lo12 (lab L).toBitVec
  simp only [BitVec.reduceNot] at h
  simp [labStep, SI.step, SI.regs, Reg64s.setRegOrZr, Reg64s.setRegOrSp, Reg64s.getRegOrSp, Reg64s.setRegOrZr64,
    Reg64s.setRegOrSp64, Reg64s.getRegOrSp64]
  exact h

/-- A label's address keeps `Fr1`. -/
theorem labStep_fr1 (lab : Label → Int64) (L : Label) {g : G} {σ : AS} (h : Fr1 g σ) : Fr1 g (labStep lab L σ) := by
  obtain ⟨-, h2, h3, -⟩ := labStep_spec lab L σ
  simpa [Fr1, Fr0, h2, h3] using h

/-- A label's address keeps `Fr2`. -/
theorem labStep_fr2 (lab : Label → Int64) (L : Label) {g : G} {n0 : BitVec 64} {σ : AS} (h : Fr2 g n0 σ) :
    Fr2 g n0 (labStep lab L σ) := by
  obtain ⟨-, h2, h3, -⟩ := labStep_spec lab L σ
  simpa [Fr2, Fr1, Fr0, h2, h3] using h

/-! ## The code -/

/-- `scc_rt_alloc_tcb`'s label. -/
abbrev fnL : Label := "scc_rt_alloc_tcb"
/-- Its entry label. -/
abbrev entryL : Label := ".L3_scc_rt_alloc_tcb.0_entry"
/-- The length's label. -/
abbrev lenL : Label := ".L3_scc_rt_alloc_tcb.1_len"
/-- The header's label. -/
abbrev okL : Label := ".L3_scc_rt_alloc_tcb.3_ok"
/-- The abort's label. -/
abbrev fullL : Label := ".L3_scc_rt_alloc_tcb.2_full"

/-- The counter's add `ldaddal x9, x11, [x10]`. -/
abbrev rmwDir : Directive := ldopDir .ADD .acqRel .X9 .X11 .X10
/-- The header's store `str x9, [x10]`. -/
abbrev hdrDir : Directive := strDir .X9 .X10 0

/-- **The pc of the own word's write** (`scc_rt_pinned_next`'s add). -/
abbrev rmwPc (lab : Label → Int64) : Int64 := lab lenL + Int64.ofNat (4 * 37)
/-- The pc of the header's store. -/
abbrev hdrPc (lab : Label → Int64) : Int64 := lab okL + Int64.ofNat (4 * 29)

/-- **`scc_rt_alloc_tcb`'s code in `prog`**: its blocks, its single
instructions and the fall-through into `.0_entry`. -/
def allocTcbIn (prog : List Directive) : Bool :=
  labelGap prog fnL entryL 6 && blockAt prog fnL 0 atPro && blockAt prog entryL 0 atChk &&
  blockAt prog entryL 4 atJ1 && blockAt prog lenL 0 atLen &&
  blockAt prog lenL 32 [(SI.adrp .X9 "scc_rt_pinned_next").toDir] &&
  blockAt prog lenL 33 [(SI.addLo12 .X9 .X9 "scc_rt_pinned_next").toDir] && blockAt prog lenL 34 atArg &&
  blockAt prog lenL 37 [rmwDir] && blockAt prog lenL 38 atBnd && blockAt prog lenL 47 atJ2 &&
  blockAt prog okL 0 [(SI.adrp .X9 "scc_rt_pinned").toDir] &&
  blockAt prog okL 1 [(SI.addLo12 .X9 .X9 "scc_rt_pinned").toDir] && blockAt prog okL 2 atOk &&
  blockAt prog okL 29 [hdrDir] && blockAt prog okL 30 atRet

#guard allocTcbIn SccCode.ret0Prog

/-- The code's check on `ret0Prog`. -/
theorem ret0_allocTcbIn : allocTcbIn SccCode.ret0Prog = true := by decide +kernel

end Spike.Lib.A64.Flow.Ret0.AllocTcb
