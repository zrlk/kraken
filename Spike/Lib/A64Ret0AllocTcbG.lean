/-
**`scc_rt_alloc_tcb` at any header** (AArch64): the walks of
`A64Ret0AllocTcb` generalised from `scc_rt_start`'s header `2307` to any
header `h` with `k = 1`, for the second call (a spawn's TCB, whose header
has a nonzero `m`). The blocks, their `arun` equations and the code check
`allocTcbIn` are `A64Ret0AllocTcb`'s, unchanged; only the frame predicates
and the walks through `atLen`, `atBnd`, `atOk` and `atRet` read the header.

    d   = lenOf h = (n + m + 1)·8,  n = (h >> 8) & 16383, m = (h >> 22) & 16383
    hdr = h | 1 << 36               stored at pinned + n0 + 8·m
    x0  = pinned + n0 + 8·m + 8     (the TCB, one word past the header)

- `nOf`, `mOf`, `lenOf`: the header's fields and the length the code
  computes; `lenOf_toNat` the same as `8 · tcbWords h 1` of the spawn
  checks (unfolded, so this file needs no trusted import).
- `PreG`, `PostG`, `Fr0G` … `Fr3G`: `Pre` … `Fr3` at the header `h`.
- `atPro_walkG` … `atRet_walkG`, `labStep_fr1G`, `labStep_fr2G`: the walks.
- `pre_of_gen0` … `fr3_of_gen0`, `post_of_gen0`: at `hdr0` the general
  predicates are the old ones (`lenOf hdr0 = tcbLen`, `mOf hdr0 = 0`).
- `StackTake.k0Of g` (`16384·g`), `k0Of_room`, `k0Of_succ`: the stack
  allocator's second call is the instance `k0 = k0Of 1` of its generic
  walks; `ThreadInit` is generic in the TCB and the base as it is.
-/
import Spike.Lib.A64Ret0StackTake

namespace Spike.Lib.A64.Flow.Ret0.AllocTcb

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

open Spike.Lib.A64.Alloc (subs_c subs_z subs_hi adrp_lo12)

set_option linter.unusedSimpArgs false

/-! ## The header's fields -/

/-- The header's field `n` (the frame words), bits 8–21. -/
def nOf (h : BitVec 64) : BitVec 64 := h >>> 8 &&& 16383#64

/-- The header's field `m` (the words below the header), bits 22–35. -/
def mOf (h : BitVec 64) : BitVec 64 := h >>> 22 &&& 16383#64

/-- **The TCB's length in bytes** the code computes for `h` and `k = 1`. -/
def lenOf (h : BitVec 64) : BitVec 64 := nOf h <<< 3 + mOf h <<< 3 + 8#64

theorem nOf_toNat (h : BitVec 64) : (nOf h).toNat = (h.toNat >>> 8) % 16384 := by
  simp only [nOf, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [show (16383 : Nat) % 2 ^ 64 = 2 ^ 14 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem mOf_toNat (h : BitVec 64) : (mOf h).toNat = (h.toNat >>> 22) % 16384 := by
  simp only [mOf, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [show (16383 : Nat) % 2 ^ 64 = 2 ^ 14 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- **The length is `8 · tcbWords h 1`** (`Scc.Cert.SpawnA64.tcbWords`,
unfolded). -/
theorem lenOf_toNat (h : BitVec 64) :
    (lenOf h).toNat = 8 * (1 * ((h.toNat >>> 8) % 16384 + (h.toNat >>> 22) % 16384) + 1) := by
  have hn := nOf_toNat h
  have hm := mOf_toNat h
  have hn' : (nOf h).toNat < 16384 := by rw [hn]; exact Nat.mod_lt _ (by decide)
  have hm' : (mOf h).toNat < 16384 := by rw [hm]; exact Nat.mod_lt _ (by decide)
  simp only [lenOf, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [← hn, ← hm]
  omega

/-- The length fits well below `2^17`. -/
theorem lenOf_lt (h : BitVec 64) : (lenOf h).toNat < 262152 := by
  rw [lenOf_toNat]
  have := Nat.mod_lt (h.toNat >>> 8) (show 0 < 16384 by decide)
  have := Nat.mod_lt (h.toNat >>> 22) (show 0 < 16384 by decide)
  omega

/-- At `scc_rt_start`'s header: `d = tcbLen`, `m = 0`. -/
theorem lenOf_hdr0 : lenOf hdr0 = tcbLen := by decide
theorem mOf_hdr0 : mOf hdr0 = 0#64 := by decide

/-- At the pre-T5 hello spawn's header `0xC00C03`: `n = 12`, `m = 3`, sixteen words. -/
example : (nOf 0xC00C03#64, mOf 0xC00C03#64, lenOf 0xC00C03#64) = (12#64, 3#64, 128#64) := by decide

/-! ## The specification -/

/-- **Entry** at the header `h`: `Pre` with `x0 = h`. -/
def PreG (g : G) (h : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = h ∧ σ.regs.X1.toBitVec = 1#64

/-- **Exit** (at `g.ra`): `x0` one word past the header at
`pinned + n0 + 8·m`. `scc_rt_pinned_next` holds `n0 + lenOf h`. -/
def PostG (g : G) (h n0 pinned : BitVec 64) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧
  σ.regs.X0.toBitVec = pinned + n0 + mOf h <<< 3 + 8#64

/-- The frame: `sp` down by 192, the saved `x29`/`x30` and the arguments. -/
def Fr0G (h : BitVec 64) (g : G) (σ : AS) : Prop :=
  σ.regs.SP.toBitVec = g.sp - 192#64 ∧ σ.slot (-16) = g.fp ∧ σ.slot (-8) = g.ra ∧
  σ.slot (-192) = h ∧ σ.slot (-184) = 1#64

/-- The frame after the length: `d` and the header's field `m`. -/
def Fr1G (h : BitVec 64) (g : G) (σ : AS) : Prop := Fr0G h g σ ∧ σ.slot (-120) = lenOf h ∧ σ.slot (-152) = mOf h

/-- The frame after the add: the counter's old value `n0`. -/
def Fr2G (h : BitVec 64) (g : G) (n0 : BitVec 64) (σ : AS) : Prop := Fr1G h g σ ∧ σ.slot (-104) = n0

/-- The frame at the header's store: the base and the offset `8·m`. -/
def Fr3G (h : BitVec 64) (g : G) (n0 pinned : BitVec 64) (σ : AS) : Prop :=
  Fr2G h g n0 σ ∧ σ.slot (-80) = pinned + n0 ∧ σ.slot (-64) = mOf h <<< 3

/-! ## At `hdr0` the predicates are the old ones -/

theorem pre_of_gen0 {g : G} {n0 : BitVec 64} {σ : AS} : Pre g n0 σ ↔ PreG g hdr0 σ := Iff.rfl

theorem fr0_of_gen0 {g : G} {σ : AS} : Fr0 g σ ↔ Fr0G hdr0 g σ := Iff.rfl

theorem fr1_of_gen0 {g : G} {σ : AS} : Fr1 g σ ↔ Fr1G hdr0 g σ := by
  rw [Fr1, Fr1G, lenOf_hdr0, mOf_hdr0]; rfl

theorem fr2_of_gen0 {g : G} {n0 : BitVec 64} {σ : AS} : Fr2 g n0 σ ↔ Fr2G hdr0 g n0 σ := by
  rw [Fr2, Fr2G, fr1_of_gen0]

theorem fr3_of_gen0 {g : G} {n0 Q : BitVec 64} {σ : AS} : Fr3 g n0 Q σ ↔ Fr3G hdr0 g n0 Q σ := by
  rw [Fr3, Fr3G, fr2_of_gen0, mOf_hdr0]; rfl

theorem post_of_gen0 {g : G} {n0 Q : BitVec 64} {σ : AS} : Post g n0 Q σ ↔ PostG g hdr0 n0 Q σ := by
  rw [Post, PostG, mOf_hdr0]; simp

/-! ## The walks -/

/-- **The prologue**: from the entry to `.0_entry`, the frame set up. -/
theorem atPro_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} (hp : PreG g h σ) :
    (arun lab atPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat (4 * 6) ∧
    (arun lab atPro ⟨pc, oE, σ⟩).so = ⟨-192, [(.X29, -16)]⟩ ∧ Fr0G h g (arun lab atPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  rw [atPro_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr0G, Spike.Lib.upd_apply, h1, h2, h3, h4, h5]

/-- **The size check is not taken** (`k = 1`). -/
theorem atChk_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} (hf : Fr0G h g σ) :
    (arun lab atChk ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 4) ∧
    (arun lab atChk ⟨pc, oI, σ⟩).so = oI ∧ Fr0G h g (arun lab atChk ⟨pc, oI, σ⟩).σ := by
  have h5 := hf.2.2.2.2
  rw [atChk_run, subs_c, h5]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, hf⟩

/-- **The length**: `d = lenOf h`, `m = mOf h`. -/
theorem atLen_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} (hf : Fr0G h g σ) :
    (arun lab atLen ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 32) ∧
    (arun lab atLen ⟨pc, oI, σ⟩).so = oI ∧ Fr1G h g (arun lab atLen ⟨pc, oI, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf
  rw [atLen_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1G, Fr0G, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, lenOf, nOf, mOf]

/-- **The add's operands**: `x9 = lenOf h`, `x10` the counter's address `P`
(in `x9` before). -/
theorem atArg_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {P : BitVec 64}
    (hf : Fr1G h g σ) (hP : σ.regs.X9.toBitVec = P) :
    (arun lab atArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 3) ∧
    (arun lab atArg ⟨pc, oI, σ⟩).so = oI ∧ Fr1G h g (arun lab atArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = lenOf h ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = P := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := hf
  rw [atArg_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr1G, Fr0G, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, hP]

/-- **The bound is not crossed** when the counter's old value `n0` (in
`x11`) has room for `lenOf h` more bytes below `2^17`. -/
theorem atBnd_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 : BitVec 64}
    (hf : Fr1G h g σ) (h11 : σ.regs.X11.toBitVec = n0) (hn : n0.toNat + (lenOf h).toNat ≤ 131072) :
    (arun lab atBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 9) ∧
    (arun lab atBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr2G h g n0 (arun lab atBnd ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩ := hf
  have hc : ¬ ((StatusFlags.subs (n0 + lenOf h - 131072#64) (n0 + lenOf h) 131072#64).c = true ∧
      (StatusFlags.subs (n0 + lenOf h - 131072#64) (n0 + lenOf h) 131072#64).z = false) := by
    rw [subs_hi, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [atBnd_run, h11, h6, ite_eq_right_iff.mpr (fun h => absurd h hc)]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr2G, Fr1G, Fr0G, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h11]

/-- **The header and its address**: `x9 = h | 1 << 36`, `x10 = Q + n0 + 8·m`
(`Q`, the pinned area's address, in `x9` before). -/
theorem atOk_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr2G h g n0 σ) (hQ : σ.regs.X9.toBitVec = Q) :
    (arun lab atOk ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat (4 * 27) ∧
    (arun lab atOk ⟨pc, oI, σ⟩).so = oI ∧ Fr3G h g n0 Q (arun lab atOk ⟨pc, oI, σ⟩).σ ∧
    (arun lab atOk ⟨pc, oI, σ⟩).σ.regs.X9.toBitVec = h ||| 1#64 <<< 36 ∧
    (arun lab atOk ⟨pc, oI, σ⟩).σ.regs.X10.toBitVec = Q + n0 + mOf h <<< 3 := by
  obtain ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, h8⟩ := hf
  rw [atOk_run]
  refine ⟨by simp only [Int64.add_assoc]; rfl, rfl, ?_⟩
  simp [Fr3G, Fr2G, Fr1G, Fr0G, Spike.Lib.upd_apply, h1, h2, h3, h4, h5, h6, h7, h8, hQ]

/-- **The return**: to `g.ra` with `x0 = Q + n0 + 8·m + 8`, the frame popped. -/
theorem atRet_walkG (lab : Label → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr3G h g n0 Q σ) :
    (arun lab atRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab atRet ⟨pc, oI, σ⟩).so = oE ∧ PostG g h n0 Q (arun lab atRet ⟨pc, oI, σ⟩).σ := by
  obtain ⟨⟨⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, h8⟩, h9, h10⟩ := hf
  rw [atRet_run]
  refine ⟨by rw [h3], rfl, ?_⟩
  simp [PostG, h1, h2, h3, h9, h10, BitVec.sub_add_cancel]

/-- A label's address keeps `Fr1G`. -/
theorem labStep_fr1G (lab : Label → Int64) (L : Label) {g : G} {h : BitVec 64} {σ : AS} (hf : Fr1G h g σ) :
    Fr1G h g (labStep lab L σ) := by
  obtain ⟨-, h2, h3, -⟩ := labStep_spec lab L σ
  simpa [Fr1G, Fr0G, h2, h3] using hf

/-- A label's address keeps `Fr2G`. -/
theorem labStep_fr2G (lab : Label → Int64) (L : Label) {g : G} {h n0 : BitVec 64} {σ : AS}
    (hf : Fr2G h g n0 σ) : Fr2G h g n0 (labStep lab L σ) := by
  obtain ⟨-, h2, h3, -⟩ := labStep_spec lab L σ
  simpa [Fr2G, Fr1G, Fr0G, h2, h3] using hf

end Spike.Lib.A64.Flow.Ret0.AllocTcb

namespace Spike.Lib.A64.Flow.Ret0.StackTake

/-! ## `scc_rt_stack_take` at generation `g`

`StackTake`'s walks are already generic in the old offset `k0`
(`stBnd_walk`'s room `hk`, `Fr4`/`Fr5`, `Post`), and `ThreadInit`'s in
the TCB and the base; the second call is the instance `k0 = 16384·g` with
`g = 1`. Only the room is left to show. -/

/-- The bump offset of generation `g`. -/
def k0Of (g : Nat) : BitVec 64 := BitVec.ofNat 64 (16384 * g)

/-- **Room for the stack of generation `g ≤ 1`** below `2^29` (`stBnd_walk`'s `hk`). -/
theorem k0Of_room {g : Nat} (hg : g ≤ 1) : (k0Of g).toNat + 16384 ≤ 536870912 := by
  unfold k0Of
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The next offset is the next generation's. -/
theorem k0Of_succ (g : Nat) : k0Of g + size0 = k0Of (g + 1) := by
  unfold k0Of size0
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem k0Of_zero : k0Of 0 = 0#64 := rfl

end Spike.Lib.A64.Flow.Ret0.StackTake
