/-
**`scc_rt_alloc_tcb` at any header** (x86-64): the walks of
`X64Ret0AllocTcb` generalised from `scc_rt_start`'s header `2307` to any
header `h` with `k = 1`, for the second call (a spawn's TCB, whose header
has a nonzero `m`). The x86-64 twin of `Spike/Lib/A64Ret0AllocTcbG.lean`.
The blocks, their `arun` equations and the code check `allocTcbIn` are
`X64Ret0AllocTcb`'s, unchanged; only the frame's cells, the values between
blocks and the walks read the header.

    d   = lenOf h = (n + m + 1)·8,  n = (h >> 8) & 16383, m = (h >> 22) & 16383
    hdr = h | 1 << 36               stored at pinned + n0 + 8·m
    rax = pinned + n0 + 8·m + 8     (the TCB, one word past the header)

- `nOf`, `mOf`, `lenOf`: the header's fields and the length the code
  computes; `lenOf_toNat` the same as `8 · tcbWords h 1` of the spawn
  checks (unfolded, so this file needs no trusted import).
- `PreG`, `PostG` and the frame's cells `s0G` … `s5G`: `Pre`, `Post`,
  `s0` … `s5` at the header `h` (the frame predicate `Fr` is unchanged).
- `atPro_walkG` … `atRet_walkG`: the walks; `path_valsG`: the single
  instructions' results between them.
- `pre_of_gen0`, `s*_of_gen0`, `post_of_gen0`: at `hdr0` the general
  predicates are the old ones (`lenOf hdr0 = tcbLen`, `mOf hdr0 = 0`).
- `StackTake.k0Of g` (`16384·g`), `k0Of_room`, `k0Of_succ`: the stack
  allocator's second call is the instance `k0 = k0Of 1` of its generic
  walks.

Where x86-64 differs from AArch64: the frame is `Fr g ss` with a cell list
per stage (`s0G` … `s5G`) where AArch64 has `Fr0G` … `Fr3G`, and every
block between two single instructions has its own walk (`atL0` … `atO5`)
where AArch64 has `atLen`/`atOk`.
-/
import Spike.Lib.X64Ret0StackTake

namespace Spike.Lib.X64.Flow.Ret0.AllocTcb

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64

set_option linter.unusedSimpArgs false

/-! ## The header's fields -/

/-- The header's field `n` (the frame words), bits 8–21. -/
def nOf (h : BitVec 64) : BitVec 64 := h >>> 8 &&& 16383#64

/-- The header's field `m` (the words below the header), bits 22–35. -/
def mOf (h : BitVec 64) : BitVec 64 := h >>> 22 &&& 16383#64

/-- **The TCB's length in bytes** the code computes for `h` and `k = 1`. -/
def lenOf (h : BitVec 64) : BitVec 64 := (nOf h + mOf h + 1#64) <<< 3

theorem nOf_toNat (h : BitVec 64) : (nOf h).toNat = (h.toNat >>> 8) % 16384 := by
  simp only [nOf, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [show (16383 : Nat) % 2 ^ 64 = 2 ^ 14 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem mOf_toNat (h : BitVec 64) : (mOf h).toNat = (h.toNat >>> 22) % 16384 := by
  simp only [mOf, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [show (16383 : Nat) % 2 ^ 64 = 2 ^ 14 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

/-- **The length is `8 · tcbWords h 1`** (`Scc.Cert.SpawnX64.tcbWords`,
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

/-- At `scc_rt_start`'s header: `n = 13`, `d = tcbLen`, `m = 0`. -/
theorem nOf_hdr0 : nOf hdr0 = 13#64 := by decide
theorem lenOf_hdr0 : lenOf hdr0 = tcbLen := by decide
theorem mOf_hdr0 : mOf hdr0 = 0#64 := by decide

/-- At the pre-T5 hello spawn's header `0xC00C03`: `n = 12`, `m = 3`, sixteen words. -/
example : (nOf 0xC00C03#64, mOf 0xC00C03#64, lenOf 0xC00C03#64) = (12#64, 3#64, 128#64) := by decide

/-! ## The specification -/

/-- **Entry** at the header `h`: `Pre` with `%rdi = h`. -/
def PreG (g : G) (h : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧
  σ.regs.rdi.toBitVec = h ∧ σ.regs.rsi.toBitVec = 1#64

/-- **Exit** (at `g.ra`): `%rax` one word past the header at
`pinned + n0 + 8·m`. `scc_rt_pinned_next` holds `n0 + lenOf h`. -/
def PostG (g : G) (h n0 pinned : BitVec 64) (σ : AS) : Prop :=
  σ.regs.rsp.toBitVec = g.sp + 8#64 ∧ σ.regs.rbp.toBitVec = g.fp ∧
  σ.regs.rax.toBitVec = pinned + n0 + mOf h <<< 3 + 8#64

/-- The return address, the saved `%rbp` and the arguments. -/
abbrev s0G (h : BitVec 64) (g : G) : List (Int × BitVec 64) := [(0, g.ra), (-8, g.fp), (-16, h), (-24, 1#64)]
/-- With the field `n`. -/
abbrev sAG (h : BitVec 64) (g : G) : List (Int × BitVec 64) := (-40, nOf h) :: s0G h g
/-- With the field `m`. -/
abbrev s1G (h : BitVec 64) (g : G) : List (Int × BitVec 64) := (-56, mOf h) :: s0G h g
/-- With `d = lenOf h`. -/
abbrev s2G (h : BitVec 64) (g : G) : List (Int × BitVec 64) := (-88, lenOf h) :: s1G h g
/-- With the counter's old value `n0`. -/
abbrev s3G (h : BitVec 64) (g : G) (n0 : BitVec 64) : List (Int × BitVec 64) := (-104, n0) :: s1G h g
/-- With the base `Q + n0`. -/
abbrev s4G (h : BitVec 64) (g : G) (n0 Q : BitVec 64) : List (Int × BitVec 64) := (-128, Q + n0) :: s3G h g n0
/-- With `8·k·m`. -/
abbrev s5G (h : BitVec 64) (g : G) (n0 Q : BitVec 64) : List (Int × BitVec 64) :=
  (-144, mOf h <<< 3) :: s4G h g n0 Q

/-! ## At `hdr0` the predicates are the old ones -/

theorem pre_of_gen0 {g : G} {n0 : BitVec 64} {σ : AS} : Pre g n0 σ ↔ PreG g hdr0 σ := Iff.rfl

theorem s0_of_gen0 (g : G) : s0 g = s0G hdr0 g := rfl
theorem sA_of_gen0 (g : G) : sA g = sAG hdr0 g := by rw [sAG, nOf_hdr0]
theorem s1_of_gen0 (g : G) : s1 g = s1G hdr0 g := by rw [s1G, mOf_hdr0]
theorem s2_of_gen0 (g : G) : s2 g = s2G hdr0 g := by rw [s2G, lenOf_hdr0, ← s1_of_gen0]
theorem s3_of_gen0 (g : G) (n0 : BitVec 64) : s3 g n0 = s3G hdr0 g n0 := by rw [s3G, ← s1_of_gen0]
theorem s4_of_gen0 (g : G) (n0 Q : BitVec 64) : s4 g n0 Q = s4G hdr0 g n0 Q := by rw [s4G, ← s3_of_gen0]
theorem s5_of_gen0 (g : G) (n0 Q : BitVec 64) : s5 g n0 Q = s5G hdr0 g n0 Q := by
  rw [s5G, ← s4_of_gen0, mOf_hdr0]; rfl

theorem post_of_gen0 {g : G} {n0 Q : BitVec 64} {σ : AS} : Post g n0 Q σ ↔ PostG g hdr0 n0 Q σ := by
  rw [Post, PostG, mOf_hdr0]; simp

/-! ## The values along the path -/

/-- **The values along the path at `h`**: the single instructions' results on
the operands the walks give, as the next walks take them (`path_vals` at `h`). -/
theorem path_valsG (h : BitVec 64) :
    h.ushiftRight (((8#64).take 8).toNat &&& 63) = h >>> 8 ∧ (h >>> 8 &&& 16383#64) = nOf h ∧
    h.ushiftRight (((22#64).take 8).toNat &&& 63) = h >>> 22 ∧ (h >>> 22 &&& 16383#64) = mOf h ∧
    (nOf h + mOf h + 1#64) <<< (((3#64).take 8).toNat &&& 63) = lenOf h ∧
    mOf h <<< (((3#64).take 8).toNat &&& 63) = mOf h <<< 3 ∧
    1#64 <<< (((36#64).take 8).toNat &&& 63) = 1#64 <<< 36 := by
  have e8 : ((8#64).take 8).toNat &&& 63 = 8 := by decide
  have e22 : ((22#64).take 8).toNat &&& 63 = 22 := by decide
  have e3 : ((3#64).take 8).toNat &&& 63 = 3 := by decide
  have e36 : ((36#64).take 8).toNat &&& 63 = 36 := by decide
  rw [e8, e22, e3, e36]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The walks -/

/-- Unfolds a frame hypothesis. -/
local macro "frh" h:ident : tactic => `(tactic| simp only [Fr, List.forall_mem_cons, List.forall_mem_nil] at $h:ident)

/-- Closes a walk's goal from the run's normal form. -/
local macro "walk" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Fr, PostG, Reg64s.set64, Reg64s.get64, upd_apply, $ts,*])

/-- **The prologue**: from the entry to `.entry`, the frame set up. -/
theorem atPro_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} (hp : PreG g h σ) :
    (arun lab atPro ⟨pc, oE, σ⟩).pc = pc + Int64.ofNat 19 ∧
    (arun lab atPro ⟨pc, oE, σ⟩).so = oI ∧ Fr g (s0G h g) (arun lab atPro ⟨pc, oE, σ⟩).σ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hp
  rw [atPro_run]
  refine ⟨rfl, rfl, ?_⟩
  walk [h1, h2, h3, h4, h5]
  bv_omega

/-- **The size check is not taken** (`k = 1`). -/
theorem atChk_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s0G h g) σ) :
    (arun lab atChk ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 20 ∧
    (arun lab atChk ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0G h g) (arun lab atChk ⟨pc, oI, σ⟩).σ := by
  frh hf
  rw [atChk_run]
  walk [hf]

/-- On to `.len`. -/
theorem atJ1_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s0G h g) σ) :
    (arun lab atJ1 ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_alloc_tcb.len" ∧
    (arun lab atJ1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0G h g) (arun lab atJ1 ⟨pc, oI, σ⟩).σ := by
  rw [atJ1_run]
  exact ⟨rfl, rfl, hf⟩

/-- `h >> 8`'s operands. -/
theorem atL0_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s0G h g) σ) :
    (arun lab atL0 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 11 ∧
    (arun lab atL0 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0G h g) (arun lab atL0 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL0 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = h ∧
    (arun lab atL0 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 8#64 := by
  frh hf
  rw [atL0_run]
  walk [hf]

/-- `(h >> 8) & 16383`'s operands. -/
theorem atL1_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s0G h g) σ) (ha : σ.regs.rax.toBitVec = h >>> 8) :
    (arun lab atL1 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atL1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s0G h g) (arun lab atL1 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL1 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = h >>> 8 ∧
    (arun lab atL1 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 16383#64 := by
  frh hf
  rw [atL1_run]
  walk [hf, ha]

/-- The field `n` saved; `h >> 22`'s operands. -/
theorem atL2_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s0G h g) σ) (ha : σ.regs.rax.toBitVec = nOf h) :
    (arun lab atL2 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atL2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (sAG h g) (arun lab atL2 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL2 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = h ∧
    (arun lab atL2 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 22#64 := by
  frh hf
  rw [atL2_run]
  walk [hf, ha]

/-- `(h >> 22) & 16383`'s operands. -/
theorem atL3_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (sAG h g) σ) (ha : σ.regs.rax.toBitVec = h >>> 22) :
    (arun lab atL3 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atL3 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (sAG h g) (arun lab atL3 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL3 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = h >>> 22 ∧
    (arun lab atL3 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 16383#64 := by
  frh hf
  rw [atL3_run]
  walk [hf, ha]

/-- `m` saved, `n + m`; `k·(n + m)`'s operands. -/
theorem atL4_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (sAG h g) σ) (ha : σ.regs.rax.toBitVec = mOf h) :
    (arun lab atL4 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 27 ∧
    (arun lab atL4 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1G h g) (arun lab atL4 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL4 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab atL4 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = nOf h + mOf h := by
  frh hf
  rw [atL4_run]
  walk [hf, ha]
  exact BitVec.add_comm _ _

/-- `k·(n + m) + 1`; the shift's operands. -/
theorem atL5_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s1G h g) σ) (ha : σ.regs.rax.toBitVec = 1#64 * (nOf h + mOf h)) :
    (arun lab atL5 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 33 ∧
    (arun lab atL5 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s1G h g) (arun lab atL5 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atL5 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = nOf h + mOf h + 1#64 ∧
    (arun lab atL5 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 3#64 := by
  frh hf
  rw [atL5_run]
  walk [hf, ha]
  exact BitVec.add_comm _ _

/-- **The length** `d = lenOf h` saved. -/
theorem atL6_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS}
    (hf : Fr g (s1G h g) σ) (ha : σ.regs.rax.toBitVec = lenOf h) :
    (arun lab atL6 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 4 ∧
    (arun lab atL6 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2G h g) (arun lab atL6 ⟨pc, oI, σ⟩).σ := by
  frh hf
  rw [atL6_run]
  walk [hf, ha]

/-- **The add's operands**: `%rax = lenOf h`, `%rcx` the counter's address `P`
(in `%rax` before). -/
theorem atArg_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {P : BitVec 64}
    (hf : Fr g (s2G h g) σ) (hP : σ.regs.rax.toBitVec = P) :
    (arun lab atArg ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 12 ∧
    (arun lab atArg ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s2G h g) (arun lab atArg ⟨pc, oI, σ⟩).σ ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = lenOf h ∧
    (arun lab atArg ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = P := by
  frh hf
  rw [atArg_run]
  walk [hf, hP]

/-- **The bound is not crossed** when the counter's old value `n0` (in
`%rax`) has room for `lenOf h` more bytes below `2^17`. -/
theorem atBnd_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 : BitVec 64}
    (hf : Fr g (s2G h g) σ) (ha : σ.regs.rax.toBitVec = n0) (hn : n0.toNat + (lenOf h).toNat ≤ 131072) :
    (arun lab atBnd ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 35 ∧
    (arun lab atBnd ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3G h g n0) (arun lab atBnd ⟨pc, oI, σ⟩).σ := by
  frh hf
  have hr : (σ.regs.rax.toNat : Int) = n0.toNat := by rw [← ha]; rfl
  rw [atBnd_run]
  walk [hf, ha]
  intro h1 h2
  by_cases he : n0.toNat + (lenOf h).toNat = 131072
  · refine absurd (BitVec.eq_of_toNat_eq ?_) h2
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Width.bits] at he ⊢
    omega
  · rw [hr] at h1; omega

/-- On to `.ok`. -/
theorem atJ2_walkG (lab : String → Int64) (pc : Int64) {g : G} {h n0 : BitVec 64} {σ : AS}
    (hf : Fr g (s3G h g n0) σ) :
    (arun lab atJ2 ⟨pc, oI, σ⟩).pc = lab ".Lscc_rt_alloc_tcb.ok" ∧
    (arun lab atJ2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s3G h g n0) (arun lab atJ2 ⟨pc, oI, σ⟩).σ := by
  rw [atJ2_run]
  exact ⟨rfl, rfl, hf⟩

/-- **The base** `Q + n0` saved (`Q`, the pinned area's address, in `%rax`
before); `k·m`'s operands. -/
theorem atO1_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr g (s3G h g n0) σ) (hQ : σ.regs.rax.toBitVec = Q) :
    (arun lab atO1 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 27 ∧
    (arun lab atO1 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s4G h g n0 Q) (arun lab atO1 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO1 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab atO1 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = mOf h := by
  frh hf
  rw [atO1_run]
  walk [hf, hQ]
  exact BitVec.add_comm _ _

/-- `8·k·m`'s operands. -/
theorem atO2_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr g (s4G h g n0 Q) σ) (ha : σ.regs.rax.toBitVec = 1#64 * mOf h) :
    (arun lab atO2 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 15 ∧
    (arun lab atO2 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s4G h g n0 Q) (arun lab atO2 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO2 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = mOf h ∧
    (arun lab atO2 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 3#64 := by
  frh hf
  rw [atO2_run]
  walk [hf, ha]

/-- `8·k·m` saved; `k << 36`'s operands. -/
theorem atO3_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr g (s4G h g n0 Q) σ) (ha : σ.regs.rax.toBitVec = mOf h <<< 3) :
    (arun lab atO3 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 18 ∧
    (arun lab atO3 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5G h g n0 Q) (arun lab atO3 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO3 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = 1#64 ∧
    (arun lab atO3 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 36#64 := by
  frh hf
  rw [atO3_run]
  walk [hf, ha]

/-- `h | k << 36`'s operands. -/
theorem atO4_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr g (s5G h g n0 Q) σ) (ha : σ.regs.rax.toBitVec = 1#64 <<< 36) :
    (arun lab atO4 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 18 ∧
    (arun lab atO4 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5G h g n0 Q) (arun lab atO4 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO4 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = h ∧
    (arun lab atO4 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = 1#64 <<< 36 := by
  frh hf
  rw [atO4_run]
  walk [hf, ha]

/-- **The header and its address**: `%rax = h | 1 << 36`, `%rcx = Q + n0 + 8·m`. -/
theorem atO5_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr g (s5G h g n0 Q) σ) (ha : σ.regs.rax.toBitVec = h ||| 1#64 <<< 36) :
    (arun lab atO5 ⟨pc, oI, σ⟩).pc = pc + Int64.ofNat 42 ∧
    (arun lab atO5 ⟨pc, oI, σ⟩).so = oI ∧ Fr g (s5G h g n0 Q) (arun lab atO5 ⟨pc, oI, σ⟩).σ ∧
    (arun lab atO5 ⟨pc, oI, σ⟩).σ.regs.rax.toBitVec = h ||| 1#64 <<< 36 ∧
    (arun lab atO5 ⟨pc, oI, σ⟩).σ.regs.rcx.toBitVec = Q + n0 + mOf h <<< 3 := by
  frh hf
  rw [atO5_run]
  walk [hf, ha]
  exact BitVec.add_comm _ _

/-- **The return**: to `g.ra` with `%rax = Q + n0 + 8·m + 8`, the frame popped. -/
theorem atRet_walkG (lab : String → Int64) (pc : Int64) {g : G} {h : BitVec 64} {σ : AS} {n0 Q : BitVec 64}
    (hf : Fr g (s5G h g n0 Q) σ) :
    (arun lab atRet ⟨pc, oI, σ⟩).pc = Int64.ofBitVec g.ra ∧
    (arun lab atRet ⟨pc, oI, σ⟩).so = oR ∧ PostG g h n0 Q (arun lab atRet ⟨pc, oI, σ⟩).σ := by
  frh hf
  rw [atRet_run]
  walk [hf]
  ac_rfl

end Spike.Lib.X64.Flow.Ret0.AllocTcb

namespace Spike.Lib.X64.Flow.Ret0.StackTake

/-! ## `scc_rt_stack_take` at generation `g`

`StackTake`'s walks are already generic in the old offset `k0`
(`stBnd_walk`'s room `hk`, `s4`, `Post`), and `ThreadInit`'s in the TCB and
the base; the second call is the instance `k0 = 16384·g` with `g = 1`. Only
the room is left to show. -/

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

end Spike.Lib.X64.Flow.Ret0.StackTake

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.nOf_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.nOf_toNat

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.mOf_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.mOf_toNat

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf_toNat

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf_lt

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.nOf_hdr0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.nOf_hdr0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf_hdr0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf_hdr0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.mOf_hdr0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.mOf_hdr0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.pre_of_gen0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.pre_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.s0_of_gen0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.s0_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.sA_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.sA_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.s1_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.s1_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.s2_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.s2_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.s3_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.s3_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.s4_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.s4_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.s5_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.s5_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.post_of_gen0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.post_of_gen0

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.path_valsG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.path_valsG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atPro_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atPro_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atChk_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atChk_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atJ1_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atJ1_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL0_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL0_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL1_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL1_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL2_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL2_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL3_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL3_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL4_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL4_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL5_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL5_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atL6_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atL6_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atArg_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atArg_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atBnd_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atBnd_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atJ2_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atJ2_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atO1_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atO1_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atO2_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atO2_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atO3_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atO3_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atO4_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atO4_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atO5_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atO5_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.AllocTcb.atRet_walkG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.AllocTcb.atRet_walkG

/-- info: 'Spike.Lib.X64.Flow.Ret0.StackTake.k0Of_room' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.StackTake.k0Of_room

/-- info: 'Spike.Lib.X64.Flow.Ret0.StackTake.k0Of_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.StackTake.k0Of_succ

/-- info: 'Spike.Lib.X64.Flow.Ret0.StackTake.k0Of_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.StackTake.k0Of_zero
