import Kraken.X64.Examples.Sbr.Parse.PsText

/-!
# `ff_ps_read_data`: the specification

`ff_ps_read_data(logctx, gb_host, ps, bits_left)` (`libavcodec/aacps_common.c`, FFmpeg n8.1)
parses one PS data block from the bit reader `*gb_host` into `ps` (a `PSCommonContext`, the
764 bytes `ps->common` of `PsWF`, see `Spec.lean`). It reads from a copy of the reader and
advances `*gb_host` once at the end (`skip_bits_long`) by the bits consumed, or by `bits_left`
on the error paths.

* Logical variables `PArgs`: the caller's memory `R`, the bytes `c` of `*ps`, the reader
  (`buffer`, `index`, `size_in_bits_plus8`, the bytes `[buffer, buffer + L)` the caller owns,
  as in `Grid.GArgs`), and the ten Huffman tables `vlc_ps[]` (`VlcTab`).
* The bitstream contents are not constrained; the reader's precondition is the one of
  `Grid.GridC`.
* Read only: the tables `num_env_tab`, `nr_iidicc_par_tab`, `nr_iidopd_par_tab`, `huff_iid`,
  `ff_log2_tab` (through its GOT slot, the label `ff_log2_tab_got`), the vector constants
  `LCPI0_28` and `LCPI0_30` (the fixed borders), and the Huffman tables with their pointer
  array `vlc_ps`.
* Postcondition, on every return: `PsWF`'s clauses on `ps->common` are kept (`PsWFb`, the row
  `psread_wf` of `ParseModel.lean`), the bounds `PsInv` that keep the array accesses inside
  their rows are kept, the reader's `index` stays within `size_in_bits_plus8`, and the result
  is in `[0, bits_left]`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Ps

/-! ## The Huffman tables

`vlc_ps[10]` holds pointers to ten `VLCElem` tables (`libavcodec/vlc.h`: `int16_t sym;
int16_t len;`, 4 bytes per entry), built by `ff_ps_init_common` with 9 index bits for the
tables `0..5` (`iid`, `icc`) and 5 for `6..9` (`ipd`, `opd`). The code inlines
`get_vlc2(gb, table, bits, max_depth)`: level 1 reads the entry at `show_bits(gb, bits)`; a
subtable entry (`len < 0`) sends the next window `w` to `(w >>> (len & 31)) + sym`. The table
contents are not constrained, except that every subtable index stays inside the table. -/

/-- One table: its address and its bytes (`4 * N` bytes for `N` entries). -/
structure VlcTab where
  p : BitVec 64
  es : List UInt8

/-- The number of entries. -/
abbrev VlcTab.N (t : VlcTab) : Nat := t.es.length / 4

/-- `table[i].sym` and `table[i].len` (little-endian `int16_t`). -/
abbrev vsym (es : List UInt8) (i : Nat) : BitVec 16 :=
  BitVec.ofInt 16 (Int.ofBytes ((es.drop (4 * i)).take 2))

abbrev vlen (es : List UInt8) (i : Nat) : BitVec 16 :=
  BitVec.ofInt 16 (Int.ofBytes ((es.drop (4 * i + 2)).take 2))

/-- The index bits of table `k`. -/
abbrev vbits (k : Nat) : Nat := if k ≤ 5 then 9 else 5

/-- The levels `get_vlc2` reads in table `k` (`max_depth`): 3 for `iid` (`0..3`), 2 for `icc`
(`4, 5`), 1 for `ipd`/`opd` (`6..9`). -/
abbrev vdepth (k : Nat) : Nat := if k ≤ 3 then 3 else if k ≤ 5 then 2 else 1

/-- The entry a subtable entry `i` (`len < 0`) sends the window whose top bits are `j` to:
`j + sym` (32-bit). The code computes `j` as `w >>> (len & 31)` for the 32-bit window `w`. -/
abbrev vnext (es : List UInt8) (i j : Nat) : Nat :=
  (BitVec.ofNat 32 j + (vsym es i).signExtend 32).toNat

/-- A walk of at most `d` levels from entry `i` reads entries of the table only and ends on an
entry with `len ≥ 0` (the code adds the last level's `len` to the index unchecked). -/
def VWalk (es : List UInt8) : Nat → Nat → Prop
  | 0, _ => False
  | d + 1, i => i < es.length / 4 ∧ ((vlen es i).msb = false
      ∨ ∀ j, j < 2 ^ (32 - (vlen es i).toNat % 32) → VWalk es d (vnext es i j))

instance VWalk.dec (es : List UInt8) : ∀ d i, Decidable (VWalk es d i)
  | 0, _ => by unfold VWalk; exact inferInstance
  | d + 1, i => by
    unfold VWalk
    haveI := fun j => VWalk.dec es d j
    exact inferInstance

/-- A table the walk stays inside: every walk of at most `d` levels from a level-1 entry
(`2 ^ nb` of them) is a `VWalk`. A closed, decidable property of the table contents (of the
tables `ff_ps_init_common` builds). -/
def VlcOk (nb d : Nat) (t : VlcTab) : Prop :=
  t.es.length % 4 = 0 ∧ t.N < 2 ^ 28 ∧ ∀ i, i < 2 ^ nb → VWalk t.es d i

instance (nb d : Nat) (t : VlcTab) : Decidable (VlcOk nb d t) := by
  unfold VlcOk; exact inferInstance

variable [CodeEnv]

/-- The pointer cells `vlc_ps[0..n-1]`. -/
def VPtrs (v : Nat → VlcTab) : Nat → Mem 64 → Prop
  | 0 => Std.ExtHashMap.emp
  | n + 1 => Int.toBytes 8 (v n).p.toInt =@ (lab "vlc_ps" + BitVec.ofNat 64 (8 * n)) ⋆ VPtrs v n

/-- The tables `0..n-1`. -/
def VTabs (v : Nat → VlcTab) : Nat → Mem 64 → Prop
  | 0 => Std.ExtHashMap.emp
  | n + 1 => (v n).es =@ (v n).p ⋆ VTabs v n

/-- Every table is `VlcOk` at its index width and depth. -/
def VlcC (v : Nat → VlcTab) : Prop := ∀ k, k < 10 → VlcOk (vbits k) (vdepth k) (v k)

/-! ## The footprint -/

/-- The constant tables the code reads (their values, from the object):
`num_env_tab[2][4]`, `nr_iidicc_par_tab[6]`, `nr_iidopd_par_tab[6]` (`int8_t`),
`huff_iid[4]` (`int`), `ff_log2_tab[0..5]` and its GOT slot, `LCPI0_28` (`{0, 1, 2, 3}`) and
`LCPI0_30` (`4`) of the vectorized fixed-border loop. -/
def ConstW : Mem 64 → Prop :=
  [0, 1, 2, 4, 1, 2, 3, 4] =@ lab "num_env_tab"
  ⋆ ([10, 20, 34, 10, 20, 34] =@ lab "nr_iidicc_par_tab"
  ⋆ ([5, 11, 17, 5, 11, 17] =@ lab "nr_iidopd_par_tab"
  ⋆ ([2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] =@ lab "huff_iid"
  ⋆ (Int.toBytes 8 (lab "ff_log2_tab").toInt =@ lab "ff_log2_tab_got"
  ⋆ ([0, 0, 1, 1, 2, 2] =@ lab "ff_log2_tab"
  ⋆ ([0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0] =@ lab "LCPI0_28"
  ⋆ [4, 0, 0, 0] =@ lab "LCPI0_30"))))))

/-- What is only read: the Huffman tables with `vlc_ps`, and `ConstW`. -/
def PsTabs (v : Nat → VlcTab) : Mem 64 → Prop :=
  VPtrs v 10 ⋆ (VTabs v 10 ⋆ ConstW)

structure PArgs where
  R : Mem 64 → Prop
  c : List UInt8
  buf : BitVec 64
  idx : BitVec 32
  p8 : BitVec 32
  L : Nat
  v : Nat → VlcTab

/-- `*gb` at `g` with `index = i` (`size_in_bits` raw), as `Grid.GbW`. -/
abbrev GbW (g : BitVec 64) (x : PArgs) (i : BitVec 32) : Mem 64 → Prop :=
  Int.toBytes 8 x.buf.toInt =@ g ⋆ (cell4 (g + 8#64) i ⋆ (4 ?@ (g + 0xc#64)
    ⋆ cell4 (g + 0x10#64) x.p8))

/-- The footprint at the values `c` of `*ps` and the reader's `index` `i`: `*ps`, `*gb_host`,
the bitstream bytes, the read-only tables, and `av_log`'s state `Ext`. -/
abbrev PF (Ext : Mem 64 → Prop) (x : PArgs) (t : MachineData) (c : List UInt8) (i : BitVec 32) :
    Mem 64 → Prop :=
  c =@ arg2 t ⋆ (GbW (arg1 t) x i ⋆ (Blocks [(x.buf, x.L)] ⋆ (PsTabs x.v ⋆ Ext)))

/-! ## The invariants -/

/-- `PsWF`'s clauses on `ps->common` (`PsWF c h ↔ PsWFb c ∧` the clauses on `h`). -/
def PsWFb (c : List UInt8) : Prop :=
  c.length = 764
  ∧ (i32 c 756 = 0 ∨ i32 c 756 = 1)
  ∧ (0 ≤ i32 c 44 ∧ i32 c 44 ≤ 5) ∧ (0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5)
  ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (246 + 34 * e + b) ∧ i8 c (246 + 34 * e + b) ≤ 7)
  ∧ (∀ e < 5, ∀ b < 34, 0 ≤ i8 c (416 + 34 * e + b) ∧ i8 c (416 + 34 * e + b) ≤ 7
      ∧ 0 ≤ i8 c (586 + 34 * e + b) ∧ i8 c (586 + 34 * e + b) ≤ 7)
  ∧ (i32 c 0 ≠ 0 →
      1 ≤ i32 c 44
      ∧ i32 c 52 = -1
      ∧ (∀ e : Nat, (e : Int) < i32 c 44 → i32 c (52 + 4 * e) ≤ i32 c (52 + 4 * (e + 1)))
      ∧ i32 c (52 + 4 * (i32 c 44).toNat) = 31
      ∧ (i32 c 4 ≠ 0 → i32 c 12 = 10 ∨ i32 c 12 = 20 ∨ i32 c 12 = 34)
      ∧ (∀ e : Nat, (e : Int) < i32 c 44 → ∀ b : Nat, b < 34 →
          (i32 c 4 = 0 ∨ (b : Int) < i32 c 12) →
          -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * e + b)
            ∧ i8 c (76 + 34 * e + b) ≤ 7 + 8 * i32 c 8))

/-- The bounds that keep the row accesses `PAR[e][b]` inside `[5][34]` (the object traps,
`ud1`, outside): `nr_iid_par` (12), `nr_ipdopd_par` (16), `nr_icc_par` (28) at most 34,
`num_env_old` (40) and `num_env` (44) in `[0, 5]`, `iid_quant` (8) in `{0, 1}` (it selects the
`iid` range). Without a header the code uses the values a previous call left; each is written
only from the tables or as a comparison result. -/
def PsInv (c : List UInt8) : Prop :=
  c.length = 764
  ∧ i32 c 12 ≤ 34 ∧ i32 c 16 ≤ 34 ∧ i32 c 28 ≤ 34
  ∧ (0 ≤ i32 c 40 ∧ i32 c 40 ≤ 5) ∧ (0 ≤ i32 c 44 ∧ i32 c 44 ≤ 5)
  ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1)

/-- `bits_left`, the low 32 bits of `rcx`. -/
abbrev bitsLeft (t : MachineData) : BitVec 32 := (arg3 t).setWidth 32

/-- The side conditions. -/
def PsC (x : PArgs) (t : MachineData) : Prop :=
  PsInv x.c ∧ VlcC x.v
  ∧ x.idx.toNat ≤ x.p8.toNat ∧ x.p8.toNat < 2 ^ 31 ∧ x.p8.toNat / 8 + 4 ≤ x.L ∧ x.L < 2 ^ 32
  ∧ 0 ≤ (bitsLeft t).toInt

/-- The stack: six pushes, `0x78` bytes of locals, the return slot of a call, the callee's
`k`. -/
abbrev psNeed (k : Nat) : Nat := 0xb0 + k

abbrev PsPre (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t : MachineData) :
    Prop :=
  CallPre (psNeed k) (PF Ext x t x.c x.idx ⋆ x.R) ra t ∧ PsC x t

/-- What a return leaves: `PsWFb` kept, `PsInv` kept, the reader's `index` within
`size_in_bits_plus8`, the result in `[0, bits_left]`. -/
def PsOut (x : PArgs) (t : MachineData) (c : List UInt8) (i : BitVec 32) (ret : BitVec 32) :
    Prop :=
  PsInv c ∧ (PsWFb x.c → PsWFb c)
  ∧ i.toNat ≤ x.p8.toNat
  ∧ 0 ≤ ret.toInt ∧ ret.toInt ≤ (bitsLeft t).toInt

abbrev PsPost (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ c i, PsOut x t c i ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (psNeed k) (PF Ext x t c i ⋆ x.R) ra t s

/-- The procedure's contract, given `av_log`'s and `memset`'s. -/
abbrev PsReadSpec (k : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "ff_ps_read_data") (PsPre k Ext) (PsPost k Ext)

/-- `PsWF` is `PsWFb` with the clauses on the phase histories. -/
theorem psWF_iff (c h : List UInt8) :
    PsWF c h ↔ PsWFb c ∧ h.length = 68
      ∧ (∀ b < 34, 0 ≤ i8 h b ∧ i8 h b ≤ 63 ∧ 0 ≤ i8 h (34 + b) ∧ i8 h (34 + b) ≤ 63) := by
  unfold PsWF PsWFb
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    exact ⟨⟨a1, a3, a4, a5, a6, a7, a8, a10⟩, a2, a9⟩
  · rintro ⟨⟨a1, a3, a4, a5, a6, a7, a8, a10⟩, a2, a9⟩
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩

end Kraken.Examples.Sbr.Ps
