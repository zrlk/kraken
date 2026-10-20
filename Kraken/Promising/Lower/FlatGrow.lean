/-
WeakCore's FlatHashMap growth (`rawIns`, `mvL`, `mvG`, `grow`; portable, `Int`
keys and values), lowered to AArch64 on the sequential machine-founded wp,
total correctness.

§1 is the model: `rawInsN`, `mvLN`, `mvGN`, `growN`, WeakCore's `rawInsD`,
`mvLD`, `mvGD`, `growD` at `x = false`, built on `FlatInsert.lean`'s `freeN`
and `placeT`. §2 states the abstract map (`ents`: the key/value pairs of the
full slots) and checks on a full one-group table that growth preserves it.
§3 unfolds the model block by block, §4 frames a table under stores elsewhere,
§5 is the code, `grow_spec`, and `full1_hyps`.

**Deviation (allocation).** WeakCore's `grow` allocates the new control and
slot buffers with `newBuf`. Here the caller provides them: already zeroed
(control bytes `0` = empty, slots `0`), of WeakCore's sizes (`m₂ = 2m + 1`
groups − 1, `c₂ = 8(m₂ + 1) − 1` slots − 1), and disjoint from the old buffers
and from each other.

Other differences from WeakCore: `rawIns` (with `hash` and `eq` at `Int`) is
inlined in `mvL`'s loop; the moved pair is written to the new table before the
old slot is zeroed (WeakCore exchanges first; the final memory is the same);
`setCtrl`'s byte store is a word read-modify-write, as in `FlatInsert.lean`;
the results come back in `insert`'s argument registers. `grow_spec` assumes
that growth terminates (`(growN ..).isSome`, every `freeSlot` probe ends);
`full1_hyps` shows the hypotheses hold at `full1`.
-/
import Kraken.Promising.Lower.FlatInsert
import Kraken.WordLemmas

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat.Grow

/-! ## 1. The model -/

/-- WeakCore's `rawIns` at `Int` keys and values (a key known to be absent):
`freeSlot` from the hash's start, then `place` (control byte, key, value),
`gl` less `isE`, `n + 1`; `none` is a `freeSlot` probe out of fuel. -/
def rawInsN (T : Tbl) (k v gl n : Nat) : Option (Tbl × Nat × Nat) :=
  match freeN T (T.mv + 1) (hashN k).2 0 with
  | none => none
  | some (sr, isE) => some (placeT T sr (hashN k).1 k v, bitN .wsub gl isE, bitN .wadd n 1)

theorem clearLow_lt' (mk : Nat) (h : mk ≠ 0) : bitN .and mk (bitN .wsub mk 1) < mk := by
  simp only [bitN]
  have h1 := Nat.mod_le mk W64
  by_cases h0 : mk % W64 = 0
  · have := @Nat.and_le_left (mk % W64) ((mk % W64 + W64 - 1 % W64) % W64 % W64)
    omega
  · have hl : (mk % W64 + W64 - 1 % W64) % W64 % W64 = mk % W64 - 1 := by
      have : mk % W64 < W64 := Nat.mod_lt _ (by decide)
      rw [show 1 % W64 = 1 by decide, Nat.mod_mod,
        show mk % W64 + W64 - 1 = (mk % W64 - 1) + W64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hl]
    exact Nat.lt_of_lt_of_le (Nat.and_pred_lt _ h0) h1

/-- The growth state: old table, new table, `gl`, `n`. -/
abbrev St := Tbl × Tbl × Nat × Nat

/-- The old slot of lane `ctz fm / 8` of the group at slot `base`. -/
def oslot (O : Tbl) (base fm : Nat) : Nat :=
  bandN (bitN .or base (bitN .shr (bit1N .ctz fm) 3)) O.cv

/-- The old table with slot `s` zeroed (`xchgAt osb s (zero ST)`). -/
def zeroSlot (O : Tbl) (s : Nat) : Tbl :=
  { O with key := upd O.key s 0, val := upd O.val s 0 }

/-- WeakCore's `mvL` [c]: move the full lanes `fm` of the old group at slot
`base` (lowest first): exchange the old slot with zero, `rawIns` its pair. -/
def mvLN (base : Nat) (O N : Tbl) (gl n fm : Nat) : Option St :=
  if _h : fm = 0 then some (O, N, gl, n)
  else
    let s := oslot O base fm
    match rawInsN N (O.key s) (O.val s) gl n with
    | none => none
    | some (N', gl', n') => mvLN base (zeroSlot O s) N' gl' n' (bitN .and fm (bitN .wsub fm 1))
termination_by fm
decreasing_by exact clearLow_lt' fm _h

/-- WeakCore's `mvG` [i, d, c]: the full lanes (`w & H8`) of old group `i`
(`loadAt ocb i`, no mask), then groups `i + 1 … i + d`. -/
def mvGN : Nat → Tbl → Tbl → Nat → Nat → Nat → Option St
  | 0, O, N, gl, n, i => mvLN (bitN .shl i 3) O N gl n (bitN .and (O.ctrl i) H8)
  | d + 1, O, N, gl, n, i => (mvLN (bitN .shl i 3) O N gl n (bitN .and (O.ctrl i) H8)).bind
      fun r => mvGN d r.1 r.2.1 r.2.2.1 r.2.2.2 (i + 1)

/-- The new (zeroed) table at the caller's buffers: `m₂ = 2m + 1`,
`c₂ = 8(m₂ + 1) − 1`. -/
def newT (O : Tbl) (cb sb : BitVec 64) : Tbl where
  mv := 2 * O.mv + 1
  cv := 8 * (2 * O.mv + 2) - 1
  ctrl := fun _ => 0
  key := fun _ => 0
  val := fun _ => 0
  cb := cb
  sb := sb

/-- `grow`'s fresh `growth_left`: `capI − capI / 8` with `capI = c₂ + 1`. -/
def glN (O : Tbl) : Nat :=
  let capI := bitN .wadd (8 * (2 * O.mv + 2) - 1) 1
  bitN .wsub capI (bitN .shr capI 3)

/-- WeakCore's `grow` at `Int` keys and values, on caller-provided zeroed
buffers: the old table (slots zeroed), the new table, its `gl` and `n`. The
input `gl`, `n` are not read (as in WeakCore). -/
def growN (O : Tbl) (cb sb : BitVec 64) : Option St :=
  mvGN O.mv O (newT O cb sb) (glN O) 0 0

/-! ## 2. The abstract map -/

/-- The key/value pairs of the full slots (control byte `≥ 0x80`), in slot
order, reading slot `s`'s byte as lane `s % 8` of word `s / 8`. -/
def ents (T : Tbl) : List (Nat × Nat) :=
  (List.range (T.cv + 1)).filterMap fun s =>
    if 128 ≤ laneN8 (T.ctrl (s / 8)) (s % 8) then some (T.key s, T.val s) else none

/-- **Growth preserves the abstract map**: the new table's full slots hold the
old table's pairs, up to order. -/
def GrowKeeps (O : Tbl) (cb sb : BitVec 64) : Prop :=
  ∀ r, growN O cb sb = some r → (ents r.2.1).Perm (ents O)

/-! ### A full one-group table -/

/-- Seven keys `1 … 7` (values `10k`) in lanes `0 … 6`, lane 7 empty: `gl = 0`
after seven inserts into `new`. -/
def full1 : Tbl where
  mv := 0
  cv := 7
  ctrl := fun _ => (List.range 7).foldl (fun w j => w + (hashN (j + 1)).1 * 2 ^ (8 * j)) 0
  key := fun s => if s < 7 then s + 1 else 0
  val := fun s => if s < 7 then 10 * (s + 1) else 0
  cb := 0x1000#64
  sb := 0x2000#64

theorem full1_lookup : (List.range 7).all (fun j => lookupN full1 (j + 1) == some (some (10 * (j + 1))))
    = true := by decide +kernel

theorem full1_grow :
    (growN full1 0x3000#64 0x4000#64).map (fun r => (decide ((ents r.2.1).Perm (ents full1)),
      (List.range 7).all (fun j => lookupN r.2.1 (j + 1) == some (some (10 * (j + 1)))),
      r.2.2.1, r.2.2.2, (List.range 8).all (fun s => r.1.key s == 0 && r.1.val s == 0)))
    = some (true, true, 7, 7, true) := by decide +kernel

/-! ## 3. The model, block by block -/

/-- `mvG`'s rest once `mvL` of group `i` has answered `r`: done (`d = 0`), or
groups `i + 1 … i + d`. -/
def contG (d i : Nat) (r : Option St) : Option St :=
  match d with
  | 0 => r
  | d + 1 => r.bind fun r => mvGN d r.1 r.2.1 r.2.2.1 r.2.2.2 (i + 1)

theorem mvGN_eq (d i gl n : Nat) (O N : Tbl) :
    mvGN d O N gl n i = contG d i (mvLN (bitN .shl i 3) O N gl n (bitN .and (O.ctrl i) H8)) := by
  cases d <;> rfl

/-- `mvL`'s rest once `freeSlot` (in the new table) has answered `r`. -/
def laneK (base : Nat) (O N : Tbl) (gl n fm : Nat) : Option (Nat × Nat) → Option St
  | none => none
  | some (sr, isE) =>
    mvLN base (zeroSlot O (oslot O base fm))
      (placeT N sr (hashN (O.key (oslot O base fm))).1 (O.key (oslot O base fm))
        (O.val (oslot O base fm)))
      (bitN .wsub gl isE) (bitN .wadd n 1) (bitN .and fm (bitN .wsub fm 1))

theorem mvLN_ne {base gl n fm : Nat} (O N : Tbl) (h : fm ≠ 0) :
    mvLN base O N gl n fm = laneK base O N gl n fm
      (freeN N (N.mv + 1) (hashN (O.key (oslot O base fm))).2 0) := by
  rw [mvLN]; simp only [h, dite_false]; unfold rawInsN
  cases freeN N (N.mv + 1) (hashN (O.key (oslot O base fm))).2 0 <;> rfl

theorem glN_eq (O : Tbl) (h : 16 * O.mv + 16 < W64) : glN O = 16 * O.mv + 16 - (16 * O.mv + 16) / 8 := by
  have e : bitN .wadd (8 * (2 * O.mv + 2) - 1) 1 = 16 * O.mv + 16 := by
    simp only [bitN, W64] at h ⊢; rw [Nat.mod_eq_of_lt (a := 1) (by decide)]; omega
  simp only [glN, e]
  simp only [W64] at h
  simp only [bitN, W64, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt h, Nat.reduceMod, Nat.reducePow]
  omega
theorem gl_bv (O : Tbl) (x : BitVec 64) (h2 : x.toNat = O.mv) (h : 16 * O.mv + 16 < W64) :
    rv (x <<< 4 + 8#64 + 8#64 - (x <<< 4 + 8#64 + 8#64) >>> 3) = glN O := by
  have hA : (x <<< 4 + 8#64 + 8#64).toNat = 16 * O.mv + 16 := by
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h2] at h ⊢
    simp only [W64] at h; simp only [BitVec.toNat_ofNat]; omega
  have hB : ((x <<< 4 + 8#64 + 8#64) >>> 3).toNat = (16 * O.mv + 16) / 8 := by
    rw [BitVec.toNat_ushiftRight, hA, Nat.shiftRight_eq_div_pow]
  rw [glN_eq O h, rv_def, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hA, hB]; omega), hA, hB]

theorem mvLN_zero (base gl n : Nat) (O N : Tbl) : mvLN base O N gl n 0 = some (O, N, gl, n) := by
  rw [mvLN]; rfl

theorem freeN_zero (T : Tbl) (p s : Nat) : freeN T 0 p s = none := rfl

/-! ## 4. Memory: a table is kept by stores elsewhere -/

/-- The table's words are 64-bit. -/
structure Wf (T : Tbl) : Prop where
  ctrl : ∀ g, T.ctrl g < W64
  key : ∀ s, T.key s < W64
  val : ∀ s, T.val s < W64

theorem W64_pos : (0 : Nat) < W64 := by decide

/-- `Mem.loadInt_congr` (`Kraken/WordLemmas.lean`) at 8 bytes; kept as an
alias. -/
theorem loadInt_congr {m m' : DataMem} {a : BitVec 64}
    (h : ∀ i < 8, m'.get? (a + BitVec.ofNat 64 i) = m.get? (a + BitVec.ofNat 64 i)) :
    m'.loadInt a 8 = m.loadInt a 8 :=
  Mem.loadInt_congr h

set_option linter.unusedVariables false in
/-- A word at offset `o` of a region of `len` bytes lies inside it
(`BitVec.toNat_offset_sub_lt`, which needs no bound on `len`; kept as an
alias, with its hypothesis `hl`). -/
theorem word_in (x : BitVec 64) (o len i : Nat) (h : o + 8 ≤ len) (hl : len ≤ W64) (hi : i < 8) :
    (x + BitVec.ofNat 64 o + BitVec.ofNat 64 i - x).toNat < len :=
  BitVec.toNat_offset_sub_lt x o len i (by omega)

/-- `InMem` survives any change outside the table's bytes. -/
theorem inMem_frame {T : Tbl} {m m' : DataMem} (hm : T.InMem m) (hs : T.Sep)
    (h : ∀ a, T.Owns a → m'.get? a = m.get? a) : T.InMem m' := by
  have := hs.lo; have := hs.hi; have := (T.sb - T.cb).isLt
  have hW : W64 = 18446744073709551616 := rfl
  refine ⟨fun g hg => ?_, fun s hs' => ⟨?_, ?_⟩⟩
  · have := hm.1 g hg; rw [ctrl_addr] at this ⊢
    rw [loadInt_congr fun i hi => h _ (Or.inl (word_in _ _ _ i (by omega) (by omega) hi)), this]
  · rw [shl_ofNat]
    have := (hm.2 s hs').1; rw [shl_ofNat] at this
    rw [loadInt_congr fun i hi => h _ (Or.inr (word_in _ _ _ i (by omega) (by omega) hi)), this]
  · have e : T.sb + s <<< 4 + 8#64 = T.sb + BitVec.ofNat 64 (2 ^ 4 * s.toNat + 8) := by
      rw [shl_ofNat]; bv_omega
    have := (hm.2 s hs').2; rw [e] at this ⊢
    rw [loadInt_congr fun i hi => h _ (Or.inr (word_in _ _ _ i (by omega) (by omega) hi)), this]

/-! ## 5. The code and its specification

ABI: `x0`–`x3` = the old table's `cb`, `sb`, `m`, `c`; `x4`, `x5` = the new
(zeroed) buffers. Results: `x0`–`x3` = the new table's `cb`, `sb`, `m₂`, `c₂`,
`x6 = gl`, `x7 = n` (`insert`'s argument registers). Scratch: `x8`–`x17`;
`x18`–`x30` and `sp` are untouched. `rawIns` is inlined in `mvL`'s loop. -/

/-- `grow`, lowered. Blocks: the sizes; `grp` (`mvG`: load old group `i`, its
full lanes); `lane` (`mvL`: the lowest full lane's old slot, the hash of its
key); `free` (one group of `freeSlot` in the new table); `place` (`isE`,
`setCtrl` as a word read-modify-write, key and value across, the old slot
zeroed, `clearLow`); `gnext` (`mvG`'s `ifeq dv 0`, `i + 1`); `done`. -/
def flatGrow : Program := parseAArch64("
flat_grow:
  lsl x6, x2, #1
  add x6, x6, #1
  add x7, x6, #1
  lsl x7, x7, #3
  lsr x8, x7, #3
  sub x7, x7, x8
  movz x8, #0
  movz x9, #0
grp:
  ldr x10, [x0, x9, lsl #3]
  and x10, x10, #0x8080808080808080
lane:
  cbz x10, gnext
  rbit x12, x10
  clz x12, x12
  lsr x12, x12, #3
  lsl x11, x9, #3
  orr x11, x11, x12
  and x11, x11, x3
  lsl x11, x11, #4
  add x11, x1, x11
  ldr x12, [x11]
  movz x16, #0x7c15
  movk x16, #0x7f4a, lsl #16
  movk x16, #0x79b9, lsl #32
  movk x16, #0x9e37, lsl #48
  umulh x14, x12, x16
  mul x17, x12, x16
  eor x14, x14, x17
  and x17, x14, #0x7f
  orr x13, x17, #0x80
  lsr x14, x14, #7
  movz x15, #0
free:
  and x16, x14, x6
  ldr x16, [x4, x16, lsl #3]
  mvn x17, x16
  and x17, x17, #0x8080808080808080
  cbnz x17, place
  add x15, x15, #1
  add x14, x14, x15
  b free
place:
  rbit x17, x17
  clz x17, x17
  and x14, x14, x6
  lsl x14, x14, #3
  lsr x15, x17, #3
  orr x14, x14, x15
  mov x15, #0x7f7f7f7f7f7f7f7f
  and x12, x16, x15
  add x12, x12, x15
  orr x12, x12, x16
  orr x12, x12, x15
  mvn x12, x12
  lsr x12, x12, x17
  and x12, x12, #1
  sub x7, x7, x12
  add x8, x8, #1
  lsr x15, x14, #3
  and x15, x15, x6
  and x17, x14, #7
  lsl x17, x17, #3
  ldr x16, [x4, x15, lsl #3]
  lsr x12, x16, x17
  and x12, x12, #0xff
  lsl x12, x12, x17
  sub x16, x16, x12
  and x12, x13, #0xff
  lsl x12, x12, x17
  add x16, x16, x12
  str x16, [x4, x15, lsl #3]
  lsl x15, x6, #3
  orr x15, x15, #7
  and x15, x14, x15
  lsl x15, x15, #4
  add x15, x5, x15
  ldr x12, [x11]
  str x12, [x15]
  ldr x12, [x11, #8]
  str x12, [x15, #8]
  str xzr, [x11]
  str xzr, [x11, #8]
  sub x12, x10, #1
  and x10, x10, x12
  b lane
gnext:
  cmp x9, x2
  b.eq done
  add x9, x9, #1
  b grp
done:
  lsl x3, x6, #3
  orr x3, x3, #7
  mov x2, x6
  mov x6, x7
  mov x7, x8
  mov x0, x4
  mov x1, x5
  ret
")

/-- `grow`'s logical arguments: the old table and the new buffers. -/
structure GrowX where
  O : Tbl
  cb : BitVec 64
  sb : BitVec 64

/-- The new (zeroed) table. -/
abbrev GrowX.N (x : GrowX) : Tbl := newT x.O x.cb x.sb

/-- The arguments in their registers, and the return address. -/
def GArgs (x : GrowX) (ra : Int64) (s : MachineData) : Prop :=
  s.regs.X0.toBitVec = x.O.cb ∧ s.regs.X1.toBitVec = x.O.sb ∧ rv s.regs.X2.toBitVec = x.O.mv
    ∧ rv s.regs.X3.toBitVec = x.O.cv ∧ s.regs.X4.toBitVec = x.cb ∧ s.regs.X5.toBitVec = x.sb
    ∧ s.regs.X30.toBitVec = ra.toBitVec

/-- The start-state hypotheses on the tables: R-INT, both tables' buffers
apart, the old and new tables disjoint, and **growth's termination**
(`growN` answers: every `freeSlot` probe ends within the new table's groups). -/
structure GrowHyps (x : GrowX) : Prop where
  wf : Wf x.O
  sepO : x.O.Sep
  sepN : x.N.Sep
  disj : ∀ a, x.O.Owns a → ¬ x.N.Owns a
  ends : (growN x.O x.cb x.sb).isSome

/-- `grow`'s precondition: the arguments, both tables in memory (the new one
zeroed), and `GrowHyps`. -/
def GrowPre (x : GrowX) (ra : Int64) (t : MachineData) : Prop :=
  GArgs x ra t ∧ x.O.InMem t.dmem ∧ x.N.InMem t.dmem ∧ GrowHyps x

/-- `grow`'s postcondition: the model's answer (the new table, `gl`, `n`) in
`insert`'s argument registers, the new table and the old one (slots zeroed)
in memory, every byte outside the four buffers as it was, `sp` and
`x19`–`x28` unchanged. -/
def GrowPost (x : GrowX) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ O' N' gl n, growN x.O x.cb x.sb = some (O', N', gl, n) ∧ s.regs.X0.toBitVec = x.cb
    ∧ s.regs.X1.toBitVec = x.sb ∧ rv s.regs.X2.toBitVec = x.N.mv ∧ rv s.regs.X3.toBitVec = x.N.cv
    ∧ rv s.regs.X6.toBitVec = gl ∧ rv s.regs.X7.toBitVec = n ∧ N'.InMem s.dmem ∧ O'.InMem s.dmem
    ∧ (∀ a, ¬ x.O.Owns a → ¬ x.N.Owns a → s.dmem.get? a = t₀.dmem.get? a) ∧ Callee t₀ s

/-- The tables mid-growth: the old one (`ok`, `ov`) and the new one (`nc`,
`nk`, `nv`) in memory, 64-bit, and the frame. -/
def Mid (x : GrowX) (t₀ s : MachineData) (ok ov nc nk nv : Nat → Nat) : Prop :=
  { x.O with key := ok, val := ov }.InMem s.dmem
    ∧ { x.N with ctrl := nc, key := nk, val := nv }.InMem s.dmem
    ∧ Wf { x.O with key := ok, val := ov } ∧ Wf { x.N with ctrl := nc, key := nk, val := nv }
    ∧ ∀ a, ¬ x.O.Owns a → ¬ x.N.Owns a → s.dmem.get? a = t₀.dmem.get? a

/-- What every block after the sizes keeps. -/
def GCom (x : GrowX) (ra : Int64) (t₀ s : MachineData) (ok ov nc nk nv : Nat → Nat) (gl n : Nat) :
    Prop :=
  GArgs x ra s ∧ GrowHyps x ∧ Callee t₀ s ∧ rv s.regs.X6.toBitVec = x.N.mv
    ∧ rv s.regs.X7.toBitVec = gl ∧ rv s.regs.X8.toBitVec = n ∧ rv s.regs.X9.toBitVec ≤ x.O.mv
    ∧ Mid x t₀ s ok ov nc nk nv

/-- The lane's old slot (`ctz fm / 8` of group `i`). -/
abbrev osl (x : GrowX) (ok ov : Nat → Nat) (s : MachineData) : Nat :=
  oslot { x.O with key := ok, val := ov } (bitN .shl (rv s.regs.X9.toBitVec) 3) (rv s.regs.X10.toBitVec)

/-- The facts of the `freeSlot` loop. -/
def FreeI (x : GrowX) (ra : Int64) (t₀ s : MachineData) (ok ov nc nk nv : Nat → Nat) (gl n : Nat) :
    Prop :=
  GCom x ra t₀ s ok ov nc nk nv gl n ∧ rv s.regs.X10.toBitVec ≠ 0
    ∧ s.regs.X11.toBitVec = x.O.sb + BitVec.ofNat 64 (osl x ok ov s) <<< 4
    ∧ rv s.regs.X13.toBitVec = (hashN (ok (osl x ok ov s))).1 ∧ rv s.regs.X15.toBitVec ≤ x.N.mv
    ∧ freeN { x.N with ctrl := nc, key := nk, val := nv } (x.N.mv + 1 - rv s.regs.X15.toBitVec)
        (rv s.regs.X14.toBitVec) (rv s.regs.X15.toBitVec)
      = freeN { x.N with ctrl := nc, key := nk, val := nv } (x.N.mv + 1) (hashN (ok (osl x ok ov s))).2 0
    ∧ contG (x.O.mv - rv s.regs.X9.toBitVec) (rv s.regs.X9.toBitVec)
        (laneK (bitN .shl (rv s.regs.X9.toBitVec) 3) { x.O with key := ok, val := ov }
          { x.N with ctrl := nc, key := nk, val := nv } gl n (rv s.regs.X10.toBitVec)
          (freeN { x.N with ctrl := nc, key := nk, val := nv } (x.N.mv + 1)
            (hashN (ok (osl x ok ov s))).2 0)) = growN x.O x.cb x.sb

/-- The spec table. -/
def growTable (x : GrowX) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "flat_grow", s => s = t₀ ∧ GrowPre x ra t₀
  | "grp", s => ∃ ok ov nc nk nv gl n, GCom x ra t₀ s ok ov nc nk nv gl n
      ∧ mvGN (x.O.mv - rv s.regs.X9.toBitVec) { x.O with key := ok, val := ov }
          { x.N with ctrl := nc, key := nk, val := nv } gl n (rv s.regs.X9.toBitVec)
        = growN x.O x.cb x.sb
  | "lane", s => ∃ ok ov nc nk nv gl n, GCom x ra t₀ s ok ov nc nk nv gl n
      ∧ contG (x.O.mv - rv s.regs.X9.toBitVec) (rv s.regs.X9.toBitVec)
          (mvLN (bitN .shl (rv s.regs.X9.toBitVec) 3) { x.O with key := ok, val := ov }
            { x.N with ctrl := nc, key := nk, val := nv } gl n (rv s.regs.X10.toBitVec))
        = growN x.O x.cb x.sb
  | "free", s => ∃ ok ov nc nk nv gl n, FreeI x ra t₀ s ok ov nc nk nv gl n
  | "place", s => ∃ ok ov nc nk nv gl n, FreeI x ra t₀ s ok ov nc nk nv gl n
      ∧ s.regs.X16.toBitVec = BitVec.ofNat 64 (nc (rv (s.regs.X14.toBitVec &&& s.regs.X6.toBitVec)))
      ∧ s.regs.X17.toBitVec = ~~~s.regs.X16.toBitVec &&& 0x8080808080808080#64
      ∧ s.regs.X17.toBitVec ≠ 0#64
  | "gnext", s => ∃ ok ov nc nk nv gl n, GCom x ra t₀ s ok ov nc nk nv gl n
      ∧ contG (x.O.mv - rv s.regs.X9.toBitVec) (rv s.regs.X9.toBitVec)
          (some ({ x.O with key := ok, val := ov }, { x.N with ctrl := nc, key := nk, val := nv }, gl, n))
        = growN x.O x.cb x.sb
  | "done", s => ∃ ok ov nc nk nv gl n, GCom x ra t₀ s ok ov nc nk nv gl n
      ∧ some ({ x.O with key := ok, val := ov }, { x.N with ctrl := nc, key := nk, val := nv }, gl, n)
        = growN x.O x.cb x.sb
  | _, _ => False

/-- The lexicographic variant: old groups left, the lane mask, the `freeSlot`
fuel (`K` bounds the last two). -/
def K : Nat := W64 + 3
def M : Nat := W64 * K
def growVar : Label → MachineData → Nat
  | "flat_grow", s => (rv s.regs.X2.toBitVec + 2) * M
  | "grp", s => (rv s.regs.X2.toBitVec - rv s.regs.X9.toBitVec) * M + (M - 1)
  | "lane", s => (rv s.regs.X2.toBitVec - rv s.regs.X9.toBitVec) * M
      + rv s.regs.X10.toBitVec * K + (K - 1)
  | "free", s => (rv s.regs.X2.toBitVec - rv s.regs.X9.toBitVec) * M
      + rv s.regs.X10.toBitVec * K + (rv s.regs.X6.toBitVec + 2 - rv s.regs.X15.toBitVec)
  | "place", s => (rv s.regs.X2.toBitVec - rv s.regs.X9.toBitVec) * M
      + rv s.regs.X10.toBitVec * K
  | "gnext", s => (rv s.regs.X2.toBitVec - rv s.regs.X9.toBitVec) * M
  | _, _ => 0

/-! ### Facts the blocks use -/

theorem ctrl_at {T : Tbl} {m : DataMem} (hm : T.InMem m) {g : BitVec 64} (h : rv g ≤ T.mv) :
    Mem.loadInt m (T.cb + g <<< 3) 8 = some (T.ctrl (rv g)) := by
  rw [rv_def] at h ⊢; exact hm.1 g h

theorem and_rv (c : Nat) (_h : c < W64) :
    rv (BitVec.ofNat 64 c &&& 0x8080808080808080#64) = bitN .and c H8 := by
  rw [rv_def, ← bitN_and]; simp only [bitN, BitVec.toNat_ofNat, W64, Nat.mod_mod]; rfl

theorem osl_bv (x9 x10 x3 : BitVec 64) {cv : Nat} (h3 : rv x3 = cv) :
    bandN (bitN .or (bitN .shl (rv x9) 3) (bitN .shr (bit1N .ctz (rv x10)) 3)) cv
      = rv ((x9 <<< 3 ||| x10.reverse.clz >>> 3) &&& x3) := by
  rw [shl3_rv, ctz_rv, shr3_rv, or_rv, bandN_rv h3]

theorem hashN_of (k : Nat) (h : k < W64) :
    hashN k = (rv (hmB (BitVec.ofNat 64 k) &&& 0x7F#64 ||| 0x80#64), rv (hmB (BitVec.ofNat 64 k) >>> 7)) := by
  rw [← hashN_rv, rv_ofNat _ h]

theorem contG_none (d i : Nat) : contG d i none = none := by cases d <;> rfl

theorem free_some {d i base gl n fm : Nat} {O N : Tbl} {r : Option (Nat × Nat)} {R : Option St}
    (hk : contG d i (laneK base O N gl n fm r) = R) (hR : R ≠ none) : r.isSome := by
  cases r
  · rw [laneK, contG_none] at hk; exact absurd hk.symm hR
  · rfl

/-- `freeSlot`'s probe has fuel left at every group it reaches. -/
theorem free_lt' {T : Tbl} {p pos st st' : Nat} (hR : (freeN T (T.mv + 1) p 0).isSome)
    (hst : st ≤ T.mv) (hf : freeN T (T.mv - st) pos st' = freeN T (T.mv + 1) p 0) : st < T.mv := by
  rcases Nat.lt_or_ge st T.mv with h | h
  · exact h
  · rw [show T.mv - st = 0 by omega] at hf
    rw [← hf] at hR; exact absurd hR (by simp [freeN])

theorem fr_nat (c : Nat) (h : c < W64) :
    bitN .and (bit1N .not c) H8 = rv (~~~BitVec.ofNat 64 c &&& 0x8080808080808080#64) := by
  rw [← fr_rv, rv_ofNat _ h]

theorem var_lane (a : Nat) (v : BitVec 64) : a * M + rv v * K + (K - 1) ≤ a * M + (M - 1) := by
  have := Nat.mul_le_mul_right K (rv_lt v)
  rw [Nat.succ_mul] at this
  have : 0 < K := by decide
  simp only [M]; omega

/-- The sizes `GrowHyps` bounds. -/
theorem grow_bounds {x : GrowX} (hh : GrowHyps x) :
    16 * x.O.mv + 16 < W64 ∧ x.O.cv < W64 ∧ 16 * (8 * (2 * x.O.mv + 2) - 1 + 1) ≤ W64 := by
  have := hh.sepN.lo; have := hh.sepN.hi; have := hh.sepO.hi; have := (x.sb - x.cb).isLt
  simp only [GrowX.N, newT, W64] at *; omega

/-- `(m₂ << 3) | 7` is the new slot mask `c₂` (`BitVec.shiftLeft_or_eq_add`
for the or). -/
theorem cm_rv (x : BitVec 64) {m : Nat} (h : rv x = 2 * m + 1) (hb : 16 * m + 16 < W64) :
    rv (x <<< 3 ||| 7#64) = 8 * (2 * m + 2) - 1 := by
  rw [rv_def] at h ⊢
  rw [BitVec.shiftLeft_or_eq_add x 3 7#64 (by decide), BitVec.toNat_add, BitVec.toNat_shiftLeft, h]
  simp only [W64] at hb
  simp only [Nat.shiftLeft_eq, BitVec.toNat_ofNat]; omega

/-- `place` keeps the table's words 64-bit. -/
theorem wf_place {N : Tbl} (hw : Wf N) (sr hh : Nat) {kk vv : Nat} (hk : kk < W64) (hv : vv < W64) :
    Wf (placeT N sr hh kk vv) := by
  refine ⟨fun g => ?_, fun s => ?_, fun s => ?_⟩ <;> simp only [placeT, setCtrlN, upd]
  · split
    · simp only [setLaneN8, laneN8, W64]
      exact (lane_arith _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide))).2
    · exact hw.ctrl _
  all_goals split
  all_goals first | assumption | exact hw.key _ | exact hw.val _

/-- **`place` and the old slot zeroed**: the five stores of the `place` block
leave the new table with the moved pair placed, the old table with its slot
zeroed, and every byte outside both tables; the two old loads between them
read the old pair. -/
theorem place_all {O N : Tbl} {m : DataMem} (hmo : O.InMem m) (hmn : N.InMem m) (hsO : O.Sep)
    (hsN : N.Sep) (hd : ∀ a, O.Owns a → ¬ N.Owns a) (hwo : Wf O) (hwn : Wf N)
    (sr mb cm os oc h2 : BitVec 64) (hmb : rv mb = N.mv) (hcm : rv cm = N.cv) (hoc : rv oc = O.cv) :
    let g := sr >>> 3 &&& mb
    let w := BitVec.ofNat 64 (N.ctrl (rv g))
    let sh := ((sr &&& 7#64) <<< 3).toNat % 64
    let W := w - (w >>> sh &&& 0xff#64) <<< sh + (h2 &&& 0xff#64) <<< sh
    let s := sr &&& cm
    let o := os &&& oc
    let k := BitVec.ofNat 64 (O.key (rv o))
    let v := BitVec.ofNat 64 (O.val (rv o))
    let m1 := m.storeInt (N.cb + g <<< 3) 8 W.toInt
    let m2 := m1.storeInt (N.sb + s <<< 4) 8 k.toInt
    let m3 := m2.storeInt (N.sb + s <<< 4 + 8#64) 8 v.toInt
    let m5 := (m3.storeInt (O.sb + o <<< 4) 8 (0#64).toInt).storeInt (O.sb + o <<< 4 + 8#64) 8 (0#64).toInt
    m1.loadInt (O.sb + o <<< 4) 8 = some ((O.key (rv o) : Nat) : Int)
      ∧ m2.loadInt (O.sb + o <<< 4 + 8#64) 8 = some ((O.val (rv o) : Nat) : Int)
      ∧ (placeT N (rv sr) (rv h2) (O.key (rv o)) (O.val (rv o))).InMem m5
      ∧ (zeroSlot O (rv o)).InMem m5 ∧ ∀ a, ¬ O.Owns a → ¬ N.Owns a → m5.get? a = m.get? a := by
  intro g w sh W s o k v m1 m2 m3 m5
  have hg : g.toNat ≤ N.mv := by rw [← hmb, rv_def, BitVec.toNat_and]; exact Nat.and_le_right
  have hsl : s.toNat ≤ N.cv := by rw [← hcm, rv_def, BitVec.toNat_and]; exact Nat.and_le_right
  have ho : o.toNat ≤ O.cv := by rw [← hoc, rv_def, BitVec.toNat_and]; exact Nat.and_le_right
  obtain ⟨Pin, Pfr⟩ := place_mem hmn hsN hwn.ctrl sr mb cm h2 k v (rv h2) (O.key (rv o)) (O.val (rv o))
    sh hmb hcm (rv_ofNat _ (hwo.key _)) (rv_ofNat _ (hwo.val _)) rfl rfl
  have e1 : O.InMem m1 := inMem_frame hmo hsO fun a ha => frame_ctrl g hsN hg _ a (hd a ha)
  have e2 : O.InMem m2 := inMem_frame e1 hsO fun a ha => frame_key s hsN hsl _ a (hd a ha)
  have e3 : O.InMem m3 := inMem_frame hmo hsO fun a ha => Pfr a (hd a ha)
  have e4 := inMem_key e3 hsO o 0#64 ho
  have e5 := inMem_val e4 ⟨hsO.lo, hsO.hi⟩ o 0#64 ho
  have f4 : ∀ a, ¬ O.Owns a → (m3.storeInt (O.sb + o <<< 4) 8 (0#64).toInt).get? a = m3.get? a :=
    fun a ha => frame_key o hsO ho _ a ha
  have f5 : ∀ a, ¬ O.Owns a → m5.get? a
      = (m3.storeInt (O.sb + o <<< 4) 8 (0#64).toInt).get? a :=
    fun a ha => frame_val (T := O) o hsO ho _ a ha
  refine ⟨(e1.2 o ho).1.trans (by rw [rv_def]; rfl), (e2.2 o ho).2.trans (by rw [rv_def]; rfl), ?_, ?_, ?_⟩
  · refine inMem_frame Pin ⟨hsN.lo, hsN.hi⟩ fun a ha => ?_
    have hn : ¬ O.Owns a := fun h => hd a h ha
    rw [f5 a hn, f4 a hn]
  · simp only [zeroSlot, rv_def]; exact e5
  · intro a ha hn
    rw [f5 a ha, f4 a ha, Pfr a hn]

/-- `cmp`'s zero flag, as values (`BitVec.toNat_eq_of_sub_eq_zero`,
`toNat_ne_of_sub_ne_zero`; kept as aliases). -/
theorem sub_zero_rv {a b : BitVec 64} (h : a - b = 0#64) : rv a = rv b := by
  rw [rv_def, rv_def]; exact BitVec.toNat_eq_of_sub_eq_zero h

theorem sub_ne_rv {a b : BitVec 64} (h : ¬ a - b = 0#64) : rv a ≠ rv b := by
  rw [rv_def, rv_def]; exact BitVec.toNat_ne_of_sub_ne_zero h

section Spec
variable [CodeEnv]


set_option hygiene false in
/-- Open block `l`'s invariant: the tables `ok ov nc nk nv`, `gl`, `n`, the
arguments `h0`–`h5`, `hlr`, `hh`, `hcs`, `h6`–`h9`, the memory facts `hmo`,
`hmn`, `hwo`, `hwn`, `hfr`, and the block's own facts `hf`. -/
local macro "open_inv" l:str : tactic => `(tactic| (
  have h := ‹growTable _ _ _ $l _ ∧ _›
  simp only [growTable, growVar, FreeI] at h
  obtain ⟨⟨ok, ov, nc, nk, nv, gl, n, hc, hf⟩, rfl⟩ := h
  simp only [GCom, GArgs, Mid, Callee] at hc
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, hlr⟩, hh, hcs, h6, h7, h8, h9, hmo, hmn, hwo, hwn, hfr⟩ := hc
  have hb := grow_bounds hh
  dsimp only at hb
  simp only [GrowX.N, newT] at hf h6 hmn hwn hfr))

set_option linter.unusedSimpArgs false in
/-- **`grow`, lowered, implements WeakCore's growth** (total correctness, sequential):
from `GrowPre`, `flat_grow` returns with `growN`'s answer in `insert`'s argument
registers, the new table and the old one (slots zeroed) in memory, and every
other byte, `sp` and `x19`–`x28` as they were. -/
theorem grow_spec (hpl : Program.PlacedIn flatGrow) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label "flat_grow") GrowPre GrowPost := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := flatGrow) growTable growVar
    (hblocks := ?_) (hpre := fun x ra t h => ⟨rfl, h⟩)
  rintro ⟨O, cb, sb⟩ ra t₀
  cfg_cases [flatGrow]
  · -- the sizes
    vcgen
    have h := ‹growTable _ ra _ "flat_grow" _ ∧ _›
    simp only [growTable, growVar, GrowPre, GArgs] at h
    obtain ⟨⟨rfl, ⟨h0, h1, h2, h3, h4, h5, hlr⟩, hmo, hmn, hh⟩, rfl⟩ := h
    have hmv := hh.sepN.lo
    simp only [growTable, growVar, GCom, GArgs, Mid, Callee]
    refine ⟨⟨O.key, O.val, fun _ => 0, fun _ => 0, fun _ => 0, glN O, 0, ?_, ?_⟩, ?_⟩
    · simp only [GrowX.N, newT] at hmv hmn ⊢
      have hb := (sb - cb).isLt
      rw [rv_def] at h2
      simp [h0, h1, h3, h4, h5, hlr, hmo, hh]
      refine ⟨?_, ?_, ?_, hmn, hh.wf, ⟨fun _ => W64_pos, fun _ => W64_pos, fun _ => W64_pos⟩⟩
      all_goals first
        | (rw [rv_def]; exact h2) | exact hmn | exact hh.wf | exact ⟨fun _ => W64_pos, fun _ => W64_pos, fun _ => W64_pos⟩
        | (simp only [rv_def, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h2,
              BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega)
        | (exact gl_bv O _ h2 (by simp only [W64] at hb ⊢; omega))
    · simp; exact rfl
    · simp [h2]
      rw [Nat.add_mul]; have : 0 < M := by decide
      omega
  · -- grp: old group `i`'s full lanes
    vcgen
    all_goals open_inv "grp"
    all_goals try have hv := ‹Mem.loadInt _ _ _ = some _›
    all_goals have hl := ctrl_at hmo h9
    all_goals dsimp only at hl
    all_goals try (simp [h0, hl]; done)
    simp [h0, hl] at hv
    subst hv
    rw [mvGN_eq] at hf
    refine ⟨⟨ok, ov, nc, nk, nv, gl, n, ?_, ?_⟩, ?_⟩
    all_goals simp [GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, hlr, hh, hcs, hmo, hmn, hwo, hwn, hfr]
    · exact hfr
    · rw [and_rv _ (hwo.ctrl _)]; exact hf
    · simp [growVar, h2]; exact var_lane _ _
  · -- lane: the lowest full lane's old slot, and its key's hash
    vcgen
    all_goals open_inv "lane"
    case vc1 => -- no full lane left: `mvG`'s next group
      rename_i hz _
      simp at hz
      have h10 := congrArg rv hz
      simp only [rv_zero] at h10
      rw [h10, mvLN_zero] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ⟨ok, ov, nc, nk, nv, gl, n, ?_, hf⟩, ?_⟩)
      · simp [GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7, h8,
          h9, hlr, hh, hcs, hmo, hmn, hwo, hwn]
        exact hfr
      · left; simp only [growVar, h10]; have : 1 < K := by decide
        omega
    all_goals
      have hz := ‹¬ _ = (0 : BitVec 64)›
      simp at hz
      try have hv := ‹Mem.loadInt _ _ _ = some _›
      have hkl := fun a => key_load hmo h3 a
      dsimp only at hkl
    all_goals try (simp [h1, hkl]; done)
    simp [h1, hkl] at hv
    subst hv
    rw [mvLN_ne _ _ (rv_ne _ hz)] at hf
    refine ⟨⟨ok, ov, nc, nk, nv, gl, n, ?_⟩, ?_⟩
    all_goals simp [FreeI, GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, hlr, hh, hcs, hmo, hmn, hwo, hwn, hfr, osl, oslot, osl_bv _ _ _ h3, hashN_of, hwo.key, hmB]
    · refine ⟨hfr, rv_ne _ hz, ?_⟩
      simpa [oslot, osl_bv _ _ _ h3, hashN_of, hwo.key, hmB] using hf
    · simp [growVar, h2, h6]
      have := hb.1; simp only [K] at *; omega
  · -- free: one group of `freeSlot` in the new table
    vcgen
    all_goals
      open_inv "free"
      simp only [osl] at hf
      obtain ⟨hz, h11, h13, h15, hfe, hk⟩ := hf
      have hR := free_some hk (by rw [← Option.isSome_iff_ne_none] at *; exact hh.ends)
      have hfe' := hfe
      rw [freeN_step _ _ _ h15, bandN_rv h6] at hfe
      dsimp only at hfe
      try have hv := ‹Mem.loadInt _ _ _ = some _›
      have hcl := fun a => ctrl_load hmn h6 a
      dsimp only at hcl
    all_goals try (simp [h4, hcl]; done)
    all_goals simp [h4, hcl] at hv; subst hv
    case vc3 => -- a free lane: `place`
      have hx := ‹¬ _ = (0 : BitVec 64)›
      simp at hx
      refine Or.inl (Table.ofLabels_at ⟨by decide, ⟨ok, ov, nc, nk, nv, gl, n, ?_⟩, ?_⟩)
      all_goals simp [FreeI, GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7,
        h8, h9, hlr, hh, hcs, hmo, hmn, hwo, hwn, hfr, hz, h11, h13, h15, hfe', hk, hx, growVar,
        rv_ofNat _ (hwn.ctrl _), osl]
      · exact hfr
      · left; omega
    case vc4 => -- no free lane: the next group
      have hx := ‹_ = (0 : BitVec 64)›
      simp at hx
      have hnc : ∀ g, nc g < W64 := hwn.ctrl
      simp (disch := exact hnc _) only [fr_nat, hx, rv_zero, ↓reduceIte] at hfe
      have hlt := free_lt' hR h15 hfe
      have h10 := rv_add1 _ (Nat.lt_of_le_of_lt (Nat.succ_le_succ h15) (by have := hb.1; omega))
      simp only [wadd1] at hfe
      simp only [wadd_rv] at hfe
      simp only [h10] at hfe
      refine Or.inl (Table.ofLabels_at ⟨by decide, ⟨ok, ov, nc, nk, nv, gl, n, ?_⟩, ?_⟩)
      all_goals simp [FreeI, GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7,
        h8, h9, hlr, hh, hcs, hmo, hmn, hwo, hwn, hfr, hz, h11, h13, h15, hfe, hk, growVar, osl, h10]
      · dsimp only at hlt; exact ⟨hfr, by omega⟩
      · omega
  · -- place
    vcgen
    all_goals
      have h := ‹growTable _ _ _ "place" _ ∧ _›
      simp only [growTable, growVar, FreeI, osl] at h
      obtain ⟨⟨ok, ov, nc, nk, nv, gl, n, ⟨hc, hz, h11, h13, h15, hfe, hk⟩, h16, h17, hx⟩, rfl⟩ := h
      simp only [GCom, GArgs, Mid, Callee] at hc
      obtain ⟨⟨h0, h1, h2, h3, h4, h5, hlr⟩, hh, hcs, h6, h7, h8, h9, hmo, hmn, hwo, hwn, hfr⟩ := hc
      have hb := grow_bounds hh
      dsimp only at hb
      simp only [GrowX.N, newT] at h6 hmn hwn hfr hfe hk h15
      have hcl := fun a => ctrl_load hmn h6 a
      have hcm := cm_rv _ h6 hb.1
      have hnk := fun a => key_load hmn hcm a
      have hnv := fun a => val_load' hmn hcm a
      have hok := fun a => key_load hmo h3 a
      have hov := fun a => val_load' hmo h3 a
      dsimp only at hcl hnk hnv hok hov
      simp only [oslot, osl_bv _ _ _ h3, ofNat_rv] at h11 h13 hk hfe
    case vc17 =>
      rename_i s _ _ _ _ c hc _ _ _ _ _ k hk' _ _ v hv' _ _ _ _
      simp [h4, hcl] at hc
      subst hc
      simp [h0, h1, h4, h5, h11, shr_mod, -BitVec.toInt_sub, -BitVec.toInt_add] at hk' hv'
      have L := place_all hmo hmn ⟨hh.sepO.lo, hh.sepO.hi⟩ ⟨hh.sepN.lo, hh.sepN.hi⟩ hh.disj hwo hwn
        ((s.regs.X14.toBitVec &&& s.regs.X6.toBitVec) <<< 3 ||| s.regs.X17.toBitVec.reverse.clz >>> 3)
        s.regs.X6.toBitVec (s.regs.X6.toBitVec <<< 3 ||| 7#64)
        (s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) s.regs.X3.toBitVec
        s.regs.X13.toBitVec
      specialize L h6 hcm h3
      dsimp only at L
      obtain ⟨L1, L2, P1, P2, P3⟩ := L
      simp [h0, h1, h4, h5, h11, shr_mod, -BitVec.toInt_sub, -BitVec.toInt_add] at L1 L2
      rw [L1] at hk'
      simp only [Option.some.injEq] at hk'
      subst hk'
      simp only [BitVec.toInt_ofNat', Nat.reducePow, Int.reducePow] at L2
      rw [L2] at hv'
      simp only [Option.some.injEq] at hv'
      subst hv'
      have e16 : nc (rv (s.regs.X14.toBitVec &&& s.regs.X6.toBitVec)) = rv s.regs.X16.toBitVec := by
        rw [h16, rv_ofNat _ (hwn.ctrl _)]
      have hst := freeN_step ⟨2 * O.mv + 1, 8 * (2 * O.mv + 2) - 1, nc, nk, nv, cb, sb⟩ (rv s.regs.X14.toBitVec) _ h15
      dsimp only at hst
      rw [hst, bandN_rv h6] at hfe
      simp only [e16, fr_rv, ← h17] at hfe
      simp only [rv_ne _ hx, ↓reduceIte, shl3_rv, ctz_rv, shr3_rv, emptyN_rv', shr_rv, and1_rv,
        or_rv] at hfe
      rw [← hfe] at hk
      simp only [laneK, oslot, osl_bv _ _ _ h3, ← h13] at hk
      refine Or.inl (Table.ofLabels_at ⟨by decide, ⟨upd ok (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec)) 0, upd ov (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec)) 0,
        (placeT ({ mv := 2 * O.mv + 1, cv := 8 * (2 * O.mv + 2) - 1, ctrl := nc, key := nk, val := nv, cb := cb, sb := sb } : Tbl) (rv ((s.regs.X14.toBitVec &&& s.regs.X6.toBitVec) <<< 3 ||| s.regs.X17.toBitVec.reverse.clz >>> 3)) (rv s.regs.X13.toBitVec) (ok (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec))) (ov (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec)))).ctrl,
        (placeT ({ mv := 2 * O.mv + 1, cv := 8 * (2 * O.mv + 2) - 1, ctrl := nc, key := nk, val := nv, cb := cb, sb := sb } : Tbl) (rv ((s.regs.X14.toBitVec &&& s.regs.X6.toBitVec) <<< 3 ||| s.regs.X17.toBitVec.reverse.clz >>> 3)) (rv s.regs.X13.toBitVec) (ok (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec))) (ov (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec)))).key,
        (placeT ({ mv := 2 * O.mv + 1, cv := 8 * (2 * O.mv + 2) - 1, ctrl := nc, key := nk, val := nv, cb := cb, sb := sb } : Tbl) (rv ((s.regs.X14.toBitVec &&& s.regs.X6.toBitVec) <<< 3 ||| s.regs.X17.toBitVec.reverse.clz >>> 3)) (rv s.regs.X13.toBitVec) (ok (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec))) (ov (rv ((s.regs.X9.toBitVec <<< 3 ||| s.regs.X10.toBitVec.reverse.clz >>> 3) &&& s.regs.X3.toBitVec)))).val,
        bitN .wsub gl (rv (zbBV s.regs.X16.toBitVec >>> (s.regs.X17.toBitVec.reverse.clz.toNat % 64) &&& 1#64)),
        bitN .wadd n 1, ?_, ?_⟩, ?_⟩)
      all_goals simp [GCom, GArgs, Mid, Callee, GrowX.N, newT, growVar, h0, h1, h2, h3, h4, h5, h6, h7,
        h8, h9, hlr, hh, hcs, -BitVec.toInt_sub, -BitVec.toInt_add]
      · refine ⟨by rw [← h7, rv_def, rv_def, rv_def, bitN_wsub]; rfl, by rw [← h8, wadd1], ?_⟩
        simp [h0, h1, h4, h5, h11, shr_mod, -BitVec.toInt_sub, -BitVec.toInt_add] at P1 P2 P3 ⊢
        refine ⟨P2, P1, ⟨hwo.ctrl, fun _ => ?_, fun _ => ?_⟩, ?_, ?_⟩
        · dsimp only [upd]; split
          · exact W64_pos
          · exact hwo.key _
        · dsimp only [upd]; split
          · exact W64_pos
          · exact hwo.val _
        · exact wf_place hwn _ _ (hwo.key _) (hwo.val _)
        · exact fun a ha hn => (P3 a ha hn).trans (hfr a ha hn)
      · rw [clear_rv] at hk; exact hk
      · left
        have hz' : s.regs.X10.toBitVec ≠ 0#64 := fun h => hz (by rw [h, rv_zero])
        have h1 := Nat.mul_le_mul_right K (clear_lt _ hz')
        have : 0 < K := by decide
        rw [Nat.succ_mul] at h1; omega
    all_goals try (simp [h0, h1, h4, h5, hcl]; done)
    all_goals try (simp [h0, h1, h4, h5, h11]; repeat apply loadInt_store_isSome
                   first | simp [hcl] | simp [hnk] | simp [hnv] | simp [hok] | simp [hov]
                   done)
  · -- gnext: `mvG`'s `ifeq dv 0`
    vcgen
    all_goals
      open_inv "gnext"
      rename_i hc _
      simp at hc
    case vc1 => -- the last group: `done`
      have hi := sub_zero_rv hc
      rw [hi, h2, Nat.sub_self] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ⟨ok, ov, nc, nk, nv, gl, n, ?_, hf⟩, ?_⟩)
      · simp [GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7, h8,
          h9, hlr, hh, hcs, hmo, hmn, hwo, hwn]
        exact hfr
      · right; simp [growVar, hi]; decide
    case vc2 => -- the next group
      rename_i s _
      have hlt : rv s.regs.X9.toBitVec < O.mv := by
        have := sub_ne_rv hc; omega
      have h10 := rv_add1 _ (by have := hb.1; omega : rv s.regs.X9.toBitVec + 1 < W64)
      rw [show O.mv - rv s.regs.X9.toBitVec = (O.mv - (rv s.regs.X9.toBitVec + 1)) + 1 by omega] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ⟨ok, ov, nc, nk, nv, gl, n, ?_, ?_⟩, ?_⟩)
      · simp [GCom, GArgs, Mid, Callee, GrowX.N, newT, h0, h1, h2, h3, h4, h5, h6, h7, h8,
          h10, hlr, hh, hcs, hmo, hmn, hwo, hwn]
        exact ⟨by omega, hfr⟩
      · simp [h10]; exact hf
      · left; simp [growVar, h2, h10]
        have : 0 < M := by decide
        rw [show O.mv - rv s.regs.X9.toBitVec = (O.mv - (rv s.regs.X9.toBitVec + 1)) + 1 by omega,
          Nat.succ_mul]; omega
  · -- done: `insert`'s argument registers
    vcgen
    open_inv "done"
    refine Or.inr ⟨by simp [hlr], _, _, _, _, hf.symm, ?_⟩
    simp [GrowX.N, newT, Callee, hcs, h4, h5, h6, h7, h8, hmo, hmn, cm_rv _ h6 hb.1]
    exact hfr

end Spec

/-- **`grow_spec`'s start-state hypotheses hold at `full1`** (new buffers at
`0x3000`, `0x4000`): R-INT, both tables' buffers apart, the tables disjoint,
and growth's termination. -/
theorem full1_hyps : GrowHyps ⟨full1, 0x3000#64, 0x4000#64⟩ := by
  refine ⟨⟨fun _ => by simp only [full1]; decide, fun s => ?_, fun s => ?_⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, fun a ha hn => ?_, by decide +kernel⟩
  · simp only [full1]; split <;> simp only [W64] <;> omega
  · simp only [full1]; split <;> simp only [W64] <;> omega
  · simp only [Tbl.Owns, full1, GrowX.N, newT] at ha hn
    bv_omega

end Kraken.Promising.Lower.Flat.Grow
