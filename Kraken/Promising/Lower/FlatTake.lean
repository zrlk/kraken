/-
**WeakCore's FlatHashMap `take` (portable,
`x = false`) for `Int` keys and values, lowered to AArch64.** ISA: AArch64;
machine: the **sequential** machine-founded wp
(`MachineWP`), total correctness, through `ProcSpec.of_cfg`. It reuses
the FlatHashMap `lookup` lowering's word model (`FlatGroupMatch.lean`) and its `lookup` model, probe
loop and invariant (`FlatLookup.lean`); every helper here is in the namespace
`Kraken.Promising.Lower.Flat.Take`.

* §1 is the model `takeN`: WeakCore's `takeD false` / `eraseCtrlD false` /
  `setCtrlD false` / `ctrlStore` at `K = V = Int`, `hash = hashInt`,
  `eq = eqInt`, over the FlatHashMap `lookup` lowering's `findN` (`Rf`).
* §2 is the memory: the separation hypothesis `Sep`, the frame, and the
  facts that the two word stores keep the table in memory.
* §3 is the code and `take_spec`; §4 the non-vacuity witnesses.
-/
import Kraken.Promising.Lower.FlatLookup

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat.Take

open Kraken.Promising.Lower.Flat

/-! ## 1. The model: WeakCore's `take` at `Int` keys and values

Control bytes (WeakCore's encoding): `0x00` empty, `0x01` deleted,
`0x80 ||| h2` full. Lane `b` of a control word is its byte `b` (bits
`8b … 8b+7`), the convention `lane` (`ctz / 8`) and `byteAt` use. -/

/-- `ctrlStore`'s `stlw cb g b v8`, on the control word `w` it writes: byte
`x` (`cvt w8`) into lane `b`. Written as the word read-modify-write the
lowering performs (WC rule 6, no sub-word store): clear the lane with the
mask `0xFF << 8b`, or in `x << 8b`. -/
def stlwN (w b x : Nat) : Nat :=
  bitN .or (bitN .and w (bit1N .not (bitN .shl 0xFF (bitN .shl b 3))))
    (bitN .shl (x % 256) (bitN .shl b 3))

-- Lane 2 of `0x…0085_0000` set to `0x00` (empty) and `0x01` (deleted); lane 0 of `0xFFFF` to `1`.
#guard stlwN 0x0000000000850000 2 0 == 0
#guard stlwN 0x1100000000850000 2 1 == 0x1100000000010000
#guard stlwN 0xFFFF 0 1 == 0xFF01
#guard stlwN 0xFFFF 7 0x185 == 0x850000000000FFFF

/-- The control word `g` replaced by `x`. -/
def setCtrl (T : Tbl) (g x : Nat) : Tbl :=
  { T with ctrl := fun j => if j = g then x else T.ctrl j }

/-- Slot `s`'s value replaced by `x` (`xchgAtF sb s [1] x`, the key stays). -/
def setVal (T : Tbl) (s x : Nat) : Tbl :=
  { T with val := fun j => if j = s then x else T.val j }

/-- WeakCore's `eraseCtrl` [m] (with `setCtrl` [m] and `ctrlStore` inlined):
group `g = band (sr >> 3) mv`, lane `b = sr & 7`; if the group has no empty
lane (`Gem = 0`) the byte becomes deleted (`1`) and the flag is `0`, else
empty (`0`) and the flag is `1`. Returns the table and the flag. -/
def eraseCtrlN (T : Tbl) (sr : Nat) : Tbl × Nat :=
  let g := bandN (bitN .shr sr 3) T.mv
  let w := T.ctrl g
  let val := if emptyN w = 0 then 1 else 0
  let fl := if emptyN w = 0 then 0 else 1
  (setCtrl T g (stlwN w (bitN .and sr 7) val), fl)

/-- `take`'s hit branch at raw slot `sr`: `s = band sr cv`, the value is
exchanged with `zero V = 0`, `eraseCtrl`, `gl1 = wadd gl fl`,
`n1 = wsub n 1`, result `inr old`. -/
def takeHitN (T : Tbl) (gl n sr : Nat) : Tbl × Nat × Nat × Option Nat :=
  let s := bandN sr T.cv
  let e := eraseCtrlN (setVal T s 0) sr
  (e.1, bitN .wadd gl e.2, bitN .wsub n 1, some (T.val s))

/-- WeakCore's `take` at `Int` keys and values: the table, `growth_left`,
`size`, and the result (`some y` is `inr y`, `none` is `inl ()`); `none`
overall is a probe that does not end within `m + 1` groups. -/
def takeN (T : Tbl) (gl n k : Nat) : Option (Tbl × Nat × Nat × Option Nat) :=
  (Rf T k).map fun r => match r with
    | none => (T, gl, n, none)
    | some sr => takeHitN T gl n sr

-- `eraseCtrl` on a full group (no empty lane): lane 2 becomes deleted (`0x01`), flag `0`;
-- on `tbl1`'s group (empty lanes left): lane 2 becomes empty, flag `1`.
#guard (eraseCtrlN { tbl1 with ctrl := fun _ => 0x8181818181818181 } 2).2 == 0
  && (eraseCtrlN { tbl1 with ctrl := fun _ => 0x8181818181818181 } 2).1.ctrl 0 == 0x8181818181018181
#guard (eraseCtrlN tbl1 2).2 == 1 && (eraseCtrlN tbl1 2).1.ctrl 0 == 0

theorem takeN_isSome (T : Tbl) (gl n k : Nat) : (takeN T gl n k).isSome = (lookupN T k).isSome := by
  simp only [takeN, lookupN_eq, Option.isSome_map]

/-! ## 2. Memory: separation, frame, and the two stores -/

/-- The control buffer's bytes `[cb, cb + 8(m+1))`. -/
def InCtrl (T : Tbl) (a : BitVec 64) : Prop :=
  T.cb.toNat ≤ a.toNat ∧ a.toNat < T.cb.toNat + 8 * (T.mv + 1)

/-- The slot buffer's bytes `[sb, sb + 16(c+1))`. -/
def InSlots (T : Tbl) (a : BitVec 64) : Prop :=
  T.sb.toNat ≤ a.toNat ∧ a.toNat < T.sb.toNat + 16 * (T.cv + 1)

/-- **The separation hypothesis** (a start-state property of the table): the
two buffers do not wrap around the address space and do not overlap. -/
structure Sep (T : Tbl) : Prop where
  cb : T.cb.toNat + 8 * (T.mv + 1) ≤ W64
  sb : T.sb.toNat + 16 * (T.cv + 1) ≤ W64
  disj : T.cb.toNat + 8 * (T.mv + 1) ≤ T.sb.toNat ∨ T.sb.toNat + 16 * (T.cv + 1) ≤ T.cb.toNat

/-- **The frame**: every byte outside the two buffers is as it was. -/
def Frame (T : Tbl) (m m' : DataMem) : Prop :=
  ∀ a, ¬ InCtrl T a → ¬ InSlots T a → m'.get? a = m.get? a

theorem get?_storeInt8 (m : DataMem) (a k : BitVec 64) (v : Int) (ha : a.toNat + 8 ≤ W64)
    (hk : ¬ (a.toNat ≤ k.toNat ∧ k.toNat < a.toNat + 8)) : (m.storeInt a 8 v).get? k = m.get? k := by
  apply Mem.get?_storeBytes_of_not_mem
  rw [mem_At_iff, Int.toBytes_length]
  rintro ⟨i, hi, rfl⟩
  apply hk
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by unfold W64 at ha; omega),
      Nat.mod_eq_of_lt (by unfold W64 at ha; omega)]
  omega

theorem loadInt_storeInt8_disj (m : DataMem) (a b : BitVec 64) (v : Int) (ha : a.toNat + 8 ≤ W64)
    (hb : b.toNat + 8 ≤ W64) (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) :
    (m.storeInt a 8 v).loadInt b 8 = m.loadInt b 8 := by
  unfold W64 at ha hb
  have hs : (b - a).toNat = (b.toNat + (2 ^ 64 - a.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; congr 1; omega
  apply Mem.loadInt_storeInt_of_above <;> rw [hs]
  · rcases h with h | h
    · rw [show b.toNat + (2 ^ 64 - a.toNat) = (b.toNat - a.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rcases h with h | h
    · rw [show b.toNat + (2 ^ 64 - a.toNat) = (b.toNat - a.toNat) + 2 ^ 64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem loadInt_storeInt8_same (m : DataMem) (a x : BitVec 64) :
    (m.storeInt a 8 x.toInt).loadInt a 8 = some (x.toNat : Int) := by
  rw [Mem.loadInt_storeInt _ _ _ _ (by decide), ofBytes_toBytes]
  congr 1
  simp only [Int.take, BitVec.toInt_eq_toNat_bmod]
  rw [show 8 * 8 = 64 from rfl, show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from rfl, Int.bmod_emod]
  exact Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)

/-- A control word's address, as a number. -/
theorem ctrl_addr {T : Tbl} (hs : Sep T) (g : BitVec 64) (hg : g.toNat ≤ T.mv) :
    (T.cb + g <<< 3).toNat = T.cb.toNat + 8 * g.toNat := by
  have := hs.cb
  unfold W64 at this
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := g.toNat * 2 ^ 3)
    (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- A slot word's address (`o = 0` the key, `o = 8` the value), as a number. -/
theorem slot_addr {T : Tbl} (hs : Sep T) (s : BitVec 64) (hs' : s.toNat ≤ T.cv) :
    (T.sb + s <<< 4).toNat = T.sb.toNat + 16 * s.toNat
      ∧ (T.sb + s <<< 4 + 8#64).toNat = T.sb.toNat + 16 * s.toNat + 8 := by
  have := hs.sb
  unfold W64 at this
  have h1 : (T.sb + s <<< 4).toNat = T.sb.toNat + 16 * s.toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (a := s.toNat * 2 ^ 4) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨h1, ?_⟩
  rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- `slot_addr` at a number. -/
theorem slot_addr' {T : Tbl} (hs : Sep T) (s : BitVec 64) (hs' : s.toNat ≤ T.cv) :
    (T.sb + s <<< 4 + 8#64).toNat + 8 ≤ W64 ∧ (T.sb + s <<< 4).toNat + 8 ≤ W64 := by
  have := hs.sb; rw [(slot_addr hs s hs').1, (slot_addr hs s hs').2]; omega

/-- Storing word `x` at slot `s`'s value keeps the table in memory, with
`val s = x`. -/
theorem inMem_setVal {T : Tbl} {m : DataMem} (hm : T.InMem m) (hs : Sep T) (s : BitVec 64)
    (hs' : s.toNat ≤ T.cv) (x : BitVec 64) :
    (setVal T s.toNat x.toNat).InMem (m.storeInt (T.sb + s <<< 4 + 8#64) 8 x.toInt) := by
  obtain ⟨hv1, hv2⟩ := slot_addr hs s hs'
  have hsb := hs.sb; have hcb := hs.cb; have hd := hs.disj
  simp only [setVal, Tbl.InMem]
  refine ⟨fun g hg => ?_, fun s' hs'' => ?_⟩
  · have := ctrl_addr hs g hg
    rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]
    exact hm.1 g hg
  · obtain ⟨hk1, hk2⟩ := slot_addr hs s' hs''
    refine ⟨?_, ?_⟩
    · rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]
      exact (hm.2 s' hs'').1
    · by_cases he : s'.toNat = s.toNat
      · rw [BitVec.eq_of_toNat_eq he, loadInt_storeInt8_same]; simp
      · rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]
        simpa [he] using (hm.2 s' hs'').2

/-- Storing word `x` at control word `g` keeps the table in memory, with
`ctrl g = x`. -/
theorem inMem_setCtrl {T : Tbl} {m : DataMem} (hm : T.InMem m) (hs : Sep T) (g : BitVec 64)
    (hg : g.toNat ≤ T.mv) (x : BitVec 64) :
    (setCtrl T g.toNat x.toNat).InMem (m.storeInt (T.cb + g <<< 3) 8 x.toInt) := by
  have hc := ctrl_addr hs g hg
  have hsb := hs.sb; have hcb := hs.cb; have hd := hs.disj
  simp only [setCtrl, Tbl.InMem]
  refine ⟨fun g' hg' => ?_, fun s' hs'' => ?_⟩
  · have := ctrl_addr hs g' hg'
    by_cases he : g'.toNat = g.toNat
    · rw [BitVec.eq_of_toNat_eq he, loadInt_storeInt8_same]; simp
    · rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]
      simpa [he] using hm.1 g' hg'
  · obtain ⟨hk1, hk2⟩ := slot_addr hs s' hs''
    exact ⟨by rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]; exact (hm.2 s' hs'').1,
      by rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]; exact (hm.2 s' hs'').2⟩

theorem Frame.refl (T : Tbl) (m : DataMem) : Frame T m m := fun _ _ _ => rfl

theorem Frame.trans {T : Tbl} {m₁ m₂ m₃ : DataMem} (h₁ : Frame T m₁ m₂) (h₂ : Frame T m₂ m₃) :
    Frame T m₁ m₃ := fun a hc hs => (h₂ a hc hs).trans (h₁ a hc hs)

/-- A word store inside one of the buffers is in the frame. -/
theorem Frame.store {T : Tbl} (m : DataMem) (a : BitVec 64) (v : Int) (ha : a.toNat + 8 ≤ W64)
    (hin : (T.cb.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ T.cb.toNat + 8 * (T.mv + 1))
      ∨ (T.sb.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ T.sb.toNat + 16 * (T.cv + 1))) :
    Frame T m (m.storeInt a 8 v) := fun k hc hs =>
  get?_storeInt8 m a k v ha (fun ⟨h1, h2⟩ => by
    simp only [InCtrl, InSlots] at hc hs; omega)

theorem frame_val {T : Tbl} (hs : Sep T) (m : DataMem) (s : BitVec 64) (hs' : s.toNat ≤ T.cv)
    (v : Int) : Frame T m (m.storeInt (T.sb + s <<< 4 + 8#64) 8 v) := by
  have := (slot_addr hs s hs').2; have := hs.sb
  exact Frame.store m _ v (by omega) (Or.inr (by omega))

theorem frame_ctrl {T : Tbl} (hs : Sep T) (m : DataMem) (g : BitVec 64) (hg : g.toNat ≤ T.mv)
    (v : Int) : Frame T m (m.storeInt (T.cb + g <<< 3) 8 v) := by
  have := ctrl_addr hs g hg; have := hs.cb
  exact Frame.store m _ v (by omega) (Or.inl (by omega))


/-! ### Bridges for the hit branch -/

theorem bitN_shl (a b : BitVec 64) : bitN .shl a.toNat b.toNat = (a <<< (b.toNat % 64)).toNat := by
  simp only [bitN, W64, BitVec.toNat_mod_cancel, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- `stlwN` is the word the code writes: `bic` the lane mask, `orr` the byte. -/
theorem stlwN_bv (w sr v : BitVec 64) (hv : v.toNat < 256) :
    stlwN w.toNat (bitN .and sr.toNat 7) v.toNat
      = ((w &&& ~~~(0xFF#64 <<< (((sr &&& 7#64) <<< 3).toNat % 64)))
          ||| v <<< (((sr &&& 7#64) <<< 3).toNat % 64)).toNat := by
  have e : bitN .shl (bitN .and sr.toNat 7) 3 = ((sr &&& 7#64) <<< 3).toNat := by
    rw [bitN_lit .and _ 7, bitN_and, bitN_lit .shl _ 3, bitN_shl]; rfl
  unfold stlwN
  rw [e, Nat.mod_eq_of_lt hv, show (0xFF : Nat) = (0xFF#64).toNat from rfl, bitN_shl, bitN_shl,
    bit1N_not, bitN_and, bitN_or]
  rfl

theorem takeN_miss {T : Tbl} {gl n k : Nat} (h : Rf T k = some none) :
    takeN T gl n k = some (T, gl, n, none) := by
  simp only [takeN, h, Option.map_some]

/-- `take` keeps the buffers and the masks. -/
theorem takeN_shape {T T' : Tbl} {gl n k gl' n' : Nat} {r : Option Nat}
    (h : takeN T gl n k = some (T', gl', n', r)) :
    T'.cb = T.cb ∧ T'.sb = T.sb ∧ T'.mv = T.mv ∧ T'.cv = T.cv := by
  unfold takeN at h
  cases hr : Rf T k with
  | none => simp [hr] at h
  | some r0 =>
    cases r0 <;> simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq, takeHitN] at h
    · obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem takeN_hit {T : Tbl} {gl n k sr : Nat} (h : Rf T k = some (some sr)) :
    takeN T gl n k = some (takeHitN T gl n sr) := by
  simp only [takeN, h, Option.map_some]

/-- Control word loads are not disturbed by the value store. -/
theorem ctrl_load_val {T : Tbl} {m : DataMem} {mb : BitVec 64} (hm : T.InMem m) (hs : Sep T)
    (h : rv mb = T.mv) (sv : BitVec 64) (hsv : sv.toNat ≤ T.cv) (v : Int) (a : BitVec 64) :
    Mem.loadInt (m.storeInt (T.sb + sv <<< 4 + 8#64) 8 v) (T.cb + (a &&& mb) <<< 3) 8
      = some (T.ctrl (rv (a &&& mb))) := by
  have hg : (a &&& mb).toNat ≤ T.mv := by
    rw [rv_def] at h; rw [← h, BitVec.toNat_and]; exact Nat.and_le_right
  have := ctrl_addr hs _ hg; have := (slot_addr hs sv hsv).2
  have := hs.cb; have := hs.sb; have := hs.disj
  rw [loadInt_storeInt8_disj _ _ _ _ (by omega) (by omega) (by omega)]
  exact ctrl_load hm h a


/-- The hit branch's effect, at the registers `take_found` reads: `x16 = sr`,
`x2 = m`, `x10 = gl`, `x11 = n`. -/
theorem found_post {T : Tbl} {m : DataMem} {k gl n sr : Nat} (hm : T.InMem m) (hs : Sep T)
    (hb : T.Bounded k) (hgl : gl < W64) {x16 x2 x10 x11 : BitVec 64} (h16 : rv x16 = sr)
    (h2 : rv x2 = T.mv) (h10 : rv x10 = gl) (h11 : rv x11 = n)
    (hsv : (BitVec.ofNat 64 (bandN sr T.cv)).toNat ≤ T.cv) :
    let g := x16 >>> 3 &&& x2
    let w := BitVec.ofNat 64 (T.ctrl (rv g))
    let fl : BitVec 64 := if zbBV w = 0#64 then 0#64 else 1#64
    let sh := ((x16 &&& 7#64) <<< 3).toNat % 64
    let w' := w &&& ~~~(255#64 <<< sh) ||| (fl ^^^ 1#64) <<< sh
    let m' := (m.storeInt (T.sb + BitVec.ofNat 64 (bandN sr T.cv) <<< 4 + 8#64) 8 0).storeInt
      (T.cb + g <<< 3) 8 w'.toInt
    rv (x10 + fl) = bitN .wadd gl (eraseCtrlN (setVal T (bandN sr T.cv) 0) sr).2
      ∧ rv (x11 - 1#64) = bitN .wsub n 1
      ∧ (eraseCtrlN (setVal T (bandN sr T.cv) 0) sr).1.InMem m' ∧ Frame T m m' := by
  intro g w fl sh w' m'
  have hg : rv g = bandN (bitN .shr sr 3) T.mv := by
    rw [← h16, rv_def x16, bitN_shr _ 3 (by decide), ← rv_def, bandN_rv h2]
  have hgle : g.toNat ≤ T.mv := by rw [← rv_def, hg]; exact Nat.and_le_right
  have hw : w.toNat = T.ctrl (rv g) := by
    have := hb.ctrl (rv g); unfold W64 at this
    simp only [w, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt this
  have he : emptyN (T.ctrl (rv g)) = rv (zbBV w) := emptyN_rv (hb.ctrl _)
  have hsr : x16.toNat = sr := by rw [← rv_def]; exact h16
  have hsv' : (BitVec.ofNat 64 (bandN sr T.cv)).toNat = bandN sr T.cv := by
    have := hb.cv; have : bandN sr T.cv ≤ T.cv := Nat.and_le_right
    rw [BitVec.toNat_ofNat]; unfold W64 at *; exact Nat.mod_eq_of_lt (by omega)
  have hmem := inMem_setCtrl (inMem_setVal hm hs _ hsv 0#64) ⟨hs.cb, hs.sb, hs.disj⟩ g hgle w'
  have hfr := (frame_val hs m _ hsv 0).trans (frame_ctrl hs _ g hgle w'.toInt)
  have hmodel : eraseCtrlN (setVal T (bandN sr T.cv) 0) sr
      = (setCtrl (setVal T (bandN sr T.cv) 0) (rv g)
          (stlwN (T.ctrl (rv g)) (bitN .and sr 7) (if emptyN (T.ctrl (rv g)) = 0 then 1 else 0)),
        if emptyN (T.ctrl (rv g)) = 0 then 0 else 1) := by
    rw [hg]; rfl
  have h11' : rv (x11 - 1#64) = bitN .wsub n 1 := by
    rw [← h11, rv_def, rv_def, ← bitN_wsub]; rfl
  rw [hmodel]
  refine ⟨?_, h11', ?_, hfr⟩
  · by_cases hz : zbBV w = 0#64
    · simp only [fl, hz, he, rv_zero, ite_true, BitVec.add_zero]
      rw [h10]; unfold W64 at hgl; simp only [bitN, W64]; omega
    · simp only [fl, hz, he, rv_ne _ hz, ite_false]
      rw [← h10, rv_def, rv_def, ← bitN_wadd]; rfl
  · have hst := stlwN_bv w x16 (fl ^^^ 1#64) (by
      simp only [fl]; split <;> decide)
    rw [hw, hsr] at hst
    have hv : (fl ^^^ 1#64).toNat = if emptyN (T.ctrl (rv g)) = 0 then 1 else 0 := by
      simp only [fl, he]; by_cases hz : zbBV w = 0#64
      · simp [hz]
      · simp [hz, rv_ne _ hz]
    rw [hv] at hst
    have hst' : w'.toNat = _ := hst.symm
    rw [hst', ← rv_def g, hsv'] at hmem
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, BitVec.toInt_zero] at hmem
    exact hmem

/-! ## 3. The code and its specification

ABI (adapted from WeakCore's by-value `MapT`): arguments
`x0 = cb`, `x1 = sb`, `x2 = m`, `x3 = c`, `x4 = k` (as `lookup`), `x10 = gl`
(`growth_left`), `x11 = n` (`size`); results `x0` = the sum's tag (`0` =
`inl ()`, `1` = `inr old`), `x1 = old`, `x10 = gl'`, `x11 = n'`. The buffers
are updated in place (`cb`, `sb`, `m`, `c` are unchanged). `x5`–`x9`,
`x12`–`x17` are scratch: the probe blocks are `lookup`'s text (`flatLookup`)
with the labels renamed, so that its block invariants (`lookupTable`) are
reused; the hash uses `x9`, `x16`, `x17` as temporaries instead of `x9`–`x11`.

`take_found` lowers the hit branch:
* `xchgAtF sb1 s [1] z` (owned buffer, one thread) as a plain `ldr` of the
  value word and a `str xzr` of `zero V = 0` (no `swp`);
* `eraseCtrl` / `setCtrl` / `ctrlStore`: `g = (sr >> 3) & m`, `ldr` of
  control word `g`, `Gem = zb w`, flag `fl = (Gem ≠ 0)` (`cmp`, `cset`), byte
  `1 - fl` (`eor #1`); the byte store `stlw cb g b v8` as a word
  read-modify-write (WC rule 6): `bic` the lane mask `0xFF << 8b`, `orr` the
  byte shifted by `8b` (`lslv`), `str` the word;
* `gl += fl`, `n -= 1`. -/

/-- `take`, lowered. -/
def flatTake : Program := parseAArch64("
flat_take:
  movz x9, #0x7c15
  movk x9, #0x7f4a, lsl #16
  movk x9, #0x79b9, lsl #32
  movk x9, #0x9e37, lsl #48
  umulh x16, x4, x9
  mul x17, x4, x9
  eor x16, x16, x17
  and x17, x16, #0x7f
  orr x5, x17, #0x80
  lsr x6, x16, #7
  movz x7, #0
  mov x12, #0x7f7f7f7f7f7f7f7f
  mov x13, #0x0101010101010101
take_find:
  and x8, x6, x2
  ldr x14, [x0, x8, lsl #3]
  mul x15, x5, x13
  eor x15, x14, x15
  and x16, x15, x12
  add x16, x16, x12
  orr x16, x16, x15
  orr x16, x16, x12
  mvn x15, x16
  and x16, x14, x12
  add x16, x16, x12
  orr x16, x16, x14
  orr x16, x16, x12
  mvn x14, x16
  lsl x8, x8, #3
take_cand:
  cbz x15, take_cand_none
  rbit x16, x15
  clz x16, x16
  lsr x16, x16, #3
  orr x16, x8, x16
  and x17, x16, x3
  lsl x17, x17, #4
  ldr x9, [x1, x17]
  cmp x4, x9
  b.eq take_found
  sub x9, x15, #1
  and x15, x15, x9
  b take_cand
take_cand_none:
  cbz x14, take_next
  movz x0, #0
  ret
take_next:
  add x7, x7, #1
  add x6, x6, x7
  b take_find
take_found:
  add x17, x1, x17
  ldr x9, [x17, #8]
  str xzr, [x17, #8]
  lsr x8, x16, #3
  and x8, x8, x2
  ldr x14, [x0, x8, lsl #3]
  and x15, x14, x12
  add x15, x15, x12
  orr x15, x15, x14
  orr x15, x15, x12
  mvn x15, x15
  and x16, x16, #7
  lsl x16, x16, #3
  movz x17, #0xff
  lsl x17, x17, x16
  bic x14, x14, x17
  cmp x15, #0
  cset x12, ne
  eor x13, x12, #1
  lsl x13, x13, x16
  orr x14, x14, x13
  str x14, [x0, x8, lsl #3]
  add x10, x10, x12
  sub x11, x11, #1
  mov x1, x9
  movz x0, #1
  ret
")

/-- The logical variable: the table, the key, `growth_left`, `size`. -/
abbrev TX := Tbl × Nat × Nat × Nat

/-- What `take` keeps besides `lookup`'s invariant: `gl`, `n` in `x10`, `x11`,
their bounds (R-INT) and the separation hypothesis. -/
def Extra (x : TX) (s : MachineData) : Prop :=
  rv s.regs.X10.toBitVec = x.2.2.1 ∧ rv s.regs.X11.toBitVec = x.2.2.2 ∧ x.2.2.1 < W64
    ∧ x.2.2.2 < W64 ∧ Sep x.1

/-- `take`'s precondition: `lookup`'s (arguments, the table in memory, R-INT,
`ProbeEnds`), `gl`, `n` in their registers and 64-bit, and `Sep`. -/
def TakePre (x : TX) (ra : Int64) (t : MachineData) : Prop :=
  LookupPre (x.1, x.2.1) ra t ∧ Extra x t

/-- `take`'s postcondition: the model's answer in the result registers, the
model's table in memory, every byte outside the two buffers as it was, and
`sp`, `x19`–`x28` unchanged. -/
def TakePost (x : TX) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ T' gl' n' r, takeN x.1 x.2.2.1 x.2.2.2 x.2.1 = some (T', gl', n', r) ∧ ResRegs r s
    ∧ rv s.regs.X10.toBitVec = gl' ∧ rv s.regs.X11.toBitVec = n' ∧ T'.InMem s.dmem
    ∧ Frame x.1 t₀.dmem s.dmem ∧ Callee t₀ s

/-- The spec table: `lookup`'s invariants on the probe blocks, and `Extra`. -/
def takeTable (x : TX) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "flat_take", s => s = t₀ ∧ TakePre x ra t₀
  | "take_find", s => lookupTable (x.1, x.2.1) ra t₀ "find" s ∧ Extra x s
  | "take_cand", s => lookupTable (x.1, x.2.1) ra t₀ "cand" s ∧ Extra x s
  | "take_cand_none", s => lookupTable (x.1, x.2.1) ra t₀ "cand_none" s ∧ Extra x s
  | "take_next", s => lookupTable (x.1, x.2.1) ra t₀ "next" s ∧ Extra x s
  | "take_found", s => Common (x.1, x.2.1) ra t₀ s ∧ Extra x s ∧ ∃ sr, Rf x.1 x.2.1 = some (some sr)
      ∧ s.regs.X17.toBitVec = BitVec.ofNat 64 (bandN sr x.1.cv) <<< 4 ∧ rv s.regs.X16.toBitVec = sr
  | _, _ => False

/-- The variant: `lookup`'s. -/
def takeVar : Label → MachineData → Nat
  | "flat_take", s => lookupVar "flat_lookup" s
  | "take_find", s => lookupVar "find" s
  | "take_cand", s => lookupVar "cand" s
  | "take_cand_none", s => lookupVar "cand_none" s
  | "take_next", s => lookupVar "next" s
  | _, _ => 0

section Spec
variable [CodeEnv]

set_option hygiene false in
/-- Open probe block `l`'s invariant (`lookup`'s, and `Extra`). -/
local macro "open_inv" l:str : tactic => `(tactic| (
  have h := ‹takeTable _ _ _ $l _ ∧ _›
  simp only [takeTable, takeVar, lookupTable, lookupVar, Common, LookupPre, Args, Callee, Extra] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1, h2, h3, h4, hlr⟩, hmem, hb, hpe⟩, hdm, hcs, h5, h12, h13, hst⟩, hf⟩,
    hx10, hx11, hgl, hn, hsep⟩, rfl⟩ := h
  rw [hdm] at hmem))

set_option hygiene false in
/-- Jump to a probe label: its invariant from the opened facts and `ts`. -/
local macro "goto_inv" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
  simp only [takeTable, takeVar, lookupTable, lookupVar, Common, LookupPre, Args, Callee, Extra, restN]
  simp [h0, h1, h2, h3, h4, hlr, hmem, hb, hpe, hdm, hcs, h5, h12, h13, hst, hx10, hx11, hgl, hn,
    hsep, $ts,*]))

set_option linter.unusedSimpArgs false in
/-- **`take`'s specification** (sequential machine, total correctness):
entered at `flat_take` with the table `T` in memory, its masks and `k` in
`x0`–`x4`, `gl`, `n` in `x10`, `x11`, R-INT, `Sep T` and `ProbeEnds T k`,
every run returns to `ra` with the model's answer `takeN T gl n k`: the result
in `x0`/`x1`, `gl'`, `n'` in `x10`, `x11`, the model's table in memory, every
byte outside the two buffers unchanged, and `sp`, `x19`–`x28` unchanged. -/
theorem take_spec (hpl : Program.PlacedIn flatTake) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label "flat_take") TakePre TakePost := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := flatTake) takeTable takeVar
    (hblocks := ?_) (hpre := fun x ra t h => ⟨rfl, h⟩)
  rintro ⟨T, k, gl, n⟩ ra t₀
  cfg_cases [flatTake]
  · -- the hash
    vcgen
    have h := ‹takeTable _ ra _ "flat_take" _ ∧ _›
    simp only [takeTable, takeVar, lookupVar, TakePre, Extra] at h
    obtain ⟨⟨rfl, ⟨⟨h0, h1, h2, h3, rfl, hlr⟩, hmem, hb, hpe⟩, hx10, hx11, hgl, hn, hsep⟩, rfl⟩ := h
    simp only [takeTable, takeVar, lookupTable, lookupVar, Common, LookupPre, Args, Callee, Extra]
    simp [h0, h1, h2, h3, hlr, hmem, hb, hpe, hashN_rv, hmB, var_le, Rf, hx10, hx11, hgl, hn, hsep]
  · -- find: one group
    vcgen
    all_goals
      open_inv "take_find"
      rw [findN_step _ _ _ _ _ hst] at hf
      simp only [bandN_rv h2, shl3_rv, matchN_rv (hb.ctrl _) h5, emptyN_rv (hb.ctrl _),
        matchBV, zbBV] at hf
      try (rename_i v hv _; simp [h0, hdm, ctrl_load hmem h2] at hv; subst hv)
      simp only [takeTable, takeVar, lookupTable, lookupVar, Common, LookupPre, Args, Callee, Extra, restN]
      simp [h0, h1, h2, h3, h4, hlr, hmem, hb, hpe, hdm, hcs, h5, h12, h13, hst, ctrl_load hmem h2,
        hf, Nat.le_of_lt (rv_lt _), hx10, hx11, hgl, hn, hsep]
  · -- cand: one lane
    vcgen
    all_goals open_inv "take_cand"
    case vc1 => -- no lane left
      rename_i hz _
      simp at hz
      simp only [hz, rv_zero, candN_zero] at hf
      goto_inv [hf, hz]
      decide
    case vc4 => -- the key matches
      rename_i hz _ v hv hc _
      simp [h1, hdm, key_load hmem h3] at hv hz
      subst hv
      simp at hc
      rw [sub_rv _ _ (hb.key _), h4] at hc
      rw [candN_rv _ _ _ _ hz] at hf
      simp only [bandN_rv h3, ← hc, eq_self, ite_true, contN] at hf
      refine Or.inl (Table.ofLabels_at ⟨by decide, ?_⟩)
      simp only [takeTable, takeVar, Common, LookupPre, Args, Callee, Extra]
      simp [h0, h1, h2, h4, hlr, hmem, hb, hpe, hdm, hcs, h5, h12, h13, hst, hx10, hx11, hgl, hn, hsep]
      exact ⟨⟨h3, hf.symm, by rw [bandN_rv h3, ofNat_rv]⟩,
        Or.inl (Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero (rv_ne _ hz)) (Nat.le_add_left _ _))⟩
    case vc5 => -- it does not: the next lane
      rename_i hz _ v hv hc _
      simp [h1, hdm, key_load hmem h3] at hv hz
      subst hv
      simp at hc
      rw [sub_rv _ _ (hb.key _), h4] at hc
      rw [candN_rv _ _ _ _ hz] at hf
      simp only [bandN_rv h3, hc, ite_false] at hf
      goto_inv [hf, clear_lt _ hz]
    all_goals simp [h1, hdm, key_load hmem h3]
  · -- cand_none
    vcgen
    all_goals open_inv "take_cand_none"
    case vc1 => -- no empty lane: the next group
      rename_i hz _
      simp at hz
      simp only [contN, hz, rv_zero, ↓reduceIte] at hf
      goto_inv [hf]
      decide
    case vc2 => -- an empty lane: absent, the table unchanged
      rename_i hz _
      simp at hz
      simp only [contN, rv_ne _ hz, ↓reduceIte] at hf
      refine Or.inr ⟨by simp [hlr], T, gl, n, none, takeN_miss hf.symm, ?_⟩
      simp [ResRegs, hdm, Callee, hcs, hx10, hx11, hmem, Frame.refl]
  · -- next: the triangular step
    vcgen
    all_goals
      open_inv "take_next"
      have hlt := next_lt hpe hst hf
      have h7 := rv_add1 _ (Nat.lt_trans (Nat.succ_lt_succ hlt) hb.mv)
      simp only [restN, wadd1] at hf
      simp only [wadd_rv] at hf
      simp only [h7] at hf
      goto_inv [hf, h7, var_lt _ _ hst, Nat.succ_le_of_lt hlt]
  · -- found
    vcgen
    all_goals
      have h := ‹takeTable _ _ _ "take_found" _ ∧ _›
      simp only [takeTable, takeVar, Common, LookupPre, Args, Callee, Extra] at h
      obtain ⟨⟨⟨⟨⟨h0, h1, h2, h3, h4, hlr⟩, hmem, hb, hpe⟩, hdm, hcs, h5, h12, h13, hst⟩,
        ⟨hx10, hx11, hgl, hn, hsep⟩, sr, hf, h17, h16⟩, rfl⟩ := h
      rw [hdm] at hmem
      have hvl := val_load hmem hb.cv (bandN sr T.cv) Nat.and_le_right
      have hsv : (BitVec.ofNat 64 (bandN sr T.cv)).toNat ≤ T.cv := by
        have e1 : bandN sr T.cv ≤ T.cv := Nat.and_le_right
        have e2 := hb.cv
        unfold W64 at e2
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact e1
    case vc9 =>
      rename_i v hv _ _ v2 hv2 _ _ _ _ _
      simp [h1, h17, hdm, hvl] at hv
      subst hv
      simp [h0, h1, h2, h17, hdm, ctrl_load_val hmem hsep h2 _ hsv] at hv2
      subst hv2
      refine Or.inr ⟨by simp [hlr], _, _, _, _, takeN_hit hf, ?_⟩
      simp only [ResRegs, Reg64s.getRegOrZr_X, Reg64s.getXReg_X1, h1, ShiftRegExpr.interp_lsl, MemWidth.bits,
    Reg64s.getXReg_X17, h17, Int64.reduceToInt, Int.toNat_zero, BitVec.shiftLeft_zero, Reg64s.setRegOrZr_X, hdm,
    AddrExpr.eval_imm, Reg64s.getRegOrSp_X, Reg64s.X17_setXReg, ↓reduceIte, UInt64.ofBitVec_add, Nat.reduceLT,
    UInt64.ofBitVec_shiftLeft, UInt64.ofBitVec_ofNat, UInt64.reduceOfNat, UInt64.toBitVec_add,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod, BitVec.shiftLeft_eq',
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ConstExpr.interp_int64, Int64.toBitVec_ofNat, MachineData.regs_mk,
    BitVec.ofInt_natCast, MachineData.status_mk, MachineData.dmem_mk, reduceCtorEq, ↓evalUBFM_lsr64, Reg64s.getXReg_X16,
    Reg64s.X16_setXReg, Reg64s.getXReg_X8, Reg64s.X8_setXReg, UInt64.ofBitVec_shiftRight, UInt64.ofBitVec_toBitVec,
    UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', Reg64s.getXReg_X2, Reg64s.X2_setXReg, Reg64s.setXReg_setXReg,
    Reg64s.getRegOrZr_XZR, BitVec.toInt_zero, AddrExpr.eval_reg, Reg64s.getXReg_X0, Reg64s.X0_setXReg, h0, or_false,
    MemExtRegExpr.interp_X, UInt64.ofBitVec_and, UInt64.toBitVec_and, MemExtendAmount.toNat, Reg64s.getXReg_X14,
    Reg64s.X14_setXReg, Reg64s.getXReg_X12, Reg64s.X12_setXReg, h12, Reg64s.getXReg_X15, Reg64s.X15_setXReg,
    UInt64.ofBitVec_or, UInt64.toBitVec_or, BitVec.zero_or, ConstExpr.immVal_int64_W64, Reg64s.setRegOrSp_X,
    Nat.reduceAdd, ↓evalUBFM_lsl64, Nat.reduceSub, BitVec.ofInt_ofNat, BitVec.reduceAnd,
    UInt64.toNat_toBitVec, UInt64.ofBitVec_not,
    UInt64.toBitVec_not, ExtOrImmReg.interp_imm64, BitVec.sub_zero, Reg64s.setRegOrZr_XZR, CondCode.interp,
    StatusFlags.subs, StatusFlags.from_result, BitVec.zero_eq, Int.sub_zero, BEq.rfl, bne_self_eq_false, StatusFlags.z_mk, beq_iff_eq, BitVec.zero_add,
    UInt64.toBitVec_ofBitVec, Reg64s.getXReg_X13, Reg64s.X13_setXReg, UInt64.ofBitVec_xor, UInt64.toBitVec_xor,
    Reg64s.getXReg_X10, Reg64s.X10_setXReg, Reg64s.getXReg_X11, Reg64s.X11_setXReg, Reg64s.getXReg_X9,
    Reg64s.X9_setXReg, Reg64s.X1_setXReg, true_and, UInt64.ofBitVec_sub, UInt64.toBitVec_sub,
    Callee, Reg64s.SP_setXReg, hcs, Reg64s.X19_setXReg, Reg64s.X20_setXReg,
    Reg64s.X21_setXReg, Reg64s.X22_setXReg, Reg64s.X23_setXReg, Reg64s.X24_setXReg, Reg64s.X25_setXReg,
    Reg64s.X26_setXReg, Reg64s.X27_setXReg, Reg64s.X28_setXReg, and_self, and_true]
      exact ⟨by simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show T.val (bandN sr T.cv) < 2 ^ 64 from hb.val _)],
        found_post hmem hsep hb hgl h16 h2 hx10 hx11 hsv⟩
    all_goals simp [h0, h1, h2, h17, hdm, hvl, ctrl_load_val hmem hsep h2 _ hsv]

end Spec

/-! ## 4. Non-vacuity on the FlatHashMap `lookup` lowering's `tbl1`

`tbl1`: one group, key `5` in lane `2` with value `55`, every other lane
empty; `gl = 3`, `n = 1`. Taking `5` hits: lane 2 becomes empty (`0x00`, the
group still has an empty lane), so the control word becomes `0`, the value
`0`, `gl = 4`, `n = 0`, result `inr 55`. Taking `6` misses: the table and
counters are unchanged, result `inl ()`. Every table-level hypothesis of
`take_spec` (`Bounded`, `Sep`, `ProbeEnds`, the counter bounds) holds for both
keys, by `decide`. -/

theorem tbl1_sep : Sep tbl1 := ⟨by decide, by decide, Or.inl (by decide)⟩

theorem tbl1_bounded6 : tbl1.Bounded 6 :=
  ⟨by decide, by decide, fun s => by simp only [tbl1]; split <;> decide,
   fun s => by simp only [tbl1]; split <;> decide,
   fun _ => by show (hashN 5).1 * 2 ^ 16 < W64; decide +kernel, by decide⟩

theorem tbl1_probeEnds6 : ProbeEnds tbl1 6 := by
  show (lookupN tbl1 6).isSome = true
  rw [tbl1_lookup6]; rfl

/-- The hit: `take 5` on `tbl1`. -/
theorem tbl1_take5 :
    (takeN tbl1 3 1 5).map (fun r => (r.1.ctrl 0, r.1.val 2, r.1.key 2, r.2.1, r.2.2.1, r.2.2.2))
      = some (0, 0, 5, 4, 0, some 55) := by decide +kernel

/-- The miss: `take 6` on `tbl1` leaves everything unchanged. -/
theorem tbl1_take6 : takeN tbl1 3 1 6 = some (tbl1, 3, 1, none) :=
  takeN_miss (by decide +kernel)

/-- The table-level part of `take_spec`'s precondition, at `tbl1` with key `k`. -/
def TblHyps (T : Tbl) (k gl n : Nat) : Prop :=
  T.Bounded k ∧ ProbeEnds T k ∧ gl < W64 ∧ n < W64 ∧ Sep T

theorem tbl1_hyps5 : TblHyps tbl1 5 3 1 := ⟨tbl1_bounded, tbl1_probeEnds, by decide, by decide, tbl1_sep⟩
theorem tbl1_hyps6 : TblHyps tbl1 6 3 1 := ⟨tbl1_bounded6, tbl1_probeEnds6, by decide, by decide, tbl1_sep⟩

/-- `take_spec`'s precondition from the registers, the table in memory and the
table-level hypotheses. -/
theorem takePre_of {T : Tbl} {k gl n : Nat} {ra : Int64} {t : MachineData} (ha : Args T k ra t)
    (h10 : rv t.regs.X10.toBitVec = gl) (h11 : rv t.regs.X11.toBitVec = n) (hm : T.InMem t.dmem)
    (h : TblHyps T k gl n) : TakePre (T, k, gl, n) ra t :=
  ⟨⟨ha, hm, h.1, h.2.1⟩, h10, h11, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

section Witness
variable [CodeEnv]

/-- **Non-vacuity, hit**: `take_spec` at `tbl1`, key `5`: `take` returns to
`ra` with `x0 = 1`, `x1 = 55`, `x10 = 4`, `x11 = 0`, control word `0` and
value `0` of slot 2 in memory, the frame intact. -/
theorem take_tbl1_hit (hpl : Program.PlacedIn flatTake) (ra : Int64) (t : MachineData)
    (ha : Args tbl1 5 ra t) (h10 : rv t.regs.X10.toBitVec = 3) (h11 : rv t.regs.X11.toBitVec = 1)
    (hm : tbl1.InMem t.dmem) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.X0 = 1 ∧ st.1.regs.X1.toNat = 55
        ∧ rv st.1.regs.X10.toBitVec = 4 ∧ rv st.1.regs.X11.toBitVec = 0
        ∧ Mem.loadInt st.1.dmem (tbl1.cb + 0#64 <<< 3) 8 = some 0
        ∧ Mem.loadInt st.1.dmem (tbl1.sb + 2#64 <<< 4 + 8#64) 8 = some 0
        ∧ Frame tbl1 t.dmem st.1.dmem)
      (t, (_root_.Executable.labels cenv).label "flat_take") :=
  eventually_weaken _ _ _ _ (fun st ⟨hra, T', gl', n', r, hr, hres, h10', h11', hin, hfr, _⟩ => by
      have h5 := tbl1_take5
      rw [hr] at h5
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h5
      obtain ⟨hcb, hsb, hmv, hcv⟩ := takeN_shape hr
      obtain ⟨hc, hv, -, rfl, rfl, rfl⟩ := h5
      have hc' := hin.1 0#64 (by rw [hmv]; decide)
      have hv' := (hin.2 2#64 (by rw [hcv]; decide)).2
      rw [hcb] at hc'; rw [hsb] at hv'
      exact ⟨hra, hres.1, hres.2, h10', h11', by rw [hc'] ; simp [hc], by rw [hv']; simp [hv], hfr⟩)
    (take_spec hpl (tbl1, 5, 3, 1) ra t (takePre_of ha h10 h11 hm tbl1_hyps5))

/-- **Non-vacuity, miss**: `take_spec` at `tbl1`, key `6`: `take` returns to
`ra` with `x0 = 0`, `x10 = 3`, `x11 = 1`, and `tbl1` still in memory. -/
theorem take_tbl1_miss (hpl : Program.PlacedIn flatTake) (ra : Int64) (t : MachineData)
    (ha : Args tbl1 6 ra t) (h10 : rv t.regs.X10.toBitVec = 3) (h11 : rv t.regs.X11.toBitVec = 1)
    (hm : tbl1.InMem t.dmem) :
    Eventually cenv.instrStep (fun st => st.2 = ra ∧ st.1.regs.X0 = 0
        ∧ rv st.1.regs.X10.toBitVec = 3 ∧ rv st.1.regs.X11.toBitVec = 1 ∧ tbl1.InMem st.1.dmem)
      (t, (_root_.Executable.labels cenv).label "flat_take") :=
  eventually_weaken _ _ _ _ (fun st ⟨hra, T', gl', n', r, hr, hres, h10', h11', hin, _⟩ => by
      rw [tbl1_take6] at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
      exact ⟨hra, hres, h10', h11', hin⟩)
    (take_spec hpl (tbl1, 6, 3, 1) ra t (takePre_of ha h10 h11 hm tbl1_hyps6))

end Witness

end Kraken.Promising.Lower.Flat.Take
