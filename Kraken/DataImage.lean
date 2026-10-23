/-
**Data images**: the initial bytes of a data section, with label-valued
words resolved.

A data section of an assembly text (`.data`, `.rodata`) is a list of
`DataImage.Item`s: labels, literal bytes (`.byte`, `.ascii`, `.asciz`), zero
fill (`.zero`, `.skip`), 8-byte words (`.quad v`), label-valued 8-byte words
(`.quad L`) and alignment (`.balign n`, `.p2align k` as `.align (2 ^ k)`).
Laid out from a base address, every item takes `size` bytes (an alignment
pads to the next multiple of `n` of the absolute address), every label names
the address of the item after it, and `image res base items` is the section's
bytes, little-endian, a `.quad L` being the bytes of `res L`. The resolution
`res` is a parameter: `resolve code base items` takes a data label to its
address in the section (`dataLabel`) and any other label to `code L`, the
address of a code label in the program's layout (the ISA files give it from
the laid-out executable: `Promising/X64Data.lean`, `Promising/AArch64Data.lean`).
`dataMem m base img` stores the image into a memory.

Lemmas, the data analogue of `codeAt`:

- `bytesOf_length`, `image_length`: the image has the sizes of the layout;
- `image_drop`: from the address of item `n` (`addrAt`), the image is the
  image of the items from `n`;
- `loadBytes_dataMem_item`: in `dataMem`, the bytes at item `n`'s address are
  that item's bytes; `loadInt_quadLabel` / `ofInt_load_quadLabel`: a
  `.quad L` reads back `res L`, `loadInt_quad` a `.quad v`;
- `dataLabel_addrAt`, `resolve_data`, `resolve_code`: a data label resolves
  to the address of its first occurrence, any other label through `code`;
- `image_congr`, `image_resolve_congr`: the image depends on the resolution
  only at the labels its `.quad`s name, so on the code only through those
  labels' addresses.
-/
import Kraken.Mem

namespace Kraken.DataImage

/-- A data directive. -/
inductive Item
  /-- A label: the address of the next item. -/
  | label (l : String)
  /-- Literal bytes (`.byte`, `.ascii`, `.asciz` with its terminator). -/
  | bytes (bs : List UInt8)
  /-- `n` zero bytes (`.zero n`, `.skip n`). -/
  | zero (n : Nat)
  /-- An 8-byte little-endian word (`.quad v`). -/
  | quad (v : Int)
  /-- The 8-byte address of a label (`.quad L`). -/
  | quadLabel (l : String)
  /-- Zero padding to the next multiple of `n` (`.balign n`; `.p2align k` is
  `.align (2 ^ k)`); no padding for `n = 0`. -/
  | align (n : Nat)
  deriving Repr, DecidableEq

/-- The padding from `cur` to the next multiple of `n`. -/
def padTo (cur n : Nat) : Nat := if n = 0 then 0 else (n - cur % n) % n

/-- The bytes an item occupies at address `cur`. -/
def size (cur : Nat) : Item → Nat
  | .label _ => 0
  | .bytes bs => bs.length
  | .zero n => n
  | .quad _ => 8
  | .quadLabel _ => 8
  | .align n => padTo cur n

/-- The address of item `n` of `items` laid out from `cur` (the end address
for `n` at or past the length). -/
def addrAt : Nat → List Item → Nat → Nat
  | cur, [], _ => cur
  | cur, _ :: _, 0 => cur
  | cur, i :: is, n + 1 => addrAt (cur + size cur i) is n

/-- The end address of `items` laid out from `cur`. -/
def endAddr (cur : Nat) (items : List Item) : Nat := addrAt cur items items.length

/-- The data labels of `items` laid out from `cur`, with their addresses, in
order. -/
def labelsFrom : Nat → List Item → List (String × Nat)
  | _, [] => []
  | cur, .label l :: is => (l, cur) :: labelsFrom cur is
  | cur, i :: is => labelsFrom (cur + size cur i) is

/-- The address of a data label (its first occurrence), if `items` has it. -/
def dataLabel (base : Nat) (items : List Item) (l : String) : Option Nat :=
  (labelsFrom base items).lookup l

/-- **The label resolution of a data section**: a data label is its address
in the section, any other label is `code l`, its address in the program's
code layout. -/
def resolve (code : String → BitVec 64) (base : Nat) (items : List Item) (l : String) : BitVec 64 :=
  match dataLabel base items l with
  | some a => BitVec.ofNat 64 a
  | none => code l

/-- The bytes of an item at address `cur`, label-valued words through `res`. -/
def bytesOf (res : String → BitVec 64) (cur : Nat) : Item → List UInt8
  | .label _ => []
  | .bytes bs => bs
  | .zero n => List.replicate n 0
  | .quad v => Int.toBytes 8 v
  | .quadLabel l => Int.toBytes 8 (res l).toInt
  | .align n => List.replicate (padTo cur n) 0

/-- **The image of a data section** laid out from `cur`: the items' bytes in
order. -/
def image (res : String → BitVec 64) : Nat → List Item → List UInt8
  | _, [] => []
  | cur, i :: is => bytesOf res cur i ++ image res (cur + size cur i) is

/-- The image stored into a memory at `base`. -/
def dataMem (m : Mem 64) (base : Nat) (img : List UInt8) : Mem 64 :=
  m.storeBytes (BitVec.ofNat 64 base) img

/-- The labels the `.quad`s of `items` name. -/
def quadLabels : List Item → List String
  | [] => []
  | .quadLabel l :: is => l :: quadLabels is
  | _ :: is => quadLabels is

theorem bytesOf_length (res : String → BitVec 64) (cur : Nat) (i : Item) :
    (bytesOf res cur i).length = size cur i := by
  cases i <;> simp [bytesOf, size, Int.toBytes_length]

theorem image_length (res : String → BitVec 64) :
    ∀ (cur : Nat) (items : List Item), (image res cur items).length + cur = endAddr cur items
  | cur, [] => by simp [image, endAddr, addrAt]
  | cur, i :: is => by
    have ih := image_length res (cur + size cur i) is
    simp only [image, List.length_append, bytesOf_length, endAddr, List.length_cons, addrAt] at *
    omega

theorem le_addrAt : ∀ (cur : Nat) (items : List Item) (n : Nat), cur ≤ addrAt cur items n
  | cur, [], _ => by simp [addrAt]
  | cur, _ :: _, 0 => by simp [addrAt]
  | cur, i :: is, n + 1 => by
    have := le_addrAt (cur + size cur i) is n
    simp only [addrAt]; omega

/-- **The image from item `n`**: past the bytes before item `n`, the image is
the image of the items from `n`, laid out from item `n`'s address. -/
theorem image_drop (res : String → BitVec 64) :
    ∀ (cur : Nat) (items : List Item) (n : Nat),
      (image res cur items).drop (addrAt cur items n - cur) = image res (addrAt cur items n) (items.drop n)
  | cur, [], _ => by simp [image, addrAt]
  | cur, _ :: _, 0 => by simp [addrAt]
  | cur, i :: is, n + 1 => by
    have ih := image_drop res (cur + size cur i) is n
    have hle := le_addrAt (cur + size cur i) is n
    simp only [image, addrAt, List.drop_succ_cons]
    rw [show addrAt (cur + size cur i) is n - cur
        = (bytesOf res cur i).length + (addrAt (cur + size cur i) is n - (cur + size cur i)) by
      rw [bytesOf_length]; omega, ← List.drop_drop, List.drop_left, ih]

/-- The bytes at item `n` (of `items` from `cur`): the item's own bytes. -/
theorem image_item (res : String → BitVec 64) (cur : Nat) (items : List Item) {n : Nat} {i : Item}
    (hn : items[n]? = some i) :
    ((image res cur items).drop (addrAt cur items n - cur)).take (size (addrAt cur items n) i)
      = bytesOf res (addrAt cur items n) i := by
  rw [image_drop, List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hn).1,
    (List.getElem?_eq_some_iff.mp hn).2, image, ← bytesOf_length res, List.take_left]

private theorem loadBytes_storeBytes_off (m : Mem 64) (a : BitVec 64) (bs : List UInt8) (off k : Nat)
    (h : off + k ≤ bs.length) (hw : bs.length ≤ 2 ^ 64) :
    (m.storeBytes a bs).loadBytes (a + BitVec.ofNat 64 off) k = some ((bs.drop off).take k) := by
  have hget : ∀ i, i < k → (m.storeBytes a bs).get? (a + BitVec.ofNat 64 off + BitVec.ofNat 64 i) =
      ((bs.drop off).take k)[i]? := by
    intro i hi
    have hlt : off + i < 2 ^ 64 := by omega
    have hbs : (bs.At a).get? (a + BitVec.ofNat 64 (off + i)) = bs[off + i]? := get?_At_idx bs a (off + i) hlt hw
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, ← Std.ExtHashMap.get?_eq_getElem?, hbs,
      List.getElem?_eq_getElem (by omega)]
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
    rfl
  have hlen : ((bs.drop off).take k).length = k := by simp; omega
  rw [Mem.loadBytes, show (List.range k).map (fun i => (m.storeBytes a bs).get? (a + BitVec.ofNat 64 off + .ofNat _ i))
    = (List.range k).map (fun i => ((bs.drop off).take k)[i]?) from
      List.map_congr_left (fun i hi => hget i (List.mem_range.mp hi))]
  have hm := List.map_range_getElem? ((bs.drop off).take k)
  rw [hlen] at hm
  rw [hm, List.allSome_map_some]

/-- **Bytes of a stored image at an offset**: `k` bytes at `base + off` of
`dataMem m base img` are the image's bytes there, inside the image. -/
theorem loadBytes_dataMem_off (m : Mem 64) (base : Nat) (img : List UInt8) (off k : Nat)
    (h : off + k ≤ img.length) (hw : img.length ≤ 2 ^ 64) :
    (dataMem m base img).loadBytes (BitVec.ofNat 64 (base + off)) k = some ((img.drop off).take k) := by
  rw [BitVec.ofNat_add]
  exact loadBytes_storeBytes_off m _ img off k h hw

theorem addrAt_size_le (cur : Nat) :
    ∀ (items : List Item) {n : Nat} {i : Item}, items[n]? = some i →
      addrAt cur items n + size (addrAt cur items n) i ≤ endAddr cur items
  | [], _, _, h => by simp at h
  | j :: is, 0, i, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have := le_addrAt (cur + size cur j) is is.length
    simp only [addrAt, endAddr, List.length_cons] at *
    omega
  | j :: is, n + 1, i, h => by
    simp only [List.getElem?_cons_succ] at h
    have := addrAt_size_le (cur + size cur j) is h
    simpa [addrAt, endAddr] using this

/-- **The bytes of item `n` in memory**: in the image stored at `base`, the
bytes at item `n`'s address are the item's bytes, if the section fits below
`2 ^ 64`. -/
theorem loadBytes_dataMem_item (res : String → BitVec 64) (m : Mem 64) (base : Nat) (items : List Item)
    (hfit : endAddr base items ≤ 2 ^ 64) {n : Nat} {i : Item} (hn : items[n]? = some i) :
    (dataMem m base (image res base items)).loadBytes (BitVec.ofNat 64 (addrAt base items n))
        (size (addrAt base items n) i) = some (bytesOf res (addrAt base items n) i) := by
  have hle := le_addrAt base items n
  have hsz := addrAt_size_le base items hn
  have hlen := image_length res base items
  have := loadBytes_storeBytes_off m (BitVec.ofNat 64 base) (image res base items) (addrAt base items n - base)
    (size (addrAt base items n) i) (by omega) (by omega)
  rw [← BitVec.ofNat_add, show base + (addrAt base items n - base) = addrAt base items n by omega,
    image_item res base items hn] at this
  exact this

/-- **A `.quad L` word in memory** holds the bytes of `res L`. -/
theorem loadInt_quadLabel (res : String → BitVec 64) (m : Mem 64) (base : Nat) (items : List Item)
    (hfit : endAddr base items ≤ 2 ^ 64) {n : Nat} {l : String} (hn : items[n]? = some (.quadLabel l)) :
    (dataMem m base (image res base items)).loadInt (BitVec.ofNat 64 (addrAt base items n)) 8
      = some (Int.ofBytes (Int.toBytes 8 (res l).toInt)) := by
  have := loadBytes_dataMem_item res m base items hfit hn
  simp only [size, bytesOf] at this
  rw [Mem.loadInt, this]
  rfl

/-- **A `.quad L` word read as a 64-bit value is `res L`.** -/
theorem ofInt_load_quadLabel (res : String → BitVec 64) (m : Mem 64) (base : Nat) (items : List Item)
    (hfit : endAddr base items ≤ 2 ^ 64) {n : Nat} {l : String} (hn : items[n]? = some (.quadLabel l)) :
    ((dataMem m base (image res base items)).loadInt (BitVec.ofNat 64 (addrAt base items n)) 8).map
      (BitVec.ofInt 64) = some (res l) := by
  rw [loadInt_quadLabel res m base items hfit hn, Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

/-- A `.quad v` word in memory holds the bytes of `v`. -/
theorem loadInt_quad (res : String → BitVec 64) (m : Mem 64) (base : Nat) (items : List Item)
    (hfit : endAddr base items ≤ 2 ^ 64) {n : Nat} {v : Int} (hn : items[n]? = some (.quad v)) :
    (dataMem m base (image res base items)).loadInt (BitVec.ofNat 64 (addrAt base items n)) 8
      = some (Int.ofBytes (Int.toBytes 8 v)) := by
  have := loadBytes_dataMem_item res m base items hfit hn
  simp only [size, bytesOf] at this
  rw [Mem.loadInt, this]
  rfl

/-! ### Labels -/

private theorem lookup_labelsFrom_label :
    ∀ (cur : Nat) (items : List Item) {n : Nat} {l : String},
      items[n]? = some (.label l) → (∀ k, k < n → items[k]? ≠ some (.label l)) →
      (labelsFrom cur items).lookup l = some (addrAt cur items n)
  | _, [], _, _, h, _ => by simp at h
  | cur, j :: is, 0, l, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [labelsFrom, addrAt]
  | cur, j :: is, n + 1, l, h, hfirst => by
    simp only [List.getElem?_cons_succ] at h
    have hj : j ≠ .label l := fun hj => hfirst 0 (by omega) (by simp [hj])
    have ih := lookup_labelsFrom_label (cur + size cur j) is h
      (fun k hk => by simpa using hfirst (k + 1) (by omega))
    cases j with
    | label l' =>
      have hl' : l' ≠ l := fun e => hj (e ▸ rfl)
      have hb : (l == l') = false := by simpa using fun e => hl' e.symm
      simp only [labelsFrom, List.lookup, hb, addrAt, size, Nat.add_zero] at ih ⊢
      exact ih
    | _ => simpa [labelsFrom, addrAt] using ih

/-- **A data label's address**: the address of its first occurrence. -/
theorem dataLabel_addrAt {base : Nat} {items : List Item} {n : Nat} {l : String}
    (hn : items[n]? = some (.label l)) (hfirst : ∀ k, k < n → items[k]? ≠ some (.label l)) :
    dataLabel base items l = some (addrAt base items n) :=
  lookup_labelsFrom_label base items hn hfirst

/-- A data label resolves to its address in the section. -/
theorem resolve_data {code : String → BitVec 64} {base : Nat} {items : List Item} {l : String} {a : Nat}
    (h : dataLabel base items l = some a) : resolve code base items l = BitVec.ofNat 64 a := by
  simp [resolve, h]

/-- Any other label resolves through the code layout. -/
theorem resolve_code {code : String → BitVec 64} {base : Nat} {items : List Item} {l : String}
    (h : dataLabel base items l = none) : resolve code base items l = code l := by
  simp [resolve, h]

/-! ### Independence of the code -/

/-- **The image depends on the resolution only at the labels its `.quad`s
name.** -/
theorem image_congr {res res' : String → BitVec 64} :
    ∀ (cur : Nat) (items : List Item), (∀ l ∈ quadLabels items, res l = res' l) →
      image res cur items = image res' cur items
  | _, [], _ => rfl
  | cur, i :: is, h => by
    have ih := image_congr (res := res) (res' := res') (cur + size cur i) is
    cases i with
    | quadLabel l =>
      simp only [quadLabels, List.mem_cons, forall_eq_or_imp] at h
      simp [image, bytesOf, h.1, ih h.2]
    | label _ => simp [image, bytesOf, ih (by simpa [quadLabels] using h)]
    | bytes _ => simp [image, bytesOf, ih (by simpa [quadLabels] using h)]
    | zero _ => simp [image, bytesOf, ih (by simpa [quadLabels] using h)]
    | quad _ => simp [image, bytesOf, ih (by simpa [quadLabels] using h)]
    | align _ => simp [image, bytesOf, ih (by simpa [quadLabels] using h)]

/-- **Two code layouts that agree on the labels the section's `.quad`s name
give the same image**: the image does not see the code otherwise. -/
theorem image_resolve_congr {code code' : String → BitVec 64} {base : Nat} {items : List Item}
    (h : ∀ l ∈ quadLabels items, code l = code' l) (cur : Nat) :
    image (resolve code base items) cur items = image (resolve code' base items) cur items :=
  image_congr cur items fun l hl => by
    unfold resolve
    split
    · rfl
    · exact h l hl

end Kraken.DataImage
