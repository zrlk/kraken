import Scc.Cert.Elf

/-!
# The byte check: an executable's `.rodata` against its text's

The loaders lay `.rodata` out from the *text* (`rodataWords`, `Scc/Sem/Target.lean`), not from the
executable: the only link between the two is the bytes `ld` wrote. `bytesCheck` compares the executable's
whole `.rodata` section with the image the loader lays out from the text's `.rodata` items (`rodataImage`,
which `rodataWords` cuts into words, `rodataWords_eq`): the image, then zeros to the section's end, with the
image's last word (zero-padded by `DataImage.words`) inside the section. The code labels are resolved by the
caller's `code`, the ISA's `quadCode` (`Scc.Cert.Link.X64.quadCode`, `Scc.Cert.Link.A64.quadCode`; the two
cannot be imported together, so this module imports neither). The executable's layout is read here
(`elfLayout`), never taken from the caller.

**The granule words** (`granuleWordsOk`): a `.text` of a granule or more must be whole granules on a granule
boundary, and the last 8 bytes of every granule (the word the runtime finds at `a - a % granule + granule - 8`
from a code address `a`, by absolute address) must be the word `.quad scc_gc_desc - .` there: the descriptor's
address minus the word's, modulo `2 ^ 64`. The descriptor's address is the loader's, from the text's
`.rodata` items at the executable's layout (the bytes `rodataOk` checks), and the executable's own
`scc_gc_desc` symbol must agree with it. The loader's cell of a word is empty (the runtime's read of it is
outside the model), so these bytes are checked here. A `.text` under one granule has no word (an output
without the granule pass); `.text` must end at the text's `scc_text_end` (`textEndOk`), so a post-pass
`.text` cannot be cut below a granule to skip its words. Untrusted until `Scc/Test/certify.sh` imports it.
Tests: `Scc/Test/ElfBytesTest.lean` (fixture `x`) and `Spike/Test/ElfBytesTest{X64,A64}.lean` (hello and
wake on both ISAs).
-/

namespace Scc.Cert.ElfBytes

open Scc.Sem Scc.Cert.Elf

/-- The code granule (64 KB, the ABI constant of the table discovery). -/
def granule : Nat := 65536

/-- **The `.rodata` image the loaders lay out** from the items, code labels through `code`: `rodataWords`
before `DataImage.words` (`rodataWords_eq`). -/
def rodataImage (Λ : Layout) (items : List Kraken.DataImage.Item) (code : String → Option Nat) : List UInt8 :=
  Kraken.DataImage.image
    (Kraken.DataImage.resolve (fun l => BitVec.ofNat 64 ((code l).getD 0)) Λ.rodata.lo items)
    Λ.rodata.lo items

/-- The words the loaders place are `rodataImage`'s: the check compares the loader's view. -/
theorem rodataWords_eq (Λ : Layout) (items : List Kraken.DataImage.Item) (code : String → Option Nat) :
    rodataWords Λ items code = Kraken.DataImage.words Λ.rodata.lo (rodataImage Λ items code) := rfl

/-- The whole `.rodata` section of `b` is `rodataImage`, then zeros, the image's last word inside it. -/
def rodataOk (b : ByteArray) (Λ : Layout) (items : List Kraken.DataImage.Item)
    (code : String → Option Nat) : Except String Unit := do
  let secs ← sections b (← header b)
  let got ← match ← secNamed? secs ".rodata" with
    | none => pure ByteArray.empty
    | some (_, s) => s.bytes b
  let img := (rodataImage Λ items code).toArray
  let need := (img.size + 7) / 8 * 8
  unless need ≤ got.size do
    throw s!".rodata: {got.size} bytes, the text's image needs {need}"
  match (List.range got.size).find? fun i => got.get! i ≠ img.getD i 0 with
  | some i => throw s!".rodata byte {i} (address {Λ.rodata.lo + i}): file {got.get! i}, text {img.getD i 0}"
  | none => pure ()

/-- The collector's descriptor (`Scc.Cert.Maps.descSym`; restated here so that the check does not import the
tables' modules, and pinned equal to it by `Spike/Test/ElfBytesTestX64.lean`). -/
def descSym : String := "scc_gc_desc"

/-- The address of the word of granule `k` of a text at `lo`: its last 8 bytes. -/
def wordAddr (lo k : Nat) : Nat := lo + (k + 1) * granule - 8

/-- The word `.quad scc_gc_desc - .` at address `w`, the descriptor at `d`: `d - w` modulo `2 ^ 64`. -/
def wordVal (d w : Nat) : Nat := (BitVec.ofInt 64 ((d : Int) - w)).toNat

/-- The words of the granules `k < n` of `text` (the `.text` bytes, at `lo`) that are not `wordVal d`:
each with its granule, address and file value (`none` past the bytes). -/
def badWords (text : ByteArray) (lo d n : Nat) : List (Nat × Nat × Option Nat) :=
  (List.range n).filterMap fun k =>
    let w := wordAddr lo k
    let v := (u64 text (w - lo)).toOption
    if v == some (wordVal d w) then none else some (k, w, v)

/-- **The granule words of `b`** at its layout `Λ`, the descriptor laid out from the text's `.rodata` items:
none under one granule; else whole granules on a granule boundary, the executable's `scc_gc_desc` at the
items' descriptor, and every granule's last word `wordVal` of it (`badWords_nil`). -/
def granuleWordsOk (b : ByteArray) (Λ : Layout) (items : List Kraken.DataImage.Item) : Except String Unit := do
  let n := Λ.code.size / granule
  if n = 0 then return
  unless Λ.code.lo % granule = 0 ∧ Λ.code.size % granule = 0 do
    throw s!".text is {Λ.code.size} bytes at {Λ.code.lo}: not whole granules on a granule boundary"
  let some d := Kraken.DataImage.dataLabel Λ.rodata.lo items descSym
    | throw s!"no {descSym} in the text's .rodata: the granule words have no descriptor"
  let secs ← sections b (← header b)
  match (← symTable b secs).find? (·.name == descSym) with
  | none => throw s!"no {descSym} symbol in the executable"
  | some s => unless s.value = d do throw s!"{descSym}: symbol at {s.value}, the text's at {d}"
  let (_, t) ← secNamed secs ".text"
  match badWords (← t.bytes b) Λ.code.lo d n with
  | [] => pure ()
  | (k, w, v) :: _ =>
    throw s!".text word of granule {k} (address {w}): file {v.map toString |>.getD "none"}, text {wordVal d w}"

/-- What `granuleWordsOk` decides past its refusals: every granule's word is the descriptor's offset. -/
theorem badWords_nil {text : ByteArray} {lo d n : Nat} (h : badWords text lo d n = []) :
    ∀ k < n, (u64 text (wordAddr lo k - lo)).toOption = some (wordVal d (wordAddr lo k)) := by
  intro k hk
  have := List.filterMap_eq_nil_iff.mp h k (List.mem_range.mpr hk)
  simp only at this
  split at this
  · next he => exact beq_iff_eq.mp he
  · cases this

/-- The end-of-text label (`Scc.IR.StackMap.textEndSym`, restated like `descSym`). -/
def textEndSym : String := "scc_text_end"

/-- **`.text` ends at the text's end**: the code label `scc_text_end`, where the caller's `code` lays it out,
is the end of `.text`. Without it a `.text` cut short below a granule (its `sh_size`) would pass with no
granule word checked. A text whose `code` does not resolve the label is refused. -/
def textEndOk (Λ : Layout) (code : String → Option Nat) : Except String Unit :=
  match code textEndSym with
  | some e =>
    unless e = Λ.code.lo + Λ.code.size do
      throw s!".text ends at {Λ.code.lo + Λ.code.size}, the text's {textEndSym} at {e}"
  | none => throw s!"the text has no {textEndSym}: the end of .text cannot be checked"

/-- **The byte check** of the executable `b` against the text's `.rodata` items, code labels through
`code Λ` at the executable's layout `Λ` (`elfLayout`, read here): the granule words (`granuleWordsOk`), the
whole `.rodata` section (`rodataOk`), then the end of `.text` (`textEndOk`). -/
def bytesCheck (b : ByteArray) (items : List Kraken.DataImage.Item)
    (code : Layout → String → Option Nat) : Except String Unit := do
  let Λ ← elfLayout b
  granuleWordsOk b Λ items
  rodataOk b Λ items (code Λ)
  textEndOk Λ (code Λ)

end Scc.Cert.ElfBytes
