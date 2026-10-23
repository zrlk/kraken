import Scc.Cert.LinkImage
import Scc.Cert.Rt.LayoutA64
import Scc.Sem.LoadA64

/-!
# The static link of an emitted AArch64 text

What `scc --code` needs to state the layout of an AArch64 listing and check
it in the kernel, besides `Scc.Cert.Link`:

- the elaborator `scc_arm_text%` (with `scc_data_secs%`,
  `Scc/Cert/LinkImage.lean`), which run the
  canonical loader's parsers (`Scc.Sem.A64.textProgram`,
  `Scc.Sem.dataSections`) on a listing at elaboration time and return the
  parsed program and data sections as literals. The kernel cannot evaluate
  the parsers (string processing, `partial` parser combinators), so the two
  parse equations are the trust boundary, as for `scc_arm_reparse%`; a
  generated file also checks them by `#guard`;
- `linkOf prog secs`: the static link at `Link.canonical`, its `.quad`
  labels the program's code labels;
- `abortsIn prog Λ`: each abort label of `Λ` is a code label of `prog`;
- `imageIn prog secs Λ`: the image holds each data symbol's item
  (`Scc.Cert.Link.imageOk`; `image_symbols`, `image_word`, `image_sub`,
  `image_disj`);
- `loadOk Λ prog secs`: the canonical loader's checks of `Λ` against the
  parsed text (`Scc.Sem.A64.target`'s `load` but the entry state's
  `Entry.clear`), and its thread's cells a valid layout
  (`validLayout_of_loadOk`, by `Scc.Cert.Rt.A64.validLayout_threadAt`);
  with the entry state's check, the canonical load of the parsed text is
  the loaded configuration (`loadParsed_of_loadOk`), and with the parse
  equations the canonical target's load of the listing is
  (`load_of_loadOk`).
-/

namespace Scc.Cert.Link.A64

open Scc.Sem Scc.Sem.A64 Kraken.Promising.AArch64

open Lean Elab Term Meta in
/-- `scc_arm_text% c`, `c` a string constant: the canonical loader's program
of its value (`textProgram`: Kraken's AArch64 parser on the `.text`
sections), at elaboration time, as a literal. -/
elab "scc_arm_text% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let text ← unsafe evalConst String n
  match textProgram text with
  | .ok p => return toExpr p
  | .error msg => throwError "Kraken's AArch64 parser rejects the text: {msg}"

/-- **The loader's parse of `asm`** is `prog` and `secs` (`textProgram`,
`dataSections`): the trust boundary of a generated file, checked there by
evaluation (`#guard`). -/
def parsesTo (asm : String) (prog : Program) (secs : DataSecs) : Bool :=
  (match textProgram asm with
   | .ok p => decide (p = prog)
   | .error _ => false) && decide (dataSections asm = some secs)

/-- The parse equations from `parsesTo`. -/
theorem parsed_of_parsesTo {asm : String} {prog : Program} {secs : DataSecs}
    (h : parsesTo asm prog secs = true) : textProgram asm = .ok prog ∧ dataSections asm = some secs := by
  simp only [parsesTo, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  have h1 := h.1
  split at h1
  · next p hp => rw [hp, of_decide_eq_true h1]
  · cases h1

/-- A code label's address in `prog` at the code base `lo`, as the
canonical target resolves it. -/
def codeOf (lo : Nat) (prog : Program) (l : String) : Option Nat :=
  labelAddr labelName Directive.fakeSize lo l prog

/-- **The static link of a parsed text** at `Link.canonical`. -/
def linkOf (prog : Program) (secs : DataSecs) : Scc.Sem.Layout :=
  link canonical secs (codeOf canonical.codeLo prog)

/-- Each abort label of `Λ` is a code label of `prog`. -/
def abortsIn (prog : Program) (Λ : Scc.Sem.Layout) : Bool :=
  kinds.all fun k => (codeOf Λ.code.lo prog (Λ.abortLbl k)).isSome

/-- The image of `Λ` holds each data symbol's item (`imageOk`), `.quad`
labels resolved in `prog`. -/
def imageIn (prog : Program) (secs : DataSecs) (Λ : Scc.Sem.Layout) : Bool :=
  imageOk Λ secs (codeOf Λ.code.lo prog)

/-- **The canonical loader's checks** of `Λ` against the parsed text, but
the entry state's (`Scc.Sem.A64.target`): the `.rodata` image fits,
`Λ.symbols` agrees with it, every `.quad` label resolves, every data symbol
is above the code; and the loaded thread's cells are a valid layout. -/
def loadOk (Λ : Scc.Sem.Layout) (prog : Program) (secs : DataSecs) : Bool :=
  let ro := secs.rodata
  let code (l : String) : Option Nat := (codeOf Λ.code.lo prog l).orElse fun _ => Λ.symbols.lookup l
  let syms := loadSyms Λ ro
  rodataFits Λ ro && symsAgree Λ ro && quadsResolve Λ ro code &&
    symsAbove Λ.code.lo (codeEnd Λ.code.lo prog) syms &&
    prog.all (fun d => Kraken.Executable.cellOk (d, d.fakeSize)) && Rt.A64.symsOk Λ.code.lo prog syms

/-- **The loaded thread's layout is valid** when the checks pass. -/
theorem validLayout_of_loadOk {Λ : Scc.Sem.Layout} {prog : Program} {secs : DataSecs}
    (h : loadOk Λ prog secs = true) (E : Entry) :
    Kraken.Executable.ValidLayout (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)).exe := by
  simp only [loadOk, Bool.and_eq_true] at h
  exact Rt.A64.validLayout_threadAt h.1.2 h.2

/-- **No data symbol below the code** when the checks pass (`symsOk`): the
premise of `Rt.A64.lays_threadAt`, `Rt.A64.endPc_threadAt` and
`Rt.A64.label_threadAt_of_codeOf`. -/
theorem above_of_loadOk {Λ : Scc.Sem.Layout} {prog : Program} {secs : DataSecs}
    (h : loadOk Λ prog secs = true) : ∀ p ∈ loadSyms Λ secs.rodata, Λ.code.lo ≤ p.2 := by
  simp only [loadOk, Bool.and_eq_true] at h
  exact Rt.A64.above_of_symsOk h.2

/-- The code labels the canonical loader resolves the `.rodata` quads
with: `prog`'s, else `Λ`'s symbols. -/
def quadCode (Λ : Scc.Sem.Layout) (prog : Program) (l : String) : Option Nat :=
  (codeOf Λ.code.lo prog l).orElse fun _ => Λ.symbols.lookup l

/-- **The canonical load of the parsed text** when the loader's checks pass
(`loadOk`) and the entry state's (`Entry.clear`): the program's thread with
the data symbols `loadSyms` and the image and `.rodata` words as initial
memory. -/
theorem loadParsed_of_loadOk {H : Scc.Sem.Hooks isaLSE2} {E : Entry}
    {Λ : Scc.Sem.Layout} {prog : Program} {secs : DataSecs}
    (h : loadOk Λ prog secs = true) (hE : E.clear Λ = true) :
    loadParsed H E Λ prog secs = some (loadProg H E Λ prog (loadSyms Λ secs.rodata)
      (imageMem Λ ++ wordsMem (rodataWords Λ secs.rodata (quadCode Λ prog)))) := by
  simp only [loadOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
  simp only [codeOf] at h3
  unfold loadParsed
  simp only [h1, h2, h3, h4, hE, Bool.and_self, ↓reduceIte]
  rfl

/-- **The canonical target's load of the listing `asm`**, from the
loader's parse of it (`parsesTo`) and the checks (`loadOk`, `Entry.clear`). -/
theorem load_of_loadOk {H : Scc.Sem.Hooks isaLSE2} {E : Entry}
    {Λ : Scc.Sem.Layout} {asm : String} {prog : Program} {secs : DataSecs}
    (hp : parsesTo asm prog secs = true) (h : loadOk Λ prog secs = true)
    (hE : E.clear Λ = true) :
    (target H E).load asm Λ = some (loadProg H E Λ prog (loadSyms Λ secs.rodata)
      (imageMem Λ ++ wordsMem (rodataWords Λ secs.rodata (quadCode Λ prog)))) := by
  obtain ⟨h1, h2⟩ := parsed_of_parsesTo hp
  rw [load_of_parsed H E Λ h1 h2, loadParsed_of_loadOk h hE]

end Scc.Cert.Link.A64
