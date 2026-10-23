/-
The canonical x64 loader, split at the parser (the twin of
`Scc/Sem/LoadA64.lean`).

`TargetX64.target H E` parses its text (`cellsOf`: Kraken's x64 parser on
the `.text` sections, laid out at the text's sizes; `dataSections`: the data
sections' lines) and then loads the laid-out cells. The parsing half is
string processing the kernel cannot evaluate (Kraken's parser is
`Std.Internal.Parsec`, with `partial` combinators, and core string
splitting does not reduce by `decide +kernel`). The loading half
(`loadParsed`) is list and number computation over the cells and data
sections, which does.

So a closed certificate for a concrete text takes the parse as its trust
boundary: the two equations `cellsOf a = some cells` and
`dataSections a.text = some secs`, for literal `cells` and `secs`, checked
by evaluation. The rest of the load is `loadParsed`, by `load_of_parsed` /
`resolve_of_parsed`.

- `loadParsed H E Λ cells secs offs`: `target`'s `load` after parsing
  (`offs`: the text's label offsets, `Asm.labelOffs`).
- `load_of_parsed`, `resolve_of_parsed`: `target`'s `load` and `resolve`
  from the parse equations.
- `parsedTarget H E`: the target whose text is the parsed triple
  `(cells, secs, offs)` itself, loaded by `loadParsed`; `correct_of_parsed`:
  `Correct` over it gives `Correct` over `target H E` at a text parsing to
  the triple (the two parse equations are the only link; `offs` is the
  text's `labelOffs` field).
-/
import Scc.Sem.TargetX64

namespace Scc.Sem.X64

open Kraken.Promising Kraken.Promising.X64

/-- **The canonical x64 load of a parsed text**: `target`'s `load` with the
cells `cells`, the data sections `secs` and the label offsets `offs`
already given. -/
def loadParsed (H : Hooks isa) (E : Entry) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat))
    (secs : DataSecs) (offs : List (String × Nat)) : Option (machine H).Cfg :=
  let ro := secs.rodata
  let code (l : String) : Option Nat := (codeLabel Λ.code.lo cells l).orElse fun _ => Λ.symbols.lookup l
  let syms := loadSyms Λ ro
  let fin := codeEnd Λ.code.lo cells
  if SizeCheck (Int64.ofNat Λ.code.lo) cells offs && rodataFits Λ ro &&
      symsAgree Λ ro && quadsResolve Λ ro code && symsAbove Λ.code.lo fin syms && E.clear Λ then
    some (loadProg H E Λ cells syms (imageMem Λ ++ wordsMem (rodataWords Λ ro code)))
  else none

/-- `target`'s load, given the parse of the text: `loadParsed`. -/
theorem load_of_parsed (H : Hooks isa) (E : Entry) (Λ : Scc.Sem.Layout) {a : Asm}
    {cells : List (Directive × Nat)} {secs : DataSecs} (hc : cellsOf a = some cells)
    (hd : dataSections a.text = some secs) :
    (target H E).load a Λ = loadParsed H E Λ cells secs a.labelOffs := by
  simp only [target, hc, hd, loadParsed]
  rfl

/-- `target`'s label resolution, given the parse of the text. -/
theorem resolve_of_parsed (H : Hooks isa) (E : Entry) (Λ : Scc.Sem.Layout) {a : Asm}
    {cells : List (Directive × Nat)} (hc : cellsOf a = some cells) (l : String) :
    (target H E).resolve a Λ l = codeLabel Λ.code.lo cells l := by
  simp only [target, hc, Option.bind_some]

/-- **The canonical x64 target on parsed texts**: the text is the parsed
triple `(cells, secs, offs)` itself, loaded by `loadParsed` and resolved as
`target` resolves after parsing. `target H E` at a text parsing to the
triple loads and resolves alike (`correct_of_parsed`). -/
def parsedTarget (H : Hooks isa) (E : Entry) : Target where
  M := machine H
  Asm := List (Directive × Nat) × DataSecs × List (String × Nat)
  load a Λ := loadParsed H E Λ a.1 a.2.1 a.2.2
  resolve a Λ l := codeLabel Λ.code.lo a.1 l

/-- **`Correct` over the text from `Correct` over its parse**: the two
parse equations are the only link between `target H E` at `a` and
`parsedTarget H E` at `(cells, secs, a.labelOffs)` (`load_of_parsed`,
`resolve_of_parsed`). -/
theorem correct_of_parsed (H : Hooks isa) (E : Entry) {S : SrcSem} {Λ : Scc.Sem.Layout} {B : Budget}
    {a : Asm} {cells : List (Directive × Nat)} {secs : DataSecs} (hc : cellsOf a = some cells)
    (hd : dataSections a.text = some secs) (h : Correct (parsedTarget H E) S Λ B (cells, secs, a.labelOffs)) :
    Correct (target H E) S Λ B a := by
  obtain ⟨w⟩ := h
  have hl : (target H E).load a Λ = (parsedTarget H E).load (cells, secs, a.labelOffs) Λ :=
    load_of_parsed H E Λ hc hd
  have hm : (target H E).marks a Λ = (parsedTarget H E).marks (cells, secs, a.labelOffs) Λ := by
    unfold Target.marks
    simp only [resolve_of_parsed H E Λ hc]
    rfl
  exact ⟨{
    R := w.R
    layout := w.layout
    start := hl ▸ w.start
    progress := hl ▸ hm ▸ w.progress
    sim := hl ▸ hm ▸ w.sim
    abort := hl ▸ hm ▸ w.abort
    explicit := w.explicit }⟩

end Scc.Sem.X64
