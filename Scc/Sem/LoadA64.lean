/-
The canonical AArch64 loader, split at the parser.

`TargetA64.target H E` parses its text (`textProgram`: Kraken's AArch64
parser on the `.text` sections; `dataSections`: the data sections' lines)
and then loads the parsed program. The parsing half is string processing
the kernel cannot evaluate: Kraken's parser is `Std.Internal.Parsec`
(`manyCore` and the parser's `parseConstExpr` are `partial`), and core
`String.splitOn`/`trimAscii` do not reduce by `decide +kernel`. The loading
half (`loadParsed`) is list and number computation over the parsed program
and data sections, which does.

So a closed certificate for a concrete text takes the parse as its trust
boundary: the two equations `textProgram asm = .ok prog` and
`dataSections asm = some secs`, for literal `prog` and `secs`, checked by
evaluation (`#guard`). The rest of the load is `loadParsed`, by
`load_of_parsed` / `resolve_of_parsed`. This is the trust the compiler's
`scc_arm_reparse%` already places in the parser, which re-reads the emitted
listing by `evalConst`.

- `loadParsed H E Λ prog secs`: `target`'s `load` after parsing.
- `load_of_parsed`, `resolve_of_parsed`: `target`'s `load` and `resolve`
  from the two parse equations.
- `parsedTarget H E`: the target whose text is the parsed pair
  `(prog, secs)` itself, loaded by `loadParsed`; `correct_of_parsed`:
  `Correct` over it gives `Correct` over `target H E` at a text parsing to
  the pair (the two parse equations are the only link).
-/
import Scc.Sem.TargetA64

namespace Scc.Sem.A64

open Kraken.Promising Kraken.Promising.AArch64

/-- **The canonical AArch64 load of a parsed text**: `target`'s `load` with
the program `prog` and the data sections `secs` already parsed. -/
def loadParsed (H : Hooks isaLSE2) (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program)
    (secs : DataSecs) : Option (machine H).Cfg :=
  let ro := secs.rodata
  let code (l : String) : Option Nat :=
    (labelAddr labelName Directive.fakeSize Λ.code.lo l prog).orElse fun _ => Λ.symbols.lookup l
  let syms := loadSyms Λ ro
  let fin := codeEnd Λ.code.lo prog
  if rodataFits Λ ro && symsAgree Λ ro && quadsResolve Λ ro code &&
      symsAbove Λ.code.lo fin syms && E.clear Λ then
    some (loadProg H E Λ prog syms (imageMem Λ ++ wordsMem (rodataWords Λ ro code)))
  else none

/-- `target`'s load, given the parse of the text: `loadParsed`. -/
theorem load_of_parsed (H : Hooks isaLSE2) (E : Entry) (Λ : Scc.Sem.Layout) {asm : String}
    {prog : Program} {secs : DataSecs} (hp : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) :
    (target H E).load asm Λ = loadParsed H E Λ prog secs := by
  simp only [target, hp, hd, Except.toOption, loadParsed]
  rfl

/-- `target`'s label resolution, given the parse of the program text. -/
theorem resolve_of_parsed (H : Hooks isaLSE2) (E : Entry) (Λ : Scc.Sem.Layout) {asm : String}
    {prog : Program} (hp : textProgram asm = .ok prog) (l : String) :
    (target H E).resolve asm Λ l = labelAddr labelName Directive.fakeSize Λ.code.lo l prog := by
  simp only [target, hp]

/-- **The canonical AArch64 target on parsed texts**: the text is the
parsed pair `(prog, secs)` itself, loaded by `loadParsed` and resolved as
`target` resolves after parsing. `target H E` at a text parsing to the pair
loads and resolves alike (`correct_of_parsed`). -/
def parsedTarget (H : Hooks isaLSE2) (E : Entry) : Target where
  M := machine H
  Asm := Program × DataSecs
  load a Λ := loadParsed H E Λ a.1 a.2
  resolve a Λ l := labelAddr labelName Directive.fakeSize Λ.code.lo l a.1

/-- **`Correct` over the text from `Correct` over its parse**: the two
parse equations are the only link between `target H E` at `asm` and
`parsedTarget H E` at `(prog, secs)` (`load_of_parsed`,
`resolve_of_parsed`). -/
theorem correct_of_parsed (H : Hooks isaLSE2) (E : Entry) {S : SrcSem} {Λ : Scc.Sem.Layout} {B : Budget}
    {asm : String} {prog : Program} {secs : DataSecs} (hp : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (h : Correct (parsedTarget H E) S Λ B (prog, secs)) :
    Correct (target H E) S Λ B asm := by
  obtain ⟨w⟩ := h
  have hl : (target H E).load asm Λ = (parsedTarget H E).load (prog, secs) Λ := load_of_parsed H E Λ hp hd
  have hm : (target H E).marks asm Λ = (parsedTarget H E).marks (prog, secs) Λ := by
    unfold Target.marks
    simp only [resolve_of_parsed H E Λ hp]
    rfl
  exact ⟨{
    R := w.R
    layout := w.layout
    start := hl ▸ w.start
    progress := hl ▸ hm ▸ w.progress
    sim := hl ▸ hm ▸ w.sim
    abort := hl ▸ hm ▸ w.abort
    explicit := w.explicit }⟩

end Scc.Sem.A64
