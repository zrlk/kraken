import Scc.Cert.MapsA64
import Scc.Cert.MapsPart

/-!
# A function's rebased slice of an AArch64 text (untrusted)

The AArch64 front end of `Scc.Cert.MapsPart`: function `i` of the IR `p`, its slice of the text
`its` (`slicesByLabel`: from its entry label to the next routine's), the slice's items, its tags
(`tagsOf`, with the argument areas `areas`, `Scc.Emit.A64.emitPre`'s, and the emitter's
safepoints `ms` whose labels are in the slice), all rebased to the entry label's address.
-/

namespace Scc.Cert.MapsA64
open Maps

/-- **Function `i`'s rebased slice** (see the module docstring): entry address, items, tags. An
error if `p` has no function `i`, or it has no single slice. -/
def sliceFn (p : IR.Program) (areas : List (IR.Sym × Nat)) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) (i : Nat) :
    Except String (Nat × List Item × FnTags) := do
  let some f := p.funcs[i]? | throw s!"sliceFn: no function {i}"
  let s ← match (slicesByLabel (entryLabels p) [f.name] its).filter (·.name == f.name) with
    | [s] => pure s
    | _ => throw s!"sliceFn: no single slice of {f.name}"
  let (items, _) ← itemsExitsFrom s.start s.its
  let tbl : List (Nat × List Int × List Int) :=
    ms.filterMap fun ((l, st, hp) : String × List Int × List Int) =>
      (labelAddr items l).map (·, st, hp)
  let ft ← tagsOf p areas items tbl (f, i)
  let some e := labelAddr items f.name | throw s!"sliceFn: no entry label {f.name}"
  pure (e, rebaseI e items, rebaseFT e ft)

end Scc.Cert.MapsA64
