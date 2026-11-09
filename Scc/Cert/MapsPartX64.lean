import Scc.Cert.MapsX64
import Scc.Cert.MapsPart

/-!
# A function's rebased slice of an x64 text (untrusted)

The x64 front end of `Scc.Cert.MapsPart`: function `i` of the IR `p`, its slice of the text
`its` (`slicesByLabel`: from its entry label to the next routine's, with the instruction sizes
`sizes`), the slice's items, its tags (`tagsOf`, with the emitter's safepoints `ms` whose labels
are in the slice), all rebased to the entry label's address.
-/

namespace Scc.Cert.MapsX64
open Maps

/-- **Function `i`'s rebased slice** (see the module docstring): entry address, items, tags. An
error if `p` has no function `i`, or it has no single slice. -/
def sliceFn (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) (sizes : List Nat) (i : Nat) :
    Except String (Nat × List Item × FnTags) := do
  let some f := p.funcs[i]? | throw s!"sliceFn: no function {i}"
  let s ← match (slicesByLabel (entryLabels p) [f.name] its sizes).filter (·.name == f.name) with
    | [s] => pure s
    | _ => throw s!"sliceFn: no single slice of {f.name}"
  let (items, _) ← itemsExitsFrom s.start s.its s.sizes
  let tbl : List (Nat × List Int × List Int) :=
    ms.filterMap fun ((l, st, hp) : String × List Int × List Int) =>
      (labelAddr items l).map (·, st, hp)
  let ft ← tagsOf p items tbl f
  let some e := labelAddr items f.name | throw s!"sliceFn: no entry label {f.name}"
  pure (e, rebaseI e items, rebaseFT e ft)

end Scc.Cert.MapsX64
