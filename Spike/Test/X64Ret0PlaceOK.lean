import Spike.Test.X64Ret0PlaceOKBase
import Spike.Test.X64Ret0PlaceOKA
import Spike.Test.X64Ret0PlaceOKB

/-!
# `PlaceOK` against the hand checks of `ret0.w` on x86-64

One kernel decision of `PlaceOK` (`Scc/Cert/PlaceOKX64.lean`),
`ret0_placeOK`, and each of the hand checks of `Spike/Lib/X64Ret0Code.lean`
re-derived from it by an extraction lemma, at the hand statement: the
components cover the hand facts, and the facts follow without another
decision; and five wrong outputs rejected. `hello1.w`'s twin is
`Spike/Test/X64Hello1PlaceOK.lean` (a module of its own: one per program
keeps each file's memory under the per-process budget). The x64 twin of
`Spike/Test/A64Ret0PlaceOK.lean`.

The block table of the placement data is the hand table `ret0T` with the
static offsets the analyser gives its blocks (`ret0Offs`,
`Spike/Test/X64Ret0Offs.lean`), zipped by `ofGrps`, and each group's cells
in no block (`ret0Evs`, `withEvs`); the table is the hand one again by
`toGrps_withEvs` and `toGrps_ofGrps`.

The module is split for memory (each part under the per-process budget):
`Spike/Test/X64Ret0PlaceOKBase.lean` (`ret0Place`, `ret0_placeOK` decided one
component per declaration, `ret0LΛ`, `ret0_limInitOk`, `breakAtB`), `Spike/Test/X64Ret0PlaceOKA.lean` (the hand
checks re-derived, including the `block_spec` coverage checks) and
`Spike/Test/X64Ret0PlaceOKB.lean` (wrong outputs rejected; the A1, A6, A8 and
A11 facts); this module imports them all.
-/
