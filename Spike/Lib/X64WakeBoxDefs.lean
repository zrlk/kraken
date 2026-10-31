/-
**wake.w's box publication, ISA-free** (for `Spike.Lib.X64WakeWcPub`):
main's term past the box's `new` and the control past its publication,
restated from `Spike.Lib.A64.Flow.WakeWc.boxTerm` (`A64WakeWcRes`) and
`Spike.Lib.A64.Flow.WakeWc.boxPubCtl` (`WakePubFence`), whose modules reach
`Kraken.AArch64.Syntax` (which cannot be imported next to
`Kraken.X64.Syntax`). This module imports neither ISA;
`Spike/Test/WakeBoxDefsEq.lean` (A64 side only) checks both against the
originals by `rfl`.

- `boxTerm`: `let c = publish o in let p = pair c me in spawnTerm`;
- `boxPubCtl`: the source past the publication, `c` the box's published
  locative;
- `boxPubSy`: the publication step at `boxTerm` under a full fence
  (`PubStep .sy`, x86-64's `mfence`).
-/
import Spike.Lib.Seg
import Spike.Lib.X64WakeSrcDefs

namespace Spike.Lib.X64WakeBoxDefs

open CoreLang CoreTerm
open Spike.Lib

/-- **main's term past the box's `new`** (wake.w's `main` after `z`, `o`):
`let c = publish o in let p = pair c me in spawnTerm`. -/
def boxTerm : CoreTerm.Expr :=
  .let_ "c" (.publish (.var "o")) (.let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.X64WakeSrcDefs.spawnTerm)

/-- The source past the publication at `boxTerm`: `let p = pair c me in
spawnTerm`, `c` bound to the box's published locative. -/
def boxPubCtl (c : Ctl) (ty : Ty) (l : WeakMem.AllocLabel) : Ctl :=
  ⟨.let_ "p" (.pair (.var "c") (.var "me")) Spike.Lib.X64WakeSrcDefs.spawnTerm,
    ("c", .ptr .pub ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩

/-- **The publication step at `boxTerm` under a full fence** (`PubStep
.sy`): `o` bound to the box's owned locative, no hold. -/
theorem boxPubSy {c : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} (ht : c.term = boxTerm) (hh : c.hold = none)
    (ho : TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])) :
    PubStep .sy c (boxPubCtl c ty l) :=
  ⟨.inr rfl, hh, "c", .var "o", _, .ptr .own ty, .ptr .pub ty, _, .inl ⟨ht, rfl⟩, ho, rfl⟩

end Spike.Lib.X64WakeBoxDefs

/-- info: 'Spike.Lib.X64WakeBoxDefs.boxPubSy' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeBoxDefs.boxPubSy
