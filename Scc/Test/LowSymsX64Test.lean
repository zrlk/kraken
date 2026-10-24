import Scc.Cert.LinkX64
import Scc.Cert.Rt.RtWordsX64
import Scc.Cert.Rt.PhasesX64

/-!
# Data symbols below the code on x86-64: the two-sided placement

The x86-64 twin of `Scc/Test/LowSymsA64Test.lean`'s two-sided part. The canonical
target places data symbols below the code before it (`Scc.Sem.placeBelow`,
`TargetX64.lean`'s `threadAt`); the layout lemmas take that prefix
(`Link.X64.lays_threadAt_below`, `endPc_threadAt_below`,
`validLayout_threadAt_below`) and the two-sided check `Link.X64.symsAround`
admits each symbol below the start of the code or at or above its end.
The certification pipeline's loader check (`Link.X64.loadOk`, the
placement check's A2) accepts a symbol below the code: the data
symbols placed around the code (`symsAround`), with no name clash
(`Link.X64.noClash`). Checked by evaluation and, on a literal program, by
the kernel.
-/

namespace Scc.Test.LowSymsX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert

/-- A literal 4-byte program of sized cells: a label, then 4 bytes. -/
private def lit : List (Directive × Nat) := [(.label "f", 0), (.byteArray (.mk #[0, 0, 0, 0]), 4)]

-- The two-sided check: a symbol below the start of the code `[48, 52)` or at
-- or above its end is placed, the boundary `52` included; one inside the code
-- is refused. Two symbols may share an address.
#guard Link.X64.symsAround 48 lit [("a", 16), ("b", 56)] &&
  Link.X64.symsAround 48 lit [("e", 52)] && Link.X64.symsAround 48 lit [("a", 47)] &&
  Link.X64.symsAround 48 lit [("a", 16), ("a2", 16), ("b", 56), ("b2", 56)] &&
  !Link.X64.symsAround 48 lit [("in", 48)] && !Link.X64.symsAround 48 lit [("in", 51)] &&
  !Link.X64.symsAround 48 lit [("a", 16), ("in", 50)]

-- The old one-sided check refuses a symbol below the code and one at its end.
#guard Link.X64.symsOk 48 lit [("b", 56)] &&
  !Link.X64.symsOk 48 lit [("a", 16)] && !Link.X64.symsOk 48 lit [("e", 52)]

/-- `trivLayout` with its data region below the code. -/
private def Λdl : Scc.Sem.Layout :=
  { trivLayout with code := ⟨48, 16⟩, data := ⟨16, 16⟩ }

/-- `Λdl` with a `.rodata` region above everything else. -/
private def Λro : Scc.Sem.Layout := { Λdl with rodata := ⟨128, 16⟩ }

/-- A literal 4-byte program without labels. -/
private def nop : List (Directive × Nat) := [(.byteArray (.mk #[0, 0, 0, 0]), 4)]

-- `Link.X64.loadOk` (A2) no longer uses `symsOk`: it accepts the layout
-- with a symbol below the code as well as one above it.
#guard Link.X64.loadOk { Λdl with symbols := [("hi", 56)] } nop {} [] &&
  Link.X64.loadOk { Λdl with symbols := [("lo", 16)] } nop {} [] &&
  Link.X64.loadOk { Λdl with symbols := [("lo", 16), ("hi", 56)] } nop {} []

-- `loadOk`'s negative cases. `symsAround`: a symbol inside the code.
-- `noClash`, first half: a symbol below the code named like a code label
-- (its label cell would come first and shadow the code label); above the
-- code the same name is fine (the code's label cell comes first).
-- `noClash`, second half: a name placed twice, below and above the code, or
-- twice among the `.rodata` labels.
#guard Link.X64.loadOk { Λdl with symbols := [("g", 16)] } lit {} [("f", 0)] &&
  !Link.X64.loadOk { Λdl with symbols := [("in", 48)] } nop {} [] &&
  !Link.X64.loadOk { Λdl with symbols := [("f", 16)] } lit {} [("f", 0)] &&
  Link.X64.symsAround 48 lit [("f", 56)] &&
  !Link.X64.loadOk { Λdl with symbols := [("x", 16), ("x", 56)] } nop {} [] &&
  Link.X64.loadOk Λro nop { rodata := [.label "x", .quad 0] } [] &&
  !Link.X64.loadOk Λro nop { rodata := [.label "x", .quad 0, .label "x", .quad 1] } []

-- With a symbol below the code, the loader's checks give the code label at
-- its `codeLabel` address (`Rt.X64.label_of_loadOk`, kernel-checked).
example : (_root_.Executable.labels (threadAt Entry.linux 48 lit
      (loadSyms { Λdl with symbols := [("lo", 16)] } [])).exe).label "f" = Int64.ofNat 48 :=
  Rt.X64.label_of_loadOk (Λ := { Λdl with symbols := [("lo", 16)] }) (secs := {}) (offs := [("f", 0)])
    (by decide +kernel) (by decide +kernel)

-- A `.data` symbol named like a `.rodata` label is not placed twice: the
-- loader drops it from `loadSyms`, and `symsAgree` asks it be at the
-- label's address.
#guard loadSyms { Λro with symbols := [("x", 128)] } [.label "x", .quad 0] == [("x", 128)] &&
  Link.X64.loadOk { Λro with symbols := [("x", 128)] } nop { rodata := [.label "x", .quad 0] } [] &&
  !Link.X64.loadOk { Λro with symbols := [("x", 16)] } nop { rodata := [.label "x", .quad 0] } []

-- The executable then starts at the lowest symbol, with two cells (padding
-- and a label) before the code.
#guard Link.X64.belowLen 48 [("a", 16), ("b", 56)] == 2 &&
  exeStart 48 [("a", 16), ("b", 56)] == 16 && Link.X64.belowLen 48 [("b", 56)] == 0

/-- Symbols on both sides of `lit` at `48`, one at the end of the code. -/
private def symsLH : List (String × Nat) := [("lo", 16), ("lo2", 40), ("e", 52), ("hi", 64)]

-- The loaded thread lays out `lit` after the cells below the code, halts at
-- its end, has a valid layout, and labels each symbol at its address, the
-- code label too.
example : Rt.X64.Lays (threadAt Entry.linux 48 lit symsLH).exe lit (Link.X64.belowLen 48 symsLH) :=
  Link.X64.lays_threadAt_below _ _ _ _ (by decide +kernel)
example : (threadAt Entry.linux 48 lit symsLH).endPc =
    Rt.X64.endOf (threadAt Entry.linux 48 lit symsLH).exe lit (Link.X64.belowLen 48 symsLH) :=
  Link.X64.endPc_threadAt_below _ _ _ _

theorem validLit : Kraken.Executable.ValidLayout (threadAt Entry.linux 48 lit symsLH).exe :=
  Link.X64.validLayout_threadAt_below (offs := []) (by decide +kernel) (by decide +kernel)

example : (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "lo2" = Int64.ofNat 40 :=
  Rt.X64.label_threadAt_of_sym_around (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "e" = Int64.ofNat 52 :=
  Rt.X64.label_threadAt_of_sym_around (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "f" = Int64.ofNat 48 :=
  have := validLit
  Rt.X64.label_threadAt_of_codeLabel_below (by decide +kernel) (by decide +kernel)

-- And by evaluation: the labels of the loaded thread.
#guard ((_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "lo",
    (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "f",
    (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "hi") ==
  (Int64.ofNat 16, Int64.ofNat 48, Int64.ofNat 64)

end Scc.Test.LowSymsX64
