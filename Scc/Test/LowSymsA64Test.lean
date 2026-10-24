import Scc.Cert.Link
import Scc.Cert.LinkA64
import Scc.Cert.Rt.RtWordsA64
import Scc.Cert.Rt.PhasesA64

/-!
# Data symbols below the code: what the link and the loader accept

The loader lets a data symbol lie below the code (default `lld` puts `.rodata`
before `.text`): `Layout.WF` (`Link.wfB`) asks of each symbol only that it
is in a data region and not inside the code, and the canonical target
places it before the code (`Scc.Sem.placeBelow`, `TargetA64.lean`'s
`cellsAround`). The certification pipeline's loader check (`Link.A64.loadOk`,
the placement check's A2) accepts one too: the data symbols
placed around the code (`Rt.A64.symsAround`), with no name clash
(`Link.A64.noClash`). Checked by evaluation.
-/

namespace Scc.Test.LowSymsA64

open Scc.Sem Scc.Sem.A64 Scc.Cert

/-- `trivLayout` with its data region below the code. -/
private def Λdl : Scc.Sem.Layout :=
  { trivLayout with code := ⟨48, 16⟩, data := ⟨16, 16⟩ }

-- A symbol below the code in the data region is well formed; one below the
-- code in no region is not, nor is one inside the code.
#guard Link.wfB { Λdl with symbols := [("lo", 16)] } &&
  !Link.wfB { trivLayout with symbols := [("lo", 8)] } &&
  !Link.wfB { trivLayout with symbols := [("in", 20)] } &&
  !Link.wfB { Λdl with symbols := [("in", 48)] }

-- The target's check: no symbol inside the code `[48, 52)`; below it or at
-- its end is fine.
#guard symsAbove 48 52 [("a", 16), ("b", 52)] &&
  !symsAbove 48 52 [("a", 48)] && !symsAbove 48 52 [("a", 51)]

private def nop : Program :=
  match textProgram "nop" with
  | .ok p => p
  | .error _ => []

-- The loader check of the pipeline places only symbols above the code
-- (`Rt.A64.symsOk`): a symbol below it, or at its end (an empty padding
-- cell before `padTo`), is refused; one past the end is accepted.
#guard Rt.A64.symsOk 48 nop [("b", 56)] &&
  !Rt.A64.symsOk 48 nop [("a", 16)] && !Rt.A64.symsOk 48 nop [("e", 52)] &&
  !Rt.A64.symsOk 48 nop [("a", 16), ("b", 56)]

-- `Link.A64.loadOk` (A2) no longer uses `symsOk`: it accepts the layout
-- with a symbol below the code as well as one above it.
#guard Link.A64.loadOk { Λdl with symbols := [("hi", 56)] } nop {} &&
  Link.A64.loadOk { Λdl with symbols := [("lo", 16)] } nop {} &&
  Link.A64.loadOk { Λdl with symbols := [("lo", 16), ("hi", 56)] } nop {}

-- The two-sided check (`Rt.A64.symsAround`): a symbol below the start of
-- the code `[48, 52)` or at or above its end is placed, the boundary `52`
-- included; one inside the code is refused. Two symbols may share an
-- address (`padTo` adds no empty padding).
#guard Rt.A64.symsAround 48 nop [("a", 16), ("b", 56)] &&
  Rt.A64.symsAround 48 nop [("e", 52)] && Rt.A64.symsAround 48 nop [("a", 47)] &&
  Rt.A64.symsAround 48 nop [("a", 16), ("a2", 16), ("b", 56), ("b2", 56)] &&
  !Rt.A64.symsAround 48 nop [("in", 48)] && !Rt.A64.symsAround 48 nop [("in", 51)] &&
  !Rt.A64.symsAround 48 nop [("a", 16), ("in", 50)]

/-- A program with the code label `f`. -/
private def withF : Program :=
  match textProgram "f:\n  nop" with
  | .ok p => p
  | .error _ => []

/-- `Λdl` with a `.rodata` region above everything else. -/
private def Λro : Scc.Sem.Layout := { Λdl with rodata := ⟨128, 16⟩ }

-- `loadOk`'s negative cases. `symsAround`: a symbol inside the code.
-- `noClash`, first half: a symbol below the code named like a code label
-- (its label cell would come first and shadow the code label); above the
-- code the same name is fine: the code label wins both where the loaded
-- thread resolves labels (`threadAt`'s cells: the code's label cell comes
-- before the symbol's, and `labels` takes the first) and where the image's
-- `.quad`s do (the loaders' `code`, `codeOf … |>.orElse` `Λ.symbols`:
-- `LoadA64.lean`, `TargetA64.lean`).
-- `noClash`, second half: a name placed twice, below and above the code, or
-- twice among the `.rodata` labels.
#guard Link.A64.loadOk { Λdl with symbols := [("g", 16)] } withF {} &&
  !Link.A64.loadOk { Λdl with symbols := [("in", 48)] } nop {} &&
  !Link.A64.loadOk { Λdl with symbols := [("f", 16)] } withF {} &&
  Rt.A64.symsAround 48 withF [("f", 56)] &&
  !Link.A64.loadOk { Λdl with symbols := [("x", 16), ("x", 56)] } nop {} &&
  Link.A64.loadOk Λro nop { rodata := [.label "x", .quad 0] } &&
  !Link.A64.loadOk Λro nop { rodata := [.label "x", .quad 0, .label "x", .quad 1] }

-- `noClash` directly: each half on its own.
#guard Link.A64.noClash 48 withF [("g", 16), ("f", 56)] &&
  !Link.A64.noClash 48 withF [("f", 16)] &&
  !Link.A64.noClash 48 withF [("x", 16), ("x", 16)] &&
  !Link.A64.noClash 48 withF [("x", 56), ("x", 64)] &&
  Link.A64.noClash 48 nop [("f", 16)]

-- The code's end in the address space (`loadOk`'s last conjunct): a code
-- ending at `2 ^ 64` is refused, one ending a byte before it accepted.
-- (`symsAround` alone does not bound it: no symbol here lies above it.)
#guard codeEnd (2 ^ 64 - 4) nop == 2 ^ 64 &&
  !Link.A64.loadOk { Λdl with code := ⟨2 ^ 64 - 4, 4⟩ } nop {} &&
  Rt.A64.symsAround (2 ^ 64 - 4) nop [] &&
  Link.A64.loadOk { Λdl with code := ⟨2 ^ 64 - 8, 4⟩ } nop {}

-- A `.data` symbol named like a `.rodata` label is not placed twice: the
-- loader drops it from `loadSyms`, and `symsAgree` asks it be at the
-- label's address.
#guard loadSyms { Λro with symbols := [("x", 128)] } [.label "x", .quad 0] == [("x", 128)] &&
  Link.A64.loadOk { Λro with symbols := [("x", 128)] } nop { rodata := [.label "x", .quad 0] } &&
  !Link.A64.loadOk { Λro with symbols := [("x", 16)] } nop { rodata := [.label "x", .quad 0] }

-- The executable then starts at the lowest symbol, with two cells (padding
-- and a label) before the code.
#guard Rt.A64.belowLen 48 [("a", 16), ("b", 56)] == 2 &&
  exeStart 48 [("a", 16), ("b", 56)] == 16 && Rt.A64.belowLen 48 [("b", 56)] == 0

/-- A literal 4-byte program (kernel-reducible, unlike the parsed `nop`). -/
private def lit : Program := [.label "f", .byteArray (.mk #[0, 0, 0, 0])]

/-- Symbols on both sides of `lit` at `48`, one at the end of the code. -/
private def symsLH : List (String × Nat) := [("lo", 16), ("lo2", 40), ("e", 52), ("hi", 64)]

-- The loaded thread lays out `lit` after the cells below the code, halts at
-- its end, has a valid layout, and labels each symbol at its address, the
-- code label too.
example : Rt.A64.Lays (threadAt Entry.linux 48 lit symsLH).exe lit (Rt.A64.belowLen 48 symsLH) :=
  Rt.A64.lays_threadAt_below _ _ _ _ (by decide +kernel)
example : (threadAt Entry.linux 48 lit symsLH).endPc =
    Rt.A64.endOf (threadAt Entry.linux 48 lit symsLH).exe lit (Rt.A64.belowLen 48 symsLH) :=
  Rt.A64.endPc_threadAt_below _ _ _ _
example : Kraken.Executable.ValidLayout (threadAt Entry.linux 48 lit symsLH).exe :=
  Rt.A64.validLayout_threadAt_below (by decide +kernel) (by decide +kernel)
example : (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "lo2" = Int64.ofNat 40 :=
  Rt.A64.label_threadAt_of_sym_around (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "e" = Int64.ofNat 52 :=
  Rt.A64.label_threadAt_of_sym_around (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "f" = Int64.ofNat 48 :=
  Rt.A64.label_threadAt_of_codeOf_below (by decide +kernel) (by decide +kernel)

-- And by evaluation: the labels of the loaded thread.
#guard ((_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "lo",
    (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "f",
    (_root_.Executable.labels (threadAt Entry.linux 48 lit symsLH).exe).label "hi") ==
  (Int64.ofNat 16, Int64.ofNat 48, Int64.ofNat 64)

end Scc.Test.LowSymsA64
