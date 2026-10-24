import Scc.Cert.PlaceOKX64

/-!
# x86-64's A2 accepts data symbols below the code

The reader does not refuse data symbols below the code
(`Scc.Cert.Elf.refuseBelowCode := false`), and x86-64's placement check
accepts them: its loader check (`Link.X64.loadOk`, A2) uses the two-sided
`Rt.X64.symsAround` with `noClash`. Checked by evaluation.
-/

namespace Scc.Test.LowSymsX64Refuse

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Cert

/-- A literal 4-byte program of sized cells: a label, then 4 bytes. -/
private def lit : List (Directive × Nat) := [(.label "f", 0), (.byteArray (.mk #[0, 0, 0, 0]), 4)]

/-- `trivLayout` with its data region below the code. -/
private def Λdl : Scc.Sem.Layout :=
  { trivLayout with code := ⟨48, 16⟩, data := ⟨16, 16⟩ }

/-- `trivLayout` with its data region above the code. -/
private def Λdh : Scc.Sem.Layout :=
  { trivLayout with code := ⟨48, 16⟩, data := ⟨64, 16⟩ }

-- A symbol above the code passes x86-64's loader check, and so does one
-- below it in a well-formed layout.
#guard Link.X64.loadOk { Λdh with symbols := [("hi", 64)] } lit {} [("f", 0)] &&
  Link.wfB { Λdl with symbols := [("lo", 16)] } &&
  Link.X64.loadOk { Λdl with symbols := [("lo", 16)] } lit {} [("f", 0)]

end Scc.Test.LowSymsX64Refuse
