import Scc.Cert.PlaceOKA64

/-!
# The end-to-end code guard on AArch64

An end-to-end test reads a layout `Λ` off a linked executable and checks
the certificate's output against it. The placement check (`placeOKAt`)
only asks that the code end within the executable's code region
(`PlaceOK.A64.codeFits`: `≤`), which is all the proofs need. An
end-to-end test asks more: that the code the canonical loader lays out from
the certificate's output fills the code region exactly (`codeFills`: `=`),
so that the text linked is the text checked, with nothing before or after
it in `.text`. `e2eOk` is the two checks together, the one guard every
end-to-end test (and the generated certification file) runs.

`codeFills` is not a component of `placeOKAt`: the theorems' premises and
statements are unchanged.
-/

namespace Scc.Cert.E2E.A64

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **The code fills its region**: the output laid out from the code base
(`Scc.Sem.A64.codeEnd`) ends exactly at the end of the layout's code
region. -/
def codeFills (o : Out) (Λ : Scc.Sem.Layout) : Bool :=
  decide (Scc.Sem.A64.codeEnd Λ.code.lo o.prog = Λ.code.lo + Λ.code.size)

/-- **The end-to-end guard**: the placement check at `Λ` and the code
filling `Λ`'s code region. -/
def e2eOk (cfg : Scc.Cert.PlaceOK.Config) (Λ : Scc.Sem.Layout) (o : Out) : Bool :=
  placeOKAt cfg Λ o && codeFills o Λ

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Out}

/-- The code's end from `codeFills`. -/
theorem codeEnd_eq_of_codeFills (h : codeFills o Λ = true) :
    Scc.Sem.A64.codeEnd Λ.code.lo o.prog = Λ.code.lo + Λ.code.size :=
  of_decide_eq_true h

/-- Filling the code region is fitting in it. -/
theorem codeFits_of_codeFills (h : codeFills o Λ = true) : codeFits o Λ = true :=
  decide_eq_true (Nat.le_of_eq (codeEnd_eq_of_codeFills h))

/-- The placement check from the end-to-end guard. -/
theorem placeOKAt_of_e2eOk (h : e2eOk cfg Λ o = true) : placeOKAt cfg Λ o = true :=
  (Bool.and_eq_true _ _ ▸ h).1

/-- The code filling its region from the end-to-end guard. -/
theorem codeFills_of_e2eOk (h : e2eOk cfg Λ o = true) : codeFills o Λ = true :=
  (Bool.and_eq_true _ _ ▸ h).2

/-- The code's end from the end-to-end guard. -/
theorem codeEnd_eq_of_e2eOk (h : e2eOk cfg Λ o = true) :
    Scc.Sem.A64.codeEnd Λ.code.lo o.prog = Λ.code.lo + Λ.code.size :=
  codeEnd_eq_of_codeFills (codeFills_of_e2eOk h)

end Scc.Cert.E2E.A64
