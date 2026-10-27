import Scc.Cert.PlaceOKA64

/-!
# A2 by keyed lookups (AArch64)

`a2` (`Scc/Cert/PlaceOKA64.lean`) checks the canonical loader's checks of
the link (`Scc.Cert.Link.A64.loadOk`), its abort labels in the program
(`abortsIn`) and its image (`imageIn`). Each resolves code labels by
`codeOf`, a scan of the program comparing strings: one scan per abort
label, per data symbol below the code (`noClash`), per `.quad` label (the
loader's and the image's).

`a2fast` is the same check (`a2fast_eq`) resolving them in the keyed table
of `Scc/Cert/Rt/PhasesA64.lean` (`codeT`, `codeT_eq`). A certificate proves
`prog_placeOK_2` by `a2_of_fast` and the kernel's evaluation of `a2fast`.
-/

namespace Scc.Cert.PlaceOK.A64

open Kraken Scc.Sem Scc.Sem.A64 Scc.Cert.Link.A64
open Scc.Cert.Rt.A64 (codeT codeT_eq)

/-- **`noClash`, keyed.** -/
def noClashK (lo : Nat) (prog : Program) (syms : List (String × Nat)) : Bool :=
  (symsBelow lo syms).all (fun p => (codeT lo prog p.1).isNone) && Link.nodupB (syms.map (·.1))

/-- **`loadOk`, keyed.** -/
def loadOkK (Λ : Scc.Sem.Layout) (prog : Program) (secs : DataSecs) : Bool :=
  let ro := secs.rodata
  let code (l : String) : Option Nat := (codeT Λ.code.lo prog l).orElse fun _ => Λ.symbols.lookup l
  let syms := loadSyms Λ ro
  rodataFits Λ ro && symsAgree Λ ro && quadsResolve Λ ro code &&
    symsAbove Λ.code.lo (codeEnd Λ.code.lo prog) syms &&
    prog.all (fun d => Kraken.Executable.cellOk (d, d.fakeSize)) && Rt.A64.symsAround Λ.code.lo prog syms &&
    noClashK Λ.code.lo prog syms && decide (codeEnd Λ.code.lo prog < 2 ^ 64)

theorem loadOkK_eq (Λ : Scc.Sem.Layout) (prog : Program) (secs : DataSecs) :
    loadOkK Λ prog secs = loadOk Λ prog secs := by
  simp only [loadOkK, loadOk, noClashK, noClash, codeT_eq]

/-- **`abortsIn`, keyed.** -/
def abortsInK (prog : Program) (Λ : Scc.Sem.Layout) : Bool :=
  Link.kinds.all fun k => (codeT Λ.code.lo prog (Λ.abortLbl k)).isSome

theorem abortsInK_eq (prog : Program) (Λ : Scc.Sem.Layout) : abortsInK prog Λ = abortsIn prog Λ := by
  simp only [abortsInK, abortsIn, codeT_eq]

/-- **`imageIn`, keyed.** -/
def imageInK (prog : Program) (secs : DataSecs) (Λ : Scc.Sem.Layout) : Bool :=
  Link.imageOk Λ secs (codeT Λ.code.lo prog)

theorem imageInK_eq (prog : Program) (secs : DataSecs) (Λ : Scc.Sem.Layout) :
    imageInK prog secs Λ = imageIn prog secs Λ := by
  simp only [imageInK, imageIn, codeT_eq]

/-- **A2 for the kernel** (`a2fast_eq`). -/
def a2fast (o : Out) (t : Tables) : Bool :=
  loadOkK t.Λ o.prog o.secs && abortsInK o.prog t.Λ && imageInK o.prog o.secs t.Λ

theorem a2fast_eq (o : Out) (t : Tables) : a2fast o t = a2 o t := by
  simp only [a2fast, a2, loadOkK_eq, abortsInK_eq, imageInK_eq]

/-- **A2 from `a2fast`** (a certificate's `prog_placeOK_2`). -/
theorem a2_of_fast {o : Out} {t : Tables} (h : a2fast o t = true) : a2 o t = true :=
  a2fast_eq o t ▸ h

end Scc.Cert.PlaceOK.A64
