/-
**wake's start loads** (AArch64): `WakeAssembly.wake_obligations`'
`hstart`, `∃ d, (target (kernel 1) E).load asm Λ = some d`, from the loader's
checks.

- `hstart_of_loadOk`: from the parse of the text (`hpa`, `hd`), the loader's
  check `loadOk` and an entry stack clear of the layout (`hE`).
- `hstart_ofPlaceOKAt`: at an output passing `placeOKAt` (A2's `loadOk`),
  the parse of its program and data sections; `hstart_linux`: at
  `Entry.linux`, whose stack `placeOKAt` puts clear of the layout.
-/
import Scc.Cert.PlaceOKA64
import Spike.Lib.WakeRunInv
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeHStart

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel

/-- **The start loads** given the parse of the text, the loader's check and
an entry stack clear of the layout. -/
theorem hstart_of_loadOk {E : Entry} {Λ : Scc.Sem.Layout} {asm : String} {prog : Program} {secs : DataSecs}
    (hpa : textProgram asm = .ok prog) (hd : dataSections asm = some secs)
    (hl : Scc.Cert.Link.A64.loadOk Λ prog secs = true) (hE : E.clear Λ = true) :
    ∃ d, (target (kernel 1) E).load asm Λ = some d :=
  ⟨_, (load_of_parsed (kernel 1) E Λ hpa hd).trans (Scc.Cert.Link.A64.loadParsed_of_loadOk hl hE)⟩

/-- **The start loads at an output passing `placeOKAt`**, given the parse of
its program (`hpa`, `WakeAssembly`'s) and data sections (`hd`). -/
theorem hstart_ofPlaceOKAt {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out} {E : Entry}
    {Λ : Scc.Sem.Layout} {asm : String} (hpl : PlaceW pcfg Λ po)
    (hpa : textProgram asm = .ok po.prog) (hd : dataSections asm = some po.secs) (hE : E.clear Λ = true) :
    ∃ d, (target (kernel 1) E).load asm Λ = some d :=
  hstart_of_loadOk hpa hd (PlaceW.loadOk_of_placeW hpl) hE

/-- **The start loads at `Entry.linux`** at an output passing `placeOKAt`. -/
theorem hstart_linux {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    {Λ : Scc.Sem.Layout} {asm : String} (hpl : PlaceW pcfg Λ po)
    (hpa : textProgram asm = .ok po.prog) (hd : dataSections asm = some po.secs) :
    ∃ d, (target (kernel 1) Entry.linux).load asm Λ = some d :=
  hstart_ofPlaceOKAt hpl hpa hd (PlaceW.clear_of_placeW hpl)

/-- info: 'Spike.Lib.WakeHStart.hstart_ofPlaceOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hstart_ofPlaceOKAt
/-- info: 'Spike.Lib.WakeHStart.hstart_linux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hstart_linux

end Spike.Lib.WakeHStart
