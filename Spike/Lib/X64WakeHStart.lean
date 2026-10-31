/-
**wake's start loads** (x86-64), the x86-64 twin of
`Spike/Lib/WakeHStart.lean`: `X64WakeAssembly.wake_obligations`' `hstart`,
`∃ d, (target (kernel 1) E).load asm Λ = some d`, from the loader's checks.

- `hstart_of_loadOk`: from the parse of the text (`hpa`, `hd`), the loader's
  check `loadOk` and an entry stack clear of the layout (`hE`).
- `hstart_ofPlaceOKAt`: at an output passing `placeOKAt` (A2's `loadOk`),
  the parse of its program and data sections; `hstart_linux`: at
  `Entry.linux`, whose stack `placeOKAt` puts clear of the layout.

**Unlike AArch64** the x86-64 text is an `Asm` (text, instruction sizes,
label offsets): the parse premise `hpa` is `cellsOf asm = some prog` (the
sized cells) rather than `textProgram asm = .ok prog`, `hd` reads
`asm.text`, and the loader's `loadOk` also checks the label offsets, so the
`PlaceWX` forms take `hoffs : asm.labelOffs = po.labelOffs`.
-/
import Scc.Cert.PlaceOKX64
import Spike.Lib.X64WakeRunInv
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeHStart

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel

/-- **The start loads** given the parse of the text, the loader's check and
an entry stack clear of the layout. -/
theorem hstart_of_loadOk {E : Entry} {Λ : Scc.Sem.Layout} {asm : Asm} {prog : List (Directive × Nat)}
    {secs : DataSecs} (hpa : cellsOf asm = some prog) (hd : dataSections asm.text = some secs)
    (hl : Scc.Cert.Link.X64.loadOk Λ prog secs asm.labelOffs = true) (hE : E.clear Λ = true) :
    ∃ d, (target (kernel 1) E).load asm Λ = some d :=
  ⟨_, (load_of_parsed (kernel 1) E Λ hpa hd).trans (Scc.Cert.Link.X64.loadParsed_of_loadOk hl hE)⟩

/-- **The start loads at an output passing `placeOKAt`**, given the parse of
its program (`hpa`, `X64WakeAssembly`'s), data sections (`hd`) and label
offsets (`hoffs`). -/
theorem hstart_ofPlaceOKAt {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out} {E : Entry}
    {Λ : Scc.Sem.Layout} {asm : Asm} (hpl : Spike.Lib.PlaceWX pcfg Λ po)
    (hpa : cellsOf asm = some po.prog) (hd : dataSections asm.text = some po.secs)
    (hoffs : asm.labelOffs = po.labelOffs) (hE : E.clear Λ = true) :
    ∃ d, (target (kernel 1) E).load asm Λ = some d :=
  hstart_of_loadOk hpa hd (hoffs ▸ Spike.Lib.PlaceWX.loadOk_of_placeWX hpl) hE

/-- **The start loads at `Entry.linux`** at an output passing `placeOKAt`. -/
theorem hstart_linux {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    {Λ : Scc.Sem.Layout} {asm : Asm} (hpl : Spike.Lib.PlaceWX pcfg Λ po)
    (hpa : cellsOf asm = some po.prog) (hd : dataSections asm.text = some po.secs)
    (hoffs : asm.labelOffs = po.labelOffs) :
    ∃ d, (target (kernel 1) Entry.linux).load asm Λ = some d :=
  hstart_ofPlaceOKAt hpl hpa hd hoffs (Spike.Lib.PlaceWX.clear_of_placeWX hpl)

end Spike.Lib.X64WakeHStart

/-- info: 'Spike.Lib.X64WakeHStart.hstart_of_loadOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHStart.hstart_of_loadOk

/-- info: 'Spike.Lib.X64WakeHStart.hstart_ofPlaceOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHStart.hstart_ofPlaceOKAt

/-- info: 'Spike.Lib.X64WakeHStart.hstart_linux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHStart.hstart_linux
