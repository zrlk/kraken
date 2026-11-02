/-
**hello's stack bounds wired in** (x86-64; the twin of `Spike/Lib/A64HelloStackW.lean`): the band of
`Spike/Lib/X64HelloStackB.lean` at the premise it discharges.

- `wcWf_W2Hb`: `WcW2.wcWf_W2H` with `wcMidW_wcGH`'s band `hband` from `BoxPureH`'s `R.base + 96` the first
  stack's top (`StackB.bandTiH_of`).

Not twinned (unreachable from the hello proof): AArch64's `SegR.childP_of_cloneR1`.

## Differences from the AArch64 version

- The bounds are `WcW2.wcWf_W2H`'s on x86-64: no `hal`, the base's 8-alignment `hR8`, `R.lo ≤ -320` and
  `16 ≤ R.hi` (AArch64: `hal`, `R.lo ≤ -336`, `0 ≤ R.hi`); the region's base is `96` below the first stack's top
  (AArch64 `80`).
- x86-64's `WcMainWH` takes the one source guard `QBH l b ws` (AArch64: `SBH` and `QBH`).
-/
import Spike.Lib.X64HelloStackB
import Spike.Lib.X64HelloWcW2

namespace Spike.Lib.X64.HelloPh.WcW2

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Ctl Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Flow.HelloWc (WcMainWH tH)
open Spike.Lib.X64.HelloPh.RootWX (W2H)
open Spike.Lib.X64HelloHMid (QBH)

section Main

variable {L : RuntimeLayout} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {R : Region} {F : MachineData → Prop} {ms : Spike.Lib.MemSide isa} {J1 : Spike.Lib.X64.AS → Ctl → Prop}
  {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word}
  (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)

set_option hygiene false in
/-- The root's third level at no frames. -/
local notation "W2" => fun s c =>
  W2H L (ntA L.lab) ar Spike.Lib.X64HelloSrc.helloSrc Dt (Spike.Lib.X64.HelloPh.ClH L) Ctx lbl lsize s c []

include hp hlo hΛ hlab hsite

/-- **`wcWf_W2H` with the band from the region's base**: `hband` by `StackB.bandTiH_of` at `R.base + 96` the
first stack's top (`hbase`, `BoxPureH`'s). -/
theorem wcWf_W2Hb (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hRlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hsepN : ntA L.lab ≠ L.pnA ∧ ntA L.lab ≠ L.lockA ∧ ntA L.lab ≠ L.freeNA ∧ ntA L.lab ≠ L.nextA)
    (hmN : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨ntA L.lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA L.lab) 8 = none)
    (hb : Spike.Lib.X64.HelloPh.Tcb2CallW.BandSp3H L R)
    (hsep : L.pnA ≠ L.lockA ∧ L.pnA ≠ L.freeNA ∧ L.pnA ≠ L.nextA ∧ L.pnA ≠ ntA L.lab)
    (hhdr : L.pinA + 80#64 + 24#64 ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, ntA L.lab])
    (hmP : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨L.pnA, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨L.pinA + 104#64, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem L.pnA 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (L.pinA + 104#64) 8 = none)
    (hbase : R.base.toNat + 96 = L.stacksA.toNat + 16384)
    (htidW : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) true ⟨tH L.lab + 56#64, 8⟩ = true ∧
      (∀ m', F m' → Mem.loadInt m'.dmem (tH L.lab + 56#64) 8 = none) ∧
      ∀ w, (⟨tH L.lab + 56#64, 8⟩, w) ∉ Spike.Lib.X64.HelloPh.own2aH L (ntA L.lab) 0)
    (hpl : WcMainWH (fun s c => PlacedSE L.Λ lbl s c []) (fun _ _ => False) L.exe L.endPc R F F ms J1
      (QBH l b ws))
    (hoff56 : ¬ (ar.heap ≤ (tH L.lab + 56#64).toNat ∧ (tH L.lab + 56#64).toNat < ar.heap + 16 * ar.cells) ∧
      (⟨tH L.lab + 56#64, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WcMainWH W2 (fun _ _ => False) L.exe L.endPc R F F ms J1 (QBH l b ws) :=
  wcWf_W2H (Dt := Dt) (Ctx := Ctx) (lsize := lsize) hp hlo hΛ hlab hsite hR hR8 hRlo hhi hsepN hmN hunN hb hsep
    hhdr hmP hmH hunP hunH (Spike.Lib.X64.HelloPh.StackB.bandTiH_of hbase) htidW hpl hoff56

end Main

end Spike.Lib.X64.HelloPh.WcW2

/-- info: 'Spike.Lib.X64.HelloPh.WcW2.wcWf_W2Hb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WcW2.wcWf_W2Hb
