/-
**`inv0R` from a segment to the heap abort** (wake.w, AArch64): any
pre-lift segment inside `WS` under the take `PhRec.K` at `msBot … E []`,
ending at `wc_main`'s heap-abort exit (`StartH0B.QabW`), puts its entry
pairs in `h0`'s invariant `inv0R` at the frames `[]`. `StartH0B.hst0_of`'s
part B for any precondition `P` (`HLand`'s counter-add tail, `Land4`).

- `inv0_of_habW`: lift at `[]` (`SegWS.liftS` into `W0S`), the heap abort
  closed (`StartH0C.wake_hab_closed`), the take as `TakeCKS`
  (`takeCKS_iff`), `W0S` as `W0W` (`marks_target`), then `gfpS_of_segWS`.
  At the root's immediate table `IW`, where `c0W`'s placement is a
  theorem (`WakeImmsC0.placedSE_c0WW`), so no placement premise.
-/
import Spike.Lib.A64WakeStartH0B
import Spike.Lib.A64WakeStartH0C
import Spike.Lib.WakeImmsC0

namespace Spike.Lib.A64.WakePh.Land5

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakeWf (DtW X0W)
open Spike.Lib (FragS Frag SegW SegWS)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeOPremW (W0W)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The root's immediate table. -/
local notation "i" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
/-- The layout of `ofPlaceW` at `IW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- The start's fragment at entry `E` (`StartH0B`'s). -/
local notation "WSE" => WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp i) wakeSrc DtW
  (Spike.Lib.WakeOD.ClW hp i) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E) (X0W (Ly) (Spike.Lib.WakeOSide.aW hp i E))

/-- **A segment to the heap abort gives `inv0R` at `[]`**: from `P` inside
`WS` under `PhRec.K` at `msBot … E []` to `QabW`, every `P` pair is in
`inv0R … E` at the frames `[]`. -/
theorem inv0_of_habW (E : Entry) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    {P : Frag isaLSE2}
    (h : SegW WSE (Spike.Lib.A64.PhRec.K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) wakeSrc (L0T (Ly).Λ)
      (WakeRoot.msBot hp i ls0 Ctx E []) P (StartH0B.QabW hp i ls0 Ctx E)) :
    ∀ s c, P s c → WakeRoot.inv0R hp i ls0 Ctx frM E s c [] := by
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hwpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hS : SegWS (W0W hp i E DtW (Ctx E) (ls0 E) (frM E))
      (Spike.Lib.A64ConsumerA.TakeCKS (Spike.Lib.WakeOSide.aW hp i E) (Spike.Lib.WakeOD.ClW hp i))
      wakeSrc (L0T (Ly).Λ) (WakeRoot.msBot hp i ls0 Ctx E) (Frag.at P []) (fun _ _ _ => False) :=
    (((Spike.Lib.SegWS.liftS (ms := WakeRoot.msBot hp i ls0 Ctx E) (W := StartH0B.W0S hp i ls0 Ctx frM E) []
      h fun _ _ h => h).seq (StartH0C.wake_hab_closed hp i hpa hwp hlo0 (Spike.Lib.WakeImmsC0.placedSE_c0WW hp))).mono_K
      fun s c fs hW s' => StartH0B.takeCKS_iff hp i hpa hwp E hW.2.1).mono_W fun s c fs h => by
        unfold W0W; rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hwpL]; exact h
  exact fun s c hP => Spike.Lib.A64GfpS.gfpS_of_segWS hS s c [] ⟨hP, rfl⟩

end Spike.Lib.A64.WakePh.Land5

/-- info: 'Spike.Lib.A64.WakePh.Land5.inv0_of_habW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land5.inv0_of_habW
