/-
**The refusal path's layout facts** (x86-64, wake.w): the return address
and code facts that the `X64WakeRefStub` pieces' proofs share (the twin of
`A64WakeRefAg`'s `raT_sp11` and the layout steps of A64's pieces; the region
is `X64WakeRefCallee.callee_of_pre`).

- `raT_x23`: the return address of the refusal's call is `.Lwc_main.x23`'s
  (`raT` is `.Lwc_main.spawnfail5 + 12`).
- `lays_W`, `endR_eq`: wake's cells laid out in `ofPlaceWX`'s executable,
  whose end is `WakeH1Inv.endR` (from the parses `hpa`, `hwp`).
- `siteOff_W`: the take site is off `scc_rt_abort`'s code (`abPT`'s
  `hsite`).

**Where this differs from AArch64**: the return address is `spawnfail5 + 12` (`call` is 5 bytes after a 7-byte `leaq`; A64's
`+ 8`); labels are compared at the resolved addresses (`4203472`,
`4203484`, the take site at `4200277`).
-/
import Spike.Lib.X64WakeRefCallee
import Spike.Lib.X64WakeOAb
import Spike.Lib.X64WakeSrcCtl
import Spike.Lib.X64SiteOfPlaceW

namespace Spike.Lib.X64.WakeRefStub

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64.WakePh (lo)
open Scc.Cert.Rt.X64 (codeT_eq)
open SccCode (wakeCells)

/-- **The return address of the refusal's call is `.Lwc_main.x23`'s.** -/
theorem raT_x23 {L : RuntimeLayout} (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    raT L.lab ".Lwc_main" = (L.lab ".Lwc_main.x23").toBitVec := by
  have h5 : L.lab (".Lwc_main" ++ ".spawnfail5") = Int64.ofNat 4203472 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  have h23 : L.lab ".Lwc_main.x23" = Int64.ofNat 4203484 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold raT
  rw [h5, h23]
  decide

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **Wake's cells are laid out** in `ofPlaceWX`'s executable. -/
theorem lays_W {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) :
    Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := by
  rw [← Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp]; exact (Ly).lays

/-- **The layout's end is `endR`.** -/
theorem endR_eq {asm : Asm} (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells) :
    (Ly).endPc = Spike.Lib.X64.WakeH1Inv.endR hp i := by
  show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _
  rw [Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp]

/-- **The take site is off `scc_rt_abort`'s code** (`abPT`'s `hsite`). -/
theorem siteOff_W (hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x) :
    ∀ a, (Spike.Lib.X64.PhRec.μ (Ly)).site .take = some a →
      a < ((Ly).lab "scc_rt_abort").toBitVec.toNat ∨ ((Ly).lab "scc_rt_thr_worker").toBitVec.toNat ≤ a := by
  intro a ha
  obtain ⟨e1, e2, -⟩ := Spike.Lib.X64.WakePh.ab_labs hlab
  have es : (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
    hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  rw [Spike.Lib.PlaceWX.site_ofPlaceWX hp i] at ha
  cases ha
  left
  rw [es, e1]
  decide

end Inst

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.raT_x23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.raT_x23

/-- info: 'Spike.Lib.X64.WakeRefStub.lays_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.lays_W

/-- info: 'Spike.Lib.X64.WakeRefStub.endR_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.endR_eq

/-- info: 'Spike.Lib.X64.WakeRefStub.siteOff_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.siteOff_W
