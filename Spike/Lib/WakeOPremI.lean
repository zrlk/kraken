/-
**`WakeO.OPrem` at `wakeD` with the load's relation closed** (AArch64): `WakeOPremW.oPrem_W` with `hinit` by `WakeOHinit.hinit_W`, the
write tail `DtW` (`hdt` by `A64WakeWf.hdtW`).

- `oPrem_WI`: `OPrem` at `wakeD` at the levels. `h0`'s take facts
  (`H0Take`, `H0TakeOwn`) come from `h0` itself (`A64WakeWf.h0Take_of`, `h0TakeOwn_of`, through `W0W`'s `X0W`). Open, as
  premises: the segments `h0`, `h1`, the take facts `h1t`, `h1o`, the start
  in `inv0` (`hst`); the counter row `hctr0`; the box store `hnew0`; the instance facts (`hlo`,
  `hstat`, `hpin2`, `hsub1`, `CtrZ`, `NtZ`) and the entry clear of the
  layout (`hE`).
-/
import Spike.Lib.WakeOPremW
import Spike.Lib.WakeOHinit

namespace Spike.Lib.WakeOPremI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeOPremW (W0W W1W)
open Spike.Lib.A64.WakeWf (DtW)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (arch : WeakMem.Arch)
  (E : Entry) (cT : Loc) (ls0 : Lsize) (Ctx : FragS isaLSE2) (frM : TermRun.Frame)
  (inv0 : FragS isaLSE2) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `wakeD` at the levels. -/
local notation "D" => WakeOD.wakeD hp i E cT DtW ls0 (W0W hp i E DtW Ctx ls0 frM) inv0 (W1W hp i E DtW Ctx ls0) inv1

set_option hygiene false in
/-- The entry's marks. -/
local notation "μE" => (target (kernel 2) E).marks SccCertificate.asm (Ly).Λ

/-- **`OPrem` at `wakeD`, `hinit` closed** (see the module doc). -/
theorem oPrem_WI (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hd : dataSections SccCertificate.asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hnz : WakeOInit.NtZ Λ0 o = true) (hE : E.clear (Ly).Λ = true)
    {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- OPEN: the segments, the take facts, the start in `inv0` -/
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) wakeSrc (A64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False) (A64ConsumerA.upd (D).L0 l b)
          (A64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    (h0 : SegInvS (D).W0 (TakeCKS (D).a (D).Cl) wakeSrc (D).L0
      (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0) (D).inv0)
    (h1t : Spike.Lib.A64.Flow.WakeWc.H1Take (Ly) (WakeOSide.aW hp i E) inv1)
    (h1o : Spike.Lib.A64.Flow.WakeWc.H1TakeOwn (Ly) (WakeOSide.aW hp i E) inv1)
    (hst : inv0 (threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata))
      ⟨Spike.Lib.WakePreAsm.wakeTh0.term, Spike.Lib.WakePreAsm.wakeTh0.env, none⟩
      Spike.Lib.WakePreAsm.wakeTh0.stack)
    /- OPEN: the counter's row; the box's store -/
    (hctr0 : ∀ s c fs, inv0 s c fs → Ctx s c fs → WrAt s (D).ar.ctrLoc →
      ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0 fs')
        (fun s' c'' => PendA wakeSrc (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0 s' c'' fs') s c')
    (hnew0 : ∀ s c fs, inv0 s c fs → Ctx s c fs → ¬ WrAt s (D).ar.ctrLoc →
      ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
      ∀ L, WrAt s L → ¬ ArenaW (D).ar (D).L0 (D).ls0 c' L →
      NewStM wakeSrc (D).L0
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0 fs')
        s c')
 :
    WakeO.OPrem arch (Ly).Λ B SccCertificate.asm E (WakeOD.AbW hp i) (WakeOD.AcW hp i) D :=
  WakeOPremW.oPrem_W hp i arch E cT DtW ls0 Ctx frM inv0 inv1 hpa hwp hd hlo hpin2 hsub1 hc hB h1 h0
    (Spike.Lib.A64.WakeWf.h0Take_of h0) (Spike.Lib.A64.WakeWf.h0TakeOwn_of h0) h1t h1o
    hctr0 hnew0 Spike.Lib.A64.WakeWf.hdtW
    (WakeOHinit.hinit_W hp i hpa hwp hd hlo hstat hsub1 hc hnz hpin2 arch hE cT DtW ls0 _ inv0 _ inv1 hst)

end Spike.Lib.WakeOPremI

/-- info: 'Spike.Lib.WakeOPremI.oPrem_WI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOPremI.oPrem_WI
