/-
**`WakeO.OPrem` at `wakeD`** (AArch64): the pre-spawn premises
at the runtime's layout `L := RuntimeLayout.ofPlaceW hp i`, the per-state
levels the (`W0W`, `W1W`: `A64WakeWf.W0`/`W1` at `wakeD`'s `own`, `ar`,
`L0`, `Cl` and the root's abort phases `AbW`, `AcW`), the closed fields
discharged:

- `ha` (`WakeOSide.ha_W`), `hsplit` (`WakeOSplit.hsplit_W`, from the take facts), the ranges (`WakeOSide.ranges_W`, given `hsub1`), `hro`,
  `hwf` (`WakeOSide.hro_W`, `hwf_W`);
- `hP`, `hsafe` (`WakeSrcOPrem.wake_hookOK`, `wake_srcSafeS`), `hrd`
  (`WakeOD.hrd_W`), `hClc` (`WakeOD.hClc_W`);
- `hGpl` (`WakeOG.hGpl_gW`, given `hpin2`), `hok` (`WakeOD.hok_W`, given
  `CtrZ`), `hB` (`WakeOD.hB_W`, a budget of `allocCells` cells);
- `hW0` (`A64WakeWf.hW0`, from the counter's row `hctr0` and the box's
  store `hnew0`), `hW1`
  (`A64WakeWf.hW1F`: `W1` writes no counter);
- `hti0` (`WakeOSide.hti0_W` at `WakeOAb.hab0_W`, `hac0_W`, given `hlo`).

Open, as premises: the segments `h0`, `h1` and take facts `h0t`, `h0o`,
`h1t`, `h1o`; the counter row `hctr0`, the box store `hnew0` and the write tail `hdt`
(`A64WakeWf.hdtW` at `DtW`);
the load's relation `hinit` (`WakePreAsm.wake_init`).
-/
import Spike.Lib.WakeO
import Spike.Lib.WakeOSplit
import Spike.Lib.WakeOAb
import Spike.Lib.WakeSrcOPrem
import Spike.Lib.A64WakeWf
import Spike.Lib.A64WakeX0

namespace Spike.Lib.WakeOPremW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}

/-- **The level before the allocation** at `wakeD`'s choices (`W0`, its
per-state facts `X0W` at the take pc `WakeOSide.aW`). -/
def W0W (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Entry)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Lsize) (frM : TermRun.Frame) : FragS isaLSE2 :=
  Spike.Lib.A64.WakeWf.W0 (RuntimeLayout.ofPlaceW hp i).Λ
    ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ)
    (Spike.Lib.A64.WakePh.ownG (RuntimeLayout.ofPlaceW hp i)
      (Spike.Lib.A64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceW hp i).lab))
    (WakeOD.arW hp i) wakeSrc Dt (WakeOD.AbW hp i) (WakeOD.ClW hp i)
    (WakeOD.AcW hp i) Ctx (Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hp i).Λ) (Spike.Lib.WakeLoadT.ls0T ls0) frM
    (Spike.Lib.A64.WakeWf.X0W (RuntimeLayout.ofPlaceW hp i) (WakeOSide.aW hp i E))

/-- **The level after the allocation** at `wakeD`'s choices (`W1`). -/
def W1W (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Entry)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Lsize) :
    WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  Spike.Lib.A64.WakeWf.W1 (RuntimeLayout.ofPlaceW hp i).Λ
    ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ)
    (Spike.Lib.A64.WakePh.ownG (RuntimeLayout.ofPlaceW hp i)
      (Spike.Lib.A64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceW hp i).lab))
    (WakeOD.arW hp i) wakeSrc Dt (WakeOD.AbW hp i) (WakeOD.ClW hp i)
    (WakeOD.AcW hp i) Ctx (Spike.Lib.WakeLoadT.L0T (RuntimeLayout.ofPlaceW hp i).Λ) (Spike.Lib.WakeLoadT.ls0T ls0)

section Prem

variable (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (arch : WeakMem.Arch)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (ls0 : Lsize) (Ctx : FragS isaLSE2) (frM : TermRun.Frame)
  (inv0 : FragS isaLSE2) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

set_option hygiene false in
/-- `wakeD` at the levels. -/
local notation "D" => WakeOD.wakeD hp i E cT Dt ls0 (W0W hp i E Dt Ctx ls0 frM) inv0 (W1W hp i E Dt Ctx ls0) inv1

set_option hygiene false in
/-- The entry's marks. -/
local notation "μE" => (target (kernel 2) E).marks SccCertificate.asm (Ly).Λ

/-- **`OPrem` at `wakeD`** (see the module doc). -/
theorem oPrem_W (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hd : dataSections SccCertificate.asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.A64.Rt.CtrZ o)
    {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- OPEN: the segments and the take facts -/
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) wakeSrc (A64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False) (A64ConsumerA.upd (D).L0 l b)
          (A64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    (h0 : SegInvS (D).W0 (TakeCKS (D).a (D).Cl) wakeSrc (D).L0
      (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0) (D).inv0)
    (h0t : Spike.Lib.A64.Flow.WakeWc.H0Take (Ly) (WakeOSide.aW hp i E) inv0)
    (h0o : Spike.Lib.A64.Flow.WakeWc.H0TakeOwn (Ly) (WakeOSide.aW hp i E) inv0)
    (h1t : Spike.Lib.A64.Flow.WakeWc.H1Take (Ly) (WakeOSide.aW hp i E) inv1)
    (h1o : Spike.Lib.A64.Flow.WakeWc.H1TakeOwn (Ly) (WakeOSide.aW hp i E) inv1)
    /- OPEN: the counter's row and the write tail; the box's store -/
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
    (hdt : ∀ s buf n, (D).Dt s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    /- OPEN: the load's relation -/
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load SccCertificate.asm (Ly).Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch wakeSrc) wakeSrc (D).G (D).own (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1)
          (HeldOk2 (Ly).Λ (D).r0 (D).r1) μE (D).ar d s0) :
    WakeO.OPrem arch (Ly).Λ B SccCertificate.asm E (WakeOD.AbW hp i) (WakeOD.AcW hp i) D := by
  obtain ⟨hs0, hs1, hz0, hz1, hdj, hw0, hw1⟩ := WakeOSide.ranges_W hp i hsub1
  exact {
    h1 := h1
    h0 := h0
    hW0 := Spike.Lib.A64.WakeWf.hW0 hctr0 hnew0
    hW1 := fun l b n s c fs _ _ hw => Spike.Lib.A64.WakeWf.hW1F (Ctx := Ctx) l b n s c fs hw
    ha := WakeOSide.ha_W hp i hpa hwp E
    hsplit := WakeOSplit.hsplit_W hp i hpa hwp E cT Dt ls0 _ inv0 _ inv1 h0t h0o h1t h1o
    hs0 := hs0
    hs1 := hs1
    hz0 := hz0
    hz1 := hz1
    hro := WakeOSide.hro_W hp i
    hd := hdj
    hw0 := hw0
    hw1 := hw1
    hP := Spike.Lib.WakeSrcOPrem.wake_hookOK arch
    hClc := WakeOD.hClc_W hp i E cT Dt ls0 _ inv0 _ inv1
    hsafe := Spike.Lib.WakeSrcOPrem.wake_srcSafeS arch _
    hrd := WakeOD.hrd_W hp i E cT Dt ls0 _ inv0 _ inv1 arch
    hwf := WakeOSide.hwf_W hp i
    hGpl := WakeOG.hGpl_gW hp i cT hpin2
    hok := WakeOD.hok_W hp i E cT Dt ls0 _ inv0 _ inv1 hc
    hB := WakeOD.hB_W hp i E cT Dt ls0 _ inv0 _ inv1 hB
    hdt := hdt
    hinit := hinit
    hti0 := WakeOSide.hti0_W hp i hpa hd E (WakeOAb.hab0_W hp i hpa hwp hlo E) (WakeOAb.hac0_W hp i hpa hwp hlo E) }

end Prem

end Spike.Lib.WakeOPremW

/-- info: 'Spike.Lib.WakeOPremW.oPrem_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeOPremW.oPrem_W
