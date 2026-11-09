/-
**`WakeO.OPrem` at `wakeD`** (x86-64): the pre-spawn premises
at the runtime's layout `L := RuntimeLayout.ofPlaceWX hp i`, the per-state
levels `W0W`, `W1W` (`X64WakeWf.W0`/`W1` at `wakeD`'s `own`, `ar`, `L0`,
`Cl` and the root's abort phases `AbW`, `AcW`), the closed fields
discharged:

- `ha` (`X64WakeOSide.ha_W`), `hsplit` (`X64WakeOSplit.hsplit_W`, from the
  take facts), the ranges (`X64WakeOSide.ranges_W`, given `hsub1`), `hro`,
  `hwf` (`X64WakeOSide.hro_W`, `hwf_W`);
- `hP`, `hsafe` (`X64WakeSrcOPrem.wake_hookOK`, `wake_srcSafeS`), `hrd`
  (`X64WakeOD.hrd_W`), `hClc` (`X64WakeOD.hClc_W`);
- `hGpl` (`X64WakeOG.hGpl_gW`, given `hpin2`), `hok` (`X64WakeOD.hok_W`,
  given `CtrZ`), `hB` (`X64WakeOD.hB_W`, a budget of `allocCells` cells);
- `hW0` (`X64WakeWf.hW0`, from the counter's row `hctr0` and the box's
  store `hnew0`), `hW1` (`X64WakeWf.hW1F`: `W1` writes no counter);
- `hti0` (`X64WakeOSide.hti0_W` at `X64WakeOAb.hab0_W`, `hac0_W`, given
  `hlo`).

Open, as premises: the segments `h0`, `h1` and take facts `h0t`, `h0o`,
`h1t`, `h1o`; the counter row `hctr0`, the box store `hnew0` and the write
tail `hdt` (`X64WakeWf.hdtW` at `DtW`); the load's relation `hinit`
(`X64WakePreAsm.wake_init`).

x86-64 twin of `Spike/Lib/WakeOPremW.lean` (same names, namespace
`Spike.Lib.X64.WakeOPremW`).

**Unlike AArch64**: the assembly is a parameter `{asm : Asm}` (A64:
`SccCertificate.asm`); `oPrem_W`'s `hpa`, `hwp` are `cellsOf asm = some
o.prog`, `= some wakeCells` (A64: `textProgram … = .ok o.prog`, `.ok
wakeProg`) and `hd` is `dataSections asm.text = some o.secs`; `hlo` is at
`X64.WakePh.lo`.
-/
import Spike.Lib.X64WakeO
import Spike.Lib.X64WakeOSplit
import Spike.Lib.X64WakeOAb
import Spike.Lib.X64WakeSrcOPrem
import Spike.Lib.X64WakeWf
import Spike.Lib.X64WakeX0

namespace Spike.Lib.X64.WakeOPremW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX FragS FrameRun)
open SccCode (wakeCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}

/-- **The level before the allocation** at `wakeD`'s choices (`W0`, its
per-state facts `X0W` at the take pc `X64WakeOSide.aW`), for the assembly
`asm`. -/
def W0W (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Entry)
    (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize) (frM : TermRun.Frame) : FragS isa :=
  Spike.Lib.X64.WakeWf.W0 (RuntimeLayout.ofPlaceWX hp i).Λ
    ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ)
    (Spike.Lib.X64.WakePh.ownGXW (RuntimeLayout.ofPlaceWX hp i)
      (Spike.Lib.X64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceWX hp i).lab))
    (WakeOD.arW hp i) wakeSrc Dt (WakeOD.AbW hp i) (WakeOD.ClW hp i)
    (WakeOD.AcW hp i) Ctx (Spike.Lib.X64WakeLoadT.L0T (RuntimeLayout.ofPlaceWX hp i).Λ)
    (Spike.Lib.X64WakeLoadT.ls0T ls0) frM
    (Spike.Lib.X64.WakeWf.X0W (RuntimeLayout.ofPlaceWX hp i) (X64WakeOSide.aW hp i E))

/-- **The level after the allocation** at `wakeD`'s choices (`W1`), for the
assembly `asm`. -/
def W1W (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (E : Entry)
    (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize) :
    WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  Spike.Lib.X64.WakeWf.W1 (RuntimeLayout.ofPlaceWX hp i).Λ
    ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ)
    (Spike.Lib.X64.WakePh.ownGXW (RuntimeLayout.ofPlaceWX hp i)
      (Spike.Lib.X64.Rt.Reserve.ntA (RuntimeLayout.ofPlaceWX hp i).lab))
    (WakeOD.arW hp i) wakeSrc Dt (WakeOD.AbW hp i) (WakeOD.ClW hp i)
    (WakeOD.AcW hp i) Ctx (Spike.Lib.X64WakeLoadT.L0T (RuntimeLayout.ofPlaceWX hp i).Λ)
    (Spike.Lib.X64WakeLoadT.ls0T ls0)

section Prem

variable (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (arch : WeakMem.Arch) (E : Entry) (cT : Loc) (Dt : State → Prop) (ls0 : Lsize) (Ctx : FragS isa)
  (frM : TermRun.Frame) (inv0 : FragS isa) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- `wakeD` at the levels. -/
local notation "D" =>
  WakeOD.wakeD hp i E cT Dt ls0 (W0W asm hp i E Dt Ctx ls0 frM) inv0 (W1W asm hp i E Dt Ctx ls0) inv1

set_option hygiene false in
/-- The entry's marks. -/
local notation "μE" => (target (kernel 2) E).marks asm (Ly).Λ

/-- **`OPrem` at `wakeD`** (see the module doc). -/
theorem oPrem_W (hpa : cellsOf asm = some o.prog)
    (hwp : cellsOf asm = some wakeCells) (hd : dataSections asm.text = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {B : Budget} (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- OPEN: the segments and the take facts -/
    (h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) wakeSrc (X64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (fun _ _ _ _ _ => False) (X64ConsumerA.upd (D).L0 l b)
          (X64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n))
    (h0 : SegInvS (D).W0 (TakeCKS (D).a (D).Cl) wakeSrc (D).L0
      (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0)
      (D).inv0)
    (h0t : Spike.Lib.X64.Flow.WakeWc.H0Take (Ly) (X64WakeOSide.aW hp i E) inv0)
    (h0o : Spike.Lib.X64.Flow.WakeWc.H0TakeOwn (Ly) (X64WakeOSide.aW hp i E) inv0)
    (h1t : Spike.Lib.X64.Flow.WakeWc.H1Take (Ly) (X64WakeOSide.aW hp i E) inv1)
    (h1o : Spike.Lib.X64.Flow.WakeWc.H1TakeOwn (Ly) (X64WakeOSide.aW hp i E) inv1)
    /- OPEN: the counter's row, the write tail and the box's store -/
    (hctr0 : ∀ s c fs, inv0 s c fs → Ctx s c fs → WrAt s (D).ar.ctrLoc →
      ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0 fs')
        (fun s' c'' => PendA wakeSrc (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0 s' c'' fs') s c')
    (hnew0 : ∀ s c fs, inv0 s c fs → Ctx s c fs → ¬ WrAt s (D).ar.ctrLoc →
      ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
      ∀ L, WrAt s L → ¬ ArenaW (D).ar (D).L0 (D).ls0 c' L →
      NewStM wakeSrc (D).L0
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1) (D).L0 (D).ls0 fs')
        s c')
    (hdt : ∀ s buf n, (D).Dt s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n))
    /- OPEN: the load's relation -/
    (hinit : ∀ d : Cfg, (target (kernel 1) E).load asm (Ly).Λ = some d →
      ∃ s0, (wakeS arch).init s0 ∧
        RSAH (Ly).Λ (srcPo 2 arch wakeSrc) wakeSrc (D).G (D).own (I2 (D).ar (D).L0 (D).ls0 (D).inv0 (D).inv1)
          (HeldOk2 (Ly).Λ (D).r0 (D).r1) μE (D).ar d s0) :
    X64WakeO.OPrem arch (Ly).Λ B asm E (WakeOD.AbW hp i) (WakeOD.AcW hp i) D := by
  obtain ⟨hs0, hs1, hz0, hz1, hdj, hw0, hw1⟩ := X64WakeOSide.ranges_W hp i hsub1
  exact {
    h1 := h1
    h0 := h0
    hW0 := Spike.Lib.X64.WakeWf.hW0 hctr0 hnew0
    hW1 := fun l b n s c fs _ _ hw => Spike.Lib.X64.WakeWf.hW1F (Ctx := Ctx) l b n s c fs hw
    ha := X64WakeOSide.ha_W hp i hpa E
    hsplit := WakeOSplit.hsplit_W hp i hpa E cT Dt ls0 _ inv0 _ inv1 h0t h0o h1t h1o
    hs0 := hs0
    hs1 := hs1
    hz0 := hz0
    hz1 := hz1
    hro := X64WakeOSide.hro_W hp i
    hd := hdj
    hw0 := hw0
    hw1 := hw1
    hP := Spike.Lib.X64WakeSrcOPrem.wake_hookOK arch
    hClc := WakeOD.hClc_W hp i E cT Dt ls0 _ inv0 _ inv1
    hsafe := Spike.Lib.X64WakeSrcOPrem.wake_srcSafeS arch _
    hrd := WakeOD.hrd_W hp i E cT Dt ls0 _ inv0 _ inv1 arch
    hwf := X64WakeOSide.hwf_W hp i
    hGpl := X64WakeOG.hGpl_gW hp i cT hpin2
    hok := WakeOD.hok_W hp i E cT Dt ls0 _ inv0 _ inv1 hc
    hB := WakeOD.hB_W hp i E cT Dt ls0 _ inv0 _ inv1 hB
    hdt := hdt
    hinit := hinit
    hti0 := X64WakeOSide.hti0_W hp i hpa hd E (X64WakeOAb.hab0_W hp i hpa hwp hlo E)
      (X64WakeOAb.hac0_W hp i hpa hwp hlo E) }

end Prem

end Spike.Lib.X64.WakeOPremW

/-- info: 'Spike.Lib.X64.WakeOPremW.oPrem_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeOPremW.oPrem_W
