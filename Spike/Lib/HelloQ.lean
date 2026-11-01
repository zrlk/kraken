/-
**hello.w on AArch64: the concrete relation data** (the twin of
`Spike.Lib.WakeQ` at hello's worker side `HelloW1.WSideH`). `helloQ` fixes
the fields of `WakeRel` that hello's assembly pins by an equation, so that
each of those equations is `rfl`:

- `PT0 := WakeM0.PT0 M` (`hPT0`; main's side past the spawn is wake's),
  `KR := HelloKRE.KRHE D r0 r1` (`hKR`; `A64HelloWriteK.KRH` (no `exit` in the
  source trace in place of an empty trace) and the worker's `write` link `Lk`,
  design (i′)), `own := WakeOwn.wakeOwn` (`hown`);
- `PT1 := HelloEmitPh.PT1hE D` (`WCompatH.pt1`; `PT1h` or mid-`write`),
  `atUnpk := WakeW1.atUnpk`,
  `atTexit := WakeW1.atTexit` (hello's worker tail is wake's);
- `C w := helloC (cT w) (cS w) passT Knobs.all arch (D.cw w)`, so
  `WCompatH.C` and `hpT` hold by `rfl`; `mviewS`, `obS` are `helloC`'s, the
  real `Promises.storeMview`/`storeOb` of the worker's `store rel c 1` (the
  review guard of `WakeRel.C`).

The target store point `passT` is a parameter (hello's listing places the
worker's `stlr` at its own labels; `WakeQ` fixes wake's `wakePassT`). The
rest (`R1`, `ι`, `SR`, the flag's words `cT`/`cS`, `pT`, `P`, `G`) are
parameters, as in `WakeQ`.
-/
import Spike.Lib.WakeQ
import Spike.Lib.HelloW1Print
import Spike.Lib.A64HelloWriteK
import Spike.Lib.HelloKRE

namespace Spike.Lib.HelloQ

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WorkerSrc
open Spike.Lib.HelloW1 (WSideH PT1h)

/-- **hello's relation data**: the pinned fields fixed, the rest given. -/
def helloQ (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (ι : Type) (SR : ι → SpawnRec)
    (cT : ι → Loc) (cS : ι → WeakMem.Address) (pT : ι → Loc) (P : ι → Inv2Params isaLSE2)
    (G : ι → Loc → Val → Prop) (passT : State → Prop) (M : WakeM0.MSide ι) (D : WSideH ι)
    (r0 r1 : ι → Range) : WakeRel where
  R1 := R1
  ι := ι
  SR := SR
  C w := helloC (cT w) (cS w) passT Promises.Knobs.all arch (D.cw w)
  pT := pT
  P := P
  G := G
  own := WakeOwn.wakeOwn
  PT0 := WakeM0.PT0 M
  PT1 := HelloEmitPh.PT1hE D
  KR := HelloKRE.KRHE D r0 r1
  atUnpk := WakeW1.atUnpk
  atTexit := WakeW1.atTexit

section Rfl

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {ι : Type} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {P : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range}

/-- The pinned fields of `helloQ`, each `rfl`. -/
theorem hPT0 : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT0 = WakeM0.PT0 M := rfl
theorem hKR : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).KR = HelloKRE.KRHE D r0 r1 := rfl
theorem hown : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own = WakeOwn.wakeOwn := rfl
theorem pt1 : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT1 = HelloEmitPh.PT1hE D := rfl
theorem atUnpk : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).atUnpk = WakeW1.atUnpk := rfl
theorem atTexit : (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).atTexit = WakeW1.atTexit := rfl
theorem hC : ∀ w, (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w =
    helloC ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).cT
      ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).cS
      ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).passT Promises.Knobs.all arch (D.cw w) :=
  fun _ => rfl
theorem hpT : ∀ w, ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).passT = passT := fun _ => rfl

/-- **`WCompatH.ownCov`** at `helloQ`: the worker owns no word. -/
theorem ownCov : ∀ w s fs L v, (L, v) ∈ (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 1 s fs →
    ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).P w).cov 1 L := fun _ _ _ _ _ h => by cases h

/-- **`WCompatH.ownDisj`** at `helloQ`: no thread owns a word. -/
theorem ownDisj : ∀ w s0 fs0 s fs L v v',
    (L, v) ∈ (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 0 s0 fs0 →
    (L, v') ∈ (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).own w 1 s fs → False :=
  fun _ _ _ _ _ _ _ _ h => by cases h

/-- **`WCompatH.pt0`** at `helloQ`: main's `PT0` does not read the memories
(`WakeM0.PT0.mem`). -/
theorem pt0 : ∀ w tm sm t0 s0 tm' sm', (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT0 w tm sm t0 s0 →
    WakeW1.W1Mem ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).P w)
      ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).cS tm sm tm' sm' →
    (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).PT0 w tm' sm' t0 s0 :=
  fun _ _ _ _ _ _ _ h _ => h

end Rfl

end Spike.Lib.HelloQ
