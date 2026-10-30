/-
**wake.w on AArch64: the concrete relation data**. `wakeQ` fixes the fields of `WakeRel` that `WakeAssembly` pins by an
equation, so that each of those equations is `rfl`:

- `PT0 := WakeM0.PT0 M` (`hPT0`), `KR := WakeKR.KR r0 r1` (`hKR`),
  `own := WakeOwn.wakeOwn` (`hown`);
- `PT1 := WakeW1.PT1 D` (`WCompat.pt1`), `atUnpk := WakeW1.atUnpk`,
  `atTexit := WakeW1.atTexit`;
- `C w := helloC (cT w) (cS w) wakePassT Knobs.all arch (D.cw w)`, so
  `WCompat.C` and `hpT` (`passT := wakePassT`) hold by `rfl`; `mviewS`,
  `obS` are `helloC`'s, the real `Promises.storeMview`/`storeOb` of the
  worker's `store rel c 1` (the review guard of `WakeRel.C`).

The rest (`R1`, `ι`, `SR`, the flag's words `cT`/`cS`, `pT`, `P`, `G`) are
parameters. `hwf_ofPlaceOK`: the layout `(RuntimeLayout.ofPlaceW hp i).Λ`
is well formed (`PlaceW.wf_link_of_placeW`).
-/
import Spike.Lib.WakeAssembly
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeQ

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WorkerSrc

/-- **wake's relation data**: the pinned fields fixed, the rest given. -/
def wakeQ (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (ι : Type) (SR : ι → SpawnRec)
    (cT : ι → Loc) (cS : ι → WeakMem.Address) (pT : ι → Loc) (P : ι → Inv2Params isaLSE2)
    (G : ι → Loc → Val → Prop) (M : WakeM0.MSide ι) (D : WakeW1.WSide ι) (r0 r1 : ι → Range) : WakeRel where
  R1 := R1
  ι := ι
  SR := SR
  C w := helloC (cT w) (cS w) Spike.Lib.A64.Flow.Worker.Wake.Pass.wakePassT Promises.Knobs.all arch (D.cw w)
  pT := pT
  P := P
  G := G
  own := WakeOwn.wakeOwn
  PT0 := WakeM0.PT0 M
  PT1 := WakeW1.PT1 D
  KR := WakeKR.KR r0 r1
  atUnpk := WakeW1.atUnpk
  atTexit := WakeW1.atTexit

section Rfl

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {ι : Type} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {P : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {M : WakeM0.MSide ι} {D : WakeW1.WSide ι} {r0 r1 : ι → Range}

/-- The pinned fields of `wakeQ`, each `rfl`: `WakeAssembly`'s `hPT0`,
`hKR`, `hown`, `wCompat_of`'s `pt1`, `atUnpk`, `atTexit`, `C`, `hpT`. -/
theorem hPT0 : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).PT0 = WakeM0.PT0 M := rfl
theorem hKR : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).KR = WakeKR.KR r0 r1 := rfl
theorem hown : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).own = WakeOwn.wakeOwn := rfl
theorem pt1 : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).PT1 = WakeW1.PT1 D := rfl
theorem atUnpk : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).atUnpk = WakeW1.atUnpk := rfl
theorem atTexit : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).atTexit = WakeW1.atTexit := rfl
theorem hC : ∀ w, (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).C w =
    helloC ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).C w).cT
      ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).C w).cS
      ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).C w).passT Promises.Knobs.all arch (D.cw w) :=
  fun _ => rfl
theorem hpT : ∀ w, ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1).C w).passT =
    Spike.Lib.A64.Flow.Worker.Wake.Pass.wakePassT := fun _ => rfl

end Rfl

/-- **The layout of a placed output is well formed** (`WakeObligations.hwf`
at `Λ := (RuntimeLayout.ofPlaceW hp i).Λ`). -/
theorem hwf_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i).Λ.WF :=
  PlaceW.wf_link_of_placeW (i := i) hp

/-- info: 'Spike.Lib.WakeQ.hwf_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hwf_ofPlaceOK

end Spike.Lib.WakeQ
