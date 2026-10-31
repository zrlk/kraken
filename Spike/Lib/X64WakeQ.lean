/-
**wake.w on x86-64: the concrete relation data** (hello plan 1.6), the
x86-64 twin of `Spike/Lib/WakeQ.lean`. `wakeQ` fixes the fields of `WakeRel` that `WakeAssembly` pins by an
equation, so that each of those equations is `rfl`:

- `PT0 := WakeM0.PT0 M` (`hPT0`), `KR := WakeKR.KR r0 r1` (`hKR`),
  `own := X64WakeOwnX.wakeOwnXW T W` (`hown`);
- `PT1 := WakeW1.PT1 D` (`WCompat.pt1`), `atUnpk := WakeW1.atUnpk`,
  `atTexit := WakeW1.atTexit`;
- `C w := helloC (cT w) (cS w) wakePassT Knobs.all arch (D.cw w)`, so
  `WCompat.C` and `hpT` (`passT := wakePassT`) hold by `rfl`; `mviewS`,
  `obS` are `helloC`'s, the real `Promises.storeMview`/`storeOb` of the
  worker's `store rel c 1` (the review guard of `WakeRel.C`).

The rest (`R1`, `ι`, `SR`, the flag's words `cT`/`cS`, `pT`, `P`, `G`) are
parameters. `hwf_ofPlaceOK`: the layout `(RuntimeLayout.ofPlaceW hp i).Λ`
is well formed (`PlaceW.wf_link_of_placeW`).

**Unlike AArch64**: the target store point `passT : State → Prop` is a
parameter of `wakeQ` (A64 fixes it to `A64.Flow.Worker.Wake.Pass.wakePassT`),
the x86-64 `WakePass` not being twinned yet; `hpT` reads `= passT`. The
instance passes the x86-64 `wakePassT` once it lands. The layout is
`RuntimeLayout.ofPlaceWX` at `PlaceWX` (`PlaceWX.wf_link_of_placeWX`). The
owned words are `X64WakeOwnX.wakeOwnXW T W` (A64: `WakeOwn.wakeOwn`, none):
main owns its TCB self word `⟨T, 8⟩`, the worker its `⟨W, 8⟩` (X64-OwnW), so
`wakeQ` takes the two self words `T W` (after `passT`).
-/
import Spike.Lib.X64WakeAssembly
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeOwnXW

namespace Spike.Lib.X64WakeQ

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WorkerSrc

/-- **wake's relation data**: the pinned fields fixed, the rest given. -/
def wakeQ (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (ι : Type) (SR : ι → SpawnRec)
    (cT : ι → Loc) (cS : ι → WeakMem.Address) (pT : ι → Loc) (P : ι → Inv2Params isa)
    (G : ι → Loc → Val → Prop) (M : X64WakeM0.MSide ι) (D : X64WakeW1.WSide ι) (r0 r1 : ι → Range)
    (passT : State → Prop) (T W : BitVec 64) : WakeRel where
  R1 := R1
  ι := ι
  SR := SR
  C w := helloC (cT w) (cS w) passT Promises.Knobs.all arch (D.cw w)
  pT := pT
  P := P
  G := G
  own := X64WakeOwnX.wakeOwnXW T W
  PT0 := X64WakeM0.PT0 M
  PT1 := X64WakeW1.PT1 D
  KR := X64WakeKR.KR r0 r1
  atUnpk := X64WakeW1.atUnpk
  atTexit := X64WakeW1.atTexit

section Rfl

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {ι : Type} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {P : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {M : X64WakeM0.MSide ι} {D : X64WakeW1.WSide ι} {r0 r1 : ι → Range}
  {passT : State → Prop} {T W : BitVec 64}

/-- The pinned fields of `wakeQ`, each `rfl`: `WakeAssembly`'s `hPT0`,
`hKR`, `hown`, `wCompat_of`'s `pt1`, `atUnpk`, `atTexit`, `C`, `hpT`. -/
theorem hPT0 : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).PT0 = X64WakeM0.PT0 M := rfl
theorem hKR : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).KR = X64WakeKR.KR r0 r1 := rfl
theorem hown : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).own = X64WakeOwnX.wakeOwnXW T W := rfl
theorem pt1 : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).PT1 = X64WakeW1.PT1 D := rfl
theorem atUnpk : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).atUnpk = X64WakeW1.atUnpk := rfl
theorem atTexit : (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).atTexit = X64WakeW1.atTexit := rfl
theorem hC : ∀ w, (wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).C w =
    helloC ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).C w).cT
      ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).C w).cS
      ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).C w).passT Promises.Knobs.all arch (D.cw w) :=
  fun _ => rfl
theorem hpT : ∀ w, ((wakeQ arch R1 ι SR cT cS pT P G M D r0 r1 passT T W).C w).passT =
    passT := fun _ => rfl

end Rfl

/-- **The layout of a placed output is well formed** (`WakeObligations.hwf`
at `Λ := (RuntimeLayout.ofPlaceWX hp i).Λ`). -/
theorem hwf_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).Λ.WF :=
  PlaceWX.wf_link_of_placeWX (i := i) hp

end Spike.Lib.X64WakeQ

/-- info: 'Spike.Lib.X64WakeQ.hPT0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.hPT0

/-- info: 'Spike.Lib.X64WakeQ.hKR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.hKR

/-- info: 'Spike.Lib.X64WakeQ.hown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.hown

/-- info: 'Spike.Lib.X64WakeQ.pt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.pt1

/-- info: 'Spike.Lib.X64WakeQ.atUnpk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.atUnpk

/-- info: 'Spike.Lib.X64WakeQ.atTexit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.atTexit

/-- info: 'Spike.Lib.X64WakeQ.hC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.hC

/-- info: 'Spike.Lib.X64WakeQ.hpT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.hpT

/-- info: 'Spike.Lib.X64WakeQ.hwf_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeQ.hwf_ofPlaceOK
