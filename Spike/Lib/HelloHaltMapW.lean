/-
**hello.w's worker at a system call runs, and off one touches only mapped locations** (AArch64;
B8-genP-hmapW; the twins of `A64WakeEndOff.hhalt1_of` and
`WakeMappedRow.hW_of` at hello's frame-aware worker side `HelloW1.WSideH`): `HelloProgress.post_progressH`'s
premises `hhalt1` and `hmapW`.

- `hhalt1_DR`: at `HelloWorkerRR.helloDR` with the segment's control fact `Z := fun _ => ZHR exe kp` and
  `endPc` the program's end, every state of the invariant at a system call runs an instruction: `helloDR_inv`'s
  `NNH` pins `s.exe`, `s.endPc`, and its pending run into `ZHR` carries `Z0`'s pc off the end, so the `svc` faults
  (`EndOff.exec_isSome_atSvc`).
- `hhalt1_I`: the same at the placed instance's worker side `HelloAssemblyI.DH` (`Z := ZI`, `HelloSegI`).
- `noTouch_outTS`: an `OutTS` row's step touches no location `K` leaves unmapped, given the memory sides' `mp`
  mapped in `K` at every frame stack, the state off a system call, and `LabMapped` at every control a frame run
  reaches (the rows' `pre`/`top` controls; `frame` and `fnc` steps touch nothing).
- `hmapW_ofH`: `hmapW` for any `WSideH` from its rows (`WSideH.closed`), `hmp` and `hlab`.
- `mp_msWH`: `HelloMsW.msWH`'s `mp` is mapped in `K0` (its first conjunct).
- `hmapW_flagH`: `hmapW_ofH` with `hlab` from a flag fact (`WakeLabMapped.labMapped_flagB`): at every control a
  frame run reaches from the invariant, every untagged locative accessed is the flag `cS w`, placed in a label at
  `b w` whose word `cT w` is shared.

Open at the instance (row B8-genP-hmapW-flag): the flag fact `hflag` at the worker's controls. `helloDR`'s
invariant carries no control fact beyond `Pend helloSrc (Z w)`, and `ZHR` none about `LabPtr`; wake gets it from
`wakeZX`'s `LabPtr` conjunct (`A64WakeCtlZ`), per node of the segment.
-/
import Spike.Lib.HelloSegI
import Spike.Lib.HelloProgress
import Spike.Lib.WakeLabMapped
import Spike.Lib.A64WakeEndOff

namespace Spike.Lib.HelloHaltMapW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloWorkerRR (helloDR helloDR_inv)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.WakeMappedRow (LabPtr LabMapped noTouch_of_outL noTouch_of_outT)
open Spike.Lib.A64Consumer (K0)
open Scc.Cert.Rt.A64 (endOf)
open SccCode (helloProg)

/-! ## `hhalt1` -/

/-- **`hhalt1` at `helloDR`** (`Z := ZHR exe kp`, `endPc` the program's end): at a system call the worker's
instruction runs. -/
theorem hhalt1_DR {ι : Type} {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hend : endPc = endOf exe helloProg kp) {SR : ι → SpawnRec}
    {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → List TermRun.Frame → MemSide isaLSE2}
    {P X : ι → FragS isaLSE2} {hK : ∀ w fs, (ms w fs).K = some abi}
    {hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
      (fun _ _ _ => False)}
    {cw : ι → TermRun.Word} {bufL : ι → WeakMem.AllocLabel} {nB mB : ι → Nat} :
    ∀ w s c fs, (helloDR exe endPc SR lbl ms P (fun _ => ZHR exe kp) X hK hseg cw bufL nB mB).Wi w s c fs →
      abi.atSys s = true → (isaLSE2.exec s).isSome := by
  intro w s c fs h ha
  obtain ⟨⟨he, hn, -, -⟩, -, _, _, -, hz⟩ :=
    helloDR_inv exe endPc SR lbl ms P (fun _ => ZHR exe kp) X hK hseg cw bufL nB mB w s c fs h
  exact Spike.Lib.A64.Flow.Worker.Wake.EndOff.exec_isSome_atSvc (he ▸ hv) ha
    (by rw [hn, hend]; exact hz.1.1.2.2.2)

/-- info: 'Spike.Lib.HelloHaltMapW.hhalt1_DR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hhalt1_DR

section Inst

open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH DH ZI)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`hhalt1` at the placed instance's worker side** (`HelloAssemblyI`'s premise at `Z := ZI`, any `G0`, `P`,
`hseg`). -/
theorem hhalt1_I (G0 : ιH hp i → Loc → Val → Prop) (P X : ιH hp i → FragS isaLSE2)
    (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ ZI hp i w s c fs) (X w) helloSrc
      (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w)
      (fun _ _ _ => False)) :
    ∀ w s c fs, (DH hp i G0 P (ZI hp i) X hseg).Wi w s c fs → abi.atSys s = true → (isaLSE2.exec s).isSome :=
  haveI := (LH hp i).valid
  hhalt1_DR rfl

/-- info: 'Spike.Lib.HelloHaltMapW.hhalt1_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hhalt1_I

end Inst

/-! ## `hmapW` -/

/-- **An `OutTS` row's step touches no location `K` leaves unmapped**: the memory sides' `mp` mapped in `K`
(`hmp`), the state off a system call of their kernel model (`hat`), and `LabMapped` at every control a frame run
reaches (`hlab`). -/
theorem noTouch_outTS {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide I} {X : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    {K : KState} (h : OutTS p lbl ms X s c fs) (hmp : ∀ fs L w, (ms fs).mp L w → mapped K w L = true)
    (hat : ∀ fs K', (ms fs).K = some K' → K'.atSys s = false)
    (hlab : ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → LabMapped lbl K c₁) {e : EvTree I.State}
    (he : I.exec s = some e) : ¬ Touches (fun l w => mapped K w l = false) e := by
  cases h with
  | pre c₁ fs₁ hr ho => exact noTouch_of_outL ho (hmp fs₁) (hat fs₁) (hlab c₁ fs₁ hr) he
  | frame s' c' fs' hx _ _ => rw [hx] at he; cases he; nofun
  | fnc k s' c' fs' hx _ _ =>
    rw [hx] at he; cases he
    intro h
    cases h with
    | fence h => cases h
  | top c₁ hr ho => exact noTouch_of_outT ho (hmp []) (hat []) (hlab c₁ [] hr) he

/-- info: 'Spike.Lib.HelloHaltMapW.noTouch_outTS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms noTouch_outTS

/-- **`hmapW` for a frame-aware worker side** from its rows: the memory sides at the kernel ABI (`hK`), their
`mp` mapped in `K0 Λ` (`hmp`), the label words mapped at every control a frame run reaches (`hlab`). -/
theorem hmapW_ofH {ι : Type} {D : WSideH ι} {Λ : Scc.Sem.Layout} (hK : ∀ w fs, (D.ms w fs).K = some abi)
    (hmp : ∀ w fs L wr, (D.ms w fs).mp L wr → mapped (K0 Λ) wr L = true)
    (hlab : ∀ w s c fs, D.Wi w s c fs → ∀ c₁ fs₁, FrameRun helloSrc (c, fs) (c₁, fs₁) →
      LabMapped (D.lbl w) (K0 Λ) c₁) :
    ∀ w s c fs, D.Wi w s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => mapped (K0 Λ) w l = false) e :=
  fun w s c fs hi hs _ he => noTouch_outTS (D.closed w s c fs hi) (hmp w)
    (fun fs K' hK' => by rw [hK w fs] at hK'; cases hK'; exact hs) (hlab w s c fs hi) he

/-- info: 'Spike.Lib.HelloHaltMapW.hmapW_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hmapW_ofH

/-- **`msWH`'s `mp` is mapped in `K0`** (`HelloMs.helloMs`' first conjunct). -/
theorem mp_msWH {ι : Type} {L : Spike.Lib.A64.Rt.RuntimeLayout} {G : ι → Loc → Val → Prop} {SR : ι → SpawnRec}
    (w : ι) {Lc : Loc} {wr : Bool} (h : (Spike.Lib.HelloMsW.msWH L G SR w).mp Lc wr) :
    mapped (K0 L.Λ) wr Lc = true :=
  h.1

/-- **`hmapW` from the flag**: `hmapW_ofH` with `LabMapped` by `labMapped_flagB`, given that at every control a
frame run reaches from the invariant every untagged locative accessed is `cS w` (`hflag`), `cS w`'s label placed
at `b w` under `D.lbl w` (`hl`), its word `cT w` (`hT`) shared (`hsh`). -/
theorem hmapW_flagH {ι : Type} {D : WSideH ι} {Λ : Scc.Sem.Layout} (hK : ∀ w fs, (D.ms w fs).K = some abi)
    (hmp : ∀ w fs L wr, (D.ms w fs).mp L wr → mapped (K0 Λ) wr L = true) {cS : ι → WeakMem.Address}
    {cT : ι → Loc} {b : ι → Nat}
    (hflag : ∀ w s c fs, D.Wi w s c fs → ∀ c₁ fs₁, FrameRun helloSrc (c, fs) (c₁, fs₁) →
      ∀ sa, LabPtr c₁ sa → sa = cS w)
    (hl : ∀ w, D.lbl w (cS w).label = some (b w)) (hT : ∀ w, cT w = wordLoc (b w + 8 * (cS w).offset))
    (hsh : ∀ w, Consumer1.LocIn Λ.shared (cT w)) :
    ∀ w s c fs, D.Wi w s c fs → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => mapped (K0 Λ) w l = false) e :=
  hmapW_ofH hK hmp fun w s c fs hi c₁ fs₁ hr =>
    Spike.Lib.WakeLabMapped.labMapped_flagB (hflag w s c fs hi c₁ fs₁ hr) (hl w) (hT w) (hsh w)

/-- info: 'Spike.Lib.HelloHaltMapW.hmapW_flagH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hmapW_flagH

end Spike.Lib.HelloHaltMapW
