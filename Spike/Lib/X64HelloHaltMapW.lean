/-
**hello.w on x86-64: the worker side's `hhalt1` and `hmapW`** (the twin of `Spike/Lib/HelloHaltMapW.lean`).

- `hhalt1_DR`: `hhalt1` at `helloDR` with `Z := ZHR exe kp`: a worker state is off the program's end (`Z0`'s last
  conjunct), so at a `syscall` its instruction runs (`X64WakeEndOff.exec_isSome_atSyscall`).
- `noTouch_outTS`: an `OutTS` row's step touches no location `K` leaves unmapped, from `LabMapped` wherever a
  frame run reaches (the rows' `pre`/`top` controls; `frame` and `fnc` steps touch nothing).
- `hmapW_ofH`: `hmapW` for any `WSideH` from its rows (`WSideH.closed`), `hmp` and `hlab`.
- `mp_msWH`: `X64HelloMsW.msWH`'s `mp` is mapped in `K0` (its first conjunct).
- `hmapW_flagH`: `hmapW_ofH` with `hlab` from a flag fact (`X64WakeLabMapped.labMapped_flagB`): at every control a
  frame run reaches from the invariant, every untagged locative accessed is the flag `cS w`, placed in a label at
  `b w` whose word `cT w` is shared.

## Differences from the AArch64 version

- `isa` (AArch64: `isaLSE2`); the end-off fact is `exec_isSome_atSyscall` (AArch64: `exec_isSome_atSvc`), the
  program `helloCells` (AArch64: `helloProg`); the modules are the `X64*` twins (`X64HelloWorkerRR`,
  `X64HelloZR`, `X64WakeMappedRow`, `X64WakeLabMapped`, `X64HelloMsW`).
- AArch64's `hhalt1_I` (at `HelloAssemblyI`'s placed instance) has no consumer and is not twinned.
-/
import Spike.Lib.X64HelloWorkerRR
import Spike.Lib.X64HelloZR
import Spike.Lib.X64HelloMsW
import Spike.Lib.X64WakeLabMapped
import Spike.Lib.X64WakeEndOff

namespace Spike.Lib.X64HelloHaltMapW

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloWorkerRR (helloDR helloDR_inv)
open Spike.Lib.X64.Flow.Worker (NNH)
open Spike.Lib.X64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.X64WakeMappedRow (LabPtr LabMapped noTouch_of_outL noTouch_of_outT)
open Spike.Lib.X64Consumer (K0)
open Scc.Cert.Rt.X64 (endOf)
open SccCode (helloCells)

/-! ## `hhalt1` -/

/-- **`hhalt1` at `helloDR`** (`Z := ZHR exe kp`, `endPc` the program's end): at a system call the worker's
instruction runs. -/
theorem hhalt1_DR {ι : Type} {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hend : endPc = endOf exe helloCells kp) {SR : ι → SpawnRec}
    {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → List TermRun.Frame → MemSide isa}
    {P X : ι → FragS isa} {hK : ∀ w fs, (ms w fs).K = some abi}
    {hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
      (fun _ _ _ => False)}
    {cw : ι → TermRun.Word} {bufL : ι → WeakMem.AllocLabel} {nB mB : ι → Nat} :
    ∀ w s c fs, (helloDR exe endPc SR lbl ms P (fun _ => ZHR exe kp) X hK hseg cw bufL nB mB).Wi w s c fs →
      abi.atSys s = true → (isa.exec s).isSome := by
  intro w s c fs h ha
  obtain ⟨⟨he, hn, -, -⟩, -, _, _, -, hz⟩ :=
    helloDR_inv exe endPc SR lbl ms P (fun _ => ZHR exe kp) X hK hseg cw bufL nB mB w s c fs h
  exact Spike.Lib.X64.Flow.Worker.Wake.EndOff.exec_isSome_atSyscall (he ▸ hv) ha
    (by rw [hn, hend]; exact hz.1.1.2.2.2)

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

/-- **`hmapW` for a frame-aware worker side** from its rows: the memory sides at the kernel ABI (`hK`), their
`mp` mapped in `K0 Λ` (`hmp`), the label words mapped at every control a frame run reaches (`hlab`). -/
theorem hmapW_ofH {ι : Type} {D : WSideH ι} {Λ : Scc.Sem.Layout} (hK : ∀ w fs, (D.ms w fs).K = some abi)
    (hmp : ∀ w fs L wr, (D.ms w fs).mp L wr → mapped (K0 Λ) wr L = true)
    (hlab : ∀ w s c fs, D.Wi w s c fs → ∀ c₁ fs₁, FrameRun helloSrc (c, fs) (c₁, fs₁) →
      LabMapped (D.lbl w) (K0 Λ) c₁) :
    ∀ w s c fs, D.Wi w s c fs → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => mapped (K0 Λ) w l = false) e :=
  fun w s c fs hi hs _ he => noTouch_outTS (D.closed w s c fs hi) (hmp w)
    (fun fs K' hK' => by rw [hK w fs] at hK'; cases hK'; exact hs) (hlab w s c fs hi) he

/-- **`msWH`'s `mp` is mapped in `K0`** (`X64HelloMs.helloMs`' first conjunct). -/
theorem mp_msWH {ι : Type} {L : Spike.Lib.X64.Rt.RuntimeLayout} {G : ι → Loc → Val → Prop} {SR : ι → SpawnRec}
    (w : ι) {Lc : Loc} {wr : Bool} (h : (Spike.Lib.X64HelloMsW.msWH L G SR w).mp Lc wr) :
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
    ∀ w s c fs, D.Wi w s c fs → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => mapped (K0 Λ) w l = false) e :=
  hmapW_ofH hK hmp fun w s c fs hi c₁ fs₁ hr =>
    Spike.Lib.X64WakeLabMapped.labMapped_flagB (hflag w s c fs hi c₁ fs₁ hr) (hl w) (hT w) (hsh w)

end Spike.Lib.X64HelloHaltMapW

/-- info: 'Spike.Lib.X64HelloHaltMapW.hhalt1_DR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHaltMapW.hhalt1_DR

/-- info: 'Spike.Lib.X64HelloHaltMapW.noTouch_outTS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHaltMapW.noTouch_outTS

/-- info: 'Spike.Lib.X64HelloHaltMapW.hmapW_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHaltMapW.hmapW_ofH

/-- info: 'Spike.Lib.X64HelloHaltMapW.hmapW_flagH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHaltMapW.hmapW_flagH
