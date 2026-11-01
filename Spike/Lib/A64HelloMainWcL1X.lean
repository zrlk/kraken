/-
**`MainWcPS.hxa` at level 1** (AArch64; `Level1I.hP`'s field): `wc_main`'s box landings `bXH` under
main's thread pointer are allocations the level's memory side continues in, from carried landing
`LandR1U.HLand2U` at the level's `xa`: each such landing, for a caller holding main's TCB at its slot `-80`
(`hslot`), is one of `GsH1`'s (`Land.GsH1`, at the first stack's top). `HLand2U` asks only at landing states with
the child's stack unmapped (`U r1Of`), so the memory side here is `KeepUn.unXa (msOfA …) r1Of` (its landings asked
only with `U r1Of`); `KeepUn`'s segment lemma carries `U r1Of` back to `msOfA …`.

At the root `HLand2U … ((MS1) (I3 …) []).xa` is `LandR1U.hland2_ofU` (`RootHP.hland2_boxMRU` from `H2StmtH`); here
it is a premise, the level's invariant `I` generic.

- `at_bXH_of_xa`: `bXH` does not read the memory side's `xa`;
- `hxa_L1`: the statement.
-/
import Spike.Lib.A64HelloLandR1U
import Spike.Lib.A64HelloMainGlueS

namespace Spike.Lib.A64.HelloPh.MainWcL1X

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.A64.Flow.HelloWc (bXH)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The level's labels. -/
local notation "L1" => Spike.Lib.A64ConsumerA.upd (LB) l b

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The level's memory side at the invariant `I`, no frame (`Level1I`'s `MS1 l b n []`). -/
local notation "MS" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.HelloGOf2H.gWH hpw TI (Spike.Lib.WakeHG.cTW hpw TI))
  (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s)
  (AR) I (L1) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) []

/-- **The box's landing does not read `xa`**: a state at `bXH` under `ms` with `xa` replaced is at `bXH` under
`ms` (`HelloWc.at_bXH_of_tpXa`'s twin for any `xa`). -/
theorem at_bXH_of_xa {ms : MemSide isaLSE2} {X : WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1 : FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : At exe endPc R F (bXH { ms with xa := X } (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, h1, h2, h3⟩

variable {I : InvS} {σC : FAS}

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- **`MainWcPS.hxa` at level 1** (module doc): at the level's memory side with its landings asked only with the
child's stack unmapped (`KeepUn.unXa (MS) r1Of`), from `HLand2U` at the level's `xa` (`hX`), the caller's slot
`-80` main's TCB (`hslot`). -/
theorem hxa_L1
    (hX : Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n (MS).xa)
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) :
    ∀ (m1 : MachineData) (σ1 : FAS) l' A s c, (L1) l' = none →
      At (Ly).exe (Ly).endPc (wcR (swR (TOP) (-helloLsw) 0) helloD)
        (wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) helloLsw 0#64 (TOP)) m1 σ1)
        (bXH (Spike.Lib.A64.KeepUn.unXa (MS) (R1)) (_root_.Executable.labels (Ly).exe).label
          (wcJ0 (mWC (_root_.Executable.labels (Ly).exe).label σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)
          l' A) s c →
      TP (TV) s → (Spike.Lib.A64.KeepUn.unXa (MS) (R1)).xa l' A 1 s c :=
  fun m1 σ1 l' A s c hl h ht hu => hX _ ⟨TOP, σC, m1, σ1, hslot, rfl⟩ l' A s c hl
    ⟨rfl, at_bXH_of_xa (X := (Spike.Lib.A64.KeepUn.unXa (MS) (R1)).xa) h, ht⟩ hu

end Spike.Lib.A64.HelloPh.MainWcL1X

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1X.hxa_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1X.hxa_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1X.at_bXH_of_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1X.at_bXH_of_xa
