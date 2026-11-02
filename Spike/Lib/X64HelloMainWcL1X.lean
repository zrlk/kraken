/-
**`MainWcPS.hxa` at level 1** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1X.lean`, same names): `wc_main`'s
box landings `bXH` under main's thread pointer are allocations the level's memory side continues in, from the
carried landing `LandR1U.HLand2U` at the level's `xa`: each such landing, for a caller holding main's TCB at its
slot `-16` (`hslot`), is one of `GsH1`'s (`Land.GsH1`, at the first stack's top). `HLand2U` asks only at landing
states with the child's stack unmapped (`U r1Of`), so the memory side here is `KeepUn.unXa (msOfA …) r1Of`.

- `at_bXH_of_xa`: `bXH` does not read the memory side's `xa`;
- `hxa_L1`: the statement.

## Differences from the AArch64 version

- The caller's slot holding main's TCB is `-16` (AArch64 `-80`); the thread pointer is `tpOf (tcbS Ly)` and the
  first stack's top `topS Ly 0`.
- `scc_rt_main`'s region at the top is `MainGlue.RS helloLsw (topS Ly 0)` (AArch64 `swR … (-helloLsw) 0`), and
  the box's landing is on `wc_main`'s frame at the saved `%rbp`, `(wcR … helloD).fp (-8)` (as x86-64's
  `MainWcPS.hxa`; AArch64: `wcR … helloD`).
-/
import Spike.Lib.X64HelloLandR1U
import Spike.Lib.X64HelloMainGlueS

namespace Spike.Lib.X64.HelloPh.MainWcL1X

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib (MemSide Frag PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (pinA tpOf)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.X64.Flow.HelloWc (bXH)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

/-- **The box's landing does not read `xa`**: a state at `bXH` under `ms'` is at `bXH` under `ms` when `ms'` is
`ms` but for `xa`. -/
theorem at_bXH_of_xa {ms ms' : MemSide isa} (hms : ms' = { ms with xa := ms'.xa })
    {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1 : FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : At exe endPc R F (bXH ms' (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨X, rfl⟩ : ∃ X, ms' = { ms with xa := X } := ⟨_, hms⟩
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, h1, h2, h3⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize) (l : WeakMem.AllocLabel) (b n : Nat)

set_option hygiene false in
local notation "TI" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw TI

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw TI

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The level's labels. -/
local notation "L1" => Spike.Lib.X64ConsumerA.upd (LB) l b

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- The level's memory side at the invariant `I`, no frame (`Level1M`'s `MS1 l b n []`). -/
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
  (AR) I (L1) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []

variable {I : InvS} {σC : FAS}

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

/-- **`MainWcPS.hxa` at level 1** (module doc): at the level's memory side with its landings asked only with the
child's stack unmapped (`KeepUn.unXa (MS) r1Of`), from `HLand2U` at the level's `xa` (`hX`), the caller's slot
`-16` main's TCB (`hslot`). -/
theorem hxa_L1
    (hX : Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n (MS).xa)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) :
    ∀ (m1 : MachineData) (σ1 : FAS) l' A s c, (L1) l' = none →
      At (Ly).exe (Ly).endPc ((wcR (RS helloLsw (TOP)) helloD).fp (-8))
        (wcF (RS helloLsw (TOP)) helloD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 (TOP)) m1 σ1)
        (bXH (Spike.Lib.X64.KeepUn.unXa (MS) (R1)) (_root_.Executable.labels (Ly).exe).label
          (wcJ0 (mWC (_root_.Executable.labels (Ly).exe).label σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)
          l' A) s c →
      TP (TV) s → (Spike.Lib.X64.KeepUn.unXa (MS) (R1)).xa l' A 1 s c :=
  fun m1 σ1 l' A s c hl h ht hu => hX _ ⟨TOP, σC, m1, σ1, hslot, rfl⟩ l' A s c hl
    ⟨rfl, at_bXH_of_xa rfl h, ht⟩ hu

end Spike.Lib.X64.HelloPh.MainWcL1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_xa

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1X.hxa_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1X.hxa_L1
