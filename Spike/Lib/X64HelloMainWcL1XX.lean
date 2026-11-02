/-
**`MainWcPS.hxa` at level 1 at `ownGHXW`** (x86-64 only): `MainWcL1X.hxa_L1` and `MainWcL1A.hxa_IU` with the
level's memory side's owned words `ownGHXW Ly ntA` (main's TCB word owned besides `ownGH`'s). The landing
`LandR1U.HLand2U` is stated at landings `bXH` of `ref1H` (at `ownGH`); `bXH` reads neither the memory side's `xa`
nor its `own`, so a landing at `ownGHXW` is one of `HLand2U`'s.

- `MainWcL1X.at_bXH_of_ownXa`: `bXH` reads neither the memory side's `xa` nor its `own`.
- `MainWcL1X.hxa_L1X`: `hxa_L1` at `ownGHXW` (`KeepUn.unXa (msOfA … ownGHXW …) r1Of`).
- `MainWcL1A.hxa_IUX`: `hxa_IU` at `ownGHXW` (the level's memory side at `invUH I`).

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there, so its level is at `ownGH` only
(`A64HelloMainWcL1X`, `A64HelloMainWcL1A`).
-/
import Spike.Lib.X64HelloMainWcL1A

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

/-- **The box's landing reads neither `xa` nor `own`**: a state at `bXH` under `ms'` is at `bXH` under `ms` when
`ms'` is `ms` but for `xa` and `own` (`at_bXH_of_xa` with the owned words too). -/
theorem at_bXH_of_ownXa {ms ms' : MemSide isa} (hms : ms' = { ms with xa := ms'.xa, own := ms'.own })
    {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J1 : FAS → Spike.Lib.Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : At exe endPc R F (bXH ms' (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨X, Y, rfl⟩ : ∃ X Y, ms' = { ms with xa := X, own := Y } := ⟨_, _, hms⟩
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
/-- The level's memory side at the invariant `I`, no frame, at `ownGHXW`. -/
local notation "MSX" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw TI (Spike.Lib.X64WakeHG.cTW hpw TI))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
  (AR) I (L1) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []

variable {I : InvS} {σC : FAS}

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

/-- **`MainWcPS.hxa` at level 1 at `ownGHXW`** (`hxa_L1` at the memory side owning `ownGHXW`'s words): from
`HLand2U` at the level's `xa` (`hX`), the caller's slot `-16` main's TCB (`hslot`). -/
theorem hxa_L1X
    (hX : Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n (MSX).xa)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) :
    ∀ (m1 : MachineData) (σ1 : FAS) l' A s c, (L1) l' = none →
      At (Ly).exe (Ly).endPc ((wcR (RS helloLsw (TOP)) helloD).fp (-8))
        (wcF (RS helloLsw (TOP)) helloD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 (TOP)) m1 σ1)
        (bXH (Spike.Lib.X64.KeepUn.unXa (MSX) (R1)) (_root_.Executable.labels (Ly).exe).label
          (wcJ0 (mWC (_root_.Executable.labels (Ly).exe).label σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)
          l' A) s c →
      TP (TV) s → (Spike.Lib.X64.KeepUn.unXa (MSX) (R1)).xa l' A 1 s c :=
  fun m1 σ1 l' A s c hl h ht hu => hX _ ⟨TOP, σC, m1, σ1, hslot, rfl⟩ l' A s c hl
    ⟨rfl, at_bXH_of_ownXa rfl h, ht⟩ hu

end Spike.Lib.X64.HelloPh.MainWcL1X

namespace Spike.Lib.X64.HelloPh.MainWcL1A

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (FragS Frag MemSide PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.X64.Flow.HelloWc (bXH)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepUn (unXa)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (invUH)
open Spike.Lib.X64WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The child's stack. -/
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `scc_rt_main`'s region at the first stack's top. -/
local notation "RM" => RS helloLsw (TOP)

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`, at
`ownGHXW`. -/
local notation "MS1X" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-- **`MainWcPS.hxa` at `invUH I` at `ownGHXW`** (`hxa_IU` at the level's memory side owning `ownGHXW`'s words):
the landing's arena cell is the arena's, and with `r1Of` unmapped `I`'s, from `MainWcL1X.hxa_L1X` at
`LandR1U.HLand2U`. -/
theorem hxa_IUX {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS}
    (hX : Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1X) I l b n []).xa)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    ∀ (m1 : MachineData) (σ1 : FAS) l' A s c, Spike.Lib.X64ConsumerA.upd (LB) l b l' = none →
      At (Ly).exe (Ly).endPc ((wcR (RM) helloD).fp (-8))
        (wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1)
        (bXH ((MS1X) (IU) l b n []) (_root_.Executable.labels (Ly).exe).label
          (wcJ0 (mWC (_root_.Executable.labels (Ly).exe).label σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)
          l' A) s c →
      TP (TV) s → ((MS1X) (IU) l b n []).xa l' A 1 s c := by
  intro m1 σ1 l' A s c hl h ht
  have hU := Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_xa (ms := unXa ((MS1X) I l b n []) (R1))
    (ms' := (MS1X) (IU) l b n []) rfl h
  refine ⟨?_, fun hu => (Spike.Lib.X64.HelloPh.MainWcL1X.hxa_L1X hpw i0 E rd ls l b n hX hslot m1 σ1 l' A s c hl
    hU ht hu).2⟩
  obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := h
  have hf : ((MS1X) (IU) l b n []).off 1 q.1.τ = 8 :=
    Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hu : 1 ≤ ((MS1X) (IU) l b n []).units 1 q.1.τ :=
    Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hcl : 2 ≤ ((MS1X) (IU) l b n []).cells := show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  show ((MS1X) (IU) l b n []).heap + 8 ≤ A ∧
    A + 8 * 1 ≤ ((MS1X) (IU) l b n []).heap + 16 * ((MS1X) (IU) l b n []).cells ∧
    1 + 1 ≤ ((MS1X) (IU) l b n []).cells
  rw [hf] at hAo; omega

end Spike.Lib.X64.HelloPh.MainWcL1A

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_ownXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_ownXa

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1X.hxa_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1X.hxa_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.hxa_IUX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.hxa_IUX
