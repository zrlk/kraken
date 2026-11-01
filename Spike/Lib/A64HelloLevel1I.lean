/-
**hello's level 1 at the root's choices** (AArch64): `h1`'s landing
segment (`H1Gfp.h1StmtHF_of_segWS`'s `hB`) from rodata's landing `StartH0H1.RdLandH` at `[FR]`, inside the level
`HelloWf.W1H` at the root's choices (context `Land.CtxR1H`, the start's facts `X0WH`), under the root's take move
`TakeCKS`, at the level's memory sides `msOfA … I (upd LB l b) (updN (ls0T ls) l n)`.

The landing (`RdLandH`, at the start's stack top `v`, the caller's `m0`, `σC`) is `Level1.LandF` with `TP`; from
there `Level1.land_segWSL` (`wc_rodata`'s `.sp0` at `JpT (JpL …) TV`, `wc_main` to its box allocation's heap
abort), then `StartH0CL.hello_hab_closedL` at the level's labels closes the abort. Only `v` at the first stack's top
occurs (`FS`, `Land.fstable_FS`); elsewhere the landing is empty.

Left (named premises, per `l b n`):
- `hP`: `MainGlueS.MainWcPS` at the level (the field map: `RdWfSF`, `WcWfR`, `HelloRdCf`, `RdPl*`/`WcPl`, …;
next rows);
- `hmem0`: the box allocation's words free at `FS` (`Alloc.hmem_of_wordsNone`, next row);
- `hhabctl`: `HabCtl.HabCtlH` at level 1 (row `5h-S-habctl-L1`; blocked on the abort path's placement,
  resolved by `HabCtlH'` placing `c0H`'s words at `wc_main`'s spilled frame slots).

- `W1R`, `XR`: the level and its per-state facts at the root's choices.
- `slot80_rdJ`: at rodata's entry `J1 := mRdJ0 J'` the caller's slot `-80` is main's TCB (`hB_land`'s `hJ1`; `hP`
  is asked only at such callers, as `Land.GsH1` pins them).
- `hB_land`: `hB` (the landing segment, no exit).
- `h1_level1`: `H1StmtHF` at `inv1G`, the root's `h1` (`StartH0U1.hst0_ofHU1_i0`).
-/
import Spike.Lib.A64HelloLevel1T
import Spike.Lib.A64HelloStartH0CL
import Spike.Lib.A64HelloStartH0H1
import Spike.Lib.A64HelloStartH0B
import Spike.Lib.A64HelloH1Gfp
import Spike.Lib.A64HelloLand1
import Spike.Lib.A64HelloW1H

namespace Spike.Lib.A64.HelloPh.Level1I

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (abi textProgram)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib (FragS Frag MemSide SegWS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Hello1 (mWC mRdJ0)
open Spike.Lib.A64.Flow.HelloM (wcJ0)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.A64.HelloPh.Level1 (LandF JpL JpT)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- Level 0's memory sides (the landing's). -/
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls

set_option hygiene false in
/-- The level's memory sides after rodata's allocation of `l` at `b`, `n` words, at the frames `fs`. -/
local notation "MS1" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) I (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

/-- **The level at the root's choices**: `W1H` with the context `CtxR1H`, the frame `FR`, the start's facts. -/
abbrev W1R : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  Spike.Lib.A64.HelloWf.W1H (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly))
    (Spike.Lib.A64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls) (FR) (X0WH (Ly) (AX))

/-- **The level's per-state facts** (`h1StmtHF_of_segWS`'s `X`): the start's `X0WH`. -/
abbrev XR : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 := fun _ _ _ s _ _ => X0WH (Ly) (AX) s

/-- **`hB_land`'s `hJ1` at rodata's entry `J1 := mRdJ0 J'`**: the caller `σC` at `wc_rodata`'s call is at `mNC`,
whose slot `-80` holds the entry's `x0`, main's TCB `pinA + 8` (`JS`). -/
theorem slot80_rdJ : ∀ σC σ c, mRdJ0 (J') σC σ c →
    σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 := by
  rintro σC σ c ⟨-, -, c', ⟨⟨σe, ⟨-, hx0⟩, -, -, h80, -, -⟩, -⟩⟩
  exact h80.trans hx0

set_option maxHeartbeats 1600000 in
/-- **Level 1's landing segment at the root's choices** (`h1StmtHF_of_segWS`'s `hB`; module doc): from rodata's
landing `RdLandH` at `[FR]`, inside `W1R ∧ XR` under `TakeCKS`, with no exit. -/
theorem hB_land {J1 : FAS → FAS → Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    /- the landing's caller holds main's TCB at its slot `-80` (`slot80_rdJ` at `J1 := mRdJ0 J'`) -/
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- `MainWcPS` at the level: `wc_rodata`'s rest from `.sp0` at `JpT (JpL …) TV` and `wc_main` to its box
    allocation, at the first stack's top -/
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b) ((MS1) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    /- the box allocation's words free at `FS` -/
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) l b n []).ctr ∨ ∃ o, o + ((MS1) l b n []).units q.n q.τ ≤ ((MS1) l b n []).cells ∧
        a.toNat = q.hdrAt ((MS1) l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    /- named premise: the controls' facts at `wc_main`'s box abort at level 1 -/
    (hhabctl : ∀ l b n (σC σ1 : FAS), HabCtlH ((MS1) l b n []) (Ly).lab helloSrc (Ly).Λ
      (Spike.Lib.A64ConsumerA.upd (LB) l b) (AR) []
      (wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)) :
    ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      SegWS (fun s c fs => W1R (asm := asm) hpw i0 E rd ls l b n s c fs ∧ XR hpw i0 l b n s c fs)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) l b n) (Frag.at (RdLandH (asm := asm) hpw i0 E rd I ls J1 l b n) [FR]) (fun _ _ _ => False) := by
  intro l b n hl hb
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hpS : Lays (Ly).exe SccCode.helloProg (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = endOf (Ly).exe SccCode.helloProg (Ly).pfx := by
    show endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  obtain ⟨hok, hal, hF⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  have hC := Spike.Lib.A64.HelloPh.StartH0CL.hello_hab_closedL hpw IH (E := E) (rd := rd) (I := I)
    (Ctx := Spike.Lib.A64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n)
    (ls0 := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) (frM := FR) (t := TV)
    (Jr1 := fun _ _ _ => Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) hpa hhp hlo0
    fun _ _ σC σ1 => hhabctl l b n σC σ1
  refine (((SegWS.exists_pre (P := fun g : BitVec 64 × MachineData × FAS =>
      Frag.at (fun s c => LandF ((MSU) [FR]) (Ly).exe (Ly).endPc (swR g.1 (-helloLsw) 0)
        (FS (Ly) (RS) helloLsw 0#64 g.1) (mRdJ0 (J') g.2.2) (J1 g.2.2) g.2.1 g.2.2 l b n s c ∧ TP (TV) s) [FR])
      fun ⟨v, m0, σC⟩ => ?_).mono_K fun s c fs hW s' =>
        Spike.Lib.A64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).mono_W
      fun s c fs h => ⟨h, h.2.1⟩).mono_pre
    fun s c fs ⟨⟨v, m0, σC, q, F', h1, h2, hA, _, ht⟩, hfs⟩ => ⟨(v, m0, σC), ⟨⟨q, F', h1, h2, hA⟩, ht⟩, hfs⟩
  by_cases hv : v = TOP
  case neg =>
    refine SegWS.empty fun s c fs h => ?_
    obtain ⟨⟨⟨q, F', h1, -, -, -, -, -, σ, -, hF', -⟩, -⟩, -⟩ := h
    exact hv (h1 _ hF').1.2.1.1
  subst hv
  by_cases hs : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64
  case neg =>
    refine SegWS.empty fun s c fs h => ?_
    obtain ⟨⟨⟨q, F', -, h2, -, -, -, -, σ, -, hF', -⟩, -⟩, -⟩ := h
    obtain ⟨mC, σ', c', -, ⟨⟨σe, hJe, -⟩, -⟩, -⟩ := h2 _ hF'
    exact hs (hJ1 _ _ _ hJe)
  obtain ⟨Jp', Jx1, J2, J2', J3, J4, J5, Jr, hPv⟩ := hP l b n m0 σC hl hb hs
  refine (Spike.Lib.A64.HelloPh.Level1.land_segWSL rfl rfl hpS hendS (D := helloD) (by decide) (by decide) hF hok hal
    (show (-helloLsw : Int) ≤ -288 by decide) (show (-helloLsw : Int) ≤ -80 - helloD by decide)
    (show (0 : Int) ≤ 0 by decide) rfl hPv (hmem0 l b n)).seq ?_
  exact hC.mono_pre fun s c fs ⟨⟨m1, σ1, h, ht⟩, hfs⟩ => ⟨⟨_, m0, σC, m1, σ1, h, ht⟩, hfs⟩

/-- **The root's `h1`** (`StartH0U1.hst0_ofHU1_i0`'s): `H1StmtHF` at the level `W1R`, its facts `XR`, the take move
`TakeCKS`, the level's memory sides, rodata's landing `RdLandH` at `[FR]`, with the invariant `inv1G` (the greatest
closed invariant inside `W1R ∧ XR`; `H1Gfp.h1StmtHF_of_segWS` at `hB_land`, `XR` off the clone's pc). -/
theorem h1_level1 {J1 : FAS → FAS → Ctl → Prop}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo)
    /- the landing's caller holds main's TCB at its slot `-80` (`slot80_rdJ` at `J1 := mRdJ0 J'`) -/
    (hJ1 : ∀ σC σ c, J1 σC σ c → σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hP : ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b) ((MS1) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) [FR]) (Ly).lab (mRdJ0 (J') σC) (J1 σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV))
    (hmem0 : ∀ l b n, ∀ q : Call, q.OKB ((MS1) l b n []) (Ly).lab → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ((MS1) l b n []).ctr ∨ ∃ o, o + ((MS1) l b n []).units q.n q.τ ≤ ((MS1) l b n []).cells ∧
        a.toNat = q.hdrAt ((MS1) l b n []) o) →
      ∀ m, FS (Ly) (RS) helloLsw 0#64 (TOP) m → Mem.loadInt m.dmem a 8 = none)
    (hhabctl : ∀ l b n (σC σ1 : FAS), HabCtlH ((MS1) l b n []) (Ly).lab helloSrc (Ly).Λ
      (Spike.Lib.A64ConsumerA.upd (LB) l b) (AR) []
      (wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)) :
    Spike.Lib.HelloPreA.H1StmtHF (W1R (asm := asm) hpw i0 E rd ls) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)))
      (AR) (LB)
      (MS1) (Ly) (RdLandH (asm := asm) hpw i0 E rd I ls J1)
      (Spike.Lib.HelloPreA.H1Gfp.inv1G (W1R (asm := asm) hpw i0 E rd ls) (XR hpw i0)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB) (MS1)) [FR] :=
  Spike.Lib.HelloPreA.H1Gfp.h1StmtHF_of_segWS (fun _ _ _ _ _ _ h => h.1)
    (hB_land hpw i0 E rd I ls hpa hhp hlo0 hJ1 hP hmem0 hhabctl)

end Spike.Lib.A64.HelloPh.Level1I

/-- info: 'Spike.Lib.A64.HelloPh.Level1I.slot80_rdJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1I.slot80_rdJ

/-- info: 'Spike.Lib.A64.HelloPh.Level1I.hB_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1I.hB_land

/-- info: 'Spike.Lib.A64.HelloPh.Level1I.h1_level1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1I.h1_level1
