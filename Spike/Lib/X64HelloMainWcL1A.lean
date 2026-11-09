/-
**`MainWcPS.hxa` at `invUH I` and the layout's `z`** (x86-64; the twin of `Spike/Lib/A64HelloMainWcL1A.lean`):
the own-generic pieces of `Level1IU.h1_level1Ug`'s `hP` (`MainGlueS.MainWcPS`) that `X64HelloMainWcL1AX`'s
`hP_level1X` and `X64HelloMainWcL1XX`'s `hxa_IUX` build on, at the level's memory sides at the fragment `invUH I`
(`I` asked only with the child's stack `r1Of` unmapped):
- `hxa` (`hxa_IU`): the landing's arena cell is the arena's (`AllocLand`, from `bXH`'s allocator fact: `off = 8`,
  one unit at least, two cells), and with `r1Of` unmapped `I`'s, from `MainWcL1X.hxa_L1` at `LandR1U.HLand2U`.

- `hxa_IU`: `MainWcPS.hxa` at `invUH I` from `HLand2U` at `I`'s `xa`.
- `hzL`: the layout's `z` from the certificate table's `i0`.

The root's `hP` and `h1` are at `ownGHXW` (`X64HelloMainWcL1AX`: `hP_level1X`, `h1_level1PX`); the producers of
`hP`'s other fields are `MainWcL1RX.hW_L1X`, `MainWcL1R.hbp_L1`/`hsl_L1`, `MainWcL1W.hra_jpL`,
`MainWcL1B.hbuf_L1`, `RdSrcL1`'s rows, `Level1.jpT_tp`, `MainWcL1Wj.hWp_L1PX`/`hWs_L1PX`,
`MainWcL1Q.hlim_L1`/`hbox_L1`/`hcell0_L1`, `Land.jr1LH_loc` and `MainWcL1Hq.hq_L1`.

## Differences from the AArch64 version

- `MainWcPS` is x86-64's: the last block's controls past the publication `J4x` (`RdSrcL1.jC5`, with `hpubx`,
  `hlocx`), and `hbp`/`hsl` (`.x15`'s `%rbp` and the saved `%rbp` it restores, `MainWcL1R.hbp_L1`/`hsl_L1`).
- The region is `RS helloLsw TOP` (AArch64 `swR TOP (-helloLsw) 0`), the caller's TCB slot `-16` (AArch64 `-80`),
  the thread pointer `tpOf (tcbS Ly)`; `hxa` is on `wc_main`'s frame based at the saved `%rbp`
  (`(wcR R D).fp (-8)`).
- The root's `hP`/`h1` (AArch64 `hP_level1`/`h1_level1P` at `ownGH`) are at `ownGHXW` in `X64HelloMainWcL1AX`.
-/
import Spike.Lib.X64HelloLevel1IU
import Spike.Lib.X64HelloLevel1M
import Spike.Lib.X64HelloMainWcL1R
import Spike.Lib.X64HelloMainWcL1Wj
import Spike.Lib.X64HelloMainWcL1Q
import Spike.Lib.X64HelloMainWcL1Hq
import Spike.Lib.X64HelloMainWcL1B
import Spike.Lib.X64HelloMainWcL1X

namespace Spike.Lib.X64.HelloPh.MainWcL1A

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Sem.X64 (cellsOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib (FragS Frag MemSide PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1 (mWC mRdJ0)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.X64.Flow.HelloWc (bXH)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH invUH)
open Spike.Lib.X64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.Level1I (XR)
open Spike.Lib.X64.HelloPh.RdPlS (RdImms)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64WakeLoadT (L0T ls0T tcb0)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloMainPreSrc (newTerm)
open Spike.Lib.X64HelloSrc (helloSrc)

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
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

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
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-! ## `hxa` at `invUH I` -/

/-- **`MainWcPS.hxa` at `invUH I`** (module doc): a box landing of `wc_main` at the level's memory side at
`invUH I` is at a cell the arena hands out (`AllocLand`: `bXH`'s offset `8`, one unit at least, two cells), and with
`r1Of` unmapped in `I` (`MainWcL1X.hxa_L1` at `HLand2U`, `hX`). -/
theorem hxa_IU {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS}
    (hX : Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) I l b n []).xa)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    ∀ (m1 : MachineData) (σ1 : FAS) l' A s c, Spike.Lib.X64ConsumerA.upd (LB) l b l' = none →
      At (Ly).exe (Ly).endPc ((wcR (RM) helloD).fp (-8))
        (wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1)
        (bXH ((MS1) (IU) l b n []) (_root_.Executable.labels (Ly).exe).label
          (wcJ0 (mWC (_root_.Executable.labels (Ly).exe).label σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)
          l' A) s c →
      TP (TV) s → ((MS1) (IU) l b n []).xa l' A 1 s c := by
  intro m1 σ1 l' A s c hl h ht
  have hU := Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_xa (ms := unXa ((MS1) I l b n []) (R1))
    (ms' := (MS1) (IU) l b n []) rfl h
  refine ⟨?_, fun hu => (Spike.Lib.X64.HelloPh.MainWcL1X.hxa_L1 hpw i0 E rd ls l b n hX hslot m1 σ1 l' A s c hl
    hU ht hu).2⟩
  obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := h
  have hf : ((MS1) (IU) l b n []).off 1 q.1.τ = 8 :=
    Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hu : 1 ≤ ((MS1) (IU) l b n []).units 1 q.1.τ :=
    Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hcl : 2 ≤ ((MS1) (IU) l b n []).cells := show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  show ((MS1) (IU) l b n []).heap + 8 ≤ A ∧ A + 8 * 1 ≤ ((MS1) (IU) l b n []).heap + 16 * ((MS1) (IU) l b n []).cells ∧
    1 + 1 ≤ ((MS1) (IU) l b n []).cells
  rw [hf] at hAo; omega

/-! ## The layout's `z` -/

/-- **The layout's `z` at `newTerm` from the certificate table's** (`IH`'s `z` is `i0`'s off the read's
entries; `HabCtlA.habCtlHA_jr1L`'s step). -/
theorem hzL (hz : i0 newTerm "z" 0 = some 0) : (Ly).Λ.imms newTerm "z" 0 = some 0 := by
  show Spike.Lib.X64.HelloImms.immsH Λ0 i0 newTerm "z" 0 = some 0
  unfold Spike.Lib.X64.HelloImms.immsH
  split
  · next h => exact absurd h.2.1 (by decide)
  · exact hz

end Spike.Lib.X64.HelloPh.MainWcL1A

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.hxa_IU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.hxa_IU

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.hzL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.hzL

