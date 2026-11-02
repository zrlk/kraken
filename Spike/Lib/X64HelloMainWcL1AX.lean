/-
**`Level1IU.h1_level1Ug`'s `hP` assembled at `ownGHXW`** (x86-64 only; the `ownGHXW` counterpart of
`X64HelloMainWcL1A`): `MainGlueS.MainWcPS` at the level `Level1I.W1Rg … (ownGHXW Ly ntA)` and its memory sides at
`ownGHXW` at the fragment `invUH I`, the root's rodata entry `J1 := mRdJ0 J'`, from the `ownGHXW` producers:
- `hW`: `MainWcL1RX.hW_L1X`; `hmem`: `hbuf_L1X`;
- `hWp`, `hWs`: `MainWcL1Wj.hWp_L1PX`, `hWs_L1PX`;
- `hxa`: `MainWcL1A.hxa_IUX` (`X64HelloMainWcL1XX`);
and `X64HelloMainWcL1A`'s own-generic ones for the other fields (`hbp`, `hsl`, `hra`, `RdSrcL1`'s rows, `hJpT`,
`hlim`, `hloc`, `hq`, `hbox`, `hcell0`). The heap abort's path inside the level (`h1_level1Ug`'s `hP0`) is
`HabLftX.hP0X`.

- `bandIn_wcAbX`: `wc_main`'s heap abort's callee region on the pool.
- `hbuf_L1X`: `MainWcL1B.hbuf_L1` at `msUHg ownGHXW`.
- `hP_level1X`: `h1_level1Ug`'s `hP` at `ownGHXW`.
- `h1_level1PX`: `h1_level1Ug` at `ownGHXW` with `hP`, `hJ1`, `hmem0`, `hP0` discharged.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there, so its root's `h1` is at `ownGH` only
(`A64HelloMainWcL1A.h1_level1P`). Against `X64HelloMainWcL1A.h1_level1P`: the level and its memory sides are at
`ownGHXW`, the landing's entry is `StartH0H1.RdLandHg … ownGHXW`, `hX` is at the level's `xa` at `ownGHXW`, and the
heap abort's path is `HabLftX.hP0X` (inside `W0` at `ownGHXW`; `h1_level1U` closes it at `ownGH` in
`Level1HA.hB_landA`).
-/
import Spike.Lib.X64HelloMainWcL1XX
import Spike.Lib.X64HelloMainWcL1WjX
import Spike.Lib.X64HelloMainWcL1RX
import Spike.Lib.X64HelloHabLftX

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
open Spike.Lib.X64 (bAddr)
open Spike.Lib.X64.WakePh (BandIn)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.X64.Flow.HelloWc (bXH)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.KeepUn (U unXa)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH invUH)
open Spike.Lib.X64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.X64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.X64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.X64.HelloPh.Level1I (W1R XR)
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
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

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
local notation "J'" => rdJH (Ly).lab (RM) (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- Level 0's memory sides at a fragment `J` (the landing's). -/
local notation "MSU" => fun (J : Spike.Lib.X64ConsumerS.InvS) => msUH (asm := asm) hpw i0 E rd J ls

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- The root data's owned words (main's and the worker's TCB words appended to `ownGH`). -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT)

set_option hygiene false in
/-- Level 0's memory sides at a fragment `J` at `ownGHXW`. -/
local notation "MSUX" => fun (J : Spike.Lib.X64ConsumerS.InvS) =>
  Spike.Lib.X64.HelloPh.StartH0U.msUHg (asm := asm) hpw i0 (OX) E rd J ls

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`, at
`ownGHXW`. -/
local notation "MS1X" => fun (J : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => (OX) s)
    (AR) J (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- The level at the root's choices at `ownGHXW`. -/
local notation "W1X" => Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hpw i0 E rd ls (OX)

/-! ## The heap abort's band -/

/-- **`wc_main`'s heap abort's callee region is on the pool** (`HabLftX.hP0X`'s `hb`): `(wcR RM helloD).callee
(-312) (-24) 16`'s band `[-32, 8]` is `scc_rt_main`'s `[-424, -384]` (`HrdRootX.bandRS`). -/
theorem bandIn_wcAbX : BandIn (Ly) ((wcR (RM) helloD).callee (-304 - 8) (-24) 16) := by
  obtain ⟨hok, -, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hbRS : Spike.Lib.X64.WakePh.BandOnP (Ly) (RM) (-424) 8 :=
    Spike.Lib.X64.HelloPh.HrdRootX.bandRS (show (8 - helloLsw : Int) ≤ -424 by decide)
      (show helloLsw < 16384 by decide) hok
  intro k h1 h2
  have e : ((wcR (RM) helloD).callee (-304 - 8) (-24) 16).addr k = (RM).addr (-80 + (-304 - 8 + k)) := by
    rw [Spike.Lib.Region.callee_addr, Spike.Lib.Region.callee_addr]
  rw [e]; exact hbRS _ (by omega) (by omega)

/-! ## `hmem` at `ownGHXW` -/

/-- **`MainWcL1B.hbuf_L1` at `ownGHXW`**: at every `.x15` state of the level's invariant at `msUHg ownGHXW`, both
buffer words are box cells under `wc_rodata`'s frame condition at the start's `FS`. -/
theorem hbuf_L1X (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat} {m0 : MachineData} {σC : FAS} :
    ∀ σ0 c, JpT (JpL (R := RM) ((MSUX) I [FR]) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV) σ0 c →
      ∀ i : Int64, (i = 0 ∨ i = 8) →
        Spike.Lib.X64.HelloPh.WcW.BoxOkH (Ly).Λ (Ly) (NT)
          (Spike.Lib.X64.Flow.Hello1.mF (RM) (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m0 σC) (bAddr σ0.regs .rax i) := by
  intro σ0 c h
  have hpl := Spike.Lib.PlaceWX.link IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hpl
  have hu : ((MSUX) I [FR]).units 2 Spike.Lib.Hello1RodataSrc.τ8 = 3 := rfl
  refine Spike.Lib.X64.HelloPh.MainWcL1B.boxOkH_q (fun m hm => hm.1.1.1.wn) (Nat.le_refl _) ?_
    (Spike.Lib.X64.HelloPh.HrdArena.offH_own hpw i0 hA13)
    (Spike.Lib.X64.HelloPh.MainWcL1B.cellX0Q_jpL Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN hu h.1)
  show (Ly).Λ.heap.lo + 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size
  omega

/-! ## `hP` and the root's `h1` at `ownGHXW` -/

/-- **`hP_level1` at `ownGHXW`** (`Level1IU.h1_level1Ug`'s `hP` at `own := ownGHXW Ly ntA`): `MainWcPS` at
`W1Rg … ownGHXW` and the level's memory sides at `ownGHXW` at `invUH I`, from the `ownGHXW` producers
(`hW`: `MainWcL1RX.hW_L1X`; `hmem`: `hbuf_L1X`; `hWp`, `hWs`: `MainWcL1Wj.hWp_L1PX`, `hWs_L1PX`; `hxa`: `hxa_IUX`)
and `hP_level1`'s own-generic ones. -/
theorem hP_level1X
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    (hz : (Ly).Λ.imms newTerm "z" 0 = some 0)
    (hX : ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1X) I l b n []).xa) :
    ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS ((W1X) l b n) (KR) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
        ((MS1X) (IU) l b n) (Ly).exe (Ly).endPc (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := RM) ((MSUX) (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n) (TV))
        Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b) (TV) := by
  intro l b n m0 σC hl hb hslot
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hJ : ∀ σ c, Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b σ c →
      ∃ w0 w1 w2 mw, c = Spike.Lib.X64HelloMainPreSrc.c0H w0 w1 w2 mw := fun _ _ h => ⟨_, _, _, _, h.1.1⟩
  have hbuf := hbuf_L1X (asm := asm) hpw i0 E rd (IU) ls hA13 (l := l) (b := b) (n := n) (m0 := m0) (σC := σC)
  have hJp := Spike.Lib.X64.HelloPh.RdJpL.jpT_rb (L0 := LB) (R := RM)
    (ms₀ := (MSUX) (IU) [FR]) (lab := (Ly).lab) (J0 := mRdJ0 (J') σC) (J1 := mRdJ0 (J') σC) (l := l) (b := b)
    (w := n) (t := TV) (Spike.Lib.X64.HelloPh.RdJpL.rdJH_rdCN (lab := (Ly).lab) (J := JS (Ly) 0#64 c0S) (σC := σC))
  exact ⟨_, _, _, _, _, _, _, _, _, {
    hW := Spike.Lib.X64.HelloPh.MainWcL1RX.hW_L1X hpw i0 hpa hhp hlo0 hc hA13 hI himm hl
    hbp := fun _ _ h => Spike.Lib.X64.HelloPh.Level1.jpL_rbp h.1
    hra := fun σ0 c h => Spike.Lib.X64.HelloPh.MainWcL1W.hra_jpL h.1
    hmem := fun σ0 c h i hi => (hbuf σ0 c h i hi).2.1
    hr0 := Spike.Lib.X64.HelloPh.RdSrcL1.hr0_rd (l := l) hJp
    h1 := Spike.Lib.X64.HelloPh.RdSrcL1.h1_rd (l := l)
    h2 := Spike.Lib.X64.HelloPh.RdSrcL1.h2_rd (l := l)
    hr2 := Spike.Lib.X64.HelloPh.RdSrcL1.hr2_rd (l := l)
    h3 := Spike.Lib.X64.HelloPh.RdSrcL1.h3_rd (l := l)
    h4 := Spike.Lib.X64.HelloPh.RdSrcL1.h4_rd (l := l)
    hfen := Spike.Lib.X64.HelloPh.RdSrcL1.hfen_rd (l := l) (Spike.Lib.X64.WakeOD.arW_pub hpw IH)
    hpubx := Spike.Lib.X64.HelloPh.RdSrcL1.hpubx_rd (l := l)
    hlocx := Spike.Lib.X64.HelloPh.RdSrcL1.hlocx_rd (l := l)
    hedge := Spike.Lib.X64.HelloPh.RdSrcL1.hedge_rd (l := l)
    hsl := fun _ _ h => Spike.Lib.X64.HelloPh.MainWcL1R.jpL_slot8 h.1
    hJpT := Spike.Lib.X64.HelloPh.Level1.jpT_tp
    hWp := fun m1 σ1 => Spike.Lib.X64.HelloPh.MainWcL1Wj.hWp_L1PX hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1)
      hp hpa hhp hlo0 hc hA13 hz hl hslot
    hWs := fun m1 σ1 => Spike.Lib.X64.HelloPh.MainWcL1Wj.hWs_L1PX hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1)
      hp hpa hhp hlo0 hc hA13 hz hl hslot
    hlim := Spike.Lib.X64.HelloPh.MainWcL1Q.hlim_L1 hpw IH
      (Spike.Lib.X64.HelloPh.MainWcL1Q.rtFree_L1 hpw IH hstat ls hb)
    hloc := Spike.Lib.X64.HelloPh.Land.jr1LH_loc hpw i0 (tm := .tid)
      (by simp [Spike.Lib.X64.HelloPh.C0S.c0S_env, TermRun.evalAt, TermRun.lookupE])
    hq := Spike.Lib.X64.HelloPh.MainWcL1Hq.hq_L1 hpw IH hstat hc hpin2 hb hJ
    hbox := Spike.Lib.X64.HelloPh.MainWcL1Q.hbox_L1 hJ
    hcell0 := Spike.Lib.X64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH hJ
    hxa := hxa_IUX hpw i0 E rd I ls (hX l b n hl hb) hslot }⟩

/-- **The root's `h1` at `ownGHXW` with `hP` discharged** (`Level1IU.h1_level1Ug` at `own := ownGHXW Ly ntA`,
`J1 := mRdJ0 J'`, `hP_level1X`; `hJ1` by `Level1I.slot16_rdJ`, `hmem0` by `Level1I.hmem0_level1g`, the heap abort's
path inside the level `hP0` by `HabLftX.hP0X` (`ownGHXW`'s separation from A13, the band `bandIn_wcAbX`)). -/
theorem h1_level1PX
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    /- the certificate table's `z` at `newTerm` (at the root's table: `HabCtlA.hz_i0M`) -/
    (hz : i0 newTerm "z" 0 = some 0)
    /- the box store's landings at level 1 with `r1Of` unmapped, at `ownGHXW` -/
    (hX : ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1X) I l b n []).xa) :
    Spike.Lib.X64HelloPreA.H1StmtHF (W1X)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (AR) (LB) ((MS1X) I) (Ly)
      (Spike.Lib.X64.HelloPh.StartH0H1.RdLandHg (asm := asm) hpw i0 (OX) E rd I ls (mRdJ0 (J')))
      (Spike.Lib.X64HelloPreA.H1Gfp.inv1G (W1X) (XR hpw i0)
        (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (LB) ((MS1X) I)) [FR] := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab := Spike.Lib.X64HelloOInit.hlab_H hpw IH hpa hhp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : Spike.Lib.X64.WakePh.tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  obtain ⟨-, hR0, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hlo1 : (RS helloLsw (TOP)).lo ≤ -80 - helloD := by show (8 : Int) - helloLsw ≤ -80 - helloD; decide
  have hhi1 : (0 : Int) ≤ (RS helloLsw (TOP)).hi := by show (0 : Int) ≤ 8; decide
  have hD : (0 : Int) ≤ helloD := by decide
  have hR : (wcR (RS helloLsw (TOP)) helloD).OK :=
    Spike.Lib.Region.callee_ok hR0 (by omega) (by omega) (by omega) (by omega)
  exact Spike.Lib.X64.HelloPh.Level1IU.h1_level1Ug (own := OX) hpw i0 E rd I ls hpa hhp hlo0
    (Spike.Lib.X64.HelloPh.Level1I.slot16_rdJ hpw i0 (RM))
    (hP_level1X hpw i0 E rd I ls hpa hhp hlo0 hstat hc hA13 hpin2 hI himm (hzL hpw i0 hz) hX)
    (Spike.Lib.X64.HelloPh.Level1I.hmem0_level1g hpw i0 E rd I ls (own := fun s _ => (OX) s) hc) hz
    fun _ _ _ => Spike.Lib.X64.HelloPh.HabLftX.hP0X hprog hlo hlab (NT) hsep ha hW (bandIn_wcAbX hpw i0) hΛ
      hR (by show (-helloD : Int) ≤ -336; decide) (by show (-296 : Int) ≤ 8; decide) (.inl rfl) Spike.Lib.X64.HelloPh.ClH.cl
      (Spike.Lib.X64.HelloPh.HAbStub.x0WH_abort hlab rfl)

end Spike.Lib.X64.HelloPh.MainWcL1A

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.bandIn_wcAbX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.bandIn_wcAbX

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.hbuf_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.hbuf_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.hP_level1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.hP_level1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1A.h1_level1PX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1A.h1_level1PX
