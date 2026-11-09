/-
**`Level1IU.h1_level1U`'s `hP` assembled** (AArch64): `MainGlueS.MainWcPS` at the
level's memory sides at the fragment `invUH I` (`I` asked only with the child's stack `r1Of` unmapped), the root's
rodata entry `J1 := mRdJ0 J'`, from the level-1 producers, all generic in the fragment and so taken at `invUH I`:
- `hW`: `MainWcL1R.hW_L1`; `hra`, `hmem`: `MainWcL1W.hra_jpL`, `MainWcL1B.hbuf_L1`;
- `hr0` … `hedge`: `RdSrcL1`'s rows at `upd LB l b` (`hfen`'s publication `arW`'s);
- `hJpT`: `Level1.jpT_tp`; `hWp`, `hWs`: `MainWcL1Wj.hWp_L1P`, `hWs_L1P`;
- `hlim`: `MainWcL1Q.hlim_L1` (`rtFree_L1`); `hloc`: `HelloJr1.jr1L_loc` (`me`'s word in `c0S.env`);
- `hq`: `MainWcL1Hq.hq_L1`; `hbox`, `hcell0`: `MainWcL1Q.hbox_L1`, `hcell0_L1`;
- `hxa` (`hxa_IU`): the landing's arena cell is the arena's (`AllocLand`, from `bXH`'s allocator fact: `off = 8`,
  one unit at least, two cells), and with `r1Of` unmapped `I`'s, from `MainWcL1X.hxa_L1` at `LandR1U.HLand2U`.

- `hxa_IU`: `MainWcPS.hxa` at `invUH I` from `HLand2U` at `I`'s `xa`.
- `hP_level1`: `h1_level1U`'s `hP` at `J1 := mRdJ0 J'`.
- `hzL`: the layout's `z` from the certificate table's `i0`.
- `h1_level1P`: `h1_level1U` with `hP` discharged (`hJ1` by `Level1I.slot80_rdJ`, `hmem0` by
  `Level1I.hmem0_level1`); no control premise (the heap abort at `wXA`, `Level1HA.hB_landA`).
-/
import Spike.Lib.A64HelloLevel1IU
import Spike.Lib.A64HelloLevel1M
import Spike.Lib.A64HelloMainWcL1R
import Spike.Lib.A64HelloMainWcL1Wj
import Spike.Lib.A64HelloMainWcL1Q
import Spike.Lib.A64HelloMainWcL1Hq
import Spike.Lib.A64HelloMainWcL1X

namespace Spike.Lib.A64.HelloPh.MainWcL1A

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (abi textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib (FragS Frag MemSide SegWS)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Hello1 (mWC mRdJ0)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.A64.Flow.HelloWc (bXH)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH invUH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.A64.HelloPh.Level1 (JpL JpT)
open Spike.Lib.A64.HelloPh.Level1I (W1R XR)
open Spike.Lib.A64.HelloPh.RdSrcL1 (jP' jX1 jC2 jC2' jX3 jC4 jRet)
open Spike.Lib.A64.HelloPh.RdPlS (RdImms)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T ls0T tcb0)
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
/-- The child's stack. -/
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- The fragment `I` asked only with `r1Of` unmapped. -/
local notation "IU" => invUH hpw i0 I

set_option hygiene false in
/-- Level 0's memory sides at a fragment `J` (the landing's). -/
local notation "MSU" => fun (J : Spike.Lib.A64ConsumerS.InvS) => msUH (asm := asm) hpw i0 E rd J ls

set_option hygiene false in
/-- The level's memory sides at a fragment `J` after rodata's allocation of `l` at `b`, `n` words, at `fs`. -/
local notation "MS1" => fun (J : Spike.Lib.A64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
    (fs : List TermRun.Frame) =>
  Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
    (AR) J (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

/-! ## `hxa` at `invUH I` -/

/-- **`MainWcPS.hxa` at `invUH I`** (module doc): a box landing of `wc_main` at the level's memory side at
`invUH I` is at a cell the arena hands out (`AllocLand`: `bXH`'s offset `8`, one unit at least, two cells), and with
`r1Of` unmapped in `I` (`MainWcL1X.hxa_L1` at `HLand2U`, `hX`). -/
theorem hxa_IU {l : WeakMem.AllocLabel} {b n : Nat} {σC : FAS}
    (hX : Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) I l b n []).xa)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    ∀ (m1 : MachineData) (σ1 : FAS) l' A s c, Spike.Lib.A64ConsumerA.upd (LB) l b l' = none →
      At (Ly).exe (Ly).endPc (wcR (swR (TOP) (-helloLsw) 0) helloD)
        (wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1)
        (bXH ((MS1) (IU) l b n []) (_root_.Executable.labels (Ly).exe).label
          (wcJ0 (mWC (_root_.Executable.labels (Ly).exe).label σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1)
          l' A) s c →
      TP (TV) s → ((MS1) (IU) l b n []).xa l' A 1 s c := by
  intro m1 σ1 l' A s c hl h ht
  have hU := Spike.Lib.HelloHMid.at_bXH_ms (ms := (MS1) (IU) l b n [])
    (ms' := unXa ((MS1) I l b n []) (R1))
    (fun q hq => Spike.Lib.A64.HelloPh.Level1IU.okb_xa rfl hq) ⟨rfl, rfl, rfl, rfl⟩ h
  refine ⟨?_, fun hu => (Spike.Lib.A64.HelloPh.MainWcL1X.hxa_L1 hpw i0 E rd ls l b n hX hslot m1 σ1 l' A s c hl
    hU ht hu).2⟩
  obtain ⟨-, -, -, -, -, -, -, q, -, -, -, ob, hAo, hlt⟩ := h
  have hf : ((MS1) (IU) l b n []).off 1 q.1.τ = 8 :=
    Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q.2.toS.accs
  have hu : 1 ≤ ((MS1) (IU) l b n []).units 1 q.1.τ :=
    Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) q.2.toS.accs
  have hcl : 2 ≤ ((MS1) (IU) l b n []).cells := show 2 ≤ Scc.Cert.PlaceOK.allocCells by decide
  show ((MS1) (IU) l b n []).heap + 8 ≤ A ∧ A + 8 * 1 ≤ ((MS1) (IU) l b n []).heap + 16 * ((MS1) (IU) l b n []).cells ∧
    1 + 1 ≤ ((MS1) (IU) l b n []).cells
  rw [hf] at hAo; omega

/-! ## `hP` -/

/-- **`h1_level1U`'s `hP` at the root's rodata entry** (module doc): `MainWcPS` at `invUH I`, `J1 := mRdJ0 J'`,
`Jp'` … `J5` `RdSrcL1`'s at the level's labels, `Jr` `wc_rodata`'s return `JrRL` on the slice at `l`. -/
theorem hP_level1
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    /- the layout's immediates (loader; at the root's `iRdM`: `ImmsMe.rdImms_iRdM`, `hmeC_iRdM`, `HabCtlA.hz_i0M`) -/
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    (hz : (Ly).Λ.imms Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    /- the box store's landings at level 1 with `r1Of` unmapped (`RootHP.hland2_boxMRU` at `I3`) -/
    (hX : ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) I l b n []).xa) :
    ∀ l b n m0 σC, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 →
      ∃ Jp' Jx1 J2 J2' J3 J4 J5 Jr : FAS → Spike.Lib.Ctl → Prop,
      MainWcPS (W1R (asm := asm) hpw i0 E rd ls l b n) (KR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
        ((MS1) (IU) l b n)
        (Ly).exe (Ly).endPc (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) (FR) m0 σC
        (JpT (JpL (R := swR (TOP) (-helloLsw) 0) ((MSU) (IU) [FR]) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n)
          (TV))
        Jp' Jx1 J2 J2' J3 J4 J5 Jr (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b) (TV) := by
  intro l b n m0 σC hl hb hslot
  have hp : o.prog = SccCode.helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hJ : ∀ σ c, Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b σ c →
      ∃ w0 w1 w2 mw, c = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw := fun _ _ h => ⟨_, _, _, _, h.1⟩
  have hbuf := Spike.Lib.A64.HelloPh.MainWcL1B.hbuf_L1 (asm := asm) hpw i0 (E := E) (rd := rd) (I := IU) (ls := ls)
    hA13 (l := l) (b := b) (n := n) (m0 := m0) (σC := σC)
  have hJp := Spike.Lib.A64.HelloPh.RdJpL.jpT_rb (L0 := LB) (R := swR (TOP) (-helloLsw) 0)
    (ms₀ := (MSU) (IU) [FR]) (lab := (Ly).lab) (J0 := mRdJ0 (J') σC) (J1 := mRdJ0 (J') σC) (l := l) (b := b)
    (w := n) (t := TV) (Spike.Lib.A64.HelloPh.RdJpL.rdJH_rdCN (lab := (Ly).lab) (J := JS (Ly) 0#64 c0S) (σC := σC))
  exact ⟨_, _, _, _, _, _, _, _, {
    hW := Spike.Lib.A64.HelloPh.MainWcL1R.hW_L1 hpw i0 (E := E) (rd := rd) (I := IU) (ls := ls) hpa hhp hlo0 hc
      hA13 hI himm (m0 := m0) (σC := σC) (n := n) hl
    hra := fun σ0 c h => Spike.Lib.A64.HelloPh.MainWcL1W.hra_jpL h.1
    hmem := fun σ0 c h i hi => (hbuf σ0 c h i hi).2.1
    hr0 := Spike.Lib.A64.HelloPh.RdSrcL1.hr0_rd (l := l) hJp
    h1 := Spike.Lib.A64.HelloPh.RdSrcL1.h1_rd (l := l)
    h2 := Spike.Lib.A64.HelloPh.RdSrcL1.h2_rd (l := l)
    hr2 := Spike.Lib.A64.HelloPh.RdSrcL1.hr2_rd (l := l)
    h3 := Spike.Lib.A64.HelloPh.RdSrcL1.h3_rd (l := l)
    h4 := Spike.Lib.A64.HelloPh.RdSrcL1.h4_rd (l := l)
    hfen := Spike.Lib.A64.HelloPh.RdSrcL1.hfen_rd (l := l) (Spike.Lib.WakeOD.arW_pub hpw IH)
    hedge := Spike.Lib.A64.HelloPh.RdSrcL1.hedge_rd (l := l)
    hJpT := Spike.Lib.A64.HelloPh.Level1.jpT_tp
    hWp := fun m1 σ1 => Spike.Lib.A64.HelloPh.MainWcL1Wj.hWp_L1P hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1)
      hp hlo0 hc hA13 hz hl hslot
    hWs := fun m1 σ1 => Spike.Lib.A64.HelloPh.MainWcL1Wj.hWs_L1P hpw i0 E rd ls (I := IU) (m1 := m1) (σ1 := σ1)
      hp hlo0 hc hA13 hz hl hslot
    hlim := Spike.Lib.A64.HelloPh.MainWcL1Q.hlim_L1 hpw IH
      (Spike.Lib.A64.HelloPh.MainWcL1Q.rtFree_L1 hpw IH hstat ls hb)
    hloc := Spike.Lib.A64.Flow.HelloJr1.jr1L_loc (tm := .tid) rfl
    hq := Spike.Lib.A64.HelloPh.MainWcL1Hq.hq_L1 hpw IH hstat hc hpin2 hb hJ
    hbox := Spike.Lib.A64.HelloPh.MainWcL1Q.hbox_L1 hJ
    hcell0 := Spike.Lib.A64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH hJ
    hxa := hxa_IU hpw i0 E rd I ls (hX l b n hl hb) hslot }⟩

/-! ## The root's `h1` -/

/-- **The layout's `z` at `newTerm` from the certificate table's** (`IH`'s `z` is `i0`'s off the read's
entries; `HabCtlA.habCtlHA_jr1L`'s step). -/
theorem hzL (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0) :
    (Ly).Λ.imms Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0 := by
  show Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0
  unfold Spike.Lib.A64.HelloPh.C0S.immsH
  split
  · next h => exact absurd h.2.1 (by decide)
  · exact hz

/-- **The root's `h1` with `hP` discharged** (`Level1IU.h1_level1U` at `J1 := mRdJ0 J'`, `hP_level1`; `hJ1` by
`Level1I.slot80_rdJ`, `hmem0` by `Level1I.hmem0_level1`; the heap abort's controls at `wXA` by
`HabCtlA.habCtlHA_jr1L` from `hz`, row `5h-S-habctl-L1`). -/
theorem h1_level1P
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hI : RdImms (Ly).Λ) (himm : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (tcb0 (Ly).Λ))
    /- the certificate table's `z` at `newTerm` (at the root's `ImmsMe.i0M`: `HabCtlA.hz_i0M`) -/
    (hz : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    /- the box store's landings at level 1 with `r1Of` unmapped (`RootHP.hland2_boxMRU` at `I3`) -/
    (hX : ∀ l b n, (LB) l = none → AllocLand (AR).heap (AR).cells b n →
      Spike.Lib.A64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n ((MS1) I l b n []).xa) :
    Spike.Lib.HelloPreA.H1StmtHF (W1R (asm := asm) hpw i0 E rd ls) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)))
      (AR) (LB) ((MS1) I) (Ly) (RdLandH (asm := asm) hpw i0 E rd I ls (mRdJ0 (J')))
      (Spike.Lib.HelloPreA.H1Gfp.inv1G (W1R (asm := asm) hpw i0 E rd ls) (XR hpw i0)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB) ((MS1) I)) [FR] :=
  Spike.Lib.A64.HelloPh.Level1IU.h1_level1U hpw i0 E rd I ls hpa hhp hlo0 hA13
    (Spike.Lib.A64.HelloPh.Level1I.slot80_rdJ hpw i0)
    (hP_level1 hpw i0 E rd I ls hpa hhp hlo0 hstat hc hA13 hpin2 hI himm (hzL hpw i0 hz) hX)
    (Spike.Lib.A64.HelloPh.Level1I.hmem0_level1 hpw i0 E rd I ls hc) hz

end Spike.Lib.A64.HelloPh.MainWcL1A

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1A.hxa_IU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1A.hxa_IU

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1A.hP_level1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1A.hP_level1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1A.hzL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1A.hzL

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1A.h1_level1P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1A.h1_level1P
