/-
**`MainWcPS.hWp`, `hWs` at the root's context with the placement discharged** (AArch64; `Level1I.hP`'s fields,
stage 3; rows `L1-WcPlS`): `MainWcL1Wi.hWp_L1`/`hWs_L1` at `Level1I`'s `Jr` (`JrRL` at the level's
labels and the start's environment `c0S.env`) and `Jr1` (`Land.Jr1LH`), their `hpl` by `WcPlS.hplP_S`/`hplS_S`:
- the entry's controls (`JrRL`'s setup continuation, `Jr1LH`'s `c0H`) are placed at the slice's registers and `me`
  at `x4`, the caller's slot `-80` (`WcPlS.plE_cont`, `plE_c0H`);
- `me`'s word `mwH` is represented at that slot: the slot is main's TCB (`hslot`), the TCB's label main's id
  (`WakeHClW.hme_W`), surviving the fresh label `l` (`hl`, `MainWcL1S.valRep_upd`);
- `c0H`'s `z` is the layout's immediate `0` (`hz`; at the root's `i0M`, `HabCtlA.hz_i0M`);
- `wc_main`'s region reaches `-144` (`wcR_ok` at `Land.fstable_FS`).

- `hme_slot`: `mwH` at the caller's slot `-80`.
- `wcR_L1`: `wc_main`'s region's facts.
- `plE_J0`, `plE_J1`: the entry controls placed (`WcPlS.PlE`), with an inhabitation `example` at concrete places.
- `hWp_L1P`, `hWs_L1P`: the statements.
-/
import Spike.Lib.A64HelloMainWcL1Wi
import Spike.Lib.A64HelloWcPlS
import Spike.Lib.A64HelloMainWcL1S

namespace Spike.Lib.A64.HelloPh.MainWcL1Wj

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry ValRep)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.A64.Flow.HelloWc (WcPreWH WcSp0WH)
open Spike.Lib.A64.Flow.WakeWc (tpG)
open Spike.Lib.A64.Flow.HelloJr1 (JrRL)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

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
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (swR (TOP) (-helloLsw) 0) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1

set_option hygiene false in
/-- The level's marks (`E`'s at `asm`). -/
local notation "MU" => (Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
/-- The level's memory side at no frame, under main's thread pointer. -/
local notation "MS" => tpXa (Spike.Lib.A64ConsumerA.msOfA (Ly).Λ (MU) rd
  (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH)) (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (NT) s)
  (AR) I (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`wc_rodata`'s return on the slice at `l`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (swR (TOP) (-helloLsw) 0))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at the root's context, no frame. -/
local notation "WL" => fun s c => Spike.Lib.A64.HelloWf.W1H (Ly) (NT) (AR) helloSrc Spike.Lib.A64.WakeWf.DtW
  (Spike.Lib.A64.HelloPh.ClH (Ly)) (Spike.Lib.A64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls)
  (Spike.Lib.HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

variable {I : Spike.Lib.A64ConsumerS.InvS} {l : WeakMem.AllocLabel} {b n : Nat} {σC σ1 : FAS} {m1 : MachineData}

/-- **`me`'s word at the caller's slot `-80`**: the slot is main's TCB (`hslot`), whose label is main's id
(`WakeHClW.hme_W`), the fresh label `l` aside (`hl`). -/
theorem hme_slot (hl : (LB) l = none)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    ValRep (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.Land.mwH.val (σC.slot (-80)).toNat := by
  refine Spike.Lib.A64.HelloPh.MainWcL1S.valRep_upd hl ⟨by decide, ((Ly).pinA + 8#64).toNat, ?_, ?_⟩
  · simp [Scc.Sem.wordAddr, Spike.Lib.WakeHClW.hme_W hpw _]
  · rw [hslot]
    show (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64).toNat = ((Ly).pinA + 8#64).toNat + 0
    rw [Spike.Lib.A64.Rt.pinA_lab0, BitVec.add_zero, Nat.add_zero]

/-- **`wc_main`'s region at the call** is a region reaching `-144` (`wcR_ok` at `Land.fstable_FS`; the caller's
state `m0`, `σ0` only fixes the frame condition, unused here). -/
theorem wcR_L1 (m0 : MachineData) (σ0 : FAS) : (RW).OK ∧ (RW).lo ≤ -144 ∧ 0 ≤ (RW).hi := by
  obtain ⟨hok, hal, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, -, -⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal hF0
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m0 σ0
  exact ⟨hR, by show (-helloD : Int) ≤ -144; decide, by show (0 : Int) ≤ 0; decide⟩

/-- `Level1I`'s `Jr`'s entry controls placed (`WcPlS.plE_cont`). -/
theorem plE_J0 (hl : (LB) l = none)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    Spike.Lib.A64.HelloPh.WcPlS.PlE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (LB) l b) (J0) :=
  Spike.Lib.A64.HelloPh.WcPlS.plE_cont rfl (hme_slot hpw i0 hl hslot) fun _ _ h => h.1

/-- `Land.Jr1LH`'s entry controls placed (`WcPlS.plE_c0H`). -/
theorem plE_J1 (hz : (Ly).Λ.imms Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    Spike.Lib.A64.HelloPh.WcPlS.PlE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (LB) l b) (J1) :=
  Spike.Lib.A64.HelloPh.WcPlS.plE_c0H hz (hme_slot hpw i0 hl hslot) fun _ _ h => h

/-- **Inhabitation of `PlE` at the real entry**: at a state of `wc_main`'s entry invariant at `Level1I`'s `Jr`, a
machine state with the same registers has its control placed, the four places the registers `x0`, `x2`, `x3`, `x4`
(`WcPlS.plE_regs` at `plE_J0`). -/
example (hl : (LB) l = none) (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    {σ : FAS} {c : Spike.Lib.Ctl} (hJ : J0 σ c) (s : State) (hs : s.st.1.regs = σ.regs) :
    Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (LB) l b) s c [] :=
  (plE_J0 hpw i0 hl hslot) σ c hJ s (.reg (.x XReg.X0.idx)) (.reg (.x XReg.X2.idx)) (.reg (.x XReg.X3.idx))
    (.reg (.x XReg.X4.idx)) (by rw [Spike.Lib.A64WakeMainW.placeVal_x, hs]; rfl)
    (by rw [Spike.Lib.A64WakeMainW.placeVal_x, hs]; rfl) (by rw [Spike.Lib.A64WakeMainW.placeVal_x, hs]; rfl)
    (by rw [Spike.Lib.A64WakeMainW.placeVal_x, hs]; rfl)

/-- **`hWp` at `CtxR1H`, placed** (module doc): `MainWcL1Wi.hWp_L1` at `Level1I`'s `Jr`, `hpl` by
`WcPlS.hplP_S`. -/
theorem hWp_L1P (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : (Ly).Λ.imms Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    WcPreWH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  have hR := wcR_L1 hpw i0 m1 σ1
  Spike.Lib.A64.HelloPh.MainWcL1Wi.hWp_L1 hpw i0 E rd ls hp hlo0 hc hA13 hslot
    (Spike.Lib.A64.HelloPh.WcPlS.hplP_S hR.1 hR.2.1 hR.2.2 (plE_J0 hpw i0 hl hslot) (plE_J1 hpw i0 hz hl hslot))

/-- **`hWs` at `CtxR1H`, placed** (module doc): `MainWcL1Wi.hWs_L1`, `hpl` by `WcPlS.hplS_S`. -/
theorem hWs_L1P (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : (Ly).Λ.imms Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    WcSp0WH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) :=
  have hR := wcR_L1 hpw i0 m1 σ1
  Spike.Lib.A64.HelloPh.MainWcL1Wi.hWs_L1 hpw i0 E rd ls hp hlo0 hc hA13 hslot
    (Spike.Lib.A64.HelloPh.WcPlS.hplS_S hR.2.1 hR.2.2 (plE_J1 hpw i0 hz hl hslot))

end Spike.Lib.A64.HelloPh.MainWcL1Wj

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wj.hme_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wj.hme_slot

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wj.wcR_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wj.wcR_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wj.hWp_L1P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wj.hWp_L1P

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wj.hWs_L1P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wj.hWs_L1P

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wj.plE_J0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wj.plE_J0

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wj.plE_J1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wj.plE_J1
