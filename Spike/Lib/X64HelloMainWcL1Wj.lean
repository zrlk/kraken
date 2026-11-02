/-
**`MainWcPS.hWp`, `hWs` at the root's context with the placement discharged** (x86-64; the twin of
`Spike/Lib/A64HelloMainWcL1Wj.lean`, same names): `MainWcL1Wi.hWp_L1`/`hWs_L1` at `Level1I`'s `Jr` (`JrRL` at the
level's labels and the start's environment `c0S.env`) and `Jr1` (`Land.Jr1LH`), their `hpl` by
`WcPlS.hplP_S`/`hplS_S`:
- the entry's controls (`JrRL`'s setup continuation, `Jr1LH`'s `c0H`) are placed at the slice's registers and `me`
  at `%r8`, the caller's slot `-16` (`WcPlS.plE_cont`, `plE_c0H`);
- `me`'s word `mwH` is represented at that slot: the slot is main's TCB (`hslot`), the TCB's label main's id
  (`L0T`'s `tcb0`, `PlaceWX.pinA_toNat_ofPlaceWX`), surviving the fresh label `l` (`hl`, `MainWcL1S.valRep_upd`);
- `c0H`'s `z` is the layout's immediate `0` (`hz`; at the root's table `HabCtlA.hz_i0M`);
- `wc_main`'s region reaches `-144` (`wcR_ok` at `Land.fstable_FS`).

- `hme_slot`: `mwH` at the caller's slot `-16`.
- `wcR_L1`: `wc_main`'s region's facts.
- `hmeE_c0S`: `me`'s binding in `c0S.env` (AArch64 closes it by `rfl` inline).
- `plE_J0`, `plE_J1`: the entry controls placed (`WcPlS.PlE`), with an inhabitation `example` at concrete places.
- `hWp_L1P`, `hWs_L1P`: the statements.

## Differences from the AArch64 version

- `me` is the caller's slot `-16` and `%r8` (AArch64: `-80`, `x4`); the four places of the inhabitation example are
  `%rdi`, `%rdx`, `%rcx`, `%r8` (AArch64: `x0`, `x2`, `x3`, `x4`).
- main's id's place at `L0T` is `tcb0 Λ = Λ.pinned.lo + 8`, matched to `pinA + 8` by
  `PlaceWX.pinA_toNat_ofPlaceWX` (AArch64: `WakeHClW.hme_W`, which has no x86-64 version).
- `wc_main`'s region is `wcR (RS helloLsw TOP) helloD` (AArch64: `wcR (swR TOP (-helloLsw) 0) helloD`), its top at
  `8` (AArch64 `0`).
- The level is inside `NoSetFsW` (no `arch_prctl`; AArch64 `NoMsrW`). `hWp_L1P`/`hWs_L1P` take `MainWcL1Wi`'s
  certificate premises: the cells (`hpa`, `hhp`) besides `hp`, and `hA13`.
-/
import Spike.Lib.X64HelloWcPlS
import Spike.Lib.X64HelloMainWcL1S
import Spike.Lib.X64HelloMainWcL1Wi
import Spike.Lib.X64HelloLevel1I

namespace Spike.Lib.X64.HelloPh.MainWcL1Wj

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry ValRep)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.X64.Flow.HelloWc (WcPreWH WcSp0WH)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.KeepTP (tpXa)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloMainPreSrc (newTerm)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (RS helloLsw (TOP)) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1

set_option hygiene false in
/-- The level's marks (`E`'s at `asm`). -/
local notation "MU" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
/-- The level's memory side at no frame, under main's thread pointer. -/
local notation "MS" => tpXa (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ (MU) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (NT) s)
  (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- The level at the root's context, no frame. -/
local notation "WL" => fun s c => Spike.Lib.X64.HelloWf.W1H (Ly) (NT) (AR) helloSrc DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls)
  (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`wc_rodata`'s return on the slice at `l`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (RS helloLsw (TOP)))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

variable {I : Spike.Lib.X64ConsumerS.InvS} {l : WeakMem.AllocLabel} {b n : Nat} {σC σ1 : FAS} {m1 : MachineData}

/-- **`me`'s word at the caller's slot `-16`**: the slot is main's TCB (`hslot`), whose label is main's id
(`L0T`'s `tcb0`), the fresh label `l` aside (`hl`). -/
theorem hme_slot (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    ValRep (Spike.Lib.X64ConsumerA.upd (LB) l b) Spike.Lib.X64.HelloPh.Land.mwH.val (σC.slot (-16)).toNat := by
  have hp0 := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hpw IH
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have hme : L0T (Ly).Λ (mainTidLbl 2) = some ((Ly).pinA.toNat + 8) := by
    simp only [L0T, Spike.Lib.X64ConsumerA.upd, ↓reduceIte, Spike.Lib.X64WakeLoadT.tcb0, Option.some.injEq]
    omega
  refine Spike.Lib.X64.HelloPh.MainWcL1S.valRep_upd hl ⟨by decide, (Ly).pinA.toNat + 8, ?_, ?_⟩
  · simp [Scc.Sem.wordAddr, hme]
  · rw [hslot, Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- **`wc_main`'s region at the call** is a region reaching `-144` (`wcR_ok` at `Land.fstable_FS`; the caller's
state `m0`, `σ0` only fixes the frame condition, unused here). -/
theorem wcR_L1 (m0 : MachineData) (σ0 : FAS) : (RW).OK ∧ (RW).lo ≤ -144 ∧ 0 ≤ (RW).hi := by
  obtain ⟨-, hok, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, -⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hF0
    (by show (8 - helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m0 σ0
  exact ⟨hR, by show (-helloD : Int) ≤ -144; decide, by show (0 : Int) ≤ 8; decide⟩

/-- `me`'s binding in the start's environment: main's id's word `mwH`. -/
theorem hmeE_c0S : TermRun.lookupE c0S.env "me" = some (.tid, [Spike.Lib.X64.HelloPh.Land.mwH]) := by
  simp [Spike.Lib.X64.HelloPh.C0S.c0S_env, TermRun.lookupE]

/-- `Level1I`'s `Jr`'s entry controls placed (`WcPlS.plE_cont`). -/
theorem plE_J0 (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    Spike.Lib.X64.HelloPh.WcPlS.PlE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) (J0) :=
  Spike.Lib.X64.HelloPh.WcPlS.plE_cont hmeE_c0S (hme_slot hpw i0 hl hslot) fun _ _ h => h.1

/-- `Land.Jr1LH`'s entry controls placed (`WcPlS.plE_c0H`). -/
theorem plE_J1 (hz : (Ly).Λ.imms newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    Spike.Lib.X64.HelloPh.WcPlS.PlE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) (J1) :=
  Spike.Lib.X64.HelloPh.WcPlS.plE_c0H hz (hme_slot hpw i0 hl hslot) fun _ _ h => h.1

/-- **Inhabitation of `PlE` at the real entry**: at a state of `wc_main`'s entry invariant at `Level1I`'s `Jr`, a
machine state with the same registers has its control placed, the four places the registers `%rdi`, `%rdx`,
`%rcx`, `%r8` (`WcPlS.plE_regs` at `plE_J0`). -/
example (hl : (LB) l = none) (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    {σ : FAS} {c : Spike.Lib.Ctl} (hJ : (J0) σ c) (s : State) (hs : s.st.1.regs = σ.regs) :
    Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c [] :=
  Spike.Lib.X64.HelloPh.WcPlS.plE_regs (plE_J0 hpw i0 hl hslot) hJ s fun r _ => by rw [hs]

/-- **`hWp` at `CtxR1H`, placed** (module doc): `MainWcL1Wi.hWp_L1` at `Level1I`'s `Jr`, `hpl` by
`WcPlS.hplP_S`. -/
theorem hWp_L1P (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : (Ly).Λ.imms newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    WcPreWH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  have hR := wcR_L1 hpw i0 m1 σ1
  Spike.Lib.X64.HelloPh.MainWcL1Wi.hWp_L1 hpw i0 E rd ls hp hpa hhp hlo0 hc hA13 hslot
    (Spike.Lib.X64.HelloPh.WcPlS.hplP_S hR.1 hR.2.1 hR.2.2 (plE_J0 hpw i0 hl hslot) (plE_J1 hpw i0 hz hl hslot))

/-- **`hWs` at `CtxR1H`, placed** (module doc): `MainWcL1Wi.hWs_L1`, `hpl` by `WcPlS.hplS_S`. -/
theorem hWs_L1P (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : (Ly).Λ.imms newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    WcSp0WH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) :=
  have hR := wcR_L1 hpw i0 m1 σ1
  Spike.Lib.X64.HelloPh.MainWcL1Wi.hWs_L1 hpw i0 E rd ls hp hpa hhp hlo0 hc hA13 hslot
    (Spike.Lib.X64.HelloPh.WcPlS.hplS_S (by have := hR.2.1; omega) hR.2.2 (plE_J1 hpw i0 hz hl hslot))

end Spike.Lib.X64.HelloPh.MainWcL1Wj

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.hme_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.hme_slot

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.wcR_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.wcR_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.hmeE_c0S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.hmeE_c0S

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.plE_J0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.plE_J0

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.plE_J1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.plE_J1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.hWp_L1P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.hWp_L1P

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.hWs_L1P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.hWs_L1P
