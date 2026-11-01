/-
**`MainWcPS.hWp`, `hWs` at the root's context `Land.CtxR1H`** (AArch64; `Level1I.hP`'s fields, stage 3):
`MainWcL1Wp.hWp_L1G`/`hWs_L1G` at `Level1I`'s choices (the context `Land.CtxR1H … E rd ls`, the marks of
`E` at `asm`, the level's sizes `ls0T ls`), the level's context discharged:
- `hctx` by `Land.hctx_main1H` (the level's memory side is `ref1H … []` but for `xa`);
- `hwr` by `Land.hwr_stH` at `Land.GsH1` (`Land.hctx_st1H`), the box's word and cell by `MainWcL1Q.hbox_L1`,
  `hcell0_L1`, the counter below the heap by `HrdArena.hlt_U`/`h64_U`; `GsH1`'s pin is the caller's slot `-80`
  (`hslot`; `Level1I.hP` is asked only at such callers, `Level1I.slot80_rdJ`).

Left: the placement `hpl` (`A64HelloWcPlS`). `wc_main`'s entry is at `Level1I`'s `Jr`
(`JrRL`; its control facts `hJr_RL`) and the caller's slot `-80` holds main's TCB (`hslot`), the call
`Land.GcM1H` pins.

- `hJr_RL`: the control facts at `JrRL lbl env l` (`HelloRdCf.cont_ctl`).
- `hWp_L1`, `hWs_L1`: the statements at `CtxR1H`.
-/
import Spike.Lib.A64HelloMainWcL1Wp
import Spike.Lib.A64HelloLand3
import Spike.Lib.A64HelloJr1L

namespace Spike.Lib.A64.HelloPh.MainWcL1Wi

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
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
open Scc.Cert.Rt.A64 (Lays endOf)

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
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`wc_rodata`'s return on the slice at `l`, as `Land.GcM1H`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (swR (TOP) (-helloLsw) 0))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at the root's context, no frame. -/
local notation "WL" => fun s c => Spike.Lib.A64.HelloWf.W1H (Ly) (NT) (AR) helloSrc DtW
  (Spike.Lib.A64.HelloPh.ClH (Ly)) (Spike.Lib.A64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls)
  (Spike.Lib.HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- The placement at the level's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (LB) l b) s c []

variable {I : Spike.Lib.A64ConsumerS.InvS} {l : WeakMem.AllocLabel} {b n : Nat}
  {Jr : FAS → Spike.Lib.Ctl → Prop} {σC σ1 : FAS} {m1 : MachineData}

/-- **`hWp_L1G`'s `hJr` at `Level1I`'s `JrRL`**: `wc_rodata`'s return's controls are the wrapper's continuation
(`HelloRdCf.cont_ctl`). -/
theorem hJr_RL (lbl : WeakMem.AllocLabel → Option Nat) (env : TermRun.Env) (l : WeakMem.AllocLabel) :
    ∀ σ c, JrRL lbl env l σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf helloSrc c [] := by
  rintro σ c ⟨rfl, -⟩
  exact Spike.Lib.HelloRdCf.cont_ctl _ none

/-- **`hWp` at `CtxR1H`** (module doc): `hWp_L1G` at `Level1I`'s `Jr` (`hJr` by `hJr_RL`), the context by
`Land.hctx_main1H` at the caller's slot `-80` main's TCB (`hslot`, `Land.GcM1H`'s pin). -/
theorem hWp_L1 (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- named premise: `wc_main` up to the allocator's return placed -/
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1)) :
    WcPreWH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  Spike.Lib.A64.HelloPh.MainWcL1Wp.hWp_L1G hpw i0 (lsW := ls0T ls) hp hlo0 hc hA13 (hJr_RL _ _ _) hpl
    (Spike.Lib.A64.HelloPh.Land.hctx_main1H (asm := asm) hpw i0 E rd ls hc l b n rfl σC hslot m1 σ1)

/-- **`hWs` at `CtxR1H`** (module doc): `hWs_L1G`, the box store's obligation by `Land.hwr_stH` at `GsH1` (the
caller's slot `-80` main's TCB, `hslot`). -/
theorem hWs_L1 (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- named premise: `.sp0` placed -/
    (hpl : WcSp0WH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1)) :
    WcSp0WH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) := by
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hpS : Lays (Ly).exe SccCode.helloProg (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = endOf (Ly).exe SccCode.helloProg (Ly).pfx := by
    show endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  refine Spike.Lib.A64.HelloPh.MainWcL1Wp.hWs_L1G hpw i0 (μ := MU) (lsW := ls0T ls) hp hlo0 hA13 hpl ?_
  refine Spike.Lib.A64.HelloPh.Land.hwr_stH hpS hendS
    (ref := Spike.Lib.A64.HelloPh.Land.ref1H (asm := asm) hpw i0 E rd ls l b n []) rfl
    (Gs := Spike.Lib.A64.HelloPh.Land.GsH1 (asm := asm) hpw i0 E rd ls l b n) ⟨TOP, σC, m1, σ1, hslot, rfl⟩
    (Spike.Lib.A64.HelloPh.MainWcL1Q.hbox_L1 (Spike.Lib.A64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0)) ?_
    (Spike.Lib.A64.HelloPh.Land.hctx_st1H (asm := asm) hpw i0 E rd ls l b n)
    (Spike.Lib.A64.HelloPh.HrdArena.hlt_U hpw i0 hc) (Spike.Lib.A64.HelloPh.HrdArena.h64_U hpw i0 hc)
  intro q hj o' hlo' hle
  have h := Spike.Lib.A64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH (μ := MU) (rd := rd)
    (own := fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (NT) s) (I := I)
    (lbl := Spike.Lib.A64ConsumerA.upd (LB) l b) (lsize := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n)
    (fs := []) (Spike.Lib.A64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0) ⟨q.1, Spike.Lib.A64.Flow.WakeWc.okb_of_tpXa q.2⟩
    hj o' hlo' hle
  exact ⟨h.1, fun m hm => h.2 m hm.1⟩

/-- **Inhabitation at `Level1I`'s `Jr`**: at `wc_rodata`'s return `JrRL (upd LB l b) c0S.env l`, `hWp_L1` asks
only the certificate's facts, the caller's slot `-80` and the placement (`hJr` by `hJr_RL`). -/
example (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-80) = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS)
      (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) c0S.env l) (TV)
        (swR (TOP) (-helloLsw) 0))).J σ1) (J1)) :
    WcPreWH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS)
      (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) c0S.env l) (TV)
        (swR (TOP) (-helloLsw) 0))).J σ1) (J1) :=
  hWp_L1 hpw i0 E rd ls hp hlo0 hc hA13 hslot hpl

end Spike.Lib.A64.HelloPh.MainWcL1Wi

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wi.hJr_RL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wi.hJr_RL

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wi.hWp_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wi.hWp_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wi.hWs_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wi.hWs_L1
