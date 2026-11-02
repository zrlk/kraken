/-
**`MainWcPS.hWp`, `hWs` at the root's context `Land.CtxR1H`** (x86-64; the twin of
`Spike/Lib/A64HelloMainWcL1Wi.lean`): `MainWcL1Wp.hWp_L1G`/`hWs_L1G` at `Level1I`'s choices (the context
`Land.CtxR1H … E rd ls`, the marks of `E` at `asm`, the level's sizes `ls0T ls`), the level's context discharged:
- `hctx` by `Land.hctx_main1H` (the level's memory side is `ref1H … []` but for `xa`);
- `hwr` by `Land.hwr_stH` at `Land.GsH1` (`Land.hctx_st1H`), the box's word and cell by `MainWcL1Q.hbox_L1`,
  `hcell0_L1`, the counter below the heap by `HrdArena.hlt_U`/`h64_U`; `GsH1`'s pin is the caller's slot `-16`
  (`hslot`).

Left: the placement `hpl`. `wc_main`'s entry is at `Level1I`'s `Jr` (`JrRL`; its control facts `hJr_RL`) and the
caller's slot `-16` holds main's TCB (`hslot`), the call `Land.GcM1H` pins.

- `hJr_RL`: the control facts at `JrRL lbl env l` (`X64HelloRdCf.cont_ctl`).
- `hWp_L1`, `hWs_L1`: the statements at `CtxR1H`.

## Unlike AArch64

- main's TCB is at the caller's slot `-16` (`mWC`'s `%r8`; AArch64 `-80`), as `Land.GcM1H`/`GsH1` pin it.
- The regions are x86-64's (`wcR (RS helloLsw TOP) helloD`, `MainWcL1Wp`), the outside-move guard `NoSetFsW`, the
  thread pointer `tpOf (tcbS Ly)`; the loader's facts are the two parses `cellsOf asm` beside `hp`.
-/
import Spike.Lib.X64HelloMainWcL1Wp
import Spike.Lib.X64HelloLand3
import Spike.Lib.X64HelloJr1L

namespace Spike.Lib.X64.HelloPh.MainWcL1Wi

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.X64.Flow.HelloWc (WcPreWH WcSp0WH)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (tpXa)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)
open Scc.Cert.Rt.X64 (Lays endOf)

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
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `scc_rt_main`'s region at the first stack's top. -/
local notation "RM" => RS helloLsw (TOP)

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (RM) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1

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
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`wc_rodata`'s return on the slice at `l`, as `Land.GcM1H`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (RM))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at the root's context, no frame. -/
local notation "WL" => fun s c => Spike.Lib.X64.HelloWf.W1H (Ly) (NT) (AR) helloSrc DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls)
  (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- The placement at the level's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c []

variable {I : Spike.Lib.X64ConsumerS.InvS} {l : WeakMem.AllocLabel} {b n : Nat}
  {σC σ1 : FAS} {m1 : MachineData}

/-- **`hWp_L1G`'s `hJr` at `Level1I`'s `JrRL`**: `wc_rodata`'s return's controls are the wrapper's continuation
(`X64HelloRdCf.cont_ctl`). -/
theorem hJr_RL (lbl : WeakMem.AllocLabel → Option Nat) (env : TermRun.Env) (l : WeakMem.AllocLabel) :
    ∀ σ c, JrRL lbl env l σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [] := by
  rintro σ c ⟨rfl, -⟩
  exact Spike.Lib.X64HelloRdCf.cont_ctl _ none

/-- **`hWp` at `CtxR1H`** (module doc): `hWp_L1G` at `Level1I`'s `Jr` (`hJr` by `hJr_RL`), the context by
`Land.hctx_main1H` at the caller's slot `-16` main's TCB (`hslot`, `Land.GcM1H`'s pin). -/
theorem hWp_L1 (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- named premise: `wc_main` up to the allocator's return placed -/
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1)) :
    WcPreWH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  Spike.Lib.X64.HelloPh.MainWcL1Wp.hWp_L1G hpw i0 (lsW := ls0T ls) hp hpa hhp hlo0 hc hA13 (hJr_RL _ _ _) hpl
    (Spike.Lib.X64.HelloPh.Land.hctx_main1H (asm := asm) hpw i0 E rd ls hc l b n rfl σC hslot m1 σ1)

/-- **`hWs` at `CtxR1H`** (module doc): `hWs_L1G`, the box store's obligation by `Land.hwr_stH` at `GsH1` (the
caller's slot `-16` main's TCB, `hslot`). -/
theorem hWs_L1 (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- named premise: `.x22` placed -/
    (hpl : WcSp0WH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1)) :
    WcSp0WH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) := by
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hpS : Lays (Ly).exe SccCode.helloCells (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = endOf (Ly).exe SccCode.helloCells (Ly).pfx := by
    show endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  refine Spike.Lib.X64.HelloPh.MainWcL1Wp.hWs_L1G hpw i0 (μ := MU) (lsW := ls0T ls) hp hpa hhp hlo0 hA13 hpl ?_
  refine Spike.Lib.X64.HelloPh.Land.hwr_stH hpS hendS
    (ref := Spike.Lib.X64.HelloPh.Land.ref1H (asm := asm) hpw i0 E rd ls l b n []) rfl
    (Gs := Spike.Lib.X64.HelloPh.Land.GsH1 (asm := asm) hpw i0 E rd ls l b n) ⟨TOP, σC, m1, σ1, hslot, rfl⟩
    (Spike.Lib.X64.HelloPh.MainWcL1Q.hbox_L1 (Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0)) ?_
    (Spike.Lib.X64.HelloPh.Land.hctx_st1H (asm := asm) hpw i0 E rd ls l b n)
    (Spike.Lib.X64.HelloPh.HrdArena.hlt_U hpw i0 hc) (Spike.Lib.X64.HelloPh.HrdArena.h64_U hpw i0 hc)
  intro q hj o' hlo' hle
  have h := Spike.Lib.X64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH (μ := MU) (rd := rd)
    (own := fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (NT) s) (I := I)
    (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b) (lsize := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n)
    (fs := []) (Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0) ⟨q.1, Spike.Lib.X64.Flow.WakeWc.okb_of_tpXa q.2⟩
    hj o' hlo' hle
  exact ⟨h.1, fun m hm => h.2 m hm.1⟩

/-- **Inhabitation at `Level1I`'s `Jr`**: at `wc_rodata`'s return `JrRL (upd LB l b) c0S.env l`, `hWp_L1` asks
only the certificate's facts, the caller's slot `-16` and the placement (`hJr` by `hJr_RL`). -/
example (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1)) :
    WcPreWH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  hWp_L1 hpw i0 E rd ls hp hpa hhp hlo0 hc hA13 hslot hpl

end Spike.Lib.X64.HelloPh.MainWcL1Wi

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.hJr_RL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.hJr_RL

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.hWp_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.hWp_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.hWs_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.hWs_L1
