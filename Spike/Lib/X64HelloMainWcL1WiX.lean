/-
**`MainWcPS.hWp`, `hWs` at the root's context at `ownGHXW`, the placement left** (x86-64 only; the `ownGHXW`
counterpart of `X64HelloMainWcL1Wi`): `MainWcL1Wp.hWp_L1GX`/`hWs_L1GX` at the level's context `Land.CtxR1H`,
`wc_rodata`'s return `JrRL` as `Jr`:
- `hctx` by `Land.hctx_main1HX` (at `CtxR1HX`, the context at `ref1HX`), carried to `CtxR1H` (`ctxR1H_of_X`);
- `hwr` by `Land.hwr_stH` at `ref1HX`/`Land.GsH1X` (`Land.hctx_st1HX`, then `ctxR1H_of_X`), the box's word and
  cell by `MainWcL1Q.hbox_L1`, `hcell0_L1` at `ownGHXW`.

The level `Level1I.W1Rg … (ownGHXW Ly ntA)` keeps the context `CtxR1H` (at `ref1H`, `ownGH`); the level's memory
side owns `ownGHXW`'s words. The two differ only in the memory side's own map, which the context's facts do not
read.

- `ctxR1H_of_X`: `CtxR1HX` is in `CtxR1H`.
- `hWp_L1X`, `hWs_L1X`: the statements at `CtxR1H` at `ownGHXW`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there, so its level is at `ownGH` only. Against
`X64HelloMainWcL1Wi`: the level and the memory side are at `ownGHXW`, the context's producers are `X64HelloLand1X`'s
(`ref1HX`), carried to `CtxR1H` by `ctxR1H_of_X`.
-/
import Spike.Lib.X64HelloMainWcL1Wi
import Spike.Lib.X64HelloMainWcL1WpX
import Spike.Lib.X64HelloMainWcL1XX
import Spike.Lib.X64HelloLand1X

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
/-- The level's memory side at no frame, under main's thread pointer, at `ownGHXW`. -/
local notation "MS" => tpXa (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ (MU) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s)
  (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`wc_rodata`'s return on the slice at `l`, as `Land.GcM1H`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (RM))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at the root's context, no frame, at `ownGHXW`. -/
local notation "WL" => fun s c => Spike.Lib.X64.HelloWf.W1Hg (Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT)) (Ly) (AR)
  helloSrc DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls)
  (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- The placement at the level's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c []

variable {I : Spike.Lib.X64ConsumerS.InvS} {l : WeakMem.AllocLabel} {b n : Nat}
  {σC σ1 : FAS} {m1 : MachineData}

/-- **`CtxR1HX` is in `CtxR1H`**: the level-1 context at `ref1HX` (`ref1H` with the own map `ownGHXW`) is one at
`ref1H`. Neither the counter add's premises (`Call.OKB`, `CtrOkS`, `Alloc.N`, `WcCtxH`) nor the box's store
(`NewStM`, `bXH`, `MainWcL1X.at_bXH_of_ownXa`) read the memory side's own map. -/
theorem ctxR1H_of_X {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl}
    {fs : List TermRun.Frame}
    (h : Spike.Lib.X64.HelloPh.Land.CtxR1HX (asm := asm) hpw i0 E rd ls l b n s c fs) :
    Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls l b n s c fs := by
  rcases h with ⟨⟨ms0, R, F, q, hms, hG, hok, hAt⟩, htp⟩ | ⟨hfs, Lnd, hGs, hst⟩
  · obtain ⟨X, rfl⟩ : ∃ X, ms0 = { Spike.Lib.X64.HelloPh.Land.ref1HX (asm := asm) hpw i0 E rd ls l b n fs with
        xa := X } := ⟨_, hms⟩
    obtain ⟨rfl, hq, σC, m1, σ1, hslot, hR, hF, hra⟩ := hG
    exact .inl ⟨⟨{ Spike.Lib.X64.HelloPh.Land.ref1H (asm := asm) hpw i0 E rd ls l b n [] with xa := X }, R, F, q,
      rfl, ⟨rfl, { hq with toS := { hq.toS with } }, σC, m1, σ1, hslot, hR, hF, hra⟩,
      ⟨{ hok.oks with }, hok.fst, hok.mem⟩, hAt⟩, htp⟩
  · obtain ⟨v, σC, m1, σ1, hslot, rfl⟩ := hGs
    obtain ⟨kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hacc, hrep, hhold, hnum, hA, hle, hxa⟩ :=
      hst
    exact .inr ⟨hfs, _, ⟨v, σC, m1, σ1, hslot, rfl⟩, kr, A, V, s', x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev,
      hacc, hrep, hhold, hnum, hA, hle, fun l' hl' =>
        let ⟨h1, h2, h3⟩ := hxa l' hl'
        ⟨h1, Spike.Lib.X64.HelloPh.MainWcL1X.at_bXH_of_ownXa rfl h2, h3⟩⟩

/-- **`hWp` at `CtxR1H` at `ownGHXW`** (`hWp_L1` at `ownGHXW`): `MainWcL1Wp.hWp_L1GX` at `Level1I`'s `Jr`, the
context by `Land.hctx_main1HX` at the caller's slot `-16` main's TCB (`hslot`), carried to `CtxR1H` by
`ctxR1H_of_X`. -/
theorem hWp_L1X (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)
    /- named premise: `wc_main` up to the allocator's return placed -/
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1)) :
    WcPreWH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  Spike.Lib.X64.HelloPh.MainWcL1Wp.hWp_L1GX hpw i0 (lsW := ls0T ls) hp hpa hhp hlo0 hc hA13 (hJr_RL _ _ _) hpl
    fun q hq hra s c hAt htp => ctxR1H_of_X hpw i0 E rd ls
      (Spike.Lib.X64.HelloPh.Land.hctx_main1HX (asm := asm) hpw i0 E rd ls hc l b n rfl σC hslot m1 σ1 q hq hra s c
        hAt htp)

/-- **`hWs` at `CtxR1H` at `ownGHXW`** (`hWs_L1` at `ownGHXW`): `MainWcL1Wp.hWs_L1GX`, the box store's obligation
by `Land.hwr_stH` at `ref1HX`/`GsH1X` (`Land.hctx_st1HX`, carried to `CtxR1H` by `ctxR1H_of_X`). -/
theorem hWs_L1X (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
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
  refine Spike.Lib.X64.HelloPh.MainWcL1Wp.hWs_L1GX hpw i0 (μ := MU) (lsW := ls0T ls) hp hpa hhp hlo0 hA13 hpl ?_
  refine Spike.Lib.X64.HelloPh.Land.hwr_stH hpS hendS
    (ref := Spike.Lib.X64.HelloPh.Land.ref1HX (asm := asm) hpw i0 E rd ls l b n []) rfl
    (Gs := Spike.Lib.X64.HelloPh.Land.GsH1X (asm := asm) hpw i0 E rd ls l b n) ⟨TOP, σC, m1, σ1, hslot, rfl⟩
    (Spike.Lib.X64.HelloPh.MainWcL1Q.hbox_L1 (Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0)) ?_
    (fun s c h => ctxR1H_of_X hpw i0 E rd ls (Spike.Lib.X64.HelloPh.Land.hctx_st1HX (asm := asm) hpw i0 E rd ls l b n s c h))
    (Spike.Lib.X64.HelloPh.HrdArena.hlt_U hpw i0 hc) (Spike.Lib.X64.HelloPh.HrdArena.h64_U hpw i0 hc)
  intro q hj o' hlo' hle
  have h := Spike.Lib.X64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH (μ := MU) (rd := rd)
    (own := fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s) (I := I)
    (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b) (lsize := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n)
    (fs := []) (Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1 hpw i0) ⟨q.1, Spike.Lib.X64.Flow.WakeWc.okb_of_tpXa q.2⟩
    hj o' hlo' hle
  exact ⟨h.1, fun m hm => h.2 m hm.1⟩

end Spike.Lib.X64.HelloPh.MainWcL1Wi

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.ctxR1H_of_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.ctxR1H_of_X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.hWp_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.hWp_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wi.hWs_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wi.hWs_L1X
