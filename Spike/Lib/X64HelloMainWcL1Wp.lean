/-
**`MainWcPS.hWp`, `hWs` at `Level1I`'s choices, the placement and the context left** (x86-64; the twin of
`Spike/Lib/A64HelloMainWcL1Wp.lean`): at any `PlaceWX` output's runtime layout
`Ly := RuntimeLayout.ofPlaceWX hpw (HelloImms.immsH Λ0 i0)`, the arena `arW`, hello's value invariant `gWH`, any
marks `μ`, the level's labels `upd (L0T Ly.Λ) l b` / `updN (ls0T ls) l n` (the memory side) and `updN lsW l n` (the
level), at the first stack's top, `wc_main` up to the allocator's return and its `.x22` lie in the level
`W1H … Ctx1 … l b n` at no frame (`WSHF … []`, which is `WSH`), guarded by main's thread pointer, inside
`NoSetFsW`.

`WcWfR.wcPreW_WSgH`/`wcSp0W_WSgH` at the level, every premise discharged here (the region by `Land.fstable_FS`
and `HelloM.wcR_ok`, its alignment by the first stack's, the limit word by the layout's fields and `HrdR.hun_FS`,
the counter and header words by `WordsNone` and `HrdArena.offH_own`, the box's cell by `MainWcL1Q.hcell0_L1`, the
controls by `hJr` at `Jr` and `WakeSrcCtl.new_ctl` at `c0H`, the allocator's free pcs by `WcWfR.allocW_freeH`) but:
- `hpl`: the placement;
- `hctx` (`hWp`), `hwr` (`hWs`): the level's context `Ctx1` at the counter add and the box's store (at the root's
  context `Land.CtxR1H` by `Land.hctx_main1H` and `Land3.hwr_stH`/`Land.hctx_st1H`, `MainWcL1Wi`).

- `c1J_L1`, `hJ_L1`: `wc_main`'s caller's controls are `c0H`'s, with their control facts.
- `hoffQ_L1`: the arena's offset within its units at the level's memory side, at a box call.
- `wcR_L1`: `wc_main`'s region at the first stack's top: `OK`, its frame condition stable, its base 8-aligned.
- `hWp_L1G`, `hWs_L1G`: the statements, generic in the level's context `Ctx1` and `wc_rodata`'s return invariant
  `Jr`.

## Unlike AArch64

- `scc_rt_main`'s region at the first stack's top is `MainGlue.RS helloLsw TOP` (AArch64 `swR TOP (-helloLsw) 0`),
  so `wc_main`'s is `wcR (RS helloLsw TOP) helloD` and `JrT` takes that region.
- The thread pointer is `%fs`'s base `tpOf (tcbS Ly)` (AArch64 `TPIDR_EL0`), the outside-move guard `NoSetFsW`
  (AArch64 `NoMsrW`, `WcWfS.wcPreW_nsH`/`wcSp0W_nsH`).
- `wcR_ok` gives no alignment: `wc_main`'s region's base is 8-aligned as the first stack's top is
  (`Region.callee_base` twice; AArch64 `wcR_ok`'s 16-alignment). The regions' high ends are `8` (`call` pushes).
- The allocator returns to `.Lwc_main.x22` (AArch64 `.L22_wc_main.sp0`), its `CallerCells` reaching `8`.
- The program is `helloCells`, its labels `codeLabel` (`X64HelloOInit.hlab_H`); the take site is `HelloPh.siteH`.
-/
import Spike.Lib.X64HelloMainWcL1Q
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64HelloW1H
import Spike.Lib.X64HelloWcEntry
import Spike.Lib.X64HelloWcWfR
import Spike.Lib.X64WakeStartGlue
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64HelloClH

namespace Spike.Lib.X64.HelloPh.MainWcL1Wp

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib (FragS PlaceWX Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW NoWrC)
open Spike.Lib.X64 (At NodeW)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.X64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH sNH)
open Spike.Lib.X64.Flow.WakeWc (AGB)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

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
/-- The level's memory side at no frame, under main's thread pointer. -/
local notation "MS" => tpXa (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (NT) s)
  (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- `wc_main`'s entry invariant (`wc_rodata`'s return `Jr`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT Jr (TV) (RM))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at no frame. -/
local notation "WL" => fun s c => Spike.Lib.X64.HelloWf.W1H (Ly) (NT) (AR) helloSrc DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx1 (LB) lsW (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- The placement at the level's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c []

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls lsW : Lsize}
  {l : WeakMem.AllocLabel} {b n : Nat} {Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {Jr : FAS → Spike.Lib.Ctl → Prop} {σC σ1 : FAS} {m1 : MachineData}

/-- `c0H`'s control facts at `wc_main`'s caller's invariant (`WakeSrcCtl.new_ctl`). -/
theorem c1J_L1 : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [] :=
  Spike.Lib.X64.Flow.HelloWc.ctl_wcJ0 fun _ _ h =>
    Spike.Lib.X64.WakeSrcCtl.new_ctl (h.1.1 ▸ Spike.Lib.X64HelloMainPreSrc.c0H_term _ _ _ _)

/-- `wc_main`'s caller's controls are `c0H`'s. -/
theorem hJ_L1 : ∀ σ c, J1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.X64HelloMainPreSrc.c0H w0 w1 w2 mw :=
  Spike.Lib.X64.Flow.HelloWc.ctl_wcJ0
    (P := fun c => ∃ w0 w1 w2 mw, c = Spike.Lib.X64HelloMainPreSrc.c0H w0 w1 w2 mw)
    fun _ _ h => ⟨_, _, _, _, h.1.1⟩

/-- The arena's offset is at most its units' room at every box call (`HrdArena.hoffQ_U` at the level). -/
theorem hoffQ_L1 : ∀ q : Call, q.OKB (MS) (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ := by
  intro q hq
  have hu := Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  have hf := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  rw [hq.one]
  show (Spike.Lib.X64.Rt.arOf (Ly).Λ).off 1 q.τ ≤ 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).units 1 q.τ
  rw [hf]; omega

/-- **`wc_main`'s region at the first stack's top**: a region, its frame condition stable, its base 8-aligned. -/
theorem wcR_L1 (m1 : MachineData) (σ1 : FAS) :
    (RW).OK ∧ FStable (RW) (FW) ∧ (RW).base.toNat % 8 = 0 := by
  obtain ⟨hok, hR0, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hR0 hF0
    (by show (8 : Int) - helloLsw ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
  have hbd : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  have hal : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat % 16 = 0 := by
    rw [(Ly).lab_stacks]; exact (Ly).stacks_al
  have hb0 : ((RM).base.toNat : Int) = (TOP).toNat + (-8 - 0) :=
    Region.callee_base hok (by show (-helloLsw : Int) ≤ -8 - 0 + (8 - helloLsw); decide) (by decide)
      (by show (-8 - 0 : Int) < 0; decide)
  have hb1 : ((RW).base.toNat : Int) = (RM).base.toNat + (-80) :=
    Region.callee_base hR0 (by show (8 : Int) - helloLsw ≤ -80 + -helloD; decide) (by decide)
      (by show (-80 : Int) < 8; decide)
  have htop : (TOP).toNat = (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 16384 := by
    simp only [topS, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact ⟨hR, hF, by omega⟩

/-- **`hWp` at the level, the placement and the context left** (module doc). -/
theorem hWp_L1G (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hJr : ∀ σ c, Jr σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [])
    /- named premise: `wc_main` up to the allocator's return placed -/
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1))
    /- the level's context at the counter add (`Land.hctx_main1H` at `CtxR1H`) -/
    (hctx : ∀ q : Call, q.OKB (MS) (Ly).lab → q.ra = ((Ly).lab ".Lwc_main.x22").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (RW)) (fun m => (FW) m ∧ CallerCells (RW) (-144) (-160) 8 m ∧
        WcCtxH (MS) (Ly).lab (RW) (J0) (J1) q m) (Spike.Lib.X64.Alloc.N (Ly).lab (MS) q .rmw) s c → TP (TV) s →
        Ctx1 l b n s c []) :
    WcPreWH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) := by
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab := Spike.Lib.X64HelloOInit.hlab_H hpw IH hpa hhp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hsite := Spike.Lib.X64.HelloPh.siteH hprog hlo hlab
  have hX0 := Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  obtain ⟨hR, -, hR8⟩ := wcR_L1 hpw i0 m1 σ1
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceWX.wf_link_of_placeWX IH hpw
  have hpl' := Spike.Lib.PlaceWX.link IH hpw
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hpl' hc
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hpl'
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = Scc.Cert.PlaceOK.allocCells := rfl
  have hct : (MS).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have h := Spike.Lib.X64.HelloPh.WcWfR.wcPreW_WSgH (a := NT) (ar := AR) (p := helloSrc) (Dt := DtW)
    (Cl := Spike.Lib.X64.HelloPh.ClH (Ly)) (Ctx := Ctx1 l b n) (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN lsW l n) (frM := Spike.Lib.X64HelloRdCf.frH c0S.env)
    (X0 := X0WH (Ly) (AX)) (rS := RS0) (t := TV) (ms := MS) (F := FW) hprog hlo hΛ hlab
    hsite (Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)) hX0 hR hR8 (by show (-helloD : Int) ≤ -304; decide)
    (by show (8 : Int) ≤ 8; decide)
    (Spike.Lib.X64.HelloPh.HrdArena.hpool_U hpw i0)
    (Spike.Lib.X64.Flow.HelloWc.tp_wcJ0 (Jr := JrT Jr (TV) (RM)) fun _ _ h => h.2.1)
    ?hmr ?hun (fun _ h => h.1) ?hmem ?hno
    (Spike.Lib.X64.Flow.HelloWc.ctl_wcJ0 fun σ c h => hJr σ c h.1) (c1J_L1 hpw i0) hpl
    (fun _ _ _ => Spike.Lib.X64.AllocG.AllocW.imp (Spike.Lib.X64.HelloPh.WcWfR.allocW_freeH hlab)
      (Spike.Lib.X64.Alloc.AllocW.triv _ _) (fun s _ h _ => hX0 s h))
    hctx rfl rfl (fun _ _ => rfl) id (Spike.Lib.X64.HelloPh.HrdArena.hlt_U hpw i0 hc)
    (Spike.Lib.X64.HelloPh.HrdArena.h64_U hpw i0 hc)
  case hmr =>
    show Scc.Sem.Kernel.mapped _ false ⟨Spike.Lib.X64.Flow.Ret0.limA (tpOf (Spike.Lib.X64.Flow.Ret0.pinA
      (Ly).lab + 0#64 + 8#64)), 8⟩ = true
    rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (i := 1) (by decide))).2.1
  case hun => exact fun m hm => Spike.Lib.X64.HelloPh.HrdR.hun_FS m hm.1
  case hmem =>
    exact Spike.Lib.X64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun m h => h.1.1.1.wn)
      (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl]; omega)
      (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩) (hoffQ_L1 hpw i0)
  case hno =>
    intro q hq w hw
    refine Spike.Lib.X64.WakePh.WcWfR.not_ownW (heap := (MS).heap) (cells := (MS).cells) (ctr := (MS).ctr)
      (Spike.Lib.X64.HelloPh.HrdArena.offH_own hpw i0 hA13) ?_
    rcases hw with h | ⟨o', ho, h⟩
    · exact .inl h
    · refine .inr ?_
      have h1 := hoffQ_L1 hpw i0 q hq
      have hroom := hq.toS.room
      rw [hq.toS.off] at h1
      rw [Spike.Lib.X64.Alloc.Call.hdrAt] at h
      generalize q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat = k at h1 h
      omega
  exact Spike.Lib.X64.HelloPh.WcWfS.wcPreW_nsH hprog h

/-- **`hWs` at the level, the placement and the store's context left** (module doc): the box's cell mapped,
unloaded (`MainWcL1Q.hcell0_L1`) and owned at no phase (in the arena's cells, `HrdArena.offH_own`). -/
theorem hWs_L1G (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    /- named premise: `.x22` placed -/
    (hpl : WcSp0WH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1))
    /- the box store's writes' obligation in the level's context (`Land3.hwr_stH` at `Land.hctx_st1H`) -/
    (hwr : NodeW (tpG (TV) (NoWrC (AR) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
      (Spike.Lib.X64ConsumerA.updN lsW l n) (Ctx1 l b n) [])) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW)
      (sNH (MS) (Ly).lab (RW) (J1) .st)) :
    WcSp0WH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) := by
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab := Spike.Lib.X64HelloOInit.hlab_H hpw IH hpa hhp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  have hsite := Spike.Lib.X64.HelloPh.siteH hprog hlo hlab
  have hX0 := Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  obtain ⟨hR, -, -⟩ := wcR_L1 hpw i0 m1 σ1
  have hpl' := Spike.Lib.PlaceWX.link IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hpl'
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hpl'
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = 4194304 := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hu2 : (MS).units 1 .int = 2 := rfl
  have hf1 : (MS).off 1 .int = 8 := rfl
  have h := Spike.Lib.X64.HelloPh.WcWfR.wcSp0W_WSgH (a := NT) (ar := AR) (p := helloSrc) (Dt := DtW)
    (Cl := Spike.Lib.X64.HelloPh.ClH (Ly)) (Ctx := Ctx1 l b n) (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN lsW l n) (frM := Spike.Lib.X64HelloRdCf.frH c0S.env)
    (X0 := X0WH (Ly) (AX)) (rS := RS0) (t := TV) hprog hlo hΛ hlab hsite
    (Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)) hX0 hR
    (by show (-helloD : Int) ≤ -136; decide) (by show (8 : Int) ≤ 8; decide) ?hbox (c1J_L1 hpw i0) hpl hwr
  case hbox =>
    intro q o' hj hlo' hle
    have hc := Spike.Lib.X64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH (μ := μ) (rd := rd)
      (own := fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (NT) s) (I := I)
      (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b) (lsize := Spike.Lib.X64ConsumerA.updN (ls0T ls) l n)
      (fs := []) (hJ_L1 hpw i0) ⟨q.1, Spike.Lib.X64.Flow.WakeWc.okb_of_tpXa q.2⟩ hj o' hlo' hle
    obtain ⟨σ, hjσ⟩ := hj
    obtain ⟨w0, w1, w2, mw, hc0⟩ := hJ_L1 hpw i0 σ _ hjσ
    have hτ := (Spike.Lib.X64.HelloPh.MainWcL1Q.box_c0H q.2 hc0).2.1
    refine ⟨hc.1.1, fun m hm => hc.2 m hm.1, Spike.Lib.X64.WakePh.WcWfR.not_ownW (heap := (MS).heap)
      (cells := (MS).cells) (ctr := (MS).ctr) (Spike.Lib.X64.HelloPh.HrdArena.offH_own hpw i0 hA13) (.inr ?_)⟩
    rw [hτ, hu2, hcl] at hle
    rw [hτ, hf1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hh]; omega), hh, hcl]
    omega
  exact Spike.Lib.X64.HelloPh.WcWfS.wcSp0W_nsH hprog h

end Spike.Lib.X64.HelloPh.MainWcL1Wp

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.c1J_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.c1J_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hoffQ_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hoffQ_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hWp_L1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hWp_L1G

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hWs_L1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hWs_L1G
