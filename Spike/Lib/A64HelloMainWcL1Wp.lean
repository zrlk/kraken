/-
**`MainWcPS.hWp`, `hWs` at `Level1I`'s choices, the placement and the context left** (AArch64; `Level1I.hP`'s
fields, stage 3; : the placement `hpl` a named premise, row `L1-WcPlS`): at any `PlaceW`
output's runtime layout `Ly := RuntimeLayout.ofPlaceW hpw (C0S.immsH Λ0 i0)`, the arena `arW`, hello's value
invariant `gWH`, any marks `μ` (so no certificate text), the level's labels `upd (L0T Ly.Λ) l b` /
`updN (ls0T ls) l n` (the memory side) and `updN lsW l n` (the level), at the first stack's top, `wc_main` up to
the allocator's return and its `.sp0` lie in the level `W1H … Ctx1 … l b n` at no frame (`WSHF … []`, which is
`WSH`), guarded by main's thread pointer, inside `NoMsrW` (wake's `WcWfR.hTopP_Rpl`/`hTopS_Rpl`).

`WcWfR.wcPreW_WSgH`/`wcSp0W_WSgH` at the level, every premise discharged here (the region by `Land.fstable_FS`
and `HelloM.wcR_ok`, the limit word by the layout's fields and `HrdR.hun_FS`, the counter and header words by
`WordsNone` and `HrdArena.offH_own`, the box's cell by `MainWcL1Q.hcell0_L1`, the controls by `hJr` at `Jr` and
`WakeSrcCtl.new_ctl` at `c0H`, the allocator's free pcs by `WcWfR.allocW_freeH`) but:
- `hpl`: the placement (`A64HelloWcPlS`);
- `hctx` (`hWp`), `hwr` (`hWs`): the level's context `Ctx1` at the counter add and the box's store; at the root's
  context `Land.CtxR1H` by `Land.hctx_main1H` and `Land3.hwr_stH`/`Land.hctx_st1H`, once those are generic in the
  certificate text (`hello-l2`).

- `c1J_L1`, `hJ_L1`: `wc_main`'s caller's controls are `c0H`'s, with their control facts.
- `hoffQ_L1`: the arena's offset within its units at the level's memory side, at a box call.
- `hWp_L1G`, `hWs_L1G`: the statements, generic in the level's context `Ctx1` and `wc_rodata`'s return invariant
  `Jr`.
-/
import Spike.Lib.A64HelloMainWcL1Q
import Spike.Lib.A64HelloHrdArena
import Spike.Lib.A64HelloLand1
import Spike.Lib.A64HelloW1H
import Spike.Lib.A64HelloWcEntry

namespace Spike.Lib.A64.HelloPh.MainWcL1Wp

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (FragS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW NoWrC)
open Spike.Lib.A64.Flow (swR At NodeW)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.A64.Flow.HelloWc (WcPreWH WcSp0WH wARH WcCtxH sNH)
open Spike.Lib.A64.Flow.WakeWc (tpG AGB)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

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
/-- The level's memory side at no frame, under main's thread pointer. -/
local notation "MS" => tpXa (Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH)) (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (NT) s)
  (AR) I (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- `wc_main`'s entry invariant (`wc_rodata`'s return `Jr`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT Jr (TV) (swR (TOP) (-helloLsw) 0))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.A64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at no frame. -/
local notation "WL" => fun s c => Spike.Lib.A64.HelloWf.W1H (Ly) (NT) (AR) helloSrc DtW
  (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx1 (LB) lsW (Spike.Lib.HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- The placement at the level's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.A64ConsumerA.upd (LB) l b) s c []

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls lsW : Lsize}
  {l : WeakMem.AllocLabel} {b n : Nat} {Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {Jr : FAS → Spike.Lib.Ctl → Prop} {σC σ1 : FAS} {m1 : MachineData}

/-- `c0H`'s control facts at `wc_main`'s caller's invariant (`WakeSrcCtl.new_ctl`). -/
theorem c1J_L1 : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf helloSrc c [] :=
  Spike.Lib.A64.Flow.HelloWc.ctl_wcJ0 fun _ _ h =>
    Spike.Lib.WakeSrcCtl.new_ctl (h.1 ▸ Spike.Lib.HelloMainPreSrc.c0H_term _ _ _ _)

/-- `wc_main`'s caller's controls are `c0H`'s. -/
theorem hJ_L1 : ∀ σ c, J1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw :=
  Spike.Lib.A64.Flow.HelloWc.ctl_wcJ0 (P := fun c => ∃ w0 w1 w2 mw, c = Spike.Lib.HelloMainPreSrc.c0H w0 w1 w2 mw)
    fun _ _ h => ⟨_, _, _, _, h.1⟩

/-- The arena's offset is at most its units' room at every call (`HrdArena.hoffQ_U` at the level). -/
theorem hoffQ_L1 : ∀ q : Call, q.OKB (MS) (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ := by
  intro q hq
  have hu := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  have hf := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  rw [hq.one]
  show (Spike.Lib.A64.Rt.arOf (Ly).Λ).off 1 q.τ ≤ 16 * (Spike.Lib.A64.Rt.arOf (Ly).Λ).units 1 q.τ
  rw [hf]; omega

/-- **`hWp` at the level, the placement and the context left** (module doc). -/
theorem hWp_L1G (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hJr : ∀ σ c, Jr σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf helloSrc c [])
    /- named premise: `wc_main` up to the allocator's return placed -/
    (hpl : WcPreWH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1))
    /- the level's context at the counter add (`Land.hctx_main1H` at `CtxR1H`) -/
    (hctx : ∀ q : Call, q.OKB (MS) (Ly).lab → q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (RW)) (fun m => (FW) m ∧ CallerCells (RW) (-144) (-160) 0 m ∧
        WcCtxH (MS) (Ly).lab (RW) (J0) (J1) q m) (Spike.Lib.A64.Alloc.N (Ly).lab (MS) q .rmw) s c → TP (TV) s →
        Ctx1 l b n s c []) :
    WcPreWH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) := by
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw IH l x (by
      show codeOf Λ0.code.lo o.prog l = some x
      rw [hlo0, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw IH
  have hX0 := Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  obtain ⟨hok, hal0, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hal, -⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal0 hF0
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceW.wf_link_of_placeW IH hpw
  have hpl' := Spike.Lib.PlaceW.link IH hpw
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW hpl' hc
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW hpl'
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = Scc.Cert.PlaceOK.allocCells := rfl
  have hct : (MS).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
  have h := Spike.Lib.A64.HelloPh.WcWfR.wcPreW_WSgH (a := NT) (ar := AR) (p := helloSrc) (Dt := DtW)
    (Cl := Spike.Lib.A64.HelloPh.ClH (Ly)) (Ctx := Ctx1 l b n) (lbl := Spike.Lib.A64ConsumerA.upd (LB) l b)
    (lsize := Spike.Lib.A64ConsumerA.updN lsW l n) (frM := Spike.Lib.HelloRdCf.frH c0S.env)
    (X0 := X0WH (Ly) (AX)) (rS := RS) (t := TV) (ms := MS) (F := FW) hprog hlo hΛ hlab
    hsite (fun _ h => h.2) hX0 hR hal (by show (-helloD : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
    (Spike.Lib.A64.HelloPh.HrdArena.hpool_U hpw i0)
    (Spike.Lib.A64.Flow.HelloWc.tp_wcJ0 (Jr := JrT Jr (TV) (swR (TOP) (-helloLsw) 0)) fun _ _ h => h.2.1)
    ?hmr ?hun (fun _ h => h.1) ?hmem ?hno
    (Spike.Lib.A64.Flow.HelloWc.ctl_wcJ0 fun σ c h => hJr σ c h.1) (c1J_L1 hpw i0) hpl
    (fun _ _ _ => Spike.Lib.A64.AllocG.AllocW.imp (Spike.Lib.A64.HelloPh.WcWfR.allocW_freeH hlab)
      (Spike.Lib.A64.Alloc.AllocW.triv _ _) (fun s _ h _ => hX0 s h))
    hctx rfl rfl (fun _ _ => rfl) id (Spike.Lib.A64.HelloPh.HrdArena.hlt_U hpw i0 hc)
    (Spike.Lib.A64.HelloPh.HrdArena.h64_U hpw i0 hc)
  case hmr =>
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  case hun => exact fun m hm => Spike.Lib.A64.HelloPh.HrdR.hun_FS m hm.1
  case hmem =>
    exact Spike.Lib.A64.WakePh.StartGlue.hmemB_of_wordsNone hwf (fun m h => h.1.1.wn)
      (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl]; omega)
      (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩) (hoffQ_L1 hpw i0)
  case hno =>
    intro q hq w hw
    refine Spike.Lib.A64.WakePh.WcWfR.not_ownW (heap := (MS).heap) (cells := (MS).cells) (ctr := (MS).ctr)
      (Spike.Lib.A64.HelloPh.HrdArena.offH_own hpw i0 hA13) ?_
    rcases hw with h | ⟨o', ho, h⟩
    · exact .inl h
    · refine .inr ?_
      have h1 := hoffQ_L1 hpw i0 q hq
      have hroom := hq.toS.room
      rw [hq.toS.off] at h1
      rw [Spike.Lib.A64.Alloc.Call.hdrAt] at h
      generalize q.n * (Spike.Lib.A64.Alloc.mOf q.h).toNat = k at h1 h
      omega
  exact Spike.Lib.A64.HelloPh.WcWfS.wcPreW_nmH hprog h

/-- **`hWs` at the level, the placement and the store's context left** (module doc): the box's cell mapped,
unloaded (`MainWcL1Q.hcell0_L1`) and owned at no phase (in the arena's cells, `HrdArena.offH_own`). -/
theorem hWs_L1G (hp : o.prog = SccCode.helloProg) (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    /- named premise: `.sp0` placed -/
    (hpl : WcSp0WH (PL) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1))
    /- the box store's writes' obligation in the level's context (`Land3.hwr_stH` at `Land.hctx_st1H`) -/
    (hwr : NodeW (tpG (TV) (NoWrC (AR) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
      (Spike.Lib.A64ConsumerA.updN lsW l n) (Ctx1 l b n) [])) (fun _ _ => False) (Ly).exe (Ly).endPc (RW) (FW)
      (sNH (MS) (Ly).lab (J1) .st)) :
    WcSp0WH (Spike.Lib.A64.Flow.NoMsrW (tpG (TV) (WL)) (Spike.Lib.A64.PhRec.K (Ly) (RS)))
      (Spike.Lib.A64.PhRec.K (Ly) (RS)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) := by
  have hprog : (Ly).prog = SccCode.helloProg := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw IH l x (by
      show codeOf Λ0.code.lo o.prog l = some x
      rw [hlo0, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw IH
  have hX0 := Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH (L := Ly) (a := AX) hlab rfl
  obtain ⟨hok, hal0, hF0⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hal, -⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal0 hF0
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  have hpl' := Spike.Lib.PlaceW.link IH hpw
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW hpl'
  have hb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.A64.Rt.ArenaW.heap_below_of_placeW hpl'
  have hh : (MS).heap = (Ly).Λ.heap.lo := rfl
  have hcl : (MS).cells = 4194304 := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hu2 : (MS).units 1 .int = 2 := rfl
  have hf1 : (MS).off 1 .int = 8 := rfl
  have h := Spike.Lib.A64.HelloPh.WcWfR.wcSp0W_WSgH (a := NT) (ar := AR) (p := helloSrc) (Dt := DtW)
    (Cl := Spike.Lib.A64.HelloPh.ClH (Ly)) (Ctx := Ctx1 l b n) (lbl := Spike.Lib.A64ConsumerA.upd (LB) l b)
    (lsize := Spike.Lib.A64ConsumerA.updN lsW l n) (frM := Spike.Lib.HelloRdCf.frH c0S.env)
    (X0 := X0WH (Ly) (AX)) (rS := RS) (t := TV) hprog hlo hΛ hlab hsite (fun _ h => h.2) hX0 hR hal
    (by show (-helloD : Int) ≤ -144; decide) (by show (0 : Int) ≤ 0; decide) ?hbox (c1J_L1 hpw i0) hpl hwr
  case hbox =>
    intro q o' hj hlo' hle
    have hc := Spike.Lib.A64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH (μ := μ) (rd := rd)
      (own := fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (NT) s) (I := I)
      (lbl := Spike.Lib.A64ConsumerA.upd (LB) l b) (lsize := Spike.Lib.A64ConsumerA.updN (ls0T ls) l n)
      (fs := []) (hJ_L1 hpw i0) ⟨q.1, Spike.Lib.A64.Flow.WakeWc.okb_of_tpXa q.2⟩ hj o' hlo' hle
    obtain ⟨σ, hjσ⟩ := hj
    obtain ⟨w0, w1, w2, mw, hc0⟩ := hJ_L1 hpw i0 σ _ hjσ
    have hτ := (Spike.Lib.A64.HelloPh.MainWcL1Q.box_c0H q.2 hc0).2.1
    refine ⟨hc.1.1, fun m hm => hc.2 m hm.1, Spike.Lib.A64.WakePh.WcWfR.not_ownW (heap := (MS).heap)
      (cells := (MS).cells) (ctr := (MS).ctr) (Spike.Lib.A64.HelloPh.HrdArena.offH_own hpw i0 hA13) (.inr ?_)⟩
    rw [hτ, hu2, hcl] at hle
    rw [hτ, hf1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hh]; omega), hh, hcl]
    omega
  exact Spike.Lib.A64.HelloPh.WcWfS.wcSp0W_nmH hprog h

end Spike.Lib.A64.HelloPh.MainWcL1Wp

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wp.c1J_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wp.c1J_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wp.hJ_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wp.hJ_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wp.hoffQ_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wp.hoffQ_L1

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wp.hWp_L1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wp.hWp_L1G

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1Wp.hWs_L1G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1Wp.hWs_L1G
