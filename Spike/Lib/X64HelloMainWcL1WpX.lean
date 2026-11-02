/-
**`MainWcPS.hWp`, `hWs` at `Level1I`'s choices at `ownGHXW`, the placement and the context left** (x86-64 only;
the `ownGHXW` counterpart of `X64HelloMainWcL1Wp`): `wc_main` up to the allocator's return and its `.x22` lie in
the level `W1Hg (ownGHXW Ly ntA) … Ctx1 … l b n` at no frame (which is `WSHX`), guarded by main's thread pointer,
inside `NoSetFsW`, at the level's memory side owning `ownGHXW`'s words.

`WcWfRX.wcPreW_WSgHX`/`wcSp0W_WSgHX` at the level, the premises discharged as in `X64HelloMainWcL1Wp`, plus
`ownGHXW`'s separation (`StartPlaceLy.wsep_W`, `tcbWH_notG_W`, from A13), `wc_main`'s band on the pool
(`bandOnP_RW`), the counter and header words off `tcbM` (the runtime words' separation, `ne_tcbM_of_heap`) and the
box's cell off `tcbM` (`WakePh.hboxM_of`). Left: the placement `hpl` and the level's context `hctx`/`hwr`.

- `hoffQ_L1X`: the arena's offset within its units at the level's memory side at `ownGHXW`, at a box call.
- `bandOnP_RW`: `wc_main`'s region at the first stack's top on the pool over `[-304, 8]`.
- `hWp_L1GX`, `hWs_L1GX`: the statements, generic in the level's context `Ctx1` and `wc_rodata`'s return
  invariant `Jr`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there, so its level is at `ownGH` only. Against
`X64HelloMainWcL1Wp`: the level and the memory side are at `ownGHXW`, and the producers take the separation, band
and `tcbM` facts above, all discharged here from A13 and the layout.
-/
import Spike.Lib.X64HelloMainWcL1Wp
import Spike.Lib.X64HelloWcWfRX
import Spike.Lib.X64HelloHrdRootX

namespace Spike.Lib.X64.HelloPh.MainWcL1Wp

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open Spike.Lib (FragS PlaceWX Region)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
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
/-- The level's memory side at no frame, under main's thread pointer, at `ownGHXW`. -/
local notation "MS" => tpXa (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s)
  (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- `wc_main`'s entry invariant (`wc_rodata`'s return `Jr`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT Jr (TV) (RM))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

set_option hygiene false in
/-- The level at no frame, at `ownGHXW`. -/
local notation "WL" => fun s c => Spike.Lib.X64.HelloWf.W1Hg (Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT)) (Ly) (AR)
  helloSrc DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx1 (LB) lsW (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- The placement at the level's labels, no frame. -/
local notation "PL" => fun s c => Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (Spike.Lib.X64ConsumerA.upd (LB) l b) s c []

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls lsW : Lsize}
  {l : WeakMem.AllocLabel} {b n : Nat} {Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {Jr : FAS → Spike.Lib.Ctl → Prop} {σC σ1 : FAS} {m1 : MachineData}

/-- The arena's offset is at most its units' room at every box call at `ownGHXW` (`hoffQ_L1`'s). -/
theorem hoffQ_L1X : ∀ q : Call, q.OKB (MS) (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ := by
  intro q hq
  have hu := Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  have hf := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  rw [hq.one]
  show (Spike.Lib.X64.Rt.arOf (Ly).Λ).off 1 q.τ ≤ 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).units 1 q.τ
  rw [hf]; omega

/-- **`wc_main`'s region at the first stack's top is on the pool over `[-304, 8]`**: `scc_rt_main`'s over
`[-384, -72]` (`HrdRootX.bandRS`), `wc_main`'s at `-80` in it. -/
theorem bandOnP_RW : BandOnP (Ly) (RW) (-304) 8 := by
  obtain ⟨hok, -, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hbRS : BandOnP (Ly) (RM) (-384) 8 :=
    Spike.Lib.X64.HelloPh.HrdRootX.bandRS (show (8 - helloLsw : Int) ≤ -384 by decide)
      (show helloLsw < 16384 by decide) hok
  intro k h1 h2
  have e : (RW).addr k = (RM).addr (-80 + k) := Region.callee_addr _ (-80) (-helloD) 8 k
  rw [e]; exact hbRS _ (by omega) (by omega)

/-- **`hWp` at the level at `ownGHXW`, the placement and the context left** (`hWp_L1G` at `ownGHXW` by
`WcWfRX.wcPreW_WSgHX`; `ownGHXW`'s separation from A13, the band by `bandOnP_RW`, the allocator's words off
`tcbM`). -/
theorem hWp_L1GX (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
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
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  have hbW : BandOnP (Ly) (RW) (-304) 8 := bandOnP_RW hpw i0
  have h := Spike.Lib.X64.HelloPh.WcWfRX.wcPreW_WSgHX (a := NT) (ar := AR) (p := helloSrc) (Dt := DtW)
    (Cl := Spike.Lib.X64.HelloPh.ClH (Ly)) (Ctx := Ctx1 l b n) (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN lsW l n) (frM := Spike.Lib.X64HelloRdCf.frH c0S.env)
    (X0 := X0WH (Ly) (AX)) (rS := RS0) (t := TV) (ms := MS) (F := FW) hprog hlo hΛ hlab
    hsite (Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)) hX0 hsep ha hW hbW hR hR8 (by show (-helloD : Int) ≤ -304; decide)
    (by show (8 : Int) ≤ 8; decide)
    (Spike.Lib.X64.HelloPh.HrdArena.hpool_U hpw i0)
    (Spike.Lib.X64.Flow.HelloWc.tp_wcJ0 (Jr := JrT Jr (TV) (RM)) fun _ _ h => h.2.1)
    ?hmr ?hun (fun _ h => h.1) ?hmem ?hno ?hnoM
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
      (.inr ⟨by rw [hct]; exact ⟨hc1, by omega⟩, by rw [hct]; exact ⟨by omega, by omega⟩⟩) (hoffQ_L1X hpw i0)
  case hno =>
    intro q hq w hw
    refine Spike.Lib.X64.WakePh.WcWfR.not_ownW (heap := (MS).heap) (cells := (MS).cells) (ctr := (MS).ctr)
      (Spike.Lib.X64.HelloPh.HrdArena.offH_own hpw i0 hA13) ?_
    rcases hw with h | ⟨o', ho, h⟩
    · exact .inl h
    · refine .inr ?_
      have h1 := hoffQ_L1X hpw i0 q hq
      have hroom := hq.toS.room
      rw [hq.toS.off] at h1
      rw [Spike.Lib.X64.Alloc.Call.hdrAt] at h
      generalize q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat = k at h1 h
      omega
  case hnoM =>
    intro q hq w hw
    rcases hw with rfl | ⟨o', ho, h⟩
    · intro he
      have hsep' : Scc.Cert.Rt.X64.WordSep (tcbM (Ly)) (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
        Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX IH hpw) _
          ((Ly).fld_mem (i := 0) (by decide))
      rw [← he, hct] at hsep'
      unfold Scc.Cert.Rt.X64.WordSep at hsep'
      omega
    · have h1 := hoffQ_L1X hpw i0 q hq
      rw [hq.toS.off] at h1
      rw [Spike.Lib.X64.Alloc.Call.hdrAt, hh] at h
      rw [hcl] at ho
      have hn := Spike.Lib.X64.WakePh.ne_tcbM_of_heap (L := Ly) hwf (c := w.toNat) w.isLt (by
        simp only [Scc.Sem.Range.contains]
        generalize q.n * (Spike.Lib.X64.Alloc.mOf q.h).toNat = k at h1 h
        generalize (MS).units q.n q.τ = u at h1 ho
        omega)
      simpa using hn
  exact Spike.Lib.X64.HelloPh.WcWfS.wcPreW_nsH hprog h

/-- **`hWs` at the level at `ownGHXW`, the placement and the store's context left** (`hWs_L1G` at `ownGHXW` by
`WcWfRX.wcSp0W_WSgHX`): the box's cell mapped, unloaded (`MainWcL1Q.hcell0_L1`), owned at no phase (in the arena's
cells, `HrdArena.offH_own`) and off `tcbM` (`WakePh.hboxM_of`). -/
theorem hWs_L1GX (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
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
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  have hbW : BandOnP (Ly) (RW) (-144) 8 := Spike.Lib.X64.WakePh.OwnMid.bandOnP_mono (bandOnP_RW hpw i0) (by decide)
    (Int.le_refl _)
  have hwf : (Ly).Λ.WF := Spike.Lib.PlaceWX.wf_link_of_placeWX IH hpw
  have hboxM := Spike.Lib.X64.WakePh.hboxM_of (L := Ly) hwf (ms := MS) (lab := (Ly).lab)
    (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl]; omega) (by rw [hh, hcl]; omega)
    (P := fun q => ∃ σ, (J1) σ q.1.c0) (fun q ⟨σ, hjσ⟩ => by
      obtain ⟨w0, w1, w2, mw, hc0⟩ := hJ_L1 hpw i0 σ _ hjσ
      have hτ := (Spike.Lib.X64.HelloPh.MainWcL1Q.box_c0H q.2 hc0).2.1
      rw [hτ, hu2, hf1]; decide)
  have h := Spike.Lib.X64.HelloPh.WcWfRX.wcSp0W_WSgHX (a := NT) (ar := AR) (p := helloSrc) (Dt := DtW)
    (Cl := Spike.Lib.X64.HelloPh.ClH (Ly)) (Ctx := Ctx1 l b n) (lbl := Spike.Lib.X64ConsumerA.upd (LB) l b)
    (lsize := Spike.Lib.X64ConsumerA.updN lsW l n) (frM := Spike.Lib.X64HelloRdCf.frH c0S.env)
    (X0 := X0WH (Ly) (AX)) (rS := RS0) (t := TV) hprog hlo hΛ hlab hsite
    (Spike.Lib.X64.HelloPh.ClH.cl (L := Ly)) hX0 hsep ha hW hbW hR
    (by show (-helloD : Int) ≤ -136; decide) (by show (8 : Int) ≤ 8; decide) ?hbox hboxM (c1J_L1 hpw i0) hpl hwr
  case hbox =>
    intro q o' hj hlo' hle
    have hc := Spike.Lib.X64.HelloPh.MainWcL1Q.hcell0_L1 hpw IH (μ := μ) (rd := rd)
      (own := fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s) (I := I)
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

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hoffQ_L1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hoffQ_L1X

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.bandOnP_RW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.bandOnP_RW

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hWp_L1GX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hWp_L1GX

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hWs_L1GX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hWs_L1GX
