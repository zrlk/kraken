/-
**hello.w from `_start` to `wc_rodata`'s heap abort at a placed output, level 0** (x86-64; the twin of
`Spike/Lib/A64HelloStartPlace0.lean`): `StartWcS0.hello_start_rd_segWS0` at the runtime's layout
`Ly := RuntimeLayout.ofPlaceWX hpw i` with wake's x86-64 `StartPlace.wake_start_wc_place`'s choices and
discharges at hello's labels. Level 0 ends at rodata's landing, so there is no `D`, no return and no box; the new
stack's depth needs `296 ≤ Lsw` (`hL296`) directly.

Left (premises): `hc0`, `hpl0`, `hro`, `hC0`, `hA13`, `hfree`, `hctr2`, `hcT`, `hc`, and the source/frame premises
(`hWe`, `hrun`, `hJ'`, `hrd`, `hloc`, `hq`, `hxa`).

- `hello_rd_place0`: the segment. Its exit keeps the start's thread pointer (`TP (tpOf (tcbS Ly))`), and `hxa`
  may assume it; the memory side's kernel under `fr` (`hK'`) is `rfl`.

## Differences from the AArch64 version

- `scc_rt_main` runs in `call scc_rt_main`'s callee region `MainGlue.RS Lsw v` (AArch64: `swR v (-Lsw) 0`), so
  `rodata`'s call invariant `J'` is indexed by the switch base (`J' v`, as `hello_start_rd_segWS0`'s), and `hrun`,
  `hJ'`, `hrd`, `hxa` are stated at `J' v`; `hloc` only at the first stack's top `J' (topS Ly 0)` (its one use,
  as `hello_start_rd_segWS0`'s); `hxa`'s kept cells are `CKept … (-48) (-160) 8`.
- The thread pointer is `tpOf (tcbS Ly)` (AArch64: `UInt64.ofBitVec (pinA + 0 + 8)`).
- The depth bound is `296 ≤ Lsw` (AArch64 `288`), the new top `8`-aligned (from `rt_h16`), and `rS`'s shape `hrS`
  replaces AArch64's `stackM_rS0` premises.
- `htcb` and `hti` hold at every frame `F'` of the start's region `(entryR E).callee (-8) (-296) 8`
  (`startTcb_WSH` with `OwnSt.bandT_of` at `bandOffP_entry`, `StartH0Ti.htiWH_place`); AArch64 builds `BandT`
  from `offE` at the callee's offsets. The runtime words off the arena come from `CalWf.off_of` (AArch64:
  `StartH0Ti.offW_arW`).
- The owned-word frames are at depths `-184`, `-200` of the callees' regions (`offE` at `(entryR E).addr`;
  AArch64: `-240`, `-304` from the entry).
- The limit bounds are `top - 8 - 8 - 64` and `top - 8 - 8 - 64 - 8 - 8 - 32`, rewritten to `top - 80` and
  `top - 128` for `room_gWH_top` (AArch64: `top - 80`, `top - 80 - 48`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `msF_K_fr`.
-/
import Spike.Lib.X64HelloStartWcS0
import Spike.Lib.X64HelloStartPlace
import Spike.Lib.X64HelloStartTcbW
import Spike.Lib.X64HelloStartOwnA
import Spike.Lib.X64HelloStartH0Ti
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64WakeStartPlaceB
import Spike.Lib.X64WakeRootP
import Spike.Lib.Rt.X64ArenaOfPlaceW
import Spike.Lib.LowerX64.ArCallMs

namespace Spike.Lib.X64.HelloPh.StartPlace0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize Pz)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WS)
open Spike.Lib.X64 (swR At enter)
open Spike.Lib.X64.Flow.Ret0 (pinA stacksA limA tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS topS tcbS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR)
open Spike.Lib.X64.Flow.HelloRd (rN rX RdPreW)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.HelloPh.StartPlace (x0WH_tcb)
open Spike.Lib.X64.WakePh.StartPlace (offE bandOffP_entry)
open Spike.Lib.DmemPriv (WordIn)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS Frag MemSide SegWS LocalRun FrameRun Region PlaceWX)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
/-- hello's thread counter, `ownGH`'s `a`. -/
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The root's memory sides at the frames `fs`. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw i cT) (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) (AR) I L0 ls0 fs

set_option hygiene false in
/-- The start's level at the root's choices. -/
local notation "WP" => WS (Ly) NT (AR) p Dt (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx lbl lsize frM (X0WH (Ly) ax)

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) RS0

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_rodata`'s heap abort at a placed hello output, level 0**:
`StartWcS0.hello_start_rd_segWS0` with the layout, region, label, runtime-word, TCB and arena premises discharged
as in wake's `StartPlace.wake_start_wc_place` (see the module doc for what is left). -/
theorem hello_rd_place0 {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {p : Prog} {Dt : State → Prop} {Ctx : FragS isa} {lbl lbl' : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc}
    {I : Spike.Lib.X64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize} {pS : Prog} {lblS : Lbl} {fr : TermRun.Frame}
    (hp : o.prog = helloCells) (hlo : (Ly).Λ.code.lo = lo)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.X64Consumer.CFacts (Ly).Λ lbl' c0)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) L0 ls0)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64HelloGOf2H.lim2AH (Ly))
    (hcT : cT ≠ ⟨(Ly).pinA + 16#64, 8⟩) (hc : Spike.Lib.X64.Rt.CtrZ o)
    {Lsw : Int} (hL296 : 296 ≤ Lsw) (hL8 : Lsw % 8 = 0) (hLmax : Lsw ≤ 12288)
    {J' : BitVec 64 → FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (RS Lsw v) (FS (Ly) RS0 Lsw 0#64 v)
      (mNC (Ly).lab (RS Lsw v) (JS (Ly) 0#64 c0)) s c → WP s c [])
    (hrun : ∀ v σ c, (mNC (Ly).lab (RS Lsw v) (JS (Ly) 0#64 c0)).J σ c →
      ∃ c', FrameRun pS (c, []) (c', [fr]) ∧ J' v σ c')
    (hJ' : ∀ v σ c', J' v σ c' → ∃ c, (mNC (Ly).lab (RS Lsw v) (JS (Ly) 0#64 c0)).J σ c)
    (hrd : ∀ v m0 σC, RdPreW (Spike.Lib.X64.WakeTP.tpG (tpOf (tcbS (Ly))) fun s c => WP s c [fr]) KR
      (Ly).exe (Ly).endPc (mR (RS Lsw v)) (mF (RS Lsw v) (FS (Ly) RS0 Lsw 0#64 v) m0 σC) ((MSF) [fr])
      (mRdJ0 (J' v) σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J' (topS (Ly) 0#64)) σC σ c → ∃ c', LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSF) [fr]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSF) [fr]) = 3#64)
    (hxa : ∀ v m0 σC, ∀ q : AG ((MSF) [fr]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RS Lsw v) (FS (Ly) RS0 Lsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.X64.Abs (mR (RS Lsw v)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mR (RS Lsw v)) (mRdJ0 (J' v) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSF) [fr]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.X64.CKept (mR (RS Lsw v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lblS l = none →
        At (Ly).exe (Ly).endPc (aR (mR (RS Lsw v))) F' (Ea ((MSF) [fr]) q.1 l b w) s c →
        TP (tpOf (tcbS (Ly))) s → ((MSF) [fr]).xa l b w s c) :
    SegWS (WP) KR pS lblS (MSF)
      ((At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ Pz RS0 m)
        (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [])
      (Frag.at (fun s c => ∃ v m0 σC,
          At (Ly).exe (Ly).endPc (mR (RS Lsw v)) (mF (RS Lsw v) (FS (Ly) RS0 Lsw 0#64 v) m0 σC)
            (rX ((MSF) [fr]) (Ly).lab lblS (mR (RS Lsw v)) (J1 σC) .abort) s c ∧
          TP (tpOf (tcbS (Ly))) s) [fr]) := by
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hpw i
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw i hA13
  have hband := bandOffP_entry (L := Ly) hE
  have hoffW : ∀ w ∈ (Ly).rtWords, ¬ ((AR).heap ≤ w.toNat ∧ w.toNat < (AR).heap + 16 * (AR).cells) ∧
      (⟨w, 8⟩ : Loc) ≠ (AR).ctrLoc := fun w hw =>
    Spike.Lib.X64.WakePh.CalWf.off_of hpw i (by simpa using ((Ly).words_mapped _ hw).2.2 0 (by decide))
      (Spike.Lib.X64.WakePh.CalWf.ne_of_sep
        (Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hpw) _ hw))
  -- the arena (`arOf`, fs-independent) and its counter in `.data`
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceWX.link i hpw)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceWX.link i hpw) hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hoffq : ∀ fs (q : Call), (∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) →
      ((MSF) fs).off q.n q.τ ≤ 16 * ((MSF) fs).units q.n q.τ := fun fs q hacc => by
    have hu : 1 ≤ ((MSF) fs).units q.n q.τ := Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) hacc
    have hf : ((MSF) fs).off q.n q.τ = 8 := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) hacc
    rw [hf]; omega
  have hfr : ∀ m, FWN m → rtF (Ly) m := fun _ h => h.2
  have hG := fun {a v} (ha : a ∈ (Ly).rtWords) hG => ((Spike.Lib.X64.Rt.stOk_rt (μ := μ) (rd := rd)
    (G := Spike.Lib.X64HelloGOf2H.gWH hpw i cT) (own := fun s => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) (v := v)
    hfree ha hG).mono hfr)
  refine Spike.Lib.X64.HelloPh.StartWcS0.hello_start_rd_segWS0 (k0 := 0#64) (Lsw := Lsw) (ms := MSF) (pS := pS)
    (lblS := lblS) (fr := fr) (J' := J') (J1 := J1)
    hp hlo hlab hsite Spike.Lib.X64.HelloPh.ClH.cl hc0 hpl0
    (Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH hlab hax) hΛ hs hro rfl rfl hwf hC0
    (Spike.Lib.X64.Rt.wordsNoneP_and_fstable hwf hE.1 (Spike.Lib.X64.Rt.entryR_ok hE)
      (by show (-65536 : Int) < 0; decide)
      (.inl (Spike.Lib.cellsR_entry hE)) (Spike.Lib.X64.Rt.rtF_stable _ hE)).1
    (Spike.Lib.X64.WakePh.RootP.pz_rS0_fstable hE)
    (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) hfr (fun _ h => h.1)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]) hsub
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub) hL296 hL8 (by decide) ?_ ?_ ?_ ?_ ?_
    (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub)
    (fun _ _ hm => ⟨Spike.Lib.X64.Rt.wordsNoneP_takeMem hwf hsub hm.1, Spike.Lib.X64.Rt.rtF_takeMem _ hsub hm.2⟩)
    (Spike.Lib.X64.WakePh.OwnSt.hoffP_of hband) ?_
    (Spike.Lib.X64.HelloPh.StartH0Ti.htiWH_place hpw i hE hp hlo hc0 hpl0 hax hA13 hro hC0)
    ?_ (fun g => ?_) ?_ (fun g => ?_) ?_ ?_ ?_ ?_
    (fun _ => Nat.le_refl _)
    (fun fs => by
      have hh : ((MSF) fs).heap = (Ly).Λ.heap.lo := rfl
      show _ + 16 * 4194304 ≤ _; rw [hh, ← hA]; omega)
    (fun fs => by
      have hct : ((MSF) fs).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
      rw [hct]; exact .inr ⟨⟨hc1, by omega⟩, ⟨by omega, by omega⟩⟩)
    (fun q hq => hoffq _ q hq.accs)
    hWe hrun hJ' hrd hloc hq hxa
  · show (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) (by omega)
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rS0_subRD _ (by omega) (by omega)
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_houtD _ (by omega) (by omega)
  · intro F' _ _ hF' g hra
    have hR1 : ((entryR E).callee (-8) (-296) 8).OK :=
      Region.callee_ok (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ _; decide) (by decide)
        (by show _ < (0 : Int); decide) (by show _ ≤ (0 : Int); decide)
    have hR2 : (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-184) 8).OK :=
      Region.callee_ok hR1 (by show (-296 : Int) ≤ _; decide) (by decide) (by show _ < (8 : Int); decide)
        (by show _ ≤ (8 : Int); decide)
    exact Spike.Lib.X64.HelloPh.StartTcb.startTcb_WSH (rS := RS0) hp hlo hlab hsite Spike.Lib.X64.HelloPh.ClH.cl
      hc0 hpl0 (x0WH_tcb hlab hax) (Spike.Lib.X64.WakePh.OwnSt.bandT_of hband) hΛ hs hC0 hR2 (Int.le_refl _)
      (Int.le_refl _) (fun m h => hfr m (hF' m h)) ⟨g, 0#64, c0⟩ rfl rfl hra (hoffW _ (Ly).pn_mem)
      (hoffW _ (Ly).pin_mem)
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]
    have h := (Spike.Lib.X64.Rt.rt_hhdr (μ := μ) (rd := rd) (G := Spike.Lib.X64HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) hfree
      (Or.inr (Spike.Lib.X64HelloGOf2H.hGh_ofPlaceW2H hpw i))).mono hfr
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have h := hG (Ly).pn_mem (Or.inr (Spike.Lib.X64HelloGOf2H.hGt_ofPlaceW2H hpw i hctr2))
    refine Spike.Lib.X64.HelloPh.StartOwnA.tcbOkA_ownGH hlab (fun _ => rfl) ?_
      (by rw [Region.callee_addr, Region.callee_addr]; exact offE hE (by decide) (by decide))
    rw [(Ly).lab_pn]; exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    intro e he
    have h := (Spike.Lib.X64.Rt.rt_hfld (μ := μ) (rd := rd) (G := Spike.Lib.X64HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) hfree
      (fun e he => Or.inr (Spike.Lib.X64HelloGOf2H.hGf_ofPlaceW2H hpw i e he)) e he).mono hfr
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have h1 := hG (Ly).lock_mem (Or.inr (Spike.Lib.X64HelloGOf2H.hG1_ofPlaceW2H hpw i hctr2))
    have h0 := hG (Ly).lock_mem (Or.inr (Spike.Lib.X64HelloGOf2H.hG0_ofPlaceW2H hpw i hctr2))
    have hn := hG (Ly).next_mem (Or.inr (Spike.Lib.X64HelloGOf2H.hGn_ofPlaceW2H hpw i hctr2))
    have hf := (Spike.Lib.X64.Rt.ldOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.X64HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) hfree (Ly).freeN_mem).mono hfr
    refine Spike.Lib.X64.HelloPh.StartOwnA.takeOkA_ownGH hlab (fun _ => rfl) ?_ ?_ ?_ ?_
      (by rw [Region.callee_addr, Region.callee_addr, Region.callee_addr]; exact offE hE (by decide) (by decide))
    · rw [(Ly).lab_lock]; exact ⟨h1.rt, h1.mp, h1.G, h1.unmapped⟩
    · rw [(Ly).lab_freeN]; exact ⟨hf.rt, hf.mp, hf.unmapped⟩
    · rw [(Ly).lab_lock]; exact ⟨h0.rt, h0.mp, h0.G, h0.unmapped⟩
    · rw [(Ly).lab_next]; exact ⟨hn.rt, hn.mp, hn.G, hn.unmapped⟩
  · intro m hm
    (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact hm.2 _ ((Ly).fld_mem (by decide))
  · (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  all_goals ((try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0])
  · have h := (Spike.Lib.X64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.X64HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) hfree
      (Spike.Lib.X64HelloGOf2H.room_gWH_top (Z := 80) hcT
        (Spike.Lib.PlaceWX.limInit_ofPlaceWX hpw i) (by decide +kernel))).mono hfr
    rw [show ∀ x : BitVec 64, x - 8#64 - 8#64 - (64 : Int64).toBitVec = x - (80 : Int64).toBitVec from fun x => by
      simp only [show (64 : Int64).toBitVec = 64#64 from rfl, show (80 : Int64).toBitVec = 80#64 from rfl,
        BitVec.sub_sub]; rfl]
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩
  · have h := (Spike.Lib.X64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.X64HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.X64.HelloPh.ownGH (Ly) NT s) hfree
      (Spike.Lib.X64HelloGOf2H.room_gWH_top (Z := 128) hcT
        (Spike.Lib.PlaceWX.limInit_ofPlaceWX hpw i) (by decide +kernel))).mono hfr
    rw [show ∀ x : BitVec 64, x - 8#64 - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec =
        x - (128 : Int64).toBitVec from fun x => by
      simp only [show (32 : Int64).toBitVec = 32#64 from rfl, show (128 : Int64).toBitVec = 128#64 from rfl,
        BitVec.sub_sub]; rfl]
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

end Spike.Lib.X64.HelloPh.StartPlace0

/--
info: 'Spike.Lib.X64.HelloPh.StartPlace0.hello_rd_place0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartPlace0.hello_rd_place0
