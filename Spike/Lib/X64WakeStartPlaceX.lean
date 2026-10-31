/-
**From `_start` to `wc_main`'s heap abort at a placed output, at `ownGXW`**
(x86-64): `StartPlace.wake_start_wc_place` with the root's memory side
owning `ownGXW Ly ntA` (main's and the worker's TCB words appended to
`ownG`'s) and the start's level `OwnImp.WSX`, through
`MainGlue.wake_start_wc_segWX`.

Discharged here, besides `wake_start_wc_place`'s: `ownGXW`'s separation
(`hsep` by `tcbSep_W`, `ha` by `tcbM_ne_ntA_W`, `hW` by `tcb2_notG_W`, the
last two from A13's data part `hA13`); `scc_rt_alloc_tcb`'s states inside
`WSX` (`htcbX`, by `OwnSt.startTcbX`); the counters and the take's words
owned at their nodes under `ownGXW` (`tcbOkA_ownGXW`, `takeOkA_ownGXW`).

Left as premises: `wake_start_wc_place`'s, with `hs` at the thread counter
`ntA`, plus `hA13` and `htiX` (the thread init's states inside `WSX`, as
`Rt.TiWAtP`); `hWp`, `hWs` inside `WSX`.

- `wake_start_wc_placeX`: the segment inside `WSX`.

Where x86-64 differs from AArch64: AArch64's root memory side owns `ownG`
(`A64WakeStartPlace`); x86-64's main also holds its own and the worker's TCB
words (`ownS`, `ownSW`), so the memory side owns `ownGXW` and the level is
`WSX`. `MainGlue.wake_start_wc_segWX` needs the thread init's states inside
both levels (`hti` inside `WS`, `htiX` inside `WSX`); the counter word `a`
is fixed to `ntA` (where A13 separates the TCB words from it).
-/
import Spike.Lib.X64WakeStartPlace
import Spike.Lib.X64WakeMainGlueX
import Spike.Lib.X64WakeStartOwnAX
import Spike.Lib.X64WakeOwnStartG
import Spike.Lib.X64WakeOwnSW
import Spike.Lib.X64WakeOwnT2W

namespace Spike.Lib.X64.WakePh.StartPlace

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64 (swR At)
open Spike.Lib.X64.Flow.Ret0 (pinA stacksA limA tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W AGB BoxW bX wX)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.DmemPriv (WordIn)
open Spike.Lib.X64.DmemPriv (WordsNoneP)
open Spike.Lib (Arena FragS SegW Region PlaceWX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "MS" => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd (Spike.Lib.X64WakeOG.gW hpw i cT)
  (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) ar' I L0 ls0 []

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "WSL" => WS (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) ar p Dt Cl Ctx lbl lsize frM (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

set_option hygiene false in
local notation "WSXL" => WSX (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) ar p Dt Cl Ctx lbl lsize frM (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_main`'s heap abort at a placed output, inside
`WSX`**: `wake_start_wc_segWX` with the layout, region, label and
runtime-word premises discharged (see the module doc for what is left). -/
theorem wake_start_wc_placeX {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl lbl' : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc}
    {ar' : Arena} {I : Spike.Lib.X64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize} {pS : Prog} {lblS : Lbl}
    (hp : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hs : Spike.Lib.X64.WakePh.WSep (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab))
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.X64Consumer.CFacts (Ly).Λ lbl' c0)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) L0 ls0)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.X64WakeGOf2.lim2A (Ly))
    (hcT : cT ≠ ⟨(Ly).pinA + 16#64, 8⟩)
    (har : ar.heap = (Ly).Λ.heap.lo ∧ ar.cells = Scc.Cert.PlaceOK.allocCells ∧
      ar.ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)
    {P : MachineData → Prop} (hP : Spike.Lib.X64.FStable (entryR E) P)
    (hti : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable ((entryR E).callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K (Ly) RS0) F' → (∀ m, F' m → FWN m) →
      ∀ g, g.ra = ((Ly).lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ j,
      Spike.Lib.X64.Rt.TiWAtP WSL (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc
        (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM RS0)
        ⟨g, tcbS (Ly), 0#64, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L P j)
    (htiX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable ((entryR E).callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K (Ly) RS0) F' → (∀ m, F' m → FWN m) →
      ∀ g, g.ra = ((Ly).lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ j,
      Spike.Lib.X64.Rt.TiWAtP WSXL (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc
        (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM RS0)
        ⟨g, tcbS (Ly), 0#64, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L P j)
    (hq0 : ∃ q : Call, q.OKB MS (Ly).lab ∧ q.c0 = c0 ∧ q.h = 256#64 ∧ q.k = 1#64 ∧ q.u MS = 2#64)
    (hH : (Ly).Λ.heap.lo ≤ (MS).heap) (hHi : (MS).heap + 16 * (MS).cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size)
    (hroom : (MS).heap + 16 * (MS).cells ≤ 2 ^ 64)
    (hctr : WordIn (Ly).Λ.heap (MS).ctr ∨ WordIn (Ly).Λ.data (MS).ctr)
    (hoff : ∀ q : Call, q.OKB MS (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ)
    (hoB : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → (MS).off 1 q.1.τ + 16 ≤ 16 * (MS).units 1 q.1.τ)
    (hmp : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → ∀ o : Nat, (MS).lo o → o + (MS).units 1 q.1.τ ≤ (MS).cells →
      (MS).mp ⟨BitVec.ofNat 64 ((MS).heap + 16 * o + (MS).off 1 q.1.τ), 8⟩ true)
    (hbox : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → BoxW lblS q.1)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.X64.NoSetFsW (Spike.Lib.X64.WakeTP.tpG (tpOf (tcbS (Ly))) WSXL)
        (Spike.Lib.X64.PhRec.K (Ly) RS0))
      (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
      (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
      (tpXa MS (tpOf (tcbS (Ly)))) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC)
      (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.X64.NoSetFsW (Spike.Lib.X64.WakeTP.tpG (tpOf (tcbS (Ly))) WSXL)
        (Spike.Lib.X64.PhRec.K (Ly) RS0))
      (Spike.Lib.X64.PhRec.K (Ly) RS0) (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD)
      (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
      (tpXa MS (tpOf (tcbS (Ly)))) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC))
    (hxa : ∀ v m0 σC l A s c, lblS l = none →
      At (Ly).exe (Ly).endPc ((wR (RS wcLsw v) wcD).fp (-8)) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
        (bX MS (Ly).lab (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) l A) s c →
      TP (tpOf (tcbS (Ly))) s → (MS).xa l A 1 s c) :
    SegW WSXL (Spike.Lib.X64.PhRec.K (Ly) RS0) pS lblS MS
      (At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ P m) (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0))
      (fun s c => ∃ v m0 σC,
        At (Ly).exe (Ly).endPc (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) RS0 wcLsw 0#64 v) m0 σC)
          (wX MS (Ly).lab (wR (RS wcLsw v) wcD) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) .abort) s c ∧
        TP (tpOf (tcbS (Ly))) s) := by
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hpw
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hpw i
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfr : ∀ m, FWN m → rtF (Ly) m := fun _ h => h.2
  have hband := bandOffP_entry (L := Ly) hE
  have hoffW : ∀ w ∈ (Ly).rtWords, ¬ (ar.heap ≤ w.toNat ∧ w.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨w, 8⟩ : Loc) ≠ ar.ctrLoc := fun w hw => by
    obtain ⟨hh, hc, hu⟩ := har
    have hm := ((Ly).words_mapped w hw).2.2 0 (by decide)
    obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (show (Ly).Λ.WF from hwf).disjoint
    have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
      Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX (Spike.Lib.PlaceWX.link i hpw)
    have hsep : Scc.Cert.Rt.X64.WordSep w (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
      Scc.Cert.Rt.X64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceWX.rtWordsOk_link_of_placeWX i hpw) w hw
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint, Scc.Cert.Rt.X64.WordSep] at hm hdh hph hsep
    refine ⟨by rw [hh, hc]; omega, fun he => ?_⟩
    have := congrArg (fun l : Loc => l.addr.toNat) he
    simp only [Arena.ctrLoc, hu] at this
    omega
  have hsep := Spike.Lib.X64.WakePh.tcbSep_W hpw i
  have ha := Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hpw i hA13
  have hW := Spike.Lib.X64.WakePh.tcb2_notG_W hpw i hA13
  have htcbX := Spike.Lib.X64.WakePh.OwnSt.startTcbX (rS := RS0) (ar := ar) (p := p) (Dt := Dt) (Ctx := Ctx)
    (lsize := lsize) (frM := frM) hp hlo hlab hsite hsep ha hW hcl hc0 hpl0 (x0W_tcb hlab hax) hΛ hs hC0
    (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
    hband hfr rfl (hoffW _ (Ly).pn_mem) (hoffW _ (Ly).pin_mem)
  refine Spike.Lib.X64.WakePh.MainGlue.wake_start_wc_segWX (k0 := 0#64) (Lsw := wcLsw) (D := wcD) hp hlo hlab
    hsite hcl hc0 hpl0 (Spike.Lib.X64.WakePh.StartGlue.x0W_of_freeN hlab hax) hΛ hs hsep ha hW hro rfl hwf hC0
    (Spike.Lib.X64.Rt.wordsNoneP_and_fstable hwf hE.1 (Spike.Lib.X64.Rt.entryR_ok hE)
      (by show (-65536 : Int) < 0; decide)
      (.inl (cellsR_entry hE)) (Spike.Lib.X64.Rt.rtF_stable _ hE)).1 hP
    (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) hfr (fun _ h => h.1) (by (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]) hsub
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub) (by decide) (by decide) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_ ?_ (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub)
    (fun _ _ hm => ⟨Spike.Lib.X64.Rt.wordsNoneP_takeMem hwf hsub hm.1, Spike.Lib.X64.Rt.rtF_takeMem _ hsub hm.2⟩)
    (Spike.Lib.X64.WakePh.OwnSt.hoffP_of hband) ?_ hti htcbX htiX ?_ (fun g => ?_) ?_ (fun g => ?_) ?_ ?_ ?_ ?_
    hq0 hH hHi hroom hctr hoff hoB hmp hbox hWp hWs hxa
  · show (stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0
    (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by decide) (by decide)
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ (by decide) (by decide)
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_houtD _ (by decide) (by decide)
  · intro F' _ _ hF' g hra
    have hR1 : ((entryR E).callee (-8) (-296) 8).OK :=
      Region.callee_ok (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ _; decide) (by decide)
        (by show _ < (0 : Int); decide) (by show _ ≤ (0 : Int); decide)
    have hR2 : (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-184) 8).OK :=
      Region.callee_ok hR1 (by show (-296 : Int) ≤ _; decide) (by decide) (by show _ < (8 : Int); decide)
        (by show _ ≤ (8 : Int); decide)
    exact Spike.Lib.X64.WakePh.StartTcb.startTcb_WS (rS := RS0) hp hlo hlab hsite hcl hc0 hpl0
      (x0W_tcb hlab hax) (Spike.Lib.X64.WakePh.OwnSt.bandT_of hband) hΛ hs hC0 hR2 (Int.le_refl _)
      (Int.le_refl _) (fun m h => hfr m (hF' m h)) ⟨g, 0#64, c0⟩ rfl rfl hra (hoffW _ (Ly).pn_mem)
      (hoffW _ (Ly).pin_mem)
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]
    have h := (Spike.Lib.X64.Rt.rt_hhdr (μ := μ) (rd := rd) (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (Or.inr (Spike.Lib.PlaceWX.hGh_ofPlaceW2 hpw i))).mono hfr
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have h := (Spike.Lib.X64.Rt.stOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (Ly).pn_mem (Or.inr (Spike.Lib.PlaceWX.hGt_ofPlaceW2 hpw i hctr2))).mono hfr
    refine Spike.Lib.X64.WakePh.tcbOkA_ownGXW hlab (fun _ => rfl) ?_
      (by rw [Region.callee_addr, Region.callee_addr]; exact offE hE (by decide) (by decide))
    rw [(Ly).lab_pn]; exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    intro e he
    have h := (Spike.Lib.X64.Rt.rt_hfld (μ := μ) (rd := rd) (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (fun e he => Or.inr (Spike.Lib.PlaceWX.hGf_ofPlaceW2 hpw i e he)) e he).mono hfr
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have ho := fun {a v} (ha : a ∈ (Ly).rtWords) hG => ((Spike.Lib.X64.Rt.stOk_rt (μ := μ) (rd := rd)
      (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (v := v)
      hfree ha hG).mono hfr)
    have h1 := ho (Ly).lock_mem (Or.inr (Spike.Lib.PlaceWX.hG1_ofPlaceW2 hpw i hctr2))
    have h0 := ho (Ly).lock_mem (Or.inr (Spike.Lib.PlaceWX.hG0_ofPlaceW2 hpw i hctr2))
    have hn := ho (Ly).next_mem (Or.inr (Spike.Lib.PlaceWX.hGn_ofPlaceW2 hpw i hctr2))
    have hf := (Spike.Lib.X64.Rt.ldOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (Ly).freeN_mem).mono hfr
    refine Spike.Lib.X64.WakePh.takeOkA_ownGXW hlab (fun _ => rfl) ?_ ?_ ?_ ?_
      (by rw [Region.callee_addr, Region.callee_addr, Region.callee_addr]; exact offE hE (by decide) (by decide))
    · rw [(Ly).lab_lock]; exact ⟨h1.rt, h1.mp, h1.G, h1.unmapped⟩
    · rw [(Ly).lab_freeN]; exact ⟨hf.rt, hf.mp, hf.unmapped⟩
    · rw [(Ly).lab_lock]; exact ⟨h0.rt, h0.mp, h0.G, h0.unmapped⟩
    · rw [(Ly).lab_next]; exact ⟨hn.rt, hn.mp, hn.G, hn.unmapped⟩
  · intro m hm
    (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact hm.2 _ ((Ly).fld_mem (by decide))
  · (try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  all_goals ((try simp only [Spike.Lib.X64.WakePh.MainGlue.topS, Spike.Lib.X64.WakePh.MainGlue.tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0])
  · have h := (Spike.Lib.X64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (Spike.Lib.X64.WakePh.StartGlue.room_gW_top (Z := 48) hcT
        (Spike.Lib.PlaceWX.limInit_ofPlaceWX hpw i) (by decide +kernel))).mono hfr
    rw [show ∀ x : BitVec 64, x - 8#64 - 8#64 - (32 : Int64).toBitVec = x - (48 : Int64).toBitVec from fun x => by
      simp only [show (32 : Int64).toBitVec = 32#64 from rfl, show (48 : Int64).toBitVec = 48#64 from rfl]; bv_omega]
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩
  · have h := (Spike.Lib.X64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.X64WakeOG.gW hpw i cT)
      (own := fun s => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (Spike.Lib.X64.WakePh.StartGlue.room_gW_top (Z := 128) hcT
        (Spike.Lib.PlaceWX.limInit_ofPlaceWX hpw i) (by decide +kernel))).mono hfr
    rw [show ∀ x : BitVec 64, x - 8#64 - 120#64 = x - (128 : Int64).toBitVec from fun x => by
      simp only [show (128 : Int64).toBitVec = 128#64 from rfl]; bv_omega]
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

end Spike.Lib.X64.WakePh.StartPlace

/-- info: 'Spike.Lib.X64.WakePh.StartPlace.wake_start_wc_placeX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlace.wake_start_wc_placeX
