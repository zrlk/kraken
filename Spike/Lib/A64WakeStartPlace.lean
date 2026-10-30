/-
**From `_start` to `wc_main`'s heap abort at a placed output** (AArch64): `MainGlue.wake_start_wc_segW` at the runtime's layout
`Ly := RuntimeLayout.ofPlaceW hpw i` of an output with wake's placement
facts, the entry stack's region `entryR E` under `WordsNone ∧ rtF`, the
first stack (`k0 = 0`, `rS0`), `D = 336`, `Lsw = 384`, and the root's memory
side `msOfA … (gW hpw i cT) (ownG Ly ntA) … []` (wake's `G` and owned
words, `WakeOD.wakeD`).

Discharged here: the layout and region facts (`entryR`, `rS0`, the new
stack's region); the labels (`hlab_ofPlaceW`, `site_ofPlaceW`, `X0W` by
`x0W_of_freeN`); the runtime's store/limit facts (`rt_*` at `gW` by
`A64StartOfPlaceW`); the counters and the take's words owned at their nodes
(`tcbOkA_ownG`, `takeOkA_ownG`, the callees' frames off the pool by
`pool_clear`); `scc_rt_alloc_tcb`'s states (`htcbW`, by `startTcb_WS`: its pcs' `X0W`, its frame off the pool, the runtime's words
off the arena, given the arena's heap, cells and counter, `har`, all `rfl`
at `WakeOD.arW`).

Left as premises:
- `htiW` (the thread init's states, its take site at the entry fact
  `P`, stable in `entryR E`, `hP`), `hc0`, `hpl0`, `hC0`, `hs`;
- `hcl`, `hq0`, `hH`, `hHi`, `hroom`, `hctr`, `hoff`, `hoB`, `hmp`,
  `hbox`, `hWp`, `hWs`, `hxa` (the box's call and cells, `wc_main` inside `W`);
- the concrete layout: `hp`, `hlo`, `hro`, `hctr2`, `hcT`, `hfree`.

- `wake_start_wc_place`: the segment.
-/
import Spike.Lib.A64WakeStartFacts
import Spike.Lib.A64WakeStartOwnA
import Spike.Lib.A64WakeStartTcbW
import Spike.Lib.Rt.A64ArenaOfPlaceW
import Spike.Lib.A64StartOfPlaceW
import Spike.Lib.A64SiteOfPlaceW
import Spike.Lib.WakeOG
import Spike.Lib.LowerA64.Correct

namespace Spike.Lib.A64.WakePh.StartPlace

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W AGB BoxW bX wX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP WordIn)
open Spike.Lib (Arena FragS SegW Region)

/-- `x - k` as `x + ofInt (-k)`, `k ≤ x`. -/
private theorem toNat_addNeg {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) :
    (x + BitVec.ofInt 64 (-(k : Int))).toNat = x.toNat - k := by
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofInt]
  have : ((-(k : Int)) % (2 ^ 64 : Nat) : Int).toNat = if k = 0 then 0 else 2 ^ 64 - k := by split <;> omega
  rw [this]; split <;> omega

private theorem bv240 (b : BitVec 64) : b + BitVec.ofInt 64 (-48) + BitVec.ofInt 64 (-192) =
    b + BitVec.ofInt 64 (-240) := by bv_decide

private theorem bv304 (b : BitVec 64) : b + BitVec.ofInt 64 (-48) + BitVec.ofInt 64 (-48) + BitVec.ofInt 64 (-208) =
    b + BitVec.ofInt 64 (-304) := by bv_decide

/-- **A word `d` below the entry `sp` is off the stack pool** (`d` within
the entry region; the pool is clear of the entry stack, `pool_clear`). -/
private theorem offE {L : RuntimeLayout} {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {x : BitVec 64} {d : Nat}
    (hx : x = (entryR E).base + BitVec.ofInt 64 (-(d : Int))) (h0 : 0 < d) (h1 : d < 65536) :
    ¬ (L.Λ.stackPool.lo < x.toNat ∧ x.toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) := by
  have hb := Spike.Lib.A64.Rt.entryR_base hE
  have := Spike.Lib.A64.Rt.entry_sp hE
  have hd := Spike.Lib.A64.Rt.pool_clear L hE.1
  have hs := Spike.Lib.A64.Rt.entryR_sub hE
  have hspd : E.sp = E.stack.lo + E.stack.size := rfl
  simp only [Scc.Sem.Range.Disjoint, Scc.Sem.Range.Sub] at hd hs
  rw [hx, toNat_addNeg (by omega), hb]
  omega

open Spike.Lib.A64.WakePh.WcW (cv freeLabs lab_cv clone_inCv) in
/-- **`X0W` inside `scc_rt_alloc_tcb`** (`startTcb_WS`'s `hX0`): below
`wc_main`'s clone, off the take site. -/
private theorem x0W_tcb {L : RuntimeLayout} {ax : Int64}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) (s : State)
    (h : Spike.Lib.A64.WakePh.inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s) :
    Spike.Lib.A64.WakeWf.X0W L ax s := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cv l by
    have := List.all_eq_true.mp freeLabs l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cv hlab this.1 this.2
  have hc := clone_inCv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc.1.1
  have ey : cv ".L21_wc_main.sp6" = y := by simp [cv, hy]
  have e : Spike.Lib.A64.Flow.WakeWc.clonePc L = y + 52 := by
    show (L.lab (".L21_wc_main" ++ ".sp6") + Int64.ofNat (4 * 13)).toBitVec.toNat = y + 52
    rw [show (".L21_wc_main" ++ ".sp6" : String) = ".L21_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 52).toNat = y + 52
    have := hc.1.2; rw [ey] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : (decide (cv Spike.Lib.A64.Flow.Ret0.StackTake.siteL < cv "scc_rt_alloc_tcb" ∨
      cv "scc_rt_thread_reserve" ≤ cv Spike.Lib.A64.Flow.Ret0.StackTake.siteL) &&
      decide (cv "scc_rt_thread_reserve" ≤ cv ".L21_wc_main.sp6")) = true := by
    unfold cv; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  unfold Spike.Lib.A64.WakePh.inPc at h
  rw [hl (by simp), hl (by simp)] at h
  exact ⟨by rw [e]; omega, fun he => absurd he (by rw [hax, hl (by simp)]; omega)⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "MS" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd (Spike.Lib.WakeOG.gW hpw i cT)
  (fun s _ => ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) ar' I L0 ls0 []

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

/-- **From `_start` to `wc_main`'s heap abort at a placed output**:
`wake_start_wc_segW` with the layout, region, label and runtime-word
premises discharged (see the module doc for what is left). -/
theorem wake_start_wc_place {a : BitVec 64} {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl lbl' : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc}
    {ar' : Arena} {I : Spike.Lib.A64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize} {pS : Prog} {lblS : Lbl}
    (hp : o.prog = wakeProg) (hlo : (Ly).Λ.code.lo = lo)
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hs : Spike.Lib.A64.WakePh.WSep (Ly) a) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.A64Consumer.CFacts (Ly).Λ lbl' c0)
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly) L0 ls0)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.WakeGOf2.lim2A (Ly))
    (hcT : cT ≠ ⟨(Ly).pinA + 16#64, 8⟩)
    (har : ar.heap = (Ly).Λ.heap.lo ∧ ar.cells = Scc.Cert.PlaceOK.allocCells ∧
      ar.ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)
    {P : MachineData → Prop} (hP : Spike.Lib.A64.Flow.FStable (entryR E) P)
    (htiW : ∀ g, g.ra = ((Ly).lab Spike.Lib.A64.Flow.Ret0.sp3L).toBitVec → ∀ j,
      Spike.Lib.A64.Flow.Ret0.TiW (WS (Ly) a ar p Dt Cl Ctx lbl lsize frM (Spike.Lib.A64.WakeWf.X0W (Ly) ax))
        (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-256) 0)
        FWN (Spike.Lib.A64.Flow.Ret0.StackM RS) ⟨g, pinA (Ly).lab + 0#64 + 8#64, 0#64, c0⟩ j P)
    (hq0 : ∃ q : Call, q.OKB MS (Ly).lab ∧ q.c0 = c0 ∧ q.h = 256#64 ∧ q.k = 1#64 ∧ q.u MS = 2#64)
    (hH : (Ly).Λ.heap.lo ≤ (MS).heap) (hHi : (MS).heap + 16 * (MS).cells ≤ (Ly).Λ.heap.lo + (Ly).Λ.heap.size)
    (hroom : (MS).heap + 16 * (MS).cells ≤ 2 ^ 64)
    (hctr : WordIn (Ly).Λ.heap (MS).ctr ∨ WordIn (Ly).Λ.data (MS).ctr)
    (hoff : ∀ q : Call, q.OKB MS (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ)
    (hoB : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → (MS).off 1 q.1.τ + 16 ≤ 16 * (MS).units 1 q.1.τ)
    (hmp : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → ∀ o : Nat, (MS).lo o → o + (MS).units 1 q.1.τ ≤ (MS).cells →
      (MS).mp ⟨BitVec.ofNat 64 ((MS).heap + 16 * o + (MS).off 1 q.1.τ), 8⟩ true)
    (hbox : ∀ q : AGB MS (Ly).lab, q.1.c0 = c0 → BoxW lblS q.1)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WS (Ly) a ar p Dt Cl Ctx lbl lsize frM
        (Spike.Lib.A64.WakeWf.X0W (Ly) ax))) (Spike.Lib.A64.PhRec.K (Ly) RS)) (Spike.Lib.A64.PhRec.K (Ly) RS)
      (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MS (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)))
      (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WS (Ly) a ar p Dt Cl Ctx lbl lsize frM
        (Spike.Lib.A64.WakeWf.X0W (Ly) ax))) (Spike.Lib.A64.PhRec.K (Ly) RS)) (Spike.Lib.A64.PhRec.K (Ly) RS)
      (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MS (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC))
    (hxa : ∀ v m0 σC l A s c, lblS l = none →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
        (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
        (bX MS (Ly).lab (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) l A) s c →
      TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) s → (MS).xa l A 1 s c) :
    SegW (WS (Ly) a ar p Dt Cl Ctx lbl lsize frM (Spike.Lib.A64.WakeWf.X0W (Ly) ax))
      (Spike.Lib.A64.PhRec.K (Ly) RS) pS lblS MS
      (Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ P m)
        (Spike.Lib.A64.Flow.Ret0.entryN (Ly).lab c0))
      (fun s c => ∃ v m0 σC,
        Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
          (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
          (wX MS (Ly).lab (wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC) .abort) s c ∧
        TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) s) := by
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hlab : ∀ l x, codeOf lo wakeProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hSM := Spike.Lib.LowerA64.stackM_rS0 (Ly) hE
  have hfr : ∀ m, FWN m → rtF (Ly) m := fun _ h => h.2
  have hbd : Spike.Lib.A64.WakePh.StartTcb.BandT (Ly) ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-192) 0) :=
    fun k h1 h2 => offE hE (d := (48 - k).toNat) (by
      simp only [Region.callee, Region.addr, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2; show (-48 : Int) + k = _; omega) (by omega) (by omega)
  have hoffW : ∀ w ∈ (Ly).rtWords, ¬ (ar.heap ≤ w.toNat ∧ w.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨w, 8⟩ : Loc) ≠ ar.ctrLoc := fun w hw => by
    obtain ⟨hh, hc, hu⟩ := har
    have hm := ((Ly).words_mapped w hw).2.2 0 (by decide)
    obtain ⟨-, -, -, hdh, -, -, -, -, hph, -⟩ := (show (Ly).Λ.WF from hwf).disjoint
    have hs : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
      Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hpw)
    have hsep : Scc.Cert.Rt.A64.WordSep w (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) :=
      Scc.Cert.Rt.A64.ctrSep_of_rtWordsOk (Spike.Lib.PlaceW.rtWordsOk_link_of_placeW i hpw) w hw
    simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint, Scc.Cert.Rt.A64.WordSep] at hm hdh hph hsep
    refine ⟨by rw [hh, hc]; omega, fun he => ?_⟩
    have := congrArg (fun l : Loc => l.addr.toNat) he
    simp only [Arena.ctrLoc, hu] at this
    omega
  refine Spike.Lib.A64.WakePh.MainGlue.wake_start_wc_segW (k0 := 0#64) (Lsw := 384) (D := 336) hp hlo hlab
    (Spike.Lib.PlaceW.site_ofPlaceW hpw i) hcl hc0 hpl0
    (Spike.Lib.A64.WakePh.StartGlue.x0W_of_freeN hlab hax) hΛ hs hro rfl hwf hC0
    (Spike.Lib.A64.Rt.wordsNoneP_and_fstable hwf hE.1 (Spike.Lib.A64.Rt.entryR_ok hE)
      (by show (-65536 : Int) < 0; decide)
      (.inl (cellsR_entry hE)) (Spike.Lib.A64.Rt.rtF_stable _ hE)).1 hP
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) hfr (fun _ h => h.1) (by rw [Spike.Lib.A64.Rt.stacksA_lab0]) hsub
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) hSM.1 hSM.2.1 hSM.2.2 (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_ ?_ ?_ ?_ ?_ (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub)
    (fun _ _ hm => ⟨Spike.Lib.A64.Rt.wordsNoneP_takeMem hwf hsub hm.1, Spike.Lib.A64.Rt.rtF_takeMem _ hsub hm.2⟩)
    (offE hE rfl (by decide) (by decide))
    (Spike.Lib.A64.WakePh.StartTcb.startTcb_WS hp hlo hlab (Spike.Lib.PlaceW.site_ofPlaceW hpw i) hcl hc0 hpl0
      (x0W_tcb hlab hax) hbd hΛ hs hC0 (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE)
      (by show (-65536 : Int) ≤ -240; decide) (by show (0 : Int) ≤ 0; decide) hfr rfl (hoffW _ (Ly).pn_mem)
      (hoffW _ (Ly).pin_mem)) htiW ?_ (fun g => ?_) ?_ (fun g => ?_) ?_ ?_ ?_ ?_
    hq0 hH hHi hroom hctr hoff hoB hmp hbox hWp hWs hxa
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]
    have h := (Spike.Lib.A64.Rt.rt_hhdr (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT) (own := fun s => ownG (Ly)
      (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) hfree (Or.inr (Spike.Lib.PlaceW.hGh_ofPlaceW2 hpw i))).mono hfr
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have h := (Spike.Lib.A64.Rt.stOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT) (own := fun s => ownG (Ly)
      (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) hfree (Ly).pn_mem
      (Or.inr (Spike.Lib.PlaceW.hGt_ofPlaceW2 hpw i hctr2))).mono hfr
    refine Spike.Lib.A64.WakePh.tcbOkA_ownG hΛ hlab (fun _ => rfl) ?_
      (offE hE (d := 240) (by simp only [Region.callee, Region.addr]; exact bv240 _) (by decide) (by decide))
    rw [(Ly).lab_pn]; exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    intro e he
    have h := (Spike.Lib.A64.Rt.rt_hfld (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT) (own := fun s => ownG (Ly)
      (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) hfree
      (fun e he => Or.inr (Spike.Lib.PlaceW.hGf_ofPlaceW2 hpw i e he)) e he).mono hfr
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have ho := fun {a v} (ha : a ∈ (Ly).rtWords) hG => ((Spike.Lib.A64.Rt.stOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT)
      (own := fun s => ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (v := v) hfree ha hG).mono hfr)
    have h1 := ho (Ly).lock_mem (Or.inr (Spike.Lib.PlaceW.hG1_ofPlaceW2 hpw i hctr2))
    have h0 := ho (Ly).lock_mem (Or.inr (Spike.Lib.PlaceW.hG0_ofPlaceW2 hpw i hctr2))
    have hn := ho (Ly).next_mem (Or.inr (Spike.Lib.PlaceW.hGn_ofPlaceW2 hpw i hctr2))
    have hf := (Spike.Lib.A64.Rt.ldOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT)
      (own := fun s => ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) hfree (Ly).freeN_mem).mono hfr
    refine Spike.Lib.A64.WakePh.takeOkA_ownG hΛ hlab (fun _ => rfl) ?_ ?_ ?_ ?_
      (offE hE (d := 304) (by simp only [Region.callee, Region.addr]; exact bv304 _) (by decide) (by decide))
    · rw [(Ly).lab_lock]; exact ⟨h1.rt, h1.mp, h1.G, h1.unmapped⟩
    · rw [(Ly).lab_freeN]; exact ⟨hf.rt, hf.mp, hf.unmapped⟩
    · rw [(Ly).lab_lock]; exact ⟨h0.rt, h0.mp, h0.G, h0.unmapped⟩
    · rw [(Ly).lab_next]; exact ⟨hn.rt, hn.mp, hn.G, hn.unmapped⟩
  · intro m hm
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact hm.2 _ ((Ly).fld_mem (by decide))
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  all_goals rw [Spike.Lib.A64.Rt.pinA_lab0]
  · have h := (Spike.Lib.A64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT) (own := fun s => ownG (Ly)
      (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) hfree (Spike.Lib.A64.WakePh.StartGlue.room_gW_top (Z := 48) hcT
        (Spike.Lib.PlaceW.limInit_ofPlaceW hpw i) (by decide))).mono hfr
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩
  · have h := (Spike.Lib.A64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.WakeOG.gW hpw i cT) (own := fun s => ownG (Ly)
      (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) hfree (Spike.Lib.A64.WakePh.StartGlue.room_gW_top (Z := 128) hcT
        (Spike.Lib.PlaceW.limInit_ofPlaceW hpw i) (by decide))).mono hfr
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

end Spike.Lib.A64.WakePh.StartPlace

/-- info: 'Spike.Lib.A64.WakePh.StartPlace.wake_start_wc_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartPlace.wake_start_wc_place
