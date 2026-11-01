/-
**hello.w from `_start` to `wc_main`'s heap abort at a placed output**
(AArch64; twin of `A64WakeStartPlace` +
the arena half of `A64WakeStartH0`): `StartWcS.hello_start_wc_segWS` (segments with frames, `wc_rodata` under
its frame `fr`) at the runtime's layout `Ly := RuntimeLayout.ofPlaceW hpw i`
of a hello output (`o.prog = helloProg`), the entry stack's region
`entryR E` under `WordsNoneP ∧ rtF` and the site frame `Pz rS0`, the first
stack (`k0 = 0`, `rS0`), the counter `ntA`, the arena `WakeOD.arW`, hello's
clone phase `ClH`, `X0WH … ax`, and the root's memory sides
`msOfA … (gWH hpw i cT) (ownGH Ly ntA) arW I L0 ls0 fs` (generic in `μ`,
`rd`, `I`, `L0`, `ls0`, `frM`).

Discharged here: the layout and region facts (`entryR`, `rS0`, the new
stack's region at depth `Lsw`); the labels (`hlab_ofPlaceW`,
`site_ofPlaceW`, `X0WH` by `x0WH_of_freeNH`); the runtime's store/limit
facts (`rt_*` at `gWH`, `A64StartOfPlaceW`); the counters and the take's
words owned at their nodes (`StartOwnA.tcbOkA_ownGH`, `takeOkA_ownGH`, the
callees' frames off the pool by `offE`); `scc_rt_alloc_tcb`'s states
(`htcbW`, `StartTcb.startTcb_WSH` with `x0WH_tcb`); the thread init's
(`htiW`, `StartH0Ti.htiWH_place`); the arena's heap, cells, counter and
offsets at every frame list (`hH`, `hHi`, `hctr`, `hoff`, `hoffB`, from
`arOf` and `CtrZ o`).

Left (premises): `hc0`, `hpl0`, `hro`, `hC0`, `hA13`, `hfree`, `hctr2`,
`hcT`, `hc` (as at wake), and `hello_start_wc_segWS`'s source/frame/`wc_main`
premises (`hfr`, `hWe`, `hrun`, `hJ'`, `hrd`, `hloc`, `hq`, `hxa`,
`hret`, `hPw`, as split in `hello_start_wc_segWS`).

- `x0WH_tcb`: `X0WH` in `scc_rt_alloc_tcb … scc_rt_thread_reserve`.
- `hello_start_wc_place`: the segment.
-/
import Spike.Lib.A64HelloStartWcS
import Spike.Lib.A64HelloStartTcbW
import Spike.Lib.A64HelloStartOwnA
import Spike.Lib.A64HelloStartH0Ti
import Spike.Lib.A64WakeStartPlace
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.StartPlace

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS)
open Spike.Lib.A64.Flow (swR At enter leave)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA entryN)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN RdPreW)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.DmemPriv (WordsNoneP WordIn)
open Spike.Lib (Arena FragS Frag MemSide SegWS LocalRun FrameRun Region)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

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

private theorem bv128 (b : BitVec 64) : b - (80 : Int64).toBitVec - (48 : Int64).toBitVec =
    b - (128 : Int64).toBitVec := by
  show b - 80#64 - 48#64 = b - 128#64; bv_decide

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

open Spike.Lib.A64.HelloPh.WcW (cvH freeLabsH lab_cvH clone_inCvH) in
/-- **`X0WH` inside `scc_rt_alloc_tcb`** (`startTcb_WSH`'s `hX0`): below
hello's clone (`.L22_wc_main.sp6 + 100`), off the take site. -/
theorem x0WH_tcb {L : RuntimeLayout} {ax : Int64}
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hax : ax.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) (s : State)
    (h : Spike.Lib.A64.WakePh.inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s) : X0WH L ax s := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cvH l by
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cvH hlab this.1 this.2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc.1.1
  have ey : cvH ".L22_wc_main.sp6" = y := by simp [cvH, hy]
  have e : Spike.Lib.HelloPreA.clonePcH L = y + 100 := by
    show (L.lab (".L22_wc_main" ++ ".sp6") + Int64.ofNat (4 * 25)).toBitVec.toNat = y + 100
    rw [show (".L22_wc_main" ++ ".sp6" : String) = ".L22_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 100).toNat = y + 100
    have := hc.1.2; rw [ey] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : (decide (cvH Spike.Lib.A64.Flow.Ret0.StackTake.siteL < cvH "scc_rt_alloc_tcb" ∨
      cvH "scc_rt_thread_reserve" ≤ cvH Spike.Lib.A64.Flow.Ret0.StackTake.siteL) &&
      decide (cvH "scc_rt_thread_reserve" ≤ cvH ".L22_wc_main.sp6")) = true := by
    unfold cvH; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  unfold Spike.Lib.A64.WakePh.inPc at h
  rw [hl (by simp), hl (by simp)] at h
  exact ⟨by rw [e]; omega, fun he => absurd he (by rw [hax, hl (by simp)]; omega)⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
/-- hello's thread counter, `ownGH`'s `a`. -/
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The root's memory sides at the frames `fs`. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.HelloGOf2H.gWH hpw i cT) (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) (AR) I L0 ls0 fs

set_option hygiene false in
/-- The start's level at the root's choices. -/
local notation "WP" => WS (Ly) NT (AR) p Dt (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx lbl lsize frM (X0WH (Ly) ax)

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_main`'s heap abort at a placed hello output**:
`hello_start_wc_segWS` with the layout, region, label, runtime-word, TCB
and arena premises discharged (see the module doc for what is left). -/
theorem hello_start_wc_place {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {p : Prog} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl lbl' : Lbl} {lsize : Lsize}
    {frM : TermRun.Frame} {c0 : Ctl} {ax : Int64} {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {cT : Loc}
    {I : Spike.Lib.A64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize} {pS : Prog} {lblS : Lbl} {fr : TermRun.Frame}
    (hp : o.prog = SccCode.helloProg) (hlo : (Ly).Λ.code.lo = lo)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.A64.WakeWf.RunWf p c0 [])
    (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE (Ly).Λ lbl s c0 [])
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) (hro : (Ly).Λ.rodata.Disjoint (Ly).Λ.stackPool)
    (hC0 : Spike.Lib.A64Consumer.CFacts (Ly).Λ lbl' c0)
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly) L0 ls0)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly))
    (hcT : cT ≠ ⟨(Ly).pinA + 16#64, 8⟩) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hfr : fr.σs = [])
    {Lsw D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0) (hLD : 80 + D ≤ Lsw) (hL8 : Lsw % 8 = 0)
    (hLmax : Lsw ≤ 12288)
    {J' : FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-Lsw) 0) (FS (Ly) RS Lsw 0#64 v) (mNC (Ly).lab (JS (Ly) 0#64 c0))
      s c → WP s c [])
    (hrun : ∀ σ c, (mNC (Ly).lab (JS (Ly) 0#64 c0)).J σ c → ∃ c', FrameRun pS (c, []) (c', [fr]) ∧ J' σ c')
    (hJ' : ∀ σ c', J' σ c' → ∃ c, (mNC (Ly).lab (JS (Ly) 0#64 c0)).J σ c)
    (hrd : ∀ v m0 σC, RdPreW (fun s c => WP s c [fr]) KR (Ly).exe (Ly).endPc (mR (swR v (-Lsw) 0))
      (mF (swR v (-Lsw) 0) (FS (Ly) RS Lsw 0#64 v) m0 σC) ((MSF) [fr]) (mRdJ0 J' σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 J' σC σ c → ∃ c', LocalRun pS c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSF) [fr]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSF) [fr]) = 3#64)
    {t : UInt64} {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    (hxa : ∀ v m0 σC, ∀ q : AG ((MSF) [fr]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-Lsw) 0) (FS (Ly) RS Lsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-Lsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 J' σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSF) [fr]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-Lsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lblS l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-Lsw) 0))) F' (Ea ((MSF) [fr]) q.1 l b w) s c →
        ((MSF) [fr]).xa l b w s c)
    (hret : ∀ v m0 σC σ c, (rX ((MSF) [fr]) (Ly).lab lblS (J1 σC) .sp0).J σ c → Jp v m0 σC σ c)
    (hPw : ∀ v m0 σC, MainWcPS (WP) KR pS lblS (MSF) (Ly).exe (Ly).endPc (swR v (-Lsw) 0) D
      (FS (Ly) RS Lsw 0#64 v) fr m0 σC (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC) (J2 v m0 σC) (J2' v m0 σC)
      (J3 v m0 σC) (J4 v m0 σC) (J5 v m0 σC) (Jr v m0 σC) (Jr1 v m0 σC) t) :
    SegWS (WP) KR pS lblS (MSF)
      ((At (Ly).exe (Ly).endPc (entryR E) (fun m => FWN m ∧ Spike.Lib.A64Consumer.Pz RS m)
        (entryN (Ly).lab c0)).at [])
      (fun s c fs => Frag.at (fun s c => ∃ v m0 σC m1 σ1,
          At (Ly).exe (Ly).endPc (wcR (swR v (-Lsw) 0) D) (wcF (swR v (-Lsw) 0) D (FS (Ly) RS Lsw 0#64 v) m1 σ1)
            (wXH ((MSF) []) (Ly).lab (wcJ0 (mWC (Ly).lab σC (Jr1 v m0 σC)).J σ1) .abort) s c ∧ TP t s) [] s c fs ∨
        Frag.at (fun s c => ∃ v m0 σC,
          At (Ly).exe (Ly).endPc (mR (swR v (-Lsw) 0)) (mF (swR v (-Lsw) 0) (FS (Ly) RS Lsw 0#64 v) m0 σC)
            (rX ((MSF) [fr]) (Ly).lab lblS (J1 σC) .abort) s c) [fr] s c fs) := by
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW i hpw
  have hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceW.hlab_ofPlaceW hpw i l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hsite := Spike.Lib.PlaceW.site_ofPlaceW hpw i
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hSM := Spike.Lib.LowerA64.stackM_rS0 (Ly) hE
  have hs := Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hpw i hA13
  have hbd : Spike.Lib.A64.WakePh.StartTcb.BandT (Ly) ((entryR E).callee Spike.Lib.A64.Abort.oI.sp (-192) 0) :=
    fun k h1 h2 => offE hE (d := (48 - k).toNat) (by
      simp only [Region.callee, Region.addr, BitVec.add_assoc, ← BitVec.ofInt_add]
      congr 2; show (-48 : Int) + k = _; omega) (by omega) (by omega)
  have hoffW := Spike.Lib.A64.WakePh.StartH0Ti.offW_arW hpw i
  -- the arena (`arOf`, fs-independent) and its counter in `.data`
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.A64.Rt.ArenaW.PlaceW.heapSize_of_placeW (Spike.Lib.PlaceW.link i hpw)
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link i hpw)
  obtain ⟨hc1, hc2, -⟩ : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ ∧
      Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size ∧ _ :=
    Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link i hpw) hc
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hoffq : ∀ fs (q : Call), (∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) →
      ((MSF) fs).off q.n q.τ ≤ 16 * ((MSF) fs).units q.n q.τ := fun fs q hacc => by
    have hu : 1 ≤ ((MSF) fs).units q.n q.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) hacc
    have hf : ((MSF) fs).off q.n q.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) hacc
    rw [hf]; omega
  have hFw : ∀ m, FWN m → rtF (Ly) m := fun _ h => h.2
  have hG := fun {a v} (ha : a ∈ (Ly).rtWords) hG => ((Spike.Lib.A64.Rt.stOk_rt (μ := μ) (rd := rd)
    (G := Spike.Lib.HelloGOf2H.gWH hpw i cT) (own := fun s => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) (v := v)
    hfree ha hG).mono hFw)
  refine Spike.Lib.A64.HelloPh.StartWcS.hello_start_wc_segWS (k0 := 0#64) (Lsw := Lsw) (ms := MSF) (pS := pS)
    (lblS := lblS) (fr := fr) (D := D) (t := t) (J' := J') (J1 := J1)
    hp hlo hlab hsite (fun _ h => h.2) hc0 hpl0
    (Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH hlab hax) hΛ hs hro rfl rfl hfr hwf hC0
    (Spike.Lib.A64.Rt.wordsNoneP_and_fstable hwf hE.1 (Spike.Lib.A64.Rt.entryR_ok hE)
      (by show (-65536 : Int) < 0; decide)
      (.inl (Spike.Lib.cellsR_entry hE)) (Spike.Lib.A64.Rt.rtF_stable _ hE)).1
    (Spike.Lib.A64.WakePh.StartH0Ti.pz_fstable_entry hE)
    (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ -304; decide)
    (by show (0 : Int) ≤ 0; decide) (fun _ h => h.2) (fun _ h => h.1) (by rw [Spike.Lib.A64.Rt.stacksA_lab0]) hsub
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) hSM.1 hSM.2.1 hSM.2.2 (by omega) hL8 (by decide) ?_ ?_ ?_ ?_ ?_
    (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub)
    (fun _ _ hm => ⟨Spike.Lib.A64.Rt.wordsNoneP_takeMem hwf hsub hm.1, Spike.Lib.A64.Rt.rtF_takeMem _ hsub hm.2⟩)
    (offE hE rfl (by decide) (by decide))
    (Spike.Lib.A64.HelloPh.StartTcb.startTcb_WSH hp hlo hlab hsite (fun _ h => h.2) hc0 hpl0
      (x0WH_tcb hlab hax) hbd hΛ hs hC0 (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE)
      (by show (-65536 : Int) ≤ -240; decide) (by show (0 : Int) ≤ 0; decide) (fun _ h => h.2) rfl
      (hoffW _ (Ly).pn_mem) (hoffW _ (Ly).pin_mem))
    (Spike.Lib.A64.HelloPh.StartH0Ti.htiWH_place hpw i hE hp hlo hc0 hpl0 hax hA13 hro hC0)
    ?_ (fun g => ?_) ?_ (fun g => ?_) ?_ ?_ ?_ ?_
    (fun _ => Nat.le_refl _)
    (fun fs => by
      have hh : ((MSF) fs).heap = (Ly).Λ.heap.lo := rfl
      show _ + 16 * 4194304 ≤ _; rw [hh, ← hA]; omega)
    (fun fs => by
      have hct : ((MSF) fs).ctr = Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := rfl
      rw [hct]; exact .inr ⟨⟨hc1, by omega⟩, ⟨by omega, by omega⟩⟩)
    (fun q hq => hoffq _ q hq.accs) (fun q hq => hoffq _ q hq.toS.accs)
    hWe hrun hJ' hrd hloc hq hD hD16 hLD hxa hret hPw
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by omega) (by omega)
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by omega) (by omega)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    exact Spike.Lib.A64.Rt.rt_houtD _ (by omega) (by omega)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]
    have h := hG (by rw [BitVec.add_zero]; exact (Ly).pin_mem) (Or.inr (Spike.Lib.HelloGOf2H.hGh_ofPlaceW2H hpw i))
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have h := hG (Ly).pn_mem (Or.inr (Spike.Lib.HelloGOf2H.hGt_ofPlaceW2H hpw i hctr2))
    refine Spike.Lib.A64.HelloPh.StartOwnA.tcbOkA_ownGH hΛ hlab (fun _ => rfl) ?_
      (offE hE (d := 240) (by simp only [Region.callee, Region.addr]; exact bv240 _) (by decide) (by decide))
    rw [(Ly).lab_pn]; exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    intro e he
    have h := (Spike.Lib.A64.Rt.rt_hfld (μ := μ) (rd := rd) (G := Spike.Lib.HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) hfree
      (fun e he => Or.inr (Spike.Lib.HelloGOf2H.hGf_ofPlaceW2H hpw i e he)) e he).mono hFw
    exact ⟨h.rt, h.mp, h.G, h.unmapped⟩
  · have h1 := hG (Ly).lock_mem (Or.inr (Spike.Lib.HelloGOf2H.hG1_ofPlaceW2H hpw i hctr2))
    have h0 := hG (Ly).lock_mem (Or.inr (Spike.Lib.HelloGOf2H.hG0_ofPlaceW2H hpw i hctr2))
    have hn := hG (Ly).next_mem (Or.inr (Spike.Lib.HelloGOf2H.hGn_ofPlaceW2H hpw i hctr2))
    have hf := (Spike.Lib.A64.Rt.ldOk_rt (μ := μ) (rd := rd) (G := Spike.Lib.HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) hfree (Ly).freeN_mem).mono hFw
    refine Spike.Lib.A64.HelloPh.StartOwnA.takeOkA_ownGH hΛ hlab (fun _ => rfl) ?_ ?_ ?_ ?_
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
  · have h := (Spike.Lib.A64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) hfree (Spike.Lib.HelloGOf2H.room_gWH_top
        (Z := 80) hcT (Spike.Lib.PlaceW.limInit_ofPlaceW hpw i) (by decide))).mono hFw
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩
  · rw [bv128]
    have h := (Spike.Lib.A64.Rt.rt_limOk (μ := μ) (rd := rd) (G := Spike.Lib.HelloGOf2H.gWH hpw i cT)
      (own := fun s => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s) hfree (Spike.Lib.HelloGOf2H.room_gWH_top
        (Z := 128) hcT (Spike.Lib.PlaceW.limInit_ofPlaceW hpw i) (by decide))).mono hFw
    exact ⟨h.rt, h.mp, h.unmapped, h.room⟩

end Spike.Lib.A64.HelloPh.StartPlace

/-- info: 'Spike.Lib.A64.HelloPh.StartPlace.x0WH_tcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartPlace.x0WH_tcb

/--
info: 'Spike.Lib.A64.HelloPh.StartPlace.hello_start_wc_place' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartPlace.hello_start_wc_place
