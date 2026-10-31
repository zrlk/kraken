/-
**`wake_start_wc_placeX` with the thread init inside `WSX` discharged**
(x86-64): `StartPlace.wake_start_wc_placeX` needs `scc_rt_thread_init`'s
states both inside `WS` (`hti`) and inside `WSX` (`htiX`); `OwnSt.tiXP`
lifts the former to the latter (the init's stores go to the TCB words
`ownSW` owns), so only `hti` is left.

Discharged here: `htiX`, by `OwnSt.tiXP` (`bandI_entry`, the two callee
regions' `OK`, `tcbS = tcbM` from `pinA_lab0`, the TCB words unmapped from
`rtF` via `tcb_rtWord`).

Left as premises: `wake_start_wc_placeX`'s minus `htiX`.

- `wake_start_wc_placeXT`: the segment inside `WSX` from `hti` alone.

Where x86-64 differs from AArch64: AArch64's root owns `ownG` and has a
single thread-init premise (`A64WakeStartPlace`); x86-64's main owns its and
the worker's TCB words (`ownGXW`, level `WSX`), so the `WS` thread init is
lifted to `WSX` here rather than carried twice.
-/
import Spike.Lib.X64WakeStartPlaceX
import Spike.Lib.X64WakeOwnStartTiP
import Spike.Lib.X64WakeRootTi

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

set_option maxHeartbeats 1600000 in

set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_main`'s heap abort at a placed output, inside
`WSX`, from the thread init inside `WS` only**: `wake_start_wc_placeX` with
`htiX` discharged by `OwnSt.tiXP` from `hti`. -/
theorem wake_start_wc_placeXT {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
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
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hpw i
  have hsep := Spike.Lib.X64.WakePh.tcbSep_W hpw i
  have ha := Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hpw i hA13
  have hW := Spike.Lib.X64.WakePh.tcb2_notG_W hpw i hA13
  have hR1 : ((entryR E).callee (-8) (-296) 8).OK :=
    Region.callee_ok (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ _; decide) (by decide)
      (by show _ < (0 : Int); decide) (by show _ ≤ (0 : Int); decide)
  have hR2 : (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8).OK :=
    Region.callee_ok hR1 (by show (-296 : Int) ≤ _; decide) (by decide) (by show _ < (8 : Int); decide)
      (by show _ ≤ (8 : Int); decide)
  have htcb : tcbS (Ly) = Spike.Lib.X64.WakePh.tcbM (Ly) := by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 = (Ly).pinA + 8#64
    rw [Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero]
  exact wake_start_wc_placeX hpw i hE hp hlo hcl hc0 hpl0 hax hs hA13 hro hC0 hfree hctr2 hcT har hP hti
    (fun F' _ _ hF' g hra => Spike.Lib.X64.WakePh.OwnSt.tiXP hp hlab hsite hsep ha hW
      (Spike.Lib.X64.WakePh.RootTi.bandI_entry hE) hR2 (Int.le_refl _) (by show (8 : Int) ≤ 8; decide) (fun m h => (hF' m h).2)
      ⟨g, tcbS (Ly), 0#64, c0⟩ htcb
      (fun b hb m h => (hF' m h).2 b (Spike.Lib.X64.WakePh.RootTi.tcb_rtWord hb)) hra (hti F' ‹_› ‹_› hF' g hra))
    hq0 hH hHi hroom hctr hoff hoB hmp hbox hWp hWs hxa

end Spike.Lib.X64.WakePh.StartPlace

/-- info: 'Spike.Lib.X64.WakePh.StartPlace.wake_start_wc_placeXT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartPlace.wake_start_wc_placeXT
