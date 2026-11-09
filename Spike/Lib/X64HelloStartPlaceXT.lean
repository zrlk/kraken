/-
**hello.w from `_start` to `wc_rodata`'s heap abort at a placed output, level 0, at `ownGHXW`, with the thread
init inside `WSHX` discharged** (x86-64; the hello counterpart of `Spike/Lib/X64WakeStartPlaceXT.lean`):
`StartPlaceX.hello_rd_placeX` needs `scc_rt_thread_init`'s states inside `WSHX` (`htiX`); `OwnSt.tiXPH` lifts
`StartH0Ti.htiWH_place` (the same states inside `WSH`) to them.

Discharged here: `htiX`, by `OwnSt.tiXPH` at `htiWH_place` (`bandI_entry`, the init's callee region `OK`,
`tcbS = tcbM` from `pinA_lab0`, the TCB words unmapped from `rtF` via `tcb_rtWord`).

Left as premises: `hello_rd_placeX`'s minus `htiX`.

- `hello_rd_placeXT`: the segment inside `WSHFg (ownGHXW Ly ntA)` without a thread-init premise.

## Differences from the AArch64 version

AArch64's root owns `ownGH` and discharges its single thread-init obligation in `A64HelloStartPlace0`; x86-64's
main also owns its and the worker's TCB words (`ownGHXW`), so the `WSH` thread init is lifted to `WSHX` here.
Against x86-64 wake's `StartPlaceXT`: the `WSH` thread init is itself discharged (`htiWH_place`), so no
thread-init premise is left, and `hW` is about the worker's word `tcbWH` (`tcbWH_notG_W`).
-/
import Spike.Lib.X64HelloStartPlaceX
import Spike.Lib.X64HelloOwnStartTiP
import Spike.Lib.X64WakeRootTi

namespace Spike.Lib.X64.HelloPh.StartPlaceX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.X64Consumer (Lbl Lsize Pz)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
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
/-- hello's thread counter, `ownGHXW`'s `a`. -/
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "FWN" => fun m : MachineData => WordsNoneP (Ly).Λ m.dmem ∧ rtF (Ly) m

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The root's memory sides at the frames `fs`, owning `ownGHXW`. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw i cT) (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT s) (AR) I L0 ls0 fs

set_option hygiene false in
/-- The start's level at `ownGHXW` with frames, at the root's choices. -/
local notation "WP" => fun s c fs => Spike.Lib.X64.HelloWf.WSHFg (Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT) (Ly) (AR) p Dt
  (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx lbl lsize frM (X0WH (Ly) ax) fs s c

set_option hygiene false in
local notation "KR" => Spike.Lib.X64.PhRec.K (Ly) RS0

set_option maxHeartbeats 1600000 in
/-- **From `_start` to `wc_rodata`'s heap abort at a placed hello output, level 0, at `ownGHXW`, without a
thread-init premise**: `hello_rd_placeX` with `htiX` by `OwnSt.tiXPH` at `StartH0Ti.htiWH_place`. -/
theorem hello_rd_placeXT {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
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
  have hlab : ∀ l x, codeLabel lo helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw i l x (by rw [hlo, hp]; exact h)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hpw i
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw i hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : Spike.Lib.X64.WakePh.tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw i hA13
  have hR1 : ((entryR E).callee (-8) (-296) 8).OK :=
    Region.callee_ok (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ _; decide) (by decide)
      (by show _ < (0 : Int); decide) (by show _ ≤ (0 : Int); decide)
  have hR2 : (((entryR E).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8).OK :=
    Region.callee_ok hR1 (by show (-296 : Int) ≤ _; decide) (by decide) (by show _ < (8 : Int); decide)
      (by show _ ≤ (8 : Int); decide)
  have htcb : tcbS (Ly) = Spike.Lib.X64.WakePh.tcbM (Ly) := by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 = (Ly).pinA + 8#64
    rw [Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero]
  exact hello_rd_placeX hpw i hE hp hlo hc0 hpl0 hax hA13 hro hC0 hfree hctr2 hcT hc hL296 hL8 hLmax
    (fun F' hF1 hF2 hF' g hra => Spike.Lib.X64.HelloPh.OwnSt.tiXPH hp hlab hsite hsep ha hW
      (Spike.Lib.X64.WakePh.RootTi.bandI_entry hE) hR2 (Int.le_refl _) (by show (8 : Int) ≤ 8; decide)
      (fun m h => (hF' m h).2) ⟨g, tcbS (Ly), 0#64, c0⟩ htcb
      (fun b hb m h => (hF' m h).2 b (Spike.Lib.X64.WakePh.RootTi.tcb_rtWord hb)) hra
      (Spike.Lib.X64.HelloPh.StartH0Ti.htiWH_place hpw i hE hp hlo hc0 hpl0 hax hA13 hro hC0 F' hF1 hF2 hF' g hra))
    hWe hrun hJ' hrd hloc hq hxa

end Spike.Lib.X64.HelloPh.StartPlaceX

/-- info: 'Spike.Lib.X64.HelloPh.StartPlaceX.hello_rd_placeXT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartPlaceX.hello_rd_placeXT
