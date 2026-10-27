/-
**The loaded thread's run is one segment at depth** (AArch64, H7a calls):
the start of `a64_start_segW1` (`Spike/Lib/LowerA64/StartSeg1.lean`) over
segments with frames, the user function's interface a `UserCallWS` inside
the runtime's obligations (`StartAllUWS`), at any callee room `D` of the
user `main` (the new stack's region of depth `D + 48`, `bareMC`'s frame 48
and the callee's `D`).

- `a64_start_segWS`: `entry_segW'` lifted at the empty frames, then
  `startU_segWS`; the runtime's arithmetic at the depth `D + 48`
  (`rt_hokD`, `rS0_subRD`, `rt_houtD`) and its memory-side facts at the
  memory side with no frame `ms []` (`hms`, the placement's).
-/
import Spike.Lib.LowerA64.StartSeg1
import Spike.Lib.Rt.A64SegsS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (CFacts SFacts Lbl Lsize msOf)
open Spike.Lib.A64.Rt (RuntimeLayout StartAllUWS nilW bareMC rtF entryR)
open Spike.Lib.A64.Flow.Ret0 (StackM limA)
open Spike.Lib.A64.PhRec (μ K)

section StartS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max => msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.A64.PhRec.own (Ly)) lbl lsize

/-- **The loaded thread's run is one segment inside `W` at depth**, for any
program `p` and memory side with frames `ms` (the placement's with no
frame, `hms`): `_start`'s block and the runtime's states inside `W` at the
empty frames (`hEntry`, `hW`), the user `main` a `UserCallWS` with the
callee room `D` (`hW.s3.user`), `main`'s exit for every control and value
the user function's post relates, after the source's frame run back to
depth 0 (`hexit`, `MainExitS`); from the entry frame condition `FE`
(implying `rtF`, stable in the entry stack's region and kept by the take,
`hFE`, `hFEs`, `hFEk`), whose private memory's facts `U` (`hUF`, kept in
the new stack's region, `hUS`) the user function's frame condition
carries. -/
theorem a64_start_segWS (hs : o.place.tail = .bare) {p : Prog} {W : FragS isaLSE2}
    {ms : List TermRun.Frame → MemSide isaLSE2} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl}
    {lsize : Lsize} (hms : ms [] = MS rd G lbl lsize)
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hD : D + 48 ≤ 16384) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hGh : G ⟨(Ly).pinA + 0#64, 8⟩ ((Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128))
    (hGf : ∀ e ∈ Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      G ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128))
    (hGt : G ⟨(Ly).pnA, 8⟩ ((0#64 + Ret0.AllocTcb.tcbLen).setWidth 128))
    (hownT : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.AllocTcb.rmwPc (Ly).lab)
      (Ly).pnA 0#64)
    (hG1 : G ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128)) (hG0 : G ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨(Ly).nextA, 8⟩ ((0#64 + Ret0.StackTake.size0).setWidth 128))
    (hownL : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.swpPc (Ly).lab)
      (Ly).lockA 0#64)
    (hownF : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.freeNPc (Ly).lab)
      (Ly).freeNA 0#64)
    (hownN : Ret0.OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.nextPc (Ly).lab)
      (Ly).nextA 0#64)
    (hroomM : ∀ v : Val, G ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec).toNat)
    (hroomU : ∀ v : Val, G ⟨limA (UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec - ZU.toBitVec).toNat)
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab bareMC.sp0 + 4 + 4 + 4, ⟨-bareMC.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (Ret0.takeMem pm (Spike.Lib.A64.Rt.rS0 (Ly)) m))
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, FE m → U m.dmem)
    (hUS : FStable (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 48)) 0) fun m => U m.dmem)
    (hEntry : BlkW (nilW W) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) (Ly).exe (Ly).endPc (entryR E) FE
      (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0) Ret0.entryB)
    (hW : StartAllUWS W (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) p lbl (Ly).exe (Ly).endPc (entryR E) FE ms
      (Spike.Lib.A64.Rt.rS0 (Ly)) 0#64 0#64 Spike.Lib.A64Consumer.c0 (D + 48) bareMC D ZU Post U)
    {Q : FragS isaLSE2} :
    SegWS W (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) p lbl ms
      ((At (Ly).exe (Ly).endPc (entryR E) FE (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0)).at []) Q := by
  have hrc := Spike.Lib.A64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly) hsub
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 48)) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by omega) (by omega)
  have h16' : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hZ48 : bareMC.Z.toInt = 48 := by decide
  refine (SegWS.liftS [] (Spike.Lib.A64.Rt.entry_segW' (p := p) (lbl := lbl) (ms := ms []) (Ly).lays rfl hrc.entry
    hFEs (Spike.Lib.A64.Rt.entryR_ok hE)
    (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 0; decide)
    Spike.Lib.A64Consumer.c0 hEntry) fun _ _ h => h).seq ?_
  refine Spike.Lib.A64.Rt.startU_segWS (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.tail hrc.ti hrc.tiSp hrc.take
    hrc.main (by omega) (by omega) (by decide) (D := D) hD0 hD8 (L := D + 48)
    (by omega) (by rw [hms]; rfl) hFEs (Spike.Lib.A64.Rt.entryR_ok hE)
    (Spike.Lib.A64.Rt.entryR_al hE)
    (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide) 0#64 0#64 Spike.Lib.A64Consumer.c0
        (by decide) ?_ ?_ (by decide) ?_ ?_ h16' hok ?_ ?_ ?_
    ?_ ?_ hexit (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) hfit (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub)
    hFEk hUF hUS hW
  · rw [hms, Spike.Lib.A64.Rt.pinA_lab0]; exact (Spike.Lib.A64.Rt.rt_hhdr hfree hGh).mono hFE
  · rw [hms]; exact (Spike.Lib.A64.Rt.rt_tcbOk hfree hGt hownT).mono hFE
  · rw [hms, Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    exact fun e he => (Spike.Lib.A64.Rt.rt_hfld hfree hGf e he).mono hFE
  · rw [hms]; exact (Spike.Lib.A64.Rt.rt_takeOk hfree hG1 hG0 hGn hownL hownF hownN).mono hFE
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by omega) (by omega)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    exact Spike.Lib.A64.Rt.rt_houtD _ (by omega) (by omega)
  · rw [hms, Spike.Lib.A64.Rt.pinA_lab0]; exact (Spike.Lib.A64.Rt.rt_limOk hfree hroomM).mono hFE
  · rw [hms, Spike.Lib.A64.Rt.pinA_lab0]; exact (Spike.Lib.A64.Rt.rt_limOk hfree hroomU).mono hFE

end StartS

end Spike.Lib.LowerA64
