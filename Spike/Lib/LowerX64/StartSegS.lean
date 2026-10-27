/-
**The loaded thread's run is one segment at depth** (x86-64, H7a calls):
the start of `x64_start_segW1` (`Spike/Lib/LowerX64/StartSeg1.lean`) with
`_start`'s segment in front, over segments with frames, the user function's
interface a `UserCallWS` inside the runtime's obligations (`StartAllUWS`),
at any callee room `D` of the user `main` (the new stack's region of depth
`D + 56`: `bareMC`'s frame 32 under the saved `%rbp`, the two return
addresses and the callee's `D`). The x86-64 twin of
`Spike/Lib/LowerA64/StartSegS.lean`.

- `x64_start_segWS`: `entry_segWS'`, its callee `startU_segWS` for every
  frame condition stable in `_start`'s callee region, kept by the take and
  implying `rtF`; the runtime's arithmetic at the depth `D + 56`
  (`rt_hokD`, `rS0_subRD`, `rt_houtD`) and its memory-side facts at the
  memory side with no frame `ms []` (`hms`, the placement's).

Where x86-64 differs from AArch64: `_start` calls `scc_rt_start`, so the
runtime's obligations `hW` are asked in that call's callee region `EC E` for
every such frame condition (as `x64_start_segW1`'s `hgen`), and `_start`'s
obligations are `EntryW`.
-/
import Spike.Lib.LowerX64.StartSeg1
import Spike.Lib.Rt.X64SegsS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize msOf)
open Spike.Lib.X64.Rt (RuntimeLayout StartAllUWS EntryW nilW bareMC rtF entryR entryN0)
open Spike.Lib.X64.Flow.Ret0 (StackM limA tpOf startN0)
open Spike.Lib.X64.PhRec (μ K)

section StartS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max =>
  msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.X64.PhRec.own (Ly)) lbl lsize

/-- The callee region of `_start`'s call at the entry state `E`, where
`scc_rt_start` runs. -/
local notation "EC" E:max => (entryR E).callee (-8) (-296) 8

/-- **The loaded thread's run is one segment inside `W` at depth**, for any
program `p` and memory side with frames `ms` (the placement's with no
frame, `hms`): `_start`'s states and the runtime's inside `W` at the empty
frames (`hEntry`, `hW`), the user `main` a `UserCallWS` with the callee room
`D` (`(hW …).s3.user`), `main`'s exit for every control and value the user
function's post relates, after the source's frame run back to depth 0
(`hexit`, `MainExitS`); from the entry frame condition `FE` (implying
`rtF`, stable in the entry stack's region and kept by the take, `hFE`,
`hFEs`, `hFEk`), whose private memory's facts `U` (`hUF`, kept in the new
stack's region, `hUS`) the user function's frame conditions carry. -/
theorem x64_start_segWS (hs : o.place.tail = .bare) {p : Prog} {W : FragS isa}
    {ms : List TermRun.Frame → MemSide isa} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl}
    {lsize : Lsize} (hms : ms [] = MS rd G lbl lsize)
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hD : D + 56 ≤ 16384) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hGh : G ⟨(Ly).pinA + 0#64, 8⟩ ((Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36).setWidth 128))
    (hGf : ∀ e ∈ Ret0.ThreadInit.fields ((Ly).pinA + 0#64 + 8#64) ((Ly).stacksA + 0#64),
      G ⟨(Ly).pinA + 0#64 + 8#64 + BitVec.ofNat 64 e.1, 8⟩ (e.2.setWidth 128))
    (hGt : G ⟨(Ly).pnA, 8⟩ ((0#64 + Ret0.AllocTcb.tcbLen).setWidth 128))
    (hownT : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.AllocTcb.rmwPc (Ly).lab) (Ly).pnA 0#64)
    (hG1 : G ⟨(Ly).lockA, 8⟩ ((1#64).setWidth 128)) (hG0 : G ⟨(Ly).lockA, 8⟩ ((0#64).setWidth 128))
    (hGn : G ⟨(Ly).nextA, 8⟩ ((0#64 + Ret0.StackTake.size0).setWidth 128))
    (hownL : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.swpPc (Ly).lab) (Ly).lockA 0#64)
    (hownF : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.freeNPc (Ly).lab) (Ly).freeNA 0#64)
    (hownN : OwnAt (MS rd G lbl lsize) (Ly).exe (Ly).endPc (Ret0.StackTake.nextPc (Ly).lab) (Ly).nextA 0#64)
    (hroomM : ∀ v : Val, G ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec).toNat)
    (hroomU : ∀ v : Val, G ⟨limA (tpOf ((Ly).pinA + 0#64 + 8#64)), 8⟩ v →
      (v.setWidth 64).toNat ≤ (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - bareMC.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec).toNat)
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At (Ly).exe (Ly).endPc R' F' ⟨(Ly).lab bareMC.sp0 + Int64.ofNat bareMC.ze0 + Int64.ofNat bareMC.ze1 +
        Int64.ofNat bareMC.ze2, ⟨-8 - bareMC.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ (ms []).abortAt s → MainExitS p (ms []) s c v.toNat)
    {FE : MachineData → Prop} (hFE : ∀ m, FE m → rtF (Ly) m) (hFEs : FStable (entryR E) FE)
    (hFEk : ∀ m pm, FE m → FE (Ret0.takeMem pm (Spike.Lib.X64.Rt.rS0 (Ly)) m))
    {U : _root_.Mem 64 → Prop} (hUF : ∀ m, FE m → U m.dmem)
    (hUS : FStable (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 56)) 0) fun m => U m.dmem)
    (hEntry : EntryW (nilW W) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) (Ly).exe (Ly).endPc (entryR E) FE
      (Ly).lab Spike.Lib.X64Consumer.c0)
    (hW : ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) F' →
      (∀ m, F' m → rtF (Ly) m) →
      StartAllUWS W (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) p lbl (Ly).exe (Ly).endPc (EC E) F' ms
        (Spike.Lib.X64.Rt.rS0 (Ly)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (D + 56) bareMC D ZU Post U)
    {Q : FragS isa} :
    SegWS W (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) p lbl ms
      ((At (Ly).exe (Ly).endPc (entryR E) FE (entryN0 (Ly).lab Spike.Lib.X64Consumer.c0)).at []) Q := by
  have hrc := Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  obtain ⟨hZ, hZ8, hps, hkm⟩ := Spike.Lib.X64.Rt.bareMC_ok
  have hZ32 : bareMC.Z.toInt = 32 := by decide
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(D + 56)) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) (by omega)
  have hEC := ec_facts _ hE hsub
  refine Spike.Lib.X64.Rt.entry_segWS' (p := p) (lbl := lbl) (ms := ms) (Ly).lays rfl hrc.start0
    hFEs (Spike.Lib.X64.Rt.entryR_ok hE) (Spike.Lib.X64.Rt.entryR_al hE)
    (by show (-65536 : Int) ≤ -8 + -296; decide) (by show (0 : Int) ≤ 0; decide)
    (Ret0.TakeK.kstable fun _ _ hm => hFEk _ _ hm)
    (fun _ _ hk _ k hk' => by
      obtain ⟨pm, he⟩ := hk.mem; rw [he]
      exact Ret0.loadInt_takeMem (Spike.Lib.X64.Rt.rS_of_sub _ hE hsub k hk'))
    Spike.Lib.X64Consumer.c0 hEntry fun F' hF' hK' hFF' Q' => ?_
  have hFF : ∀ m, F' m → rtF (Ly) m := fun m h => hFE m (hFF' m h)
  refine Spike.Lib.X64.Rt.startU_segWS (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.call2 hrc.tail hrc.ti hrc.take
    hrc.main hZ hZ8 hps hkm (D := D) hD0 hD8 (L := D + 56) (by omega) (by omega) (by rw [hms]; rfl) hF' hEC.1
    hEC.2.1 hEC.2.2.1 0#64 0#64 Spike.Lib.X64Consumer.c0
    (by decide) (by decide) ?_ ?_ ?_ ?_ hok ?_ ?_ ?_ ?_ ?_ hexit ?_ hfit ?_
    (Spike.Lib.X64.Flow.Ret0.takeMem_of_kstable hK' (Ly).exe (Ly).endPc) (fun m h => hUF m (hFF' m h))
    hUS (hW F' hF' hK' hFF)
  · rw [hms, Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_hhdr hfree hGh).mono hFF
  · rw [hms]; exact (Spike.Lib.X64.Rt.rt_tcbOk hfree hGt hownT).mono hFF
  · rw [hms, Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact fun e he => (Spike.Lib.X64.Rt.rt_hfld hfree hGf e he).mono hFF
  · rw [hms]; exact (Spike.Lib.X64.Rt.rt_takeOk hfree hG1 hG0 hGn hownL hownF hownN).mono hFF
  · rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ (by omega) (by omega)
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
  · rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_houtD _ (by omega) (by omega)
  · rw [hms, Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_limOk hfree hroomM).mono hFF
  · rw [hms, Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_limOk hfree hroomU).mono hFF
  · exact hEC.2.2.2.1
  · exact hEC.2.2.2.2

end StartS

end Spike.Lib.LowerX64
