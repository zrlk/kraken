/-
**The start segment with the frame `WordsNone ∧ rtF`** for a main-only
call-free `Accepted1` source (AArch64): `a64_start_segW1`
(`Spike/Lib/LowerA64/StartSeg1.lean`) with `Spike.Lib.DmemPriv.WordsNone`
carried in the frame of every segment, before the stack switch and after it.

- `a64_start_segW1_wn`: the same premises, `hEntry` at the frame
  `WordsNone ∧ rtF` and `hgen` at `SwUWF`/`StartAllUWF`
  (`Spike/Lib/Rt/A64SegsF.lean`) with the extra frame `Fw := WordsNone`.
  Before the switch the frame is `FStable` in `entryR E`
  (`Alloc.wordsNone_and_fstable`, `cellsR_entry`), survives the take
  (`Rt.wordsNone_takeMem`), and the runtime's store/limit premises weaken to
  it (`StOk.mono` & co.); after it `WordsNone ∧ swFSL` is `FStable` in the new
  region (`Rt.wordsNone_swFSL_fstable`), and the user function's interface is
  `userCallW1_swF`'s (`startUF_segW`, `swUWF_gen_dt`).
-/
import Spike.Lib.LowerA64.StartSeg1
import Spike.Lib.LowerA64.StartUF
import Spike.Lib.Rt.A64RtStartUF
import Spike.Lib.Rt.A64SwWordsNone
import Spike.Lib.RegionCells

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (CFacts SFacts Lbl Lsize msOf)
open Spike.Lib.A64.Rt (RuntimeLayout UserCallW SwUW StartAllUW SwUWF StartAllUWF swFSL bareMC rtF entryR)
open Spike.Lib.A64.Flow.Ret0 (StackM limA)
open Spike.Lib.A64.PhRec (μ K)

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **The facts every state of the start's run carries**: `SFacts` at the
record, the first stack `rS0` taken, the write tail `Dt`. -/
local notation "WS" lbl:max Dt:max => fun s c => SFacts (Ly).Λ (μ (Ly)) (Spike.Lib.A64.PhRec.own (Ly))
  (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) lbl s c Dt

/-- The frame before the switch: `WordsNone` and the runtime's words. -/
local notation "FWN" => fun m : MachineData => Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧ rtF (Ly) m

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max => msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.A64.PhRec.own (Ly)) lbl lsize

/-- The user function's post at the start. -/
local notation "UP" d:max lbl:max => UPost [d] lbl Spike.Lib.A64Consumer.c0

/-- **`a64_start_segW1` with the frame `WordsNone ∧ rtF`** before the
switch: the loaded thread's run is one segment inside `SFacts … Dt`, for a
main-only call-free `Accepted1` source: `main`
lowered by `lower1` to `r` (`hr`), its blocks' code at `Cd1` (`hcode`,
`hbl`) in place of `bodyIn` and its phase check, the abort block's premises
when a block has a checked `+` (`hab`), the immediates `imms1Of [d]`. -/
theorem a64_start_segW1_wn {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) (hs : o.place.tail = .bare)
    {cx : FnCtx} {r : Scc.Lower.Inv.Res1}
    {entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC o.prog cx bareMC.fn entry = true)
    (hr : Scc.Lower.Inv.lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    (hcode : Code1 cx (Cd1 o.prog (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab cx
      (Int64.ofBitVec ((Ly).lab bareMC.e0 + 4).toBitVec)) ((Ly).lab entry) r.insts r.term)
    (hbl : BlocksCode cx (Cd1 o.prog (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab cx
      (Int64.ofBitVec ((Ly).lab bareMC.e0 + 4).toBitVec)) (Ly).lab r.blocks)
    {Dt : State → Prop} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl} {lsize : Lsize}
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    (hphP : ProPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab
      (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts (Ly).Λ lbl Spike.Lib.A64Consumer.c0)
    (hab : ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true →
      Scc.Cert.Rt.A64.blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly))
        (fun _ => false) (Ly).lab ((Ly).lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (himm : i = Scc.Lower.imms1Of [d])
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At (Ly).exe (Ly).endPc R' F' (A64.Abort.N (Ly).lab A64.Abort.overflow c .svc) s c' → Dt s)
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
      (v.setWidth 64).toNat ≤
        (Ret0.stacksA (Ly).lab + 0#64 + 16384#64 - bareMC.Z.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat)
    (hmph : Spike.Lib.A64.Rt.MainU.MainPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab
      bareMC)
    (hsw : Spike.Lib.A64.Rt.MainU.SwPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab)
    (hEntry : BlkW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) (Ly).exe (Ly).endPc (entryR E) FWN
      (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0) Ret0.entryB)
    (hgen : SwUWF (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (entryR E)
        (fun m => FWN m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly)) m) (Spike.Lib.DmemPriv.WordsNone (Ly).Λ)
        (MS rd G lbl lsize) (Spike.Lib.A64.Rt.rS0 (Ly))
        (Ret0.pinA (Ly).lab + 0#64 + 8#64) (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) Spike.Lib.A64Consumer.c0
        (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame) (UP d lbl) →
      StartAllUWF (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (entryR E) FWN
        (Spike.Lib.DmemPriv.WordsNone (Ly).Λ) (MS rd G lbl lsize) (Spike.Lib.A64.Rt.rS0 (Ly)) 0#64 0#64
        Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame) (UP d lbl))
    {Q : Frag isaLSE2} :
    SegW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) [d] lbl (MS rd G lbl lsize)
      (At (Ly).exe (Ly).endPc (entryR E) FWN (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0)) Q := by
  have hwf : (Ly).Λ.WF := wf_link_of_placeOKAt (i := i) h
  have hFS := (Spike.Lib.A64.Alloc.wordsNone_and_fstable hwf hE.1 (Spike.Lib.A64.Rt.entryR_ok hE)
    (.inl (cellsR_entry hE)) (Spike.Lib.A64.Rt.rtF_stable _ hE)).1
  have hrc := Spike.Lib.A64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub (Ly) hsub
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.A64.Rt.rS0 (Ly))
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(cx.frame + 96)) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by omega) (by omega)
  have h16' : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 16 = 0 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false
      ⟨limA (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hsubS : ∀ k, (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(cx.frame + 96)) 0).Off k →
      ((swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(cx.frame + 96)) 0).addr k).toNat % 8 = 0 ∧
      (Spike.Lib.A64.Rt.rS0 (Ly)).contains
        ((swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(cx.frame + 96)) 0).addr k).toNat ∧
      (Spike.Lib.A64.Rt.rS0 (Ly)).contains
        (((swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-(cx.frame + 96)) 0).addr k).toNat + 7) := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by omega) (by omega)
  have hfitL : (limA (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
    rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _
  have houtL : ((limA (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat + -(cx.frame + 96) ∨
      ((Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (Ret0.pinA (Ly).lab + 0#64 + 8#64))).toNat := by
    rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    exact Spike.Lib.A64.Rt.rt_houtD _ (by omega) (by omega)
  have hFwS := fun v => Spike.Lib.A64.Rt.wordsNone_swFSL_fstable (v := v) hwf hsub hok (by omega) (by omega)
    hsubS hfitL houtL hfit
  have hZ48 : bareMC.Z.toInt = 48 := by decide
  have hU := userCallW1_swF (fn := bareMC.fn) (ra := ((Ly).lab bareMC.e0 + 4).toBitVec)
    (tcb := Ret0.pinA (Ly).lab + 0#64 + 8#64) (ms := MS rd G lbl lsize) (Dt := Dt) (Z := bareMC.Z)
    (L := cx.frame + 96) (D := cx.frame + 48) (Fw := Spike.Lib.DmemPriv.WordsNone (Ly).Λ)
    hd hf h1 h16 hpro hr hI (by omega) (by omega) h16' hok (by omega)
    (by omega) (by omega) (by omega) hcode hbl hphP hC0 hmr hsub hfit hab (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h i) himm (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i)
    (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl hwr
  have hs3 := swUWF_gen_dt (F := FWN) (R := entryR E) hI hrc.tail hrc.main hC0
    (fun c v (hp : UPost [d] lbl Spike.Lib.A64Consumer.c0 c v) => hp.1 ▸ hC0) hmph hsw
    h16' hok (by omega) (by omega) (by omega) (by omega) (by decide) hmr hsub hfit hU
  refine (Spike.Lib.A64.Rt.entry_segW' (Ly).lays rfl hrc.entry hFS
    (Spike.Lib.A64.Rt.entryR_ok hE)
    (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 0; decide)
    Spike.Lib.A64Consumer.c0 hEntry).seq ?_
  refine Spike.Lib.A64.Rt.startUF_segW (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.tail hrc.ti hrc.tiSp hrc.take
    hrc.main (by omega) (by omega) (by decide) (D := cx.frame + 48) (by omega) (by omega) (L := cx.frame + 96)
    (by omega) rfl hFS (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE)
    (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide) 0#64 0#64 Spike.Lib.A64Consumer.c0
        (by decide) ?_ ?_ (by decide) ?_ ?_ h16' hok hsubS (fun _ h => h.1) hFwS
    ?_ ?_ (uPost_exit rfl) (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) hfit (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub)
    (fun _ _ hm => ⟨Spike.Lib.A64.Rt.wordsNone_takeMem hwf hsub hm.1,
      Spike.Lib.A64.Rt.rtF_takeMem _ hsub hm.2⟩) (hgen hs3)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact (Spike.Lib.A64.Rt.rt_hhdr hfree hGh).mono fun _ h => h.2
  · exact (Spike.Lib.A64.Rt.rt_tcbOk hfree hGt hownT).mono fun _ h => h.2
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact fun e he =>
      (Spike.Lib.A64.Rt.rt_hfld hfree hGf e he).mono fun _ h => h.2
  · exact (Spike.Lib.A64.Rt.rt_takeOk hfree hG1 hG0 hGn hownL hownF hownN).mono fun _ h => h.2
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact (Spike.Lib.A64.Rt.rt_limOk hfree hroomM).mono fun _ h => h.2
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact (Spike.Lib.A64.Rt.rt_limOk hfree hroomU).mono fun _ h => h.2

end Start

end Spike.Lib.LowerA64
