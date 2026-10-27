/-
**The start segment with the extra frame `WordsNone` after the switch**
for a main-only call-free `Accepted1` source (x86-64): `x64_start_segW1`
(`Spike/Lib/LowerX64/StartSeg1.lean`) with `Spike.Lib.DmemPriv.WordsNone`
in the frame of every segment, before the stack switch and after it; the
twin of `Spike/Lib/LowerA64/StartSeg1WN.lean`.

- `x64_start_segW1_wn`: the same premises, `hgen` at `SwUWF`/`StartAllUWF`
  (`Spike/Lib/Rt/X64SegsF.lean`) with the extra frame `Fw := WordsNone`,
  for every frame `F'` in `_start`'s callee region giving `WordsNone ∧ rtF`.
  Before the switch the runtime's store/limit premises weaken to `F'`
  (`StOk.mono` & co.); after it `WordsNone ∧ swFSL` is `FStable` in the new
  region (`Rt.wordsNone_swFSL_fstable`), and the user function's interface
  is `userCallW1_sw`'s at the weaker frame (`startUF_segW`, `swUWF_gen_dt`).
-/
import Spike.Lib.LowerX64.StartSeg1
import Spike.Lib.LowerX64.StartUF
import Spike.Lib.Rt.X64SwWordsNone

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize blkPh msOf)
open Spike.Lib.X64.Rt (RuntimeLayout SwUW StartAllUW SwUWF StartAllUWF swFSL bareMC rtF entryR)
open Spike.Lib.X64.Flow.Ret0 (StackM limA tpOf startN0)
open Spike.Lib.X64.PhRec (μ K)

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **The facts every state of the start's run carries**: `SFacts` at the
record, the first stack `rS0` taken, the write tail `Dt`. -/
local notation "WS" lbl:max Dt:max => fun s c => SFacts (Ly).Λ (μ (Ly)) (Spike.Lib.X64.PhRec.own (Ly))
  (Spike.Lib.X64.Rt.rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) lbl s c Dt

/-- The frame before the switch: `WordsNone` and the runtime's words. -/
local notation "FWN" => fun m : MachineData => Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧ rtF (Ly) m

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max =>
  msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.X64.PhRec.own (Ly)) lbl lsize

/-- The user function's post at the start. -/
local notation "UP" d:max lbl:max => UPost [d] lbl Spike.Lib.X64Consumer.c0

/-- The callee region of `_start`'s call at the entry state `E`, where
`scc_rt_start` runs. -/
local notation "EC" E:max => (entryR E).callee (-8) (-296) 8

/-- **`x64_start_segW1` with `WordsNone` in every segment's frame**: the
run from `scc_rt_start` is one segment inside `SFacts … Dt` at every frame
`F'` giving `WordsNone ∧ rtF`, the switch's obligations at `SwUWF` with
`Fw := WordsNone`. -/
theorem x64_start_segW1_wn {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) (hs : o.place.tail = .bare)
    {fr : Scc.Emit.X64.Frame} {r : Scc.Lower.Inv.Res1} {entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr)
    (h4 : fr.size ≤ 4096) (h16 : fr.size % 16 = 0)
    (hpro : proInC o.prog fr bareMC.fn entry zl zf z1 z2 zs = true)
    (hr : Scc.Lower.Inv.lower1 [(d.arg, .unit, [])] 0 d.body = some r)
    (hcode : Code1 fr (Cd1 o.prog (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab fr
      (Int64.ofBitVec ((Ly).lab bareMC.sp0).toBitVec)) ((Ly).lab entry) r.insts r.term)
    (hbl : BlocksCode fr (Cd1 o.prog (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab fr
      (Int64.ofBitVec ((Ly).lab bareMC.sp0).toBitVec)) (Ly).lab r.blocks)
    {Dt : State → Prop} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl} {lsize : Lsize}
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    (hphP : ProPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab bareMC.fn
      (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts (Ly).Λ lbl Spike.Lib.X64Consumer.c0)
    (hab : ((⟨"entry", r.insts, r.term⟩ :: r.blocks : List Scc.IR.Block).any fun b =>
        b.insts.any fun | .addChk .. => true | _ => false) = true →
      Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
        ((Ly).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (himm : i = Scc.Lower.imms1Of [d])
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At (Ly).exe (Ly).endPc R' F' (Abort.N (Ly).lab Abort.overflow c .sys) s c' → Dt s)
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
        8#64 - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat)
    (hmph : Spike.Lib.X64.Rt.MainU.MainPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab
      bareMC)
    (hsw : Spike.Lib.X64.Rt.MainU.SwPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab)
    (hgen : ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) F' →
      (∀ m, F' m → FWN m) →
      SwUWF (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly)) m) (Spike.Lib.DmemPriv.WordsNone (Ly).Λ)
          (MS rd G lbl lsize) (Spike.Lib.X64.Rt.rS0 (Ly))
          (Ret0.pinA (Ly).lab + 0#64 + 8#64) (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) Spike.Lib.X64Consumer.c0
          (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UP d lbl) →
        StartAllUWF (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (EC E) F'
          (Spike.Lib.DmemPriv.WordsNone (Ly).Λ) (MS rd G lbl lsize) (Spike.Lib.X64.Rt.rS0 (Ly)) 0#64 0#64
          Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UP d lbl)) :
    ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) F' →
      (∀ m, F' m → FWN m) → ∀ Q : Frag isa,
      SegW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (MS rd G lbl lsize)
        (At (Ly).exe (Ly).endPc (EC E) F' (startN0 (Ly).lab Spike.Lib.X64Consumer.c0)) Q := by
  intro F' hF' hK' hFF Q
  have hrc := Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.X64.Rt.rS0 (Ly))
  obtain ⟨hL, hL8, hL0, hL1, hD8⟩ := swL_ok h4 h16
  obtain ⟨hZ, hZ8, hps, hkm⟩ := Spike.Lib.X64.Rt.bareMC_ok
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swL fr.size) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hL1
  have h8 : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false
      ⟨limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hwf : (Ly).Λ.WF := wf_link_of_placeOKAt (i := i) h
  have hU0 := userCallW1_sw (ra := ((Ly).lab bareMC.sp0).toBitVec) (tcb := Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (ms := MS rd G lbl lsize) (Dt := Dt) (Z := bareMC.Z) (L := swL fr.size) (D := (fr.size : Int) + 48)
    hd hf (by omega) hpro hr hI (Int.le_refl _) hD8 h8 hok hL hL8 hZ8 hZ hcode hbl hphP hC0 hmr hsub hfit hab
    (hprog_ofPlaceOK h i) (hsysIn_ofPlaceOK h i) (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h i) himm
    (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl
    hwr
  have hU : ∀ v (F'' : MachineData → Prop), (∀ m, F'' m → (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
      swFSL (swL fr.size) (Spike.Lib.X64.Rt.rS0 (Ly)) (Ret0.stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
      Ret0.CallerCells (swR v (-swL fr.size) 0) (-8 - 0) (8 - swL fr.size) 8 m) → _ :=
    fun v F'' hF'' => hU0 v F'' fun m hm => ⟨(hF'' m hm).1.2, (hF'' m hm).2⟩
  have hsubS : ∀ k, (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swL fr.size) 0).Off k →
      ((swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swL fr.size) 0).addr k).toNat % 8 = 0 ∧
      (Spike.Lib.X64.Rt.rS0 (Ly)).contains
        ((swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swL fr.size) 0).addr k).toNat ∧
      (Spike.Lib.X64.Rt.rS0 (Ly)).contains
        (((swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swL fr.size) 0).addr k).toNat + 7) := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hL1
  have hfitL : (limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64 := by
    rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
  have houtL : ((limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat + -swL fr.size ∨
      ((Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64))).toNat := by
    rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hL1
  have hFwS := fun v => Spike.Lib.X64.Rt.wordsNone_swFSL_fstable (v := v) hwf hsub hok (by omega) hL8
    hsubS hfitL houtL hfit
  have hs3 := swUWF_gen_dt (F := F') (R := EC E) hI hrc.tail hrc.main hC0
    (fun c v (hp : UPost [d] lbl Spike.Lib.X64Consumer.c0 c v) => hp.1 ▸ hC0) hmph hsw h8 hok (by omega) hL8 hZ
    hZ8 hps hkm hmr hsub hfit hU
  have hEC := ec_facts _ hE hsub
  refine Spike.Lib.X64.Rt.startUF_segW (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.call2 hrc.tail hrc.ti hrc.take
    hrc.main hZ hZ8 hps hkm (D := (fr.size : Int) + 48) (by omega) hD8 (L := swL fr.size) hL hL8 rfl hF' hEC.1
    hEC.2.1 hEC.2.2.1 0#64 0#64 Spike.Lib.X64Consumer.c0
    (by decide) (by decide) ?_ ?_ ?_ ?_ hok hsubS (fun m hm => (hFF m hm).1) hFwS ?_ ?_ (uPost_exit rfl) ?_
    hfit ?_
    (Spike.Lib.X64.Flow.Ret0.takeMem_of_kstable hK' (Ly).exe (Ly).endPc) (hgen F' hF' hK' hFF hs3)
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_hhdr hfree hGh).mono fun m hm => (hFF m hm).2
  · exact (Spike.Lib.X64.Rt.rt_tcbOk hfree hGt hownT).mono fun m hm => (hFF m hm).2
  · rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact fun e he => (Spike.Lib.X64.Rt.rt_hfld hfree hGf e he).mono fun m hm => (hFF m hm).2
  · exact (Spike.Lib.X64.Rt.rt_takeOk hfree hG1 hG0 hGn hownL hownF hownN).mono fun m hm => (hFF m hm).2
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_limOk hfree hroomM).mono fun m hm => (hFF m hm).2
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_limOk hfree hroomU).mono fun m hm => (hFF m hm).2
  · exact hEC.2.2.2.1
  · exact hEC.2.2.2.2

end Start

end Spike.Lib.LowerX64
