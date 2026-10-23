/-
**The loaded thread's run is one segment inside the consumer's facts**
(AArch64, P4): for an output passing `placeOK` whose source is one
`Accepted0` `main`, the run from `_start` at the runtime's layout
(`RuntimeLayout.ofPlaceOK`) is a segment inside `SFacts … Dt`, the take its
outside move, never leaving it (to any `Q`).
The taken range is the first stack (`rS0`): the main thread always starts on
it, so this fixes an intermediate statement, not `lower_correct`'s claim.

- `a64_start_segW`: `entry_segW'` then `startU_segW` at `bareMC`, the user
  function's depth `D = frame + 48` and the switch region's `frame + 96`
  (at most `4176 ≤ 16384`, `accepted0_frame_le`). The obligations are
  `startAllUW_gen`'s (`hgen`, from `swUW_gen_dt` with `userCallW_sw`) and
  `_start`'s block (`hEntry`); `main`'s exit is `uPost_exit`; the layout's
  arithmetic is `Spike/Lib/Rt/A64StartArith.lean`'s; the overflow exit
  call's site premises are `Spike/Lib/LowerA64/AbortOfPlaceOK.lean`'s.
-/
import Spike.Lib.LowerA64.StartU
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Lib.Rt.A64StartArith
import Spike.Lib.Rt.A64RtCode

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64Consumer (CFacts SFacts Lbl Lsize msOf)
open Spike.Lib.A64.Rt (RuntimeLayout UserCallW SwUW StartAllUW swFSL bareMC rtF entryR)
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

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max => msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.A64.PhRec.own (Ly)) lbl lsize

/-- The user function's post at the start. -/
local notation "UP" d:max lbl:max => UPost [d] lbl Spike.Lib.A64Consumer.c0

/-- **The loaded thread's run is one segment inside `SFacts … Dt`** (P4),
the take of the first stack its outside move, for an output passing
`placeOK` (`h`, at the immediates `i`) whose source is one `Accepted0`
`main` (`hd`) lowered to `r` (`hr`) at the context `cx` with its code in
the program (`hpro`, `hbody`): from `_start`'s entry on the entry stack
(`entryR`, the runtime's words unloaded, `rtF`), to any `Q`.

Temporary: `hgen` is `startAllUW_gen`'s conclusion from its last premise
(`Spike/Lib/Rt/A64RtStartU.lean`, in progress; its other premises are
discharged at the plug-in by `entryR_ok`, `entryR_al`, `rS0_sub` and
`stackM_stable`), `hEntry` `_start`'s block (`entryW_gen`), `hmph`/`hsw` the phase records
(`mainPh_ofPlaceOK`, `swPh_ofPlaceOK`). Open: the lowered
function's code and phases (`hf` … `hbody`, `hphB`, `hphP`, `hab`:
A9 at the IR link, P5), the immediates (`himm`: the layout's are the
lowering's, `immsOf d`, which the abort label's invariant records), the
write tail (`hwr`, for a 16-aligned region holding the stub's frame:
`ovfDt_of_at` at `Dt := OvfDt`), the runtime memory invariant at the runtime's words (`hG*`,
`hown*`, `hroom*`) and the labels off the words (`hfree`). -/
theorem a64_start_segW {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {cx : FnCtx} {r : Scc.Lower.Inv.Res}
    {entry : Label} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hpro : proInC o.prog cx bareMC.fn entry = true)
    (hr : Scc.Lower.Inv.lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn o.prog cx entry 0 r.insts r.ret = true)
    {Dt : State → Prop} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl} {lsize : Lsize}
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    (hphB : bodyPhOk (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab cx
      entry r.insts r.ret (Int64.ofBitVec ((Ly).lab bareMC.e0 + 4).toBitVec) = true)
    (hphP : ProPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab
      (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [])
    (hC0 : CFacts (Ly).Λ lbl Spike.Lib.A64Consumer.c0)
    (hab : r.insts ≠ [] → Scc.Cert.Rt.A64.blockAt o.prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly))
        (fun _ => false) (Ly).lab ((Ly).lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (himm : i = Spike.Lib.LowerNode.immsOf d)
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
    (hEntry : BlkW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) (Ly).exe (Ly).endPc (entryR E) (rtF (Ly))
      (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0) Ret0.entryB)
    (hgen : SwUW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (entryR E)
        (fun m => rtF (Ly) m ∧ StackM (Spike.Lib.A64.Rt.rS0 (Ly)) m) (MS rd G lbl lsize) (Spike.Lib.A64.Rt.rS0 (Ly))
        (Ret0.pinA (Ly).lab + 0#64 + 8#64) (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) Spike.Lib.A64Consumer.c0
        (cx.frame + 96) bareMC (cx.frame + 48) (Int64.ofInt cx.frame) (UP d lbl) →
      StartAllUW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (entryR E) (rtF (Ly))
        (MS rd G lbl lsize) (Spike.Lib.A64.Rt.rS0 (Ly)) 0#64 0#64 Spike.Lib.A64Consumer.c0 (cx.frame + 96) bareMC
        (cx.frame + 48) (Int64.ofInt cx.frame) (UP d lbl))
    {Q : Frag isaLSE2} :
    SegW (WS lbl Dt) (K (Ly) (Spike.Lib.A64.Rt.rS0 (Ly))) [d] lbl (MS rd G lbl lsize)
      (At (Ly).exe (Ly).endPc (entryR E) (rtF (Ly)) (Ret0.entryN (Ly).lab Spike.Lib.A64Consumer.c0)) Q := by
  have hrc := Spike.Lib.A64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h)
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
  have hZ48 : bareMC.Z.toInt = 48 := by decide
  have hU := userCallW_sw (fn := bareMC.fn) (ra := ((Ly).lab bareMC.e0 + 4).toBitVec)
    (tcb := Ret0.pinA (Ly).lab + 0#64 + 8#64) (ms := MS rd G lbl lsize) (Dt := Dt) (Z := bareMC.Z)
    (L := cx.frame + 96) (D := cx.frame + 48)
    hd hf h1 h16 hpro hr hbody hI (by omega) (by omega) h16' hok (by omega)
    (by omega) (by omega) (by omega) hphB hphP hC0 hmr hsub hfit hab (hprog_ofPlaceOK h i)
    (Spike.Lib.A64.PhRec.abortPhOk_ofPlaceOK h i) himm (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i)
    (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl hwr
  have hs3 := swUW_gen_dt (F := rtF (Ly)) (R := entryR E) hI hrc.tail hrc.main hC0
    (fun c v (hp : UPost [d] lbl Spike.Lib.A64Consumer.c0 c v) => hp.1 ▸ hC0) hmph hsw
    h16' hok (by omega) (by omega) (by omega) (by omega) (by decide) hmr hsub hfit hU
  refine (Spike.Lib.A64.Rt.entry_segW' (Ly).lays rfl hrc.entry (Spike.Lib.A64.Rt.rtF_stable _ hE)
    (Spike.Lib.A64.Rt.entryR_ok hE)
    (Spike.Lib.A64.Rt.entryR_al hE) (by show (-65536 : Int) ≤ 0; decide) (by show (0 : Int) ≤ 0; decide)
    Spike.Lib.A64Consumer.c0 hEntry).seq ?_
  refine Spike.Lib.A64.Rt.startU_segW (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.tail hrc.ti hrc.tiSp hrc.take
    hrc.main (by omega) (by omega) (by decide) (D := cx.frame + 48) (by omega) (by omega) (L := cx.frame + 96)
    (by omega) rfl (Spike.Lib.A64.Rt.rtF_stable _ hE) (Spike.Lib.A64.Rt.entryR_ok hE) (Spike.Lib.A64.Rt.entryR_al hE)
    (by show (-65536 : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide) 0#64 0#64 Spike.Lib.A64Consumer.c0
        (by decide) ?_ ?_ (by decide) ?_ ?_ h16' hok ?_ ?_ ?_
    ?_ ?_ (uPost_exit rfl) (Spike.Lib.A64.Rt.rS_of_sub _ hE hsub) hfit (Spike.Lib.A64.Rt.outS_of_sub _ hE hsub)
    (fun _ _ hm => Spike.Lib.A64.Rt.rtF_takeMem _ hsub hm) (hgen hs3)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hhdr hfree hGh
  · exact Spike.Lib.A64.Rt.rt_tcbOk hfree hGt hownT
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hfld hfree hGf
  · exact Spike.Lib.A64.Rt.rt_takeOk hfree hG1 hG0 hGn hownL hownF hownN
  · rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by omega) (by omega)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
    exact Spike.Lib.A64.Rt.rt_houtD _ (by omega) (by omega)
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_limOk hfree hroomM
  · rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_limOk hfree hroomU

end Start

end Spike.Lib.LowerA64
