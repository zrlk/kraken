/-
**The loaded thread's run from `scc_rt_start` is one segment inside the
consumer's facts** (x86-64, P4): for an output passing `placeOK` whose
source is one `Accepted0` `main`, the run from `scc_rt_start`'s entry at the
runtime's layout (`RuntimeLayout.ofPlaceOK`) is a segment inside
`SFacts … Dt`, the take its outside move, never leaving it (to any `Q`).
The taken range is the first stack (`rS0`): the main thread always starts on
it. The twin of `Spike/Lib/LowerA64/StartSeg.lean`.

- `x64_start_segW`: `startU_segW` at `bareMC`, the user function's depth
  `D = fr.size + 48` and the switch region's `swL fr.size`, from
  `scc_rt_start`'s entry in the callee region of `_start`'s call
  (`entryR.callee (-8) (-296) 8`), for every frame condition `F'` stable
  there, kept by the take and implying `rtF`. The obligations are
  `startAllUW_gen`'s (`hgen`, from `swUW_gen_dt` with `userCallW_sw`);
  `main`'s exit is `uPost_exit`; the layout's arithmetic is
  `Spike/Lib/Rt/X64StartArith.lean`'s; the overflow exit call's premises
  are `Spike/Lib/LowerX64/AbortOfPlaceOK.lean`'s.

Where x86-64 differs from AArch64: `_start` is `xor`, `and` and a `call`, so
`scc_rt_start` runs in the call's callee region, not the entry stack's
region. The conclusion is stated as the callee continuation of a generic
`_start` segment (the hand `Spike.Lib.X64.Flow.Ret0.Inst.entry_segW`'s
`hS`), so that the segment from `_start` is that segment applied to this
one. The exit call's site premises are discharged from A6's sites distinct
(`hrel_ofPlaceOK`, `htk_ofPlaceOK`, `hk_ofPlaceOK`, `hKex_ofPlaceOK`).
-/
import Spike.Lib.LowerX64.StartU
import Spike.Lib.LowerX64.AbortOfPlaceOK
import Spike.Lib.Rt.X64StartArith
import Spike.Lib.Rt.X64RtCode
import Spike.Lib.X64Ret0I

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Lower.Inv (lower0 Res)
open Spike.Lib.X64Consumer (CFacts SFacts Lbl Lsize blkPh msOf)
open Spike.Lib.X64.Rt (RuntimeLayout SwUW StartAllUW bareMC rtF entryR)
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

/-- The placement's memory side at the record. -/
local notation "MS" rd:max G:max lbl:max lsize:max =>
  msOf (Ly).Λ (μ (Ly)) rd G (Spike.Lib.X64.PhRec.own (Ly)) lbl lsize

/-- The user function's post at the start. -/
local notation "UP" d:max lbl:max => UPost [d] lbl Spike.Lib.X64Consumer.c0

/-- The callee region of `_start`'s call at the entry state `E`, where
`scc_rt_start` runs. -/
local notation "EC" E:max => (entryR E).callee (-8) (-296) 8

/-- **`scc_rt_start`'s region at an admissible entry state** (`hE`): the
callee region `EC E` of `_start`'s call does not wrap, has room for
`scc_rt_start`'s frames (`lo ≤ -296`, `8 ≤ hi`), and a range `rS` in the
pool is off it, cell by cell and word by word. These are the region
premises of `scc_rt_start`'s segments at `R := EC E`. -/
theorem ec_facts (L : RuntimeLayout) {E : Scc.Sem.Entry} (hE : E.Ok L.Λ) {rS : Scc.Sem.Range}
    (hsub : rS.Sub L.pool) :
    (EC E).OK ∧ (EC E).lo ≤ -296 ∧ 8 ≤ (EC E).hi ∧
      (∀ k, (EC E).Off k → ∀ i < 8, (EC E).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS) ∧
      (∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
        (a : Int) + 8 ≤ (EC E).base.toNat + (EC E).lo ∨ ((EC E).base.toNat : Int) + (EC E).hi ≤ a) := by
  refine ⟨Region.callee_ok (Spike.Lib.X64.Rt.entryR_ok hE) (by show (-65536 : Int) ≤ -8 + -296; decide)
    (by decide) (by show (-8 : Int) < 0; decide) (by show (-8 + 8 : Int) ≤ 0; decide),
    by show (-296 : Int) ≤ -296; decide, by show (8 : Int) ≤ 8; decide, ?_, ?_⟩
  · intro k hk' i hi
    rw [Region.callee_addr]
    exact Spike.Lib.X64.Rt.rS_of_sub _ hE hsub _
      (Region.callee_off (by show (-65536 : Int) ≤ -8 + -296; decide) (by show (-8 + 8 : Int) ≤ 0; decide)
        (by decide) hk') i hi
  · exact Spike.Lib.X64.Flow.Ret0.Inst.out_callee (Spike.Lib.X64.Rt.entryR_ok hE)
      (by show (-65536 : Int) ≤ -8 + -296; decide) (by decide) (by show (-8 : Int) < 0; decide)
      (by show (-8 + 8 : Int) ≤ 0; decide)
      (Spike.Lib.X64.Rt.outS_of_sub _ hE hsub)

/-- **The run from `scc_rt_start` is one segment inside `SFacts … Dt`**
(P4), the take of the first stack its outside move, for an output passing
`placeOK` (`h`, at the immediates `i`) whose source is one `Accepted0`
`main` (`hd`; so a bare tail, `hs`) lowered to `r` (`hr`) at the frame `fr` with its code in the
program (`hpro`, `hbody`): from `scc_rt_start`'s entry in the callee region
of `_start`'s call, for every frame condition `F'` stable there, kept by
the take and implying the runtime's words unloaded (`rtF`), to any `Q`.
This is the callee continuation of `_start`'s segment.

Temporary: `hgen` is `startAllUW_gen`'s conclusion from its last premise,
`hmph`/`hsw` the phase records (`mainPh_ofPlaceOK`, `swPh_ofPlaceOK`).
Open: the lowered function's code
and phases (`hf` … `hbody`, `hphB`, `hphP`, `hab`), the immediates
(`himm`: the layout's are the lowering's, `immsOf d`, which the abort
label's invariant records), the write tail (`hwr`, for a region holding the
stub's frame: `ovfDt_of_at` at `Dt := OvfDt`), the runtime memory invariant at the
runtime's words (`hG*`, `hown*`, `hroom*`) and the labels off the words
(`hfree`). -/
theorem x64_start_segW {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) (hs : o.place.tail = .bare)
    {fr : Scc.Emit.X64.Frame} {r : Res} {entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr)
    (h4 : fr.size ≤ 4096) (h16 : fr.size % 16 = 0)
    (hpro : proInC o.prog fr bareMC.fn entry zl zf z1 z2 zs = true)
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r)
    (hbody : bodyIn o.prog fr entry 0 r.insts r.ret = true)
    {Dt : State → Prop} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lbl : Lbl} {lsize : Lsize}
    (hfree : Spike.Lib.X64.Rt.RtFree (Ly) lbl lsize)
    {E : Scc.Sem.Entry} (hE : E.Ok (Ly).Λ)
    (hphB : bodyPhOk (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      o.prog fr entry r.insts r.ret (Int64.ofBitVec ((Ly).lab bareMC.sp0).toBitVec) = true)
    (hphP : ProPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab bareMC.fn
      (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [])
    (hC0 : CFacts (Ly).Λ lbl Spike.Lib.X64Consumer.c0)
    (hab : r.insts ≠ [] → Scc.Cert.Rt.X64.blockAtB o.prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
        ((Ly).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (himm : i = Spike.Lib.LowerNode.immsOf d)
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
      (∀ m, F' m → rtF (Ly) m) →
      SwUW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly)) m) (MS rd G lbl lsize) (Spike.Lib.X64.Rt.rS0 (Ly))
          (Ret0.pinA (Ly).lab + 0#64 + 8#64) (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) Spike.Lib.X64Consumer.c0
          (swL fr.size) bareMC ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UP d lbl) →
        StartAllUW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (EC E) F'
          (MS rd G lbl lsize) (Spike.Lib.X64.Rt.rS0 (Ly)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swL fr.size) bareMC
          ((fr.size : Int) + 48) (Int64.ofInt fr.size) (UP d lbl)) :
    ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) F' →
      (∀ m, F' m → rtF (Ly) m) → ∀ Q : Frag isa,
      SegW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (MS rd G lbl lsize)
        (At (Ly).exe (Ly).endPc (EC E) F' (startN0 (Ly).lab Spike.Lib.X64Consumer.c0)) Q := by
  intro F' hF' hK' hFF Q
  have hrc := Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.X64.Rt.rS0 (Ly))
  obtain ⟨hL, hL8, hL0, hL1, hD8⟩ := swL_ok h4 h16
  obtain ⟨hZ, hZ8, hps, hkm⟩ := Spike.Lib.X64.Rt.bareMC_ok
  have hZ32 : bareMC.Z.toInt = 32 := by decide
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swL fr.size) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hL1
  have h8 : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false
      ⟨limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hU := userCallW_sw (ra := ((Ly).lab bareMC.sp0).toBitVec) (tcb := Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (ms := MS rd G lbl lsize) (Dt := Dt) (Z := bareMC.Z) (L := swL fr.size) (D := (fr.size : Int) + 48)
    hd hf (by omega) hpro hr hbody hI (Int.le_refl _) hD8 h8 hok hL hL8 hZ8 hZ hphB hphP hC0 hmr hsub hfit hab
    (hprog_ofPlaceOK h i) (hsysIn_ofPlaceOK h i) (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h i) himm
    (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl
    hwr
  have hs3 := swUW_gen_dt (F := F') (R := EC E) hI hrc.tail hrc.main hC0
    (fun c v (hp : UPost [d] lbl Spike.Lib.X64Consumer.c0 c v) => hp.1 ▸ hC0) hmph hsw h8 hok (by omega) hL8 hZ
    hZ8 hps hkm hmr hsub hfit hU
  have hEC := ec_facts _ hE hsub
  refine Spike.Lib.X64.Rt.startU_segW (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.call2 hrc.tail hrc.ti hrc.take
    hrc.main hZ hZ8 hps hkm (D := (fr.size : Int) + 48) (by omega) hD8 (L := swL fr.size) hL hL8 rfl hF' hEC.1
    hEC.2.1 hEC.2.2.1 0#64 0#64 Spike.Lib.X64Consumer.c0
    (by decide) (by decide) ?_ ?_ ?_ ?_ hok ?_ ?_ ?_ ?_ ?_ (uPost_exit rfl) ?_ hfit ?_
    (Spike.Lib.X64.Flow.Ret0.takeMem_of_kstable hK' (Ly).exe (Ly).endPc) (hgen F' hF' hK' hFF hs3)
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_hhdr hfree hGh).mono hFF
  · exact (Spike.Lib.X64.Rt.rt_tcbOk hfree hGt hownT).mono hFF
  · rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact fun e he => (Spike.Lib.X64.Rt.rt_hfld hfree hGf e he).mono hFF
  · exact (Spike.Lib.X64.Rt.rt_takeOk hfree hG1 hG0 hGn hownL hownF hownN).mono hFF
  · rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rS0_subRD _ hL0 hL1
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _
  · rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_houtD _ hL0 hL1
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_limOk hfree hroomM).mono hFF
  · rw [Spike.Lib.X64.Rt.pinA_lab0]; exact (Spike.Lib.X64.Rt.rt_limOk hfree hroomU).mono hFF
  · exact hEC.2.2.2.1
  · exact hEC.2.2.2.2

end Start

end Spike.Lib.LowerX64
