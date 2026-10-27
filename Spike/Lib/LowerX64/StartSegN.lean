/-
**The loaded thread's run from `scc_rt_start` with the user function's
depth a parameter** (x86-64): `x64_start_segW1`
(`Spike/Lib/LowerX64/StartSeg1.lean`) with the switch region sized by the
user function's depth `D` (`swLD D = D + 56`) instead of by its frame
(`swL fr.size = fr.size + 104`, the depth `fr.size + 48`), so that a `main`
with calls can be given the depth its stack need asks for.

- `swLD`, `swLD_ok`, `swLD_frame`: the switch region's depth for a user
  depth `D`; at `D = fr.size + 48` it is `swL fr.size`.
- `x64_start_segW1D`: `x64_start_segW1` at any 8-aligned `D` with
  `fr.size + 48 ≤ D` and `D + 56 ≤ 16384`.
- `x64_start_segW1_ofD`: `x64_start_segW1`'s statement again, from
  `x64_start_segW1D` at `D = fr.size + 48` (the frame's case, `fr.size ≤
  4096`).
- `needD`, `MainNeedOk`, `needD_ok`: the user depth from `main`'s row of the
  stack need table (`needD fr n`, at least the frame's `fr.size + 48` and
  the need plus `40`, 8-aligned), and the decidable premise that its
  switch region fits the first stack.
-/
import Spike.Lib.LowerX64.StartSeg1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
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

/-- **The switch region's depth for a user depth `D`**: `scc_rt_main`'s
frame (`32`), its return address and saved `%rbp` and the user's return
address (`24`), and the user's depth `D` (`swL n` at `D = n + 48`). -/
def swLD (D : Int) : Int := D + 56

/-- At the frame's depth `n + 48`, `swLD` is `swL n`. -/
theorem swLD_frame (n : Nat) : swLD ((n : Int) + 48) = swL n := by
  unfold swLD swL; omega

/-- **`swLD` fits `startU_segW` and the first stack** for every 8-aligned
user depth `D` of at least a frame's `n + 48` whose switch region fits the
`16384` bytes of a stack (`swL_ok`'s conclusion at `D`). -/
theorem swLD_ok {n : Nat} {D : Int} (hD : (n : Int) + 48 ≤ D) (hD8 : D % 8 = 0) (hcap : D + 56 ≤ 16384) :
    8 + 8 + Spike.Lib.X64.Rt.bareMC.Z.toInt + 8 + D ≤ swLD D ∧ swLD D % 8 = 0 ∧
      0 ≤ swLD D ∧ swLD D ≤ 16384 ∧ D % 8 = 0 := by
  have hZ : Spike.Lib.X64.Rt.bareMC.Z.toInt = 32 := by decide
  unfold swLD
  omega

/-- **The run from `scc_rt_start` is one segment inside `SFacts … Dt`**,
the user function's depth `D` a parameter (`x64_start_segW1` at any `D`
from `fr.size + 48` to `16384 - 56`, 8-aligned; the switch region `swLD D`)
for a main-only call-free `Accepted1` source: `main`
lowered by `lower1` to `r` (`hr`), its blocks' code at `Cd1` (`hcode`,
`hbl`) in place of `bodyIn` and its phase check, the abort block's premises
when a block has a checked `+` (`hab`), the immediates `imms1Of [d]`. -/
theorem x64_start_segW1D {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) (hs : o.place.tail = .bare)
    {fr : Scc.Emit.X64.Frame} {r : Scc.Lower.Inv.Res1} {entry : Label} {zl zf z1 z2 zs : Nat} (hf : FrameOk fr)
    {D : Int} (hD : (fr.size : Int) + 48 ≤ D) (hD8 : D % 8 = 0) (hcap : D + 56 ≤ 16384)
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
      (∀ m, F' m → rtF (Ly) m) →
      SwUW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (EC E)
          (fun m => F' m ∧ StackM (Spike.Lib.X64.Rt.rS0 (Ly)) m) (MS rd G lbl lsize) (Spike.Lib.X64.Rt.rS0 (Ly))
          (Ret0.pinA (Ly).lab + 0#64 + 8#64) (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) Spike.Lib.X64Consumer.c0
          (swLD D) bareMC D (Int64.ofInt fr.size) (UP d lbl) →
        StartAllUW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (Ly).exe (Ly).endPc (EC E) F'
          (MS rd G lbl lsize) (Spike.Lib.X64.Rt.rS0 (Ly)) 0#64 0#64 Spike.Lib.X64Consumer.c0 (swLD D) bareMC
          D (Int64.ofInt fr.size) (UP d lbl)) :
    ∀ F' : MachineData → Prop, FStable (EC E) F' → KStable (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) F' →
      (∀ m, F' m → rtF (Ly) m) → ∀ Q : Frag isa,
      SegW (WS lbl Dt) (K (Ly) (Spike.Lib.X64.Rt.rS0 (Ly))) [d] lbl (MS rd G lbl lsize)
        (At (Ly).exe (Ly).endPc (EC E) F' (startN0 (Ly).lab Spike.Lib.X64Consumer.c0)) Q := by
  intro F' hF' hK' hFF Q
  have hrc := Spike.Lib.X64.Rt.rtCodeIn_of_ok (rtCodeOk_bare_of_placeOKAt h hs)
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub (Ly) hsub
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := Spike.Lib.X64.Rt.rS0 (Ly))
  obtain ⟨hL, hL8, hL0, hL1, -⟩ := swLD_ok hD hD8 hcap
  obtain ⟨hZ, hZ8, hps, hkm⟩ := Spike.Lib.X64.Rt.bareMC_ok
  have hok : (swR (Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-swLD D) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ hL0 hL1
  have h8 : (Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (Ly).Λ) false
      ⟨limA (tpOf (Ret0.pinA (Ly).lab + 0#64 + 8#64)), 8⟩ = true := by
    rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  have hU := userCallW1_sw (ra := ((Ly).lab bareMC.sp0).toBitVec) (tcb := Ret0.pinA (Ly).lab + 0#64 + 8#64)
    (ms := MS rd G lbl lsize) (Dt := Dt) (Z := bareMC.Z) (L := swLD D) (D := D)
    hd hf (by omega) hpro hr hI hD hD8 h8 hok hL hL8 hZ8 hZ hcode hbl hphP hC0 hmr hsub hfit hab
    (hprog_ofPlaceOK h i) (hsysIn_ofPlaceOK h i) (Spike.Lib.X64.PhRec.abortPhOk_ofPlaceOK h i) himm
    (hrel_ofPlaceOK h i) (htk_ofPlaceOK h i) (hk_ofPlaceOK h i) (hKex_ofPlaceOK h i) (hms_ofPlaceOK h i) rfl
    hwr
  have hs3 := swUW_gen_dt (F := F') (R := EC E) hI hrc.tail hrc.main hC0
    (fun c v (hp : UPost [d] lbl Spike.Lib.X64Consumer.c0 c v) => hp.1 ▸ hC0) hmph hsw h8 hok (by omega) hL8 hZ
    hZ8 hps hkm hmr hsub hfit hU
  have hEC := ec_facts _ hE hsub
  refine Spike.Lib.X64.Rt.startU_segW (Ly).lays rfl hrc.call hrc.start hrc.tcb hrc.call2 hrc.tail hrc.ti hrc.take
    hrc.main hZ hZ8 hps hkm (D := D) (by omega) hD8 (L := swLD D) hL hL8 rfl hF' hEC.1
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

/-- **`x64_start_segW1` from `x64_start_segW1D`** at the frame's depth
`fr.size + 48` (its switch region `swL fr.size`, `swLD_frame`): the
call-free case, where `main`'s need is its frame. -/
theorem x64_start_segW1_ofD {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) (hs : o.place.tail = .bare)
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
  rw [← swLD_frame] at hgen
  exact x64_start_segW1D h i hd hs hf (Int.le_refl _) (by omega) (by omega) hpro hr hcode hbl hfree hE hphP hC0
    hab himm hwr hGh hGf hGt hownT hG1 hG0 hGn hownL hownF hownN hroomM hroomU hmph hsw hgen

end Start

/-! ## The user depth from the stack need -/

/-- **The user depth from `main`'s stack need `n`** (its row of the stack
need table: the most bytes below its entry stack pointer until it returns):
at least the frame's depth `fr.size + 48` (`x64_start_segW1D`'s floor) and
the need with the return address and the overflow stub's `32` bytes
(`n + 40`), rounded up to 8. With no calls the need is the frame below the
entry stack pointer, `fr.size + 8`, and `needD` is `fr.size + 48`
(`needD_frame`). -/
def needD (fr : Scc.Emit.X64.Frame) (n : Nat) : Int :=
  max ((fr.size : Int) + 48) (8 * (((n : Int) + 40 + 7) / 8))

/-- `needD` meets `x64_start_segW1D`'s hypotheses on `D` when its switch
region fits the first stack, and covers the need. -/
theorem needD_ok (fr : Scc.Emit.X64.Frame) (n : Nat) (h16 : fr.size % 16 = 0) (hcap : needD fr n + 56 ≤ 16384) :
    (fr.size : Int) + 48 ≤ needD fr n ∧ needD fr n % 8 = 0 ∧ needD fr n + 56 ≤ 16384 ∧
      (n : Int) + 40 ≤ needD fr n := by
  unfold needD at *
  omega

/-- **With no calls `needD` is the frame's depth**: at the need `fr.size +
8` (the frame and the saved `%rbp`, the row `needOk1` checks). -/
theorem needD_frame (fr : Scc.Emit.X64.Frame) (h16 : fr.size % 16 = 0) :
    needD fr (fr.size + 8) = (fr.size : Int) + 48 := by
  unfold needD
  omega

/-- **`main`'s switch region by its stack need fits the first stack**: the
row of the function `name` (at the frame `fr`) of the stack need table
`tbl` (`o.place.need`, checked by `placeOKAt`'s A4 and `needOk1`) has a
need `n` with `needD fr n + 56 ≤ 16384`. Decided per program, as
`MainFrame1Ok`. -/
def MainNeedOk (tbl : List Scc.Cert.NeedX64.Row) (name : String) (fr : Scc.Emit.X64.Frame) : Bool :=
  match Scc.Cert.NeedX64.row? tbl name with
  | some (_, _, n) => decide (needD fr n + 56 ≤ 16384)
  | none => false

/-- `MainNeedOk` gives the row's need and the bound. -/
theorem mainNeedOk_row {tbl : List Scc.Cert.NeedX64.Row} {name : String} {fr : Scc.Emit.X64.Frame}
    (h : MainNeedOk tbl name fr = true) :
    ∃ l f n, Scc.Cert.NeedX64.row? tbl name = some (l, f, n) ∧ needD fr n + 56 ≤ 16384 := by
  unfold MainNeedOk at h
  split at h
  · next l f n hr => exact ⟨l, f, n, hr, by simpa using h⟩
  · cases h

/-- **`MainFrame1Ok`'s bound is `MainNeedOk`'s at the frame's need**: a
frame of at most `4096` bytes (16-aligned) fits by `needD_frame`. -/
theorem needD_frame_cap (fr : Scc.Emit.X64.Frame) (h4 : fr.size ≤ 4096) (h16 : fr.size % 16 = 0) :
    needD fr (fr.size + 8) + 56 ≤ 16384 := by
  rw [needD_frame fr h16]; omega

end Spike.Lib.LowerX64
