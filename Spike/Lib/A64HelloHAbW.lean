/-
**hello.w's heap abort path at `ownGH`** (AArch64; the twin of
`A64WakeHAbW` at `SccCode.helloProg`): wake's `WakePh.AbPH` (`AbP` at every node of `scc_rt_abort(2)` with the
return address and of `scc_rt_abort_heap`) at hello's labels, `ownGH`'s agreement with the instance it picks
there on every obligation of `Abort.Disp.HPathW`, and the path's phase check at `phH`. The program-independent
pieces (`WakePh.AbPH`, `AbW`, `abP_blk'`, `abP_node`, `keep_adrp`, `keep_add`, `BlkW.agree_of`,
`NodeW.agree_of`) are wake's.

- `abH_labsH`: the path's labels, resolved in `helloProg` (with the take and release sites and the callers'
  return points, off the path).
- `abPHH`: `AbPH` at hello's labels.
- `AbHAgreeH`, `abHAgreeH`, `abHAgreeWH`: the agreement at every node of the path from where `ownGH` picks the
  instance there (`ownH` from a caller other than `.L3_scc_rt_alloc_tcb.sp13` on a pool stack and
  `.L22_wc_main.sp15`).
- `abortHTabH`, `abortHFactsH`, `abortPhHH`: `abortPhHeapOk` at `phH`.
-/
import Spike.Lib.A64HelloOwnGAbT
import Spike.Lib.A64WakeHAbW

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf nextPc abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc SpAt)
open Spike.Lib.A64.Flow (ND BlkW NodeW At SI)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)
open Spike.Lib.A64.WakePh (AbP AbW AbPH BandOut Keep keep_svc keep_pc keep_adrp keep_add abP_blk' abP_node
  BlkW.agree_of NodeW.agree_of)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout}

/-- **The heap abort path's labels**, resolved at hello's base `lo` (with the take and release sites, off the
path, and the callers' return points). -/
theorem abH_labsH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_abort" = Int64.ofNat 2168064 ∧ L.lab "scc_rt_thr_worker" = Int64.ofNat 2168628 ∧
    L.lab ".L12_scc_rt_abort.0_entry" = Int64.ofNat 2168084 ∧
    L.lab ".L12_scc_rt_abort.1_is0" = Int64.ofNat 2168104 ∧
    L.lab ".L12_scc_rt_abort.2_next1" = Int64.ofNat 2168120 ∧
    L.lab ".L12_scc_rt_abort.3_is2" = Int64.ofNat 2168140 ∧
    L.lab "scc_rt_abort_heap" = Int64.ofNat 2168340 ∧
    L.lab ".L14_scc_rt_abort_heap.0_entry" = Int64.ofNat 2168356 ∧
    L.lab "scc_rt_abort_heap_exit" = Int64.ofNat 2168400 ∧
    codeOf lo SccCode.helloProg "scc_rt_take_site" = some 2165980 ∧
    codeOf lo SccCode.helloProg "scc_rt_release_site" = some 2166036 ∧
    L.lab ".L2_scc_rt_alloc.4_full" = Int64.ofNat 2164516 ∧
    L.lab ".L3_scc_rt_alloc_tcb.sp13" = Int64.ofNat 2164996 ∧
    L.lab ".L22_wc_main.sp15" = Int64.ofNat 2169912 ∧ L.lab ".L22_wc_main.sp6" = Int64.ofNat 2169772 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, ?_, ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- The abstract run's simp set over the path's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Flow.arun, Flow.dstep, Flow.classify, Flow.RegOnly, Flow.AI.so, Flow.AI.step, Flow.AI.tgt,
    Flow.soReg, Flow.regDst, Flow.zrB, Flow.regRes, Operation.interp, MachineData.setRegOrZr,
    MachineData.setRegOrSp, Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64,
    Reg64s.setRegOrSp, Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg,
    Reg64s.getXReg, ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Flow.SO.get, Flow.SO.set, Flow.SO.kill, Flow.SO.write, Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm])

set_option hygiene false in
/-- A block of the path: `abP_blk'` with its code `cd`, its `okBlk` `ok`,
the block `b`, its pcs and its run's facts decided on the resolved labels. -/
local macro "abh_blk " cd:term:max ok:ident b:ident : tactic =>
  `(tactic| (
    refine abP_blk' $cd $ok hR hal (by omega) hhi hsite ?_ ?_
    · intro k hk
      simp only [$b:ident, List.length_cons, List.length_nil] at hk
      simp only [DN.nd2R, NT, Abort.N, Abort.pcSvc, Abort.heap]
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9] <;> decide
    · intro σ c hJ k hk
      simp only [$b:ident, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd2R, NT, Abort.JR, Abort.JI, Abort.pcSvc, Abort.heap] at hJ ⊢
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> arun_simp <;>
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, hJ] <;>
        (try split) <;> decide))

set_option hygiene false in
/-- A single-instruction node of the path: `abP_node` with the successors
from `kp` at its cell `cd`. -/
local macro "abh_node " cd:term:max kp:term : tactic =>
  `(tactic| (
    refine abP_node (fun s c hAt s' h => ?_) ?_ (by simp only [NT]; decide) (fun σ c hJ => ?_)
    · obtain ⟨he, hn, -, hp, -⟩ := hAt
      have hc := ($cd s he hn).cell (j := 0) rfl rfl rfl (by rw [hp]; simp)
      exact ⟨$kp hc h, by rw [keep_pc hc ($kp hc h), hp]; rfl⟩
    · simp only [NT, Abort.pcSvc, Abort.heap, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      decide
    · simp only [NT, Abort.JR, Abort.JI] at hJ
      first | exact hJ.2 | exact hJ.1.2))

/-- The successors of an `svc` cell keep `sp` and `x30`. -/
private theorem keep_svcAtHH {μ : Scc.Sem.Marks} {s s' : State}
    (hc : Kraken.Promising.Lower.A64.CellAt s Spike.Lib.A64.Flow.svcDir 4) (h : StSucc μ s s') : Keep s s' :=
  keep_svc (Scc.Sem.A64.atSvc_of_cellAt hc) h

/-- **`AbP` at every node of the heap abort path** at hello's labels: in the dispatcher's region `R` (covering
its 32-byte frame and the stub's 48), the take site off the path (`hsite`), the code of the dispatcher and of
the heap stub. -/
theorem abPHH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {μ : Scc.Sem.Marks}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.heap c0 Abort.b1Heap L.exe endPc) :
    AbPH L μ endPc R F c0 ra := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, -, -, -, -, -, -⟩ := abH_labsH hlab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · abh_blk hd.e Abort.Disp.d0_ok Abort.Disp.d0
  · abh_blk hd.t1 Abort.Disp.t1_ok Abort.Disp.t1
  · abh_blk hd.j1 Abort.Disp.j1_ok Abort.Disp.j1
  · abh_blk hd.t2 Abort.Disp.t2_ok Abort.Disp.t2
  · abh_blk hd.g2 Abort.Disp.g2_ok Abort.Disp.g2
  · abh_blk hs.e Abort.b0_ok Abort.b0
  · abh_node hs.n1 keep_adrp
  · abh_node hs.n1b keep_add
  · abh_blk hs.n2 Abort.b1Heap_ok Abort.b1Heap
  · abh_node hs.svc keep_svcAtHH
  · abh_blk hs.n5 Abort.b2_ok Abort.b2
  · abh_node hs.ex keep_svcAtHH

/-! ### The agreement -/

/-- **`ownGH`'s agreement with `own` at every node of the heap abort path** (`hag` of `BlkW.ownCongr2` and
`SFactsSt2.congr`'s at each of `Abort.Disp.HPathW`'s obligations). -/
structure AbHAgreeH (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t2) Abort.Disp.t2
  dg2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .g2) Abort.Disp.g2
  se : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .e) Abort.b0
  sn1 : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n1)
  sn1b : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n1b)
  sn2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n2) Abort.b1Heap
  ssvc : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .svc)
  sn5 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n5) Abort.b2
  sex : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .ex)

/-- **The agreement on the heap path from where `ownGH` picks `own` on it.** -/
theorem abHAgreeH {a : BitVec 64} {own : State → List (Loc × Val)} {μ : Scc.Sem.Marks} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} (h : AbPH L μ endPc R F c0 ra)
    (hpick : ∀ s, AbP L R ra s → ownGH L a s = own s) : AbHAgreeH L a own μ endPc R F c0 ra :=
  ⟨BlkW.agree_of h.de hpick, BlkW.agree_of h.dt1 hpick, BlkW.agree_of h.dj1 hpick,
    BlkW.agree_of h.dt2 hpick, BlkW.agree_of h.dg2 hpick, BlkW.agree_of h.se hpick,
    NodeW.agree_of h.sn1 hpick, NodeW.agree_of h.sn1b hpick, BlkW.agree_of h.sn2 hpick,
    NodeW.agree_of h.ssvc hpick, BlkW.agree_of h.sn5 hpick, NodeW.agree_of h.sex hpick⟩

/-- **The agreement with `ownH`** on the heap path from a caller other than the two return points `ownGH`
reads there. -/
theorem abHAgreeWH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {a : BitVec 64} {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {ra : BitVec 64} (h : AbPH L μ endPc R F c0 ra)
    (h13 : ra = (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec → BandOut L R)
    (h15 : ra ≠ (L.lab ".L22_wc_main.sp15").toBitVec) :
    AbHAgreeH L a (fun s => ownH L a (phH (pcOf s))) μ endPc R F c0 ra :=
  abHAgreeH h fun _ hs => ownGH_W hlab (goodWH_ab hs h13 h15)

/-! ### The heap abort path's phase check at `phH` -/

/-- **The heap abort path's facts** (`abortPhHeapOk`'s), as the certificate's table. -/
def abortHTabH : List Scc.Cert.Rt.A64.PhFact :=
  [.blk "scc_rt_abort" 0 Abort.Disp.d0 none none, .blk ".L12_scc_rt_abort.0_entry" 0 Abort.Disp.t1 none none,
   .blk ".L12_scc_rt_abort.0_entry" 4 Abort.Disp.j1 none none,
   .blk ".L12_scc_rt_abort.2_next1" 0 Abort.Disp.t2 none none,
   .blk ".L12_scc_rt_abort.3_is2" 0 Abort.Disp.g2 none none, .blk "scc_rt_abort_heap" 0 Abort.b0 none none,
   .step ".L14_scc_rt_abort_heap.0_entry" 0, .step ".L14_scc_rt_abort_heap.0_entry" 1,
   .blk ".L14_scc_rt_abort_heap.0_entry" 2 Abort.b1Heap none none, .step ".L14_scc_rt_abort_heap.0_entry" 7,
   .blk ".L14_scc_rt_abort_heap.0_entry" 8 Abort.b2 none none,
   .ph "scc_rt_abort_heap_exit" 1 0, .ph "scc_rt_abort_heap_exit" 0 0]

/-- The table's facts hold at the resolved phases. -/
theorem abortHFactsH : abortHTabH.all (Scc.Cert.Rt.A64.factOk (codeT lo SccCode.helloProg) okC phC) = true := by
  decide +kernel

/-- **`abortPhHeapOk` at `phH`** with the certificate's labels. -/
theorem abortPhHH {Λ : Scc.Sem.Layout} {lab : Label → Int64} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    Spike.Lib.A64.StubW.abortPhHeapOk (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) phH lab = true := by
  have h := abortHFactsH
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at h
  simp only [abortHTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = lab r := fun _ h => by cases h
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have so : ∀ {l : String} {k : Nat},
      Scc.Cert.Rt.A64.factOk (codeOf lo SccCode.helloProg) (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) phH
        (.step l k) = true →
      Spike.Lib.A64.StubW.phOne (Scc.Cert.Rt.A64.okPcOf lo SccCode.helloProg Λ) phH (lab l + Int64.ofNat (4 * k))
        = true :=
    fun h => by
      obtain ⟨h1, h2⟩ := Spike.Lib.A64.Rt.PhOfTab.step_of_factOk hlab h
      simp only [Spike.Lib.A64.StubW.phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have e11 := Spike.Lib.A64.Rt.PhOfTab.ph_of_factOk hlab f11
  have e12 := Spike.Lib.A64.Rt.PhOfTab.ph_of_factOk hlab f12
  rw [Spike.Lib.A64.Flow.ofNat4_zero] at e12
  unfold Spike.Lib.A64.StubW.abortPhHeapOk
  simp only [Abort.heap]
  rw [Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f0, Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f1,
    Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f2, Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f3,
    Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f4, Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f5,
    so f6, so f7, Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f8, so f9,
    Spike.Lib.A64.Rt.PhOfTab.blkPh_of_factOk hlab hr hn f10]
  simp only [Bool.true_and, beq_iff_eq]
  exact e11.trans e12.symm

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.abH_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abH_labsH

/-- info: 'Spike.Lib.A64.HelloPh.abPHH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abPHH

/-- info: 'Spike.Lib.A64.HelloPh.abHAgreeWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abHAgreeWH

/-- info: 'Spike.Lib.A64.HelloPh.abortPhHH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abortPhHH
