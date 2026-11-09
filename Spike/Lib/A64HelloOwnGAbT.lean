/-
**hello.w's global owned-words map on the threads abort path, node by node**
(AArch64; twin of `A64WakeOwnGAbT`): wake's `WakePh.AbPT`
(`AbP` at every node of `scc_rt_abort(5)` and `scc_rt_abort_threads` and at
its successors, in the dispatcher's region) at hello's labels, and hence
`ownGH`'s agreement with the instance it picks there on every obligation of
`Abort.Disp.StubTW` (`AbAgreeH`, `abAgreeH`). The program-independent
pieces (`WakePh.AbW`, `AbPT`, `abP_blk'`, `keep_adrp`, `keep_add`) are
wake's.

- `ab_labsH`: the path's labels, resolved in `helloProg`.
- `abPTH`: `AbPT` at hello's labels.
- `AgWH`, `AbAgreeH`, `abAgreeH`: the agreement at every node of the path
  from where `ownGH` picks the instance there; `abAgree2aH`, `abAgree2bH`
  (from `.L22_wc_main.sp15`), `abAgreeWH`.
-/
import Spike.Lib.A64HelloOwnGAb
import Spike.Lib.A64WakeOwnGAbT

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
open Spike.Lib.A64.WakePh (AbP AbW AbPT BandIn BandOut Keep keep_svc keep_pc keep_adrp keep_add abP_blk' abP_node
  BlkW.agree_of NodeW.agree_of)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout}

/-- **The threads abort path's labels**, resolved at hello's base `lo`. -/
theorem ab_labsH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_abort" = Int64.ofNat 2168064 ∧ L.lab "scc_rt_thr_worker" = Int64.ofNat 2168628 ∧
    L.lab ".L12_scc_rt_abort.0_entry" = Int64.ofNat 2168084 ∧
    L.lab ".L12_scc_rt_abort.1_is0" = Int64.ofNat 2168104 ∧
    L.lab ".L12_scc_rt_abort.2_next1" = Int64.ofNat 2168120 ∧
    L.lab ".L12_scc_rt_abort.3_is2" = Int64.ofNat 2168140 ∧
    L.lab ".L12_scc_rt_abort.4_next3" = Int64.ofNat 2168156 ∧
    L.lab ".L12_scc_rt_abort.5_is4" = Int64.ofNat 2168176 ∧
    L.lab ".L12_scc_rt_abort.6_next5" = Int64.ofNat 2168192 ∧
    L.lab ".L12_scc_rt_abort.7_is6" = Int64.ofNat 2168212 ∧
    L.lab ".L12_scc_rt_abort.8_next7" = Int64.ofNat 2168228 ∧
    L.lab ".L12_scc_rt_abort.9_is8" = Int64.ofNat 2168248 ∧
    L.lab ".L12_scc_rt_abort.10_next9" = Int64.ofNat 2168264 ∧
    L.lab "scc_rt_abort_threads" = Int64.ofNat 2168556 ∧
    L.lab ".L17_scc_rt_abort_threads.0_entry" = Int64.ofNat 2168572 ∧
    L.lab "scc_rt_abort_threads_exit" = Int64.ofNat 2168616 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
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
local macro "ab_blk " cd:term:max ok:ident b:ident : tactic =>
  `(tactic| (
    refine abP_blk' $cd $ok hR hal (by omega) hhi hsite ?_ ?_
    · intro k hk
      simp only [$b:ident, List.length_cons, List.length_nil] at hk
      simp only [DN.nd5, NT, Abort.Disp.DN.nd, Abort.N, Abort.pcSvc, Abort.threads]
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
        e11, e12, e13, e14, e15, e16] <;> decide
    · intro σ c hJ k hk
      simp only [$b:ident, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd5, NT, Abort.JR, Abort.JI, Abort.pcSvc, Abort.threads] at hJ ⊢
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> arun_simp <;>
        simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, hJ] <;>
        (try split) <;> decide))

set_option hygiene false in
/-- A single-instruction node of the path: `abP_node` with the successors
from `kp` at its cell `cd`. -/
local macro "ab_node " cd:term:max kp:term : tactic =>
  `(tactic| (
    refine abP_node (fun s c hAt s' h => ?_) ?_ (by simp only [NT]; decide) (fun σ c hJ => ?_)
    · obtain ⟨he, hn, -, hp, -⟩ := hAt
      have hc := ($cd s he hn).cell (j := 0) rfl rfl rfl (by rw [hp]; simp)
      exact ⟨$kp hc h, by rw [keep_pc hc ($kp hc h), hp]; rfl⟩
    · simp only [NT, Abort.pcSvc, Abort.threads, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
        e15, e16]
      decide
    · simp only [NT, Abort.JR, Abort.JI] at hJ
      first | exact hJ.2 | exact hJ.1.2))

/-- The successors of an `svc` cell keep `sp` and `x30`. -/
private theorem keep_svcAtH {μ : Scc.Sem.Marks} {s s' : State}
    (hc : Kraken.Promising.Lower.A64.CellAt s Spike.Lib.A64.Flow.svcDir 4) (h : StSucc μ s s') : Keep s s' :=
  keep_svc (Scc.Sem.A64.atSvc_of_cellAt hc) h

/-- **`AbP` at every node of the threads abort path**: in the dispatcher's
region `R` (covering its 32-byte frame and the stub's 48), the take site
off the path (`hsite`), the code of the dispatcher and of the threads
stub. -/
theorem abPTH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {μ : Scc.Sem.Marks}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.threads c0 Abort.b1Threads L.exe endPc) :
    AbPT L μ endPc R F c0 ra := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := ab_labsH hlab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ab_blk hd.e Abort.Disp.d0_ok Abort.Disp.d0
  · ab_blk hd.t1 Abort.Disp.t1_ok Abort.Disp.t1
  · ab_blk hd.j1 Abort.Disp.j1_ok Abort.Disp.j1
  · ab_blk hd.t2 Abort.Disp.t2_ok Abort.Disp.t2
  · ab_blk hd.j2 Abort.Disp.j2_ok Abort.Disp.j2
  · ab_blk hd.t3 Abort.Disp.t3_ok Abort.Disp.t3
  · ab_blk hd.j3 Abort.Disp.j3_ok Abort.Disp.j3
  · ab_blk hd.t4 Abort.Disp.t4_ok Abort.Disp.t4
  · ab_blk hd.j4 Abort.Disp.j4_ok Abort.Disp.j4
  · ab_blk hd.t5 Abort.Disp.t5_ok Abort.Disp.t5
  · ab_blk hd.g5 Abort.Disp.g5_ok Abort.Disp.g5
  · ab_blk hs.e Abort.b0_ok Abort.b0
  · ab_node hs.n1 keep_adrp
  · ab_node hs.n1b keep_add
  · ab_blk hs.n2 Abort.b1Threads_ok Abort.b1Threads
  · ab_node hs.svc keep_svcAtH
  · ab_blk hs.n5 Abort.b2_ok Abort.b2
  · ab_node hs.ex keep_svcAtH

/-! ### The agreement -/

/-- **`ownGH` agrees with `own` at a state and its successors.** -/
def AgWH (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks) :
    Frag isaLSE2 :=
  fun s _ => ownGH L a s = own s ∧ ∀ s', StSucc μ s s' → ownGH L a s' = own s'

/-- **`ownGH`'s agreement with `own` at every node of the threads abort
path** (`hag` of `BlkW.ownCongr2` and `SFactsSt2.congr`'s at each of
`Abort.Disp.StubTW`'s obligations and the `write` call's node). -/
structure AbAgreeH (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t2) Abort.Disp.t2
  dj2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j2) Abort.Disp.j2
  dt3 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t3) Abort.Disp.t3
  dj3 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j3) Abort.Disp.j3
  dt4 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t4) Abort.Disp.t4
  dj4 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j4) Abort.Disp.j4
  dt5 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t5) Abort.Disp.t5
  dg5 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .g5) Abort.Disp.g5
  se : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .e) Abort.b0
  sn1 : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n1)
  sn1b : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n1b)
  sn2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n2) Abort.b1Threads
  ssvc : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .svc)
  sn5 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n5) Abort.b2
  sex : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .ex)

/-- **The agreement on the path from where `ownGH` picks `own` on it**
(`hpick`: `good2aH_ab`, `good2bH_ab` or `goodWH_ab` with `ownGH_2a`, `ownGH_2b`,
`ownGH_W`). -/
theorem abAgreeH {a : BitVec 64} {own : State → List (Loc × Val)} {μ : Scc.Sem.Marks} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} (h : AbPT L μ endPc R F c0 ra)
    (hpick : ∀ s, AbP L R ra s → ownGH L a s = own s) : AbAgreeH L a own μ endPc R F c0 ra :=
  ⟨BlkW.agree_of h.de hpick, BlkW.agree_of h.dt1 hpick, BlkW.agree_of h.dj1 hpick,
    BlkW.agree_of h.dt2 hpick, BlkW.agree_of h.dj2 hpick, BlkW.agree_of h.dt3 hpick,
    BlkW.agree_of h.dj3 hpick, BlkW.agree_of h.dt4 hpick, BlkW.agree_of h.dj4 hpick,
    BlkW.agree_of h.dt5 hpick, BlkW.agree_of h.dg5 hpick, BlkW.agree_of h.se hpick,
    NodeW.agree_of h.sn1 hpick, NodeW.agree_of h.sn1b hpick, BlkW.agree_of h.sn2 hpick,
    NodeW.agree_of h.ssvc hpick, BlkW.agree_of h.sn5 hpick, NodeW.agree_of h.sex hpick⟩

/-- **The agreement with `own2aH`** on the path from `scc_rt_alloc_tcb`'s
abort on a pool stack. -/
theorem abAgree2aH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (h : AbPT L μ endPc R F c0 (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec) (hb : BandIn L R) :
    AbAgreeH L a (fun s => own2aH L a (ph2aH (pcOf s))) μ endPc R F c0 (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec :=
  abAgreeH h fun _ hs => ownGH_2a hlab (good2aH_ab hs hb)

/-- **The agreement with `own2bH`** on the path from `wc_main`'s spawn
failure. -/
theorem abAgree2bH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (h : AbPT L μ endPc R F c0 (L.lab ".L22_wc_main.sp15").toBitVec) :
    AbAgreeH L a (fun s => own2bH L a (ph2bH (pcOf s))) μ endPc R F c0 (L.lab ".L22_wc_main.sp15").toBitVec :=
  abAgreeH h fun _ hs => ownGH_2b hlab (good2bH_ab hlab hs)

/-- **The agreement with `ownH`** on the path from any other caller, or from
`scc_rt_alloc_tcb`'s abort off the pool stacks. -/
theorem abAgreeWH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : AbPT L μ endPc R F c0 ra)
    (h13 : ra = (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec → BandOut L R)
    (h15 : ra ≠ (L.lab ".L22_wc_main.sp15").toBitVec) :
    AbAgreeH L a (fun s => ownH L a (phH (pcOf s))) μ endPc R F c0 ra :=
  abAgreeH h fun _ hs => ownGH_W hlab (goodWH_ab hs h13 h15)

/-- info: 'Spike.Lib.A64.HelloPh.abPTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abPTH

/-- info: 'Spike.Lib.A64.HelloPh.abAgree2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.abAgree2bH

end Spike.Lib.A64.HelloPh
