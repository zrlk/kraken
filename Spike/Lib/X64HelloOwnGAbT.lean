/-
**hello.w's global owned-words map on the threads abort path, node by node**
(x86-64; the twin of `Spike/Lib/A64HelloOwnGAbT.lean`, at the template of
`Spike/Lib/X64WakeOwnGAbT.lean`): wake's `WakePh.AbPT` (`AbP` at every node
of `scc_rt_abort(5)` and `scc_rt_abort_threads` and at its successors, in
the dispatcher's region) at hello's labels, and hence `ownGH`'s agreement
with the instance it picks there on every obligation of
`Abort.Disp.StubTW` (`AbAgreeH`, `abAgreeH`). The program-independent
pieces (`WakePh.AbW`, `AbPT`, `abP_blk'`, `abP_node`, `ns_of`, `raOK_bp`,
`keepM_lea`, `keepM_sysAt`) are wake's.

- `ab_labsH`: the path's labels (and the other stubs' and taken tests',
  which `raSp` reads), resolved in `helloCells`.
- `abPTH`: `AbPT` at hello's labels.
- `AgWH`, `AbAgreeH`, `abAgreeH`: the agreement at every node of the path
  from where `ownGH` picks the instance there; `abAgree2bH` (from
  `.Lwc_main.x5`).

**Deviation from the A64 file.** As in `X64WakeOwnGAbT`: the return address
is the region's word at offset `8` (`slot 8`, `RaOK`), so `abPTH`
discharges `RaOK`, `R.Off 8` and `slot 8 = ra` from the region's bounds
(`[-24, 16)` at least, no `hal`); the stub's `leaq` is one node, so
`AbPT`/`AbAgreeH` have 17 fields (A64: 18); the `write` call's node is
`ssvc` at `NT .sys`. A64's `abAgree2aH` and `abAgreeWH` have no consumer
and are not twinned.
-/
import Spike.Lib.X64HelloOwnGAb
import Spike.Lib.X64WakeOwnGAbT

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc)
open Spike.Lib.X64 (BlkW NodeW SO)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN)
open Spike.Lib.X64.WakePh (AbP AbPT RaOK raSp raSp8 abFns abGos abP_blk' abP_node ns_of raOK_bp keep_pc
  keepM_lea keepM_sysAt BlkW.agree_of NodeW.agree_of)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout}

/-- **The threads abort path's labels**, resolved at hello's base, with the
other stubs' and the taken tests' (`raSp`, `raSp8`). -/
theorem ab_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_abort" = Int64.ofNat 4202524 ∧ L.lab "scc_rt_thr_worker" = Int64.ofNat 4203010 ∧
    L.lab ".Lscc_rt_abort.entry" = Int64.ofNat 4202536 ∧
    L.lab ".Lscc_rt_abort.is0" = Int64.ofNat 4202554 ∧
    L.lab ".Lscc_rt_abort.next1" = Int64.ofNat 4202560 ∧
    L.lab ".Lscc_rt_abort.is2" = Int64.ofNat 4202578 ∧
    L.lab ".Lscc_rt_abort.next3" = Int64.ofNat 4202587 ∧
    L.lab ".Lscc_rt_abort.is4" = Int64.ofNat 4202605 ∧
    L.lab ".Lscc_rt_abort.next5" = Int64.ofNat 4202614 ∧
    L.lab ".Lscc_rt_abort.is6" = Int64.ofNat 4202632 ∧
    L.lab ".Lscc_rt_abort.next7" = Int64.ofNat 4202641 ∧
    L.lab ".Lscc_rt_abort.is8" = Int64.ofNat 4202659 ∧
    L.lab "scc_rt_abort_overflow" = Int64.ofNat 4202670 ∧
    L.lab "scc_rt_abort_heap" = Int64.ofNat 4202738 ∧
    L.lab "scc_rt_abort_stack" = Int64.ofNat 4202806 ∧
    L.lab "scc_rt_abort_write" = Int64.ofNat 4202874 ∧
    L.lab "scc_rt_abort_threads" = Int64.ofNat 4202942 ∧
    L.lab ".Lscc_rt_abort_threads.entry" = Int64.ofNat 4202950 ∧
    L.lab "scc_rt_abort_threads_exit" = Int64.ofNat 4203002 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- The abstract run's simp set over the path's blocks
(`Spike/Lib/X64WakeOwnGAbT.lean`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg, Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, Spike.Lib.X64.SO.get, Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write,
    Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.tgt_jmp', Spike.Lib.X64.BlockSpec.AI.tgt_jcc',
    Spike.Lib.X64.BlockSpec.AI.tgt_ld', Spike.Lib.X64.BlockSpec.AI.tgt_st',
    Spike.Lib.X64.BlockSpec.AI.tgt_push', Spike.Lib.X64.BlockSpec.AI.tgt_pop',
    Spike.Lib.X64.BlockSpec.AI.tgt_reg'])

set_option hygiene false in
/-- A block of the path: `abP_blk'` with its code `cd`, its `okBlk` `ok`,
the block `b`, its pcs and its run's facts decided on the resolved labels. -/
local macro "ab_blk " cd:term:max ok:ident b:ident : tactic =>
  `(tactic| (
    refine abP_blk' $cd $ok hR (by omega) (by omega) (by omega) (by omega) hsite ?_ ?_
    · intro k hk
      simp only [$b:ident, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd5, NT, Abort.pcSys, Abort.threads]
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> simp [Spike.Lib.X64.cellOff, e1, e2, e3, e4, e5, e6, e7, e8,
        e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19] <;> decide
    · intro σ c hJ k hk
      simp only [$b:ident, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd5, NT, Abort.JR, Abort.JI, Abort.pcSys, Abort.threads] at hJ ⊢
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> arun_simp <;>
        simp only [RaOK, raSp, raSp8, abFns, abGos, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
          hJ] <;>
        (try split) <;> decide))

set_option hygiene false in
/-- A single-instruction node `nd` of the path: `abP_node` with the
successors from `kp` at its cell `cd` of size `sz`. -/
local macro "ab_node " cd:term:max kp:term:max nd:term:max sz:term:max : tactic =>
  `(tactic| (
    have hP : ∀ p ∈ [($nd).pc, ($nd).pc + Int64.ofNat $sz],
        (L.lab "scc_rt_abort").toBitVec.toNat ≤ p.toBitVec.toNat ∧
          p.toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat := by
      simp only [NT, Abort.pcSys, Abort.threads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19]
      decide
    refine abP_node (sz := $sz) hoff (fun s c hAt s' h => ?_) hP ?_ (by simp only [NT]; decide)
      (fun σ c hJ => ?_)
    · obtain ⟨he, hn, -, hp, -⟩ := hAt
      have hc := ($cd s he hn).cell0 rfl rfl hp
      obtain ⟨hK, hm⟩ := $kp hc (ns_of hsite hp (hP _ (by simp))) h
      exact ⟨hK, hm, by rw [keep_pc hc hK, hp]⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> refine raOK_bp ?_ ?_ rfl <;>
        simp only [raSp, raSp8, abFns, abGos, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          NT, Abort.pcSys, Abort.threads, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19] <;>
        decide
    · simp only [NT, Abort.JR, Abort.JI] at hJ
      first | exact hJ.2 | exact hJ.1.2))

/-- **`AbP` at every node of the threads abort path** at hello's labels: in
the dispatcher's region `R` (covering its frame `[-24, 16)`, the return
address at `8`), the take site off the path (`hsite`), the code of the
dispatcher and of the threads stub. -/
theorem abPTH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {μ : Scc.Sem.Marks}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.threads c0 Abort.x1Threads L.exe endPc) :
    AbPT L μ endPc R F c0 ra := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19⟩ := ab_labsH hlab
  have hoff : R.Off 8 := ⟨by omega, by omega, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · ab_blk hs.e Abort.x0_ok Abort.x0
  · ab_node hs.n1 keepM_lea (NT L.lab Abort.threads c0 ra .n1) 7
  · ab_blk hs.n2 Abort.x1Threads_ok Abort.x1Threads
  · ab_node hs.sys keepM_sysAt (NT L.lab Abort.threads c0 ra .sys) 2
  · ab_blk hs.n5 Abort.x2_ok Abort.x2
  · ab_node hs.ex keepM_sysAt (NT L.lab Abort.threads c0 ra .ex) 2

/-! ### The agreement -/

/-- **`ownGH` agrees with `own` at a state and its successors.** -/
def AgWH (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks) : Frag isa :=
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
  se : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .e) Abort.x0
  sn1 : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n1)
  sn2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n2) Abort.x1Threads
  ssvc : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .sys)
  sn5 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n5) Abort.x2
  sex : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .ex)

/-- **The agreement on the path from where `ownGH` picks `own` on it**
(`hpick`: `good2bH_ab` or `goodWH_ab` with `ownGH_2b`, `ownGH_W`). -/
theorem abAgreeH {a : BitVec 64} {own : State → List (Loc × Val)} {μ : Scc.Sem.Marks} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} (h : AbPT L μ endPc R F c0 ra)
    (hpick : ∀ s, AbP L R ra s → ownGH L a s = own s) : AbAgreeH L a own μ endPc R F c0 ra :=
  ⟨BlkW.agree_of h.de hpick, BlkW.agree_of h.dt1 hpick, BlkW.agree_of h.dj1 hpick,
    BlkW.agree_of h.dt2 hpick, BlkW.agree_of h.dj2 hpick, BlkW.agree_of h.dt3 hpick,
    BlkW.agree_of h.dj3 hpick, BlkW.agree_of h.dt4 hpick, BlkW.agree_of h.dj4 hpick,
    BlkW.agree_of h.dt5 hpick, BlkW.agree_of h.dg5 hpick, BlkW.agree_of h.se hpick,
    NodeW.agree_of h.sn1 hpick, BlkW.agree_of h.sn2 hpick,
    NodeW.agree_of h.ssvc hpick, BlkW.agree_of h.sn5 hpick, NodeW.agree_of h.sex hpick⟩

/-- **The agreement with `own2bH`** on the path from `wc_main`'s spawn
failure. -/
theorem abAgree2bH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (h : AbPT L μ endPc R F c0 (L.lab ".Lwc_main.x5").toBitVec) :
    AbAgreeH L a (fun s => own2bH L a (ph2bH (pcOf s))) μ endPc R F c0 (L.lab ".Lwc_main.x5").toBitVec :=
  abAgreeH h fun _ hs => ownGH_2b hlab (good2bH_ab hlab hs)

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.ab_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ab_labsH

/-- info: 'Spike.Lib.X64.HelloPh.abPTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abPTH

/-- info: 'Spike.Lib.X64.HelloPh.abAgreeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abAgreeH

/-- info: 'Spike.Lib.X64.HelloPh.abAgree2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abAgree2bH
