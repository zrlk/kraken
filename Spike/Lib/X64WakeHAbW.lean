/-
**wake.w's heap abort path at `ownG`** (x86-64; the twin of
`Spike/Lib/A64WakeHAbW.lean`): `AbP` (`Spike/Lib/X64WakeOwnGAb.lean`) at
every node of `scc_rt_abort(2)` with the return address
(`Abort.Disp.DN.nd2R`) and of `scc_rt_abort_heap` (`Abort.NT … Abort.heap`),
hence `ownG`'s agreement with the instance it picks there on every
obligation of `Abort.Disp.HPathW` (`Spike/Lib/X64WakeOwnGAbT.lean`'s threads
path, at the heap code).

- `abH_labs`: the heap stub's entry and exit labels, resolved (the rest of
  the path's are `ab_labs`').
- `AbPH`: `AbP` at every node of the path; `abPH`: its proof.
- `AbHAgree`, `abHAgree`, `abHAgreeW`: the agreement at every node of the
  path from where `ownG` picks the instance there.

**Where this differs from AArch64** (as `X64WakeOwnGAbT`'s threads path):
the return address is the region's word at offset `8` (`slot 8`, `RaOK`),
not `x30`, so `abPH` discharges `RaOK`, `R.Off 8` and `slot 8 = ra` at every
pc of the path from the region's bounds and the nodes' invariants; no `hal`
(the band is `[-32, 8]`, the region `[-24, 16)` at least: `abPH`'s `hlo`,
`hhi`; A64's `[-48, 0)`); the stub's `leaq` is one node (`sn1`, A64's
`sn1`/`sn1b`), so `AbPH` has 11 fields, the `write` call's node `ssvc` at
`NT .sys`; `ownG` reads the two return points `.Lscc_rt_alloc_tcb.x0` and
`.Lwc_main.x5` on the path (A64's `.sp13`, `.sp11`: `abHAgreeW`'s `h5`,
`h23`). `abH_labs` resolves only the two labels `ab_labs` lacks; the path's
phase check at `phW` (A64's `abortHTabW`, `abortPhHW`) is not restated here.
-/
import Spike.Lib.X64WakeOwnGAbT
import Spike.Lib.X64AbortHeapRW

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf nextPc abi privLoad)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SpAt)
open Spike.Lib.X64 (ND BlkW NodeW At SO SI Abs arun cellOff okBlk CodeAt)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout}

/-- **The heap stub's entry and exit labels**, resolved at the canonical
base. -/
theorem abH_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".Lscc_rt_abort_heap.entry" = Int64.ofNat 4202709 ∧
    L.lab "scc_rt_abort_heap_exit" = Int64.ofNat 4202761 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **`AbP` at every node of the heap abort path**: the dispatcher's blocks
at code 2 and the heap stub's nodes, in the dispatcher's region `R`
(`Abort.Disp.HPathW`'s obligations). -/
structure AbPH (L : RuntimeLayout) (μ : Scc.Sem.Marks) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t2) Abort.Disp.t2
  dg2 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .g2) Abort.Disp.g2
  se : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .e) Abort.x0
  sn1 : NodeW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n1)
  sn2 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n2) Abort.x1Heap
  ssvc : NodeW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .sys)
  sn5 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n5) Abort.x2
  sex : NodeW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .ex)

/-- The abstract run's simp set over the path's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly, Spike.Lib.X64.AI.so,
    Spike.Lib.X64.soReg, Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write,
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
local macro "abh_blk " cd:term:max ok:ident b:ident : tactic =>
  `(tactic| (
    refine abP_blk' $cd $ok hR (by omega) (by omega) (by omega) (by omega) hsite ?_ ?_
    · intro k hk
      simp only [$b:ident, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd2R, NT, Abort.pcSys, Abort.heap]
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> simp [cellOff, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
        e11, e12, e13, e14, e15, e16, e17, e18, e19, h1, h2] <;> decide
    · intro σ c hJ k hk
      simp only [$b:ident, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd2R, NT, Abort.JR, Abort.JI, Abort.pcSys, Abort.heap] at hJ ⊢
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> arun_simp <;>
        simp only [RaOK, raSp, raSp8, abFns, abGos, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
          h1, h2, hJ] <;>
        (try split) <;> decide))

set_option hygiene false in
/-- A single-instruction node `nd` of the path: `abP_node` with the
successors from `kp` at its cell `cd` of size `sz`. -/
local macro "abh_node " cd:term:max kp:term:max nd:term:max sz:term:max : tactic =>
  `(tactic| (
    have hP : ∀ p ∈ [($nd).pc, ($nd).pc + Int64.ofNat $sz],
        (L.lab "scc_rt_abort").toBitVec.toNat ≤ p.toBitVec.toNat ∧
          p.toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat := by
      simp only [NT, Abort.pcSys, Abort.heap, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, h1, h2]
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
          NT, Abort.pcSys, Abort.heap, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, h1, h2] <;>
        decide
    · simp only [NT, Abort.JR, Abort.JI] at hJ
      first | exact hJ.2 | exact hJ.1.2))

/-- **`AbP` at every node of the heap abort path**: in the dispatcher's
region `R` (covering its frame `[-24, 16)`, the return address at `8`), the
take site off the path (`hsite`), the code of the dispatcher and of the
heap stub. `RaOK`, the return address word inside `R` and `slot 8 = ra` are
discharged here from the region's bounds and the nodes' invariants. -/
theorem abPH (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {μ : Scc.Sem.Marks}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.heap c0 Abort.x1Heap L.exe endPc) :
    AbPH L μ endPc R F c0 ra := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19⟩ := ab_labs hlab
  obtain ⟨h1, h2⟩ := abH_labs hlab
  have hoff : R.Off 8 := ⟨by omega, by omega, by omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · abh_blk hd.e Abort.Disp.d0_ok Abort.Disp.d0
  · abh_blk hd.t1 Abort.Disp.t1_ok Abort.Disp.t1
  · abh_blk hd.j1 Abort.Disp.j1_ok Abort.Disp.j1
  · abh_blk hd.t2 Abort.Disp.t2_ok Abort.Disp.t2
  · abh_blk hd.g2 Abort.Disp.g2_ok Abort.Disp.g2
  · abh_blk hs.e Abort.x0_ok Abort.x0
  · abh_node hs.n1 keepM_lea (NT L.lab Abort.heap c0 ra .n1) 7
  · abh_blk hs.n2 Abort.x1Heap_ok Abort.x1Heap
  · abh_node hs.sys keepM_sysAt (NT L.lab Abort.heap c0 ra .sys) 2
  · abh_blk hs.n5 Abort.x2_ok Abort.x2
  · abh_node hs.ex keepM_sysAt (NT L.lab Abort.heap c0 ra .ex) 2

/-! ### The agreement -/

/-- **`ownG`'s agreement with `own` at every node of the heap abort path**
(`hag` of `BlkW.ownCongr2` and `SFactsSt2.congr`'s at each of
`Abort.Disp.HPathW`'s obligations). -/
structure AbHAgree (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t2) Abort.Disp.t2
  dg2 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .g2) Abort.Disp.g2
  se : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .e) Abort.x0
  sn1 : NodeW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n1)
  sn2 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n2) Abort.x1Heap
  ssvc : NodeW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .sys)
  sn5 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n5) Abort.x2
  sex : NodeW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .ex)

/-- **The agreement on the heap path from where `ownG` picks `own` on it.** -/
theorem abHAgree {a : BitVec 64} {own : State → List (Loc × Val)} {μ : Scc.Sem.Marks} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} (h : AbPH L μ endPc R F c0 ra)
    (hpick : ∀ s, AbP L R ra s → ownG L a s = own s) : AbHAgree L a own μ endPc R F c0 ra :=
  ⟨BlkW.agree_of h.de hpick, BlkW.agree_of h.dt1 hpick, BlkW.agree_of h.dj1 hpick,
    BlkW.agree_of h.dt2 hpick, BlkW.agree_of h.dg2 hpick, BlkW.agree_of h.se hpick,
    NodeW.agree_of h.sn1 hpick, BlkW.agree_of h.sn2 hpick,
    NodeW.agree_of h.ssvc hpick, BlkW.agree_of h.sn5 hpick, NodeW.agree_of h.sex hpick⟩

/-- **The agreement with `ownW`** on the heap path from a caller other than
the two return points `ownG` reads there (`h5`, `h23`). -/
theorem abHAgreeW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : AbPH L μ endPc R F c0 ra)
    (h5 : ra = (L.lab ".Lscc_rt_alloc_tcb.x0").toBitVec → BandOut L R)
    (h23 : ra ≠ (L.lab ".Lwc_main.x5").toBitVec) :
    AbHAgree L a (fun s => ownW L a (phW (pcOf s))) μ endPc R F c0 ra :=
  abHAgree h fun _ hs => ownG_W hlab (goodW_ab hs h5 h23)

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.abH_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abH_labs

/-- info: 'Spike.Lib.X64.WakePh.abPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abPH

/-- info: 'Spike.Lib.X64.WakePh.abHAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abHAgree

/-- info: 'Spike.Lib.X64.WakePh.abHAgreeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abHAgreeW
