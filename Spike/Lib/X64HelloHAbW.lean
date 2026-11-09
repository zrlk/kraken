/-
**hello.w's heap abort path at `ownGH`** (x86-64; the twin of
`Spike/Lib/A64HelloHAbW.lean`, at the template of
`Spike/Lib/X64WakeHAbW.lean` and `X64WakeHAbWf`'s phase check): wake's
`WakePh.AbPH` (`AbP` at every node of `scc_rt_abort(2)` with the return
address and of `scc_rt_abort_heap`) at hello's labels, `ownGH`'s agreement
with the instance it picks there on every obligation of
`Abort.Disp.HPathW`, and the path's phase check at `phH`. The
program-independent pieces (`WakePh.AbPH`, `AbW`, `abP_blk'`, `abP_node`,
`keepM_lea`, `keepM_sysAt`, `BlkW.agree_of`, `NodeW.agree_of`) are wake's.

- `abH_labsH`: the heap stub's entry and exit labels, resolved in
  `helloCells` (the rest of the path's are `ab_labsH`').
- `abPHH`: `AbPH` at hello's labels.
- `AbHAgreeH`, `abHAgreeH`, `abHAgreeWH`: the agreement at every node of the
  path from where `ownGH` picks the instance there (`ownH` from a caller
  other than `.Lscc_rt_alloc_tcb.x0` on a pool stack and `.Lwc_main.x5`).
- `abortHTabH`, `abortHFactsH`, `abortPhHH`: `abortPhHeapOk` at `phH`.

**Deviation from the A64 file.** As in `X64WakeHAbW`: the return address is
the region's word at offset `8`, so `abPHH` discharges `RaOK`, `R.Off 8`
and `slot 8 = ra` from the region's bounds (`[-24, 16)` at least, no
`hal`); the stub's `leaq` is one node, so `AbPH`/`AbHAgreeH` have 11 fields
(A64: 12); the `write` call's node is `ssvc` at `NT .sys`. `abH_labsH`
resolves only the two labels `ab_labsH` lacks (A64's also resolves the
sites and return points, which no x86-64 consumer reads). The table's
exit-call phase equation is decided on the resolved exit label (A64's two
`.ph` facts), as `X64WakeHAbWf.abortPhHW`.
-/
import Spike.Lib.X64HelloOwnGAbT
import Spike.Lib.X64WakeHAbW

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq PhFact factOk deadN okPcOf)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (BlkW NodeW SO)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN)
open Spike.Lib.X64.WakePh (AbP AbPH BandOut RaOK raSp raSp8 abFns abGos abP_blk' abP_node ns_of raOK_bp keep_pc
  keepM_lea keepM_sysAt BlkW.agree_of NodeW.agree_of)
open Spike.Lib.X64.StubW (abortPhHeapOk phOne)
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout}

/-- **The heap stub's entry and exit labels**, resolved at hello's base. -/
theorem abH_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".Lscc_rt_abort_heap.entry" = Int64.ofNat 4202746 ∧
    L.lab "scc_rt_abort_heap_exit" = Int64.ofNat 4202798 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- The abstract run's simp set over the path's blocks
(`Spike/Lib/X64WakeHAbW.lean`'s). -/
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
local macro "abh_blk " cd:term:max ok:ident b:ident : tactic =>
  `(tactic| (
    refine abP_blk' $cd $ok hR (by omega) (by omega) (by omega) (by omega) hsite ?_ ?_
    · intro k hk
      simp only [$b:ident, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd2R, NT, Abort.pcSys, Abort.heap]
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> simp [Spike.Lib.X64.cellOff, e1, e2, e3, e4, e5, e6, e7, e8,
        e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, h1, h2] <;> decide
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

/-- **`AbP` at every node of the heap abort path** at hello's labels: in the
dispatcher's region `R` (covering its frame `[-24, 16)`, the return address
at `8`), the take site off the path (`hsite`), the code of the dispatcher
and of the heap stub. -/
theorem abPHH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {μ : Scc.Sem.Marks}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.heap c0 Abort.x1Heap L.exe endPc) :
    AbPH L μ endPc R F c0 ra := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19⟩ := ab_labsH hlab
  obtain ⟨h1, h2⟩ := abH_labsH hlab
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

/-- **`ownGH`'s agreement with `own` at every node of the heap abort path**
(`hag` of `BlkW.ownCongr2` and `SFactsSt2.congr`'s at each of
`Abort.Disp.HPathW`'s obligations). -/
structure AbHAgreeH (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .t2) Abort.Disp.t2
  dg2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd2R L.lab c0 ra .g2) Abort.Disp.g2
  se : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .e) Abort.x0
  sn1 : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n1)
  sn2 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n2) Abort.x1Heap
  ssvc : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .sys)
  sn5 : BlkW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .n5) Abort.x2
  sex : NodeW (AgWH L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.heap c0 ra .ex)

/-- **The agreement on the heap path from where `ownGH` picks `own` on it.** -/
theorem abHAgreeH {a : BitVec 64} {own : State → List (Loc × Val)} {μ : Scc.Sem.Marks} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} (h : AbPH L μ endPc R F c0 ra)
    (hpick : ∀ s, AbP L R ra s → ownGH L a s = own s) : AbHAgreeH L a own μ endPc R F c0 ra :=
  ⟨BlkW.agree_of h.de hpick, BlkW.agree_of h.dt1 hpick, BlkW.agree_of h.dj1 hpick,
    BlkW.agree_of h.dt2 hpick, BlkW.agree_of h.dg2 hpick, BlkW.agree_of h.se hpick,
    NodeW.agree_of h.sn1 hpick, BlkW.agree_of h.sn2 hpick,
    NodeW.agree_of h.ssvc hpick, BlkW.agree_of h.sn5 hpick, NodeW.agree_of h.sex hpick⟩

/-- **The agreement with `ownH`** on the heap path from a caller other than
the two return points `ownGH` reads there (`h6`, `h27`). -/
theorem abHAgreeWH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {a : BitVec 64} {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {ra : BitVec 64} (h : AbPH L μ endPc R F c0 ra)
    (h6 : ra = (L.lab ".Lscc_rt_alloc_tcb.x0").toBitVec → BandOut L R)
    (h27 : ra ≠ (L.lab ".Lwc_main.x5").toBitVec) :
    AbHAgreeH L a (fun s => ownH L a (phH (pcOf s))) μ endPc R F c0 ra :=
  abHAgreeH h fun _ hs => ownGH_W hlab (goodWH_ab hs h6 h27)

/-! ### The heap abort path's phase check at `phH` -/

/-- **The heap abort path's facts** (`abortPhHeapOk`'s but the exit
call's), as the certificate's table. -/
def abortHTabH : List PhFact :=
  [.blk "scc_rt_abort" 0 Abort.Disp.d0 none none, .blk ".Lscc_rt_abort.entry" 0 Abort.Disp.t1 none none,
   .blk ".Lscc_rt_abort.entry" 16 Abort.Disp.j1 none none,
   .blk ".Lscc_rt_abort.next1" 0 Abort.Disp.t2 none none,
   .blk ".Lscc_rt_abort.is2" 0 Abort.Disp.g2 none none, .blk "scc_rt_abort_heap" 0 Abort.x0 none none,
   .step ".Lscc_rt_abort_heap.entry" 0 7, .blk ".Lscc_rt_abort_heap.entry" 7 Abort.x1Heap none none,
   .step ".Lscc_rt_abort_heap.entry" 34 2, .blk ".Lscc_rt_abort_heap.entry" 36 Abort.x2 none none]

/-- The table's facts hold at the resolved phases. -/
theorem abortHFactsH : abortHTabH.all (factOk (codeT lo helloCells) okC phC) = true := by
  decide +kernel

/-- **`abortPhHeapOk` at `phH`** with the certificate's labels. -/
theorem abortPhHH {Λ : Scc.Sem.Layout} {lab : Label → Int64} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → lab l = Int64.ofNat x) :
    abortPhHeapOk (okPcOf lo helloCells Λ) phH lab = true := by
  have h := abortHFactsH
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at h
  simp only [abortHTabH, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = lab r + Int64.ofNat o' :=
    fun _ _ h => by cases h
  have hn : ∀ t, deadN (codeLabel lo helloCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [deadN] at h
  have so : ∀ {l : String} {o z : Nat},
      factOk (codeLabel lo helloCells) (okPcOf lo helloCells Λ) phH (.step l o z) = true →
      phOne (okPcOf lo helloCells Λ) phH (lab l + Int64.ofNat o) z = true := fun h => by
    obtain ⟨h1, h2⟩ := step_of_factOk hlab h
    simp only [phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have hex : lab "scc_rt_abort_heap_exit" = Int64.ofNat 4202798 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold abortPhHeapOk
  simp only [Abort.heap]
  rw [blkPh_of_factOk hlab hr hn f0, blkPh_of_factOk hlab hr hn f1, blkPh_of_factOk hlab hr hn f2,
    blkPh_of_factOk hlab hr hn f3, blkPh_of_factOk hlab hr hn f4, blkPh_of_factOk hlab hr hn f5, so f6,
    blkPh_of_factOk hlab hr hn f7, so f8, blkPh_of_factOk hlab hr hn f9, hex, phH_eq]
  decide +kernel

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.abH_labsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abH_labsH

/-- info: 'Spike.Lib.X64.HelloPh.abPHH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abPHH

/-- info: 'Spike.Lib.X64.HelloPh.abHAgreeWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abHAgreeWH

/-- info: 'Spike.Lib.X64.HelloPh.abortPhHH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.abortPhHH
