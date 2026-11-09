/-
**wake.w's global owned-words map on the threads abort path, node by node**
(x86-64; the twin of `Spike/Lib/A64WakeOwnGAbT.lean`): `AbP`
(`Spike/Lib/X64WakeOwnGAb.lean`) at every state of each node of
`scc_rt_abort(5)` (`Abort.Disp.DN.nd5`) and `scc_rt_abort_threads`
(`Abort.NT`) and at its successors, in the dispatcher's region; hence
`ownG`'s agreement with the instance it picks there on every obligation of
`Abort.Disp.StubTW` (`AbAgree`, `abAgree`).

- `ab_labs`: the path's labels (and the other stubs' and taken tests', which
  `raSp` reads), resolved.
- `abP_blk'`: `abP_blk` with the take site off the path, the region's word
  at offset `8` from its bounds.
- `keepM_lea`: the successors of the stub's `leaq` keep `%rsp`, `%rbp` and
  the private memory.
- `AbPT`: `AbP` at every node of the path; `abPT`: its proof.
- `AbAgree`, `abAgree`: the agreement at every node of the path from where
  `ownG` picks the instance there.

**Unlike AArch64**: the return address is the region's word at offset `8`
(`slot 8`, `RaOK`), not `x30`, so `abPT` discharges `RaOK`, `R.Off 8` and
`slot 8 = ra` at every pc of the path (from the region's bounds and the
nodes' invariants) instead of `x30`'s value; no `hal` (the band is
`[-32, 8]`, the region `[-24, 16)` at least, `abPT`'s `hlo`, `hhi`); the
stub's `leaq` is one node (`sn1`, A64's `sn1`/`sn1b` for `adrp`/`add`), so
`AbPT` has 17 fields; the `write` call's node is `ssvc` at `NT .sys`.
-/
import Spike.Lib.X64WakeOwnGAb
import Spike.Lib.X64AbortThreadsW

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

/-- **The threads abort path's labels**, resolved at the canonical base,
with the other stubs' and the taken tests' (`raSp`, `raSp8`). -/
theorem ab_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_abort" = Int64.ofNat 4202487 ∧ L.lab "scc_rt_thr_worker" = Int64.ofNat 4202973 ∧
    L.lab ".Lscc_rt_abort.entry" = Int64.ofNat 4202499 ∧
    L.lab ".Lscc_rt_abort.is0" = Int64.ofNat 4202517 ∧
    L.lab ".Lscc_rt_abort.next1" = Int64.ofNat 4202523 ∧
    L.lab ".Lscc_rt_abort.is2" = Int64.ofNat 4202541 ∧
    L.lab ".Lscc_rt_abort.next3" = Int64.ofNat 4202550 ∧
    L.lab ".Lscc_rt_abort.is4" = Int64.ofNat 4202568 ∧
    L.lab ".Lscc_rt_abort.next5" = Int64.ofNat 4202577 ∧
    L.lab ".Lscc_rt_abort.is6" = Int64.ofNat 4202595 ∧
    L.lab ".Lscc_rt_abort.next7" = Int64.ofNat 4202604 ∧
    L.lab ".Lscc_rt_abort.is8" = Int64.ofNat 4202622 ∧
    L.lab "scc_rt_abort_overflow" = Int64.ofNat 4202633 ∧
    L.lab "scc_rt_abort_heap" = Int64.ofNat 4202701 ∧
    L.lab "scc_rt_abort_stack" = Int64.ofNat 4202769 ∧
    L.lab "scc_rt_abort_write" = Int64.ofNat 4202837 ∧
    L.lab "scc_rt_abort_threads" = Int64.ofNat 4202905 ∧
    L.lab ".Lscc_rt_abort_threads.entry" = Int64.ofNat 4202913 ∧
    L.lab "scc_rt_abort_threads_exit" = Int64.ofNat 4202965 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_,
    hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;>
    (rw [← codeT_eq]; decide +kernel)

/-- **The take site off a pc of the path.** -/
theorem ns_of {μ : Scc.Sem.Marks} {s : State} {p : Int64}
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hp : s.st.2 = p)
    (hr : (L.lab "scc_rt_abort").toBitVec.toNat ≤ p.toBitVec.toNat ∧
      p.toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat) :
    ∀ a, μ.site .take = some a → pcOf s ≠ a := by
  intro a ha he
  have h1 : pcOf s = p.toBitVec.toNat := by show s.st.2.toBitVec.toNat = _; rw [hp]
  have := hsite a ha
  omega

/-- **`RaOK` off the `raSp`, `raSp8` pcs**: `%rbp` at the frame base. -/
theorem raOK_bp {p : Int64} {o : SO} (h1 : p.toBitVec.toNat ∉ raSp L) (h2 : p.toBitVec.toNat ∉ raSp8 L)
    (h3 : o.get .rbp = some 0) : RaOK L p o :=
  ⟨fun h => absurd h h1, fun _ h => absurd h h2, fun _ _ => h3⟩

section Blk

variable {μ : Scc.Sem.Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int} {ra : BitVec 64}

/-- **`abP_blk` with the take site off the path** (`hsite`), the block's
pcs on it (`hpc0`), the return address word inside the region (`hlo8`,
`hhi8`). -/
theorem abP_blk'
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hlo8 : R.lo ≤ 8) (hhi8 : 16 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hpc0 : ∀ k < blk.length,
      (L.lab "scc_rt_abort").toBitVec.toNat ≤ (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ∧
      (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat < (L.lab "scc_rt_thr_worker").toBitVec.toNat)
    (hfx : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      ((L.lab "scc_rt_abort").toBitVec.toNat ≤
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat <
          (L.lab "scc_rt_thr_worker").toBitVec.toNat) ∧
      RaOK L (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so ∧
      (-32 ≤ (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ≤ 8) ∧
      (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot 8 = ra) :
    BlkW (fun s _ => AbP L R ra s ∧ ∀ s', StSucc μ s s' → AbP L R ra s') (fun _ _ => False)
      exe endPc R F n blk := by
  refine abP_blk hcode hok hR hlo hhi ⟨by omega, hlo8, by omega⟩ ?_ (fun σ c h k hk => (hfx σ c h k hk).1)
    (fun σ c h k hk => (hfx σ c h k hk).2.1) (fun σ c h k hk => (hfx σ c h k hk).2.2.1)
    (fun σ c h k hk => (hfx σ c h k hk).2.2.2)
  intro a ha k hk he
  have hp := hpc0 k hk
  rw [he] at hp
  have := hsite a ha
  omega

end Blk

/-! ### The successors of the single-instruction nodes -/

section Keep

variable {μ : Scc.Sem.Marks} {s : State}

/-- **`leaq L(%rip), %rax`'s successors off the take site keep `%rsp`,
`%rbp` and the private memory.** -/
theorem keepM_lea {L' : Label} {z : Nat}
    (hc : Kraken.Promising.Lower.X64.CellAt s (SI.leaRip .rax L').toDir z)
    (hns : ∀ a, μ.site .take = some a → pcOf s ≠ a) {s' : State} (h : StSucc μ s s') :
    Keep s s' ∧ s'.st.1.dmem = s.st.1.dmem := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨a, ha, hpc, -⟩
  · rw [Spike.Lib.X64.exec_si hc] at htr
    cases htr; cases hl
    exact ⟨⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩, rfl⟩
  · rw [hs] at hs'; cases hs'
  · exact absurd hpc (hns a ha)

/-- **A `syscall` cell's successors off the take site keep `%rsp`, `%rbp`
and the private memory.** -/
theorem keepM_sysAt {z : Nat} (hc : Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 .syscall) z)
    (hns : ∀ a, μ.site .take = some a → pcOf s ≠ a) {s' : State} (h : StSucc μ s s') :
    Keep s s' ∧ s'.st.1.dmem = s.st.1.dmem :=
  keepM_syscall (Scc.Sem.X64.atSyscall_of_cellAt hc) hns h

end Keep

/-! ### `AbP` at every node of the path -/

/-- **`AbP` at a state and its successors.** -/
def AbW (L : RuntimeLayout) (R : Region) (ra : BitVec 64) (μ : Scc.Sem.Marks) : Frag isa :=
  fun s _ => AbP L R ra s ∧ ∀ s', StSucc μ s s' → AbP L R ra s'

/-- **`AbP` at every node of the threads abort path**: the dispatcher's
blocks at code 5 and the threads stub's nodes, in the dispatcher's region
`R` (`Abort.Disp.StubTW`'s obligations, the `write` call's node `ssvc`
added). -/
structure AbPT (L : RuntimeLayout) (μ : Scc.Sem.Marks) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t2) Abort.Disp.t2
  dj2 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j2) Abort.Disp.j2
  dt3 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t3) Abort.Disp.t3
  dj3 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j3) Abort.Disp.j3
  dt4 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t4) Abort.Disp.t4
  dj4 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j4) Abort.Disp.j4
  dt5 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t5) Abort.Disp.t5
  dg5 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .g5) Abort.Disp.g5
  se : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .e) Abort.x0
  sn1 : NodeW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n1)
  sn2 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n2) Abort.x1Threads
  ssvc : NodeW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .sys)
  sn5 : BlkW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n5) Abort.x2
  sex : NodeW (AbW L R ra μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .ex)

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
local macro "ab_blk " cd:term:max ok:ident b:ident : tactic =>
  `(tactic| (
    refine abP_blk' $cd $ok hR (by omega) (by omega) (by omega) (by omega) hsite ?_ ?_
    · intro k hk
      simp only [$b:ident, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
      simp only [DN.nd5, NT, Abort.pcSys, Abort.threads]
      rcases k with _|_|_|_|_|_|k <;> (try omega) <;> simp [cellOff, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
        e11, e12, e13, e14, e15, e16, e17, e18, e19] <;> decide
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

/-- **`AbP` at every node of the threads abort path**: in the dispatcher's
region `R` (covering its frame `[-24, 16)`, the return address at `8`), the
take site off the path (`hsite`), the code of the dispatcher and of the
threads stub. `RaOK`, the return address word inside `R` and `slot 8 = ra`
are discharged here from the region's bounds and the nodes' invariants. -/
theorem abPT (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {μ : Scc.Sem.Marks}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hsite : ∀ a, μ.site .take = some a →
      a < (L.lab "scc_rt_abort").toBitVec.toNat ∨ (L.lab "scc_rt_thr_worker").toBitVec.toNat ≤ a)
    (hd : Abort.Disp.Code c0 L.exe endPc) (hs : Abort.Code Abort.threads c0 Abort.x1Threads L.exe endPc) :
    AbPT L μ endPc R F c0 ra := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19⟩ := ab_labs hlab
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

/-- **`ownG` agrees with `own` at a state and its successors.** -/
def AgW (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks) : Frag isa :=
  fun s _ => ownG L a s = own s ∧ ∀ s', StSucc μ s s' → ownG L a s' = own s'

/-- **`ownG`'s agreement with `own` at every node of the threads abort
path** (`hag` of `BlkW.ownCongr2` and `SFactsSt2.congr`'s at each of
`Abort.Disp.StubTW`'s obligations and the `write` call's node). -/
structure AbAgree (L : RuntimeLayout) (a : BitVec 64) (own : State → List (Loc × Val)) (μ : Scc.Sem.Marks)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ra : BitVec 64) : Prop where
  de : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .e) Abort.Disp.d0
  dt1 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t1) Abort.Disp.t1
  dj1 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j1) Abort.Disp.j1
  dt2 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t2) Abort.Disp.t2
  dj2 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j2) Abort.Disp.j2
  dt3 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t3) Abort.Disp.t3
  dj3 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j3) Abort.Disp.j3
  dt4 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t4) Abort.Disp.t4
  dj4 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .j4) Abort.Disp.j4
  dt5 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .t5) Abort.Disp.t5
  dg5 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (DN.nd5 L.lab c0 ra .g5) Abort.Disp.g5
  se : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .e) Abort.x0
  sn1 : NodeW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n1)
  sn2 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n2) Abort.x1Threads
  ssvc : NodeW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .sys)
  sn5 : BlkW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .n5) Abort.x2
  sex : NodeW (AgW L a own μ) (fun _ _ => False) L.exe endPc R F (NT L.lab Abort.threads c0 ra .ex)

/-- **The agreement on the path from where `ownG` picks `own` on it**
(`hpick`: `good2a_ab`, `good2b_ab` or `goodW_ab` with `ownG_2a`, `ownG_2b`,
`ownG_W`). -/
theorem abAgree {a : BitVec 64} {own : State → List (Loc × Val)} {μ : Scc.Sem.Marks} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} (h : AbPT L μ endPc R F c0 ra)
    (hpick : ∀ s, AbP L R ra s → ownG L a s = own s) : AbAgree L a own μ endPc R F c0 ra :=
  ⟨BlkW.agree_of h.de hpick, BlkW.agree_of h.dt1 hpick, BlkW.agree_of h.dj1 hpick,
    BlkW.agree_of h.dt2 hpick, BlkW.agree_of h.dj2 hpick, BlkW.agree_of h.dt3 hpick,
    BlkW.agree_of h.dj3 hpick, BlkW.agree_of h.dt4 hpick, BlkW.agree_of h.dj4 hpick,
    BlkW.agree_of h.dt5 hpick, BlkW.agree_of h.dg5 hpick, BlkW.agree_of h.se hpick,
    NodeW.agree_of h.sn1 hpick, BlkW.agree_of h.sn2 hpick,
    NodeW.agree_of h.ssvc hpick, BlkW.agree_of h.sn5 hpick, NodeW.agree_of h.sex hpick⟩

/-- **The agreement with `own2a`** on the path from `scc_rt_alloc_tcb`'s
abort on a pool stack. -/
theorem abAgree2a (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (h : AbPT L μ endPc R F c0 (L.lab ".Lscc_rt_alloc_tcb.x0").toBitVec) (hb : BandIn L R) :
    AbAgree L a (fun s => own2a L a (ph2a (pcOf s))) μ endPc R F c0 (L.lab ".Lscc_rt_alloc_tcb.x0").toBitVec :=
  abAgree h fun _ hs => ownG_2a hlab (good2a_ab hs hb)

/-- **The agreement with `own2b`** on the path from `wc_main`'s spawn
failure. -/
theorem abAgree2b (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    (h : AbPT L μ endPc R F c0 (L.lab ".Lwc_main.x5").toBitVec) :
    AbAgree L a (fun s => own2b L a (ph2b (pcOf s))) μ endPc R F c0 (L.lab ".Lwc_main.x5").toBitVec :=
  abAgree h fun _ hs => ownG_2b hlab (good2b_ab hlab hs)

/-- **The agreement with `ownW`** on the path from any other caller, or from
`scc_rt_alloc_tcb`'s abort off the pool stacks. -/
theorem abAgreeW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {a : BitVec 64}
    {μ : Scc.Sem.Marks} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : AbPT L μ endPc R F c0 ra)
    (h5 : ra = (L.lab ".Lscc_rt_alloc_tcb.x0").toBitVec → BandOut L R)
    (h23 : ra ≠ (L.lab ".Lwc_main.x5").toBitVec) :
    AbAgree L a (fun s => ownW L a (phW (pcOf s))) μ endPc R F c0 ra :=
  abAgree h fun _ hs => ownG_W hlab (goodW_ab hs h5 h23)

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ab_labs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ab_labs

/-- info: 'Spike.Lib.X64.WakePh.ns_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ns_of

/-- info: 'Spike.Lib.X64.WakePh.raOK_bp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.raOK_bp

/-- info: 'Spike.Lib.X64.WakePh.abP_blk'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abP_blk'

/-- info: 'Spike.Lib.X64.WakePh.keepM_lea' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keepM_lea

/-- info: 'Spike.Lib.X64.WakePh.keepM_sysAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keepM_sysAt

/-- info: 'Spike.Lib.X64.WakePh.abPT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abPT

/-- info: 'Spike.Lib.X64.WakePh.abAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abAgree

/-- info: 'Spike.Lib.X64.WakePh.abAgree2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abAgree2a

/-- info: 'Spike.Lib.X64.WakePh.abAgree2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abAgree2b

/-- info: 'Spike.Lib.X64.WakePh.abAgreeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abAgreeW
