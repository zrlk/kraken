/-
**`scc_rt_print` of a spawning program on AArch64, with the thread rows**: `hello.w`'s `scc_rt_print` (`scc --arch arm -o -
Scc/Test/hello.w`) is `hello1.w`'s (`Spike/Lib/A64Print.lean`) with one
`dmb ish` as the first instruction of `.L9_scc_rt_print.2_write` (and its
dead halt labels renumbered `sp10`/`halt11`, unused here). The blocks are
`A64Print`'s; only the nodes' pcs after `.2_write` move by 4 and the fence
is one more node, `.fence`, at `.2_write` (`dmb_nd`: the row `OutT.fnc`,
the source stutters).

- `PrintF.seg_printF`: the function as one `SegT` segment, from its entry
  to its return or its abort, the `write` system call a given node (as in
  `Print.seg_printW`);
- `PrintF.FA.seg_printFA`: the same against a source that prints byte by
  byte (`PrintA`'s invariants), and `PrintF.FA.hsvc_of_emitT`, its system
  call from the output row (`Out.emit`).
-/
import Spike.Lib.A64WorkerRows
import Spike.Lib.A64PrintCall
import Spike.Lib.LowerA64.NodeTp

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.Flow.Worker.PrintF

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-- The fence block. -/
def bF : List Directive := parseAArch64("dmb ish")

example : bF = [.instr ⟨.W64, .DMB .sy⟩] := by decide

/-! ## The graph -/

/-- The internal nodes: `Print.PN`'s and the fence. -/
inductive PN where
  | e | n1 | loop | n3 | fence | write | svc | n5 | n6 | n7 | chk2 | n9 | n10 | chk3 | n12 | adv | fail | done

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64)

/-- The pc after the system call's argument block (the fence and four
instructions after `.2_write`). -/
abbrev pcSvc : Int64 := lab ".L9_scc_rt_print.2_write" + 4 + 4 + 4 + 4 + 4

/-- **The nodes**: `Print.N`'s, the ones after `.2_write` moved by the
fence. -/
def N : PN → ND
  | .e => Print.N lab c0 x29 ra .e
  | .n1 => Print.N lab c0 x29 ra .n1
  | .loop => Print.N lab c0 x29 ra .loop
  | .n3 => Print.N lab c0 x29 ra .n3
  | .fence => ⟨lab ".L9_scc_rt_print.2_write", Print.oI, Print.JI c0 x29 ra⟩
  | .write => ⟨lab ".L9_scc_rt_print.2_write" + 4, Print.oI, Print.JI c0 x29 ra⟩
  | .svc => ⟨pcSvc lab, Print.oI, fun σ c => Print.JI c0 x29 ra σ c ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64⟩
  | .n5 => ⟨pcSvc lab + 4, Print.oI, Print.JI c0 x29 ra⟩
  | .n6 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, Print.oI, Print.JI c0 x29 ra⟩
  | .n7 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, Print.oI, Print.JI c0 x29 ra⟩
  | .chk2 => Print.N lab c0 x29 ra .chk2
  | .n9 => Print.N lab c0 x29 ra .n9
  | .n10 => Print.N lab c0 x29 ra .n10
  | .chk3 => Print.N lab c0 x29 ra .chk3
  | .n12 => Print.N lab c0 x29 ra .n12
  | .adv => Print.N lab c0 x29 ra .adv
  | .fail => Print.N lab c0 x29 ra .fail
  | .done => Print.N lab c0 x29 ra .done

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .e).pc Print.b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n1).pc Print.b1
  loop : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .loop).pc Print.b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n3).pc Print.b3
  fence : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .fence).pc bF
  write : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .write).pc Print.b4
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n5).pc Print.b5
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n6).pc Print.b6
  n7 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n7).pc Print.b7
  chk2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .chk2).pc Print.b8
  n9 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n9).pc Print.b9
  n10 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n10).pc Print.b10
  chk3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .chk3).pc Print.b11
  n12 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n12).pc Print.b12
  adv : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .adv).pc Print.b13
  fail : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .fail).pc Print.b14
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .done).pc Print.b16
  /-- The `write` system call at `.svc` (a given node of the proof). -/
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .svc).pc [svcDir]

/-- The code does not depend on the ghosts (the nodes' pcs do not). -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c0' : Ctl} {x29 ra x29' ra' : BitVec 64}
    (h : Code c0 x29 ra exe endPc) : Code c0' x29' ra' exe endPc :=
  ⟨h.e, h.n1, h.loop, h.n3, h.fence, h.write, h.n5, h.n6, h.n7, h.chk2, h.n9, h.n10, h.chk3, h.n12, h.adv,
    h.fail, h.done, h.svc⟩

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {x29 ra : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Print.N, Print.JI, Spike.Lib.upd_apply]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, Print.N, Print.E, Print.JI, Spike.Lib.upd_apply]))

/-- **Hello's `scc_rt_print` is one segment with the thread rows** from
its entry to its return or its abort (`Print.E`), for every frame
condition `F` no write inside the frame breaks; the fence is a target-only
step (`OutT.fnc`), the source stutters throughout, and the system call is
a given segment. -/
theorem seg_printF (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hcode : Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hsvc : SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n5))) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .e))
      (fun s c => ∃ x, At exe endPc R F (Print.E (_root_.Executable.labels exe).label c0 x29 ra x) s c) := by
  refine fn_segT (N := N _ c0 x29 ra) (E := Print.E _ c0 x29 ra) (fun i => ?_) PN.e
  cases i
  case svc => exact hsvc.mono_post fun _ _ h => .inl ⟨PN.n5, h⟩
  case e => node Print.b0 Print.b0_ok e; rw [N, Print.N, Print.b0_run]; hit PN.n1
  case n1 => node Print.b1 Print.b1_ok n1; rw [N, Print.N, Print.b1_run]; hit PN.loop
  case loop =>
    node Print.b2 Print.b2_ok loop; rw [N, Print.N, Print.b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => node Print.b3 Print.b3_ok n3; rw [N, Print.N, Print.b3_run]; hit PN.fence
  case fence =>
    refine dmb_nd (fun s he hn => hcode.fence s he hn) fun σ c hJ => ?_
    hit PN.write
  case write => node Print.b4 Print.b4_ok write; rw [N, Print.b4_run]; hit PN.svc
  case n5 => node Print.b5 Print.b5_ok n5; rw [N, Print.b5_run]; hit PN.n6
  case n6 =>
    node Print.b6 Print.b6_ok n6; rw [N, Print.b6_run]
    by_cases hz : σ.status.z = true
    · hit PN.loop
    · hit PN.n7
  case n7 => node Print.b7 Print.b7_ok n7; rw [N, Print.b7_run]; hit PN.chk2
  case chk2 => node Print.b8 Print.b8_ok chk2; rw [N, Print.N, Print.b8_run]; hit PN.n9
  case n9 =>
    node Print.b9 Print.b9_ok n9; rw [N, Print.N, Print.b9_run]
    by_cases hz : σ.status.z = true
    · hit PN.loop
    · hit PN.n10
  case n10 => node Print.b10 Print.b10_ok n10; rw [N, Print.N, Print.b10_run]; hit PN.chk3
  case chk3 =>
    node Print.b11 Print.b11_ok chk3; rw [N, Print.N, Print.b11_run]
    split
    · hit PN.fail
    · hit PN.n12
  case n12 => node Print.b12 Print.b12_ok n12; rw [N, Print.N, Print.b12_run]; hit PN.adv
  case adv => node Print.b13 Print.b13_ok adv; rw [N, Print.N, Print.b13_run]; hit PN.loop
  case fail => node Print.b14 Print.b14_ok fail; rw [N, Print.N, Print.b14_run]; exit Print.PX.abort
  case done => node Print.b16 Print.b16_ok done; rw [N, Print.N, Print.b16_run]; exit Print.PX.ret

end Proof

/-! ## Against a source that prints byte by byte

`PrintA`'s invariants (`Spike/Lib/A64PrintA.lean`) on hello's code: the
same nodes, the ones after `.2_write` moved by the fence, the fence node
`.fence` with `PrintA.JIlt`. -/

/-- Landing at nodes with the thread pointer `tp` (`ND.withTp`): landing
at the nodes, `tpidr_el0` holding `tp`. -/
theorem lands_withTp {ι κ : Sort _} {N : ι → ND} {E : κ → ND} {am : AM} {c : Ctl} {tp : UInt64}
    (ht : am.σ.regs.TPIDR_EL0 = tp) (h : Lands N E am c) :
    Lands (fun j => (N j).withTp tp) (fun x => (E x).withTp tp) am c := by
  rcases h with ⟨j, a, b, d⟩ | ⟨x, a, b, d⟩
  · exact .inl ⟨j, a, b, d, ht⟩
  · exact .inr ⟨x, a, b, d, ht⟩

namespace FA

open Spike.Lib.A64.Print hiding N E JI PN Code pcSvc PrintW
open Spike.Lib.A64.PrintA hiding N E JI pcSvc PrintAW
open Scc.Sem.Kernel (writeRefused results)
open Kraken.Promising.Lower.A64

section Spec

variable (lab : Label → Int64) (x29 ra buf0 : BitVec 64) (len0 : Nat) (P Q : Nat → Ctl → Prop)

/-- **The nodes**: `PrintA.N`'s, the ones after `.2_write` moved by the
fence. -/
def N : PN → ND
  | .e => PrintA.N lab x29 ra buf0 len0 P Q .e
  | .n1 => PrintA.N lab x29 ra buf0 len0 P Q .n1
  | .loop => PrintA.N lab x29 ra buf0 len0 P Q .loop
  | .n3 => PrintA.N lab x29 ra buf0 len0 P Q .n3
  | .fence => ⟨lab ".L9_scc_rt_print.2_write", oI, JIlt x29 ra buf0 len0 P⟩
  | .write => ⟨lab ".L9_scc_rt_print.2_write" + 4, oI, JIlt x29 ra buf0 len0 P⟩
  | .svc => ⟨PrintF.pcSvc lab, oI, fun σ c => JIlt x29 ra buf0 len0 P σ c ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64 ∧
      σ.regs.X1.toBitVec = σ.slot (-48) ∧ σ.regs.X2.toBitVec = σ.slot (-40)⟩
  | .n5 => ⟨PrintF.pcSvc lab + 4, oI, fun σ c => ∃ k, JL x29 ra buf0 len0 k σ ∧ RC0 len0 P Q k σ.regs.X0.toBitVec c⟩
  | .n6 => ⟨PrintF.pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      (∃ k, JL x29 ra buf0 len0 k σ ∧ RC0 len0 P Q k (σ.slot (-32)) c) ∧
        σ.status = StatusFlags.subs (σ.slot (-32) - C4) (σ.slot (-32)) C4⟩
  | .n7 => ⟨PrintF.pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c =>
      ∃ k, JL x29 ra buf0 len0 k σ ∧ RC1 len0 P Q k (σ.slot (-32)) c⟩
  | .chk2 => PrintA.N lab x29 ra buf0 len0 P Q .chk2
  | .n9 => PrintA.N lab x29 ra buf0 len0 P Q .n9
  | .n10 => PrintA.N lab x29 ra buf0 len0 P Q .n10
  | .chk3 => PrintA.N lab x29 ra buf0 len0 P Q .chk3
  | .n12 => PrintA.N lab x29 ra buf0 len0 P Q .n12
  | .adv => PrintA.N lab x29 ra buf0 len0 P Q .adv
  | .fail => PrintA.N lab x29 ra buf0 len0 P Q .fail
  | .done => PrintA.N lab x29 ra buf0 len0 P Q .done

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop} {tp : UInt64}

set_option hygiene false in
/-- A block node with the thread pointer: the block, its `okBlk`, its code;
the source stays, the block keeps `tpidr_el0` (`arun_tpidr`); the edge
(without the thread pointer) is left, the invariant in `hJ`. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| (refine Seg.toT (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJt => ⟨c, .refl c,
      lands_withTp (by rw [arun_tpidr]; exact hJt.2) ?_⟩); have hJ := hJt.1; dsimp only [ND.withTp]))

set_option hygiene false in
/-- Hitting node `j`: the pc and offsets; the invariant is left, unfolded. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> try simp only [N, PrintA.N]) <;> try first | rfl | exact hentry)

/-- Hitting exit `x`: the offsets; the pc and the invariant are left. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> try simp only [PrintA.E]) <;> try rfl)

set_option maxHeartbeats 1000000 in
/-- **Hello's `scc_rt_print` is one segment with the thread rows** against
a source that prints byte by byte (`PrintA.seg_printAW` over `SegT`): the
block nodes and the fence (`OutT.fnc`) keep the source where it is, the
system call (`hsvc`, a given segment) moves it by the count it returns. The
code is `PrintF.Code` (any ghosts). -/
theorem seg_printFA (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hlen : len0 < 2 ^ 63) (hcode : PrintF.Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hsvc : SegT p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5).withTp tp))) :
    SegT p lbl ms (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e).withTp tp))
      (fun s c => ∃ x, At exe endPc R F
        ((PrintA.E (_root_.Executable.labels exe).label x29 ra len0 P Q x).withTp tp) s c) := by
  have hl64 : len0 < 2 ^ 64 := by omega
  refine fn_segT (N := fun i => (N _ x29 ra buf0 len0 P Q i).withTp tp)
    (E := fun x => (PrintA.E _ x29 ra len0 P Q x).withTp tp) (fun i => ?_) PN.e
  cases i
  case svc => exact hsvc.mono_post fun _ _ h => .inl ⟨PN.n5, h⟩
  case e =>
    node Print.b0 Print.b0_ok e; rw [N, PrintA.N, Print.b0_run]; hit PN.n1
    obtain ⟨hP, h29, h30, h0, h1⟩ := hJ
    exact ⟨0, ⟨by simp [Spike.Lib.upd_apply, h29], by simp [Spike.Lib.upd_apply, h30],
      by simp [Spike.Lib.upd_apply, h0], by simp [Spike.Lib.upd_apply, h1], Nat.zero_le _⟩, hP⟩
  case n1 => node Print.b1 Print.b1_ok n1; rw [N, PrintA.N, Print.b1_run]; hit PN.loop; exact hJ
  case loop =>
    node Print.b2 Print.b2_ok loop; rw [N, PrintA.N, Print.b2_run]
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, hP⟩ := hJ
    simp only [subs0_z, h40]
    by_cases hz : k = len0
    · subst hz
      simp only [Nat.sub_self, decide_true, ite_true]
      hit PN.done
      exact ⟨h16, h8, hP⟩
    · have hz' : ¬ BitVec.ofNat 64 (len0 - k) = 0#64 := fun h => hz ((len_zero hl64 hk).1 h)
      simp only [hz', decide_false, Bool.false_eq_true, ite_false]
      hit PN.n3
      exact ⟨k, ⟨h16, h8, h48, h40, hk⟩, by omega, hP⟩
  case n3 => node Print.b3 Print.b3_ok n3; rw [N, PrintA.N, Print.b3_run]; hit PN.fence; exact hJ
  case fence =>
    refine dmb_nd (fun s he hn => hcode.fence s he hn) fun σ c hJt => lands_withTp hJt.2 ?_
    hit PN.write; exact hJt.1
  case write =>
    node Print.b4 Print.b4_ok write; rw [N, Print.b4_run]; hit PN.svc
    refine ⟨hJ, ?_⟩
    simp
  case n5 =>
    node Print.b5 Print.b5_ok n5; rw [N, Print.b5_run]; hit PN.n6
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, hr⟩ := hJ
    refine ⟨⟨k, ⟨?_, ?_, ?_, ?_, hk⟩, ?_⟩, ?_⟩
    · simp [Spike.Lib.upd_apply, h16]
    · simp [Spike.Lib.upd_apply, h8]
    · simp [Spike.Lib.upd_apply, h48]
    · simp [Spike.Lib.upd_apply, h40]
    · simpa [Spike.Lib.upd_apply] using hr
    · simp only [Spike.Lib.upd_apply, ite_true]
  case n6 =>
    node Print.b6 Print.b6_ok n6; rw [N, Print.b6_run]
    obtain ⟨⟨k, hL, hr⟩, hs⟩ := hJ
    simp only [hs, subs_z]
    by_cases hz : σ.slot (-32) = C4
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h11, -⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at h11; exact absurd h11 (by decide)
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C4, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne4 hw)
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      hit PN.n7
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h4, -⟩ | h
      · exact absurd h4 hz
      · exact h
  case n7 => node Print.b7 Print.b7_ok n7; rw [N, Print.b7_run]; hit PN.chk2; exact hJ
  case chk2 =>
    node Print.b8 Print.b8_ok chk2; rw [N, PrintA.N, Print.b8_run]; hit PN.n9
    exact ⟨hJ, trivial⟩
  case n9 =>
    node Print.b9 Print.b9_ok n9; rw [N, PrintA.N, Print.b9_run]
    obtain ⟨⟨k, hL, hr⟩, hs⟩ := hJ
    simp only [hs, subs_z]
    by_cases hz : σ.slot (-32) = C11
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C11, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne11 hw)
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      hit PN.n10
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h11, -⟩ | h
      · exact absurd h11 hz
      · exact h
  case n10 => node Print.b10 Print.b10_ok n10; rw [N, PrintA.N, Print.b10_run]; hit PN.chk3; exact hJ
  case chk3 =>
    node Print.b11 Print.b11_ok chk3; rw [N, PrintA.N, Print.b11_run]
    obtain ⟨k, hL, hr⟩ := hJ
    rcases hr with ⟨h0, hle, hP⟩ | ⟨hw, hQ⟩
    · have hn : ¬ ((StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).z = true ∨
          ¬(StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).n =
            (StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).v) := by
        rw [subs0_le]; exact pos_not_le h0 (by omega)
      simp only [hn, ite_false]
      hit PN.n12
      exact ⟨k, hL, h0, hle, hP⟩
    · have hy : ((StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).z = true ∨
          ¬(StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).n =
            (StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).v) := by
        rw [subs0_le]; exact refused_le hw
      simp only [hy, ite_true]
      hit PN.fail
      exact ⟨k, hQ⟩
  case n12 => node Print.b12 Print.b12_ok n12; rw [N, PrintA.N, Print.b12_run]; hit PN.adv; exact hJ
  case adv =>
    node Print.b13 Print.b13_ok adv; rw [N, PrintA.N, Print.b13_run]; hit PN.loop
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, h0, hle, hP⟩ := hJ
    refine ⟨k + (σ.slot (-32)).toNat, ⟨?_, ?_, ?_, ?_, by omega⟩, hP⟩
    · simp [Spike.Lib.upd_apply, h16]
    · simp [Spike.Lib.upd_apply, h8]
    · simp only [Spike.Lib.upd_apply]; simp only [show (-48 : Int) ≠ -40 by decide, ite_true, ite_false]
      rw [h48, adv_buf]
    · simp only [Spike.Lib.upd_apply, ite_true]; rw [h40, adv_len hl64 hle]
  case fail =>
    node Print.b14 Print.b14_ok fail; rw [N, PrintA.N, Print.b14_run]; exit Print.PX.abort
    exact ⟨by trivial, hJ⟩
  case done =>
    node Print.b16 Print.b16_ok done; rw [N, PrintA.N, Print.b16_run]; exit Print.PX.ret
    · rw [hJ.2.1]
    · exact ⟨hJ.1, hJ.2.1, hJ.2.2⟩

/-- **The write system call from the output row** (`PrintA.hsvc_of_emit`
over `SegT`, the row `Out.emit` with the memory side's byte step `ms.bo`
and abort justification `ms.we`): from `.svc` to `.n5`. -/
theorem hsvc_of_emitT (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).pc [svcDir])
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → ms.bo s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      ∀ k c1, Q k c1 → ms.we s c1) :
    SegT p lbl ms (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5).withTp tp)) := by
  refine SegT.step fun s c hAt => ?_
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨⟨k, hL, hk, hP⟩, h0, h8, h1, h2⟩, htp⟩ := id hAt
  obtain ⟨h16, h8', h48, h40, hkl⟩ := hL
  have hl := hlen k c hP
  have hc : Lower.A64.CellAt s svcDir 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [ND.withTp])
  have hx1 : s.st.1.regs.X1.toNat = (buf0 + BitVec.ofNat 64 k).toNat := by
    rw [hA.regs, ← h48, ← h1]; rfl
  have hx2 : s.st.1.regs.X2.toNat = len0 - k := by
    rw [hA.regs, UInt64.toNat, h2, h40, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.write 1 (buf0 + BitVec.ofNat 64 k).toNat (len0 - k)) := by
    have hr0 : s.st.1.regs.X0 = 1 := by rw [hA.regs]; exact h0
    have hr8 : s.st.1.regs.X8 = 64 := by rw [hA.regs]; exact h8
    simp [Scc.Sem.A64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, hr0, hr8, ← hx1,
      ← hx2]
  refine Out.toT (.emit Scc.Sem.A64.abi _ _ (fun j c1 => P (k + j) c1) (Q k) hK (Scc.Sem.A64.atSvc_of_cellAt hc) hd
    ⟨c, .refl c, hP⟩ (fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h)
    (fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩) (fun c1 h => hwe s c hAt k c1 h))
  · rw [Scc.Sem.A64.abi_ret_of_cellAt hc r]
    have hA' : Flow.Abs R oI { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } }
        (svcStep r σ) := by
      refine Flow.Abs.weaken (o' := oI) (o := oI.kill .X0) (by decide)
        ⟨by simp only [svcStep, hA.regs], hA.status, ?_, hA.slot⟩
      refine hA.so.kill .X0 fun r hr => ?_
      rcases r with y | _
      · cases y <;> first | rfl | exact absurd rfl hr
      · rfl
    have hD' : F { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } } :=
      hF _ _ hD fun _ _ _ => rfl
    refine ⟨he, hn, hdc, ?_, svcStep r σ, hA', hD', ⟨k, ⟨h16, h8', h48, h40, hkl⟩, ?_⟩, htp⟩
    · simp only [svcRet, after, hpc]; rfl
    · have hx0 : (svcStep r σ).regs.X0.toBitVec = r := by simp [svcStep]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
  · subst hj0; exact hPQ k c1 hPj

end Proof

end FA

/-! ## The call -/

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _}
  {N' : ι → ND} {E' : κ → ND}

/-- The callee's nodes for the call state `σC`: `x29`, `x30`, the buffer
`x0` and the count `x1` of `σC`, the source predicates `Pc σC`, `Qc σC`. -/
abbrev cN (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) (i : PN) : ND :=
  (FA.N lab σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC)
    i).withTp σC.regs.TPIDR_EL0

/-- The callee's entry, pinned to the call state `σC` entered at `nC`'s
offset, a realizable one. -/
def cNe (lab : Label → Int64) (Pc Qc : AS → Nat → Ctl → Prop) (nC : ND) (σC : AS) : ND :=
  ⟨(cN lab Pc Qc σC .e).pc, (cN lab Pc Qc σC .e).o, fun σ c =>
    (cN lab Pc Qc σC .e).J σ c ∧ σ = enter nC.o.sp σC ∧ ∃ c0, nC.J σC c0⟩

/-- **A call of hello's `scc_rt_print` with the thread rows**, from any
call node `nC` (pc `scc_rt_print`, `sp` offset 16-aligned with print's 48
bytes inside `R`): `call_ndT` with `seg_printFA`, for any source
predicates `Pc`/`Qc` of the call state. The write system call (`hsvc`) is
asked in every callee region and frame condition, at every realizable
call state (`hsvc_of_emitT` gives it from the output row); the return
(`hret`) and the abort (`habort`) land at the caller's nodes. -/
theorem printF_callT {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pc σ 0 c)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c, nC.J σC c →
      SegT p lbl ms (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .svc))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      σR.regs.TPIDR_EL0 = σC.regs.TPIDR_EL0 → Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp (-48) 0).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N' E' ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → Qc σC k c' →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp (-48) 0).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N' E' ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F nC) (Next exe endPc R F N' E') := by
  refine call_ndT (lo' := -48) (hi' := 0) (Ne := cNe (_root_.Executable.labels exe).label Pc Qc nC)
    (Ex := fun σC x => (PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec σC.regs.X30.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) x).withTp σC.regs.TPIDR_EL0)
    hR hal hF hlo (by decide) hhi (by decide) hk16 (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF σC => ?_) (fun _ => rfl) ?_ ?_
  · by_cases hg : ∃ c0, nC.J σC c0
    · obtain ⟨c0, hJ0⟩ := hg
      refine (FA.seg_printFA hF' hR' hal' hlo' hhi' (hlen σC c0 hJ0) (c0 := c0) (tp := σC.regs.TPIDR_EL0)
        hcode.ghost hentry
        (hsvc R' F' hR' hal' hlo' hhi' hF' hFF σC c0 hJ0)).mono_pre ?_
      rintro s c ⟨a, b, d, e, σ, hA, hD, hJ', -, -⟩
      exact ⟨a, b, d, e, σ, hA, hD, hJ'⟩
    · exact SegT.step fun s c ⟨_, _, _, _, _, _, _, _, _, h⟩ => absurd h hg
  · intro σC c hJ
    exact ⟨σC, by rw [hpc]; rfl, ⟨⟨hP0 σC c hJ, rfl, rfl, rfl, by simp [enter]⟩, rfl⟩, rfl, c, hJ⟩
  · rintro g y σC c σx c' σR hJ ⟨-, he, -⟩ hx hreg - hsl
    obtain rfl : σC = g := enter_inj he
    cases y
    · obtain ⟨⟨h29, h30, hP⟩, htp⟩ := hx
      have h := hret σC c σR c' hJ (by rw [hreg]; exact h29) (by rw [hreg]; exact h30) (by rw [hreg]; exact htp) hP
        hsl
      simpa [PrintA.E, Print.oE, ND.withTp] using h
    · obtain ⟨⟨h4, k, hQ⟩, -⟩ := hx
      exact habort σC c σR c' k hJ (by rw [hreg]; exact h4) hQ hsl

end Call

end Spike.Lib.A64.Flow.Worker.PrintF
