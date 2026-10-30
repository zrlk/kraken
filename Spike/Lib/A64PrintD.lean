/-
**`scc_rt_print` with the fenced write on AArch64**: every AArch64 program's
`scc_rt_print` (`Runtime.printF`) has the barrier `dmb ish` (`Print.bF`) as
the first instruction of `.L9_scc_rt_print.2_write`; its other blocks are
`Spike/Lib/A64Print.lean`'s, the ones after `.2_write` one instruction on.
The function is one `Seg` as `Print.seg_print`, with one more node, the
barrier (`PN.fence`, at `.2_write`), whose row is `Out.fence` (the source
stutters).

- `dmb_ndW`, `dmb_nd`: **a node at a fence** `dmb <opt>`: the abstract
  state and the source's control unchanged, landing at `pc + 4`.
- `N`, `E`, `Code`, `PrintW`: the graph, the code and the obligations of
  `Print`'s, with the barrier's node.
- `seg_printW`, `seg_print`: the function as one segment, the `write`
  system call a given node.
-/
import Spike.Lib.A64Print

namespace Spike.Lib.A64.PrintD

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
  Spike.Lib.A64.Flow Spike.Lib.A64.Print

/-! ## A node at a fence -/

section Fence

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a fence** `dmb <opt>` inside `W`: the abstract state and the
source's control are unchanged (`Out.fence`, the source stutters), landing
at `pc + 4`. Its states lie in `W` and no outside move `K` moves them. -/
theorem dmb_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .DMB k⟩])
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ σ c, n.J σ c → Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨.W64, .DMB k⟩) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  refine .fence k _ c (exec_dmb hc) (.loc (.refl c)) ?_
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1]
  rcases hedge σ c hJ with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hA hD⟩
  · exact .inr ⟨y, hy.at he hn hdc hA hD⟩

/-- **A node at a fence** (`dmb_ndW` inside the trivial predicate, with no
outside moves). -/
theorem dmb_nd {n : ND} {k : FenceKind}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨.W64, .DMB k⟩])
    (hedge : ∀ σ c, n.J σ c → Lands N E ⟨n.pc + Int64.ofNat 4, n.o, σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (dmb_ndW (W := fun _ _ => True) (K := fun _ _ => False) hcode NodeW.triv hedge).toSeg

end Fence

/-! ## The graph -/

/-- The internal nodes: `Print.PN`'s and the barrier. -/
inductive PN where
  | e | n1 | loop | n3 | fence | write | svc | n5 | n6 | n7 | chk2 | n9 | n10 | chk3 | n12 | adv | fail | done

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64)

/-- The pc after the system call's argument block (the barrier and four
instructions after `.2_write`). -/
abbrev pcSvc : Int64 := lab ".L9_scc_rt_print.2_write" + 4 + 4 + 4 + 4 + 4

/-- **The nodes**: `Print.N`'s, the barrier at `.2_write` and the ones after
it one instruction on. -/
def N : PN → ND
  | .e => Print.N lab c0 x29 ra .e
  | .n1 => Print.N lab c0 x29 ra .n1
  | .loop => Print.N lab c0 x29 ra .loop
  | .n3 => Print.N lab c0 x29 ra .n3
  | .fence => ⟨lab ".L9_scc_rt_print.2_write", oI, JI c0 x29 ra⟩
  | .write => ⟨lab ".L9_scc_rt_print.2_write" + 4, oI, JI c0 x29 ra⟩
  | .svc => ⟨pcSvc lab, oI, fun σ c => JI c0 x29 ra σ c ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64⟩
  | .n5 => ⟨pcSvc lab + 4, oI, JI c0 x29 ra⟩
  | .n6 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .n7 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .chk2 => Print.N lab c0 x29 ra .chk2
  | .n9 => Print.N lab c0 x29 ra .n9
  | .n10 => Print.N lab c0 x29 ra .n10
  | .chk3 => Print.N lab c0 x29 ra .chk3
  | .n12 => Print.N lab c0 x29 ra .n12
  | .adv => Print.N lab c0 x29 ra .adv
  | .fail => Print.N lab c0 x29 ra .fail
  | .done => Print.N lab c0 x29 ra .done

/-- **The exits**: `Print.E`'s. -/
abbrev E : PX → ND := Print.E lab c0 x29 ra

/-- **The code**: every block at its node's pc, the barrier at `.fence`. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n1).pc b1
  loop : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .loop).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n3).pc b3
  fence : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .fence).pc bF
  write : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .write).pc b4
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n5).pc b5
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n6).pc b6
  n7 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n7).pc b7
  chk2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .chk2).pc b8
  n9 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n9).pc b9
  n10 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n10).pc b10
  chk3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .chk3).pc b11
  n12 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n12).pc b12
  adv : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .adv).pc b13
  fail : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .fail).pc b14
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .done).pc b16
  /-- The `write` system call at `.svc` (a given node of the proof, so
  unused by it; its consumers read the instruction there). -/
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .svc).pc [svcDir]

/-- **The function's states inside `W`**, none moved by `K`: one obligation
per block node and the barrier's (the system call is a given node). -/
structure PrintW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .e) b0
  n1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n1) b1
  loop : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .loop) b2
  n3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n3) b3
  fence : NodeW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .fence)
  write : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .write) b4
  n5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n5) b5
  n6 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n6) b6
  n7 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n7) b7
  chk2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .chk2) b8
  n9 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n9) b9
  n10 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n10) b10
  chk3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .chk3) b11
  n12 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n12) b12
  adv : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .adv) b13
  fail : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .fail) b14
  done : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .done) b16

/-- The function is inside the trivial predicate, with no outside moves. -/
theorem PrintW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    PrintW c0 x29 ra (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, NodeW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv⟩

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {x29 ra : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code, its `W` obligation; the
edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) hW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- Hitting node `j`: the pc, offsets and invariant, by `simp` and `decide`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Print.N, JI, upd_apply]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, Print.N, E, Print.E, JI, upd_apply]))

/-- **`scc_rt_print` with the fenced write is one segment inside `W`** from
its entry to its return or its abort, for every frame condition `F` no
write inside the frame breaks: its block nodes' and the barrier's states lie
in `W`, none moved by `K` (`hW`), and the system call is a given segment
inside `W`. (`seg_print` is the frame condition `DFrame R m0`.) -/
theorem seg_printW {W : Frag isaLSE2} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hW : PrintW c0 x29 ra W K exe endPc R F)
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label c0 x29 ra x) s c) := by
  refine fn_segW (N := N _ c0 x29 ra) (E := E _ c0 x29 ra) (fun i => ?_) PN.e
  cases i
  case svc => exact seg_givenW PN.n5 hsvc
  case fence =>
    refine dmb_ndW (k := .sy) (fun s he hn => hcode.fence s he hn) hW.fence fun σ c hJ => ?_
    hit PN.write
  case e => node b0 b0_ok e; rw [N, Print.N, b0_run]; hit PN.n1
  case n1 => node b1 b1_ok n1; rw [N, Print.N, b1_run]; hit PN.loop
  case loop =>
    node b2 b2_ok loop; rw [N, Print.N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => node b3 b3_ok n3; rw [N, Print.N, b3_run]; hit PN.fence
  case write => node b4 b4_ok write; rw [N, b4_run]; hit PN.svc
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; hit PN.n6
  case n6 =>
    node b6 b6_ok n6; rw [N, b6_run]
    by_cases hz : σ.status.z = true
    · hit PN.loop
    · hit PN.n7
  case n7 => node b7 b7_ok n7; rw [N, b7_run]; hit PN.chk2
  case chk2 => node b8 b8_ok chk2; rw [N, Print.N, b8_run]; hit PN.n9
  case n9 =>
    node b9 b9_ok n9; rw [N, Print.N, b9_run]
    by_cases hz : σ.status.z = true
    · hit PN.loop
    · hit PN.n10
  case n10 => node b10 b10_ok n10; rw [N, Print.N, b10_run]; hit PN.chk3
  case chk3 =>
    node b11 b11_ok chk3; rw [N, Print.N, b11_run]
    split
    · hit PN.fail
    · hit PN.n12
  case n12 => node b12 b12_ok n12; rw [N, Print.N, b12_run]; hit PN.adv
  case adv => node b13 b13_ok adv; rw [N, Print.N, b13_run]; hit PN.loop
  case fail => node b14 b14_ok fail; rw [N, Print.N, b14_run]; exit PX.abort
  case done => node b16 b16_ok done; rw [N, Print.N, b16_run]; exit PX.ret

/-- **`scc_rt_print` with the fenced write is one segment** from its entry
to its return or its abort. -/
theorem seg_print (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 x29 ra .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 x29 ra .n5))) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 x29 ra .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label c0 x29 ra x) s c) :=
  (seg_printW (FStable.dframe R m0) hR hal hlo hhi hcode hentry (PrintW.triv c0 x29 ra) (SegW.ofSeg hsvc)).toSeg

end Proof

end Spike.Lib.A64.PrintD
