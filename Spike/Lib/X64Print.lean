/-
**A whole runtime function on x64**: `scc_rt_print` of `hello.w`'s listing
(an earlier revision) as one `Seg`, composed from its blocks over its
control-flow graph (`Spike/Lib/X64Cfg.lean`): the x64 twin of
`Spike/Lib/A64Print.lean` (same routine, same graph).

The region is `[-40, 16)` from the frame's base: `%rsp` is at offset 8 on
entry, the return address in the cell `[8, 16)`, the caller's `%rbp` pushed
to `[0, 8)`, the frame below. Ghost parameters: the source control `c0`, the
caller's `%rbp` and the return address `ra`. Entry (`.e`): `%rsp` at offset
8, `%rbp = rbp0`, `ra` in its cell. Return (exit `.ret`): pc at `ra`, `%rsp`
at offset 16 (the return address popped), `%rbp` restored, the memory
outside the region unchanged. Abort (exit `.abort`): pc at `scc_rt_abort`
with `%rdi = 4`. The system call is a given node (`hsys`), the code and the
prologue's fall-through into `.entry` are hypotheses.
-/
import Spike.Lib.X64Cfg
import Kraken.X64.Parser

namespace Spike.Lib.X64.Print

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64

/-! ## The blocks (generated) -/

/- Each block is zipped with its instructions' sizes in bytes; a node's pc
is a label plus the sizes of the instructions before it. -/

def x0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp
movq %rdi, -8(%rbp)
movq %rsi, -16(%rbp)")).zip [1, 3, 4, 4, 4]
def x1 : List (Directive × Nat) := (parse("jmp .Lscc_rt_print.loop")).zip [2]
def x2 : List (Directive × Nat) := (parse("movq -16(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
je .Lscc_rt_print.done")).zip [4, 7, 3, 6]
def x3 : List (Directive × Nat) := (parse("jmp .Lscc_rt_print.write")).zip [2]
def x4 : List (Directive × Nat) := (parse("movq $1, %rdi
movq -8(%rbp), %rsi
movq -16(%rbp), %rdx
movl $1, %eax")).zip [7, 4, 4, 5]
def x5 : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq -24(%rbp), %rax
movq $-4, %rcx
cmpq %rcx, %rax
je .Lscc_rt_print.loop")).zip [4, 4, 7, 3, 2]
def x6 : List (Directive × Nat) := (parse("jmp .Lscc_rt_print.chk2")).zip [2]
def x7 : List (Directive × Nat) := (parse("movq -24(%rbp), %rax
movq $-11, %rcx
cmpq %rcx, %rax
je .Lscc_rt_print.loop")).zip [4, 7, 3, 2]
def x8 : List (Directive × Nat) := (parse("jmp .Lscc_rt_print.chk3")).zip [2]
def x9 : List (Directive × Nat) := (parse("movq -24(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax
jle .Lscc_rt_print.fail")).zip [4, 7, 3, 2]
def x10 : List (Directive × Nat) := (parse("jmp .Lscc_rt_print.adv")).zip [2]
def x11 : List (Directive × Nat) := (parse("movq -8(%rbp), %rax
movq -24(%rbp), %rcx
addq %rcx, %rax
movq %rax, -8(%rbp)
movq -16(%rbp), %rax
movq -24(%rbp), %rcx
subq %rcx, %rax
movq %rax, -16(%rbp)
jmp .Lscc_rt_print.loop")).zip [4, 4, 3, 4, 4, 4, 3, 4, 5]
def x12 : List (Directive × Nat) := (parse("movq $4, %rdi
call scc_rt_abort")).zip [7, 5]
def x13 : List (Directive × Nat) := (parse("movq %rbp, %rsp
popq %rbp
ret")).zip [3, 1, 1]

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-32, [(.rbp, 0)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨8, []⟩

block_spec x0 (-40) 16 oE x0
block_spec x1 (-40) 16 oI x1
block_spec x2 (-40) 16 oI x2
block_spec x3 (-40) 16 oI x3
block_spec x4 (-40) 16 oI x4
block_spec x5 (-40) 16 oI x5
block_spec x6 (-40) 16 oI x6
block_spec x7 (-40) 16 oI x7
block_spec x8 (-40) 16 oI x8
block_spec x9 (-40) 16 oI x9
block_spec x10 (-40) 16 oI x10
block_spec x11 (-40) 16 oI x11
block_spec x12 (-40) 16 oI x12
block_spec x13 (-40) 16 oI x13

/-! ## The graph -/

/-- The internal nodes: one per block, and the system call. -/
inductive PN where
  | e | n1 | loop | n3 | write | sys | n5 | n6 | chk2 | n8 | chk3 | n10 | adv | fail | done

/-- The exits. -/
inductive PX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64)

/-- Inside the frame: the source has not moved, the caller's `%rbp` and the
return address are in their cells. -/
def JI (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.slot 0 = rbp0 ∧ σ.slot 8 = ra

/-- The pc of the system call. -/
abbrev pcSys : Int64 := lab ".Lscc_rt_print.write" + 20

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_print", oE, fun σ c => c = c0 ∧ σ.regs.rbp.toBitVec = rbp0 ∧ σ.slot 8 = ra⟩
  | .n1 => ⟨lab ".Lscc_rt_print.entry", oI, JI c0 rbp0 ra⟩
  | .loop => ⟨lab ".Lscc_rt_print.loop", oI, JI c0 rbp0 ra⟩
  | .n3 => ⟨lab ".Lscc_rt_print.loop" + 20, oI, JI c0 rbp0 ra⟩
  | .write => ⟨lab ".Lscc_rt_print.write", oI, JI c0 rbp0 ra⟩
  | .sys => ⟨pcSys lab, oI, fun σ c => JI c0 rbp0 ra σ c ∧ σ.regs.get64 .rdi = 1⟩
  | .n5 => ⟨lab ".Lscc_rt_print.write" + 22, oI, JI c0 rbp0 ra⟩
  | .n6 => ⟨lab ".Lscc_rt_print.write" + 42, oI, JI c0 rbp0 ra⟩
  | .chk2 => ⟨lab ".Lscc_rt_print.chk2", oI, JI c0 rbp0 ra⟩
  | .n8 => ⟨lab ".Lscc_rt_print.chk2" + 16, oI, JI c0 rbp0 ra⟩
  | .chk3 => ⟨lab ".Lscc_rt_print.chk3", oI, JI c0 rbp0 ra⟩
  | .n10 => ⟨lab ".Lscc_rt_print.chk3" + 16, oI, JI c0 rbp0 ra⟩
  | .adv => ⟨lab ".Lscc_rt_print.adv", oI, JI c0 rbp0 ra⟩
  | .fail => ⟨lab ".Lscc_rt_print.fail", oI, JI c0 rbp0 ra⟩
  | .done => ⟨lab ".Lscc_rt_print.done", oI, JI c0 rbp0 ra⟩

/-- **The exits.** -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rbp = rbp0⟩
  | .abort => ⟨lab "scc_rt_abort", ⟨-40, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = 4⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .e).pc x0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n1).pc x1
  loop : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .loop).pc x2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n3).pc x3
  write : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .write).pc x4
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5).pc x5
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n6).pc x6
  chk2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .chk2).pc x7
  n8 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n8).pc x8
  chk3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .chk3).pc x9
  n10 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .n10).pc x10
  adv : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .adv).pc x11
  fail : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .fail).pc x12
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .done).pc x13
  /-- The `write` system call at `.sys` (a given node of the proof, so
  unused by it; its consumers read the instruction there). -/
  sys : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 rbp0 ra .sys).pc
      [(.instr (.regular .W64 .W64 .syscall), 2)]

/-- **The function's states inside `W`**, none moved by `K`: one obligation
per block node (the system call is a given node). -/
structure PrintW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .e) x0
  n1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n1) x1
  loop : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .loop) x2
  n3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n3) x3
  write : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .write) x4
  n5 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5) x5
  n6 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n6) x6
  chk2 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .chk2) x7
  n8 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n8) x8
  chk3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .chk3) x9
  n10 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n10) x10
  adv : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .adv) x11
  fail : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .fail) x12
  done : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .done) x13

/-- The function is inside the trivial predicate, with no outside moves. -/
theorem PrintW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} :
    PrintW c0 rbp0 ra (fun _ _ => True) (fun _ _ => False) exe endPc R F :=
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv⟩

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {rbp0 ra : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code, its `W` obligation; the
edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi (fun s he hn => hcode.$f s he hn) hW.$f
    fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;>
    simp_all [N, E, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne]))

/-- **`scc_rt_print` is one segment inside `W`** from its entry to its
return or its abort, for every frame condition `F` no write inside the
frame breaks: its block nodes' states lie in `W`, none moved by `K` (`hW`),
and the system call is a given segment inside `W`. (`seg_print` is the
frame condition `DFrame R m0`.) -/
theorem seg_printW {W : Frag isa} {K : State → State → Prop} {F : MachineData → Prop} (hF : FStable R F)
    (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hcode : Code c0 rbp0 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hW : PrintW c0 rbp0 ra W K exe endPc R F)
    (hsys : SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label c0 rbp0 ra x) s c) := by
  refine fn_segW (N := N _ c0 rbp0 ra) (E := E _ c0 rbp0 ra) (fun i => ?_) PN.e
  cases i
  case e => node x0 x0_ok e; rw [N, x0_run]; hit PN.n1
  case n1 => node x1 x1_ok n1; rw [N, x1_run]; hit PN.loop
  case loop =>
    node x2 x2_ok loop; rw [N, x2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => node x3 x3_ok n3; rw [N, x3_run]; hit PN.write
  case write => node x4 x4_ok write; rw [N, x4_run]; hit PN.sys
  case sys => exact seg_givenW PN.n5 hsys
  case n5 =>
    node x5 x5_ok n5; rw [N, x5_run]
    split
    · hit PN.loop
    · hit PN.n6
  case n6 => node x6 x6_ok n6; rw [N, x6_run]; hit PN.chk2
  case chk2 =>
    node x7 x7_ok chk2; rw [N, x7_run]
    split
    · hit PN.loop
    · hit PN.n8
  case n8 => node x8 x8_ok n8; rw [N, x8_run]; hit PN.chk3
  case chk3 =>
    node x9 x9_ok chk3; rw [N, x9_run]
    split
    · hit PN.fail
    · hit PN.n10
  case n10 => node x10 x10_ok n10; rw [N, x10_run]; hit PN.adv
  case adv => node x11 x11_ok adv; rw [N, x11_run]; hit PN.loop
  case fail => node x12 x12_ok fail; rw [N, x12_run]; exit PX.abort
  case done => node x13 x13_ok done; rw [N, x13_run]; exit PX.ret

/-- **`scc_rt_print` is one segment** from its entry to its return or its
abort. -/
theorem seg_print (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hcode : Code c0 rbp0 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".Lscc_rt_print.entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 16)
    (hsys : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .sys))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5))) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 rbp0 ra .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label c0 rbp0 ra x) s c) :=
  (seg_printW (FStable.dframe R m0) hR hlo hhi hcode hentry (PrintW.triv c0 rbp0 ra) (SegW.ofSeg hsys)).toSeg

end Proof

end Spike.Lib.X64.Print
