/-
**A whole runtime function on AArch64**: `scc_rt_print` of `hello.w`'s
listing (an earlier revision, listing lines 879–945) as one `Seg`, composed from
its blocks over its control-flow graph (`Spike/Lib/A64Cfg.lean`).

    scc_rt_print(buf = x0, len = x1):
      prologue (frame of 48 bytes, x29/x30 saved at 32/40, buf/len at 0/8)
      loop:  if len = 0 goto done
             r = write(1, buf, len)               -- svc #0, x8 = 64
             if r = -4 (EINTR) goto loop
             if r = -11 (EAGAIN) goto loop
             if r <= 0 goto fail
             buf += r; len -= r; goto loop
      fail:  x0 = 4; bl scc_rt_abort
      done:  epilogue; ret

The region is the function's frame: offsets `[-48, 0)` from the `sp` at
entry. Ghost parameters: the source control `c0` (the routine is runtime
code: the source stutters throughout), the caller's `x29` and the return
address `ra`. The specification:

- **entry** (`.e`): pc at `scc_rt_print`, `sp` at offset 0, `x29 = x29`,
  `x30 = ra`;
- **return** (exit `.ret`): pc at `ra`, `sp` at offset 0 again, `x29` and
  `x30` restored, the memory outside the frame unchanged;
- **abort** (exit `.abort`): pc at `scc_rt_abort` with `x0 = 4`.

The system call is a given node (`hsvc`): from `x0 = 1, x8 = 64` it returns
to the next instruction with the frame's cells and the offsets kept. The
layout facts are hypotheses: each block is at its node's pc (`CodeAt`, from
`CodeAt.of_codeAt` on the laid-out program), and the prologue falls through
to the label `.0_entry` (`hentry`).

The blocks' offsets are computed with a meet at joins (the loop head is
entered with `x29` known from the prologue and unknown after the system
call, so its offsets are `⟨-48, []⟩`).
-/
import Spike.Lib.A64Nodes
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Print

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-! ## The blocks (generated) -/

def b0 : List Directive := parseAArch64("sub sp, sp, #48
str x29, [sp, #32]
str x30, [sp, #40]
add x29, sp, #32
str x0, [sp]
str x1, [sp, #8]")
def b1 : List Directive := parseAArch64("b .L9_scc_rt_print.1_loop")
def b2 : List Directive := parseAArch64("ldr x9, [sp, #8]
movz x10, #0
subs xzr, x9, x10
b.eq .L9_scc_rt_print.7_done")
def b3 : List Directive := parseAArch64("b .L9_scc_rt_print.2_write")
def b4 : List Directive := parseAArch64("movz x0, #1
ldr x1, [sp]
ldr x2, [sp, #8]
movz x8, #64")
def b5 : List Directive := parseAArch64("str x0, [sp, #16]
ldr x9, [sp, #16]
movz x10, #65532
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs xzr, x9, x10")
def b6 : List Directive := parseAArch64("b.eq .L9_scc_rt_print.1_loop")
def b7 : List Directive := parseAArch64("b .L9_scc_rt_print.3_chk2")
def b8 : List Directive := parseAArch64("ldr x9, [sp, #16]
movz x10, #65525
movk x10, #65535, lsl #16
movk x10, #65535, lsl #32
movk x10, #65535, lsl #48
subs xzr, x9, x10")
def b9 : List Directive := parseAArch64("b.eq .L9_scc_rt_print.1_loop")
def b10 : List Directive := parseAArch64("b .L9_scc_rt_print.4_chk3")
def b11 : List Directive := parseAArch64("ldr x9, [sp, #16]
movz x10, #0
subs xzr, x9, x10
b.le .L9_scc_rt_print.6_fail")
def b12 : List Directive := parseAArch64("b .L9_scc_rt_print.5_adv")
def b13 : List Directive := parseAArch64("ldr x9, [sp]
ldr x10, [sp, #16]
add x9, x9, x10
str x9, [sp]
ldr x9, [sp, #8]
ldr x10, [sp, #16]
sub x9, x9, x10
str x9, [sp, #8]
b .L9_scc_rt_print.1_loop")
def b14 : List Directive := parseAArch64("movz x0, #4
bl scc_rt_abort")
def b16 : List Directive := parseAArch64("ldr x29, [sp, #32]
ldr x30, [sp, #40]
add sp, sp, #48
ret")

/-- **The barrier** `dmb ish` (`Emit.A64.fullFence`) that leads
`.L9_scc_rt_print.2_write` in every AArch64 program (`Runtime.printF`). -/
def bF : List Directive := parseAArch64("dmb ish")

example : bF = [.instr ⟨.W64, .DMB .sy⟩] := by decide

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-48, []⟩
/-- The offsets at entry and return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-48) 0 oE b0
block_spec b1 (-48) 0 oI b1
block_spec b2 (-48) 0 oI b2
block_spec b3 (-48) 0 oI b3
block_spec b4 (-48) 0 oI b4
block_spec b5 (-48) 0 oI b5
block_spec b6 (-48) 0 oI b6
block_spec b7 (-48) 0 oI b7
block_spec b8 (-48) 0 oI b8
block_spec b9 (-48) 0 oI b9
block_spec b10 (-48) 0 oI b10
block_spec b11 (-48) 0 oI b11
block_spec b12 (-48) 0 oI b12
block_spec b13 (-48) 0 oI b13
block_spec b14 (-48) 0 oI b14
block_spec b16 (-48) 0 oI b16

/-! ## The graph -/

/-- The internal nodes: one per block, and the system call. -/
inductive PN where
  | e | n1 | loop | n3 | write | svc | n5 | n6 | n7 | chk2 | n9 | n10 | chk3 | n12 | adv | fail | done

/-- The exits. -/
inductive PX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64)

/-- Inside the frame: the source has not moved, the caller's `x29` and the
return address are in their cells. -/
def JI (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra

/-- The pc after the system call's argument block. -/
abbrev pcSvc : Int64 := lab ".L9_scc_rt_print.2_write" + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_print", oE, fun σ c => c = c0 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra⟩
  | .n1 => ⟨lab ".L9_scc_rt_print.0_entry", oI, JI c0 x29 ra⟩
  | .loop => ⟨lab ".L9_scc_rt_print.1_loop", oI, JI c0 x29 ra⟩
  | .n3 => ⟨lab ".L9_scc_rt_print.1_loop" + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .write => ⟨lab ".L9_scc_rt_print.2_write", oI, JI c0 x29 ra⟩
  | .svc => ⟨pcSvc lab, oI, fun σ c => JI c0 x29 ra σ c ∧ σ.regs.X0 = 1 ∧ σ.regs.X8 = 64⟩
  | .n5 => ⟨pcSvc lab + 4, oI, JI c0 x29 ra⟩
  | .n6 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .n7 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .chk2 => ⟨lab ".L9_scc_rt_print.3_chk2", oI, JI c0 x29 ra⟩
  | .n9 => ⟨lab ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .n10 => ⟨lab ".L9_scc_rt_print.3_chk2" + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .chk3 => ⟨lab ".L9_scc_rt_print.4_chk3", oI, JI c0 x29 ra⟩
  | .n12 => ⟨lab ".L9_scc_rt_print.4_chk3" + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .adv => ⟨lab ".L9_scc_rt_print.5_adv", oI, JI c0 x29 ra⟩
  | .fail => ⟨lab ".L9_scc_rt_print.6_fail", oI, JI c0 x29 ra⟩
  | .done => ⟨lab ".L9_scc_rt_print.7_done", oI, JI c0 x29 ra⟩

/-- **The exits**: the return to `ra` with `sp`, `x29` and `x30` restored,
and the abort with code 4. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, fun σ c => c = c0 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra⟩
  | .abort => ⟨lab "scc_rt_abort", oI, fun σ c => c = c0 ∧ σ.regs.X0 = 4⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n1).pc b1
  loop : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .loop).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n3).pc b3
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
per block node (the system call is a given node). -/
structure PrintW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) : Prop where
  e : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .e) b0
  n1 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n1) b1
  loop : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .loop) b2
  n3 : BlkW W K exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n3) b3
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
  ⟨BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv,
    BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv, BlkW.triv⟩

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
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, upd_apply]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI, upd_apply]))

/-- **`scc_rt_print` is one segment inside `W`** from its entry to its
return or its abort, for every frame condition `F` no write inside the
frame breaks: its block nodes' states lie in `W`, none moved by `K` (`hW`),
and the system call is a given segment inside `W`. (`seg_print` is the
frame condition `DFrame R m0`.) -/
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
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.n1
  case n1 => node b1 b1_ok n1; rw [N, b1_run]; hit PN.loop
  case loop =>
    node b2 b2_ok loop; rw [N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.write
  case write => node b4 b4_ok write; rw [N, b4_run]; hit PN.svc
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; hit PN.n6
  case n6 =>
    node b6 b6_ok n6; rw [N, b6_run]
    by_cases hz : σ.status.z = true
    · hit PN.loop
    · hit PN.n7
  case n7 => node b7 b7_ok n7; rw [N, b7_run]; hit PN.chk2
  case chk2 => node b8 b8_ok chk2; rw [N, b8_run]; hit PN.n9
  case n9 =>
    node b9 b9_ok n9; rw [N, b9_run]
    by_cases hz : σ.status.z = true
    · hit PN.loop
    · hit PN.n10
  case n10 => node b10 b10_ok n10; rw [N, b10_run]; hit PN.chk3
  case chk3 =>
    node b11 b11_ok chk3; rw [N, b11_run]
    split
    · hit PN.fail
    · hit PN.n12
  case n12 => node b12 b12_ok n12; rw [N, b12_run]; hit PN.adv
  case adv => node b13 b13_ok adv; rw [N, b13_run]; hit PN.loop
  case fail => node b14 b14_ok fail; rw [N, b14_run]; exit PX.abort
  case done => node b16 b16_ok done; rw [N, b16_run]; exit PX.ret

/-- **`scc_rt_print` is one segment** from its entry to its return or its
abort. -/
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

end Spike.Lib.A64.Print
