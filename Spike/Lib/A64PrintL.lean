/-
**A whole compiled function on AArch64**: `wc_printL` of `hello.w`'s
listing (plain calls, no stack depth counter, `Scc.Lower.callBlock`) as one
`Seg`, composed from its blocks over its control-flow graph
(`Spike/Lib/A64Cfg.lean`).

    wc_printL(xs = x0, o = x1, i = x2, n = x3, acc = x4):
      stack check: if sp - 128 < limit (thread pointer + 8) goto grow
      prologue (frame of 128 bytes, x29/x30 saved at 112/120, arguments at 0–32)
      e = load(xs + zext32(o + 8 i))              -- a heap load
      acc' = wc_emit8(e, acc)                     -- a call
      if n = 0 then return acc'
      n' = n - 1 (saturating); i' = i + 1 (abort on overflow)
      tail call wc_printL(xs, o, i', n', acc')
      grow: save x0–x7, x29, x30 in a frame of 80; bl scc_rt_morestack; restore; goto stack check

The region is `[-128, 0)` from the `sp` at entry: the frame, and the stack
grow path's 80 bytes inside it. Ghost parameters: the source control `c0`
(the specification is the machine-level frame discipline; the source
stutters), the caller's `x29` and the return address `ra`. Entry (`.e`):
`sp` at offset 0, `x29 = x29`, `x30 = ra`; the tail call comes back to it.
Return (exit `.ret`): pc at `ra`, `sp` at offset 0, `x29`, `x30` restored.
Abort (exit `.abort`): pc at `scc_rt_abort` with `x0 = 1` (overflow).

Given nodes (hypotheses): the thread-pointer load of the stack limit
(`htls`), the heap load (`hheap`), the call to `wc_emit8` (`hcall`, from its
entry with the return address in `x30` back to `.sp5`) and the call to
`scc_rt_morestack` (`hms`). The calls may grow the stack and so move the
frame: the region, the frame condition `F` (any condition no write inside
the region breaks, `FStable`; the callees' specifications keep it) and the
caller's `x29` are a ghost (`fn_seg_g`), and `hcall` and `hms` land at some
ghost. The code, the prologue's fall-through into `.0_entry` and the
stack-check label at the function's address are hypotheses.
-/
import Spike.Lib.A64Cfg
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.PrintL

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

/-! ## The blocks (generated) -/

def b0 : List Directive := parseAArch64("sub x9, sp, #128
mrs x10, tpidr_el0")
def b1 : List Directive := parseAArch64("subs xzr, x9, x10
b.lo .L21_wc_printL.stack_grow")
def b2 : List Directive := parseAArch64("add sp, x9, #0
str x29, [sp, #112]
str x30, [sp, #120]
add x29, sp, #112
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]")
def b3 : List Directive := parseAArch64("ldr x9, [sp, #16]
movz x10, #8
madd x9, x9, x10, xzr
str x9, [sp, #40]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
add x9, x9, x10
str x9, [sp, #48]
ldr x9, [sp, #48]
ubfm x9, x9, #0, #31
str x9, [sp, #56]
ldr x9, [sp]
ldr x10, [sp, #56]
add x9, x9, x10
str x9, [sp, #64]
ldr x10, [sp, #64]")
def b4 : List Directive := parseAArch64("str x9, [sp, #72]
ldr x0, [sp, #72]
ldr x1, [sp, #32]
bl wc_emit8")
def b5 : List Directive := parseAArch64("str x0, [sp, #80]
ldr x9, [sp, #24]
movz x10, #0
subs xzr, x9, x10
b.eq .L21_wc_printL.1_then6")
def b6 : List Directive := parseAArch64("b .L21_wc_printL.2_else7")
def b7 : List Directive := parseAArch64("ldr x0, [sp, #80]
ldr x29, [sp, #112]
ldr x30, [sp, #120]
add sp, sp, #128
ret")
def b8 : List Directive := parseAArch64("ldr x9, [sp, #24]
movz x10, #1
subs x9, x9, x10
csel x9, x9, xzr, hs
str x9, [sp, #88]
ldr x9, [sp, #16]
movz x10, #1
adds x9, x9, x10
b.hs .L21_wc_printL.abort_overflow")
def b9 : List Directive := parseAArch64("str x9, [sp, #96]
ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #96]
ldr x3, [sp, #88]
ldr x4, [sp, #80]
ldr x29, [sp, #112]
ldr x30, [sp, #120]
add sp, sp, #128
b wc_printL")
def b10 : List Directive := parseAArch64("sub sp, sp, #80
str x0, [sp]
str x1, [sp, #8]
str x2, [sp, #16]
str x3, [sp, #24]
str x4, [sp, #32]
str x5, [sp, #40]
str x6, [sp, #48]
str x7, [sp, #56]
str x29, [sp, #64]
str x30, [sp, #72]
add x29, sp, #64
movz x0, #128
bl scc_rt_morestack")
def b11 : List Directive := parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
ldr x2, [sp, #16]
ldr x3, [sp, #24]
ldr x4, [sp, #32]
ldr x5, [sp, #40]
ldr x6, [sp, #48]
ldr x7, [sp, #56]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b .L21_wc_printL.stack_check")
def b12 : List Directive := parseAArch64("movz x0, #1
bl scc_rt_abort")

/-- The offsets inside the frame. -/
abbrev oI : SO := ⟨-128, []⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets during the stack check (`x9` the new `sp`). -/
abbrev oX : SO := ⟨0, [(.X9, -128)]⟩
/-- The offsets in the stack grow path. -/
abbrev oG : SO := ⟨-80, []⟩

block_spec b0 (-128) 0 oE b0
block_spec b1 (-128) 0 oX b1
block_spec b2 (-128) 0 oX b2
block_spec b3 (-128) 0 oI b3
block_spec b4 (-128) 0 oI b4
block_spec b5 (-128) 0 oI b5
block_spec b6 (-128) 0 oI b6
block_spec b7 (-128) 0 oI b7
block_spec b8 (-128) 0 oI b8
block_spec b9 (-128) 0 oI b9
block_spec b10 (-128) 0 oE b10
block_spec b11 (-128) 0 oG b11
block_spec b12 (-128) 0 oI b12

/-! ## The graph -/

/-- The internal nodes: one per block, and the given nodes. -/
inductive PN where
  | e | tls | n1 | n2 | entry | heap | n4 | call | sp5 | n6 | then6 | else7 | n9 | grow | ms | spc | abort

/-- The exits. -/
inductive PX where
  | ret | abort

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64)

/-- Outside the frame: the source has not moved, `x29` and `x30` are the
caller's. -/
def JE (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra

/-- Inside the frame: the caller's `x29` and the return address are in
their cells. -/
def JI (σ : AS) (c : Ctl) : Prop := c = c0 ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "wc_printL", oE, JE c0 x29 ra⟩
  | .tls => ⟨lab "wc_printL" + 4 + 4, oX, JE c0 x29 ra⟩
  | .n1 => ⟨lab "wc_printL" + 4 + 4 + 4, oX, JE c0 x29 ra⟩
  | .n2 => ⟨lab "wc_printL" + 4 + 4 + 4 + 4 + 4, oX, JE c0 x29 ra⟩
  | .entry => ⟨lab ".L21_wc_printL.0_entry", oI, JI c0 x29 ra⟩
  | .heap => ⟨lab ".L21_wc_printL.0_entry" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
      + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .n4 => ⟨lab ".L21_wc_printL.0_entry" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
      + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .call => ⟨lab "wc_emit8", oI, fun σ c => JI c0 x29 ra σ c ∧
      σ.regs.X30.toBitVec =
        BitVec.ofInt 64
          (((lab ".L21_wc_printL.0_entry" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4
            + 4 + 4 + 4 + 4 + 4).toInt + 4 + 4 + 4 + 4).bmod 18446744073709551616)⟩
  | .sp5 => ⟨lab ".L21_wc_printL.sp5", oI, JI c0 x29 ra⟩
  | .n6 => ⟨lab ".L21_wc_printL.sp5" + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .then6 => ⟨lab ".L21_wc_printL.1_then6", oI, JI c0 x29 ra⟩
  | .else7 => ⟨lab ".L21_wc_printL.2_else7", oI, JI c0 x29 ra⟩
  | .n9 => ⟨lab ".L21_wc_printL.2_else7" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JI c0 x29 ra⟩
  | .grow => ⟨lab ".L21_wc_printL.stack_grow", oE, JE c0 x29 ra⟩
  | .ms => ⟨lab "scc_rt_morestack", oG, fun σ c => JI c0 x29 ra σ c ∧
      σ.regs.X30.toBitVec =
        BitVec.ofInt 64
          (((lab ".L21_wc_printL.stack_grow").toInt + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4).bmod
            18446744073709551616)⟩
  | .spc => ⟨lab ".L21_wc_printL.sp_check", oG, JI c0 x29 ra⟩
  | .abort => ⟨lab ".L21_wc_printL.abort_overflow", oI, JI c0 x29 ra⟩

/-- **The exits.** -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, JE c0 x29 ra⟩
  | .abort => ⟨lab "scc_rt_abort", oI, fun σ c => c = c0 ∧ σ.regs.X0 = 1⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n1).pc b1
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n2).pc b2
  entry : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .entry).pc b3
  n4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n4).pc b4
  sp5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .sp5).pc b5
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n6).pc b6
  then6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .then6).pc b7
  else7 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .else7).pc b8
  n9 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .n9).pc b9
  grow : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .grow).pc b10
  spc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .spc).pc b11
  abort : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra .abort).pc b12

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64} {γ : Sort _} {Rg : γ → Region}
  {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_fix g (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩))

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JE, JI, upd_apply]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, E, JE, JI, upd_apply]))

/-- **`wc_printL` is one segment** from its entry to its return or its
aborts. Its frame may move (a call that grows the stack): the region, the
frame condition and the caller's `x29` are a ghost `g` (`Rg g`, `Fg g`,
`fp g`), the given nodes `hcall` and `hms` land at some ghost, and the
function exits at some ghost (`fn_seg_g`). -/
theorem seg_printL (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -128) (hhi : ∀ g, 0 ≤ (Rg g).hi)
    (hcode : ∀ g, Code c0 (fp g) ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L21_wc_printL.0_entry" =
      (_root_.Executable.labels exe).label "wc_printL" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hcheck : (_root_.Executable.labels exe).label ".L21_wc_printL.stack_check" =
      (_root_.Executable.labels exe).label "wc_printL")
    (htls : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (fp g) ra .tls))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (fp g) ra .n1)))
    (hheap : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (fp g) ra .heap))
        (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (fp g) ra .n4)))
    (hcall : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (fp g) ra .call))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (N (_root_.Executable.labels exe).label c0 (fp g') ra .sp5) s c))
    (hms : ∀ g,
      Seg p lbl ms (At exe endPc (Rg g) (Fg g) (N (_root_.Executable.labels exe).label c0 (fp g) ra .ms))
        (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (N (_root_.Executable.labels exe).label c0 (fp g') ra .spc) s c))
    (g0 : γ) :
    Seg p lbl ms (At exe endPc (Rg g0) (Fg g0) (N (_root_.Executable.labels exe).label c0 (fp g0) ra .e))
      (fun s c => ∃ g x, At exe endPc (Rg g) (Fg g) (E (_root_.Executable.labels exe).label c0 (fp g) ra x) s c) := by
  refine fn_seg_g (Rg := Rg) (Fg := Fg) (N := fun g => N _ c0 (fp g) ra) (E := fun g => E _ c0 (fp g) ra)
    (fun g i => ?_) g0 PN.e
  have hF := hF g; have hR := hR g; have hal := hal g; have hlo := hlo g; have hhi := hhi g
  have hcode := hcode g
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.tls
  case tls => exact seg_fix g (seg_given PN.n1 (htls g))
  case n1 =>
    node b1 b1_ok n1; rw [N, b1_run]
    split
    · hit PN.grow
    · hit PN.n2
  case n2 => node b2 b2_ok n2; rw [N, b2_run]; hit PN.entry
  case entry => node b3 b3_ok entry; rw [N, b3_run]; hit PN.heap
  case heap => exact seg_fix g (seg_given PN.n4 (hheap g))
  case n4 => node b4 b4_ok n4; rw [N, b4_run]; hit PN.call
  case call => exact seg_moved PN.sp5 (hcall g)
  case sp5 =>
    node b5 b5_ok sp5; rw [N, b5_run]
    split
    · hit PN.then6
    · hit PN.n6
  case n6 => node b6 b6_ok n6; rw [N, b6_run]; hit PN.else7
  case then6 => node b7 b7_ok then6; rw [N, b7_run]; exit PX.ret
  case else7 =>
    node b8 b8_ok else7; rw [N, b8_run]
    split
    · hit PN.n9
    · hit PN.abort
  case n9 => node b9 b9_ok n9; rw [N, b9_run]; hit PN.e
  case grow => node b10 b10_ok grow; rw [N, b10_run]; hit PN.ms
  case ms => exact seg_moved PN.spc (hms g)
  case spc => node b11 b11_ok spc; rw [N, b11_run]; hit PN.e
  case abort => node b12 b12_ok abort; rw [N, b12_run]; exit PX.abort

end Proof

end Spike.Lib.A64.PrintL
