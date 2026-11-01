/-
**hello.w's `wc_main` from `.sp6` to its `clone`** (AArch64), at the listing level, in `wc_main`'s 144-byte frame
(`oWH`),
in hello.w's listing (`SccCode.helloProg`, label prefix `.L22_wc_main`):

    .L22_wc_main.sp6:                   -- x0 = the child's stack top k
      str x0, [sp, #64]                 -- k
      ldr x9, [sp, #8];  str x9, [sp, #72]     -- the packet: sl1
      ldr x9, [sp, #16]; str x9, [sp, #80]     --             sl2
      ldr x9, [sp, #24]; str x9, [sp, #88]     --             sl3
      ldr x9, [sp, #40]; str x9, [sp, #96]     --             the cell cA
      ldr x9, [sp, #32]; str x9, [sp, #104]    --             main's word me   (sp6AH)
      dmb ish                           -- row (`fenceB`)
      ldr x1, [sp, #64]; ldr x3, [sp, #56]; ldr x9, [sp]
      ldr x10 .. x14, [sp, #72 .. #104]
      movz x0, #3840; movk x0, #13, lsl #16; movz x2, #0; movz x4, #0
      movz x8, #220                                              (cloneArgsH)
    .sp6+100: svc #0                    -- the clone (`svcH`)

wake.w's `A64WakeWcSp4` (`.sp6` part) at hello's frame: the five spills
`x0 .. x4` of `wc_main`'s arguments at `[sp, #0 .. #32]` (the slice's four
registers `sl` and main's word `me`), the cell at `[sp, #40]`, the TCB at
`[sp, #56]`, the packet `[sp, #72 .. #104]`. This file has the blocks,
their code in `helloProg`, the nodes and the blocks' edges; the segment
inside `W` is `A64HelloWcSp6Seg`. It imports nothing of hello-c3 (only
hello-b2's `A64HelloCode` and wake's files), so `A64HelloWcSp3` can
import it for its exit node `wcN6H`.

- `sp6AH`, `cloneArgsH`, `svcH` (`block_spec`); `wcSp6In`, `hello_wcSp6In`:
  the blocks and the fence at their offsets in `helloProg`.
- `oWH`, `FrWH sl me cA fr`: the frame's offsets; its words (the spills,
  the cell, the caller's `x29`, `x30`).
- `wcN6H`, `wcN6fH`, `wcN6aH`, `wcNSH`: the nodes (`.sp6` with `x0 = k`, the
  TCB `t` at `[sp, #56]`; the fence and past it, with the packet; the
  `svc`, `clone(855808, k, 0, t, 0)` with `x9 .. x14` the packet's words);
  `sp6AH_edge`, `cloneArgsH_edge`: the blocks' edges.
-/
import Spike.Lib.A64WakeWcSp4
import Spike.Lib.A64HelloCode

namespace Spike.Lib.A64.HelloPh.WcSp6

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4 (fenceB Edge)
open Scc.Cert.Rt.A64 (blockAt)
open SccCode (helloProg)

/-! ## The blocks -/

/-- `wc_main`'s frame offsets (`sp` 144 below the entry's). -/
abbrev oWH : SO := ⟨-144, []⟩

/-- `.sp6`'s first block: the stack top to `[sp, #64]`, the packet. -/
def sp6AH : List Directive := parseAArch64("str x0, [sp, #64]
ldr x9, [sp, #8]
str x9, [sp, #72]
ldr x9, [sp, #16]
str x9, [sp, #80]
ldr x9, [sp, #24]
str x9, [sp, #88]
ldr x9, [sp, #40]
str x9, [sp, #96]
ldr x9, [sp, #32]
str x9, [sp, #104]")

/-- The clone's arguments. -/
def cloneArgsH : List Directive := parseAArch64("ldr x1, [sp, #64]
ldr x3, [sp, #56]
ldr x9, [sp]
ldr x10, [sp, #72]
ldr x11, [sp, #80]
ldr x12, [sp, #88]
ldr x13, [sp, #96]
ldr x14, [sp, #104]
movz x0, #3840
movk x0, #13, lsl #16
movz x2, #0
movz x4, #0
movz x8, #220")

/-- The clone's system call. -/
def svcH : List Directive := parseAArch64("svc #0")

block_spec sp6AH (-144) 0 oWH sp6AH
block_spec cloneArgsH (-144) 0 oWH cloneArgsH

/-- **The blocks and the fence in `prog`** at `.sp6` (`0`, `11`, `12`, and
the `svc` at `25`). -/
def wcSp6In (prog : List Directive) : Bool :=
  blockAt prog ".L22_wc_main.sp6" 0 sp6AH && blockAt prog ".L22_wc_main.sp6" 11 fenceB &&
    blockAt prog ".L22_wc_main.sp6" 12 cloneArgsH && blockAt prog ".L22_wc_main.sp6" 25 svcH

theorem hello_wcSp6In : wcSp6In helloProg = true := by decide +kernel

/-! ## The nodes -/

/-- **The frame's words**: the spills of `wc_main`'s arguments, the slice's
registers `sl` at `[sp, #0 .. #24]` and main's word `me` at `[sp, #32]`;
the cell `cA` at `[sp, #40]`; the caller's frame pointer and return address
`fr` at `[sp, #128]`, `[sp, #136]`. -/
def FrWH (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64)
    (σ : Spike.Lib.A64.Flow.AS) : Prop :=
  σ.slot (-144) = sl.1 ∧ σ.slot (-136) = sl.2.1 ∧ σ.slot (-128) = sl.2.2.1 ∧ σ.slot (-120) = sl.2.2.2 ∧
    σ.slot (-112) = me ∧ σ.slot (-104) = cA ∧ σ.slot (-16) = fr.1 ∧ σ.slot (-8) = fr.2

/-- **The packet** at `[sp, #72 .. #104]`: `sl1`, `sl2`, `sl3`, the cell,
main's word. -/
def PktH (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (me cA : BitVec 64) (σ : Spike.Lib.A64.Flow.AS) : Prop :=
  σ.slot (-72) = sl.2.1 ∧ σ.slot (-64) = sl.2.2.1 ∧ σ.slot (-56) = sl.2.2.2 ∧ σ.slot (-48) = cA ∧
    σ.slot (-40) = me

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t k : BitVec 64) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
  (me cA : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- **At `.sp6`** (back from `scc_rt_thread_init`): `x0` the stack top `k`,
the TCB `t` at `[sp, #56]`, the frame's words. -/
def wcN6H : ND := ⟨lab ".L22_wc_main.sp6", oWH, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = k ∧
  σ.slot (-88) = t ∧ FrWH sl me cA fr σ⟩

/-- At the fence: `k` at `[sp, #64]`, the packet. -/
def wcN6fH : ND := ⟨lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 11), oWH, fun σ c => c = c0 ∧
  σ.slot (-80) = k ∧ σ.slot (-88) = t ∧ PktH sl me cA σ ∧ FrWH sl me cA fr σ⟩

/-- Past the fence (the same facts). -/
def wcN6aH : ND := ⟨lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 12), oWH, fun σ c => c = c0 ∧
  σ.slot (-80) = k ∧ σ.slot (-88) = t ∧ PktH sl me cA σ ∧ FrWH sl me cA fr σ⟩

/-- **At the clone's `svc`**: `clone(flags, k, 0, t, 0)`, `x9` the slice's
first register, `x10 .. x14` the packet; the frame's words. -/
def wcNSH : ND := ⟨lab ".L22_wc_main.sp6" + Int64.ofNat (4 * 25), oWH, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = 855808#64 ∧ σ.regs.X1.toBitVec = k ∧ σ.regs.X2.toBitVec = 0#64 ∧
  σ.regs.X3.toBitVec = t ∧ σ.regs.X4.toBitVec = 0#64 ∧ σ.regs.X8.toBitVec = 220#64 ∧
  σ.regs.X9.toBitVec = sl.1 ∧ σ.regs.X10.toBitVec = sl.2.1 ∧ σ.regs.X11.toBitVec = sl.2.2.1 ∧
  σ.regs.X12.toBitVec = sl.2.2.2 ∧ σ.regs.X13.toBitVec = cA ∧ σ.regs.X14.toBitVec = me ∧ FrWH sl me cA fr σ⟩

end Nodes

/-! ## The edges -/

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : Spike.Lib.A64.Flow.AS} {c : Ctl}

/-- An edge in hello's frame: the block's run from `n` reaches `n'`. -/
abbrev EdgeH (lab : Label → Int64) (blk : List Directive) (n n' : ND) (σ : Spike.Lib.A64.Flow.AS) (c : Ctl) : Prop :=
  (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oWH, σ⟩).pc = n'.pc ∧
    (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oWH, σ⟩).so = n'.o ∧
    n'.J (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oWH, σ⟩).σ c

/-- `sp6AH` from `.sp6` to the fence. -/
theorem sp6AH_edge (hJ : (wcN6H lab c0 t k sl me cA fr).J σ c) :
    EdgeH lab sp6AH (wcN6H lab c0 t k sl me cA fr) (wcN6fH lab c0 t k sl me cA fr) σ c := by
  obtain ⟨h0, hx, h88, h144, h136, h128, h120, h112, h104, h16, h8⟩ := hJ
  refine ⟨?_, ?_, ?_⟩
  · simp only [wcN6H, wcN6fH, sp6AH_run]
    rw [show Int64.ofNat (4 * 11) = 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl]
    simp only [Int64.add_assoc]
  · simp only [wcN6H, wcN6fH, sp6AH_run]
  · simp only [wcN6H, wcN6fH, sp6AH_run, FrWH, PktH, Spike.Lib.upd]
    simp_all

/-- `cloneArgsH` from past the fence to the clone's `svc`. -/
theorem cloneArgsH_edge (hJ : (wcN6aH lab c0 t k sl me cA fr).J σ c) :
    EdgeH lab cloneArgsH (wcN6aH lab c0 t k sl me cA fr) (wcNSH lab c0 t k sl me cA fr) σ c := by
  obtain ⟨h0, h80, h88, ⟨p72, p64, p56, p48, p40⟩, hF⟩ := hJ
  obtain ⟨h144, h136, h128, h120, h112, h104, h16, h8⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · simp only [wcN6aH, wcNSH, cloneArgsH_run]
    rw [show Int64.ofNat (4 * 12) = 48 from rfl,
      show Int64.ofNat (4 * 25) = 48 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl]
    simp only [Int64.add_assoc]
  · simp only [wcN6aH, wcNSH, cloneArgsH_run]
  · simp only [wcN6aH, wcNSH, cloneArgsH_run, FrWH]
    exact ⟨h0, rfl, h80, rfl, h88, rfl, rfl, h144, p72, p64, p56, p48, p40, h144, h136, h128, h120, h112, h104,
      h16, h8⟩

end Edges

/-- info: 'Spike.Lib.A64.HelloPh.WcSp6.sp6AH_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sp6AH_edge

/-- info: 'Spike.Lib.A64.HelloPh.WcSp6.cloneArgsH_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cloneArgsH_edge

end Spike.Lib.A64.HelloPh.WcSp6
