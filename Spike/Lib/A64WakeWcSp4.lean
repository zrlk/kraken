/-
**wake.w's `wc_main` from `.sp4` to its `clone`** (AArch64), at the listing
level, in `wc_main`'s 80-byte frame (`oW`):

    .L21_wc_main.sp4:                   -- x0 = the second TCB t
      str x0, [sp, #24]; ldr x9, [sp, #16]; ldr x10, [sp, #24]   (sp4A)
      str x9, [x10, #56]                -- row: the TCB's tid word
      ldr x0, [sp, #24]; bl scc_rt_thread_init                   (initCall)
    .L21_wc_main.sp6:                   -- x0 = the child's stack top k
      str x0, [sp, #32]; ldr x9, [sp]; str x9, [sp, #40]         (sp6A)
      dmb ish                           -- row
      ldr x1, [sp, #32]; ldr x3, [sp, #24]; ldr x9, [sp, #8]; ldr x10, [sp, #40]
      movz x0, #3840; movk x0, #13, lsl #16; movz x2, #0; movz x4, #0
      movz x8, #220                                              (cloneArgs)
      svc #0                            -- `WakeChildAt.svcB` (`cloneAt`)

The blocks, their code in `wakeProg` and runs, the nodes between them and
the edges the runs give. The two rows (a store off the frame, a fence) and
the node obligations inside `W` are on top (`A64WakeWcMid`);
a row keeps every node fact here but `x9`/`x10` (`wcN4s` to `wcN5`) and
nothing (`wcN6f` to `wcN6a`). At the `svc`, `ownG_clone`: the owned words
`hPC` asks (`scc_rt_stack_next` at `32768`, `scc_rt_nthreads` at `1`). The
listing is wake.w's certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `sp4A`, `initCall`, `sp6A`, `cloneArgs` (`block_spec`); `wcSp4In`,
  `wake_wcSp4In`: the blocks and rows at their offsets, the labels' gaps.
- `FrW cA m fr`: the frame's cell `[sp, #8]`, main's word `[sp]`, and the
  caller's `x29`, `x30` (`fr`) at `[sp, #64]`, `[sp, #72]`.
- `wcN4F`, `wcN4s`, `wcN5`, `wcNI`, `wcN6`, `wcN6f`, `wcN6a`, `wcNS`: the
  nodes; `sp4A_edge`, `initCall_edge`, `sp6A_edge`, `cloneArgs_edge`: the
  blocks' edges.
- `ownG_clone`: the owned words at the `svc`.
-/
import Spike.Lib.A64WakeTcb2Call
import Spike.Lib.A64WakeOwnGEq

namespace Spike.Lib.A64.WakePh.WcSp4

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.Tcb2Call (oW)
open Scc.Cert.Rt.A64 (Lays blockAt labelGap label_labelGap codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-! ## The blocks -/

/-- `.sp4`'s first block: the TCB to `[sp, #24]`, the reserve's id and the TCB. -/
def sp4A : List Directive := parseAArch64("str x0, [sp, #24]
ldr x9, [sp, #16]
ldr x10, [sp, #24]")

/-- The tid word's store (a row). -/
def tidSt : List Directive := parseAArch64("str x9, [x10, #56]")

/-- The call of `scc_rt_thread_init` on the TCB. -/
def initCall : List Directive := parseAArch64("ldr x0, [sp, #24]
bl scc_rt_thread_init")

/-- `.sp6`'s first block: the stack top to `[sp, #32]`, main's word to `[sp, #40]`. -/
def sp6A : List Directive := parseAArch64("str x0, [sp, #32]
ldr x9, [sp]
str x9, [sp, #40]")

/-- The fence (a row). -/
def fenceB : List Directive := parseAArch64("dmb ish")

/-- The clone's arguments. -/
def cloneArgs : List Directive := parseAArch64("ldr x1, [sp, #32]
ldr x3, [sp, #24]
ldr x9, [sp, #8]
ldr x10, [sp, #40]
movz x0, #3840
movk x0, #13, lsl #16
movz x2, #0
movz x4, #0
movz x8, #220")

block_spec sp4A (-80) 0 oW sp4A
block_spec initCall (-80) 0 oW initCall
block_spec sp6A (-80) 0 oW sp6A
block_spec cloneArgs (-80) 0 oW cloneArgs

/-- **The blocks and rows in `prog`** at `.sp4` (`0`, `3`, `4`) and `.sp6`
(`0`, `3`, `4`), `.sp6` six instructions after `.sp4`. -/
def wcSp4In (prog : List Directive) : Bool :=
  blockAt prog ".L21_wc_main.sp4" 0 sp4A && blockAt prog ".L21_wc_main.sp4" 3 tidSt &&
    blockAt prog ".L21_wc_main.sp4" 4 initCall && labelGap prog ".L21_wc_main.sp4" ".L21_wc_main.sp6" 6 &&
    blockAt prog ".L21_wc_main.sp6" 0 sp6A && blockAt prog ".L21_wc_main.sp6" 3 fenceB &&
    blockAt prog ".L21_wc_main.sp6" 4 cloneArgs

theorem wake_wcSp4In : wcSp4In wakeProg = true := by decide +kernel

/-! ## The nodes -/

/-- **The frame's words** the clone reads: the cell `cA` at `[sp, #8]`,
main's word `m` at `[sp]`; and the caller's frame pointer and return address
`fr` the prologue saved at `[sp, #64]`, `[sp, #72]` (main's after the
clone: `WakeParent.JS`). -/
def FrW (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (σ : Spike.Lib.A64.Flow.AS) : Prop :=
  σ.slot (-72) = cA ∧ σ.slot (-80) = m ∧ σ.slot (-16) = fr.1 ∧ σ.slot (-8) = fr.2

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t k cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- At `.sp4`: `x0` the TCB `t`, the frame's words. -/
def wcN4F : ND := ⟨lab ".L21_wc_main.sp4", oW, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = t ∧ FrW cA m fr σ⟩

/-- At the tid store: `x9` the reserve's id `[sp, #16]`, `x10` and `[sp, #24]` the TCB. -/
def wcN4s : ND := ⟨lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 3), oW, fun σ c => c = c0 ∧
  σ.regs.X9.toBitVec = σ.slot (-64) ∧ σ.regs.X10.toBitVec = t ∧ σ.slot (-56) = t ∧ FrW cA m fr σ⟩

/-- Past the tid store: `[sp, #24]` the TCB. -/
def wcN5 : ND := ⟨lab ".L21_wc_main.sp4" + Int64.ofNat (4 * 4), oW, fun σ c => c = c0 ∧
  σ.slot (-56) = t ∧ FrW cA m fr σ⟩

/-- **The call node**: at `scc_rt_thread_init`, `x0` the TCB, the return address `.sp6`. -/
def wcNI : ND := ⟨lab "scc_rt_thread_init", oW, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = t ∧
  σ.regs.X30.toBitVec = (lab ".L21_wc_main.sp6").toBitVec ∧ σ.slot (-56) = t ∧ FrW cA m fr σ⟩

/-- Back at `.sp6`: `x0` the stack top `k`. -/
def wcN6 : ND := ⟨lab ".L21_wc_main.sp6", oW, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = k ∧
  σ.slot (-56) = t ∧ FrW cA m fr σ⟩

/-- At the fence: `k` at `[sp, #32]`, main's word at `[sp, #40]`. -/
def wcN6f : ND := ⟨lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 3), oW, fun σ c => c = c0 ∧
  σ.slot (-48) = k ∧ σ.slot (-40) = m ∧ σ.slot (-56) = t ∧ FrW cA m fr σ⟩

/-- Past the fence (the same facts). -/
def wcN6a : ND := ⟨lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 4), oW, fun σ c => c = c0 ∧
  σ.slot (-48) = k ∧ σ.slot (-40) = m ∧ σ.slot (-56) = t ∧ FrW cA m fr σ⟩

/-- **At the clone's `svc`**: `clone(flags, k, 0, t, 0)`, `x9` the cell, `x10` main's word; the
frame's words. -/
def wcNS : ND := ⟨lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13), oW, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = 855808#64 ∧ σ.regs.X1.toBitVec = k ∧ σ.regs.X2.toBitVec = 0#64 ∧
  σ.regs.X3.toBitVec = t ∧ σ.regs.X4.toBitVec = 0#64 ∧ σ.regs.X8.toBitVec = 220#64 ∧
  σ.regs.X9.toBitVec = cA ∧ σ.regs.X10.toBitVec = m ∧ FrW cA m fr σ⟩

end Nodes

/-! ## The edges -/

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
  {σ : Spike.Lib.A64.Flow.AS} {c : Ctl}

/-- An edge: the block's run from `n` reaches `n'`. -/
abbrev Edge (lab : Label → Int64) (blk : List Directive) (n n' : ND) (σ : Spike.Lib.A64.Flow.AS) (c : Ctl) : Prop :=
  (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oW, σ⟩).pc = n'.pc ∧ (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oW, σ⟩).so = n'.o ∧
    n'.J (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, oW, σ⟩).σ c

/-- `sp4A` from `.sp4` to the tid store. -/
theorem sp4A_edge (hJ : (wcN4F lab c0 t cA m fr).J σ c) :
    Edge lab sp4A (wcN4F lab c0 t cA m fr) (wcN4s lab c0 t cA m fr) σ c := by
  obtain ⟨h0, hx, h72, h80⟩ := hJ
  refine ⟨?_, ?_, ?_⟩
  · simp only [wcN4F, wcN4s, sp4A_run]
    rw [show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc]
  · simp only [wcN4F, wcN4s, sp4A_run]
  · simp only [wcN4F, wcN4s, sp4A_run, FrW, Spike.Lib.upd]
    simp_all

/-- `initCall` from past the tid store to `scc_rt_thread_init`, in any
layout of `wakeProg`. -/
theorem initCall_edge {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeProg kp) (hJ : (wcN5 (_root_.Executable.labels exe).label c0 t cA m fr).J σ c) :
    Edge (_root_.Executable.labels exe).label initCall (wcN5 (_root_.Executable.labels exe).label c0 t cA m fr)
      (wcNI (_root_.Executable.labels exe).label c0 t cA m fr) σ c := by
  obtain ⟨h0, h56, hF⟩ := hJ
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  refine ⟨by simp only [initCall_run]; rfl, by simp only [initCall_run]; rfl, h0, by simp only [initCall_run, wcN5]; exact h56, ?_,
    by simp only [initCall_run]; exact h56, by simp only [initCall_run]; exact hF⟩
  simp only [wcN5, initCall_run, Spike.Lib.A64.Flow.Ret0.ofInt_bmod]
  rw [label_labelGap hp hin.1.1.1.2, show Int64.ofNat (4 * 4) = 16 from rfl, show Int64.ofNat (4 * 6) = 24 from rfl,
    Int64.toBitVec_add, show ∀ y : Int, y + 4 + 4 = y + 8 from fun y => by omega, BitVec.ofInt_add,
    Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

/-- `sp6A` from `.sp6` to the fence. -/
theorem sp6A_edge (hJ : (wcN6 lab c0 t k cA m fr).J σ c) :
    Edge lab sp6A (wcN6 lab c0 t k cA m fr) (wcN6f lab c0 t k cA m fr) σ c := by
  obtain ⟨h0, hx, h56, h72, h80⟩ := hJ
  refine ⟨?_, ?_, ?_⟩
  · simp only [wcN6, wcN6f, sp6A_run]
    rw [show Int64.ofNat (4 * 3) = 4 + 4 + 4 from rfl]; simp only [Int64.add_assoc]
  · simp only [wcN6, wcN6f, sp6A_run]
  · simp only [wcN6, wcN6f, sp6A_run, FrW, Spike.Lib.upd]
    simp_all

/-- `cloneArgs` from past the fence to the clone's `svc`. -/
theorem cloneArgs_edge (hJ : (wcN6a lab c0 t k cA m fr).J σ c) :
    Edge lab cloneArgs (wcN6a lab c0 t k cA m fr) (wcNS lab c0 t k cA m fr) σ c := by
  obtain ⟨h0, h48, h40, h56, h72, h80⟩ := hJ
  refine ⟨?_, ?_, ?_⟩
  · simp only [wcN6a, wcNS, cloneArgs_run]
    rw [show Int64.ofNat (4 * 4) = 16 from rfl, show Int64.ofNat (4 * 13) = 16 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 from rfl]
    simp only [Int64.add_assoc]
  · simp only [wcN6a, wcNS, cloneArgs_run]
  · simp only [wcN6a, wcNS, cloneArgs_run]
    exact ⟨h0, rfl, h48, rfl, h56, rfl, rfl, h72, h40, h72, h80⟩

end Edges

/-! ## The owned words at the clone -/

/-- **The owned words at the clone's `svc`** (`hPC`'s): under `ownG`, with
the labels resolved at the canonical base, `scc_rt_stack_next` holds
`32768` and `scc_rt_nthreads` (`a`) `1` (`own2b` past the second take). -/
theorem ownG_clone {L : RuntimeLayout} {a : BitVec 64} {s : State}
    (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hpc : pcOf s = (L.lab ".L21_wc_main.sp6" + Int64.ofNat (4 * 13)).toBitVec.toNat) :
    ((⟨L.nextA, 8⟩ : Loc), (32768#64 : BitVec 64).setWidth 128) ∈ ownG L a s ∧
      ((⟨a, 8⟩ : Loc), (1#64 : BitVec 64).setWidth 128) ∈ ownG L a s := by
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eq (L := L) hlab
  have h6 : pcOf s = 2169344 := by
    rw [hpc, Int64.toBitVec_add, BitVec.toNat_add, e6]; rfl
  have hg : Good2b L s := .inr (.inl (by simp only [inPc, e6, e7, h6]; decide))
  rw [ownG_2b hlab hg, h6]
  have hb : ph2b 2169344 / 4 % 2 = 0 ∧ ph2b 2169344 / 16 % 2 = 0 := by rw [ph2b_eq]; decide +kernel
  simp only [own2b, ownV, hb.1, hb.2]
  simp

/-- info: 'Spike.Lib.A64.WakePh.WcSp4.ownG_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ownG_clone

/-- info: 'Spike.Lib.A64.WakePh.WcSp4.cloneArgs_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cloneArgs_edge

/-- info: 'Spike.Lib.A64.WakePh.WcSp4.initCall_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms initCall_edge

end Spike.Lib.A64.WakePh.WcSp4
