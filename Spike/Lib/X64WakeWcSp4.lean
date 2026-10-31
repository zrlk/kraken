/-
**wake.w's `wc_main` from `.x20` to `.x21`** (x86-64; twin of
`Spike/Lib/A64WakeWcSp4.lean`'s `.sp4` half), at the listing level, in
`wc_main`'s frame (`oW`: `%rsp` at `-64`, `%rbp` at `0`):

    .Lwc_main.x20:                      -- %rax = the second TCB t
      movq %rax, -32(%rbp); movq -32(%rbp), %rcx; movq -24(%rbp), %rax   (x20A)
      movq %rax, 56(%rcx)               -- row: the TCB's tid word
      movq -32(%rbp), %rdi; call scc_rt_thread_init                     (initCall)
    .Lwc_main.x21:                      -- %rax = the child's stack top k

The `.x21` half (to the clone's `syscall`) is `Spike/Lib/X64WakeClone.lean`
(`WcClone.wcN21` … `wcNS`). The tid store is a row (a store off the frame),
on top, as A64's.

Where x86-64 differs from AArch64: the return address is the word the
`call` pushes at `-72` (`initCall_ra`), so the call node `wcNI` is at the
offsets `oC`; `%rcx` holds the TCB at the tid store (A64's `x10`), `%rax`
the reserve's id (A64's `x9`).

- `x20A`, `tidSt`, `initCall` (`block_spec`); `wcSp4In`, `wake_wcSp4In`:
  the blocks and the row at `.x20`'s offsets, `.x21` 25 bytes after.
- `FrV cA m fr`: the frame's words before the TCB's spill (`WcClone.FrW`
  without `-32`; `frW_of`).
- `wcN20`, `wcN20s`, `wcN20p`, `wcNI`: the nodes; `x20A_edge`,
  `initCall_edge`: the blocks' edges, the call's into `scc_rt_thread_init`
  with `.x21` pushed.
- `ownG_clone`: the owned words at the clone's `syscall` (`own2b` past the
  second take: `scc_rt_stack_next` at `32768`, `scc_rt_nthreads` at `1`).
-/
import Spike.Lib.X64WakeClone
import Spike.Lib.X64WakeOwnGEq

namespace Spike.Lib.X64.WakePh.WcSp4

open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (oW x21L FrW)
open Scc.Cert.Rt.X64 (Lays blockAt labelGap label_labelGap_lays)
open Scc.Sem.X64 (codeLabel pcOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open SccCode (wakeCells)

/-! ## The blocks -/

/-- The offsets after the `call` (the return address at `-72`). -/
abbrev oC : SO := ⟨-72, [(.rbp, 0)]⟩

/-- The label of `.x20`. -/
abbrev x20L : Label := ".Lwc_main.x20"

/-- `.x20`'s first block: the TCB to `-32` and `%rcx`, the reserve's id to `%rax`. -/
def x20A : List (Directive × Nat) := (parse("movq %rax, -32(%rbp)
movq -32(%rbp), %rcx
movq -24(%rbp), %rax")).zip [4, 4, 4]

/-- The tid word's store (a row). -/
def tidSt : List (Directive × Nat) := (parse("movq %rax, 56(%rcx)")).zip [4]

/-- The call of `scc_rt_thread_init` on the TCB. -/
def initCall : List (Directive × Nat) := (parse("movq -32(%rbp), %rdi
call scc_rt_thread_init")).zip [4, 5]

block_spec x20A (-64) 16 oW x20A
block_spec initCall (-72) 16 oW initCall

/-- **The blocks and the row in `cells`** at `.x20` (indices `0`, `3`, `4`,
byte offsets `0`, `12`, `16`), `.x21` six instructions and 25 bytes after. -/
def wcSp4In (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x20L 0 0 x20A && blockAt cells x20L 3 12 tidSt && blockAt cells x20L 4 16 initCall &&
    labelGap cells x20L x21L 6 25

theorem wake_wcSp4In : wcSp4In wakeCells = true := by decide +kernel

/-! ## The nodes -/

/-- **The frame's words** before the TCB's spill: the cell `cA` at `-16`,
main's word `m` at `-8`, the caller's `%rbp` and return address `fr` at
`0`, `8`. -/
def FrV (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (σ : AS) : Prop :=
  σ.slot (-16) = cA ∧ σ.slot (-8) = m ∧ σ.slot 0 = fr.1 ∧ σ.slot 8 = fr.2

/-- `WcClone.FrW` is `FrV` and the TCB at `-32`. -/
theorem frW_of {cA m t : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS} (h : FrV cA m fr σ)
    (h32 : σ.slot (-32) = t) : FrW cA m t fr σ :=
  ⟨h.1, h.2.1, h32, h.2.2.1, h.2.2.2⟩

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (t cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- At `.x20`: `%rax` the TCB `t`. -/
def wcN20 : ND := ⟨lab x20L, oW, fun σ c => c = c0 ∧ σ.regs.get64 .rax = t ∧ FrV cA m fr σ⟩

/-- At the tid store: `%rcx` and `-32` the TCB, `%rax` the reserve's id `-24`. -/
def wcN20s : ND := ⟨lab x20L + 12, oW, fun σ c => c = c0 ∧
  σ.regs.get64 .rcx = t ∧ σ.regs.get64 .rax = σ.slot (-24) ∧ σ.slot (-32) = t ∧ FrV cA m fr σ⟩

/-- Past the tid store: `-32` the TCB. -/
def wcN20p : ND := ⟨lab x20L + 16, oW, fun σ c => c = c0 ∧ σ.slot (-32) = t ∧ FrV cA m fr σ⟩

/-- **The call node**: at `scc_rt_thread_init`, `%rdi` the TCB, `.x21`
pushed at `-72`. -/
def wcNI : ND := ⟨lab Flow.Ret0.ThreadInit.fnL, oC, fun σ c => c = c0 ∧ σ.regs.get64 .rdi = t ∧
  σ.slot (-72) = (lab x21L).toBitVec ∧ FrW cA m t fr σ⟩

end Nodes

/-! ## The edges -/

section Edges

variable {lab : Label → Int64} {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {σ : AS} {c : Ctl}

/-- `x20A` from `.x20` to the tid store. -/
theorem x20A_edge (hJ : (wcN20 lab c0 t cA m fr).J σ c) :
    Hit (wcN20s lab c0 t cA m fr) (arun lab x20A ⟨(wcN20 lab c0 t cA m fr).pc, oW, σ⟩) c := by
  obtain ⟨h0, ht, h16, h8, hf1, hf2⟩ := hJ
  rw [x20A_run]
  refine ⟨by simp only [wcN20, wcN20s], rfl, h0, ?_, ?_, ?_, ?_⟩
  · simp [Reg64s.get64] at ht ⊢; exact ht
  · simp [upd, Reg64s.get64]
  · simp [Reg64s.get64] at ht ⊢; exact ht
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [upd, h16, h8, hf1, hf2]

/-- `initCall` from past the tid store to `scc_rt_thread_init`, `.x21`
pushed, in any layout of `wakeCells`. -/
theorem initCall_edge {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeCells kp) (hJ : (wcN20p (_root_.Executable.labels exe).label c0 t cA m fr).J σ c) :
    Hit (wcNI (_root_.Executable.labels exe).label c0 t cA m fr)
      (arun (_root_.Executable.labels exe).label initCall
        ⟨(wcN20p (_root_.Executable.labels exe).label c0 t cA m fr).pc, oW, σ⟩) c := by
  obtain ⟨h0, h32, h16, h8, hf1, hf2⟩ := hJ
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  have hg := label_labelGap_lays hp hin.2
  rw [initCall_run]
  refine ⟨rfl, rfl, h0, ?_, ?_, ?_⟩
  · simp [Reg64s.get64, h32]
  · simp only [upd_apply, ↓reduceIte, wcN20p, hg, Int64.toBitVec_add, BitVec.add_assoc]; rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [upd, h16, h8, h32, hf1, hf2]

end Edges

/-! ## The owned words at the clone -/

/-- **The owned words at the clone's `syscall`** (`.x21 + 46`): under
`ownG`, with the labels resolved at the canonical base,
`scc_rt_stack_next` holds `32768` and `scc_rt_nthreads` (`a`) `1`
(`own2b` past the second take). -/
theorem ownG_clone {L : RuntimeLayout} {a : BitVec 64} {s : State}
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hpc : pcOf s = (L.lab x21L + 46).toBitVec.toNat) :
    ((⟨L.nextA, 8⟩ : Loc), (32768#64 : BitVec 64).setWidth 128) ∈ ownG L a s ∧
      ((⟨a, 8⟩ : Loc), (1#64 : BitVec 64).setWidth 128) ∈ ownG L a s := by
  obtain ⟨-, -, -, -, -, e6, e7, -, -⟩ := labs_eq (L := L) hlab
  have e6' : L.lab x21L = Int64.ofNat 4203397 := by
    rw [hlab _ 4203397 (by rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel)]
  have h6 : pcOf s = 4203443 := by rw [hpc, e6']; rfl
  have hg : Good2b L s := .inr (.inl (by simp only [inPc, e6, e7, h6]; decide))
  rw [ownG_2b hlab hg, h6]
  have hb : ph2b 4203443 / 4 % 2 = 0 ∧ ph2b 4203443 / 16 % 2 = 0 := by rw [ph2b_eq]; decide +kernel
  simp only [own2b, ownV, hb.1, hb.2]
  simp

end Spike.Lib.X64.WakePh.WcSp4

/-- info: 'Spike.Lib.X64.WakePh.WcSp4.wake_wcSp4In' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4.wake_wcSp4In

/-- info: 'Spike.Lib.X64.WakePh.WcSp4.x20A_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4.x20A_edge

/-- info: 'Spike.Lib.X64.WakePh.WcSp4.initCall_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4.initCall_edge

/-- info: 'Spike.Lib.X64.WakePh.WcSp4.ownG_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcSp4.ownG_clone
