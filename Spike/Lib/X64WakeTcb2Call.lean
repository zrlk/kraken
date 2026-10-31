/-
**wake.w's second `scc_rt_alloc_tcb` call site** (x86-64; twin of
`Spike/Lib/A64WakeTcb2Call.lean`): `wc_main`'s block at `.x19`, in its
frame (`subq $64` after `pushq %rbp`; `%rsp` at `-64`, `%rbp` at `0`),

    .Lwc_main.x19:
      movq %rax, -24(%rbp)              -- the reserve's result
      movq $8390915, %rdi               -- %rdi = hdr2 (n = 9, m = 2)
      movq $1, %rsi
      call scc_rt_alloc_tcb             -- pushes .x20 at -72
    .Lwc_main.x20:

at the listing level: the block, its code in `wakeCells`, its run, and the
nodes around the call. The call's ghost record is `tcb2Q g c0 :=
⟨g, hdr2, 80, c0⟩`, so the TCB the call returns is `pinA + 104`
(`tcb2Q_tcbOf`).

Where x86-64 differs from AArch64: the return address is not a register
but the word the `call` pushes, at offset `-72` (`tcb2Call_ra`, in place of
`tcb2Call_x30`); the run ends at the offsets `oC` (`%rsp` at `-72`), so the
call node `wcNC` is at `oC` (A64's is at `oW`). The arguments are `%rdi`,
`%rsi` (`tcb2Call_rdi`, `tcb2Call_rsi` for A64's `tcb2Call_x0`,
`tcb2Call_x1`), the result `%rax`. The block is checked by byte offsets
(`blockAtB`, `labelGapB`).

- `oW`, `oC`: `wc_main`'s frame offsets, before and after the `call`;
  `tcb2Call`, `tcb2Call_ok`, `tcb2Call_run`: the block (`block_spec`).
- `tcb2CallIn`, `wake_tcb2CallIn`: the block at `.x19`, `.x20` 23 bytes
  after.
- `tcb2Call_rdi`, `tcb2Call_rsi`, `tcb2Call_pc`, `tcb2Call_keep`,
  `tcb2Call_ra`: the run's arguments, target, kept state and return address.
- `tcb2Q`, `tcb2Q_tcbOf`, `tcb2Q_hdrA`: the call's ghost record and its TCB.
- `wcN3`, `wcNC`, `wcN4`: the nodes at `.x19` (any invariant `J`), at the
  callee's entry (the arguments, `.x20` pushed), back at `.x20` (`%rax` the
  TCB).
-/
import Spike.Lib.X64WakeTcb2
import Spike.Lib.Rt.X64RtTcbG

namespace Spike.Lib.X64.WakePh.Tcb2Call

open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Ret0.AllocTcb (mOf)
open Spike.Lib.X64.Rt (TcbGG hdrA tcbOf)
open Scc.Cert.Rt.X64 (Lays blockAtB labelGapB label_labelGapB)
open SccCode (wakeCells)

/-! ## The block -/

/-- `wc_main`'s frame offsets (`%rsp` 64 below `%rbp`, the saved `%rbp`). -/
abbrev oW : SO := ⟨-64, [(.rbp, 0)]⟩

/-- The offsets after the `call` (the return address at `-72`). -/
abbrev oC : SO := ⟨-72, [(.rbp, 0)]⟩

/-- **The second call's block** at `.x19`. -/
def tcb2Call : List (Directive × Nat) := (parse("movq %rax, -24(%rbp)
movq $8390915, %rdi
movq $1, %rsi
call scc_rt_alloc_tcb")).zip [4, 7, 7, 5]

block_spec tcb2Call (-72) 16 oW tcb2Call

/-- **The block's code in `wakeCells`**: at `.x19`, `.x20` right after. -/
def tcb2CallIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.x19" 0 tcb2Call && labelGapB cells ".Lwc_main.x19" ".Lwc_main.x20" 23

theorem wake_tcb2CallIn : tcb2CallIn wakeCells = true := by decide +kernel

/-! ## The run -/

section Run

variable (lab : Label → Int64) (pc : Int64) (σ : AS)

/-- The run's `%rdi` is the header `hdr2`. -/
theorem tcb2Call_rdi : (arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.rdi.toBitVec = hdr2 := by
  rw [tcb2Call_run]; rfl

/-- The run's `%rsi` is `1` (`k`). -/
theorem tcb2Call_rsi : (arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.rsi.toBitVec = 1#64 := by
  rw [tcb2Call_run]; rfl

/-- The run ends at the callee's label, `%rsp` past the return address. -/
theorem tcb2Call_pc : (arun lab tcb2Call ⟨pc, oW, σ⟩).pc = lab "scc_rt_alloc_tcb" ∧
    (arun lab tcb2Call ⟨pc, oW, σ⟩).so = oC := by
  rw [tcb2Call_run]; exact ⟨rfl, rfl⟩

/-- The run moves `%rsp` 8 down, keeps `%rbp`, and writes the frame's
`-24` (the reserve's result) and `-72` (the return address `pc + 23`). -/
theorem tcb2Call_keep : (arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.rsp.toBitVec = σ.regs.rsp.toBitVec - 8#64 ∧
    (arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.rbp = σ.regs.rbp ∧
    (arun lab tcb2Call ⟨pc, oW, σ⟩).σ.slot =
      upd (upd σ.slot (-24) σ.regs.rax.toBitVec) (-72) (pc.toBitVec + 23#64) := by
  rw [tcb2Call_run]; exact ⟨rfl, rfl, rfl⟩

end Run

/-- **The return address is `.x20`** in any layout of `wakeCells`, from
`.x19`. -/
theorem tcb2Call_ra {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeCells kp) (σ : AS) :
    (arun (_root_.Executable.labels exe).label tcb2Call
        ⟨(_root_.Executable.labels exe).label ".Lwc_main.x19", oW, σ⟩).σ.slot (-72) =
      ((_root_.Executable.labels exe).label ".Lwc_main.x20").toBitVec := by
  have hin := wake_tcb2CallIn
  simp only [tcb2CallIn, Bool.and_eq_true] at hin
  rw [label_labelGapB hp hin.2, (tcb2Call_keep _ _ _).2.2, Int64.toBitVec_add]
  simp only [upd_apply, ↓reduceIte]; rfl

/-! ## The call's ghost record and the nodes -/

/-- **The second call's ghost record**: the header `hdr2`, the counter's
old value `80` (the first TCB's eighty bytes). -/
def tcb2Q (g : Flow.Ret0.AllocTcb.G) (c0 : Ctl) : TcbGG := ⟨g, hdr2, 80#64, c0⟩

/-- `tcb2Q`'s header word: `pinned + 96`. -/
theorem tcb2Q_hdrA (lab : Label → Int64) (g : Flow.Ret0.AllocTcb.G) (c0 : Ctl) :
    hdrA lab (tcb2Q g c0) = Flow.Ret0.pinA lab + 96#64 := by
  show Flow.Ret0.pinA lab + 80#64 + mOf hdr2 <<< 3 = _
  rw [mOf_hdr2, BitVec.add_assoc]; rfl

/-- **`tcb2Q`'s TCB**: `pinned + 104`. -/
theorem tcb2Q_tcbOf (lab : Label → Int64) (g : Flow.Ret0.AllocTcb.G) (c0 : Ctl) :
    tcbOf lab (tcb2Q g c0) = Flow.Ret0.pinA lab + 104#64 := by
  show hdrA lab (tcb2Q g c0) + 8#64 = _
  rw [tcb2Q_hdrA, BitVec.add_assoc]; rfl

section Nodes

variable (lab : Label → Int64)

/-- **At `.x19`**, in `wc_main`'s frame, the source control `c0` and any
invariant `J` of the state. -/
def wcN3 (J : AS → Prop) (c0 : Ctl) : ND := ⟨lab ".Lwc_main.x19", oW, fun σ c => c = c0 ∧ J σ⟩

/-- **The call node**: at `scc_rt_alloc_tcb`'s label, its arguments `hdr2`
and `1`, the return address `.x20` pushed at `-72`. -/
def wcNC (c0 : Ctl) : ND := ⟨lab Flow.Ret0.AllocTcb.fnL, oC, fun σ c => c = c0 ∧
  σ.regs.rdi.toBitVec = hdr2 ∧ σ.regs.rsi.toBitVec = 1#64 ∧
  σ.slot (-72) = (lab ".Lwc_main.x20").toBitVec⟩

/-- **Back at `.x20`**: `%rax` the TCB of `tcb2Q g c0`. -/
def wcN4 (g : Flow.Ret0.AllocTcb.G) (c0 : Ctl) : ND := ⟨lab ".Lwc_main.x20", oW, fun σ c => c = c0 ∧
  σ.regs.rax.toBitVec = tcbOf lab (tcb2Q g c0)⟩

end Nodes

/-- **The block's run from `wcN3` meets `wcNC`** (pc, offsets, invariant). -/
theorem tcb2Call_wcNC {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeCells kp) {J : AS → Prop} {c0 : Ctl} {σ : AS} {c : Ctl}
    (hJ : (wcN3 (_root_.Executable.labels exe).label J c0).J σ c) :
    let r := arun (_root_.Executable.labels exe).label tcb2Call
      ⟨(wcN3 (_root_.Executable.labels exe).label J c0).pc, oW, σ⟩
    r.pc = (wcNC (_root_.Executable.labels exe).label c0).pc ∧
      r.so = (wcNC (_root_.Executable.labels exe).label c0).o ∧
      (wcNC (_root_.Executable.labels exe).label c0).J r.σ c :=
  ⟨(tcb2Call_pc _ _ _).1, (tcb2Call_pc _ _ _).2,
    hJ.1, tcb2Call_rdi _ _ _, tcb2Call_rsi _ _ _, tcb2Call_ra hp σ⟩

end Spike.Lib.X64.WakePh.Tcb2Call

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.wake_tcb2CallIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.wake_tcb2CallIn

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_rdi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_rdi

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_rsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_rsi

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_pc

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_keep

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_ra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_ra

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_hdrA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_hdrA

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_tcbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_tcbOf

/-- info: 'Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_wcNC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Tcb2Call.tcb2Call_wcNC
