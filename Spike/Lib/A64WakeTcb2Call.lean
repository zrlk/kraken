/-
**wake.w's second `scc_rt_alloc_tcb` call site** (AArch64): `wc_main`'s
block at `.sp3`, in its 80-byte frame,

    .L21_wc_main.sp3:
      str x0, [sp, #16]                 -- the reserve's result
      movz x0, #2307
      movk x0, #128, lsl #16            -- x0 = hdr2 = 8390915 (n = 9, m = 2)
      movz x1, #1
      bl scc_rt_alloc_tcb               -- x30 = .sp4
    .L21_wc_main.sp4:

at the listing level: the block, its code in `wakeProg`, its run, and the
nodes around the call. The call's ghost record is `tcb2Q g c0 :=
⟨g, hdr2, 80, c0⟩` (`Q2` by `rfl`), so the TCB the call returns is
`pinA + 104` (`tcb2Q_tcbOf`). The node obligations inside `W` (the
callee by `tcbW_postG` at `tcbPh2a`, the owned words by
`A64WakeOwnGAgree`) are on top of these (`A64WakeWcMid`
reuses the nodes). The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `oW`: `wc_main`'s frame offsets; `tcb2Call`, `tcb2Call_ok`,
  `tcb2Call_run`: the block (`block_spec`).
- `tcb2CallIn`, `wake_tcb2CallIn`: the block at `.sp3`, `.sp4` right after.
- `tcb2Call_x0`, `tcb2Call_x1`, `tcb2Call_x30`, `tcb2Call_pc`: the run's
  arguments, return address and target.
- `tcb2Q`, `tcb2Q_tcbOf`, `tcb2Q_hdrA`: the call's ghost record and its TCB.
- `wcN3`, `wcNC`, `wcN4`: the nodes at `.sp3` (any invariant `J`), at the
  callee's entry (the arguments, `x30 = .sp4`), back at `.sp4` (`x0` the
  TCB).
-/
import Spike.Lib.A64WakeTcb2
import Spike.Lib.Rt.A64RtTcbG

namespace Spike.Lib.A64.WakePh.Tcb2Call

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.AllocTcb (mOf)
open Spike.Lib.A64.Rt (TcbGG hdrA tcbOf)
open Scc.Cert.Rt.A64 (Lays blockAt labelGap label_labelGap)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-! ## The block -/

/-- `wc_main`'s frame offsets (`sp` 80 below the entry's). -/
abbrev oW : SO := ⟨-80, []⟩

/-- **The second call's block** at `.sp3`. -/
def tcb2Call : List Directive := parseAArch64("str x0, [sp, #16]
movz x0, #2307
movk x0, #128, lsl #16
movz x1, #1
bl scc_rt_alloc_tcb")

block_spec tcb2Call (-80) 0 oW tcb2Call

/-- **The block's code in `wakeProg`**: at `.sp3`, `.sp4` right after. -/
def tcb2CallIn (prog : List Directive) : Bool :=
  blockAt prog ".L21_wc_main.sp3" 0 tcb2Call && labelGap prog ".L21_wc_main.sp3" ".L21_wc_main.sp4" 5

theorem wake_tcb2CallIn : tcb2CallIn wakeProg = true := by decide +kernel

/-! ## The run -/

section Run

variable (lab : Label → Int64) (pc : Int64) (σ : Spike.Lib.A64.Flow.AS)

/-- The run's `x0` is the header `hdr2`. -/
theorem tcb2Call_x0 : (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.X0.toBitVec = hdr2 := by
  rw [tcb2Call_run]; rfl

/-- The run's `x1` is `1` (`k`). -/
theorem tcb2Call_x1 : (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.X1.toBitVec = 1#64 := by
  rw [tcb2Call_run]; rfl

/-- The run ends at the callee's label, the offsets unchanged. -/
theorem tcb2Call_pc : (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).pc = lab "scc_rt_alloc_tcb" ∧
    (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).so = oW := by
  rw [tcb2Call_run]; exact ⟨rfl, rfl⟩

/-- The run keeps `sp`, `x29` and the frame's slots but `-64` (`[sp, #16]`). -/
theorem tcb2Call_keep : (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.SP = σ.regs.SP ∧
    (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).σ.regs.X29 = σ.regs.X29 ∧
    (Spike.Lib.A64.Flow.arun lab tcb2Call ⟨pc, oW, σ⟩).σ.slot = Spike.Lib.upd σ.slot (-64) σ.regs.X0.toBitVec := by
  rw [tcb2Call_run]; exact ⟨rfl, rfl, rfl⟩

end Run

/-- **The return address is `.sp4`** in any layout of `wakeProg`, from
`.sp3`. -/
theorem tcb2Call_x30 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeProg kp) (σ : Spike.Lib.A64.Flow.AS) :
    (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label tcb2Call
        ⟨(_root_.Executable.labels exe).label ".L21_wc_main.sp3", oW, σ⟩).σ.regs.X30.toBitVec =
      ((_root_.Executable.labels exe).label ".L21_wc_main.sp4").toBitVec := by
  have hin := wake_tcb2CallIn
  simp only [tcb2CallIn, Bool.and_eq_true] at hin
  rw [label_labelGap hp hin.2, tcb2Call_run]
  simp only [Spike.Lib.A64.Flow.Ret0.ofInt_bmod]
  rw [show Int64.ofNat (4 * 5) = 20 from rfl, Int64.toBitVec_add,
    show ∀ y : Int, y + 4 + 4 + 4 + 4 + 4 = y + 20 from fun y => by omega, BitVec.ofInt_add,
    Spike.Lib.int64_ofInt_toInt]; rfl

/-! ## The call's ghost record and the nodes -/

/-- **The second call's ghost record**: the header `hdr2`, the counter's
old value `80` (the first TCB's eighty bytes). -/
def tcb2Q (g : Ret0.AllocTcb.G) (c0 : Ctl) : TcbGG := ⟨g, hdr2, 80#64, c0⟩

/-- `tcb2Q`'s header word: `pinned + 96`. -/
theorem tcb2Q_hdrA (lab : Label → Int64) (g : Ret0.AllocTcb.G) (c0 : Ctl) :
    hdrA lab (tcb2Q g c0) = Ret0.pinA lab + 96#64 := by
  show Ret0.pinA lab + 80#64 + mOf hdr2 <<< 3 = _
  rw [mOf_hdr2, BitVec.add_assoc]; rfl

/-- **`tcb2Q`'s TCB**: `pinned + 104`. -/
theorem tcb2Q_tcbOf (lab : Label → Int64) (g : Ret0.AllocTcb.G) (c0 : Ctl) :
    tcbOf lab (tcb2Q g c0) = Ret0.pinA lab + 104#64 := by
  show hdrA lab (tcb2Q g c0) + 8#64 = _
  rw [tcb2Q_hdrA, BitVec.add_assoc]; rfl

section Nodes

variable (lab : Label → Int64)

/-- **At `.sp3`**, in `wc_main`'s frame, the source control `c0` and any
invariant `J` of the state. -/
def wcN3 (J : Spike.Lib.A64.Flow.AS → Prop) (c0 : Ctl) : ND := ⟨lab ".L21_wc_main.sp3", oW, fun σ c => c = c0 ∧ J σ⟩

/-- **The call node**: at `scc_rt_alloc_tcb`'s label, its arguments `hdr2`
and `1`, the return address `.sp4`. -/
def wcNC (c0 : Ctl) : ND := ⟨lab Ret0.AllocTcb.fnL, oW, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = hdr2 ∧ σ.regs.X1.toBitVec = 1#64 ∧
  σ.regs.X30.toBitVec = (lab ".L21_wc_main.sp4").toBitVec⟩

/-- **Back at `.sp4`**: `x0` the TCB of `tcb2Q g c0`. -/
def wcN4 (g : Ret0.AllocTcb.G) (c0 : Ctl) : ND := ⟨lab ".L21_wc_main.sp4", oW, fun σ c => c = c0 ∧
  σ.regs.X0.toBitVec = tcbOf lab (tcb2Q g c0)⟩

end Nodes

/-- **The block's run from `wcN3` meets `wcNC`** (pc, offsets, invariant). -/
theorem tcb2Call_wcNC {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeProg kp) {J : Spike.Lib.A64.Flow.AS → Prop} {c0 : Ctl} {σ : Spike.Lib.A64.Flow.AS} {c : Ctl}
    (hJ : (wcN3 (_root_.Executable.labels exe).label J c0).J σ c) :
    let r := Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label tcb2Call
      ⟨(wcN3 (_root_.Executable.labels exe).label J c0).pc, oW, σ⟩
    r.pc = (wcNC (_root_.Executable.labels exe).label c0).pc ∧
      r.so = (wcNC (_root_.Executable.labels exe).label c0).o ∧
      (wcNC (_root_.Executable.labels exe).label c0).J r.σ c :=
  ⟨(tcb2Call_pc _ _ _).1, (tcb2Call_pc _ _ _).2,
    hJ.1, tcb2Call_x0 _ _ _, tcb2Call_x1 _ _ _, tcb2Call_x30 hp σ⟩

/-- info: 'Spike.Lib.A64.WakePh.Tcb2Call.tcb2Call_wcNC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcb2Call_wcNC

/-- info: 'Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q_tcbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tcb2Q_tcbOf

/-- info: 'Spike.Lib.A64.WakePh.Tcb2Call.wake_tcb2CallIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wake_tcb2CallIn

end Spike.Lib.A64.WakePh.Tcb2Call
