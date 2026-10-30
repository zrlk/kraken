/-
**`scc_rt_park` on AArch64 as one segment**: `hello.w`'s listing of the
park routine (`scc --arch arm -o - Scc/Test/hello.w`, the lines from
`scc_rt_park:` to `scc_rt_unpark:`), composed from its blocks over its
control-flow graph (`Spike/Lib/A64Cfg.lean`), as `scc_rt_print` is in
`Spike/Lib/A64Print.lean`.

    scc_rt_park:
      prologue (frame of 64 bytes, x29/x30 saved at 48/56)
      entry: tp = tpidr_el0 (spilled at 0)
             old = swpal(0, [tp + 16])            -- take the permit
             if old = 1 goto done
      wait:  futex(tp + 16, FUTEX_WAIT_PRIVATE, 0, 0)   -- svc #0, x8 = 98
             swpal(0, [tp + 16])                  -- consume a permit
             epilogue; ret
      done:  epilogue; ret

The region is the function's frame: offsets `[-64, 0)` from the `sp` at
entry. Ghost parameters: the source control `c0` (runtime code: the source
stutters throughout), the caller's `x29`, the return address `ra` and the
thread pointer `tp` (`TPIDR_EL0`, kept by every instruction here). The
specification:

- **entry** (`.e`): pc at `scc_rt_park`, `sp` at offset 0, `x29`,
  `x30 = ra`, `TPIDR_EL0 = tp`;
- **return** (exit `.ret`): pc at `ra`, `sp` at offset 0 again, `x29`,
  `x30` and `TPIDR_EL0` as at entry, the memory outside the frame unchanged.

The permit word at `tp + 16` is the runtime's but not owned by the thread
(the unparking thread swaps it too): both exchanges are `Out.rtRmw` rows
for **any** old value (`rtSwp_nd`), with the memory-side facts of the word
for the new value `0` a hypothesis (`hS`, `StOk`). The futex wait is an
`svc_nd` node under the kernel model (`hK`); its address must be 4-aligned
(`htp4`). The layout facts are hypotheses: each block is at its node's pc
(`Code`), and the prologue falls through to `.0_entry` (`hentry`).
-/
import Spike.Lib.A64Ret0
import Spike.Lib.A64KeepTP
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Flow.Park

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64

open Spike.Lib.A64.Flow.Ret0 (StOk land_ldStep)

/-! ## A non-owned runtime word's exchange -/

section RtSwp

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- `swp<k> Xs, Xt, [Xn]`, 64-bit. -/
def swpDir (k : RmwKind) (rs rt b : XReg) : Directive :=
  .instr ⟨.W64, .SWP k .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩

/-- **A node at a runtime word's `swp<k> Xs, Xt, [Xn]`, the word not owned
by the thread** (another thread may write it): `Xn` holds the word's
address `A`, the new value (`Xs`'s) is one runtime memory may hold there
(`StOk`), and for **every** old value `v` the state after it (`Xt := v`)
lands at a node; the source stutters. The owned variant is `ownSwp_ndW`
(`Spike/Lib/A64Ret0.lean`). Inside `W`, not moved by `K` (`hW`). -/
theorem rtSwp_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : RmwKind} {rs rt b : XReg}
    {A : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [swpDir k rs rt b])
    (hW : NodeW W K exe endPc R F n)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg rs) .W64)) ∧
      ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : Lower.A64.CellAt s (swpDir k rs rt b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, hS, hL⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := Lower.A64.exec_swp hc (by rw [hb']; exact hS.unmapped _ hD)
  rw [hb', Lower.A64.access_agrees (agrees_of_decls hdc _ _)] at hex
  refine .rtRmw k _ _ _ c hex hS.rt hS.mp (.refl c) fun old _ _ => ?_
  refine ⟨fun new hnew => ?_, land_ldStep hF he hn hdc hpc hA hD (hL _)⟩
  simp only [Option.some.injEq] at hnew
  subst hnew
  rw [hA.regs]; exact hS.G

/-- **A node at a non-owned runtime word's `swp<k>`** (`rtSwp_ndW` inside
the trivial predicate, with no outside moves). -/
theorem rtSwp_nd {n : ND} {k : RmwKind} {rs rt b : XReg} {A : BitVec 64} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [swpDir k rs rt b])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧ StOk ms F exe endPc A (σ.regs.getRegOrZr (.low (.reg rs) .W64)) ∧
      ∀ v : BitVec 64, Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill rt, ldStep rt v σ⟩ c) :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (rtSwp_ndW hF hcode NodeW.triv hedge).toSeg

end RtSwp

/-- `swpDir` is what Kraken's parser makes of scc's `swpal`. -/
theorem swpal_parse : parseAArch64("swpal x9, x11, [x10]") = [swpDir .acqRel .X9 .X11 .X10] := by decide

/-- **The futex wait the kernel model decodes**: `x8 = 98`, `x1 =
FUTEX_WAIT_PRIVATE`, a 4-aligned address in `x0`, no timeout (`x3 = 0`). -/
theorem svcCall_futexWait {r : Reg64s} (h8 : r.X8.toNat = 98) (h1 : r.X1.toNat = 128) (h0 : r.X0.toNat % 4 = 0)
    (h3 : r.X3.toNat = 0) : svcCall r = some .futexWait := by
  simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, Scc.Sem.Kernel.futexWaitPrivate,
    h8, h1, h0]
  exact h3

/-! ## The blocks (generated) -/

def b0 : List Directive := parseAArch64("sub sp, sp, #64
str x29, [sp, #48]
str x30, [sp, #56]
add x29, sp, #48")
def b1 : List Directive := parseAArch64("mrs x9, tpidr_el0
str x9, [sp]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")
def b2 : List Directive := parseAArch64("str x11, [sp, #8]
ldr x9, [sp, #8]
movz x10, #1
subs xzr, x9, x10
b.eq .L10_scc_rt_park.2_done")
def b3 : List Directive := parseAArch64("b .L10_scc_rt_park.1_wait")
def b4 : List Directive := parseAArch64("ldr x9, [sp]
movz x10, #16
add x9, x9, x10
str x9, [sp, #16]
ldr x0, [sp, #16]
movz x1, #128
movz x2, #0
movz x3, #0
movz x4, #0
movz x5, #0
movz x8, #98")
def b5 : List Directive := parseAArch64("str x0, [sp, #24]
movz x9, #0
ldr x10, [sp]
add x10, x10, #16")
def b6 : List Directive := parseAArch64("str x11, [sp, #32]
ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret")
def b7 : List Directive := parseAArch64("ldr x29, [sp, #48]
ldr x30, [sp, #56]
add sp, sp, #64
ret")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-64, []⟩
/-- The offsets at entry and return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-64) 0 oE b0
block_spec b1 (-64) 0 oI b1
block_spec b2 (-64) 0 oI b2
block_spec b3 (-64) 0 oI b3
block_spec b4 (-64) 0 oI b4
block_spec b5 (-64) 0 oI b5
block_spec b6 (-64) 0 oI b6
block_spec b7 (-64) 0 oI b7

/-! ## The graph -/

/-- The internal nodes: one per block, the two exchanges and the system
call. -/
inductive PN where
  | e | n1 | swp1 | n2 | n3 | wait | svc | n5 | swp2 | n6 | done

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (x29 ra tp : BitVec 64)

/-- Inside the frame: the source has not moved, the caller's `x29` and the
return address are in their cells, the thread pointer is `tp`. -/
def JI (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- After the thread pointer's spill: `JI`, and `tp` in the frame's cell 0. -/
def JT (σ : AS) (c : Ctl) : Prop := JI c0 x29 ra tp σ c ∧ σ.slot (-64) = tp

/-- At an exchange: `x10` the permit's address, `x9` the new value `0`. -/
def JS (σ : AS) (c : Ctl) : Prop :=
  JT c0 x29 ra tp σ c ∧ σ.regs.X10.toBitVec = tp + 16#64 ∧ σ.regs.X9.toBitVec = 0#64

/-- At entry and return. -/
def JE (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- The pc of the futex wait's `svc`. -/
abbrev pcSvc : Int64 := lab ".L10_scc_rt_park.1_wait" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "scc_rt_park", oE, JE c0 x29 ra tp⟩
  | .n1 => ⟨lab ".L10_scc_rt_park.0_entry", oI, JI c0 x29 ra tp⟩
  | .swp1 => ⟨lab ".L10_scc_rt_park.0_entry" + 4 + 4 + 4 + 4 + 4, oI, JS c0 x29 ra tp⟩
  | .n2 => ⟨lab ".L10_scc_rt_park.0_entry" + 4 + 4 + 4 + 4 + 4 + 4, oI, JT c0 x29 ra tp⟩
  | .n3 => ⟨lab ".L10_scc_rt_park.0_entry" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, JT c0 x29 ra tp⟩
  | .wait => ⟨lab ".L10_scc_rt_park.1_wait", oI, JT c0 x29 ra tp⟩
  | .svc => ⟨pcSvc lab, oI, fun σ c => JT c0 x29 ra tp σ c ∧ σ.regs.X0.toBitVec = tp + 16#64 ∧
      σ.regs.X1 = 128 ∧ σ.regs.X3 = 0 ∧ σ.regs.X8 = 98⟩
  | .n5 => ⟨pcSvc lab + 4, oI, JT c0 x29 ra tp⟩
  | .swp2 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4, oI, JS c0 x29 ra tp⟩
  | .n6 => ⟨pcSvc lab + 4 + 4 + 4 + 4 + 4 + 4, oI, JT c0 x29 ra tp⟩
  | .done => ⟨lab ".L10_scc_rt_park.2_done", oI, JT c0 x29 ra tp⟩

/-- **The exit**: the return to `ra` with `sp`, `x29`, `x30` and the thread
pointer as at entry. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, JE c0 x29 ra tp⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .e).pc b0
  n1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .n1).pc b1
  swp1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .swp1).pc [swpDir .acqRel .X9 .X11 .X10]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .n2).pc b2
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .n3).pc b3
  wait : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .wait).pc b4
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .svc).pc [svcDir]
  n5 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .n5).pc b5
  swp2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .swp2).pc [swpDir .acqRel .X9 .X11 .X10]
  n6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .n6).pc b6
  done : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 x29 ra tp .done).pc b7

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {x29 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, JT, JS, JE, Spike.Lib.upd_apply, Reg64s.getSysReg, svcStep, ldStep, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- Hitting exit `x`. -/
macro "exit " x:term : tactic =>
  `(tactic| (refine .inr ⟨$x, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI, JT, JS, JE, Spike.Lib.upd_apply, Reg64s.getSysReg, svcStep, ldStep, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`scc_rt_park` is one segment** from its entry to its return: the
source stutters throughout, the permit word at `tp + 16` is exchanged with
`0` (twice on the waiting path) for any old value, and the futex wait
returns `0`, `-EAGAIN` or `-EINTR`. -/
theorem seg_park (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -64)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hcode : Code c0 x29 ra tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4) :
    Seg p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c0 x29 ra tp x) s c) := by
  refine fn_seg (N := N _ c0 x29 ra tp) (E := E c0 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.n1
  case n1 => node b1 b1_ok n1; rw [N, b1_run]; hit PN.swp1
  case swp1 =>
    refine rtSwp_nd (A := tp + 16#64) hF (fun s he hn => hcode.swp1 s he hn) fun m σ c _ _ hJ => ?_
    obtain ⟨hT, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, fun v => ?_⟩
    hit PN.n2
  case n2 =>
    node b2 b2_ok n2; rw [N, b2_run]
    split
    · hit PN.done
    · hit PN.n3
  case n3 => node b3 b3_ok n3; rw [N, b3_run]; hit PN.wait
  case wait => node b4 b4_ok wait; rw [N, b4_run]; hit PN.svc
  case svc =>
    refine svc_nd hK hF (fun s he hn => hcode.svc s he hn) (fun σ c hJ => ?_) ?_
    · obtain ⟨hT, h0, h1, h3, h8⟩ := hJ
      refine ⟨.futexWait, svcCall_futexWait (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl)
        (by rw [h3]; rfl), fun v _ => ⟨c, .refl c, ?_⟩⟩
      hit PN.n5
    · rintro s c σ call - ⟨-, h0, h1, h3, h8⟩ hcall
      rw [svcCall_futexWait (by rw [h8]; rfl) (by rw [h1]; rfl) (by rw [← htp4, ← h0]; rfl) (by rw [h3]; rfl)]
        at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
  case n5 => node b5 b5_ok n5; rw [N, b5_run]; hit PN.swp2
  case swp2 =>
    refine rtSwp_nd (A := tp + 16#64) hF (fun s he hn => hcode.swp2 s he hn) fun m σ c _ _ hJ => ?_
    obtain ⟨hT, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, fun v => ?_⟩
    hit PN.n6
  case n6 => node b6 b6_ok n6; rw [N, b6_run]; exit PX.ret
  case done => node b7 b7_ok done; rw [N, b7_run]; exit PX.ret

end Proof

end Spike.Lib.A64.Flow.Park
