/-
**Main's spin-wait on x64**: the x64 twin of
`Spike/Lib/A64WaitLoop.lean`. `wc_waitLoop` of `wake.w`'s listing (the
lines from `wc_waitLoop:` to `.size wc_waitLoop` in `SccCode.wakeAsm`) as
one segment with the load-or-stutter row (`SegL`, `Spike/Lib/SegLd.lean`),
composed from its blocks over its control-flow graph
(`Spike/Lib/X64CfgL.lean`).

    wc_waitLoop(c = %rdi):
      prologue (push %rbp; stack check against %fs:8; frame of 16; c at -8(%rbp))
      d = movq (c)                                -- the (TSO acquire) load of the flag
      if d = 1 then return 0
      park (call scc_rt_park); tail call wc_waitLoop(c)
      stk: save the argument registers; call scc_rt_morestack; goto the check

The source is `let d = load acq c in e` (its control `c0`). As on AArch64
**the source never parks**: it stutters at its load until the target's
`movq (%rcx), %rax` reads `1` (`ldSt_nd`), and the park and the tail call
back into the prologue are stutters as well. So on the way back to the
entry (`.e`) the source is at `c0`, and the return exit (`.ret`) has the
source past its load (`Past`).

The region is `[-88, 8)` from the `%rsp` at entry (the return address at
`[0, 8)`): the frame (`[-24, 0)`, the saved `%rbp` at `-8`, `c` at `-16`),
the return address the park call pushes at `-32` and the park routine's
frame below it (`[-56, 8)` from the call's `%rsp`, `Spike/Lib/X64Park.lean`).
**The frame does not move** (unlike AArch64's, whose stack grow path is a
call): the park call returns into the same frame and the tail call
re-enters the prologue at the same `%rsp`, so the region, the frame
condition and the caller's `%rbp` are fixed (no ghost; `fn_seg_gL` is used
at `Unit`). The stack check never fails: the limit word's facts (`hlim`,
`Ret0.LimOk` at `tp + 8` for the frame's `%rsp`) are a hypothesis, so the
stack grow path (`.stk`, `.x17`) has no node.

Ghost parameters: the source control `c0` with its load's binder `x`,
continuation `e` and the type `ty` of its address, the words the source may
read as `1` (`Rd`), the address `A` of the flag (in `%rdi` at entry), the
caller's `%rbp` `fp`, the return address `ra`, the thread pointer `tp`
(`fsBase`, kept everywhere: `scc_rt_park` needs it) and the `%rsp` at entry
`sp` (instantiated with `R.addr 0`). Entry (`.e`): `%rsp = sp` at offset 0,
`%rdi = A`, `%rbp = fp`, the return address `ra` at offset 0, the source at
`c0`; the tail call comes back to it. Return (exit `.ret`): pc at `ra`,
`%rsp` at offset 8 (`sp + 8`), `%rbp = fp`, `%rax = 0`, the source past its
load.

The code is checked once per program (`waitIn`, by the kernel for
`SccCode.wakeCells`: `wake_waitIn`); the theorems take any valid layout of
cells passing it. `seg_waitLoop` takes the park call as a hypothesis
(`hpark`); `seg_parkCall` discharges it with
`Spike.Lib.X64.Flow.Park.seg_park` through `call_nd_F`, and `seg_waitLoopP`
is `seg_waitLoop` with it.
-/
import Spike.Lib.X64Park
import Spike.Lib.X64CfgL
import Spike.Lib.X64CodeSegs
import Spike.Lib.X64Call
import Spike.Lib.X64WakeCode
import Spike.Lib.SegCommon
import Kraken.X64.Parser

namespace Spike.Lib.X64.WaitLoop

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk seg_one)
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-! ## The blocks (generated) -/

def b4 : List (Directive × Nat) := (parse("movq -8(%rbp), %rcx")).zip [4]
def b5 : List (Directive × Nat) := (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rax
movq $1, %rcx
cmpq %rcx, %rax
je .Lwc_waitLoop.then1")).zip [4, 4, 7, 3, 2]
def b6 : List (Directive × Nat) := (parse("jmp .Lwc_waitLoop.else2")).zip [2]
def b7 : List (Directive × Nat) := (parse("movq $0, %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [7, 3, 1, 1]
def b8 : List (Directive × Nat) := (parse("call scc_rt_park")).zip [5]
def b9 : List (Directive × Nat) := (parse("movq -8(%rbp), %rdi
movq %rbp, %rsp
popq %rbp
jmp wc_waitLoop")).zip [4, 3, 1, 2]

/-- The load between `b4` and `b5`. -/
theorem ld_parse : ((parse("movq (%rcx), %rax")).zip [3] : List (Directive × Nat)) = [(ldDir .rcx 0 .rax, 3)] := by
  decide

/-- The offsets inside the frame: `%rsp` at the frame's base, `%rbp` at the
saved `%rbp`. -/
abbrev oI : SO := ⟨-24, [(.rbp, -8)]⟩
/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets after the park call's return (`%rbp` from the invariant). -/
abbrev oP : SO := ⟨-24, []⟩

block_spec b4 (-88) 8 oI b4
block_spec b5 (-88) 8 oI b5
block_spec b6 (-88) 8 oI b6
block_spec b7 (-88) 8 oI b7
block_spec b8 (-88) 8 oI b8
block_spec b9 (-88) 8 oI b9

/-! ## The code -/

/-- **`wc_waitLoop` in `cells`**: the stack-checked prologue (frame of 16,
`%rdi` stored at `-8(%rbp)`), the blocks and the load at their labels, and
`.x16` right after the park call. -/
def waitIn (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "wc_waitLoop" ".Lwc_waitLoop.chk" ".Lwc_waitLoop.entry" 16 8 ".Lwc_waitLoop.stk" 5 9 3 2 4
      [(.rdi, -8, 4)] &&
    blockAtB cells ".Lwc_waitLoop.entry" 0 b4 && blockAtB cells ".Lwc_waitLoop.entry" 4 [(ldDir .rcx 0 .rax, 3)] &&
    blockAtB cells ".Lwc_waitLoop.entry" 7 b5 && blockAtB cells ".Lwc_waitLoop.entry" 27 b6 &&
    blockAtB cells ".Lwc_waitLoop.then1" 0 b7 && blockAtB cells ".Lwc_waitLoop.else2" 0 b8 &&
    blockAtB cells ".Lwc_waitLoop.x16" 0 b9 && labelGapB cells ".Lwc_waitLoop.else2" ".Lwc_waitLoop.x16" 5

theorem wake_waitIn : waitIn SccCode.wakeCells = true := by decide +kernel

/-! ## The graph -/

/-- The internal nodes: the entry, one per block, and the load. -/
inductive PN where
  | e | entry | ld | n5 | n6 | then1 | else2 | park | x16

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 : Ctl) (x : String) (e : Expr) (ty : Ty) (Rd : TermRun.Word → Prop)
  (A fp ra tp sp : BitVec 64)

/-- The source past its load: `x` bound to a word of `Rd`. -/
def Past (c : Ctl) : Prop := ∃ w', Rd w' ∧ c = ⟨e, (x, loadTy ty, [w']) :: c0.env, none⟩

/-- At entry: the source at its load, `%rdi` the flag's address, the
caller's `%rbp`, the return address at offset 0, `%rsp`, the thread pointer. -/
def JE (σ : AS) (c : Ctl) : Prop :=
  c = c0 ∧ σ.regs.rdi.toBitVec = A ∧ σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ σ.regs.rsp.toBitVec = sp ∧
    σ.regs.fsBase.toBitVec = tp

/-- Inside the frame: the caller's `%rbp`, the return address and the flag's
address in their cells. -/
def JF (σ : AS) : Prop := σ.slot (-8) = fp ∧ σ.slot 0 = ra ∧ σ.slot (-16) = A

/-- Inside the frame: `JF`, the thread pointer, `%rbp` at the saved `%rbp`. -/
def JK (σ : AS) : Prop := JF A fp ra σ ∧ σ.regs.fsBase.toBitVec = tp ∧ σ.regs.rbp.toBitVec = sp - 8#64

/-- Inside the frame, the source at its load. -/
def JI (σ : AS) (c : Ctl) : Prop := c = c0 ∧ JK A fp ra tp sp σ

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab "wc_waitLoop", oE, JE c0 A fp ra tp sp⟩
  | .entry => ⟨lab ".Lwc_waitLoop.entry", oI, JI c0 A fp ra tp sp⟩
  | .ld => ⟨lab ".Lwc_waitLoop.entry" + 4, oI, fun σ c => JI c0 A fp ra tp sp σ c ∧ σ.regs.get64 .rcx = A⟩
  | .n5 => ⟨lab ".Lwc_waitLoop.entry" + 7, oI, fun σ c => JK A fp ra tp sp σ ∧
      ((σ.regs.rax.toBitVec = 1#64 ∧ Past c0 x e ty Rd c) ∨ (σ.regs.rax.toBitVec ≠ 1#64 ∧ c = c0))⟩
  | .n6 => ⟨lab ".Lwc_waitLoop.entry" + 27, oI, JI c0 A fp ra tp sp⟩
  | .then1 => ⟨lab ".Lwc_waitLoop.then1", oI, fun σ c => JK A fp ra tp sp σ ∧ Past c0 x e ty Rd c ∧
      σ.slot (-24) = 1#64⟩
  | .else2 => ⟨lab ".Lwc_waitLoop.else2", oI, JI c0 A fp ra tp sp⟩
  | .park => ⟨lab "scc_rt_park", ⟨-32, [(.rbp, -8)]⟩, fun σ c => JI c0 A fp ra tp sp σ c ∧
      σ.slot (-32) = (lab ".Lwc_waitLoop.else2").toBitVec + 5#64⟩
  | .x16 => ⟨lab ".Lwc_waitLoop.x16", oP, JI c0 A fp ra tp sp⟩

/-- **The exit**: back at the caller, `%rsp` past the return address, the
source past its load, `%rax = 0`, `%rbp` and the thread pointer as at entry;
the flag's address and the loaded `1` still in the (popped) frame's cells
(`-16`, `-24`: where the source's environment is placed until main's exit). -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, ⟨8, []⟩, fun σ c => Past c0 x e ty Rd c ∧ σ.regs.rax.toBitVec = 0#64 ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.regs.fsBase.toBitVec = tp ∧ σ.regs.rsp.toBitVec = sp + 8#64 ∧
      σ.slot (-16) = A ∧ σ.slot (-24) = 1#64⟩

end Spec

/-- The words the source may read as `1`. -/
abbrev RdOne {ms : MemSide isa} (lbl : WeakMem.AllocLabel → Option Nat) : TermRun.Word → Prop :=
  fun w' => ms.rd w' ∧ ValRep lbl w'.val 1

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
  {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

omit [Executable.ValidLayout exe] in
/-- **`%rbp`'s offset from an invariant fact** (as `Flow.Hello1.At.rbp_addr`):
at a node whose invariant puts `%rbp` at `R.addr k`, `%rbp` is at offset
`k`. -/
theorem At.rbpOf {R : Region} {F : MachineData → Prop} {pc : Int64}
    {sp k : Int} {rs : List (Reg64 × Int)} {J : AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F ⟨pc, ⟨sp, rs⟩, J⟩ s c) (hJ : ∀ σ c, J σ c → σ.regs.get64 .rbp = R.addr k) :
    At exe endPc R F ⟨pc, ⟨sp, (.rbp, k) :: rs⟩, J⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ'⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, ⟨hA.regs, hA.zmms, hA.status, fun r k' hk => ?_, hA.slot⟩, hD, hJ'⟩
  unfold SO.get at hk
  split at hk
  · rename_i hr; subst hr; cases hk; exact hA.so .rsp sp (SO.get_rsp _)
  · rename_i hr
    simp only [lk] at hk
    split at hk
    · rename_i hb; subst hb; cases hk; exact hJ σ c hJ'
    · exact hA.so r k' (by simp only [SO.get, hr, ↓reduceIte]; exact hk)

/-- The saved `%rbp`'s address. -/
theorem addr0_sub8 (R : Region) : R.addr 0 - 8#64 = R.addr (-8) := by
  rw [show (-8 : Int) = 0 - 8 from rfl, Region.addr_sub]; rfl

omit [Executable.ValidLayout exe] in
/-- `scc_rt_park`'s code does not depend on its ghosts (its nodes' pcs do
not). -/
theorem _root_.Spike.Lib.X64.Flow.Park.Code.ghost {c0 c0' : Ctl}
    {rbp0 ra tp rbp0' ra' tp' : BitVec 64} (h : Park.Code c0 rbp0 ra tp exe endPc) :
    Park.Code c0' rbp0' ra' tp' exe endPc :=
  ⟨h.e, h.fsl, h.n1, h.xchg1, h.n2, h.n3, h.wait, h.sys, h.n5, h.xchg2, h.n6, h.done⟩

set_option hygiene false in
/-- A block node at `l + k`: the block, its `okBlk`, its code; the edge is
left. -/
local macro "node " b:ident ok:ident hc:ident : tactic =>
  `(tactic| refine seg_fixL () (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend $hc (by first | rfl | exact ofNat_zero' _)) fun σ c hJ => ⟨c, .refl c, ?_⟩).toL)

/-- Hitting node `j`. -/
local macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, JK, JF, JE, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, ownStep, Reg64s.set64, Reg64s.get64]))

/-- **`wc_waitLoop` is one segment with the load-or-stutter row** from its
entry to its return, in any valid layout of cells with `waitIn`. The source
stutters at its load `c0` until the `movq` reads `1`, and then takes it
(`Past`); it never parks. The park call is a hypothesis (`hpark`, from the
call node at `scc_rt_park` back to `.x16`): `seg_parkCall`. -/
theorem seg_waitLoop (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (R.addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hpark : Seg p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .park))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .x16))) :
    SegL p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .e))
      (fun s c => ∃ y, At exe endPc R F (E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0) y) s c) := by
  have hin' := hin
  simp only [waitIn, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, hg⟩ := hin'
  refine (fn_seg_gL (Rg := fun _ : Unit => R) (Fg := fun _ => F)
    (N := fun _ => N _ c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0))
    (E := fun _ => E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0)) (fun _ i => ?_) () PN.e).mono_post
    fun _ _ ⟨_, y, h⟩ => ⟨y, h⟩
  cases i
  case e =>
    refine seg_fixL () (seg_given PN.entry (prologue_seg_of hp hend hpro (by decide) hF hR
      (by have : (16 : Int64).toInt = 16 := by decide
          omega) (by omega) (by decide) rfl (by show SO.le oI (oF 16) = true; decide) ?_)).toL
    rintro σ c ⟨rfl, hdi, hbp, h0, hsp, htp⟩
    rw [htp]
    refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨by rw [hsp]; exact hlim.room v hv, fun σ' hr hs => ?_⟩⟩
    refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hs]; simp [xStSlots, xS1, upd_apply, hbp]
    · rw [hs]; simp [xStSlots, xS1, upd_apply, h0]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
  case entry => node b4 b4_ok h4; rw [N, b4_run]; hit PN.ld
  case ld =>
    refine seg_fixL () (ldSt_nd (V := 1) (by decide) hF (code_field hp hend hld rfl) hdm ?_)
    rintro m σ c - - ⟨⟨rfl, hK⟩, hcx⟩
    refine ⟨by simp [bAddr, hcx], x, a, e, ty, w, hterm, hev, hval, htag, fun v hv => ?_,
      fun v w' hv hr hr' => ?_⟩
    · refine .inl ⟨PN.n5, ?_, by show SO.le oI (oI.kill .rax) = true; decide, ?_, .inr ⟨?_, rfl⟩⟩
      · show _ + 7 = _ + 4 + Int64.ofNat 3; rw [Int64.add_assoc]; rfl
      · simpa [JK, JF, ownStep, Reg64s.set64] using hK
      · simp only [ownStep, Reg64s.set64, UInt64.toBitVec_ofBitVec]
        intro h; exact hv (by rw [h]; rfl)
    · refine .inl ⟨PN.n5, ?_, by show SO.le oI (oI.kill .rax) = true; decide, ?_, .inl ⟨?_, w', ⟨hr, hr'⟩, rfl⟩⟩
      · show _ + 7 = _ + 4 + Int64.ofNat 3; rw [Int64.add_assoc]; rfl
      · simpa [JK, JF, ownStep, Reg64s.set64] using hK
      · simp only [ownStep, Reg64s.set64, UInt64.toBitVec_ofBitVec]
        exact BitVec.eq_of_toNat_eq (by rw [hv]; rfl)
  case n5 =>
    node b5 b5_ok h5; rw [N, b5_run]
    obtain ⟨hK, h | h⟩ := hJ
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [h.1]; rfl))]
      hit PN.then1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h'; exact h.1 (by bv_decide)))]
      hit PN.n6
  case n6 => node b6 b6_ok h6; rw [N, b6_run]; hit PN.else2
  case then1 =>
    node b7 b7_ok h7; rw [N, b7_run]
    obtain ⟨⟨⟨h8', h0, h16⟩, htp, hbp⟩, hP, h24⟩ := hJ
    refine .inr ⟨PX.ret, ?_, rfl, hP, ?_, ?_, ?_, ?_, h16, h24⟩
    · simp [E, h0]
    · simp [Reg64s.set64]
    · simp [Reg64s.set64, h8']
    · simp [Reg64s.set64, htp]
    · simp only [Reg64s.set64, UInt64.toBitVec_ofBitVec]; rw [hbp]; bv_omega
  case else2 => node b8 b8_ok h8; rw [N, b8_run]; hit PN.park
  case park => exact seg_fixL () (seg_given PN.x16 hpark).toL
  case x16 =>
    refine seg_fixL () ((seg_nd (n := ⟨_, oI, _⟩) (by simp [b9]) b9_ok hF hR hlo hhi
      (code_field hp hend h9 (ofNat_zero' _)) fun σ c hJ => ⟨c, .refl c, ?_⟩).mono_pre
      fun _ _ h => At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.2, addr0_sub8]).toL
    rw [b9_run]
    obtain ⟨rfl, ⟨h8', h0, h16⟩, htp, hbp⟩ := hJ
    refine .inl ⟨PN.e, rfl, rfl, rfl, ?_, ?_, h0, ?_, ?_⟩
    · simp [Reg64s.set64, h16]
    · simp [Reg64s.set64, h8']
    · simp only [Reg64s.set64, UInt64.toBitVec_ofBitVec]; rw [hbp]; bv_omega
    · simp [Reg64s.set64, htp]

/-! ## The park call -/

/-- **The call of `scc_rt_park`** (`call_nd_F` with `Park.seg_park`, frame
`[-56, 8)` from the call's `%rsp`, which is at offset `-32`): from `.park`
back to `.x16`, the frame unmoved. The ghosts of `seg_park` are the source
control, `%rbp` and the return address at the call (the thread pointer is
`tp`, in `JK`). The facts it needs are hypotheses: the kernel model (`hK`),
the TCB's self pointer (`hT`, `hown`), the permit word's (`hS`, `htp4`), the
park routine's code (`hpcode`, for any of its ghosts: `Park.Code.ghost`)
and its prologue's fall-through (`hpentry`). -/
theorem seg_parkCall (hp : Lays exe cells kp) (hin : waitIn cells = true) {Rd : TermRun.Word → Prop}
    {sp : BitVec 64} {c0' : Ctl} {rbp0' ra' tp' : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8) :
    Seg p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .park))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .x16)) := by
  have hg : labelGapB cells ".Lwc_waitLoop.else2" ".Lwc_waitLoop.x16" 5 = true := by
    simp only [waitIn, Bool.and_eq_true] at hin; exact hin.2
  have ex16 := label_labelGapB hp hg
  refine seg_one (call_nd_F (e0 := 0) (lo' := -56) (hi' := 8)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .x16)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : Ctl × BitVec 64 × BitVec 64 => Park.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 tp .e)
    (Ex := fun g y => Park.E g.1 g.2.1 g.2.2 tp y)
    hR hF (by show R.lo ≤ -32 - 0 + -56; omega) (by decide) (by show (-32 : Int) - 0 < R.hi; omega)
    (by show (-32 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-32 : Int) - 0) % 8 = 0; decide) (by decide)
    (by decide)
    (fun R' F' hR' hlo' hhi' hF' hFF g =>
      Park.seg_park hF' hR' hlo' hhi' hK (hT.mono hFF) hown (hS.mono hFF) htp4 hpcode.ghost hpentry)
    (fun _ => rfl) ?_ ?_)
  · rintro σC c ⟨⟨rfl, -, htp, -⟩, -⟩
    exact ⟨(c, σC.regs.rbp.toBitVec, σC.slot (-32 - 0 + 0)), rfl, rfl, rfl, rfl, htp⟩
  · rintro ⟨c1, rbp1, ra1⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, ⟨h8, h0, h16⟩, -, hbp⟩, h32⟩ ⟨hc, hrb, hra, -⟩
      ⟨hc', hrb', htp'⟩ hreg - - hslot
    have hout : ∀ k : Int, -16 ≤ k → k % 8 = 0 → k ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, by show SO.le oP ⟨-32 - 0 + 8, []⟩ = true; decide, hc'.trans hc.symm,
      ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label ".Lwc_waitLoop.x16" = Int64.ofBitVec (σC.slot (-32))
      rw [h32, ex16]; rfl
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout 0 (by decide) (by decide) (by decide)]; exact h0
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have : σx.regs.get64 .rbp = rbp1 := hrb'
      rw [hreg]; simp only [Reg64s.get64] at this; rw [this]
      exact (show σC.regs.rbp.toBitVec = rbp1 from hrb).symm.trans hbp

/-- **`wc_waitLoop` with its park call discharged** (`seg_waitLoop` with
`hpark` from `seg_parkCall`): the park routine's facts (the kernel model,
the TCB's self pointer, the permit word, its code and its prologue's
fall-through) are hypotheses. -/
theorem seg_waitLoopP (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (R.addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    {c0' : Ctl} {rbp0' ra' tp' : BitVec 64} (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8) :
    SegL p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .e))
      (fun s c => ∃ y, At exe endPc R F (E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0) y) s c) :=
  seg_waitLoop hp hend hin hF hR hlo hhi hlim hterm hev hval htag hdm
    (seg_parkCall hp hin hF hR hlo hhi hK hT hown hS htp4 hpcode hpentry)

end Proof

end Spike.Lib.X64.WaitLoop

/-- info: 'Spike.Lib.X64.WaitLoop.seg_waitLoopP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WaitLoop.seg_waitLoopP
