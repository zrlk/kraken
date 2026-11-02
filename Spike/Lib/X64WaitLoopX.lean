/-
**Main's spin-wait on x64, at any return label**: `Spike/Lib/X64WaitLoop.lean` with the label
after the park call (`xl`, wake.w's `.Lwc_waitLoop.x16`) a parameter. scc numbers its local
labels per program, so the label differs between listings (hello.w's is `.Lwc_waitLoop.x20`);
the blocks, the graph's shape and every proof step are `X64WaitLoop`'s.

- `waitInX xl cells`: `X64WaitLoop.waitIn` with `xl` (`waitInX_x16`: wake's is the instance).
- `NX xl`: `X64WaitLoop.N` with the node `.x16` at `lab xl` (`NX_x16`).
- `seg_waitLoopX`, `seg_parkCallX`, `seg_waitLoopPX`: `seg_waitLoop`, `seg_parkCall`,
  `seg_waitLoopP` at `xl`.

The blocks (`b4` … `b9`, their `block_spec` facts), the node and exit types (`PN`, `PX`), the
invariants (`Past`, `JE`, `JF`, `JK`, `JI`), the exit `E`, `RdOne`, `At.rbpOf` and
`addr0_sub8` are `X64WaitLoop`'s, imported.

Unlike AArch64 (`Spike/Lib/A64WaitLoop.lean`, generic in the function's label prefix `pfx`, the
label gaps as hypotheses), the x86-64 labels carry no prefix: only the one numbered label the
loop names is a parameter, and its gap is in the cells' check `waitInX`.
-/
import Spike.Lib.X64WaitLoop

namespace Spike.Lib.X64.WaitLoopX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk seg_one)
open Scc.Sem (ValRep)
open Spike.Lib.X64.WaitLoop

set_option linter.unusedSimpArgs false

/-- **`wc_waitLoop` in `cells`, `xl` right after the park call**: `X64WaitLoop.waitIn` with
`xl` for `.x16`. -/
def waitInX (xl : Label) (cells : List (Directive × Nat)) : Bool :=
  prologueIn cells "wc_waitLoop" ".Lwc_waitLoop.chk" ".Lwc_waitLoop.entry" 16 8 ".Lwc_waitLoop.stk" 5 9 3 2 4
      [(.rdi, -8, 4)] &&
    blockAtB cells ".Lwc_waitLoop.entry" 0 b4 && blockAtB cells ".Lwc_waitLoop.entry" 4 [(ldDir .rcx 0 .rax, 3)] &&
    blockAtB cells ".Lwc_waitLoop.entry" 7 b5 && blockAtB cells ".Lwc_waitLoop.entry" 27 b6 &&
    blockAtB cells ".Lwc_waitLoop.then1" 0 b7 && blockAtB cells ".Lwc_waitLoop.else2" 0 b8 &&
    blockAtB cells xl 0 b9 && labelGapB cells ".Lwc_waitLoop.else2" xl 5

/-- wake's check is the instance at `.Lwc_waitLoop.x16`. -/
theorem waitInX_x16 : waitInX ".Lwc_waitLoop.x16" = waitIn := rfl

section Spec

variable (xl : Label) (lab : Label → Int64) (c0 : Ctl) (x : String) (e : Expr) (ty : Ty)
  (Rd : TermRun.Word → Prop) (A fp ra tp sp : BitVec 64)

/-- **The nodes**, the park's return at `lab xl`. -/
def NX : PN → ND
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
  | .x16 => ⟨lab xl, oP, JI c0 A fp ra tp sp⟩

/-- wake's nodes are the instance at `.Lwc_waitLoop.x16`. -/
theorem NX_x16 : NX ".Lwc_waitLoop.x16" lab c0 x e ty Rd A fp ra tp sp = N lab c0 x e ty Rd A fp ra tp sp := by
  funext n; cases n <;> rfl

end Spec

/-! ## The proof -/

section Proof

variable {xl : Label} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
  {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

set_option hygiene false in
/-- A block node at `l + k`: the block, its `okBlk`, its code; the edge is
left. -/
local macro "node " b:ident ok:ident hc:ident : tactic =>
  `(tactic| refine seg_fixL () (seg_nd (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend $hc (by first | rfl | exact ofNat_zero' _)) fun σ c hJ => ⟨c, .refl c, ?_⟩).toL)

/-- Hitting node `j`. -/
local macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [NX, JI, JK, JF, JE, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, ownStep, Reg64s.set64, Reg64s.get64]))

/-- **`wc_waitLoop` is one segment with the load-or-stutter row** from its
entry to its return, in any valid layout of cells with `waitIn`. The source
stutters at its load `c0` until the `movq` reads `1`, and then takes it
(`Past`); it never parks. The park call is a hypothesis (`hpark`, from the
call node at `scc_rt_park` back to `xl`): `seg_parkCall`. -/
theorem seg_waitLoopX (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitInX xl cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (R.addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hpark : Seg p lbl ms
      (At exe endPc R F (NX xl (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .park))
      (At exe endPc R F (NX xl (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .x16))) :
    SegL p lbl ms
      (At exe endPc R F (NX xl (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .e))
      (fun s c => ∃ y, At exe endPc R F (E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0) y) s c) := by
  have hin' := hin
  simp only [waitInX, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, hg⟩ := hin'
  refine (fn_seg_gL (Rg := fun _ : Unit => R) (Fg := fun _ => F)
    (N := fun _ => NX xl _ c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0))
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
  case entry => node b4 b4_ok h4; rw [NX, b4_run]; hit PN.ld
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
    node b5 b5_ok h5; rw [NX, b5_run]
    obtain ⟨hK, h | h⟩ := hJ
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [h.1]; rfl))]
      hit PN.then1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h'; exact h.1 (by bv_decide)))]
      hit PN.n6
  case n6 => node b6 b6_ok h6; rw [NX, b6_run]; hit PN.else2
  case then1 =>
    node b7 b7_ok h7; rw [NX, b7_run]
    obtain ⟨⟨⟨h8', h0, h16⟩, htp, hbp⟩, hP, h24⟩ := hJ
    refine .inr ⟨PX.ret, ?_, rfl, hP, ?_, ?_, ?_, ?_, h16, h24⟩
    · simp [E, h0]
    · simp [Reg64s.set64]
    · simp [Reg64s.set64, h8']
    · simp [Reg64s.set64, htp]
    · simp only [Reg64s.set64, UInt64.toBitVec_ofBitVec]; rw [hbp]; bv_omega
  case else2 => node b8 b8_ok h8; rw [NX, b8_run]; hit PN.park
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
back to `xl`, the frame unmoved. The ghosts of `seg_park` are the source
control, `%rbp` and the return address at the call (the thread pointer is
`tp`, in `JK`). The facts it needs are hypotheses: the kernel model (`hK`),
the TCB's self pointer (`hT`, `hown`), the permit word's (`hS`, `htp4`), the
park routine's code (`hpcode`, for any of its ghosts: `Park.Code.ghost`)
and its prologue's fall-through (`hpentry`). -/
theorem seg_parkCallX (hp : Lays exe cells kp) (hin : waitInX xl cells = true) {Rd : TermRun.Word → Prop}
    {sp : BitVec 64} {c0' : Ctl} {rbp0' ra' tp' : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8) :
    Seg p lbl ms (At exe endPc R F (NX xl (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .park))
      (At exe endPc R F (NX xl (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .x16)) := by
  have hg : labelGapB cells ".Lwc_waitLoop.else2" xl 5 = true := by
    simp only [waitInX, Bool.and_eq_true] at hin; exact hin.2
  have ex16 := label_labelGapB hp hg
  refine seg_one (call_nd_F (e0 := 0) (lo' := -56) (hi' := 8)
    (N := fun _ : Unit => NX xl (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .x16)
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
        simp only [Region.callee, NX] at h; omega
    refine .inl ⟨(), ?_, by show SO.le oP ⟨-32 - 0 + 8, []⟩ = true; decide, hc'.trans hc.symm,
      ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label xl = Int64.ofBitVec (σC.slot (-32))
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
theorem seg_waitLoopPX (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitInX xl cells = true)
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
      (At exe endPc R F (NX xl (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .e))
      (fun s c => ∃ y, At exe endPc R F (E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0) y) s c) :=
  seg_waitLoopX hp hend hin hF hR hlo hhi hlim hterm hev hval htag hdm
    (seg_parkCallX hp hin hF hR hlo hhi hK hT hown hS htp4 hpcode hpentry)


end Proof

end Spike.Lib.X64.WaitLoopX

/-- info: 'Spike.Lib.X64.WaitLoopX.seg_waitLoopPX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WaitLoopX.seg_waitLoopPX
