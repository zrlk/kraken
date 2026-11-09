/-
**`wc_waitLoop` inside a state predicate `W`** (x64): the x64
twin of `Spike/Lib/A64WaitLoopW.lean`. `WaitLoop.seg_waitLoop`
(`Spike/Lib/X64WaitLoop.lean`) as a `SegLW W` segment
(`Spike/Lib/SegLW.lean`) for any `W`, the obligation that every state of
the loop is in `W` left per node (`LoopW`: `XProW` for the prologue,
`BlkW` for the block nodes, `NodeW` for the acquire load), the park call
given as a `SegW W` segment. wake's main after the spawn instantiates `W`
with its abort-site predicate.

- `LoopW`: the per-node obligations.
- `seg_waitLoopW`: the loop from its entry to its return, inside `W`.
- `seg_parkCallW`: the park call inside `W` (`call_nd_FW` with
  `Park.seg_parkWG`), given the routine's states in `W` in every callee
  frame condition the call can pass (`hPW`: below the caller's, the caller's
  cells outside the callee's region as at the call).

As in `X64WaitLoop` the frame is fixed (`fn_seg_gLW` at `Unit`), and the
`.x16` block runs from the node with `%rbp`'s offset added (`At.rbpOf`), so
its `BlkW` obligation is at that node (`x16N`).
-/
import Spike.Lib.X64WaitLoop
import Spike.Lib.X64CfgLW
import Spike.Lib.X64ParkW

namespace Spike.Lib.X64.WaitLoop

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB blockAcrossB)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk seg_oneW)
open Scc.Sem (ValRep)

set_option linter.unusedSimpArgs false

/-- The `.x16` node with `%rbp`'s offset (where its block runs from). -/
def x16N (lab : Label → Int64) (c0 : Ctl) (A fp ra tp sp : BitVec 64) : ND :=
  ⟨lab ".Lwc_waitLoop.x1", oI, JI c0 A fp ra tp sp⟩

/-- **The loop's states inside `W`**, at one region `R`, frame condition
`F` and the loop's ghosts: the prologue's (`XProW`), every block node's
internal states (`BlkW`) and the acquire load's (`NodeW`). -/
structure LoopW (W : Frag isa) (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (c0 : Ctl) (x : String) (e : Expr) (ty : Ty)
    (Rd : TermRun.Word → Prop) (A fp ra tp sp : BitVec 64) : Prop where
  pro : XProW W (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_waitLoop") 16 8
    ".Lwc_waitLoop.stk" 5 9 3 2 4 [(.rdi, -8, 4)] (JE c0 A fp ra tp sp)
  entry : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .entry) b4
  ld : NodeW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .ld)
  n5 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .n5) b5
  n6 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .n6) b6
  then1 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .then1) b7
  else2 : BlkW W (fun _ _ => False) exe endPc R F
    (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .else2) b8
  x16 : BlkW W (fun _ _ => False) exe endPc R F (x16N (_root_.Executable.labels exe).label c0 A fp ra tp sp) b9

section ProofW

variable {W : Frag isa} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
  {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

set_option hygiene false in
/-- A block node inside `W`: the block, its `okBlk`, its code and `LoopW`
field; the edge is left. -/
local macro "nodeLW " b:ident ok:ident hc:ident f:ident : tactic =>
  `(tactic| refine seg_fixLW () (SegLW.ofSegW (seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend $hc (by first | rfl | exact ofNat_zero' _)) hLW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)))

set_option hygiene false in
/-- `nodeLW` for a block split by a return label after its first `n` rows
(`blockAcrossB`, `Spike.Lib.X64.code_field_blockAcrossB`). -/
local macro "nodeLWX " b:ident ok:ident hc:ident f:ident : tactic =>
  `(tactic| refine seg_fixLW () (SegLW.ofSegW (seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (Spike.Lib.X64.code_field_blockAcrossB hp hend $hc (List.take_append_drop _ _)
      (by first | rfl | exact ofNat_zero' _)) hLW.$f fun σ c hJ => ⟨c, .refl c, ?_⟩)))

/-- Hitting node `j`. -/
local macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, JK, JF, JE, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, ownStep, Reg64s.set64, Reg64s.get64]))

/-- **`wc_waitLoop` inside `W`** (`seg_waitLoop` over `SegLW W`): every
node's states in `W` (`hLW`) and the park call (`hpark`) a segment inside
`W`. -/
theorem seg_waitLoopW (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (R.addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hLW : LoopW W ms exe endPc R F c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0))
    (hpark : SegW W (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .park))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .x16))) :
    SegLW W p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp
        (R.addr 0) .e))
      (fun s c => ∃ y, At exe endPc R F (E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0) y) s c) := by
  have hin' := hin
  simp only [waitIn, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, hg⟩ := hin'
  refine (fn_seg_gLW (Rg := fun _ : Unit => R) (Fg := fun _ => F)
    (N := fun _ => N _ c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0))
    (E := fun _ => E c0 x e ty (RdOne (ms := ms) lbl) A fp ra tp (R.addr 0)) (fun _ i => ?_) () PN.e).mono_post
    fun _ _ ⟨_, y, h⟩ => ⟨y, h⟩
  cases i
  case e =>
    refine seg_fixLW () (SegLW.ofSegW (seg_givenW PN.entry (prologue_seg_ofW hp hend hpro (by decide) hF hR
      (by have : (16 : Int64).toInt = 16 := by decide
          omega) (by omega) (by decide) rfl (by show SO.le oI (oF 16) = true; decide) hLW.pro ?_)))
    rintro σ c ⟨rfl, hdi, hbp, h0, hsp, htp⟩
    rw [htp]
    refine ⟨hlim.rt, hlim.mp, hlim.unmapped, fun v hv => ⟨by rw [hsp]; exact hlim.room v hv, fun σ' hr hs => ?_⟩⟩
    refine ⟨rfl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hs]; simp [xStSlots, xS1, upd_apply, hbp]
    · rw [hs]; simp [xStSlots, xS1, upd_apply, h0]
    · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
  case entry => nodeLW b4 b4_ok h4 entry; rw [N, b4_run]; hit PN.ld
  case ld =>
    refine seg_fixLW () (ldSt_ndW (V := 1) (by decide) hF (code_field hp hend hld rfl) hdm
      (fun s c h => (hLW.ld s c h).1) ?_)
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
    nodeLW b5 b5_ok h5 n5; rw [N, b5_run]
    obtain ⟨hK, h | h⟩ := hJ
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [h.1]; rfl))]
      hit PN.then1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h'; exact h.1 (by bv_decide)))]
      hit PN.n6
  case n6 => nodeLW b6 b6_ok h6 n6; rw [N, b6_run]; hit PN.else2
  case then1 =>
    nodeLWX b7 b7_ok h7 then1; rw [N, b7_run]
    obtain ⟨⟨⟨h8', h0, h16⟩, htp, hbp⟩, hP, h24⟩ := hJ
    refine .inr ⟨PX.ret, ?_, rfl, hP, ?_, ?_, ?_, ?_, h16, h24⟩
    · simp [E, h0]
    · simp [Reg64s.set64]
    · simp [Reg64s.set64, h8']
    · simp [Reg64s.set64, htp]
    · simp only [Reg64s.set64, UInt64.toBitVec_ofBitVec]; rw [hbp]; bv_omega
  case else2 => nodeLW b8 b8_ok h8 else2; rw [N, b8_run]; hit PN.park
  case park => exact seg_fixLW () (SegLW.ofSegW (seg_givenW PN.x16 hpark))
  case x16 =>
    refine seg_fixLW () (SegLW.ofSegW ((seg_ndW (n := x16N _ c0 A fp ra tp (R.addr 0)) (by simp [b9]) b9_ok hF hR
      hlo hhi (code_field hp hend h9 (ofNat_zero' _)) hLW.x16 fun σ c hJ => ⟨c, .refl c, ?_⟩).mono_pre
      fun _ _ h => At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.2, addr0_sub8]))
    rw [x16N, b9_run]
    obtain ⟨rfl, ⟨h8', h0, h16⟩, htp, hbp⟩ := hJ
    refine .inl ⟨PN.e, rfl, rfl, rfl, ?_, ?_, h0, ?_, ?_⟩
    · simp [Reg64s.set64, h16]
    · simp [Reg64s.set64, h8']
    · simp only [Reg64s.set64, UInt64.toBitVec_ofBitVec]; rw [hbp]; bv_omega
    · simp [Reg64s.set64, htp]

/-- **The call of `scc_rt_park` inside `W`** (`seg_parkCall` over `SegW W`:
`call_nd_FW` with `Park.seg_parkWG`). The routine's states are in `W` for
every callee region and frame condition the call passes (`hPW`): the
callee's region below the call's `%rsp` (offset `-32`), the condition
stronger than `F`, each of its states' memory outside the callee's region
that of a state at the call, and the routine's ghost source the caller's
(`g.1 = c0`). -/
theorem seg_parkCallW (hp : Lays exe cells kp) (hin : waitIn cells = true) {Rd : TermRun.Word → Prop}
    {sp : BitVec 64} {c0' : Ctl} {rbp0' ra' tp' : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hPW : ∀ (R' : Region) (F' : MachineData → Prop), R' = R.callee (-32) (-56) 8 → R'.OK →
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ (mC : MachineData) (σC : AS) (c : Ctl), Abs R ⟨-32, [(.rbp, -8)]⟩ mC σC ∧
        (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .park).J σC c ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -32) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      ∀ g : Ctl × BitVec 64 × BitVec 64, g.1 = c0 → Park.ParkGW W exe endPc R' F' g.1 g.2.1 g.2.2 tp) :
    SegW W (fun _ _ => False) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .park))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .x16)) := by
  have hg : labelGapB cells ".Lwc_waitLoop.else2" ".Lwc_waitLoop.x1" 5 = true := by
    simp only [waitIn, Bool.and_eq_true] at hin; exact hin.2
  have ex16 := label_labelGapB hp hg
  refine seg_oneW (call_nd_FW (e0 := 0) (lo' := -56) (hi' := 8) (M := fun _ => True)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp sp .x16)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : Ctl × BitVec 64 × BitVec 64 => Park.N (_root_.Executable.labels exe).label g.1 g.2.1 g.2.2 tp .e)
    (Ex := fun g y => Park.E g.1 g.2.1 g.2.2 tp y)
    hR hF (by show R.lo ≤ -32 - 0 + -56; omega) (by decide) (by show (-32 : Int) - 0 < R.hi; omega)
    (by show (-32 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-32 : Int) - 0) % 8 = 0; decide) (by decide)
    (by decide) (KStable.none F) (fun _ _ h => h.elim) (fun _ h _ => h)
    (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e _ g hg hm =>
      (Park.seg_parkWG hF' hR' hlo' hhi' hK (hT.mono hFF) hown (hS.mono hFF) htp4 hpcode.ghost hpentry
        (hPW R' F' hR'e hR' hFF
          (fun m hm' => let ⟨mC, σC, c, hA, hJ, _, hk⟩ := hm m hm'; ⟨mC, σC, c, hA, hJ, hk⟩) g
          (let ⟨_, _, ⟨⟨h1, _⟩, _⟩, h2, _⟩ := hg; h2.symm.trans h1))).mono_post
        fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
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
      show (_root_.Executable.labels exe).label ".Lwc_waitLoop.x1" = Int64.ofBitVec (σC.slot (-32))
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

end ProofW

end Spike.Lib.X64.WaitLoop

/-- info: 'Spike.Lib.X64.WaitLoop.seg_waitLoopW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WaitLoop.seg_waitLoopW

/-- info: 'Spike.Lib.X64.WaitLoop.seg_parkCallW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WaitLoop.seg_parkCallW
