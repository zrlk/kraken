/-
**hello.w's `wc_worker` tail on AArch64** (B5 check-in 3): a copy of
`Spike.Lib.A64.Flow.Worker.WkTail` (`Spike/Lib/A64WorkerRows.lean`) at
hello's certificate labels `.L20_wc_worker.sp4`/`.sp6`
(`Spike/Test/Cert/A64HelloCert.lean`); the blocks, nodes and proofs are
`WkTail`'s, only the label changes. `A64WorkerRows` is in wake's import
closure and is not edited (hence a hello copy of `WkTail`).

- `HelloTail.N`, `E`, `Code`, `seg_wkTail`, `seg_unparkCall`,
  `seg_wkTailU`: as `WkTail`'s.
-/
import Spike.Lib.A64WorkerRows

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow.Ret0 (StOk land_ldStep)
open Spike.Lib.A64.Flow.Park (swpDir)

/-! ## `wc_worker`'s tail

    .sp4:  x9 = 1; x10 = c (cell 32)
           stlr x9, [x10]                 -- the source's `store rel c 1`
           x0 = j (cell 40)
           bl scc_rt_unpark               -- the source's `unpark j` (inside)
    .sp6:  epilogue (x29/x30 at 80/88, frame of 96); ret

The region is the frame, offsets `[-96, 0)`. Ghosts: the source controls
`c0` (at `let d = store rel a b in e1`), `c1` (past the store), `c2`
(past the `unpark`), the address `A` of `c` and the tid `B` of `j` in their
cells, the caller's `x29`, the return address `ra`, the thread pointer
`tp`. The source facts of the store (`a`'s word an untagged locative
representing `A`, `b`'s word representing `1`) and that `A` is not private
memory (`hdm`) are hypotheses; so is the call of `scc_rt_unpark` (`hunpk`,
from its entry with the return address in `x30` back to `.sp6`; its
segment is `Unpark.seg_unpark` in the callee's region). -/

namespace HelloTail

def b0 : List Directive := parseAArch64("movz x9, #1
ldr x10, [sp, #32]")
def b1 : List Directive := parseAArch64("ldr x0, [sp, #40]")
def b2 : List Directive := parseAArch64("bl scc_rt_unpark")
def b3 : List Directive := parseAArch64("ldr x29, [sp, #80]
ldr x30, [sp, #88]
add sp, sp, #96
ret")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-96, []⟩
/-- The offsets at return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-96) 0 oI b0
block_spec b1 (-96) 0 oI b1
block_spec b2 (-96) 0 oI b2
block_spec b3 (-96) 0 oI b3

/-- The internal nodes. -/
inductive PN where
  | sp4 | st | n3 | bl | unpk | sp6

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (lab : Label → Int64) (c0 c1 c2 : Ctl) (A B x29 ra tp : BitVec 64)

/-- Inside the frame, the source at `c'`: the caller's `x29`, the return
address, `A` and `B` in their cells, the thread pointer `tp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-64) = A ∧ σ.slot (-56) = B ∧
    σ.regs.TPIDR_EL0.toBitVec = tp

/-- The pc of the `bl`. -/
abbrev pcBl : Int64 := lab ".L20_wc_worker.sp4" + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .sp4 => ⟨lab ".L20_wc_worker.sp4", oI, JI A B x29 ra tp c0⟩
  | .st => ⟨lab ".L20_wc_worker.sp4" + 4 + 4, oI, fun σ c => JI A B x29 ra tp c0 σ c ∧
      σ.regs.X10.toBitVec = A ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .n3 => ⟨lab ".L20_wc_worker.sp4" + 4 + 4 + 4, oI, JI A B x29 ra tp c1⟩
  | .bl => ⟨pcBl lab, oI, fun σ c => JI A B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B⟩
  | .unpk => ⟨lab "scc_rt_unpark", oI, fun σ c => JI A B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B ∧
      σ.regs.X30.toBitVec = BitVec.ofInt 64 (((pcBl lab).toInt + 4).bmod 18446744073709551616)⟩
  | .sp6 => ⟨lab ".L20_wc_worker.sp6", oI, JI A B x29 ra tp c2⟩

/-- **The exit**: the return to `ra`, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, fun σ c => c = c2 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
      σ.regs.TPIDR_EL0.toBitVec = tp⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4).pc b0
  st : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .st).pc
      [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩]
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .n3).pc b1
  bl : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .bl).pc b2
  sp6 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6).pc b3

end Spec

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B x29 ra tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`wc_worker`'s tail is one segment with the thread rows** from `.sp4`
to its return: the `stlr` is the source's `store rel c 1` (`Out.store`),
the call of `scc_rt_unpark` the given node `hunpk` (where the source takes
its `unpark`), the rest stutters. -/
theorem seg_wkTail (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B x29 ra tp exe endPc)
    (hunpk : SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6))) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) := by
  refine fn_segT (N := N _ c0 c1 c2 A B x29 ra tp) (E := E c2 x29 ra tp) (fun i => ?_) PN.sp4
  cases i
  case sp4 => node b0 b0_ok sp4; rw [N, b0_run]; hit PN.st
  case st =>
    refine (relStore_nd (A := A) (fun s he hn => hcode.st s he hn) hdm fun m σ c _ _ hJ => ?_).toT
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hvb, ?_⟩
    rw [← hc1]
    hit PN.n3
  case n3 => node b1 b1_ok n3; rw [N, b1_run]; hit PN.bl
  case bl => node b2 b2_ok bl; rw [N, b2_run]; hit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.sp6, h⟩
  case sp6 =>
    node b3 b3_ok sp6; rw [N, b3_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI]


/-- **The call of `scc_rt_unpark`** (`call_ndT` with `Unpark.seg_unpark`,
frame `[-48, 0)` from the call's `sp`, which is at offset `-96`): from
`.unpk` back to `.sp6`, the frame unmoved, the source from `c1` (at its
`let x = unpark a in e`, `a`'s word representing `B`) to `c2` (past it).
The ghosts of `seg_unpark` are `x29` and `x30` at the call. The facts it
needs are hypotheses: the kernel model (`hK`), the permit word's (`hS`,
`htp4`), the routine's code (`hpcode`, any ghosts: `Unpark.Code.ghost`)
and prologue fall-through (`hpentry`), and the return label `.sp6` after
the `bl` (`hsp6`). -/
theorem seg_unparkCall (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp6 : (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" = pcBl (_root_.Executable.labels exe).label + 4) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)) := by
  refine (call_ndT (lo' := -48) (hi' := 0)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : BitVec 64 × BitVec 64 => Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1 g.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1 g.2 tp y)
    hR hal hF (by show R.lo ≤ -96 + -48; omega) (by decide) (by show (-96 : Int) < R.hi; omega) (by decide)
    (by show (-96 : Int) % 16 = 0; decide) (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      Unpark.seg_unpark hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry)
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp⟩, h0, -⟩
    exact ⟨(σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, h0, rfl, rfl, htp⟩
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h16, h8, h64, h56, -⟩, -, h30⟩ ⟨-, -, -, hra, -⟩ ⟨hc', -, -, htp'⟩ hreg -
      hslot
    have hout : ∀ k : Int, -96 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc', ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, hsp6, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout (-64) (by decide) (by decide) (by decide)]; exact h64
    · rw [hout (-56) (by decide) (by decide) (by decide)]; exact h56
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

/-- **`wc_worker`'s tail with its `unpark` call discharged** (`seg_wkTail`
with `hunpk` from `seg_unparkCall`): the region holds `scc_rt_unpark`'s
frame below the tail's (`hlo`, `-96 - 48`). -/
theorem seg_wkTailU (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B x29 ra tp exe endPc)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp6 : (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" = pcBl (_root_.Executable.labels exe).label + 4) :
    SegT p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) :=
  seg_wkTail hF hR hal (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCall hF hR hal hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hsp6)

end Proof

end HelloTail

/-- info: 'Spike.Lib.A64.Flow.Worker.HelloTail.seg_wkTailU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloTail.seg_wkTailU

end Spike.Lib.A64.Flow.Worker
