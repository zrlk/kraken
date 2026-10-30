/-
**wake.w's worker rows on AArch64** (the worker's
half): the target side of `wake.w`'s `wc_worker` (`store rel c 1`,
`unpark j`, return; no print) and of `scc_rt_thr_worker` (the call of
`wc_worker`, the `exited` release, the `exit`), over the thread rows
(`OutT`, `SegT`). The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

**The label prefix** `pfx` (a parameter of `N`, `Code` and the proofs, as
in `Spike.Lib.A64.WaitLoop`): the function's local labels are
`pfx ++ ".0_entry"` etc.; in wake's certificate `wc_worker`'s is
`.L19_wc_worker` and `scc_rt_thr_worker`'s `.L18_scc_rt_thr_worker`
(`WkTailW.pfx0`, `ThrTailW.pfx0`). No block branches to a local label (the
`bl`s target global symbols), so the blocks do not depend on it.

- `WkTailW.seg_wkTailW`: `wc_worker` from `.0_entry` (after its prologue,
  frame of 32: `c`/`j` at `-32`/`-24`, `x29`/`x30` at `-16`/`-8`) to its
  return: the `stlr` (the source's store, `relStore_nd`), the call of
  `scc_rt_unpark` as a given node, the epilogue at `.sp1`;
  `WkTailW.seg_unparkCallW` discharges the call with `Unpark.seg_unpark`
  (`WkTailW.seg_wkTailWU`, region `[-80, 0)`).
- `ThrTailW.seg_thrTailW`: `scc_rt_thr_worker`'s tail from `.sp0` (frame
  of 48, the thread pointer spilled at `[sp, #16]`).
- `ThrHeadW.seg_thrHeadW`: `scc_rt_thr_worker`'s `.0_entry` block (`x0`,
  `x1` from the frame, `bl wc_worker`) and the call (`call_ndT`,
  `wc_worker`'s segment given in every region `[-80, 0)` below the frame of
  48: the region reaches `-128`).
-/
import Spike.Lib.A64WorkerRows

namespace Spike.Lib.A64.Flow.Worker.Wake

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StOk)

/-! ## `wc_worker`

    .0_entry: x9 = 1; x10 = c (cell 0)
              stlr x9, [x10]                 -- the source's `store rel c 1`
              x0 = j (cell 8)
              bl scc_rt_unpark               -- the source's `unpark j` (inside)
    .sp1:     epilogue (x29/x30 at 16/24, frame of 32); ret

The region is the frame, offsets `[-32, 0)`. Ghosts as in `WkTail`: the
source controls `c0` (at `let d = store rel a b in e1`), `c1` (past the
store), `c2` (past the `unpark`), the address `A` of `c` and the tid `B` of
`j` in their cells, the caller's `x29`, the return address `ra`, the thread
pointer `tp`. -/

namespace WkTailW

/-- `wc_worker`'s label prefix in wake's certificate. -/
abbrev pfx0 : String := ".L19_wc_worker"

def b0 : List Directive := parseAArch64("movz x9, #1
ldr x10, [sp]")
def b1 : List Directive := parseAArch64("ldr x0, [sp, #8]")
def b2 : List Directive := parseAArch64("bl scc_rt_unpark")
def b3 : List Directive := parseAArch64("ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
ret")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-32, []⟩
/-- The offsets at return. -/
abbrev oE : SO := ⟨0, []⟩

block_spec b0 (-32) 0 oI b0
block_spec b1 (-32) 0 oI b1
block_spec b2 (-32) 0 oI b2
block_spec b3 (-32) 0 oI b3

/-- The internal nodes. -/
inductive PN where
  | e | st | n3 | bl | unpk | sp1

/-- The exits. -/
inductive PX where
  | ret

section Spec

variable (pfx : String) (lab : Label → Int64) (c0 c1 c2 : Ctl) (A B x29 ra tp : BitVec 64)

/-- Inside the frame, the source at `c'`: the caller's `x29`, the return
address, `A` and `B` in their cells, the thread pointer `tp`. -/
def JI (c' : Ctl) (σ : AS) (c : Ctl) : Prop :=
  c = c' ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.slot (-32) = A ∧ σ.slot (-24) = B ∧
    σ.regs.TPIDR_EL0.toBitVec = tp

/-- The pc of the `bl`. -/
abbrev pcBl : Int64 := lab (pfx ++ ".0_entry") + 4 + 4 + 4 + 4

/-- **The nodes.** -/
def N : PN → ND
  | .e => ⟨lab (pfx ++ ".0_entry"), oI, JI A B x29 ra tp c0⟩
  | .st => ⟨lab (pfx ++ ".0_entry") + 4 + 4, oI, fun σ c => JI A B x29 ra tp c0 σ c ∧
      σ.regs.X10.toBitVec = A ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .n3 => ⟨lab (pfx ++ ".0_entry") + 4 + 4 + 4, oI, JI A B x29 ra tp c1⟩
  | .bl => ⟨pcBl pfx lab, oI, fun σ c => JI A B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B⟩
  | .unpk => ⟨lab "scc_rt_unpark", oI, fun σ c => JI A B x29 ra tp c1 σ c ∧ σ.regs.X0.toBitVec = B ∧
      σ.regs.X30.toBitVec = BitVec.ofInt 64 (((pcBl pfx lab).toInt + 4).bmod 18446744073709551616)⟩
  | .sp1 => ⟨lab (pfx ++ ".sp1"), oI, JI A B x29 ra tp c2⟩

/-- **The exit**: the return to `ra`, the source past its `unpark`. -/
def E : PX → ND
  | .ret => ⟨Int64.ofBitVec ra, oE, fun σ c => c = c2 ∧ σ.regs.X29.toBitVec = x29 ∧ σ.regs.X30.toBitVec = ra ∧
      σ.regs.TPIDR_EL0.toBitVec = tp⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e).pc b0
  st : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .st).pc
      [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩]
  n3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .n3).pc b1
  bl : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .bl).pc b2
  sp1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1).pc b3

/-- The code does not depend on the ghosts (the nodes' pcs do not). -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c1 c2 c0' c1' c2' : Ctl}
    {A B x29 ra tp A' B' x29' ra' tp' : BitVec 64} (h : Code pfx c0 c1 c2 A B x29 ra tp exe endPc) :
    Code pfx c0' c1' c2' A' B' x29' ra' tp' exe endPc :=
  ⟨h.e, h.st, h.n3, h.bl, h.sp1⟩

end Spec

section Proof

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
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

/-- **`wc_worker` after its prologue is one segment with the thread rows**,
from `.0_entry` to its return: the `stlr` is the source's `store rel c 1`
(`Out.store`), the call of `scc_rt_unpark` the given node `hunpk`, the rest
stutters. -/
theorem seg_wkTailW (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code pfx c0 c1 c2 A B x29 ra tp exe endPc)
    (hunpk : SegT p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1))) :
    SegT p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) := by
  refine fn_segT (N := N pfx _ c0 c1 c2 A B x29 ra tp) (E := E c2 x29 ra tp) (fun i => ?_) PN.e
  cases i
  case e => node b0 b0_ok e; rw [N, b0_run]; hit PN.st
  case st =>
    refine (relStore_nd (A := A) (fun s he hn => hcode.st s he hn) hdm fun m σ c _ _ hJ => ?_).toT
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hvb, ?_⟩
    rw [← hc1]
    hit PN.n3
  case n3 => node b1 b1_ok n3; rw [N, b1_run]; hit PN.bl
  case bl => node b2 b2_ok bl; rw [N, b2_run]; hit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.sp1, h⟩
  case sp1 =>
    node b3 b3_ok sp1; rw [N, b3_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI]

/-- **The call of `scc_rt_unpark`** (`call_ndT` with `Unpark.seg_unpark`,
frame `[-48, 0)` from the call's `sp`, which is at offset `-32`): from
`.unpk` back to `.sp1`, the frame unmoved, the source from `c1` (at its
`let x = unpark a in e`, `a`'s word representing `B`) to `c2` (past it).
The hypotheses are `WkTail.seg_unparkCall`'s; the return label is `.sp1`
after the `bl` (`hsp1`). -/
theorem seg_unparkCallW (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp1 : (_root_.Executable.labels exe).label (pfx ++ ".sp1") =
      pcBl pfx (_root_.Executable.labels exe).label + 4) :
    SegT p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1)) := by
  refine (call_ndT (lo' := -48) (hi' := 0)
    (N := fun _ : Unit => N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp1)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : BitVec 64 × BitVec 64 => Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1 g.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1 g.2 tp y)
    hR hal hF (by show R.lo ≤ -32 + -48; omega) (by decide) (by show (-32 : Int) < R.hi; omega) (by decide)
    (by show (-32 : Int) % 16 = 0; decide) (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      Unpark.seg_unpark hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry)
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp⟩, h0, -⟩
    exact ⟨(σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), rfl, rfl, h0, rfl, rfl, htp⟩
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h16, h8, h32, h24, -⟩, -, h30⟩ ⟨-, -, -, hra, -⟩ ⟨hc', -, -, htp'⟩ hreg -
      hslot
    have hout : ∀ k : Int, -32 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc', ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label (pfx ++ ".sp1") = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [h30, hsp1, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout (-32) (by decide) (by decide) (by decide)]; exact h32
    · rw [hout (-24) (by decide) (by decide) (by decide)]; exact h24
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

/-- **`wc_worker` after its prologue, its `unpark` call discharged**
(`seg_wkTailW` with `hunpk` from `seg_unparkCallW`): the region holds
`scc_rt_unpark`'s frame below the worker's (`hlo`, `-32 - 48`). -/
theorem seg_wkTailWU (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code pfx c0 c1 c2 A B x29 ra tp exe endPc)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp1 : (_root_.Executable.labels exe).label (pfx ++ ".sp1") =
      pcBl pfx (_root_.Executable.labels exe).label + 4) :
    SegT p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) :=
  seg_wkTailW hF hR hal (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCallW hF hR hal hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hsp1)

end Proof

end WkTailW

/-! ## `scc_rt_thr_worker`'s tail

    .sp0:  x9 = tpidr_el0 (spilled at 16); x10 = x9 + 24
           stlr 1, [x10]                  -- the thread's `exited` word
           x0 = 0; x8 = 93
           svc #0                         -- exit: the thread ends

`ThrTail` with the frame of 48 (offsets `[-48, 0)`) and the spill at 16. -/

namespace ThrTailW

/-- `scc_rt_thr_worker`'s label prefix in wake's certificate. -/
abbrev pfx0 : String := ".L18_scc_rt_thr_worker"

def b0 : List Directive := parseAArch64("mrs x9, tpidr_el0
str x9, [sp, #16]
movz x9, #1
ldr x10, [sp, #16]
add x10, x10, #24")
def b1 : List Directive := parseAArch64("movz x0, #0
movz x8, #93")

/-- The function's offsets inside the frame. -/
abbrev oI : SO := ⟨-48, []⟩

block_spec b0 (-48) 0 oI b0
block_spec b1 (-48) 0 oI b1

/-- The internal nodes. -/
inductive PN where
  | sp0 | ex | n2 | svc

section Spec

variable (pfx : String) (lab : Label → Int64) (c0 : Ctl) (tp : BitVec 64)

/-- **The nodes.** -/
def N : PN → ND
  | .sp0 => ⟨lab (pfx ++ ".sp0"), oI, fun σ c => c = c0 ∧ σ.regs.TPIDR_EL0.toBitVec = tp⟩
  | .ex => ⟨lab (pfx ++ ".sp0") + 4 + 4 + 4 + 4 + 4, oI, fun σ c => c = c0 ∧
      σ.regs.X10.toBitVec = tp + 24#64 ∧ σ.regs.X9.toBitVec = 1#64⟩
  | .n2 => ⟨lab (pfx ++ ".sp0") + 4 + 4 + 4 + 4 + 4 + 4, oI, fun _ c => c = c0⟩
  | .svc => ⟨lab (pfx ++ ".sp0") + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oI, fun σ c => c = c0 ∧
      σ.regs.X8 = 93⟩

/-- **The code**: every block at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  sp0 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .sp0).pc b0
  ex : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .ex).pc
      [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .n2).pc b1
  svc : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (N pfx (_root_.Executable.labels exe).label c0 tp .svc).pc [svcDir]

/-- The code does not depend on the ghosts. -/
theorem Code.ghost {exe : _root_.Executable} {endPc : Int64} {c0 c0' : Ctl} {tp tp' : BitVec 64}
    (h : Code pfx c0 tp exe endPc) : Code pfx c0' tp' exe endPc :=
  ⟨h.sp0, h.ex, h.n2, h.svc⟩

end Spec

section Proof

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}

set_option hygiene false in
/-- A block node: the block, its `okBlk`, its code; the edge is left. -/
macro "node " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine (seg_nd (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) fun σ c hJ => ⟨c, .refl c, ?_⟩).toT)

/-- Hitting node `j`. -/
macro "hit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`scc_rt_thr_worker`'s tail is one segment with the thread rows** from
`.sp0` to any fragment: the release of the thread's `exited` word (at
`tp + 24`, `StOk`), then the `exit` with the source at `ret a`
(`OutT.texit`). -/
theorem seg_thrTailW {Q : Frag isaLSE2} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code pfx c0 tp exe endPc) :
    SegT p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 tp .sp0)) Q := by
  refine (fn_segT (N := N pfx _ c0 tp) (E := (nofun : Empty → ND)) (fun i => ?_) PN.sp0).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case sp0 => node b0 b0_ok sp0; rw [N, b0_run]; hit PN.ex
  case ex =>
    refine (Spike.Lib.A64.Flow.Ret0.ownStlr_nd (A := tp + 24#64) (fun s he hn => hcode.ex s he hn) fun m σ c _ _ hJ => ?_).toT
    obtain ⟨rfl, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, ?_⟩
    hit PN.n2
  case n2 => node b1 b1_ok n2; rw [N, b1_run]; hit PN.svc
  case svc =>
    refine texit_nd hK (fun s he hn => hcode.svc s he hn) fun σ c ⟨hc, h8⟩ => ⟨by rw [h8]; rfl, a, ?_⟩
    rw [hc]; exact ht

end Proof

end ThrTailW

/-! ## `scc_rt_thr_worker`'s head

    .0_entry: x0, x1 = the words at [sp, #0], [sp, #8]; bl wc_worker
    .sp0:     (ThrTailW)

The frame is `[-48, 0)`; `wc_worker` runs below it, in its own region
`[-80, 0)` from the call's `sp` (its frame of 32 and `scc_rt_unpark`'s 48
below), so the region reaches `-128`. -/

namespace ThrHeadW

/-- `scc_rt_thr_worker`'s `.0_entry` block: the arguments, the call. -/
def thE : List Directive := parseAArch64("ldr x0, [sp]
ldr x1, [sp, #8]
bl wc_worker")

block_spec thE (-128) 0 (⟨-48, []⟩ : SO) thE

/-- The head's internal nodes. -/
inductive TN where
  | e | call

/-- **The head's nodes**, from the invariant `J` at `.0_entry`; across the
block the source moves from `c0` to `c` with `L c0 c` (a local run: the
worker's `split` of its argument pair). -/
def tN (pfx : String) (lab : Label → Int64) (J : AS → Ctl → Prop) (L : Ctl → Ctl → Prop) : TN → ND
  | .e => ⟨lab (pfx ++ ".0_entry"), ⟨-48, []⟩, J⟩
  | .call => ⟨lab "wc_worker", ⟨-48, []⟩, fun σ c => ∃ σ0 c0, J σ0 c0 ∧ L c0 c ∧
      σ = (arun lab thE ⟨lab (pfx ++ ".0_entry"), ⟨-48, []⟩, σ0⟩).σ⟩

section Proof

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_thr_worker`'s head is one segment with the thread rows**,
from `.0_entry` (invariant `J`) to the caller's nodes `N`/exits `E`: the
block, then the call of `wc_worker` (`call_ndT`, `wc_worker`'s region
`[-80, 0)` below the frame). `wc_worker`'s segment from its entry `Ne g`
to its exits `Ex g` is given for every region holding its frames and every
frame condition giving `F` (`hwk`); `hent` picks the ghost at the call,
`hret` lands its exits (the return to `.sp0` is `ThrTailW.N .sp0`). The
source takes a local run `L` across the block (`hL`). -/
theorem seg_thrHeadW {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label (pfx ++ ".0_entry")) thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -80 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegT p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-48) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-48) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-48) (-80) 0).Off (k - (-48)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-48 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegT p lbl ms (At exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegT.seq (Q := At exe endPc R F (tN pfx lab J L .call))
    (Seg.toT (seg_nd (N := fun _ : Unit => tN pfx lab J L .call) (E := (nofun : Empty → ND)) (by simp [thE]) thE_ok
      hF hR hal hlo hhi hcodeE fun σ c hJ => ?_) |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndT (lo' := -80) (hi' := 0) hR hal hF (by show R.lo ≤ -48 + -80; omega) (by decide)
      (by show (-48 : Int) < R.hi; omega) (by decide) (by show (-48 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end Proof

end ThrHeadW

end Spike.Lib.A64.Flow.Worker.Wake
