/-
**hello.w's worker tail off the transfer sites** (`WCompatH.noSite`, AArch64): `HelloTail.seg_wkTail`,
`seg_unparkCall` and
`seg_wkTailU` (`Spike/Lib/A64HelloWkTail.lean`) over
`SegTC (NNZ exe endPc Z)`, every state of their hidden invariants at a cell
other than a `nop` (the twins of `Wake.WkTailW`'s in
`Spike/Lib/A64WakeWorkerNN.lean`). wake's `NNZ` is hello's `NNZH`
(`SegTC.toH`, `Spike/Lib/A64HelloNN.lean`).

The proofs are the originals' with the leaves of `Spike/Lib/A64WakeNN.lean`
(`seg_ndNNA`, `relStore_ndNNA`, `call_ndTS`) and `Unpark.seg_unparkNNA`
(`Spike/Lib/A64WakeWorkerNNA.lean`). Each segment keeps `Z` at its nodes'
states, given per node as `NodeZA Z exe endPc R F (N i) (blkN i)` (`hZ`;
`hZU` for the unpark callee in every callee region and at every ghost
return frame): `Z` may read the registers and the frame's cells, not only
the pc and the control (`NodeZ.toAOf … (lenN_eq i)` from a `NodeZ`).

- `HelloTail.lenN`, `HelloTail.blkN`, `HelloTail.lenN_eq`: the nodes' block
  lengths and blocks.
- `HelloTail.seg_wkTailNN`, `seg_unparkCallNN`, `seg_wkTailUNN`.
-/
import Spike.Lib.A64HelloWkTail
import Spike.Lib.A64WakeWorkerNNA

namespace Spike.Lib.A64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow.Ret0 (StOk land_ldStep)

namespace HelloTail

/-- Each node's block length (`1` at the store, `0` at the call), the `len`
of its `NodeZ` obligation. -/
def lenN : PN → Nat
  | .sp4 => b0.length | .st => 1 | .n3 => b1.length | .bl => b2.length | .unpk => 0 | .sp6 => b3.length

/-- Each node's block (the store's instruction, none at the call), the
`blk` of its `NodeZA` obligation. -/
def blkN : PN → List Directive
  | .sp4 => b0 | .st => [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] | .n3 => b1
  | .bl => b2 | .unpk => [] | .sp6 => b3

theorem lenN_eq (i : PN) : lenN i = (blkN i).length := by cases i <;> rfl

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B x29 ra tp : BitVec 64} {Z : Frag isaLSE2}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "wnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNNA (by simp [$b:ident]) $ok (by simp [$b:ident, notNop]) hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "whit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, JI, Spike.Lib.upd_apply, Reg64s.getSysReg, KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`seg_wkTail` off the transfer sites** (`hunpk` over `SegTC`). -/
theorem seg_wkTailNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96)
    (hhi : 0 ≤ R.hi) (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B x29 ra tp exe endPc)
    (hunpk : SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)))
    (hZ : ∀ i, NodeZA Z exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) := by
  refine fn_segTS (N := N _ c0 c1 c2 A B x29 ra tp) (E := E c2 x29 ra tp) (fun i => ?_) PN.sp4
  cases i
  case sp4 => wnode b0 b0_ok sp4; rw [N, b0_run]; whit PN.st
  case st =>
    refine relStore_ndNNA (A := A) (fun s he hn => hcode.st s he hn) hdm (fun m σ c _ _ hJ => ?_) (hZ .st).toW
    obtain ⟨⟨rfl, hJ⟩, h10, h9⟩ := hJ
    refine ⟨h10, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hvb, ?_⟩
    rw [← hc1]
    whit PN.n3
  case n3 => wnode b1 b1_ok n3; rw [N, b1_run]; whit PN.bl
  case bl => wnode b2 b2_ok bl; rw [N, b2_run]; whit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.sp6, h⟩
  case sp6 =>
    wnode b3 b3_ok sp6; rw [N, b3_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;> simp_all [N, E, JI]

/-- **`seg_unparkCall` off the transfer sites** (`call_ndTS` with
`Unpark.seg_unparkNNA`). -/
theorem seg_unparkCallNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' x29' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L11_scc_rt_unpark.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 4 + 4 + 4 + 4 + 4)
    (hsp6 : (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" = pcBl (_root_.Executable.labels exe).label + 4)
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) →
      ∀ x29' ra', Int64.ofBitVec ra' = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" →
      ∀ i, NodeZA Z exe endPc R' F' (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29' ra' tp i)
        (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)) := by
  refine (call_ndTS (lo' := -48) (hi' := 0)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp6)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : {g : BitVec 64 × BitVec 64 //
        Int64.ofBitVec g.2 = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6"} =>
      Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1.1 g.1.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1.1 g.1.2 tp y)
    hR hal hF (by show R.lo ≤ -96 + -48; omega) (by decide) (by show (-96 : Int) < R.hi; omega) (by decide)
    (by show (-96 : Int) % 16 = 0; decide) (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g =>
      Unpark.seg_unparkNNA hF' hR' hal' hlo' hhi' hK (hS.mono hFF) htp4 ht hh hev hv hc2 hpcode.ghost hpentry
        (hZU R' F' hR' hal' hlo' hhi' hF' hFF g.1.1 g.1.2 g.2))
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp⟩, h0, h30⟩
    refine ⟨⟨(σC.regs.X29.toBitVec, σC.regs.X30.toBitVec), ?_⟩, rfl, rfl, h0, rfl, rfl, htp⟩
    show Int64.ofBitVec σC.regs.X30.toBitVec = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6"
    rw [h30, hsp6, Ret0.ofInt_bmod, BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
  · rintro ⟨⟨x29', ra'⟩, hpin⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h16, h8, h64, h56, -⟩, -, -⟩ - ⟨hc', -, -, htp'⟩ hreg -
      hslot
    have hout : ∀ k : Int, -96 ≤ k → k % 8 = 0 → k + 8 ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, rfl, hc', ?_, ?_, ?_, ?_, ?_⟩
    · exact hpin.symm
    · rw [hout (-16) (by decide) (by decide) (by decide)]; exact h16
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout (-64) (by decide) (by decide) (by decide)]; exact h64
    · rw [hout (-56) (by decide) (by decide) (by decide)]; exact h56
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'

/-- **`seg_wkTailU` off the transfer sites** (`seg_wkTailNN` with
`seg_unparkCallNN`). -/
theorem seg_wkTailUNN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
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
    (hsp6 : (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" = pcBl (_root_.Executable.labels exe).label + 4)
    (hZ : ∀ i, NodeZA Z exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i) (blkN i))
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) →
      ∀ x29' ra', Int64.ofBitVec ra' = (_root_.Executable.labels exe).label ".L20_wc_worker.sp6" →
      ∀ i, NodeZA Z exe endPc R' F' (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29' ra' tp i)
        (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ x, At exe endPc R F (E c2 x29 ra tp x) s c) :=
  seg_wkTailNN hF hR hal (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCallNN hF hR hal hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hsp6 hZU) hZ

end ProofNN

end HelloTail

/-- info: 'Spike.Lib.A64.Flow.Worker.HelloTail.seg_wkTailUNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms HelloTail.seg_wkTailUNN

end Spike.Lib.A64.Flow.Worker
