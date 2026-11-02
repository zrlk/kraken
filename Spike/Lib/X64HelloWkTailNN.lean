/-
**hello.w's `wc_worker` tail off the transfer sites on x86-64** (the twin of
`Spike/Lib/A64HelloWkTailNN.lean`): the segments of hello's `wc_worker`
tail (`Spike/Lib/X64HelloWkTail.lean`) over `SegTC (NNZ exe endPc Z)`, every
state of their hidden invariants at a cell other than a `nop`, each node
keeping a fragment `Z` at its executing offsets (`NodeZA`), as wake.w's
x86-64 `WkTailW` ones (`Spike/Lib/X64WakeWorkerNNA.lean`).

- `HelloTail.blkN`: each node's block (`[]` at the call node).
- `HelloTail.NA`: the nodes at their executing offsets (the epilogue `.x18`
  at `oI`, `%rbp` claimed back from the invariant).
- `seg_wkTailNN`: from `.x17` to the return, the call of `scc_rt_unpark`
  given over `SegTC`.
- `seg_unparkCallNN`: the call (`call_ndTSA` with
  `Unpark.seg_unparkNNA`, the callee's frame `[-40, 8)` from the call's
  `%rsp` at offset `-96`).
- `seg_wkTailUNN`: the two together (the region down to `-136`).

## Differences from the AArch64 version

- `NodeZA` is indexed by a node's block (`blkN`, sized cells), not by a
  count of 4-byte instructions: A64's `lenN`, `lenN_eq` have no twin.
- The obligations are at the executing offsets (`NA`; `NodeZA`, `CallerF`
  for the callee) and the epilogue claims `%rbp`'s offset back
  (`WaitLoop.At.rbpOf`), as in `X64WakeWorkerNNA`; no alignment premise
  (`hal`).
- The return label premise is `hx18 : .x18 = .x17 + 14 + 9` (the `call`'s
  end), the unpark entry premise `hpentry` as in wake.w's.
-/
import Spike.Lib.X64HelloWkTail
import Spike.Lib.X64WakeWorkerNNA

namespace Spike.Lib.X64.Flow.Worker

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)

set_option linter.unusedSimpArgs false

namespace HelloTail

/-- Each node's block (the store's cell; `[]` at the call node), the block
of its `NodeZ` obligation. -/
def blkN : PN → List (Directive × Nat)
  | .e => b0 | .st => [(stDir .rcx 0 .rax, 3)] | .n3 => b1 | .unpk => [] | .x18 => b2

/-- **The nodes at their executing offsets**: `N`, but the epilogue `.x18`
at the frame's offsets with `%rbp` (`oI`, claimed back from the invariant:
`WaitLoop.At.rbpOf`), the node its block runs from. -/
def NA (lab : Label → Int64) (c0 c1 c2 : Ctl) (A B rbp0 ra tp sp : BitVec 64) : PN → ND
  | .e => N lab c0 c1 c2 A B rbp0 ra tp sp .e
  | .st => N lab c0 c1 c2 A B rbp0 ra tp sp .st
  | .n3 => N lab c0 c1 c2 A B rbp0 ra tp sp .n3
  | .unpk => N lab c0 c1 c2 A B rbp0 ra tp sp .unpk
  | .x18 => ⟨(N lab c0 c1 c2 A B rbp0 ra tp sp .x18).pc, oI, (N lab c0 c1 c2 A B rbp0 ra tp sp .x18).J⟩

section ProofNNA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 c1 c2 : Ctl}
  {A B rbp0 ra tp sp : BitVec 64} {Z : Frag isa}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "wnode " b:ident ok:ident f:ident i:term : tactic =>
  `(tactic| refine seg_ndNNA (blk := $b:ident) (by simp [$b:ident]) $ok (by decide) hF hR hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ $i))

/-- Hitting node `j`. -/
local macro "whit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;>
    simp_all [N, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self,
      Reg64s.get64_set64_ne, KeepTP.set64_tp, Reg64s.set64, Reg64s.get64]))

/-- **`WkTailW.seg_wkTailW`'s twin off the transfer sites** (`hunpk` over `SegTC`). -/
theorem seg_wkTailNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -96) (hhi : 8 ≤ R.hi)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B rbp0 ra tp (R.addr 0) exe endPc)
    (hunpk : SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .x18)))
    (hZ : ∀ i, NodeZA Z exe endPc R F (NA (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) i)
      (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 rbp0 ra tp x) s c) := by
  refine fn_segTS (N := N _ c0 c1 c2 A B rbp0 ra tp (R.addr 0)) (E := E c2 rbp0 ra tp) (fun i => ?_) PN.e
  cases i
  case e => wnode b0 b0_ok e PN.e; rw [N, b0_run]; whit PN.st
  case st =>
    refine relStore_ndNNA (A := A) (fun s he hn => hcode.st s he hn) hdm (fun m σ c _ _ hJ => ?_) (hZ .st).toW
    obtain ⟨⟨rfl, hJ⟩, hc, ha⟩ := hJ
    refine ⟨by rw [bAddr, hc]; simp, d, a, b, e1, ty, tb, w, wb, ht, hev, hv, htag, hevb,
      by rw [ha]; exact hvb, ?_⟩
    rw [← hc1]
    whit PN.n3
  case n3 => wnode b1 b1_ok n3 PN.n3; rw [N, b1_run]; whit PN.unpk
  case unpk => exact hunpk.mono_post fun s c h => .inl ⟨PN.x18, h⟩
  case x18 =>
    let n := N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .x18
    refine (seg_ndNNA (n := ⟨n.pc, oI, n.J⟩) (blk := b2) (by simp [b2]) b2_ok (by decide) hF hR hlo hhi
      (fun s he hn => hcode.x18 s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ .x18)).mono_pre
      fun _ _ h => WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.2.2.2.2, WaitLoop.addr0_sub8]
    rw [b2_run]
    refine .inr ⟨PX.ret, ?_, rfl, ?_⟩ <;>
      simp_all [n, N, E, JI, Int64.add_assoc, upd_apply, Reg64s.get64_set64_self, Reg64s.get64_set64_ne,
        KeepTP.set64_tp]

/-- **`WkTailW.seg_unparkCallW`'s twin off the transfer sites** (`call_ndTSA` with
`Unpark.seg_unparkNNA`). -/
theorem seg_unparkCallNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {jw : TermRun.Word}
    (ht : c1.term = .let_ x (.ext .unpark a) e) (hh : c1.hold = none)
    (hev : TermRun.evalAt c1.env a = some (ty, [jw])) (hv : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' rbp0' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hx18 : (_root_.Executable.labels exe).label ".Lwc_worker.x18" =
      (_root_.Executable.labels exe).label ".Lwc_worker.x17" + 14 + 9)
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop),
      CallerF R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .unpk) 0 (-40) 8 R' F' →
      ∀ rbp1 ra1, Int64.ofBitVec ra1 = (_root_.Executable.labels exe).label ".Lwc_worker.x18" →
      ∀ i, NodeZA Z exe endPc R' F' (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
        (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .unpk))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x18)) := by
  refine (call_ndTSA (e0 := 0) (lo' := -40) (hi' := 8)
    (N := fun _ : Unit => N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp sp .x18)
    (E := fun e : Empty => e.elim)
    (Ne := fun g : {g : BitVec 64 × BitVec 64 //
        Int64.ofBitVec g.2 = (_root_.Executable.labels exe).label ".Lwc_worker.x18"} =>
      Unpark.N (_root_.Executable.labels exe).label c1 c2 B g.1.1 g.1.2 tp .e)
    (Ex := fun g y => Unpark.E c2 g.1.1 g.1.2 tp y)
    hR hF (by show R.lo ≤ -96 - 0 + -40; omega) (by decide) (by show (-96 : Int) - 0 < R.hi; omega)
    (by show (-96 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-96 : Int) - 0) % 8 = 0; decide) (by decide)
    (by decide)
    (fun R' F' hC g =>
      Unpark.seg_unparkNNA hC.stab hC.ok hC.lo hC.hi hK (hS.mono fun m hm => (hC.sees m hm).1) htp4 ht hh hev hv
        hc2 hpcode.ghost hpentry (hZU R' F' hC g.1.1 g.1.2 g.2))
    (fun _ => rfl) ?_ ?_).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  · rintro σC c ⟨⟨rfl, -, -, -, -, htp, -⟩, hdi, h96⟩
    refine ⟨⟨(σC.regs.rbp.toBitVec, σC.slot (-96 - 0 + 0)), ?_⟩, rfl, rfl, hdi, rfl, rfl, htp⟩
    -- the pushed return address is `.x18` (the node's slot `-96`)
    refine Eq.symm ?_
    show (_root_.Executable.labels exe).label ".Lwc_worker.x18" = Int64.ofBitVec (σC.slot (-96))
    rw [h96, hx18]; rfl
  · rintro ⟨⟨rbp1, ra1⟩, _hg⟩ ⟨⟩ σC c σx c' σR ⟨⟨rfl, h8, h0, h48, h56, -, hbp⟩, -, h96⟩ ⟨hc, -, hrb, hra, -⟩
      ⟨hc', hrb', htp'⟩ hreg - - hslot
    have hout : ∀ k : Int, -88 ≤ k → k % 8 = 0 → k ≤ 0 → σR.slot k = σC.slot k := fun k h1 h2 h3 =>
      hslot k ⟨h2, by omega, by omega⟩ fun ⟨_, _, h⟩ => by
        simp only [Region.callee, N] at h; omega
    refine .inl ⟨(), ?_, by show SO.le oP ⟨-96 - 0 + 8, []⟩ = true; decide, hc',
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · subst hra
      show (_root_.Executable.labels exe).label ".Lwc_worker.x18" = Int64.ofBitVec (σC.slot (-96))
      rw [h96, hx18]; rfl
    · rw [hout (-8) (by decide) (by decide) (by decide)]; exact h8
    · rw [hout 0 (by decide) (by decide) (by decide)]; exact h0
    · rw [hout (-48) (by decide) (by decide) (by decide)]; exact h48
    · rw [hout (-56) (by decide) (by decide) (by decide)]; exact h56
    · show σR.regs.fsBase.toBitVec = tp
      rw [hreg]; exact htp'
    · show σR.regs.rbp.toBitVec = _
      have : σx.regs.get64 .rbp = rbp1 := hrb'
      rw [hreg]; simp only [Reg64s.get64] at this; rw [this]
      exact (show σC.regs.rbp.toBitVec = rbp1 from hrb).symm.trans hbp

/-- **`WkTailW.seg_wkTailWU`'s twin off the transfer sites** (`seg_wkTailNN` with
`seg_unparkCallNN`). -/
theorem seg_wkTailUNN (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -136) (hhi : 8 ≤ R.hi)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c0.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c0.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: c0.env, none⟩)
    (hcode : Code c0 c1 c2 A B rbp0 ra tp (R.addr 0) exe endPc)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    {c0' c1' : Ctl} {B' rbp0' ra' tp' : BitVec 64} (hpcode : Unpark.Code c0' c1' B' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_unpark.entry" =
      (_root_.Executable.labels exe).label "scc_rt_unpark" + 12)
    (hx18 : (_root_.Executable.labels exe).label ".Lwc_worker.x18" =
      (_root_.Executable.labels exe).label ".Lwc_worker.x17" + 14 + 9)
    (hZ : ∀ i, NodeZA Z exe endPc R F (NA (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) i)
      (blkN i))
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop),
      CallerF R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .unpk) 0 (-40) 8 R' F' →
      ∀ rbp1 ra1, Int64.ofBitVec ra1 = (_root_.Executable.labels exe).label ".Lwc_worker.x18" →
      ∀ i, NodeZA Z exe endPc R' F' (Unpark.N (_root_.Executable.labels exe).label c1 c2 B rbp1 ra1 tp i)
        (Unpark.blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 c1 c2 A B rbp0 ra tp (R.addr 0) .e))
      (fun s c => ∃ x, At exe endPc R F (E c2 rbp0 ra tp x) s c) :=
  seg_wkTailNN hF hR (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 hcode
    (seg_unparkCallNN hF hR hlo hhi hK hS htp4 htu hhu hevu hvu hc2 hpcode hpentry hx18 hZU) hZ

end ProofNNA

end HelloTail

end Spike.Lib.X64.Flow.Worker

/-- info: 'Spike.Lib.X64.Flow.Worker.HelloTail.seg_wkTailNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.HelloTail.seg_wkTailNN

/-- info: 'Spike.Lib.X64.Flow.Worker.HelloTail.seg_unparkCallNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.HelloTail.seg_unparkCallNN

/-- info: 'Spike.Lib.X64.Flow.Worker.HelloTail.seg_wkTailUNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.HelloTail.seg_wkTailUNN
