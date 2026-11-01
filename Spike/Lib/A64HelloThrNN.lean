/-
**hello.w's thread worker off the transfer sites** (`WCompatH.noSite`, AArch64): `HThrTail.seg_thrTail` and
`HThrHead.seg_thrHead` (`Spike/Lib/A64HelloThr.lean`) over
`SegTC (NNZ exe endPc Z)`, every state of their hidden invariants at a cell
other than a `nop` (the twins of `Wake.ThrTailW`'s and `Wake.ThrHeadW`'s
in `Spike/Lib/A64WakeWorkerNN.lean`, at hello's frame of 80 and
`wc_worker`'s region `[-144, 0)`). wake's `NNZ` is hello's `NNZH`
(`SegTC.toH`).

The proofs are the originals' with the leaves of `Spike/Lib/A64WakeNN.lean`
(`seg_ndNNA`, `ownStlr_ndNNA`, `texit_ndNNA`, `call_ndTS`). Each segment
keeps `Z` at its nodes' states, given per node as
`NodeZA Z exe endPc R F (N i) (blkN i)` (`hZ`; `NodeZ.toAOf … (lenN_eq i)`
from a `NodeZ`).

- `HThrTail.lenN`, `HThrTail.blkN`, `HThrTail.seg_thrTailNN`: the tail, to
  any fragment.
- `HThrHead.lenN`, `HThrHead.blkN`, `HThrHead.seg_thrHeadNN`: the head
  (`hwk` over `SegTC`).
-/
import Spike.Lib.A64HelloThr
import Spike.Lib.A64WakeNN

namespace Spike.Lib.A64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)

set_option linter.unusedSimpArgs false

namespace HThrTail

/-- Each node's block length (`1` at the store and the `svc`), the `len` of
its `NodeZ` obligation. -/
def lenN : PN → Nat
  | .sp0 => b0.length | .ex => 1 | .n2 => b1.length | .svc => 1

/-- Each node's block (the instruction at the store and the `svc`), the
`blk` of its `NodeZA` obligation. -/
def blkN : PN → List Directive
  | .sp0 => b0 | .ex => [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] | .n2 => b1
  | .svc => [svcDir]

theorem lenN_eq (i : PN) : lenN i = (blkN i).length := by cases i <;> rfl

section ProofNN

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {tp : BitVec 64}
  {Z : Frag isaLSE2}

set_option hygiene false in
/-- A block node off the transfer sites: the block, its `okBlk`, its code;
the edge is left. -/
local macro "tnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| refine seg_ndNNA (by simp [$b:ident]) $ok (by simp [$b:ident, notNop]) hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZ _))

/-- Hitting node `j`. -/
local macro "thit " j:term : tactic =>
  `(tactic| (refine .inl ⟨$j, ?_, rfl, ?_⟩ <;> simp_all [N, Spike.Lib.upd_apply, Reg64s.getSysReg,
    KeepTP.setRegOrZr_tp, KeepTP.setXReg_tp]))

/-- **`seg_thrTail` off the transfer sites.** -/
theorem seg_thrTailNN {Q : Frag isaLSE2} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (tp + 24#64) 1#64) {a : CoreTerm.At} (ht : c0.term = .ret a)
    (hcode : Code pfx c0 tp exe endPc)
    (hZ : ∀ i, NodeZA Z exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 tp i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (N pfx (_root_.Executable.labels exe).label c0 tp .sp0)) Q := by
  refine (fn_segTS (N := N pfx _ c0 tp) (E := (nofun : Empty → ND)) (fun i => ?_) PN.sp0).mono_post
    fun _ _ ⟨x, _⟩ => x.elim
  cases i
  case sp0 => tnode b0 b0_ok sp0; rw [N, b0_run]; thit PN.ex
  case ex =>
    refine ownStlr_ndNNA (A := tp + 24#64) (fun s he hn => hcode.ex s he hn) (fun m σ c _ _ hJ => ?_) (hZ .ex).toW
    obtain ⟨rfl, h10, h9⟩ := hJ
    refine ⟨h10, by rw [Spike.Lib.A64.Flow.Ret0.getRegOrZr_x9, h9]; exact hS, ?_⟩
    thit PN.n2
  case n2 => tnode b1 b1_ok n2; rw [N, b1_run]; thit PN.svc
  case svc =>
    refine texit_ndNNA hK (fun s he hn => hcode.svc s he hn) (fun σ c ⟨hc, h8⟩ => ⟨by rw [h8]; rfl, a, ?_⟩) (hZ .svc).toW
    rw [hc]; exact ht

end ProofNN

end HThrTail

namespace HThrHead

/-- Each node's block length (`0` at the call), the `len` of its `NodeZ`
obligation. -/
def lenN : TN → Nat
  | .e => thE.length | .call => 0

/-- Each node's block (none at the call), the `blk` of its `NodeZA`
obligation. -/
def blkN : TN → List Directive
  | .e => thE | .call => []

theorem lenN_eq (i : TN) : lenN i = (blkN i).length := by cases i <;> rfl

section ProofNN

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {Z : Frag isaLSE2}

/-- **`seg_thrHead` off the transfer sites** (`hwk` over `SegTC`). -/
theorem seg_thrHeadNN {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label (pfx ++ ".0_entry")) thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -144 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-80) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-80) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-80) (-144) 0).Off (k - (-80)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-80 + (Ex g x).o.sp, []⟩, σR⟩ c')
    (hZ : ∀ i, NodeZA Z exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L i) (blkN i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (Q := At exe endPc R F (tN pfx lab J L .call))
    ((seg_ndNNA (blk := thE) (N := fun _ : Unit => tN pfx lab J L .call) (E := (nofun : Empty → ND)) (by simp [thE]) thE_ok
      (by simp [thE, notNop]) hF hR hal hlo hhi hcodeE (fun σ c hJ => ?_) (hZ .e)) |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndTS (lo' := -144) (hi' := 0) hR hal hF (by show R.lo ≤ -80 + -144; omega) (by decide)
      (by show (-80 : Int) < R.hi; omega) (by decide) (by show (-80 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end ProofNN

end HThrHead

end Spike.Lib.A64.Flow.Worker.Hello

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.HThrTail.seg_thrTailNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.HThrTail.seg_thrTailNN

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.HThrHead.seg_thrHeadNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.HThrHead.seg_thrHeadNN
