import Spike.Lib.LowerX64.Node2Edges
import Spike.Lib.Src.GroupAlg

/-!
**A `ret` of words by their placements** (x86-64): the exit of a block
whose result's operands are placed by its type (`Form.group`), a locative
two operands, each operand in its result register (`%rax`, `%rdx`, …), as
the emitter moves a `ret`'s IR operands one per register (`loadArgs fr
retRegs vs`). `RetJ2` is the case of one-word placements; the setup block,
whose result holds a locative, returns by `RetJS`.

- `RetJS`, `retNS`: the exit and its node;
- `RetJS.words`: the operands' count is the result type's word count
  (`valWords`), each operand valued in its register, the words at the
  placements (`WordsRep`) under that valuation;
- `ret_edgeS`: `ret a`'s edge at `bodyN2` to `retNS` (as `ret_edgeN2`, the
  placements any `group`'s).
-/

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal SEnv sevalAt WordPl WordsRep group)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode

/-- **The return's exit by placements**: `ret a`, `a`'s words `ws` at the
placements `pls` its type `t` makes of operands `ops` (`group`), at most
six, operand `k` valued (`val`) by result register `k`, the words at their
placements under `val`; `%rbp` restored. -/
def RetJS (lbl : WeakMem.AllocLabel → Option Nat) (fp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  ∃ a t ws, ∃ ops : List Scc.IR.Operand, ∃ pls : List WordPl, ∃ val : Scc.IR.Operand → Option Nat,
    c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, ws) ∧ group t ops = some pls ∧
    ops.length ≤ Scc.Emit.X64.retRegs.length ∧
    (∀ k (hk : k < ops.length) (hr : k < Scc.Emit.X64.retRegs.length),
      val ops[k] = some (σ.regs.get64 Scc.Emit.X64.retRegs[k]).toNat) ∧
    WordsRep lbl val ws pls ∧ σ.regs.get64 .rbp = fp

/-- **The return's exit node by placements**: `%rsp` past the popped
return address. -/
def retNS (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) : ND :=
  ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => RetJS lbl fp σ c ∧ LocalRun p c0 c⟩

/-- **The result's operands by register** (for the caller of the setup
block): as many operands as the result type's words, each valued by its
result register, the words at their placements. -/
theorem RetJS.words {lbl : WeakMem.AllocLabel → Option Nat} {fp : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJS lbl fp σ c) :
    ∃ a t ws, ∃ ops : List Scc.IR.Operand, ∃ pls : List WordPl, ∃ val : Scc.IR.Operand → Option Nat,
      c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, ws) ∧
      (∀ n, Scc.Obj.valWords t = some n → ops.length = n) ∧ ops.length ≤ Scc.Emit.X64.retRegs.length ∧
      (∀ k (hk : k < ops.length) (hr : k < Scc.Emit.X64.retRegs.length),
        val ops[k] = some (σ.regs.get64 Scc.Emit.X64.retRegs[k]).toNat) ∧
      WordsRep lbl val ws pls := by
  obtain ⟨a, t, ws, ops, pls, val, ht, hh, he, hg, hn, hv, hw, -⟩ := h
  refine ⟨a, t, ws, ops, pls, val, ht, hh, he, fun n hn' => ?_, hn, hv, hw⟩
  have h1 := (group_grp hg).1
  rw [valWords_opLen hn'] at h1
  exact (Option.some.inj h1).symm

section RetS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {c0 : Ctl}
  {lits : List (String × Scc.Lower.LitV)}
  {cs bufs : List (String × Nat)}

/-- **`ret a`'s edge by placements at `bodyN2`**: `a`'s operands `vs`
(placed by its type, `group`) loaded into the result registers (`getOps`
into `retRegs`), the epilogue, `ret`; lands at `retNS`. -/
theorem ret_edgeS {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (retDirs lw).length) (lab : String → Int64) {fp ra : BitVec 64} {a : At} {s : SEnv}
    {t : Ty} {pls : List WordPl} (hsa : sevalAt s a = some (t, pls)) (hg : group t vs = some pls)
    {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc (.ret a) s lits cs bufs)
      ((retDirs lw).zip zs) (fun _ : Unit => retNS p lbl fp ra c0) (fun e : Empty => e.elim) := by
  have hrr : Scc.Emit.X64.retRegs = Spike.Lib.X64.retRegs := rfl
  rw [hrr] at hl hn
  obtain ⟨rws, hlen, hd, hoks, hvs⟩ := getOps_rw hf h1 hl hn
  have hblk : retDirs lw = retBlk rws := by
    rw [retDirs, dirs_append, dirs_epiItems, hd]; rfl
  rw [hblk] at hz ⊢
  have hne : (retBlk rws).zip zs ≠ [] := by
    intro h
    have h' := congrArg List.length h
    simp only [List.length_zip, List.length_nil, ← hz, Nat.min_self] at h'
    rw [h'] at hz
    simp [retBlk, epi] at hz
  refine ⟨hne, retBlk_ok (by omega) hoks hz, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  obtain ⟨c1, hr, hj, -, -, -, -⟩ := hJ
  obtain ⟨t', ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  have hg' := (Spike.Lib.Form.group_of_eraseLen hE vs).trans hg
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨c1, hr, .inl ⟨(), retBlk_hit lab pc (-(fr.size : Int)) σ rws hz (by simp [retNS, hra]) rfl ?_⟩⟩
  intro σ' hsl _ hbp _ hreg
  refine ⟨⟨a, t', ws, vs, pls, opdVal (rsOf fr) σ.slot, hj.1, hj.2.1, he, hg', hrr ▸ hn, fun k hk hk2 => ?_, hw,
    ?_⟩, hc0.trans hr⟩
  · have hkr : k < rws.length := hlen ▸ hk
    rw [hvs k hk hkr σ.slot]
    have hm : (Spike.Lib.X64.retRegs[k]'(hrr ▸ hk2), rws[k]) ∈ Spike.Lib.X64.retRegs.zip rws := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩
    have := hreg _ _ hm
    simp only [hrr]
    rw [this]
  · rw [hbp, hfp]

end RetS

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.ret_edgeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ret_edgeS

/-- info: 'Spike.Lib.LowerX64.RetJS.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RetJS.words

end Spike.Lib.LowerX64
