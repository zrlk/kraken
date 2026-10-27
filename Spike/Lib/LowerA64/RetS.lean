import Spike.Lib.LowerA64.Node2Edges
import Spike.Lib.Src.GroupAlg

/-!
**A `ret` of words by their placements** (AArch64): the exit of a block
whose result's operands are placed by its type (`Form.group`), a locative
two operands, each operand in its argument register (`x0`, `x1`, …), as
the emitter moves a `ret`'s IR operands one per register (`FnCtx.term`'s
`.ret vs`). `RetJ2` is the case of one-word placements; the setup block,
whose result holds a locative, returns by `RetJS`.

- `RetJS`, `retNS`: the exit and its node;
- `RetJS.words`: the operands' count is the result type's word count
  (`valWords`), each operand valued in its register, the words at the
  placements (`WordsRep`) under that valuation;
- `ret_edgeS`: `ret a`'s edge at `bodyN2` to `retNS` (as `ret_edgeN2`, the
  placements any `group`'s).
-/

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal SEnv sevalAt WordPl WordsRep group)
open Spike.Lib.LowerNode

/-- **The return's exit by placements**: `ret a`, `a`'s words `ws` at the
placements `pls` its type `t` makes of operands `ops` (`group`), at most
the argument registers', operand `k` valued (`val`) by argument register
`k`, the words at their placements under `val`; the saved pair restored. -/
def RetJS (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  ∃ a t ws, ∃ ops : List Scc.IR.Operand, ∃ pls : List WordPl, ∃ val : Scc.IR.Operand → Option Nat,
    c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, ws) ∧ group t ops = some pls ∧
    ops.length ≤ argRegs.length ∧
    (∀ k (hk : k < ops.length) (hr : k < argRegs.length),
      val ops[k] = some (σ.regs.getXReg argRegs[k]).toBitVec.toNat) ∧
    WordsRep lbl val ws pls ∧ σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra

/-- **The return's exit node by placements.** -/
def retNS (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) : ND :=
  ⟨Int64.ofBitVec ra, ⟨0, []⟩, fun σ c => RetJS lbl fp ra σ c ∧ LocalRun p c0 c⟩

/-- **The result's operands by register** (for the caller of the setup
block): as many operands as the result type's words, each valued by its
argument register, the words at their placements. -/
theorem RetJS.words {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJS lbl fp ra σ c) :
    ∃ a t ws, ∃ ops : List Scc.IR.Operand, ∃ pls : List WordPl, ∃ val : Scc.IR.Operand → Option Nat,
      c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, ws) ∧
      (∀ n, Scc.Obj.valWords t = some n → ops.length = n) ∧ ops.length ≤ argRegs.length ∧
      (∀ k (hk : k < ops.length) (hr : k < argRegs.length),
        val ops[k] = some (σ.regs.getXReg argRegs[k]).toBitVec.toNat) ∧
      WordsRep lbl val ws pls := by
  obtain ⟨a, t, ws, ops, pls, val, ht, hh, he, hg, hn, hv, hw, -⟩ := h
  refine ⟨a, t, ws, ops, pls, val, ht, hh, he, fun n hn' => ?_, hn, hv, hw⟩
  have h1 := (group_grp hg).1
  rw [valWords_opLen hn'] at h1
  exact (Option.some.inj h1).symm

section RetS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {c0 : Ctl}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`ret a`'s edge by placements at `bodyN2`**: `a`'s operands `vs`
(placed by its type, `group`) loaded into `x0`, `x1`, … (`retLoads`), then
the epilogue to `retNS`. -/
theorem ret_edgeS {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty} {pls : List WordPl}
    (hsa : sevalAt s a = some (t, pls)) (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN2 p lbl lsize i cx fp ra c0 pc (.ret a) s lits cs bufs)
      (directives (ls ++ cx.leave ++ [ret])) (fun _ : Unit => retNS p lbl fp ra c0) (fun e : Empty => e.elim) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have hds := directives_leave hf h1 ls
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (ls ++ cx.leave ++ [ret])) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [hds, okBlk_retLoads hf h1 h16 _ _ hl]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this
  refine ⟨by rw [hds]; simp [epi], hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  obtain ⟨c1, hr, hj, -, -, -, -⟩ := hJ
  obtain ⟨t', ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  have hg' := (Spike.Lib.Form.group_of_eraseLen hE vs).trans hg
  obtain ⟨R, hrun, -, hval⟩ := arun_retLoads hf h1 lab _ hl pc σ
  have hsnd : ((vs.zip argRegs).map Prod.snd).Nodup := by
    exact argRegs_nodup.sublist (map_snd_zip_sublist _ _)
  refine ⟨c1, hr, .inl ⟨(), ?_⟩⟩
  show Hit (retNS p lbl fp ra c0) (arun _ (directives (ls ++ cx.leave ++ [ret])) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c1
  rw [hds, arun_append, hrun]
  obtain ⟨hpc, hso, hsl, -, h29, h30, hr0⟩ := arun_epi lab
    (pc + Int64.ofNat (4 * (directives ls).length)) (-(cx.frame : Int)) { σ with regs := R }
    (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  have h16' : (Int64.ofInt cx.frame - 16).toInt = cx.frame - 16 := by
    rw [Int64.toInt_sub, show (16 : Int64).toInt = 16 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc h30
  rw [h16', show -(cx.frame : Int) + (cx.frame - 16) = -16 by omega] at h29
  rw [hF64, show -(cx.frame : Int) + cx.frame = 0 by omega] at hso
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨?_, ?_, ⟨a, t', ws, vs, pls, opdVal (rsOf cx) σ.slot, hj.1, hj.2.1, he, hg', hn, fun k hk hr' => ?_, hw,
    ?_, ?_⟩, hc0.trans hr⟩
  · rw [hpc]; simp [retNS, hra]
  · rw [hso]; rfl
  · have hmem : (vs[k], argRegs[k]) ∈ vs.zip argRegs := by
      have hz : (vs.zip argRegs)[k]'(by simp; omega) = (vs[k], argRegs[k]) := List.getElem_zip
      rw [← hz]
      exact List.getElem_mem _
    obtain ⟨v, hv, hR⟩ := hval hsnd _ hmem
    have hne := argRegs_ne (List.getElem_mem hr')
    rw [hr0 _ hne.1 hne.2]
    simp only at hR hv
    rw [hR, hv]
  · rw [h29]; exact hfp
  · rw [h30]; exact hra

end RetS

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.ret_edgeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ret_edgeS

/-- info: 'Spike.Lib.LowerA64.RetJS.words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RetJS.words

end Spike.Lib.LowerA64
