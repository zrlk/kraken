/-
**The phase check of the lowered code blocks** (x86-64; A9's `fnPhOk`):
for every `func0`-shaped function of an IR program (the functions
`fnCodeOk` checks), the phase facts its segment proofs ask, checked on the
program at A6's tables (`phOf`, `okPcOf`) and the cells' code labels
(`labC`), fail-closed:

- `proPhOk`: the Boolean form of the prologue's `ProPh`
  (`Spike/Lib/LowerX64/UserW.lean`), its blocks' `blkPh` at their pcs, the
  limit's load off the sites and in its next pc's phase;
- with an instruction, the local overflow block's `blkPh` (`ovfBlk` at
  `ovfL`: its call target `scc_rt_abort` in its phase);
- `bodyPhOk` (`Spike/Lib/LowerX64/BodyPh.lean`) at the return address after
  `scc_rt_main`'s `call` (`.Lscc_rt_main.x2`);
- every label the checks read resolves (`res`: the function's, its check's
  and its body's labels and every branch or call target of the blocks,
  `blkLabs`), so that `labC` is the loader's label on them.

`blkPh_congr`: `blkPh` reads the labels only at the blocks' targets, so two
label maps agreeing on `blkLabs` give the same check. The projections to the
consumers' premises are in `Spike/Lib/LowerX64/PhOfPlaceOK.lean`; this file
stays free of the segment proofs so that `PlaceOK` (A9) reads it.
-/
import Spike.Lib.LowerX64.BodyPh
import Scc.Cert.Rt.PhasesX64

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64Consumer (blkPh aiTgts)
open Spike.Lib.X64.Flow (xHead xLea xCmp xFr)
open Scc.Emit.X64 (labelOf)
open Scc.Sem.X64 (codeLabel)

/-! ## The labels a block reads -/

/-- The label of a branch or call. -/
def aiLab : AI → Option String
  | .jmp L | .call L | .jcc _ L => some L
  | _ => none

/-- **The labels a block's checks read**: its branches' and calls' targets. -/
def blkLabs (blk : List (Directive × Nat)) : List String :=
  blk.filterMap fun dz => (classify dz.1).bind aiLab

theorem aiTgts_congr {lab lab' : String → Int64} {fall ra : Int64} {a : AI}
    (h : ∀ L, aiLab a = some L → lab L = lab' L) : aiTgts lab fall ra a = aiTgts lab' fall ra a := by
  cases a <;> simp only [aiTgts, aiLab] at h ⊢ <;> first | rfl | rw [h _ rfl]

/-- **`blkPh` reads the labels at the block's targets only.** -/
theorem blkPh_congr {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Nat → Bool} {lab lab' : String → Int64}
    {pc ra : Int64} {blk : List (Directive × Nat)} (h : ∀ L ∈ blkLabs blk, lab L = lab' L) :
    blkPh okPc ph dead lab pc ra blk = blkPh okPc ph dead lab' pc ra blk := by
  unfold blkPh
  congr 1
  funext k
  congr 1
  cases hk : blk[k]? with
  | none => rfl
  | some dz =>
    simp only
    cases hc : classify dz.1 with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨dz, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-! ## The checks -/

/-- **The Boolean form of the prologue's phase facts** (`ProPh`). -/
def proPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (fn sc : Label) (Z : Int64)
    (L : Label) (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab fn + Int64.ofNat 0) 0 xHead &&
  blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat 0) 0 (xLea Z zl) &&
  okPc (lab sc + Int64.ofNat zl).toBitVec.toNat &&
  ph (lab sc + Int64.ofNat zl + Int64.ofNat zf).toBitVec.toNat == ph (lab sc + Int64.ofNat zl).toBitVec.toNat &&
  blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (zl + zf)) 0 (xCmp L z1 z2) &&
  blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (zl + zf + z1 + z2)) 0 (xFr Z zs ps)

/-- The labels the prologue's blocks read. -/
def proLabs (Z : Int64) (L : Label) (zl z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) : List String :=
  blkLabs xHead ++ blkLabs (xLea Z zl) ++ blkLabs (xCmp L z1 z2) ++ blkLabs (xFr Z zs ps)

/-- **One function's phase facts**, at the frame `fr`, its label `fn`, its
body `is`/`w`, the return address `ra`, every label read resolving
(`res`): the prologue's at the sizes the listing gives its five cells, with
an instruction the local overflow block's (`ovfBlk` at `ovfL`, its call into
`scc_rt_abort`), the body's. -/
def fnPh1 (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) (fn : String) (is : List Scc.IR.Inst)
    (w : Scc.IR.Operand) (ra : Int64) : Bool :=
  match sizesAt cells (labelOf fr.fn "chk") 0 5 with
  | [zl, zf, z1, z2, zs] =>
    res fn && res (labelOf fr.fn "chk") && res (labelOf fn "entry") &&
      (proLabs (Int64.ofInt fr.size) (proL fr) zl z1 z2 zs []).all res &&
      (bodyBlks cells fr (labelOf fn "entry") 0 is [w]).all (fun x => (blkLabs x.2).all res) &&
      proPhOk okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [] &&
      (is.isEmpty || (res (ovfL fr) && (blkLabs ovfBlk).all res &&
        blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 ovfBlk)) &&
      bodyPhOk okPc ph (fun _ => false) lab cells fr (labelOf fn "entry") is [w] ra
  | _ => false

/-- **Every `func0`-shaped function's phase facts** (the functions
`fnCodeOk` checks). -/
def fnPhAll (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  ir.funcs.all fun f =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then fnPh1 okPc ph lab res cells (frOf ir f) f.name is w ra else true
    | _, _, _ => true

/-- **A code label's address** in the cells at `lo` (`0` if it does not
resolve; `fnPhOk` then fails on every label it reads). -/
def labC (lo : Nat) (cells : List (Directive × Nat)) (l : String) : Int64 :=
  Int64.ofNat ((codeLabel lo cells l).getD 0)

/-- The return label of `scc_rt_main`'s `call` of the user `main`. -/
def raL : String := ".Lscc_rt_main.x2"

/-- **A9's phase part**: at A6's phase table and sites of the cells at
`lo` (`false` if either is missing) and the cells' code labels, every
`func0`-shaped function's phase facts, the return address after
`scc_rt_main`'s `call`. -/
def fnPhOk (lo : Nat) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (ir : Scc.IR.Program) : Bool :=
  match Scc.Cert.Rt.X64.phTabOf lo cells, Scc.Cert.Rt.X64.sitesOf lo cells Λ with
  | some T, some ss =>
    (codeLabel lo cells raL).isSome &&
      fnPhAll (fun pc => !ss.contains pc) T.ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells ir
        (labC lo cells raL)
  | _, _ => false

/-! ## Its parts -/

/-- **`fnPhOk`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem fnPhOk_parts {lo : Nat} {Λ : Scc.Sem.Layout} {cells : List (Directive × Nat)} {ir : Scc.IR.Program}
    (h : fnPhOk lo Λ cells ir = true) :
    (codeLabel lo cells raL).isSome = true ∧
      fnPhAll (Scc.Cert.Rt.X64.okPcOf lo cells Λ) (Scc.Cert.Rt.X64.phOf lo cells) (labC lo cells)
        (fun l => (codeLabel lo cells l).isSome) cells ir (labC lo cells raL) = true := by
  unfold fnPhOk at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true] at h
    have hph : Scc.Cert.Rt.X64.phOf lo cells = T.ph := by unfold Scc.Cert.Rt.X64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.X64.okPcOf lo cells Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.X64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`fnPhAll` at a lowered code block**: `func0 name r` a function of
`ir`, its instructions `addChk`s and its result one operand. -/
theorem fnPhAll_func0 {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {cells : List (Directive × Nat)} {ir : Scc.IR.Program} {ra : Int64} (h : fnPhAll okPc ph lab res cells ir ra = true)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} (hf : Scc.Lower.Inv.func0 name r ∈ ir.funcs)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    fnPh1 okPc ph lab res cells (frOf ir (Scc.Lower.Inv.func0 name r)) name r.insts w ra = true := by
  have hall : r.insts.all isAddChk = true := by
    rw [List.all_eq_true]; intro i hi; obtain ⟨d, a, b, rfl⟩ := hI i hi; rfl
  have := List.all_eq_true.mp h _ hf
  obtain ⟨insts, ret, next, marked, here⟩ := r
  simp only at hw hall
  subst hw
  simpa only [Scc.Lower.Inv.func0, hall, ite_true] using this

end Spike.Lib.LowerX64
