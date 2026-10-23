/-
**The phase check of the lowered code blocks** (AArch64; A9's `fnPhOk`):
for every `func0`-shaped function of an IR program (the functions
`fnCodeOk` checks), the phase facts its segment proofs ask, checked on the
program at A6's tables (`phOf`, `okPcOf`) and the program's code labels
(`labC`), fail-closed:

- `proPhOk`: the Boolean form of the prologue's `ProPh`
  (`Spike/Lib/LowerA64/UserW.lean`), its blocks' `blkPh` at their pcs, the
  limit's load off the sites and in its next pc's phase;
- with an instruction, the local overflow block's `blkPh` (`ovfBlk` at
  `abort_overflow`: its call target `scc_rt_abort` in its phase);
- the body's phase check (`bodyPhOk`, `Spike/Lib/LowerA64/BodyW.lean`,
  written out here: `fnPh1`'s last conjunct is `bodyPhOk` by `rfl`) at the
  return address after `scc_rt_main`'s `bl` (`.L1_scc_rt_main.0_entry`
  plus 4, `raC`);
- every label the checks read resolves (`res`: the function's, its check's
  and its body's labels and every branch or call target of the blocks,
  `blkLabs`), so that `labC` is the loader's label on them.

`blkPh_congr`: `blkPh` reads the labels only at the blocks' targets, so two
label maps agreeing on `blkLabs` give the same check. The projections to the
consumers' premises are in `Spike/Lib/LowerA64/PhOfPlaceOK.lean`; this file
stays free of the segment proofs so that `PlaceOK` (A9) reads it.
-/
import Spike.Lib.LowerA64.Checks
import Spike.Lib.A64SegInst
import Scc.Cert.Rt.PhasesA64

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (blkPh aiTgts)
open Scc.Emit.A64
open Scc.Cert.Link.A64 (codeOf)

/-! ## The labels a block reads -/

/-- The label of a branch or call. -/
def aiLab : AI → Option String
  | .b L | .bl L | .bcond _ L | .cbz _ L | .cbnz _ L => some L
  | _ => none

/-- **The labels a block's checks read**: its branches' and calls' targets. -/
def blkLabs (blk : List Directive) : List String :=
  blk.filterMap fun d => (classify d).bind aiLab

theorem aiTgts_congr {lab lab' : Label → Int64} {fall ra : Int64} {a : AI}
    (h : ∀ L, aiLab a = some L → lab L = lab' L) : aiTgts lab fall ra a = aiTgts lab' fall ra a := by
  cases a <;> simp only [aiTgts, aiLab] at h ⊢ <;> first | rfl | rw [h _ rfl]

/-- **`blkPh` reads the labels at the block's targets only.** -/
theorem blkPh_congr {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Nat → Bool} {lab lab' : Label → Int64}
    {pc ra : Int64} {blk : List Directive} (h : ∀ L ∈ blkLabs blk, lab L = lab' L) :
    blkPh okPc ph dead lab pc ra blk = blkPh okPc ph dead lab' pc ra blk := by
  unfold blkPh
  congr 1
  funext k
  congr 1
  cases hk : blk[k]? with
  | none => rfl
  | some d =>
    simp only
    cases hc : classify d with
    | none => rfl
    | some a =>
      simp only
      rw [aiTgts_congr fun L hL => h L ?_]
      exact List.mem_filterMap.mpr ⟨d, List.mem_of_getElem? hk, by rw [hc]; exact hL⟩

/-! ## The checks -/

/-- **The Boolean form of the prologue's phase facts** (`ProPh`). -/
def proPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (sc : Label) (Z : Int64)
    (L : Label) (ps : List (XReg × Int64)) : Bool :=
  blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 0)) 0 (chkHead Z) &&
  okPc (lab sc + Int64.ofNat (4 * 2)).toBitVec.toNat &&
  ph (lab sc + Int64.ofNat (4 * 2) + Int64.ofNat 4).toBitVec.toNat ==
    ph (lab sc + Int64.ofNat (4 * 2)).toBitVec.toNat &&
  blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 3)) 0 (chkBr L) &&
  blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 5)) 0 (frameSet Z ps)

/-- The labels the prologue's blocks read. -/
def proLabs (Z : Int64) (L : Label) (ps : List (XReg × Int64)) : List String :=
  blkLabs (chkHead Z) ++ blkLabs (chkBr L) ++ blkLabs (frameSet Z ps)

/-- **One function's phase facts**, at its context `cx`, its label `fn`,
its body `is`/`w`, the return address `ra`, every label read resolving
(`res`): the prologue's, with an instruction the local overflow block's
(`ovfBlk` at `abort_overflow`, its call into `scc_rt_abort`), the body's
(`bodyPhOk` written out). -/
def fnPh1 (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool) (cx : FnCtx)
    (fn : String) (is : List Scc.IR.Inst) (w : Scc.IR.Operand) (ra : Int64) : Bool :=
  res fn && res (cx.local "stack_check") && res (cx.prefix ++ "0_entry") &&
    (proLabs (Int64.ofInt cx.frame) (proL cx) []).all res &&
    (bodyBlks cx 0 is [w]).all (fun x => (blkLabs x.2).all res) &&
    proPhOk okPc ph lab (cx.local "stack_check") (Int64.ofInt cx.frame) (proL cx) [] &&
    (is.isEmpty || (res (cx.local "abort_overflow") && (blkLabs ovfBlk).all res &&
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0 ovfBlk)) &&
    (bodyBlks cx 0 is [w]).all fun x =>
      blkPh okPc ph (fun _ => false) lab (lab (cx.prefix ++ "0_entry") + Int64.ofNat (4 * x.1)) ra x.2

/-- **Every `func0`-shaped function's phase facts** (the functions
`fnCodeOk` checks, at their contexts recomputed from `ir`). -/
def fnPhAll (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  ir.funcs.zipIdx.all fun (f, fi) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        fnPh1 okPc ph lab res (fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi f)
          f.name is w ra
      else true
    | _, _, _ => true

/-- **A code label's address** in the program at `lo` (`0` if it does not
resolve; `fnPhOk` then fails on every label it reads). -/
def labC (lo : Nat) (prog : Program) (l : String) : Int64 :=
  Int64.ofNat ((codeOf lo prog l).getD 0)

/-- The label of `scc_rt_main`'s body, whose first instruction is the `bl`
of the user `main`. -/
def raL : String := ".L1_scc_rt_main.0_entry"

/-- **A9's phase part**: at A6's phase table and sites of the program at
`lo` (`false` if either is missing) and its code labels, every
`func0`-shaped function's phase facts, the return address after
`scc_rt_main`'s `bl` (`raL` plus 4). -/
def fnPhOk (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) : Bool :=
  match Scc.Cert.Rt.A64.phTabOf lo prog, Scc.Cert.Rt.A64.sitesOf lo prog Λ with
  | some T, some ss =>
    (codeOf lo prog raL).isSome &&
      fnPhAll (fun pc => !ss.contains pc) T.ph (labC lo prog) (fun l => (codeOf lo prog l).isSome) ir
        (labC lo prog raL + 4)
  | _, _ => false

/-! ## Its parts -/

/-- **`fnPhOk`'s parts** at A6's `phOf`/`okPcOf`. -/
theorem fnPhOk_parts {lo : Nat} {Λ : Scc.Sem.Layout} {prog : Program} {ir : Scc.IR.Program}
    (h : fnPhOk lo Λ prog ir = true) :
    (codeOf lo prog raL).isSome = true ∧
      fnPhAll (Scc.Cert.Rt.A64.okPcOf lo prog Λ) (Scc.Cert.Rt.A64.phOf lo prog) (labC lo prog)
        (fun l => (codeOf lo prog l).isSome) ir (labC lo prog raL + 4) = true := by
  unfold fnPhOk at h
  split at h
  · next T ss hT hs =>
    simp only [Bool.and_eq_true] at h
    have hph : Scc.Cert.Rt.A64.phOf lo prog = T.ph := by unfold Scc.Cert.Rt.A64.phOf; rw [hT]
    have hok : Scc.Cert.Rt.A64.okPcOf lo prog Λ = fun pc => !ss.contains pc := by
      funext pc; unfold Scc.Cert.Rt.A64.okPcOf; rw [hs]
    rw [hph, hok]
    exact h
  · cases h

/-- **`fnPhAll` at a lowered code block**: `func0 name r` the `fi`th
function of `ir`, its instructions `addChk`s and its result one operand. -/
theorem fnPhAll_func0 {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {res : String → Bool}
    {ir : Scc.IR.Program} {ra : Int64} (h : fnPhAll okPc ph lab res ir ra = true)
    {name : Scc.IR.Sym} {r : Scc.Lower.Inv.Res} {fi : Nat} (hf : (Scc.Lower.Inv.func0 name r, fi) ∈ ir.funcs.zipIdx)
    (hI : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) {w : Scc.IR.Operand} (hw : r.ret = [w]) :
    fnPh1 okPc ph lab res (fnCtx ir.abortFn ir.growth (Scc.IR.StackMap.argAreas ir argRegs.length) fi
      (Scc.Lower.Inv.func0 name r)) name r.insts w ra = true := by
  have hall : r.insts.all isAddChk = true := by
    rw [List.all_eq_true]; intro i hi; obtain ⟨d, a, b, rfl⟩ := hI i hi; rfl
  have := List.all_eq_true.mp h _ hf
  obtain ⟨insts, ret, marked⟩ := r
  simp only at hw hall
  subst hw
  simpa only [Scc.Lower.Inv.func0, hall, ite_true] using this

end Spike.Lib.LowerA64
