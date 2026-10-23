/-
**The emitted body's placement, from the function's frame** (x86-64); the
twin of `Spike/Lib/LowerA64/BodyIn.lean`.

`bodyIn cells fr l off insts ret`: a closed Boolean that walks a lowered
body's instructions (`Scc.Lower.Inv.lower0`'s `addChk` sequence, then the
return of `ret`), keeping a running byte offset `off` after the label `l`.
For each instruction it emits the construct's directives from the frame
`fr` (`getOp`, `addChecked`, the slot store; the return's `getOp ++
epilogue`) and checks each block with `blkAt` at its offset. `bodyCode_of`
turns the check into `BodyCode` in any valid layout. The check is
discharged per program by `decide +kernel`. It reads only the listing's
cell run after `l`, independent of how `--blocks` groups it.

Where x86-64 differs from AArch64: the cells have sizes. `blkAt` reads a
block's sizes off the listing (`sizesAt`: the sizes of the cells at the
offset) and checks the block at them (`blockAtB`); the running offset moves
by the sizes' sum (AArch64: `4` bytes a directive, an instruction count).
-/
import Spike.Lib.LowerX64.Body
import Spike.Lib.X64CodeSegs

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_add' ofNat_zero')
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field after cellRun dropBytes)

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64}

/-- **`blkAt` gives the block's code** at its sizes. -/
theorem blkAt_code (hp : Lays exe cells) (hend : endPc = endOf exe cells) {l : String} {off : Nat}
    {ds : List Directive} (h : blkAt cells l off ds = true) :
    (sizesAt cells l off ds.length).length = ds.length ∧
      CdOf exe endPc ((_root_.Executable.labels exe).label l + Int64.ofNat off)
        (ds.zip (sizesAt cells l off ds.length)) := by
  simp only [blkAt, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, code_field hp hend h.2 rfl⟩

/-- **`bodyIn` gives the body's code** in any valid layout of `cells`. -/
theorem bodyCode_of (hp : Lays exe cells) (hend : endPc = endOf exe cells) {fr : Scc.Emit.X64.Frame}
    {l : String} :
    ∀ (is : List Scc.IR.Inst) (off : Nat) (ws : List Scc.IR.Operand), bodyIn cells fr l off is ws = true →
      BodyCode fr (CdOf exe endPc) ((_root_.Executable.labels exe).label l + Int64.ofNat off) is ws := by
  intro is
  induction is with
  | nil =>
    intro off ws h
    match ws, h with
    | [w], h =>
      cases hg : getOp fr .rax w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg] at h
        obtain ⟨hz, hc⟩ := blkAt_code hp hend h
        exact ⟨lw, _, hg, hz, hc⟩
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro off ws h
    cases i
    case addChk d a b =>
      cases ha : getOp fr .rax a <;> cases hb : getOp fr .rcx b <;> cases hd : rsOf fr d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.some la lb o =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        obtain ⟨hz1, hc1⟩ := blkAt_code hp hend h1
        obtain ⟨hz2, hc2⟩ := blkAt_code hp hend h2
        generalize sizesAt cells l off (addDirs fr la lb).length = zs at hz1 hc1 hc2 hz2 h3
        generalize hzz : sizesAt cells l (off + zs.sum) [stDir o].length = zz at hz2 hc2 h3
        match zz, hz2 with
        | [z], _ =>
        refine ⟨la, lb, o, zs, z, ha, hb, hd, hz1, hc1, ?_, ?_⟩
        · rw [← ofNat_add']; exact hc2
        · have := ih _ ws h3
          rwa [ofNat_add', ofNat_add', List.sum_singleton] at this
    all_goals simp [bodyIn] at h

/-- The code predicate of a body's blocks: the code at `pc`, and `blk` one
of `S`'s blocks at its byte offset after `l`. -/
def CdIn (exe : _root_.Executable) (endPc : Int64) (l : String) (S : List (Nat × List (Directive × Nat)))
    (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  CdOf exe endPc pc blk ∧ ∃ j, pc = (_root_.Executable.labels exe).label l + Int64.ofNat j ∧ (j, blk) ∈ S

/-- **`bodyIn` gives the body's code with its blocks' offsets**: `BodyCode`
at every block of `bodyBlks` among `S`'s. -/
theorem bodyCode_in (hp : Lays exe cells) (hend : endPc = endOf exe cells) {fr : Scc.Emit.X64.Frame}
    {l : String} {S : List (Nat × List (Directive × Nat))} :
    ∀ (is : List Scc.IR.Inst) (off : Nat) (ws : List Scc.IR.Operand), bodyIn cells fr l off is ws = true →
      (∀ x ∈ bodyBlks cells fr l off is ws, x ∈ S) →
      BodyCode fr (CdIn exe endPc l S) ((_root_.Executable.labels exe).label l + Int64.ofNat off) is ws := by
  intro is
  induction is with
  | nil =>
    intro off ws h hS
    match ws, h with
    | [w], h =>
      cases hg : getOp fr .rax w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg] at h
        obtain ⟨hz, hc⟩ := blkAt_code hp hend h
        exact ⟨lw, _, hg, hz, hc, off, rfl, hS _ (by simp [bodyBlks, hg])⟩
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro off ws h hS
    cases i
    case addChk d a b =>
      cases ha : getOp fr .rax a <;> cases hb : getOp fr .rcx b <;> cases hd : rsOf fr d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.some la lb o =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        simp only [bodyBlks, ha, hb, hd] at hS
        have hm1 := hS _ (List.mem_cons_self ..)
        have hm2 := hS _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hrest := fun x hx => hS x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
        obtain ⟨hz1, hc1⟩ := blkAt_code hp hend h1
        obtain ⟨hz2, hc2⟩ := blkAt_code hp hend h2
        generalize sizesAt cells l off (addDirs fr la lb).length = zs at hz1 hc1 hc2 hz2 h3 hm1 hm2 hrest
        generalize hzz : sizesAt cells l (off + zs.sum) [stDir o].length = zz at hz2 hc2 h3 hm2 hrest
        match zz, hz2 with
        | [z], _ =>
        refine ⟨la, lb, o, zs, z, ha, hb, hd, hz1, ⟨hc1, off, rfl, hm1⟩,
          ⟨?_, off + zs.sum, (ofNat_add' _ _ _).symm, hm2⟩, ?_⟩
        · rw [← ofNat_add']; exact hc2
        · have := ih _ ws h3 hrest
          rwa [ofNat_add', ofNat_add', List.sum_singleton] at this
    all_goals simp [bodyIn] at h

/-- **`bodyIn` gives the body's code at its blocks** (`InBody`). -/
theorem bodyCode_inBody (hp : Lays exe cells) (hend : endPc = endOf exe cells) {fr : Scc.Emit.X64.Frame}
    {l : String} {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} (h : bodyIn cells fr l 0 is ws = true) :
    BodyCode fr (CdIn exe endPc l (bodyBlks cells fr l 0 is ws)) ((_root_.Executable.labels exe).label l) is ws := by
  have := bodyCode_in (S := bodyBlks cells fr l 0 is ws) hp hend is 0 ws h fun _ hx => hx
  rwa [ofNat_zero'] at this

end Code

end Spike.Lib.LowerX64
