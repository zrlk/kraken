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
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field after cellRun dropBytes label_labelGapB)
open Scc.Emit.X64 (i64)

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64}

/-- **`blkAt` gives the block's code** at its sizes. -/
theorem blkAt_code {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {l : String} {off : Nat}
    {ds : List Directive} (h : blkAt cells l off ds = true) :
    (sizesAt cells l off ds.length).length = ds.length ∧
      CdOf exe endPc ((_root_.Executable.labels exe).label l + Int64.ofNat off)
        (ds.zip (sizesAt cells l off ds.length)) := by
  simp only [blkAt, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, code_field hp hend h.2 rfl⟩

/-- The return's block is the load and teardown's, then `[ret]`'s. -/
theorem retZip_eq {lw : List Item} {zs1 zs2 : List Nat} (hz : zs1.length = (tearDirs lw).length) :
    (retDirs lw).zip (zs1 ++ zs2) = (tearDirs lw).zip zs1 ++ [i64 .ret].zip zs2 := by
  rw [retDirs, dirs_epiItems_split, ← tearDirs, List.zip_append hz.symm]

omit [Kraken.Executable.ValidLayout exe] in
/-- **The return's block across its label**: the load and teardown at
`pc`, `[ret]` at the label right after them, are `retDirs`' block at the
sizes `zs1 ++ zs2`. -/
theorem cd_ret {pc : Int64} {lw : List Item} {zs1 zs2 : List Nat} (hz : zs1.length = (tearDirs lw).length)
    (h1 : CdOf exe endPc pc ((tearDirs lw).zip zs1))
    (h2 : CdOf exe endPc (pc + Int64.ofNat zs1.sum) ([i64 .ret].zip zs2)) :
    CdOf exe endPc pc ((retDirs lw).zip (zs1 ++ zs2)) := by
  have e := retZip_eq (zs2 := zs2) hz
  have hs : (((tearDirs lw).zip zs1).map (·.2)).sum = zs1.sum := by
    rw [List.map_snd_zip (by omega)]
  intro s hs1 hs2
  rw [e]
  exact CodeAt.append (h1 s hs1 hs2) (by rw [hs]; exact h2 s hs1 hs2)

/-- The code predicate of a body's blocks: the code at `pc`, and `blk` one
of `S`'s blocks at its byte offset after `l`. -/
def CdIn (exe : _root_.Executable) (endPc : Int64) (l : String) (S : List (Nat × List (Directive × Nat)))
    (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  CdOf exe endPc pc blk ∧ ∃ j, pc = (_root_.Executable.labels exe).label l + Int64.ofNat j ∧ (j, blk) ∈ S

/-- **`bodyIn` gives the body's code with its blocks' offsets**: `BodyCode`
at every block of `bodyBlks` among `S`'s, from the current label `L`, `e`
bytes after `l`, `o` bytes into `L`'s run. -/
theorem bodyCode_in {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fr : Scc.Emit.X64.Frame}
    {l : String} {S : List (Nat × List (Directive × Nat))} :
    ∀ (is : List Scc.IR.Inst) (L : String) (n e o : Nat) (ws : List Scc.IR.Operand),
      bodyIn cells fr L n o is ws = true →
      (_root_.Executable.labels exe).label L = (_root_.Executable.labels exe).label l + Int64.ofNat e →
      (∀ x ∈ bodyBlks cells fr L n e o is ws, x ∈ S) →
      BodyCode fr (CdIn exe endPc l S) ((_root_.Executable.labels exe).label l + Int64.ofNat (e + o)) is ws := by
  intro is
  induction is with
  | nil =>
    intro L n e o ws h hL hS
    match ws, h with
    | [w], h =>
      cases hg : getOp fr .rax w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg, Bool.and_eq_true] at h
        obtain ⟨⟨h1, hgap⟩, h2⟩ := h
        obtain ⟨hz1, hc1⟩ := blkAt_code hp hend h1
        obtain ⟨hz2, hc2⟩ := blkAt_code hp hend h2
        have hR := label_labelGapB hp hgap
        simp only [bodyBlks, hg] at hS
        generalize sizesAt cells L o (tearDirs lw).length = zs1 at hz1 hc1 hR hS
        generalize sizesAt cells (retL fr.fn n) 0 [i64 .ret].length = zs2 at hz2 hc2 hS
        have hpc : (_root_.Executable.labels exe).label l + Int64.ofNat (e + o) =
            (_root_.Executable.labels exe).label L + Int64.ofNat o := by rw [hL, ofNat_add']
        rw [hR, ofNat_zero', ofNat_add', ← hpc] at hc2
        rw [← hpc] at hc1
        refine ⟨lw, zs1 ++ zs2, hg, ?_, cd_ret hz1 hc1 hc2, e + o, rfl, by rw [retZip_eq hz1]; exact hS _ (List.mem_singleton_self _)⟩
        rw [List.length_append, hz1, hz2, retDirs, dirs_epiItems_split, ← tearDirs, List.length_append]
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro L n e o ws h hL hS
    cases i
    case addChk d a b =>
      cases ha : getOp fr .rax a <;> cases hb : getOp fr .rcx b <;> cases hd : rsOf fr d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.some la lb off =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨h1, hgap⟩, h2⟩, h3⟩ := h
        simp only [bodyBlks, ha, hb, hd] at hS
        have hm1 := hS _ (List.mem_cons_self ..)
        have hm2 := hS _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have hrest := fun x hx => hS x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
        obtain ⟨hz1, hc1⟩ := blkAt_code hp hend h1
        obtain ⟨hz2, hc2⟩ := blkAt_code hp hend h2
        have hR := label_labelGapB hp hgap
        generalize sizesAt cells L o (addDirs fr la lb).length = zs at hz1 hc1 hR hm1 hm2 hrest
        generalize hzz : sizesAt cells (retL fr.fn n) 0 [stDir off].length = zz at hz2 hc2 h3 hm2 hrest
        match zz, hz2 with
        | [z], _ =>
        have hpc : (_root_.Executable.labels exe).label l + Int64.ofNat (e + o) =
            (_root_.Executable.labels exe).label L + Int64.ofNat o := by rw [hL, ofNat_add']
        have hR' : (_root_.Executable.labels exe).label (retL fr.fn n) =
            (_root_.Executable.labels exe).label l + Int64.ofNat (e + o + zs.sum) := by
          rw [hR, ofNat_add', ← hpc, ← ofNat_add']
        rw [hR', ofNat_zero'] at hc2
        rw [← hpc] at hc1
        refine ⟨la, lb, off, zs, z, ha, hb, hd, hz1, ⟨hc1, e + o, rfl, hm1⟩,
          ⟨?_, e + o + zs.sum, (ofNat_add' _ _ _).symm, hm2⟩, ?_⟩
        · rw [← ofNat_add']; exact hc2
        · have := ih (retL fr.fn n) (n + 1) (e + o + zs.sum) z ws (by simpa using h3) hR' (by simpa using hrest)
          rwa [ofNat_add', ofNat_add'] at this
    all_goals simp [bodyIn] at h

/-- **Every block of `bodyBlks` is in the code** at its byte offset after
`l`: from the current label `L`, `e` bytes after `l`, `o` bytes into `L`'s
run (the return's block across its label by `cd_ret`). -/
theorem cdOf_bodyBlks {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {fr : Scc.Emit.X64.Frame} {l : String} :
    ∀ (is : List Scc.IR.Inst) (L : String) (n e o : Nat) (ws : List Scc.IR.Operand) {j : Nat}
      {blk : List (Directive × Nat)},
      bodyIn cells fr L n o is ws = true →
      (_root_.Executable.labels exe).label L = (_root_.Executable.labels exe).label l + Int64.ofNat e →
      (j, blk) ∈ bodyBlks cells fr L n e o is ws →
      CdOf exe endPc ((_root_.Executable.labels exe).label l + Int64.ofNat j) blk := by
  intro is
  induction is with
  | nil =>
    intro L n e o ws j blk h hL hm
    match ws, h with
    | [w], h =>
      cases hg : getOp fr .rax w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg, Bool.and_eq_true] at h
        obtain ⟨⟨h1, hgap⟩, h2⟩ := h
        obtain ⟨hz1, hc1⟩ := blkAt_code hp hend h1
        obtain ⟨-, hc2⟩ := blkAt_code hp hend h2
        have hR := label_labelGapB hp hgap
        simp only [bodyBlks, hg, List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        generalize sizesAt cells L o (tearDirs lw).length = zs1 at hz1 hc1 hR
        generalize sizesAt cells (retL fr.fn n) 0 [i64 .ret].length = zs2 at hc2
        have hpc : (_root_.Executable.labels exe).label l + Int64.ofNat (e + o) =
            (_root_.Executable.labels exe).label L + Int64.ofNat o := by rw [hL, ofNat_add']
        rw [hR, ofNat_zero', ofNat_add', ← hpc] at hc2
        rw [← hpc] at hc1
        have := cd_ret hz1 hc1 hc2
        rwa [retZip_eq hz1] at this
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro L n e o ws j blk h hL hm
    cases i
    case addChk d a b =>
      cases ha : getOp fr .rax a <;> cases hb : getOp fr .rcx b <;> cases hd : rsOf fr d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.some la lb off =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨h1, hgap⟩, h2⟩, h3⟩ := h
        simp only [bodyBlks, ha, hb, hd] at hm
        obtain ⟨-, hc1⟩ := blkAt_code hp hend h1
        obtain ⟨-, hc2⟩ := blkAt_code hp hend h2
        have hR := label_labelGapB hp hgap
        have hpc : (_root_.Executable.labels exe).label l + Int64.ofNat (e + o) =
            (_root_.Executable.labels exe).label L + Int64.ofNat o := by rw [hL, ofNat_add']
        have hR' : (_root_.Executable.labels exe).label (retL fr.fn n) =
            (_root_.Executable.labels exe).label l +
              Int64.ofNat (e + o + (sizesAt cells L o (addDirs fr la lb).length).sum) := by
          rw [hR, ofNat_add', ← hpc, ← ofNat_add']
        rcases List.mem_cons.mp hm with hm | hm
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
          rwa [hpc]
        rcases List.mem_cons.mp hm with hm | hm
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
          rw [hR', ofNat_zero'] at hc2
          exact hc2
        · exact ih _ _ _ _ ws h3 hR' hm
    all_goals simp [bodyIn] at h

/-- **`bodyIn` gives the body's code at its blocks** (`InBody`). -/
theorem bodyCode_inBody {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {fr : Scc.Emit.X64.Frame}
    {l : String} {n : Nat} {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} (h : bodyIn cells fr l n 0 is ws = true) :
    BodyCode fr (CdIn exe endPc l (bodyBlks cells fr l n 0 0 is ws)) ((_root_.Executable.labels exe).label l) is ws := by
  have := bodyCode_in (S := bodyBlks cells fr l n 0 0 is ws) hp hend is l n 0 0 ws h (ofNat_zero' _).symm
    fun _ hx => hx
  rwa [ofNat_zero'] at this

end Code

end Spike.Lib.LowerX64
