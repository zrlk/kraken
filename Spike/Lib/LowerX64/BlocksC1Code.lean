/-
**The code predicate of an `Accepted1` body's blocks with calls**
(x86-64): the code of a block, instruction by instruction, at a code
predicate `Cd` on sized blocks and a call predicate `Bl` (a `callq` and the
return label after it); the twin of `Spike/Lib/LowerA64/BlocksC1Code.lean`.

- `CodeC`: the code of the instructions `is` at `pc`, the label counter at
  `k`, then the terminator's: each non-call instruction's code (`Emits`, at
  `Cd`), or a one-word user call's argument load (`Cd`), its `callq` and
  return label `.L<fn>.x<k>` (`Bl`) and its result's store (`Cd`), the
  counter `k + 1` after it; a checked `+`'s add (`addDirs`, `Cd`) and, after
  its fall-through's label `.L<fn>.x<k>`, its store (`Cd`), the counter
  `k + 1` after it; a `ret`'s code (`retDirs`) as one label-free `Cd` piece
  around its return site's label (P5);
- `BlC`: the `Bl` instance: the `callq` is code `j` cells after a label `L`
  (`blockAt`), the return label follows `L` after `j + 1` cells
  (`labelGap`), and the `callq` passes its phase check (`blkPh`), as
  `call_blockAt` gives;
- `BlocksCodeC`: every block not ending in `unreachable` (the bracket's dead
  abort block `deepBlock`) is at its label, at some label number.
- `At1Q`, `AtQ`, `CdCQ`, `CdC`: the `Cd` instance: a label-free piece of
  sized cells after a label of `Q` (`blockAt`), whole or in two pieces
  around a fresh label (`AtQ`), passing its phase check from its pc
  (`runPhB`); `CdC` at any labels; `.mono`, `.sub` (a sub-piece),
  `CdCQ.toCdC`; `cdCQ_at1`, `cdCQ_at`, `cdC_at`: a piece of a segment;
  `AtQ.cdOf`, `cdOf_cdC` put it in the code of a laid-out program;
- `codeC_of_seg`: a block's code after its label (`segIn`), as the emitter
  writes it from a state (`instsCode`, `emitTerm`), every run from there
  passing `runPhB`, gives `CodeC` at `CdC` and `BlC` (each call's return
  label, checked `+`'s fall-through label and `ret`'s return site label
  `.L<fn>.x<k>` starting a new run, at the address `labelGap` gives,
  `hgap`; `hgap_of_lays` on a laid-out program);
- `codeC_block`, `blocksCodeC`, `entryCodeC`: from a block's `blocksOk` and
  `blocksPh` (as `Blocks1.lean`'s `code1_block`), a block of `lowerC`'s
  shape (`BlockC`) without the stack abort's call (`abortI`; none without
  the depth counter, `lowerC_noStackAbort`; with it only in the `unreachable`
  block `deepBlock`, `ne_abortI_of_callBlk`);
- `fnCodeC`: a code block's function `func1 …`: its entry block at `CodeC`
  from its label counter and its later blocks at `BlocksCodeC`;
  `fnCodeC_ofPlaceOK`: for every code block of an `Accepted1` program
  passing `PlaceOK`, as `fnPh1_ofPlaceOK` numbers them, with its `lowerC`
  (`LowC`) and `maps`; `fnCodeC_of_fnPh1` at `fnPh1_ofPlaceOK`'s own
  witnesses (`hgap_ofPlaceOK`: `hgap` at its layout).

Where x86-64 differs from AArch64: the emitter is a state monad, so an
instruction's code is the items it emits from every state (`Emits`,
`Spike/Lib/LowerX64/BlocksC1.lean`) rather than an `Except` value; a block
is sized (`ds.zip zs`, the pc after it `pc + Int64.ofNat zs.sum`); the
return label is the label counter's `.L<fn>.x<k>` (`k` counts the calls
before it in the block, from the block's first number), not the
instruction index; a block's label is `labelOf fr.fn l` (it cannot fail).
-/
import Spike.Lib.LowerX64.BlocksC1
import Spike.Lib.LowerX64.Body1

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Emit.X64 (S E Item emitInst emitTerm labelOf i64 rel directives)
open Scc.Cert.Rt.X64 (blockAt labelGap after after_eq)
open Scc.Cert.Code1X64 (segIn segIn_iff segIn_label blockAt_of_segIn labelGap_of_segIn)
open Scc.Cert.Ph1X64 (runsAux runPhB blkPh_of_runPhB runs runPh blocksPh blocksPh_block blocksPh_blockPh segCells)
open Scc.Cert.Code1X64 (blockItems blocksOk blocksOk_block)
open Scc.Sem.X64 (codeLabel)
open Scc.Lower.Inv (Res1 func1 params1R)
open CoreTerm (Decl)
open Spike.Lib.X64 (cellOff)
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.LowerShape (isCall InstC TermC)

/-! ## The code predicate -/

/-- **The code of a block's instructions `is` at `pc`, its label counter
at `k`, then of its terminator `tm`**. A non-call instruction: the items
`l` it emits (`Emits`, its stack map irrelevant) at `pc` (`Cd`), at some
cell sizes `zs`. A one-word user call `call [d] g [w]`: `w`'s load `lw`
into `%rdi` at `pc` (`Cd`), the `callq g` of `zc` bytes after it with the
return label `.L<fn>.x<k>` (`Bl`), then `%rax`'s store into `d`'s slot
`off` (`Cd`), the counter `k + 1` after it. A checked `+` `addChk d a b`
(P5): the operands' loads and the checked add (`addDirs`) at `pc` (`Cd`),
then, after its fall-through's label `.L<fn>.x<k>`, the store into `d`'s
slot `off` (`Cd`), the counter `k + 1` after it. The terminator: an
`unreachable` (no claim), the items it emits at `pc` (`Emits`, `Cd`), or a
`ret [w]`'s load, epilogue and `ret` (`retDirs`, label-free, its return
site's label `.L<fn>.x<k>` between the epilogue and `ret`) at `pc` (`Cd`).
`Cd pc blk`: `blk` is the code at `pc`; `Bl pc zc g k`: `callq g` of `zc`
bytes is the code at `pc`, followed by the label `.L<fn>.x<k>`. -/
def CodeC (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) : Nat → Int64 → List Scc.IR.Inst → Scc.IR.Term → Prop
  | _, pc, [], tm => tm = .unreachable ∨
      (∃ l zs, Emits (emitTerm fr tm) l ∧ zs.length = (dirs l).length ∧ Cd pc ((dirs l).zip zs)) ∨
      (∃ w lw zs, tm = .ret [w] ∧ getOp fr .rax w = .ok lw ∧ zs.length = (retDirs lw).length ∧
        Cd pc ((retDirs lw).zip zs))
  | k, pc, i :: is, tm =>
    (isCall i = false ∧ ∃ l zs, Emits (emitInst fr none i) l ∧ zs.length = (dirs l).length ∧
      Cd pc ((dirs l).zip zs) ∧ CodeC fr Cd Bl k (pc + Int64.ofNat zs.sum) is tm) ∨
    (∃ d g w lw off zs zc z, i = .call [d] (Scc.Lower.Names.user g) [w] ∧ getOp fr .rdi w = .ok lw ∧
      rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧ Cd pc ((dirs lw).zip zs) ∧
      Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧
      CodeC fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) is tm) ∨
    (∃ d a b la lb off zs z, i = .addChk d a b ∧ getOp fr .rax a = .ok la ∧ getOp fr .rcx b = .ok lb ∧
      rsOf fr d = some off ∧ zs.length = (addDirs fr la lb).length ∧ Cd pc ((addDirs fr la lb).zip zs) ∧
      Cd (pc + Int64.ofNat zs.sum) [(stDir off, z)] ∧
      CodeC fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat z) is tm)

/-- **A call's `callq g` of `zc` bytes at `pc` with the return label
`.L<fn>.x<k>` after it**: `j` cells (`off` bytes) after a label `L`
(`blockAt`), with the return label after `L` at `j + 1` cells (`labelGap`),
passing the phase check at `pc` with no dead target and the return address
`ra`, the return label in the phase of `ra` (the callee's return address of
`ra`'s phase). -/
def BlC (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (fr : Scc.Emit.X64.Frame) (ra : Int64) (pc : Int64) (zc : Nat) (g : Label) (k : Nat) : Prop :=
  ∃ L j off, lab L + Int64.ofNat off = pc ∧ blockAt cells L j off [(i64 (.call (rel g)), zc)] = true ∧
    labelGap cells L s!".L{fr.fn}.x{k}" (j + 1) (off + zc) = true ∧
    blkPh okPc ph (fun _ => false) lab pc ra [(i64 (.call (rel g)), zc)] = true ∧
    ph (pc + Int64.ofNat zc).toBitVec.toNat = ph ra.toBitVec.toNat

/-- **The code of a function's blocks**: each block not ending in
`unreachable` (the bracket's dead abort block `deepBlock`) at its assembler
label (`lab`), as `CodeC` from some label number. -/
def BlocksCodeC (fr : Scc.Emit.X64.Frame) (Cd : Int64 → List (Directive × Nat) → Prop)
    (Bl : Int64 → Nat → Label → Nat → Prop) (lab : Label → Int64) (bs : List Scc.IR.Block) : Prop :=
  ∀ b ∈ bs, b.term ≠ .unreachable → ∃ k, CodeC fr Cd Bl k (lab (labelOf fr.fn b.label)) b.insts b.term

/-- A non-call instruction's code does not depend on its stack map. -/
theorem emitInst_sm {fr : Scc.Emit.X64.Frame} {i : Scc.IR.Inst} (hc : isCall i = false)
    (sm sm' : Option Scc.IR.StackMap.Entry) : emitInst fr sm i = emitInst fr sm' i := by
  cases i <;> first | rfl | simp [isCall] at hc

/-! ## The `Cd` instance -/

/-- **`blk` is placed at `pc` after a label of `Q`**: `j` cells (`off`
bytes) after a label `L` of `Q` (`blockAt`). -/
def At1Q (Q : Label → Prop) (cells : List (Directive × Nat)) (lab : Label → Int64) (pc : Int64)
    (blk : List (Directive × Nat)) : Prop :=
  ∃ L j off, Q L ∧ lab L + Int64.ofNat off = pc ∧ blockAt cells L j off blk = true

/-- **`blk` is placed at `pc` after labels of `Q`**, whole (`At1Q`) or in
two pieces, the second right after the first (a checked `+`'s code around
its fall-through's label, a `ret`'s around its return site's label, P5). -/
def AtQ (Q : Label → Prop) (cells : List (Directive × Nat)) (lab : Label → Int64) (pc : Int64)
    (blk : List (Directive × Nat)) : Prop :=
  At1Q Q cells lab pc blk ∨ ∃ b1 b2, blk = b1 ++ b2 ∧ At1Q Q cells lab pc b1 ∧
    At1Q Q cells lab (pc + Int64.ofNat (b1.map (·.2)).sum) b2

/-- **A piece of a block's code at `pc` after labels of `Q`**: label-free
cells, placed after labels of `Q` (`AtQ`), passing the phase check from
`pc` (`runPhB`) with the return address `ra`. -/
def CdCQ (Q : Label → Prop) (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat)
    (lab : Label → Int64) (ra : Int64) (pc : Int64) (blk : List (Directive × Nat)) : Prop :=
  blk.all (fun c => !c.1.isLabel) = true ∧ AtQ Q cells lab pc blk ∧ runPhB okPc ph lab pc ra blk = true

/-- **A piece of a block's code at `pc`**: `CdCQ` at any labels. -/
abbrev CdC (cells : List (Directive × Nat)) (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64)
    (ra : Int64) : Int64 → List (Directive × Nat) → Prop :=
  CdCQ (fun _ => True) cells okPc ph lab ra

/-- The stack abort's call (the deep block's). -/
abbrev abortI : Scc.IR.Inst :=
  .call [] Scc.Lower.Names.abort [Scc.Lower.imm Scc.IR.AbortKind.stack.code]

/-! ## Runs -/

/-- **`runPhB` of a sub-run**: in a run `xs ++ ys ++ zs` passing `runPhB`,
`ys` at its pc passes `runPhB`. -/
theorem runPhB_sub {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {xs ys zs : List (Directive × Nat)} (h : runPhB okPc ph lab pc ra (xs ++ ys ++ zs) = true) :
    runPhB okPc ph lab (pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) xs.length)) ra ys = true := by
  have hpc : ∀ k, k ≤ ys.length → pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) xs.length) + Int64.ofNat (cellOff ys k) =
      pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) (xs.length + k)) := by
    intro k hk; rw [Scc.Cert.Ph1X64.cellOff_mid hk, Int64.add_assoc, ← Int64.ofNat_add]
  unfold runPhB
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.mp hk
  have hlen : xs.length + k < (xs ++ ys ++ zs).length := by simp; omega
  obtain ⟨h1, h2, h3⟩ := Scc.Cert.Ph1X64.runPhB_get h hlen
  have hget : (xs ++ ys ++ zs)[xs.length + k] = ys[k] := by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact List.getElem_append_left hk'
  have h0 : ph (pc + Int64.ofNat (cellOff (xs ++ ys ++ zs) xs.length)).toBitVec.toNat = ph pc.toBitVec.toNat := by
    have hlen0 : xs.length + 0 < (xs ++ ys ++ zs).length := by simp; omega
    simpa using (Scc.Cert.Ph1X64.runPhB_get h hlen0).2.1
  rw [hget] at h3
  rw [List.getElem?_eq_getElem hk', hpc k (by omega)]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, h0]
  exact ⟨⟨h1, h2⟩, fun t ht => h3 t ht⟩

/-- **`runPhB` of two runs, one right after the other**, the second's pc
in the first's phase. -/
theorem runPhB_append {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra : Int64}
    {a b : List (Directive × Nat)} (ha : runPhB okPc ph lab pc ra a = true)
    (hb : runPhB okPc ph lab (pc + Int64.ofNat (a.map (·.2)).sum) ra b = true)
    (he : ph (pc + Int64.ofNat (a.map (·.2)).sum).toBitVec.toNat = ph pc.toBitVec.toNat) :
    runPhB okPc ph lab pc ra (a ++ b) = true := by
  unfold runPhB at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · have hoff : cellOff (a ++ b) k = cellOff a k := by
      unfold cellOff; rw [List.take_append_of_le_length (by omega)]
    rw [hoff, List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have hoff : cellOff (a ++ b) (a.length + j) = (a.map (·.2)).sum + cellOff b j := by
      unfold cellOff
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.map_append,
        List.sum_append]
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [hoff, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Int64.ofNat_add, ← Int64.add_assoc]
    exact this

/-- **A block inside a placed block is placed**, `pre.length` cells and
`pre`'s bytes further. -/
theorem blockAt_sub {cells : List (Directive × Nat)} {l : Label} {k off : Nat}
    {pre blk post : List (Directive × Nat)} (h : blockAt cells l k off (pre ++ blk ++ post) = true) :
    blockAt cells l (k + pre.length) (off + (pre.map (·.2)).sum) blk = true := by
  unfold blockAt at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hl, hoff⟩, hb⟩ := h
  generalize Scc.Cert.Rt.X64.run cells l = r at hoff hb ⊢
  have hlen : (pre ++ blk ++ post).length ≤ (r.drop k).length := by
    have := congrArg List.length hb
    simp only [List.length_take] at this
    omega
  have hd : r.drop k = pre ++ blk ++ post ++ (r.drop k).drop (pre ++ blk ++ post).length := by
    have := List.take_append_drop (pre ++ blk ++ post).length (r.drop k)
    rw [hb] at this
    exact this.symm
  refine ⟨⟨hl, ?_⟩, ?_⟩
  · rw [List.take_add, List.map_append, List.sum_append, hoff, hd]
    simp
  · rw [← List.drop_drop, hd]
    simp

section Q

variable {Q : Label → Prop} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64}

theorem At1Q.mono {Q' : Label → Prop} (hQ : ∀ L, Q L → Q' L) {pc : Int64} {blk : List (Directive × Nat)}
    (h : At1Q Q cells lab pc blk) : At1Q Q' cells lab pc blk :=
  let ⟨L, j, off, hL, he, hb⟩ := h
  ⟨L, j, off, hQ L hL, he, hb⟩

theorem AtQ.mono {Q' : Label → Prop} (hQ : ∀ L, Q L → Q' L) {pc : Int64} {blk : List (Directive × Nat)}
    (h : AtQ Q cells lab pc blk) : AtQ Q' cells lab pc blk := by
  rcases h with h | ⟨b1, b2, e, h1, h2⟩
  · exact .inl (h.mono hQ)
  · exact .inr ⟨b1, b2, e, h1.mono hQ, h2.mono hQ⟩

theorem CdCQ.mono {Q' : Label → Prop} (hQ : ∀ L, Q L → Q' L) {pc : Int64} {blk : List (Directive × Nat)}
    (h : CdCQ Q cells okPc ph lab ra pc blk) : CdCQ Q' cells okPc ph lab ra pc blk :=
  ⟨h.1, h.2.1.mono hQ, h.2.2⟩

/-- **`CdCQ` forgets its labels' predicate.** -/
theorem CdCQ.toCdC {pc : Int64} {blk : List (Directive × Nat)}
    (h : CdCQ Q cells okPc ph lab ra pc blk) : CdC cells okPc ph lab ra pc blk :=
  h.mono fun _ _ => trivial

/-- **A block inside a placed block is placed** (`blockAt_sub`). -/
theorem At1Q.sub {pc0 pc : Int64} {pre blk post : List (Directive × Nat)}
    (h : At1Q Q cells lab pc0 (pre ++ blk ++ post)) (hpc : pc = pc0 + Int64.ofNat (pre.map (·.2)).sum) :
    At1Q Q cells lab pc blk := by
  obtain ⟨L, j, off, hL, he, hb⟩ := h
  refine ⟨L, j + pre.length, off + (pre.map (·.2)).sum, hL, ?_, blockAt_sub hb⟩
  rw [hpc, ← he, Int64.ofNat_add, Int64.add_assoc]

/-- **A block inside a block placed in pieces is placed in pieces**: inside
one piece, or across the two. -/
theorem AtQ.sub {pc0 pc : Int64} {pre blk post : List (Directive × Nat)}
    (h : AtQ Q cells lab pc0 (pre ++ blk ++ post)) (hpc : pc = pc0 + Int64.ofNat (pre.map (·.2)).sum) :
    AtQ Q cells lab pc blk := by
  subst hpc
  rcases h with h | ⟨b1, b2, e, h1, h2⟩
  · exact .inl (h.sub rfl)
  · rcases List.append_eq_append_iff.mp e with ⟨a1, rfl, rfl⟩ | ⟨c1, e2, rfl⟩
    · exact .inl (h1.sub rfl)
    · rcases List.append_eq_append_iff.mp e2 with ⟨a1, rfl, rfl⟩ | ⟨c2, rfl, rfl⟩
      · refine .inr ⟨a1, c1, rfl, At1Q.sub (pre := pre) (post := []) (by rwa [List.append_nil]) rfl, ?_⟩
        refine At1Q.sub (pre := []) (post := post) (by rwa [List.nil_append]) ?_
        simp [List.sum_append, Int64.ofNat_add, Int64.add_assoc, show Int64.ofNat 0 = 0 from rfl]
      · refine .inl (h2.sub (pre := c2) (post := post) ?_)
        simp [List.sum_append, Int64.ofNat_add, Int64.add_assoc]

/-- **A block inside a piece at `CdCQ` is at `CdCQ`** (`AtQ.sub`,
`runPhB_sub`). -/
theorem CdCQ.sub {pc0 pc : Int64} {pre blk post : List (Directive × Nat)}
    (h : CdCQ Q cells okPc ph lab ra pc0 (pre ++ blk ++ post))
    (hpc : pc = pc0 + Int64.ofNat (pre.map (·.2)).sum) : CdCQ Q cells okPc ph lab ra pc blk := by
  obtain ⟨hl, hat, hr⟩ := h
  refine ⟨?_, hat.sub hpc, ?_⟩
  · simp only [List.all_append, Bool.and_eq_true] at hl
    exact hl.1.2
  · have := runPhB_sub hr
    have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
      simp [cellOff]
    rwa [hc, ← hpc] at this

end Q

section Code

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64}

/-- **A piece `c` of a run, after one label of `Q`**: after the label-free
`xs` in the segment after `l` of `Q` (the cells `t`), the runs from there
passing `runPhB`; at the sizes of its cells, label-free, after `l`
(`At1Q`), passing `runPhB`, the pc past it at `xs ++ c`'s offset, and its
pc in the phase of `l`'s if it is not empty. -/
theorem cdCQ_at1 {Q : Label → Prop} {l : Label} (hQ : Q l) {t : List (Directive × Nat)}
    (ht : after l cells = some t) {xs c zs : List Directive}
    (hseg : segIn cells l (xs ++ c ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true)
    (hc : c.all (fun d => !d.isLabel) = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (c ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    ∃ zc, zc.length = c.length ∧ (c.zip zc).all (fun c => !c.1.isLabel) = true ∧
      At1Q Q cells lab (lab l + Int64.ofNat (cellOff t xs.length)) (c.zip zc) ∧
      runPhB okPc ph lab (lab l + Int64.ofNat (cellOff t xs.length)) ra (c.zip zc) = true ∧
      lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zc.sum =
        lab l + Int64.ofNat (cellOff t (xs ++ c).length) ∧
      (c ≠ [] → ph (lab l + Int64.ofNat (cellOff t xs.length)).toBitVec.toNat = ph (lab l).toBitVec.toNat) := by
  have hY := seg_slice ht hseg
  have hYe := zip_fst_snd ((t.drop xs.length).take c.length)
  rw [hY] at hYe
  have hlenT : (xs ++ c ++ zs).length ≤ t.length := by
    have := congrArg List.length (seg_take ht hseg)
    simp only [List.length_map, List.length_take] at this
    omega
  have hlenY : ((t.drop xs.length).take c.length).length = c.length := by
    simpa using congrArg List.length hY
  have hS := slice_noLabel hY hc
  have hph' := hph
  rw [List.length_append, List.take_add, runsAux_shift _ _ _ _ hS] at hph'
  obtain ⟨P, hP⟩ := runsAux_run0 l (((t.drop xs.length).take c.length).reverse ++ (t.take xs.length).reverse)
    (((t.drop xs.length).drop c.length).take zs.length)
  have hr := hph' _ hP
  simp only [List.reverse_append, List.reverse_reverse] at hr
  have hr' : runPhB okPc ph lab (lab l) ra (t.take xs.length ++ (t.drop xs.length).take c.length ++ P) = true := by
    simpa only [List.append_assoc] using hr
  have e : cellOff (t.take xs.length ++ (t.drop xs.length).take c.length ++ P) (t.take xs.length).length =
      cellOff t xs.length := by
    unfold cellOff
    rw [List.append_assoc, List.take_left' rfl]
  refine ⟨((t.drop xs.length).take c.length).map (·.2), by simp; simp at hlenT; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hYe]
    exact List.all_eq_true.mpr fun d hd => by simp [hS d hd]
  · rw [hYe]
    refine ⟨l, xs.length, cellOff t xs.length, hQ, rfl, ?_⟩
    obtain ⟨t', ht', -, hb⟩ := blockAt_of_segIn hseg hx hc
    rw [ht] at ht'
    cases ht'
    exact hb
  · rw [hYe]
    have := runPhB_sub hr'
    rwa [e] at this
  · rw [List.length_append, pc_step]
  · intro hne
    have hne' : 0 < ((t.drop xs.length).take c.length).length := by
      rw [hlenY]
      exact Nat.pos_of_ne_zero fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
    have hlen : (t.take xs.length).length < (t.take xs.length ++ (t.drop xs.length).take c.length ++ P).length := by
      simp only [List.length_append] at hne' ⊢
      omega
    have := (Scc.Cert.Ph1X64.runPhB_get hr' hlen).2.1
    rwa [e] at this

/-- **A piece `c` of a run is at `CdCQ Q`** (`cdCQ_at1`): after the
label-free `xs` in the segment after `l` of `Q` (the cells `t`), the runs
from there passing `runPhB`; at the sizes of its cells, the pc past it at
`xs ++ c`'s offset. -/
theorem cdCQ_at {Q : Label → Prop} {l : Label} (hQ : Q l) {t : List (Directive × Nat)}
    (ht : after l cells = some t) {xs c zs : List Directive}
    (hseg : segIn cells l (xs ++ c ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true)
    (hc : c.all (fun d => !d.isLabel) = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (c ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    ∃ zc, zc.length = c.length ∧
      CdCQ Q cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) (c.zip zc) ∧
      lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zc.sum =
        lab l + Int64.ofNat (cellOff t (xs ++ c).length) := by
  obtain ⟨zc, hz, ha, hat, hr, hpc, -⟩ := cdCQ_at1 hQ ht hseg hx hc hph
  exact ⟨zc, hz, ⟨ha, .inl hat, hr⟩, hpc⟩

/-- **A piece `c` of a run is at `CdC`** (`cdCQ_at` at any labels). -/
theorem cdC_at {l : Label} {t : List (Directive × Nat)} (ht : after l cells = some t) {xs c zs : List Directive}
    (hseg : segIn cells l (xs ++ c ++ zs) = true) (hx : xs.all (fun d => !d.isLabel) = true)
    (hc : c.all (fun d => !d.isLabel) = true)
    (hph : ∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (c ++ zs).length),
      runPhB okPc ph lab (lab r.1) ra r.2 = true) :
    ∃ zc, zc.length = c.length ∧ CdC cells okPc ph lab ra (lab l + Int64.ofNat (cellOff t xs.length)) (c.zip zc) ∧
      lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zc.sum =
        lab l + Int64.ofNat (cellOff t (xs ++ c).length) :=
  cdCQ_at trivial ht hseg hx hc hph

/-- **A block's code after its label gives `CodeC`**: the code `code` its
instructions `is` (`InstC` but the stack abort's call, a stack map each,
`ms`) and terminator `tm` (`TermC`) emit from a state `s` (the label counter
`s.next`), after the label-free `xs` and before `zs` in the segment after
`l` (`segIn`; the cells `t`), every run from there passing `runPhB` at `lab`
(`hph`); the stack maps on (`hm`), and `lab` following the labels' gaps
(`hgap`). Each call's return label starts a new run. -/
theorem codeC_of_seg (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    {frames : Option Nat} {tm : Scc.IR.Term} (htm : TermC frames tm) :
    ∀ (is : List Scc.IR.Inst) (ms : List (Option Scc.IR.StackMap.Entry)) (s s' : S) (code : List Item)
      (l : Label) (t : List (Directive × Nat)) (xs zs : List Directive),
      (∀ i ∈ is, InstC i ∧ i ≠ abortI) → is.length ≤ ms.length →
      (do instsCode fr is ms; emitTerm fr tm) s = .ok ((), s') → s'.out = code.reverse ++ s.out →
      after l cells = some t → segIn cells l (xs ++ directives code ++ zs) = true →
      xs.all (fun d => !d.isLabel) = true →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true) →
      (∀ r ∈ runsAux l (t.take xs.length).reverse ((t.drop xs.length).take (directives code ++ zs).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) →
      CodeC fr (CdC cells okPc ph lab ra) (BlC cells okPc ph lab fr ra) s.next
        (lab l + Int64.ofNat (cellOff t xs.length)) is tm
  | [], ms, s, s', code, l, t, xs, zs, _, _, h, hD, ht, hseg, hx, hph, hrl => by
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_nil] at hI
    cases hI
    by_cases hu : tm = .unreachable
    · exact Or.inl hu
    by_cases hr : ∀ ws, tm ≠ .ret ws
    · obtain ⟨ct, et, act⟩ := emitTerm_allIns htm hr hT
      rw [et] at hT
      cases hT
      have hc : code = ct := by
        have h1 : code.reverse ++ s.out = ct.reverse ++ s.out := hD.symm
        have h2 := List.append_cancel_right h1
        rw [← List.reverse_reverse code, h2, List.reverse_reverse]
      subst hc
      obtain ⟨zc, hz, hcd, -⟩ := cdC_at ht hseg hx act hph
      exact Or.inr (Or.inl ⟨code, zc, et, hz, hcd⟩)
    -- `ret [w]`: its return site's label between the epilogue and `ret` (P5)
    obtain ⟨w, rfl⟩ : ∃ w, tm = .ret [w] := by
      cases htm with
      | ret w _ => exact ⟨w, rfl⟩
      | unreachable => exact absurd rfl hu
      | _ => exact absurd (fun _ h => by cases h) hr
    obtain ⟨lw, hlw⟩ : ∃ lw, getOp fr .rax w = .ok lw := by
      rcases ld_cases fr w .rax s with ⟨lw, hlw, -⟩ | ⟨e, he⟩
      · exact ⟨lw, hlw⟩
      · rw [Scc.Lower.InvX64.emitTerm_ret1, bind_err he] at hT; cases hT
    rw [emitTerm_ret hlw] at hT
    cases hT
    have hc : code = lw ++ retItems fr.fn s.next := by
      have h1 : code.reverse ++ s.out = (lw ++ retItems fr.fn s.next).reverse ++ s.out := hD.symm
      have h2 := List.append_cancel_right h1
      rw [← List.reverse_reverse code, h2, List.reverse_reverse]
    subst hc
    have eT : dirs (lw ++ tearItems) = tearDirs lw := rfl
    rw [directives_eq_dirs, dirs_retItems, eT] at hseg hph hrl
    have hRe : retDirs lw = tearDirs lw ++ [i64 .ret] := by rw [retDirs, dirs_epiItems_split, ← tearDirs]
    have hTl : (tearDirs lw).all (fun d => !d.isLabel) = true := by
      have : AllIns (lw ++ tearItems) := by
        unfold tearItems; allIns_tac
      exact this
    have hTne : tearDirs lw ≠ [] := by
      obtain ⟨dl, hdl⟩ := dirs_getOp hlw
      rw [tearDirs, dirs_append, hdl]; simp
    -- the load and teardown
    have hseg1 : segIn cells l (xs ++ tearDirs lw ++ .label (retL fr.fn s.next) :: ([i64 .ret] ++ zs)) = true := by
      simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hseg
    have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
        ((t.drop xs.length).take (tearDirs lw ++ .label (retL fr.fn s.next) :: ([i64 .ret] ++ zs)).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true := by
      simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hph
    have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
        ((t.drop xs.length).take (tearDirs lw ++ .label (retL fr.fn s.next) :: ([i64 .ret] ++ zs)).length),
        ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
      simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hrl
    obtain ⟨z1, hz1, ha1, hat1, hr1, hpc1, hp1⟩ := cdCQ_at1 (Q := fun _ => True) trivial ht hseg1 hx hTl hph1
    have hxT : (xs ++ tearDirs lw).all (fun d => !d.isLabel) = true := by rw [List.all_append, hx, hTl]; rfl
    obtain ⟨ht2, hseg2, hsp⟩ := label_at hgap ht (by simpa only [List.append_assoc] using hseg1) hxT
    obtain ⟨-, hafter⟩ := runs_label ht hseg1 hTl hph1
    obtain ⟨-, hrafter⟩ := runs_label ht hseg1 hTl hrl1
    generalize t.drop ((xs ++ tearDirs lw).length + 1) = t2 at ht2 hafter hrafter
    -- `ret`, after the return site's label
    have hph2 : ∀ r ∈ runsAux (retL fr.fn s.next) (t2.take ([] : List Directive).length).reverse
        ((t2.drop ([] : List Directive).length).take ([i64 .ret] ++ zs).length),
        runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa using hafter
    obtain ⟨z2, hz2, ha2, hat2, hr2, -, -⟩ := cdCQ_at1 (Q := fun _ => True) (xs := []) trivial ht2
      (by simpa using hseg2) rfl rfl hph2
    simp only [List.length_nil, Spike.Lib.X64.cellOff_zero, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]
      at hat2 hr2
    have hphR : ph (lab (retL fr.fn s.next)).toBitVec.toNat = ph ra.toBitVec.toNat := by
      obtain ⟨y, hy⟩ := runsAux_head (retL fr.fn s.next) [] _
      exact hrafter _ hy
    have hphl : ph (lab l).toBitVec.toNat = ph ra.toBitVec.toNat := by
      obtain ⟨y, hy⟩ := runsAux_head l _ _
      exact hrl _ hy
    have hsp' : lab (retL fr.fn s.next) = lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat z1.sum := by
      rw [hpc1, hsp]
    have hs1 : (((tearDirs lw).zip z1).map (·.2)).sum = z1.sum := by
      rw [List.map_snd_zip (by omega)]
    refine Or.inr (Or.inr ⟨w, lw, z1 ++ z2, rfl, hlw, by rw [hRe]; simp [hz1, hz2], ?_⟩)
    rw [hRe, List.zip_append hz1.symm]
    refine ⟨by rw [List.all_append, ha1, ha2]; rfl, .inr ⟨_, _, rfl, hat1, by rw [hs1, ← hsp']; exact hat2⟩, ?_⟩
    exact runPhB_append hr1 (by rw [hs1, ← hsp']; exact hr2) (by rw [hs1, ← hsp', hphR, hp1 hTne, hphl])
  | i :: is, ms, s, s', code, l, t, xs, zs, hs, hms, h, hD, ht, hseg, hx, hph, hrl => by
    obtain ⟨m, ms, rfl⟩ : ∃ m ms', ms = m :: ms' := by
      cases ms with
      | nil => simp at hms
      | cons m ms' => exact ⟨m, ms', rfl⟩
    have hs' := List.forall_mem_cons.mp hs
    have hms' : is.length ≤ ms.length := by simp at hms; omega
    obtain ⟨u, s1, hI, hT⟩ := bind_inv h
    rw [instsCode_cons] at hI
    obtain ⟨u2, s2, hE, hI⟩ := bind_inv hI
    have hrest : (do instsCode fr is ms; emitTerm fr tm) s2 = .ok ((), s') := by
      rw [bind_ok hI]; exact hT
    obtain ⟨c', hc'⟩ := (Pre.bind' (instsCode_pre fr is ms) fun _ => emitTerm_pre fr tm).out _ _ _ hrest
    have hD' : s'.out = c'.reverse.reverse ++ s2.out := by rw [List.reverse_reverse]; exact hc'
    by_cases hac : ∃ d a b, i = .addChk d a b
    · -- a checked `+`: its fall-through's label before the store (P5)
      obtain ⟨d, a, b, rfl⟩ := hac
      obtain ⟨la, lb, off, hla, hlb, hd, rfl⟩ := emitInst_add_cases fr m d a b s hE
      have hcode : code = (la ++ lb ++ addChecked (ovfL fr) ++
          [Item.d (.label (retL fr.fn s.next)), Item.d (stDir off)]) ++ c'.reverse := by
        have h1 : code.reverse ++ s.out = (c' ++ (la ++ lb ++ addChecked (ovfL fr) ++
            [Item.d (.label (retL fr.fn s.next)), Item.d (stDir off)]).reverse) ++ s.out := by
          rw [← hD, hc']; simp
        have h2 := List.append_cancel_right h1
        rw [← List.reverse_reverse code, h2]; simp
      subst hcode
      generalize hDd : directives c'.reverse = D at hseg hph hrl
      have hdd : directives ((la ++ lb ++ addChecked (ovfL fr) ++
          [Item.d (.label (retL fr.fn s.next)), Item.d (stDir off)]) ++ c'.reverse) =
          addDirs fr la lb ++ .label (retL fr.fn s.next) :: stDir off :: D := by
        rw [← hDd]
        simp only [directives_eq_dirs, dirs_append, addDirs, List.append_assoc]
        rfl
      rw [hdd] at hseg hph hrl
      have hAl : (addDirs fr la lb).all (fun d => !d.isLabel) = true := by
        have : AllIns (la ++ lb ++ addChecked (ovfL fr)) := by
          unfold addChecked; allIns_tac
        exact this
      have hSl : (stDir off).isLabel = false := rfl
      -- the checked add
      have hseg1 : segIn cells l (xs ++ addDirs fr la lb ++ .label (retL fr.fn s.next) :: ([stDir off] ++ (D ++ zs))) =
          true := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (addDirs fr la lb ++ .label (retL fr.fn s.next) :: ([stDir off] ++ (D ++ zs))).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (addDirs fr la lb ++ .label (retL fr.fn s.next) :: ([stDir off] ++ (D ++ zs))).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
        simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hrl
      obtain ⟨zl, hzl, hcdl, hpcl⟩ := cdC_at ht hseg1 hx hAl hph1
      have hxA : (xs ++ addDirs fr la lb).all (fun d => !d.isLabel) = true := by rw [List.all_append, hx, hAl]; rfl
      obtain ⟨ht2, hseg2, hsp⟩ := label_at hgap ht (by simpa only [List.append_assoc] using hseg1) hxA
      obtain ⟨-, hafter⟩ := runs_label ht hseg1 hAl hph1
      obtain ⟨-, hrafter⟩ := runs_label ht hseg1 hAl hrl1
      generalize t.drop ((xs ++ addDirs fr la lb).length + 1) = t2 at ht2 hafter hrafter
      -- the store, after the fall-through's label
      have hsegS : segIn cells (retL fr.fn s.next) ([] ++ [stDir off] ++ (D ++ zs)) = true := by simpa using hseg2
      have hphS : ∀ r ∈ runsAux (retL fr.fn s.next) (t2.take ([] : List Directive).length).reverse
          ((t2.drop ([] : List Directive).length).take ([stDir off] ++ (D ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by simpa using hafter
      have hrlS : ∀ r ∈ runsAux (retL fr.fn s.next) (t2.take ([] : List Directive).length).reverse
          ((t2.drop ([] : List Directive).length).take ([stDir off] ++ (D ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by simpa using hrafter
      obtain ⟨zst, hzst, hcds, hpcs⟩ := cdC_at ht2 hsegS rfl (by simp [hSl]) hphS
      obtain ⟨z, rfl⟩ := length_one hzst
      -- the rest of the block, the label counter at `k + 1`
      have hSS := slice_noLabel (seg_slice ht2 hsegS) (by simp [hSl])
      rw [show ([stDir off] ++ (D ++ zs)).length = [stDir off].length + (D ++ zs).length from
        List.length_append, runs_step hSS] at hphS hrlS
      have := codeC_of_seg hm hgap htm is ms _ s' c'.reverse _ _ [stDir off] zs hs'.2 hms' hrest hD' ht2
        (by rw [hDd]; simpa using hsegS) (by simp [hSl]) (by rw [hDd]; simpa using hphS)
        (by rw [hDd]; simpa using hrlS)
      simp only [List.length_nil, List.nil_append, List.length_singleton, Spike.Lib.X64.cellOff_zero] at hpcs hcds this
      have hsp' : lab (retL fr.fn s.next) = lab l + Int64.ofNat (cellOff t xs.length) + Int64.ofNat zl.sum := by
        rw [hpcl, hsp]
      refine Or.inr (Or.inr ⟨d, a, b, la, lb, off, zl, z, rfl, hla, hlb, hd, hzl, hcdl, ?_, ?_⟩)
      · rw [← hsp']; simpa using hcds
      · rw [← hsp']; rw [← hpcs] at this; simpa using this
    by_cases hc : isCall i = false
    · -- an instruction other than a call or a checked `+`: label-free items
      obtain ⟨ci, ei, ai⟩ := emitInst_allIns hs'.1.1 hc (fun d a b h => hac ⟨d, a, b, h⟩) hE
      rw [ei] at hE
      cases hE
      have hcode : code = ci ++ c'.reverse := by
        have h1 : code.reverse ++ s.out = (c' ++ ci.reverse) ++ s.out := by
          rw [← hD, hc', List.append_assoc]
        have h2 := List.append_cancel_right h1
        rw [← List.reverse_reverse code, h2]; simp
      subst hcode
      have hdd : directives (ci ++ c'.reverse) = directives ci ++ directives c'.reverse := dirs_append _ _
      rw [hdd] at hseg hph
      have hseg1 : segIn cells l (xs ++ directives ci ++ (directives c'.reverse ++ zs)) = true := by
        simpa only [List.append_assoc] using hseg
      have hph1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (directives ci ++ (directives c'.reverse ++ zs)).length),
          runPhB okPc ph lab (lab r.1) ra r.2 = true := by
        simpa only [List.append_assoc] using hph
      have hrl1 : ∀ r ∈ runsAux l (t.take xs.length).reverse
          ((t.drop xs.length).take (directives ci ++ (directives c'.reverse ++ zs)).length),
          ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
        rw [hdd] at hrl
        simpa only [List.append_assoc] using hrl
      obtain ⟨zc, hz, hcd, hpc⟩ := cdC_at ht hseg1 hx ai hph1
      have hS := slice_noLabel (seg_slice ht hseg1) ai
      rw [List.length_append, runs_step hS] at hph1 hrl1
      have := codeC_of_seg hm hgap htm is ms _ s' c'.reverse l t (xs ++ directives ci) zs hs'.2 hms' hrest hD' ht
        (by simpa only [List.append_assoc] using hseg1) (by rw [List.all_append, hx, ai]; rfl)
        (by rw [List.length_append]; exact hph1) (by rw [List.length_append]; exact hrl1)
      refine Or.inl ⟨hc, ci, zc, by rw [emitInst_sm hc none m]; exact ei, hz, hcd, ?_⟩
      rw [hpc]
      exact this
    · obtain ⟨hIc, hnA⟩ := hs'.1
      cases hIc with
      | call d g w _ =>
        obtain ⟨lw, off, mp, hw, hd, aw, rfl⟩ := emitInst_call1_inv hm hE
        generalize hK : s!".L{fr.fn}.x{s.next}" = spK at hc' hD'
        generalize hC : i64 (.call (rel (Scc.Lower.Names.user g))) = C at hc' hD'
        have hcode : code = (lw ++ [Item.d C, Item.d (.label spK)] ++ [Item.d (stDir off)]) ++ c'.reverse := by
          have h1 : code.reverse ++ s.out =
              (c' ++ (lw ++ [Item.d C, Item.d (.label spK)] ++ [Item.d (stDir off)]).reverse) ++ s.out := by
            rw [← hD, hc']; simp
          have h2 := List.append_cancel_right h1
          rw [← List.reverse_reverse code, h2]; simp
        subst hcode
        generalize hDd : directives c'.reverse = D at hseg hph hrl
        have hdd : directives ((lw ++ [Item.d C, Item.d (.label spK)] ++ [Item.d (stDir off)]) ++ c'.reverse) =
            directives lw ++ C :: .label spK :: stDir off :: D := by
          rw [← hDd]
          simp only [directives_eq_dirs, dirs_append, List.append_assoc]
          rfl
        rw [hdd] at hseg hph hrl
        have hCl : C.isLabel = false := by rw [← hC]; exact isLabel_callq _
        have hSl : (stDir off).isLabel = false := rfl
        -- the argument's load
        have hsegA : segIn cells l (xs ++ directives lw ++ (C :: .label spK :: stDir off :: D ++ zs)) = true := by
          simpa only [List.append_assoc, List.cons_append] using hseg
        have hphA : ∀ r ∈ runsAux l (t.take xs.length).reverse
            ((t.drop xs.length).take (directives lw ++ (C :: .label spK :: stDir off :: D ++ zs)).length),
            runPhB okPc ph lab (lab r.1) ra r.2 = true := by
          simpa only [List.append_assoc, List.cons_append] using hph
        have hrlA : ∀ r ∈ runsAux l (t.take xs.length).reverse
            ((t.drop xs.length).take (directives lw ++ (C :: .label spK :: stDir off :: D ++ zs)).length),
            ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
          simpa only [List.append_assoc, List.cons_append] using hrl
        obtain ⟨zl, hzl, hcdl, hpcl⟩ := cdC_at ht hsegA hx aw hphA
        have hSA := slice_noLabel (seg_slice ht hsegA) aw
        rw [List.length_append, runs_step hSA, ← List.length_append] at hphA hrlA
        have hx1 : (xs ++ directives lw).all (fun d => !d.isLabel) = true := by
          rw [List.all_append, hx, aw]; rfl
        -- the `callq`
        have hsegB : segIn cells l ((xs ++ directives lw) ++ [C] ++ (.label spK :: stDir off :: D ++ zs)) = true := by
          simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hsegA
        obtain ⟨t', ht', hY1, hb⟩ := blockAt_of_segIn hsegB hx1 (by simp [hCl])
        rw [ht] at ht'
        cases ht'
        obtain ⟨⟨C', zc⟩, hS1⟩ : ∃ p, (t.drop (xs ++ directives lw).length).take 1 = [p] :=
          List.length_eq_one_iff.mp (by simpa using congrArg List.length hY1)
        rw [List.length_singleton, hS1] at hY1 hb
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hY1
        subst hY1
        have hx2 : ((xs ++ directives lw) ++ [C']).all (fun d => !d.isLabel) = true := by
          rw [List.all_append, hx1]; simp [hCl]
        have hsegL : segIn cells l (((xs ++ directives lw) ++ [C']) ++ .label spK :: (stDir off :: D ++ zs)) = true := by
          simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using hsegA
        obtain ⟨t'', ht'', hg⟩ := labelGap_of_segIn hsegL hx2
        rw [ht] at ht''
        cases ht''
        have hoff : cellOff t ((xs ++ directives lw) ++ [C']).length = cellOff t (xs ++ directives lw).length + zc := by
          rw [List.length_append, List.length_singleton, cellOff_add, hS1]; simp
        rw [hoff, List.length_append, List.length_singleton] at hg
        -- the runs: the one through the `callq`, then those after the return label
        have hph2 := hphA
        have hrl2 := hrlA
        rw [show (C' :: .label spK :: stDir off :: D ++ zs).length = 1 + (.label spK :: stDir off :: D ++ zs).length by
          simp; omega, runs_step (by rw [hS1]; simp [hCl])] at hph2 hrl2
        have hYL := seg_slice ht (xs := (xs ++ directives lw) ++ [C']) (ys := [.label spK])
          (zs := stDir off :: D ++ zs) (by simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
            using hsegA)
        obtain ⟨⟨dl, z0⟩, hL1⟩ : ∃ p, (t.drop ((xs ++ directives lw) ++ [C']).length).take 1 = [p] :=
          List.length_eq_one_iff.mp (by simpa using congrArg List.length hYL)
        rw [List.length_singleton, hL1] at hYL
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hYL
        subst hYL
        rw [List.length_append, List.length_singleton] at hL1
        have htk : t.take ((xs ++ directives lw).length + 1) = t.take (xs ++ directives lw).length ++ [(C', zc)] := by
          rw [List.take_add, hS1]
        have hsplit : (t.drop ((xs ++ directives lw).length + 1)).take (1 + (stDir off :: D ++ zs).length) =
            (t.drop ((xs ++ directives lw).length + 1)).take 1 ++
              (t.drop ((xs ++ directives lw).length + 1 + 1)).take (stDir off :: D ++ zs).length := by
          rw [List.take_add, List.drop_drop]
        rw [show (Directive.label spK :: stDir off :: D ++ zs).length = 1 + (stDir off :: D ++ zs).length by
          simp; omega, hsplit, hL1, htk] at hph2 hrl2
        simp only [List.singleton_append, runsAux, List.mem_cons, forall_eq_or_imp] at hph2 hrl2
        obtain ⟨hfirst, hafter⟩ := hph2
        obtain ⟨-, hrafter⟩ := hrl2
        simp only [List.reverse_reverse] at hfirst
        have hblk := blkPh_of_runPhB (xs := t.take (xs ++ directives lw).length) (ys := [(C', zc)]) (zs := [])
          (by simpa using hfirst) (by rw [← hC]; simp [classify_callq])
        have e1 : cellOff (t.take (xs ++ directives lw).length ++ [(C', zc)] ++ []) (t.take (xs ++ directives lw).length).length =
            cellOff t (xs ++ directives lw).length := by
          unfold cellOff
          rw [List.append_assoc, List.take_left' rfl]
        rw [e1] at hblk
        -- the return label's address
        have hsp : lab spK = lab l + Int64.ofNat (cellOff t (xs ++ directives lw).length) + Int64.ofNat zc := by
          rw [hgap _ _ _ _ hg, Int64.ofNat_add, Int64.add_assoc]
        -- the result's store
        have ht2 := after_label hsegL ht
        rw [List.length_append, List.length_singleton] at ht2
        have hsegS : segIn cells spK ([] ++ [stDir off] ++ (D ++ zs)) = true := by
          simpa using segIn_label hsegL
        have hphS : ∀ r ∈ runsAux spK ((t.drop ((xs ++ directives lw).length + 1 + 1)).take ([] : List Directive).length).reverse
            (((t.drop ((xs ++ directives lw).length + 1 + 1)).drop ([] : List Directive).length).take
              ([stDir off] ++ (D ++ zs)).length), runPhB okPc ph lab (lab r.1) ra r.2 = true := by
          simpa [Nat.add_assoc] using hafter
        have hrlS : ∀ r ∈ runsAux spK ((t.drop ((xs ++ directives lw).length + 1 + 1)).take
            ([] : List Directive).length).reverse
            (((t.drop ((xs ++ directives lw).length + 1 + 1)).drop ([] : List Directive).length).take
              ([stDir off] ++ (D ++ zs)).length), ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat := by
          simpa [Nat.add_assoc] using hrafter
        -- the return label in the phase of `ra`
        have hspk : ph (lab spK).toBitVec.toNat = ph ra.toBitVec.toNat := by
          obtain ⟨y, hy⟩ := runsAux_head spK _ _
          exact hrlS _ hy
        obtain ⟨zst, hzst, hcds, hpcs⟩ := cdC_at ht2 hsegS rfl (by simp [hSl]) hphS
        obtain ⟨z, rfl⟩ := length_one hzst
        -- the rest of the block, after the return label
        have hSS := slice_noLabel (seg_slice ht2 hsegS) (by simp [hSl])
        rw [show ([stDir off] ++ (D ++ zs)).length = [stDir off].length + (D ++ zs).length from
          List.length_append, runs_step hSS] at hphS hrlS
        subst hK hC
        have := codeC_of_seg hm hgap htm is ms _ s' c'.reverse _ _ [stDir off] zs hs'.2 hms' hrest hD' ht2
          (by rw [hDd]; simpa using hsegS) (by simp [hSl]) (by rw [hDd]; simpa using hphS)
          (by rw [hDd]; simpa using hrlS)
        simp only [List.length_nil, List.nil_append, List.length_singleton, Spike.Lib.X64.cellOff_zero] at hpcs hcds this
        rw [← hpcl] at hblk
        refine Or.inr (Or.inl ⟨d, g, w, lw, off, zl, zc, z, rfl, hw, hd, hzl, hcdl,
          ⟨l, (xs ++ directives lw).length, cellOff t (xs ++ directives lw).length, hpcl.symm, hb, hg, hblk,
            by rw [hpcl, ← hsp]; exact hspk⟩,
          ?_, ?_⟩)
        · rw [hpcl, ← hsp]; simpa using hcds
        · rw [hpcl, ← hsp]; rw [← hpcs] at this; simpa using this
      | abort => exact absurd rfl hnA
      | _ => exact absurd rfl hc

end Code

/-! ## From the placement checks -/

/-- An instruction other than a call is not the stack abort's call. -/
theorem ne_abortI_of_isCall {i : Scc.IR.Inst} (h : isCall i = false) : i ≠ abortI := by
  rintro rfl
  simp [isCall] at h

/-- **A block of `lowerC`'s shape not ending in `unreachable` has no stack
abort's call**: only the bracket's abort block `deepBlock` has one. -/
theorem ne_abortI_of_callBlk {lcx : Scc.Lower.Ctx} {b : Scc.IR.Block} (hb : Spike.Lib.LowerCall.CallBlk lcx b)
    (ht : b.term ≠ .unreachable) : ∀ i ∈ b.insts, i ≠ abortI := by
  cases hb with
  | deep n => exact absurd rfl ht
  | plain b hn => exact fun i hi => ne_abortI_of_isCall (hn i hi)
  | call n g w rest t _ _ hn =>
    intro i hi
    simp only [List.mem_append] at hi
    rcases hi with hi | hi
    · rintro rfl
      simp [Scc.Lower.Inv.callPost] at hi
    · exact ne_abortI_of_isCall (hn i hi)

section Place

variable {fr : Scc.Emit.X64.Frame} {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
  {lab : Label → Int64} {ra : Int64} {lo : Nat}

/-- **A placed block's code gives `CodeC`** at its label, its label counter
from `n`: its code after the label (`segIn`) and its runs' phase facts at the
code labels (`labC`), every label read resolving, which `lab` agrees with
(`hlab`); the block of `lowerC`'s shape (`BlockC`) without the stack abort's
call, every instruction with a stack map (`hms`). -/
theorem codeC_block (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {frames : Option Nat} {b : Scc.IR.Block} (hs : Spike.Lib.LowerShape.BlockC frames b)
    (hna : ∀ i ∈ b.insts, i ≠ abortI) {ms : List (Option Scc.IR.StackMap.Entry)}
    (hms : b.insts.length ≤ ms.length) {n n' : Nat} {code : List Item}
    (hc : blockItems fr n b ms = .ok (code, n'))
    (hseg : segIn cells (labelOf fr.fn b.label) (directives code) = true)
    (hph : ∀ r ∈ runs (labelOf fr.fn b.label) (segCells cells (labelOf fr.fn b.label) (directives code).length),
      runPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) ra r = true ∧
        ph (labC lo cells r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC fr (CdC cells okPc ph lab ra) (BlC cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  unfold blockItems at hc
  split at hc
  · next s heq =>
    cases hc
    obtain ⟨i, hi, -, -⟩ := segIn_iff.mp hseg
    obtain ⟨t, ht⟩ : ∃ t, after (labelOf fr.fn b.label) cells = some t := ⟨_, by rw [after_eq, hi]; rfl⟩
    have hsc : ∀ m, segCells cells (labelOf fr.fn b.label) m = t.take m := by
      intro m; unfold segCells; rw [ht]
    have := codeC_of_seg (okPc := okPc) (ph := ph) (ra := ra) (lab := lab) hm hgap hs.2 b.insts ms
      { next := n } s s.out.reverse (labelOf fr.fn b.label) t [] [] (fun i hi => ⟨hs.1 i hi, hna i hi⟩) hms
      (by rw [← blockCode_eq]; exact heq) (by simp) ht (by simpa using hseg) rfl
      (fun r hr => by
        have h' := (hph r (by rw [hsc]; simpa [runs] using hr)).1
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨hres, hlabs⟩, hrun⟩ := h'
        rw [labC_eq hlab hres, runPhB_congr fun L hL => labC_eq hlab (List.all_eq_true.mp hlabs L hL)] at hrun
        exact hrun)
      (fun r hr => by
        have h' := hph r (by rw [hsc]; simpa [runs] using hr)
        simp only [runPh, Bool.and_eq_true] at h'
        obtain ⟨⟨⟨hres, -⟩, -⟩, hp⟩ := h'
        rw [labC_eq hlab hres] at hp
        exact hp)
    simpa [Spike.Lib.X64.cellOff_zero] using this
  · cases hc

/-- **The later blocks' code** (`BlocksCodeC`) at `CdC` and `BlC`, from the
function's `blocksOk` and `blocksPh` (the blocks `bs` after `pre`, each with
its stack maps `G b`, one per instruction). -/
theorem blocksCodeC (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {frames : Option Nat} {n : Nat} {pre bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((pre ++ bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((pre ++ bs).map fun b => (b, G b)) = true)
    (hs : ∀ b ∈ bs, Spike.Lib.LowerShape.BlockC frames b)
    (hna : ∀ b ∈ bs, b.term ≠ .unreachable → ∀ i ∈ b.insts, i ≠ abortI) :
    BlocksCodeC fr (CdC cells okPc ph lab ra) (BlC cells okPc ph lab fr ra) lab bs := by
  intro b hb hu
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
  have e : (pre ++ (s ++ b :: t)).map (fun b => (b, G b)) =
      (pre ++ s).map (fun b => (b, G b)) ++ (b, G b) :: t.map (fun b => (b, G b)) := by simp
  rw [e] at hok hph
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh hph
  rw [hc] at hc'; cases hc'
  exact ⟨_, codeC_block hm hgap hlab (hs b hb) (hna b hb hu) (Nat.le_of_eq (hG b).symm) hc hseg hr⟩

/-- **The entry block's code** (`CodeC` at the entry's label, its label
counter from `n`) from the function's `blocksOk` and `blocksPh`. -/
theorem entryCodeC (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {G : Scc.IR.Block → List (Option Scc.IR.StackMap.Entry)} (hG : ∀ b, (G b).length = b.insts.length)
    {frames : Option Nat} {n : Nat} {b : Scc.IR.Block} {bs : List Scc.IR.Block}
    (hok : blocksOk cells fr n ((b :: bs).map fun b => (b, G b)) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((b :: bs).map fun b => (b, G b)) = true)
    (hs : Spike.Lib.LowerShape.BlockC frames b) (hna : ∀ i ∈ b.insts, i ≠ abortI) :
    CodeC fr (CdC cells okPc ph lab ra) (BlC cells okPc ph lab fr ra) n (lab (labelOf fr.fn b.label))
      b.insts b.term := by
  obtain ⟨code, n', hc, hseg⟩ := blocksOk_block (pre := []) hok
  obtain ⟨code', n'', hc', hr⟩ := blocksPh_blockPh (pre := []) hph
  rw [hc] at hc'; cases hc'
  exact codeC_block hm hgap hlab hs hna (Nat.le_of_eq (hG b).symm) hc hseg hr

/-- **A code block's function's code** (`bodyC_segS`'s two code premises):
the function `f = func1 name (params1R d) r` of the closed form `r` of an
`Accepted1` code block `d` (`lowerC` without the depth counter), its entry block
at `CodeC` from its label counter `n` and its later blocks at `BlocksCodeC`,
from its `blocksOk` and `blocksPh` with its stack maps (`callMaps`). -/
theorem fnCodeC (hm : fr.maps = true)
    (hgap : ∀ a b n off, labelGap cells a b n off = true → lab b = lab a + Int64.ofNat off)
    (hlab : ∀ l a, codeLabel lo cells l = some a → lab l = Int64.ofNat a)
    {lcx : Scc.Lower.Ctx} (hf : lcx.frames = none) {earlier : List String} {d : Decl}
    (hd : Scc.Lower.decl1 earlier d = true) {r : Res1}
    (hr : Scc.Lower.Inv.lowerC lcx (Scc.Lower.Inv.env1 d) 0 "entry" 0 d.body = some r) {name : Scc.IR.Sym}
    {n : Nat}
    (hok : blocksOk cells fr n ((func1 name (params1R d) r).blocks.zip
      (Scc.IR.StackMap.callMaps (func1 name (params1R d) r))) = true)
    (hph : blocksPh okPc ph (labC lo cells) (fun l => (codeLabel lo cells l).isSome) cells fr ra n
      ((func1 name (params1R d) r).blocks.zip (Scc.IR.StackMap.callMaps (func1 name (params1R d) r))) = true) :
    CodeC fr (CdC cells okPc ph lab ra) (BlC cells okPc ph lab fr ra) n (lab (labelOf fr.fn "entry"))
        r.insts r.term ∧
      BlocksCodeC fr (CdC cells okPc ph lab ra) (BlC cells okPc ph lab fr ra) lab r.blocks := by
  obtain ⟨G, hz, hG⟩ := zip_callMaps (func1 name (params1R d) r)
  rw [hz] at hok hph
  have hsh := Spike.Lib.LowerShape.func1_shape lcx hd hr name
  have hna := Spike.Lib.LowerCall.lowerC_noStackAbort lcx hf d.body _ _ _ _ r hr
  refine ⟨entryCodeC (b := ⟨"entry", r.insts, r.term⟩) (bs := r.blocks) hm hgap hlab hG hok hph
    (hsh _ (List.mem_cons_self ..)) hna.1, ?_⟩
  exact blocksCodeC (pre := [⟨"entry", r.insts, r.term⟩]) hm hgap hlab hG hok hph
    (fun b hb => hsh b (List.mem_cons_of_mem _ hb))
    fun b hb _ => hna.2 b hb

end Place

/-! ## On a laid-out program -/

section Lays

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **A piece placed after labels (`AtQ`) is in the code** of a laid-out
program, at its labels: each piece (`codeAt_blockAt_lays`), the two
concatenated (`CodeAt.append`). -/
theorem AtQ.cdOf (hp : Scc.Cert.Rt.X64.Lays exe cells kp) {endPc : Int64}
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe cells kp) {Q : Label → Prop} {pc : Int64}
    {blk : List (Directive × Nat)} (h : AtQ Q cells (_root_.Executable.labels exe).label pc blk) :
    CdOf exe endPc pc blk := by
  have h1 : ∀ pc blk, At1Q Q cells (_root_.Executable.labels exe).label pc blk → CdOf exe endPc pc blk := by
    rintro _ _ ⟨L, j, off, -, hpc, hb⟩ s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hp hs (hn.trans hend) hb
    rwa [hpc] at this
  rcases h with h | ⟨b1, b2, rfl, ha1, ha2⟩
  · exact h1 _ _ h
  · exact fun s hs hn => Spike.Lib.X64.CodeAt.append (h1 _ _ ha1 s hs hn) (h1 _ _ ha2 s hs hn)

/-- **A piece at `CdC` is in the code** of a laid-out program, at its
labels. -/
theorem cdOf_cdC (hp : Scc.Cert.Rt.X64.Lays exe cells kp) {endPc : Int64}
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe cells kp) {okPc : Nat → Bool} {ph : Nat → Nat} {ra : Int64} :
    ∀ pc blk, CdC cells okPc ph (_root_.Executable.labels exe).label ra pc blk → CdOf exe endPc pc blk :=
  fun _ _ h => h.2.1.cdOf hp hend

/-- **A call at `BlC` is in the code** of a laid-out program, at its
labels (the bracket's `hBl`). -/
theorem cdOf_blC (hp : Scc.Cert.Rt.X64.Lays exe cells kp) {endPc : Int64}
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe cells kp) {okPc : Nat → Bool} {ph : Nat → Nat}
    {fr : Scc.Emit.X64.Frame} {ra : Int64} :
    ∀ pc zc g k, BlC cells okPc ph (_root_.Executable.labels exe).label fr ra pc zc g k →
      CdOf exe endPc pc [(i64 (.call (rel g)), zc)] := by
  rintro _ _ _ _ ⟨L, j, off, hpc, hb, -, -, -⟩ s hs hn
  have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hp hs (hn.trans hend) hb
  rwa [hpc] at this

end Lays

/-- **A call's return address at `BlC` is in the phase of `ra`**. -/
theorem blC_ph {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}
    {fr : Scc.Emit.X64.Frame} {ra pc : Int64} {zc : Nat} {g : Label} {k : Nat}
    (h : BlC cells okPc ph lab fr ra pc zc g k) :
    ph (pc + Int64.ofNat zc).toBitVec.toNat = ph ra.toBitVec.toNat :=
  h.choose_spec.choose_spec.choose_spec.2.2.2.2

/-- **A code block's function's code from `PlaceOK`, at `fnPh1_ofPlaceOK`'s
witnesses**: for the closed forms `rs` and runtime functions `rt`, the `j`th
declaration's function `f` with its frame `frOf ir f`, its label counter `n`,
blocks and phase facts as `fnPh1_ofPlaceOK` gives them, at the layout
`RuntimeLayout.ofPlaceOK h i`, the frame records stack maps (`maps`), its
entry block is at `CodeC` from `n` and its later blocks are at
`BlocksCodeC`. -/
theorem fnCodeC_of_fnPh1 {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted1 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) {rs : List Res1} {rt : List Scc.IR.Func}
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir =
      Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d)
    (hL : Spike.Lib.LowerNode.LowC p cfg.layout.obj none d r) {n : Nat}
    (hbo : blocksOk (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)) n
      ((func1 (Scc.Lower.Names.user d.name) (params1R d) r).blocks.zip
        (Scc.IR.StackMap.callMaps (func1 (Scc.Lower.Names.user d.name) (params1R d) r))) = true)
    {ra : Int64}
    (hbp : blocksPh (Spike.Lib.X64.PhRec.okPc (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.PhRec.ph (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i))
      (labC Λ.code.lo (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog)
      (fun l => (codeLabel Λ.code.lo
        (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog l).isSome)
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)) ra n
      ((func1 (Scc.Lower.Names.user d.name) (params1R d) r).blocks.zip
        (Scc.IR.StackMap.callMaps (func1 (Scc.Lower.Names.user d.name) (params1R d) r))) = true) :
    let o := Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let Ly := Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i
    let fr := frOf (Scc.Lower.X64.lowerAll cfg p).low.ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)
    fr.maps = true ∧
      CodeC fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) n
          (Ly.lab (labelOf fr.fn "entry")) r.insts r.term ∧
        BlocksCodeC fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra)
          (BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra) Ly.lab r.blocks := by
  intro o Ly fr
  have hm : fr.maps = true := by
    show (Scc.Lower.X64.lowerAll cfg p).low.ir.growth.isSome = true
    rw [hir]; rfl
  obtain ⟨earlier, hd1⟩ := Spike.Lib.LowerNode.decl1_of_decls1 p [] (Spike.Lib.LowerNode.decls1_of_accepted1 hp)
    d (List.mem_of_getElem? hd)
  exact ⟨hm, fnCodeC hm (hgap_ofPlaceOK h i) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i) rfl hd1 hL hbo hbp⟩

/-- **Each code block's function's code from `PlaceOK`** on an `Accepted1`
program, at the layout `RuntimeLayout.ofPlaceOK h i` (any immediates `i`),
as `fnPh1_ofPlaceOK` numbers them: the `j`th declaration `d` with its closed
form `r` (`lowerC` without the depth counter) is the function `f = func1
(user d.name) (params1R d) r`, whose frame `frOf ir f` records stack maps
(`maps`), whose entry block is at `CodeC` from some label counter `n` and
whose later blocks are at `BlocksCodeC`, at every return address of the
phase of `raL`. With `fnPh1_ofPlaceOK`'s other facts, use
`fnCodeC_of_fnPh1` at its witnesses. -/
theorem fnCodeC_ofPlaceOK {cfg : Scc.Config} {p : CoreTerm.Prog} (hp : Scc.Lower.Accepted1 p = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.X64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    let o := Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    let Ly := Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h i
    ∃ (rs : List Res1) (rt : List Scc.IR.Func),
      Spike.Lib.LowerNode.Pairwise2 (Spike.Lib.LowerNode.LowC p cfg.layout.obj none) p rs ∧
      ir = Scc.Lower.Inv.progOf cfg.layout rt (Spike.Lib.LowerNode.funcs1 p rs) ∧
      ∀ (j : Nat) (d : Decl) (r : Res1), p[j]? = some d → rs[j]? = some r →
        let f := func1 (Scc.Lower.Names.user d.name) (params1R d) r
        let fr := frOf ir f
        Spike.Lib.LowerNode.LowC p cfg.layout.obj none d r ∧ fr.maps = true ∧
        ∃ n : Nat, ∀ ra' : Int64,
          Spike.Lib.X64.PhRec.ph Ly ra'.toBitVec.toNat = Spike.Lib.X64.PhRec.ph Ly (Ly.lab raL).toBitVec.toNat →
          CodeC fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') n
              (Ly.lab (labelOf fr.fn "entry")) r.insts r.term ∧
            BlocksCodeC fr (CdC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab ra')
              (BlC o.prog (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) Ly.lab fr ra') Ly.lab
              r.blocks := by
  intro o ir Ly
  obtain ⟨rs, rt, hrs, hir, -, H⟩ := fnPh1_ofPlaceOK hp hlow h i
  refine ⟨rs, rt, hrs, hir, fun j d r hd hr => ?_⟩
  obtain ⟨hL, -, n, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbo, hbp, -⟩ := H j d r hd hr
  have H' := fun ra' hra => fnCodeC_of_fnPh1 hp h i hir hd hL hbo (hbp ra' hra)
  exact ⟨hL, (H' (Ly.lab raL) rfl).1, n, fun ra' hra => (H' ra' hra).2⟩

end Spike.Lib.LowerX64
