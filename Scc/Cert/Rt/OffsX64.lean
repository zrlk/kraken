import Scc.Cert.Rt.CodeX64
import Spike.Lib.X64Block

/-!
# The static offsets of the block table (x64)

The x64 twin of `Scc/Cert/Rt/OffsA64.lean`. The block table (`Grp`,
`scc --blocks`) names each block by its place and its cells; a block's proof
(`Spike.Lib.X64`, `block_spec`) also needs its **static offsets**: the
region `[lo, hi)` of its accesses and the offsets `o` of `%rsp` and the
stack-address registers at its entry, under which the block is covered
(`okBlk lo hi o blk`). The analyser of `Scc/Cert/Blocks.lean` computes them
by a fixpoint over each function.

An **offset row** (`OBlk`) is a block of the table with its offsets; the
rows are grouped by label as the table is (`OGrp`, `OGrp.toGrp` forgets the
offsets). `offsetsOk` checks, in one pass over the rows:

* every row is covered at its offsets (`okBlk`): `okBlk_of_offsetsOk`;
* along the fall-through edge from a row to the next one of its group (the
  next block starting where the row's ends, the row not ending in `jmp`,
  `ret` or `call`), the next row's offsets are implied by those the row
  leaves (`soAfter`, the offsets `arun` reaches: `arun_so`): `SO.Le`,
  `soLe_of_offsetsOk`. The offsets the analyser records may know fewer
  registers than the block leaves, never others; `SORel.of_le` weakens the
  relation accordingly.

Branch, call, return and label-entry edges are not checked here.

Where x64 differs from AArch64: a row's place is its cell count and byte
offset from its label (as `Grp`'s); a block ending in `call` has no
fall-through edge here: the run continues at the callee (`AI.tgt`) with
`%rsp` 8 lower (`AI.so`), and the analyser's offsets after the call are
those after the callee's return (`%rsp` as before the call), a return edge.
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Spike.Lib Spike.Lib.X64

/-! ## Rows -/

/-- **An offset row**: a block of the table (`k` cells and `off` bytes
after its group's label, the cells `blk`) with its access region `[lo, hi)`
and its entry offsets `o`. -/
structure OBlk where
  k : Nat
  off : Nat
  lo : Int
  hi : Int
  o : SO
  blk : List (Directive × Nat)

/-- **The rows after a label**, and the cells of its run in no row (`ev`,
their indices in the run, ascending): single instructions between blocks,
e.g. the stack switches `mov %rax, %rsp` of the runtime, that the proofs
take one at a time. A3's coverage (`coverOk`, `Scc/Cert/Rt/CoverX64.lean`)
checks that the rows and these instructions tile the run. -/
structure OGrp where
  l : Label
  bs : List OBlk
  ev : List Nat

/-- The block table of a group of rows. -/
def OGrp.toGrp (g : OGrp) : Grp := ⟨g.l, g.bs.map fun b => (b.k, b.off, b.blk)⟩

/-- The block table of the rows. -/
def toGrps (gs : List OGrp) : List Grp := gs.map OGrp.toGrp

theorem mem_toGrps {gs : List OGrp} {g : OGrp} (hg : g ∈ gs) {b : OBlk} (hb : b ∈ g.bs) :
    g.toGrp ∈ toGrps gs ∧ (b.k, b.off, b.blk) ∈ g.toGrp.bs :=
  ⟨List.mem_map_of_mem hg, List.mem_map_of_mem (f := fun b : OBlk => (b.k, b.off, b.blk)) hb⟩

/-- One group's rows from its blocks and a list of offsets (region and entry
offsets per block, in order; missing ones are `(0, 0, ⟨0, []⟩)`), and the
offsets left. -/
def ofBs : List (Nat × Nat × List (Directive × Nat)) → List (Int × Int × SO) →
    List OBlk × List (Int × Int × SO)
  | [], os => ([], os)
  | (k, off, b) :: bs, os =>
    let (lo, hi, o) := os.headD (0, 0, ⟨0, []⟩)
    let r := ofBs bs os.tail
    (⟨k, off, lo, hi, o, b⟩ :: r.1, r.2)

/-- **The rows of a block table** with its blocks' offsets, in table order
(`scc --blocks`' order); no group has single instructions (`withEvs` adds
them). -/
def ofGrps : List Grp → List (Int × Int × SO) → List OGrp
  | [], _ => []
  | g :: gs, os => let r := ofBs g.bs os; ⟨g.l, r.1, []⟩ :: ofGrps gs r.2

/-- The groups with their single instructions, one list per group in order
(missing ones are `[]`). -/
def withEvs : List OGrp → List (List Nat) → List OGrp
  | [], _ => []
  | g :: gs, es => { g with ev := es.headD [] } :: withEvs gs es.tail

/-- The single instructions do not change the block table. -/
theorem toGrps_withEvs : ∀ (gs : List OGrp) (es : List (List Nat)), toGrps (withEvs gs es) = toGrps gs
  | [], _ => rfl
  | g :: gs, es => by
    have ih := toGrps_withEvs gs es.tail
    simp only [toGrps] at ih
    simp only [withEvs, toGrps, List.map_cons, OGrp.toGrp, ih]

private theorem ofBs_map : ∀ (bs : List (Nat × Nat × List (Directive × Nat))) (os : List (Int × Int × SO)),
    (ofBs bs os).1.map (fun b => (b.k, b.off, b.blk)) = bs
  | [], _ => rfl
  | (k, off, b) :: bs, os => by simp [ofBs, ofBs_map bs]

/-- The rows of a table are the table, whatever the offsets. -/
theorem toGrps_ofGrps : ∀ (gs : List Grp) (os : List (Int × Int × SO)), toGrps (ofGrps gs os) = gs
  | [], _ => rfl
  | g :: gs, os => by
    simp only [ofGrps, toGrps, List.map_cons, OGrp.toGrp, ofBs_map] at *
    rw [show List.map OGrp.toGrp (ofGrps gs (ofBs g.bs os).2) = gs from toGrps_ofGrps gs _]

/-! ## Offsets after a block -/

/-- **The offsets after a block** from `o`: each covered cell's (`AI.so`);
the others leave them. -/
def soAfter (o : SO) : List (Directive × Nat) → SO
  | [] => o
  | (d, _) :: ds =>
    match classify d with
    | some a => soAfter (a.so o) ds
    | none => soAfter o ds

/-- The abstract run of a block reaches the offsets `soAfter` computes. -/
theorem arun_so (lab : String → Int64) : ∀ (blk : List (Directive × Nat)) (am : AM),
    (arun lab blk am).so = soAfter am.so blk
  | [], _ => rfl
  | (d, z) :: ds, am => by
    show (arun lab ds (dstep lab am (d, z))).so = _
    rw [arun_so lab ds]
    rcases h : classify d with _ | a <;> simp [soAfter, dstep, h]

/-- **`a` implies `b`'s offsets are no stronger**: the same `%rsp`, and
every register `a` knows has the same offset in `b`. -/
def SO.Le (a b : SO) : Prop := a.sp = b.sp ∧ ∀ r k, a.get r = some k → b.get r = some k

/-- `SO.Le`, decided: the same `%rsp`, and each entry of `a`'s list `b`'s
offset of its register. -/
def soLe (a b : SO) : Bool := a.sp == b.sp && a.regs.all fun e => lk b.regs e.1 == some e.2

private theorem lk_of_all {a b : List (Reg64 × Int)} (h : a.all (fun e => lk b e.1 == some e.2) = true) :
    ∀ r k, lk a r = some k → lk b r = some k := by
  induction a with
  | nil => intro r k h'; simp [lk] at h'
  | cons e a ih =>
    obtain ⟨x, j⟩ := e
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    intro r k h'
    unfold lk at h'
    split at h'
    · rename_i hr; cases h'; subst hr; exact h.1
    · exact ih h.2 r k h'

theorem SO.le_of_soLe {a b : SO} (h : soLe a b = true) : SO.Le a b := by
  simp only [soLe, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun r k hk => ?_⟩
  by_cases hr : r = .rsp
  · subst hr; simp only [Spike.Lib.X64.SO.get, ↓reduceIte] at hk ⊢; rw [← h.1]; exact hk
  · simp only [Spike.Lib.X64.SO.get, hr, ↓reduceIte] at hk ⊢; exact lk_of_all h.2 r k hk

/-- The registers at their offsets `b` are at the weaker offsets `a`. -/
theorem SORel.of_le {R : Region} {a b : SO} {regs : Reg64s} (h : SO.Le a b) (hr : SORel R b regs) :
    SORel R a regs :=
  fun r k hk => hr r k (h.2 r k hk)

/-! ## The check -/

/-- A block falls through to the cell after it: its last cell is not
`jmp`, `ret` or `call`. -/
def fallsThrough (blk : List (Directive × Nat)) : Bool :=
  match blk.getLast? with
  | some (d, _) =>
    match classify d with
    | some (.jmp _) | some .ret | some (.call _) => false
    | _ => true
  | none => true

/-- A row covered at its offsets. -/
def OBlk.ok (b : OBlk) : Bool := okBlk b.lo b.hi b.o b.blk

/-- The fall-through edge from `b` to `b'`, if there is one (`b'` starts
where `b` ends, and `b` falls through): `b'`'s offsets implied by those `b`
leaves. -/
def fallOk (b b' : OBlk) : Bool :=
  !(Nat.beq b'.k (b.k + b.blk.length) && fallsThrough b.blk) || soLe b'.o (soAfter b.o b.blk)

/-- A group's rows: each covered, each fall-through edge between
consecutive rows. -/
def rowsOk : List OBlk → Bool
  | [] => true
  | [b] => b.ok
  | b :: b' :: bs => b.ok && fallOk b b' && rowsOk (b' :: bs)

/-- **A5 on x86-64**: every row of the table covered at its offsets, and
the offsets agree along the fall-through edges. -/
def offsetsOk (gs : List OGrp) : Bool := gs.all fun g => rowsOk g.bs

/-! ## Extraction -/

private theorem ok_of_rowsOk : ∀ {bs : List OBlk}, rowsOk bs = true → ∀ b ∈ bs, b.ok = true
  | [], _, _, hb => by cases hb
  | [b], h, b', hb => by
    simp only [List.mem_singleton] at hb; subst hb; exact h
  | b :: b' :: bs, h, b'', hb => by
    simp only [rowsOk, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1.1
    · exact ok_of_rowsOk h.2 _ hb

private theorem fall_of_rowsOk : ∀ {bs : List OBlk}, rowsOk bs = true →
    ∀ {b b' : OBlk}, [b, b'] <:+: bs → fallOk b b' = true
  | [], _, _, _, hi => by simp at hi
  | [_], _, _, _, hi => by
    have := hi.length_le; simp at this
  | c :: c' :: bs, h, b, b', hi => by
    simp only [rowsOk, Bool.and_eq_true] at h
    rcases List.infix_cons_iff.mp hi with hp | hi
    · simp only [List.cons_prefix_cons] at hp
      obtain ⟨rfl, rfl, -⟩ := hp
      exact h.1.2
    · exact fall_of_rowsOk h.2 hi

/-- **A row of a checked table is covered at its offsets.** -/
theorem okBlk_of_offsetsOk {gs : List OGrp} (h : offsetsOk gs = true) {g : OGrp} (hg : g ∈ gs) {b : OBlk}
    (hb : b ∈ g.bs) : okBlk b.lo b.hi b.o b.blk = true :=
  ok_of_rowsOk (List.all_eq_true.mp h g hg) b hb

/-- **The offsets of a checked table agree along a fall-through edge**:
consecutive rows `b`, `b'` of a group, `b'` starting where `b` ends and `b`
falling through. -/
theorem soLe_of_offsetsOk {gs : List OGrp} (h : offsetsOk gs = true) {g : OGrp} (hg : g ∈ gs) {b b' : OBlk}
    (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length) (hf : fallsThrough b.blk = true) :
    SO.Le b'.o (soAfter b.o b.blk) := by
  have := fall_of_rowsOk (List.all_eq_true.mp h g hg) hi
  have hb : Nat.beq (b.k + b.blk.length) (b.k + b.blk.length) = true := Nat.beq_refl _
  simp only [fallOk, hk, hb, hf, Bool.and_self, Bool.not_true, Bool.false_or] at this
  exact SO.le_of_soLe this

/-- The fall-through edge's offsets for the abstract run of `b` from its
offsets: the registers at the offsets the run leaves are at `b'`'s. -/
theorem sorel_next_of_offsetsOk {gs : List OGrp} (h : offsetsOk gs = true) {g : OGrp} (hg : g ∈ gs)
    {b b' : OBlk} (hi : [b, b'] <:+: g.bs) (hk : b'.k = b.k + b.blk.length) (hf : fallsThrough b.blk = true)
    {R : Region} (lab : String → Int64) (pc : Int64) (σ : AS)
    (hr : SORel R (arun lab b.blk ⟨pc, b.o, σ⟩).so (arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs) :
    SORel R b'.o (arun lab b.blk ⟨pc, b.o, σ⟩).σ.regs := by
  rw [arun_so] at hr
  exact SORel.of_le (soLe_of_offsetsOk h hg hi hk hf) hr

/-! ## A row by its label

A proof names a block of the table by its label and its row (`rowIn`): a
lookup, not a check of the block, so a row of a checked table is covered
(`okBlk_of_rowIn`) without deciding `okBlk` again. -/

/-- Two rows are the same: place, region, offsets and cells. -/
def OBlk.eqb (a b : OBlk) : Bool :=
  decide (a.k = b.k) && decide (a.off = b.off) && decide (a.lo = b.lo) && decide (a.hi = b.hi) &&
    decide (a.o.sp = b.o.sp) && decide (a.o.regs = b.o.regs) && decide (a.blk = b.blk)

theorem OBlk.eq_of_eqb {a b : OBlk} (h : a.eqb b = true) : a = b := by
  obtain ⟨k, off, lo, hi, ⟨sp, regs⟩, blk⟩ := a
  obtain ⟨k', off', lo', hi', ⟨sp', regs'⟩, blk'⟩ := b
  simp only [OBlk.eqb, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- **The row `b` is in the group of label `l`.** -/
def rowIn (gs : List OGrp) (l : Label) (b : OBlk) : Bool :=
  gs.any fun g => decide (g.l = l) && g.bs.any (·.eqb b)

theorem mem_of_rowIn {gs : List OGrp} {l : Label} {b : OBlk} (h : rowIn gs l b = true) :
    ∃ g ∈ gs, g.l = l ∧ b ∈ g.bs := by
  simp only [rowIn, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨g, hg, hl, b', hb', he⟩ := h
  exact ⟨g, hg, hl, OBlk.eq_of_eqb he ▸ hb'⟩

/-- **A row of a checked table, named by its label, is covered.** -/
theorem okBlk_of_rowIn {gs : List OGrp} (h : offsetsOk gs = true) {l : Label} {b : OBlk}
    (hr : rowIn gs l b = true) : okBlk b.lo b.hi b.o b.blk = true :=
  let ⟨_, hg, _, hb⟩ := mem_of_rowIn hr
  okBlk_of_offsetsOk h hg hb

/-! ## A wider region -/

private theorem offOk_mono {lo hi lo' hi' : Int} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') {k : Int}
    (h : offOk lo hi k = true) : offOk lo' hi' k = true := by
  simp only [offOk, decide_eq_true_eq] at h ⊢; omega

private theorem aiOk_mono {lo hi lo' hi' : Int} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') {o : SO} :
    ∀ {a : AI}, a.ok lo hi o = true → a.ok lo' hi' o = true
  | .ld r b n, h => by
    simp only [AI.ok, Bool.and_eq_true] at h ⊢
    refine ⟨?_, h.2⟩
    have h1 := h.1
    cases hg : o.get b <;> simp only [hg] at h1 ⊢
    · exact h1
    · exact offOk_mono hlo hhi h1
  | .st b n r, h => by
    simp only [AI.ok] at h ⊢
    cases hg : o.get b <;> simp only [hg] at h ⊢
    · exact h
    · exact offOk_mono hlo hhi h
  | .push _, h => offOk_mono hlo hhi h
  | .pop r, h => by
    simp only [AI.ok, Bool.and_eq_true] at h ⊢
    exact ⟨offOk_mono hlo hhi h.1, h.2⟩
  | .reg _ _, h => h
  | .jmp _, h => h
  | .jcc _ _, h => h
  | .call _, h => offOk_mono hlo hhi h
  | .ret, h => offOk_mono hlo hhi h

/-- A block covered in `[lo, hi)` is covered in any region containing it. -/
theorem okBlk_mono {lo hi lo' hi' : Int} (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    ∀ {o : SO} {blk : List (Directive × Nat)}, okBlk lo hi o blk = true → okBlk lo' hi' o blk = true
  | _, [], _ => rfl
  | o, (d, _) :: ds, h => by
    unfold okBlk at h ⊢
    split at h
    · rename_i a _
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨⟨aiOk_mono hlo hhi h.1.1, h.1.2⟩, okBlk_mono hlo hhi h.2⟩
    · cases h

/-- info: [true, false, true, true] -/
#guard_msgs in
#eval
  let push : Directive × Nat := (op64 (.push (.reg (.low .rbp .W64))), 1)
  let call : Directive × Nat := (op64 (.call (.rel (.sub (.label "g") .after_current_instruction))), 5)
  let b0 : OBlk := ⟨0, 0, -16, 0, ⟨0, []⟩, [push]⟩
  [offsetsOk [⟨"f", [b0, ⟨1, 1, -16, 0, ⟨-8, []⟩, []⟩], []⟩],
   offsetsOk [⟨"f", [b0, ⟨1, 1, -16, 0, ⟨0, []⟩, []⟩], []⟩],
   offsetsOk [⟨"f", [b0, ⟨2, 1, -16, 0, ⟨0, []⟩, []⟩], []⟩],
   offsetsOk [⟨"f", [⟨0, 0, -16, 0, ⟨0, []⟩, [call]⟩, ⟨1, 5, -16, 0, ⟨0, []⟩, []⟩], []⟩]]

end Scc.Cert.Rt.X64
