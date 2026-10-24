/-
**The phase checks of the blocks from the placement check** (component A6,
`Scc/Cert/Rt/PhasesA64.lean`): a row of the block table of an AArch64 output
passing `Scc.Cert.PlaceOK.A64.placeOK` passes `blkPh`, the phase check a
block's proof takes (`blkPh_sound`), with the sites `Rt.A64.okPcOf` and the
phases `Rt.A64.phOf` of the program, at its address in the loaded thread.

A6 checks the rows' pcs, not their targets: a target in another phase than
the row's entry (a **crossing**, `crossOf`: a branch out of the phase, or a
`ret` whose return address `ra` is in another phase) must be dead. The
lemmas take any dead set holding the row's crossings; a row without
crossings takes `fun _ => false` (`crossOf … = []`).

- **`blkPh_of_rowPhOk`**: a row passing `Rt.A64.rowPhOk` at its group's
  address passes `blkPh`;
- **`blkPh_of_placeOK`**, **`blkPh_of_rowIn_placeOK`**, **`blkPh_of_rowAt_placeOK`**: every row of the
  table of an output passing `placeOK`, at its label's address in the
  canonical loader's thread (any entry state and data symbols), the row
  named by its label (`Rt.A64.rowIn`), or by its label, offset and
  instructions at any static offsets (`rowAt`).
-/
import Scc.Cert.PlaceOKA64
import Spike.Lib.A64SegInst

namespace Spike.Lib.A64.Phases

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow Spike.Lib.A64Consumer
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64 Scc.Cert.Link.A64

/-- **A block's crossings** at `pc`: the targets of its instructions (a
`ret`'s the return address `ra`, `aiTgts`) in another phase than `pc`'s. -/
def crossOf (lab : Label → Int64) (ph : Nat → Nat) (pc ra : Int64) (blk : List Directive) : List Nat :=
  (List.range blk.length).flatMap fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => ((aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).map (·.toBitVec.toNat)).filter
          fun t => ph t != ph pc.toBitVec.toNat
      | none => []
    | none => []

/-- **A checked row passes `blkPh`** at its group's address `a`, with any
dead set holding its crossings. -/
theorem blkPh_of_rowPhOk {okPc : Nat → Bool} {ph : Nat → Nat} {a : Nat} {b : Scc.Cert.Rt.A64.OBlk}
    {lab : Label → Int64} {pc ra : Int64} {dead : Nat → Bool} (h : Scc.Cert.Rt.A64.rowPhOk okPc ph a b = true)
    (hpc : pc = Int64.ofNat a + Int64.ofNat (4 * b.k)) (hd : ∀ t ∈ crossOf lab ph pc ra b.blk, dead t = true) :
    blkPh okPc ph dead lab pc ra b.blk = true := by
  obtain ⟨h1, h2⟩ := Scc.Cert.Rt.A64.rowPhOk_spec h
  have hq : ∀ j, (pc + Int64.ofNat (4 * j)).toBitVec.toNat = (a + 4 * (b.k + j)) % 2 ^ 64 := by
    intro j
    rw [hpc, ← Int64.ofNat_add, ← Int64.ofNat_add, show a + 4 * b.k + 4 * j = a + 4 * (b.k + j) by omega]
    simp
  have hp0 : pc.toBitVec.toNat = (a + 4 * b.k) % 2 ^ 64 := by
    rw [hpc, ← Int64.ofNat_add]; simp
  unfold blkPh
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.mp hk
  obtain ⟨o1, o2⟩ := h1 k hk'
  rw [← hp0] at o2
  obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.mp (h2 _ (List.getElem_mem hk'))
  have hc : ∀ t ∈ aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra ai,
      ph t.toBitVec.toNat ≠ ph pc.toBitVec.toNat → dead t.toBitVec.toNat = true := by
    intro t ht he
    apply hd
    simp only [crossOf, List.mem_flatMap, List.mem_range]
    refine ⟨k, hk', ?_⟩
    rw [List.getElem?_eq_getElem hk']
    dsimp only
    rw [hai, List.mem_filter, List.mem_map]
    exact ⟨⟨t, ht, rfl⟩, by simpa using he⟩
  rw [List.getElem?_eq_getElem hk']
  dsimp only
  rw [hai, hq k, o1, o2]
  simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  intro t ht
  by_cases he : ph t.toBitVec.toNat = ph pc.toBitVec.toNat
  · exact Or.inl he
  · exact Or.inr (hc t ht he)

variable {cfg : Config} {o : Scc.Cert.PlaceOK.A64.Out}

/-- **A row of the table of an output passing `placeOK` passes `blkPh`**
at its label's address in the canonical loader's thread (`lab`, any entry
state, any data symbols none of those below the code named like a code
label: `hs`, `Link.A64.noClash`'s first half), with the program's sites and phases and any dead
set holding its crossings. -/
theorem blkPh_of_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt cfg Λ o = true) {g : Scc.Cert.Rt.A64.OGrp}
    (hg : g ∈ o.place.blocks)
    {b : Scc.Cert.Rt.A64.OBlk} (hb : b ∈ g.bs) {E : Scc.Sem.Entry} {syms : List (String × Nat)}
    {lab : Label → Int64}
    (hl : (_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog syms).exe).label = lab)
    (hs : ∀ p ∈ Scc.Sem.symsBelow Λ.code.lo syms, Scc.Cert.Link.A64.codeOf Λ.code.lo o.prog p.1 = none) {ra : Int64} {dead : Nat → Bool}
    (hd : ∀ t ∈ crossOf lab (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog)
      (lab g.l + Int64.ofNat (4 * b.k)) ra b.blk, dead t = true) :
    blkPh (Scc.Cert.Rt.A64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog) dead lab (lab g.l + Int64.ofNat (4 * b.k)) ra
      b.blk = true := by
  obtain ⟨a, ha, hr⟩ := rowPhOk_of_placeOKAt h hg hb
  refine blkPh_of_rowPhOk hr ?_ hd
  rw [← hl, label_of_placeOKAt hs ha]

/-- **`blkPh_of_placeOK` for a row named by its label** (`Rt.A64.rowIn`). -/
theorem blkPh_of_rowIn_placeOK {Λ : Scc.Sem.Layout}
    (h : placeOKAt cfg Λ o = true) {l : Label} {b : Scc.Cert.Rt.A64.OBlk}
    (hr : Scc.Cert.Rt.A64.rowIn o.place.blocks l b = true) {E : Scc.Sem.Entry} {syms : List (String × Nat)}
    {lab : Label → Int64}
    (hl : (_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog syms).exe).label = lab)
    (hs : ∀ p ∈ Scc.Sem.symsBelow Λ.code.lo syms, Scc.Cert.Link.A64.codeOf Λ.code.lo o.prog p.1 = none) {ra : Int64} {dead : Nat → Bool}
    (hd : ∀ t ∈ crossOf lab (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog)
      (lab l + Int64.ofNat (4 * b.k)) ra b.blk, dead t = true) :
    blkPh (Scc.Cert.Rt.A64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog) dead lab (lab l + Int64.ofNat (4 * b.k)) ra
      b.blk = true := by
  obtain ⟨g, hg, rfl, hb⟩ := Scc.Cert.Rt.A64.mem_of_rowIn hr
  exact blkPh_of_placeOK h hg hb hl hs hd

/-- **A row at `l + 4 k` with the instructions `blk`**, at any offsets (a
block's phase check does not read them). -/
def rowAt (gs : List Scc.Cert.Rt.A64.OGrp) (l : Label) (k : Nat) (blk : List Directive) : Bool :=
  gs.any fun g => decide (g.l = l) && g.bs.any fun b => b.k == k && decide (b.blk = blk)

/-- **`blkPh_of_placeOK` for a block named by its label, offset and
instructions** (`rowAt`). -/
theorem blkPh_of_rowAt_placeOK {Λ : Scc.Sem.Layout}
    (h : placeOKAt cfg Λ o = true) {l : Label} {k : Nat} {blk : List Directive}
    (hr : rowAt o.place.blocks l k blk = true) {E : Scc.Sem.Entry} {syms : List (String × Nat)}
    {lab : Label → Int64}
    (hl : (_root_.Executable.labels
      (Scc.Sem.A64.threadAt E Λ.code.lo o.prog syms).exe).label = lab)
    (hs : ∀ p ∈ Scc.Sem.symsBelow Λ.code.lo syms, Scc.Cert.Link.A64.codeOf Λ.code.lo o.prog p.1 = none) {ra : Int64} {dead : Nat → Bool}
    (hd : ∀ t ∈ crossOf lab (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog)
      (lab l + Int64.ofNat (4 * k)) ra blk, dead t = true) :
    blkPh (Scc.Cert.Rt.A64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.A64.phOf Λ.code.lo o.prog) dead lab (lab l + Int64.ofNat (4 * k)) ra
      blk = true := by
  simp only [rowAt, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  obtain ⟨g, hg, rfl, b, hb, rfl, rfl⟩ := hr
  exact blkPh_of_placeOK h hg hb hl hs hd

end Spike.Lib.A64.Phases
