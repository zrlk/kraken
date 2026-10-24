/-
**The phase checks of the blocks from the placement check** on x86-64
(component A6, `Scc/Cert/Rt/PhasesX64.lean`), the twin of
`Spike/Lib/A64PhasesOfPlaceOK.lean`: a row of the block table of an x86-64
output passing `Scc.Cert.PlaceOK.X64.placeOK`, not a site's `nop`, passes
`blkPh`, the phase check a block's proof takes (`blkPh_sound`), with the
sites `Rt.X64.okPcOf` and the phases `Rt.X64.phOf` of the cells, at its
address in the loaded thread.

A6 checks the rows' pcs, not their targets: a target in another phase than
the row's entry (a **crossing**, `crossOf`: a branch out of the phase, or a
`ret` whose return address `ra` is in another phase) must be dead. The
lemmas take any dead set holding the row's crossings; a row without
crossings takes `fun _ => false` (`crossOf … = []`).

- **`blkPh_of_rowPhOk`**: a row passing `Rt.X64.rowPhOk` at its group's
  address passes `blkPh`;
- **`blkPh_of_placeOK`**, **`blkPh_of_rowIn_placeOK`**, **`blkPh_of_rowAt_placeOK`**: every row of the
  table of an output passing `placeOKAt` at any layout `Λ` but a site's
  `nop`, at its label's address plus its byte offset in the canonical
  loader's thread (any entry state, the loader's data symbols, on either
  side of the code: A2's `noClash` keeps those below it off the code
  labels, `label_of_placeOKAt`), the row named by its label
  (`Rt.X64.rowIn`), or by its label, byte offset and cells at any static
  offsets (`rowAt`). None assumes every symbol above the code.

Where x86-64 differs from AArch64: a row's pc is its label's address plus
its byte offset (`b.off`), each instruction's the sizes of the cells before
it further (`cellOff`), the fall-through the cell's size after that; the
data symbols are the loader's (`loadSyms`: the label lemma needs a valid
layout, which A2 gives for them); a site's `nop` row is not checked by A6
(`hs`).
-/
import Scc.Cert.PlaceOKX64
import Spike.Lib.X64SegInst

namespace Spike.Lib.X64.Phases

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64 Spike.Lib.X64Consumer
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64 Scc.Cert.Link.X64

/-- **A block's crossings** at `pc`: the targets of its instructions (a
`ret`'s the return address `ra`, `aiTgts`) in another phase than `pc`'s. -/
def crossOf (lab : Label → Int64) (ph : Nat → Nat) (pc ra : Int64) (blk : List (Directive × Nat)) : List Nat :=
  (List.range blk.length).flatMap fun k =>
    match blk[k]? with
    | some dz => match Spike.Lib.X64.classify dz.1 with
      | some a => ((aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a).map
          (·.toBitVec.toNat)).filter fun t => ph t != ph pc.toBitVec.toNat
      | none => []
    | none => []

/-- **A checked row passes `blkPh`** at its group's address `a` plus its
byte offset, with any dead set holding its crossings. -/
theorem blkPh_of_rowPhOk {okPc : Nat → Bool} {ph : Nat → Nat} {a : Nat} {b : Scc.Cert.Rt.X64.OBlk}
    {lab : Label → Int64} {pc ra : Int64} {dead : Nat → Bool} (h : Scc.Cert.Rt.X64.rowPhOk okPc ph a b = true)
    (hpc : pc = Int64.ofNat a + Int64.ofNat b.off) (hd : ∀ t ∈ crossOf lab ph pc ra b.blk, dead t = true) :
    blkPh okPc ph dead lab pc ra b.blk = true := by
  obtain ⟨h1, h2⟩ := Scc.Cert.Rt.X64.rowPhOk_spec h
  have hq : ∀ j, (pc + Int64.ofNat (cellOff b.blk j)).toBitVec.toNat =
      (a + b.off + cellOff b.blk j) % 2 ^ 64 := by
    intro j
    rw [hpc, ← Int64.ofNat_add, ← Int64.ofNat_add]
    simp
  have hp0 : pc.toBitVec.toNat = (a + b.off) % 2 ^ 64 := by
    rw [hpc, ← Int64.ofNat_add]; simp
  unfold blkPh
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.mp hk
  obtain ⟨o1, o2⟩ := h1 k hk'
  rw [← hp0] at o2
  obtain ⟨ai, hai⟩ := Option.isSome_iff_exists.mp (h2 _ (List.getElem_mem hk'))
  have hc : ∀ t ∈ aiTgts lab (pc + Int64.ofNat (cellOff b.blk k) + Int64.ofNat b.blk[k].2) ra ai,
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

variable {cfg : Config} {o : Scc.Cert.PlaceOK.X64.Out}

/-- **A row of the table of an output passing `placeOK`, not a site's
`nop`, passes `blkPh`** at its label's address plus its byte offset in the
canonical loader's thread (`lab`, any entry state, the loader's data
symbols), with the program's sites and phases and any dead set holding its
crossings. -/
theorem blkPh_of_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt cfg Λ o = true) {g : Scc.Cert.Rt.X64.OGrp}
    (hg : g ∈ o.place.blocks)
    {b : Scc.Cert.Rt.X64.OBlk} (hb : b ∈ g.bs) (hs : b.blk ≠ Scc.Cert.Rt.X64.siteBlk) {E : Scc.Sem.Entry}
    {lab : Label → Int64}
    (hl : (_root_.Executable.labels (Scc.Sem.X64.threadAt E Λ.code.lo o.prog
      (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label = lab)
    {ra : Int64} {dead : Nat → Bool}
    (hd : ∀ t ∈ crossOf lab (Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog)
      (lab g.l + Int64.ofNat b.off) ra b.blk, dead t = true) :
    blkPh (Scc.Cert.Rt.X64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog) dead lab (lab g.l + Int64.ofNat b.off) ra
      b.blk = true := by
  obtain ⟨a, ha, hr⟩ := rowPhOk_of_placeOKAt h hg hb hs
  refine blkPh_of_rowPhOk hr ?_ hd
  rw [← hl, label_of_placeOKAt h ha]

/-- **`blkPh_of_placeOK` for a row named by its label** (`Rt.X64.rowIn`). -/
theorem blkPh_of_rowIn_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt cfg Λ o = true) {l : Label}
    {b : Scc.Cert.Rt.X64.OBlk}
    (hr : Scc.Cert.Rt.X64.rowIn o.place.blocks l b = true) (hs : b.blk ≠ Scc.Cert.Rt.X64.siteBlk)
    {E : Scc.Sem.Entry} {lab : Label → Int64}
    (hl : (_root_.Executable.labels (Scc.Sem.X64.threadAt E Λ.code.lo o.prog
      (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label = lab)
    {ra : Int64} {dead : Nat → Bool}
    (hd : ∀ t ∈ crossOf lab (Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog)
      (lab l + Int64.ofNat b.off) ra b.blk, dead t = true) :
    blkPh (Scc.Cert.Rt.X64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog) dead lab (lab l + Int64.ofNat b.off) ra
      b.blk = true := by
  obtain ⟨g, hg, rfl, hb⟩ := Scc.Cert.Rt.X64.mem_of_rowIn hr
  exact blkPh_of_placeOK h hg hb hs hl hd

/-- **A row at `l + off` with the cells `blk`**, at any offsets (a block's
phase check does not read them). -/
def rowAt (gs : List Scc.Cert.Rt.X64.OGrp) (l : Label) (off : Nat) (blk : List (Directive × Nat)) : Bool :=
  gs.any fun g => decide (g.l = l) && g.bs.any fun b => b.off == off && decide (b.blk = blk)

/-- **`blkPh_of_placeOK` for a block named by its label, byte offset and
cells** (`rowAt`). -/
theorem blkPh_of_rowAt_placeOK {Λ : Scc.Sem.Layout} (h : placeOKAt cfg Λ o = true) {l : Label} {off : Nat}
    {blk : List (Directive × Nat)}
    (hr : rowAt o.place.blocks l off blk = true) (hs : blk ≠ Scc.Cert.Rt.X64.siteBlk) {E : Scc.Sem.Entry}
    {lab : Label → Int64}
    (hl : (_root_.Executable.labels (Scc.Sem.X64.threadAt E Λ.code.lo o.prog
      (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label = lab)
    {ra : Int64} {dead : Nat → Bool}
    (hd : ∀ t ∈ crossOf lab (Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog)
      (lab l + Int64.ofNat off) ra blk, dead t = true) :
    blkPh (Scc.Cert.Rt.X64.okPcOf Λ.code.lo o.prog Λ)
      (Scc.Cert.Rt.X64.phOf Λ.code.lo o.prog) dead lab (lab l + Int64.ofNat off) ra
      blk = true := by
  simp only [rowAt, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  obtain ⟨g, hg, rfl, b, hb, rfl, rfl⟩ := hr
  exact blkPh_of_placeOK h hg hb hs hl hd

end Spike.Lib.X64.Phases
