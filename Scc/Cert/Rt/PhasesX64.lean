import Scc.Cert.LinkX64
import Scc.Cert.Rt.OffsX64

/-!
# The phases of the runtime's thread start on x86-64

The x86-64 twin of `Scc/Cert/Rt/PhasesA64.lean`. The runtime's thread start
owns four words (`scc_rt_pinned_next`, the stack lock, `scc_rt_stack_next`,
the take's word) whose values are functions of the pc: a **phase index**
`ph pc`, four bits, each set on a fixed set of code ranges of the runtime
(`phTab`: ranges between two code labels, each plus a number of bytes). A
block's proof needs its pcs off the marks' sites (`okPc`) and in its entry's
phase, and so every target but a dead one (`Spike.Lib.X64Consumer.blkPh`).

The ranges and the sites are fixed by the runtime's code, the same in every
output: `phOf lo cells` and `okPcOf lo cells Λ` resolve them in the code
cells at the code base. `phasesOk` (the placement check's component A6)
checks every row of the block table: its group's label resolves, every pc
of the row is off the sites and in the row's entry phase, and every
instruction of the row is covered (`classify`), but for a **site row**:
the one-byte `nop` at a site (`siteRow`), whose proof is the site's
obligation (the hand `takeSiteW`), not a block's. The rows' targets are not
checked: a target in another phase is a crossing (`crossOf`,
`Spike/Lib/X64PhasesOfPlaceOK.lean`), which the row's proof shows dead.

`label_threadAt_of_codeLabel` (generic) puts a code label of the cells at
its `codeLabel` address in the canonical loader's thread, for any data
symbols none below the code giving a valid layout.

Where x86-64 differs from AArch64: offsets are in bytes (a range's bound is
a label plus a byte count; a row's pcs are its group's address plus the
row's byte offset plus the sizes of the cells before each, `cellOff`); a
label cell has size `0` in a valid layout only, so the label lemma takes
`ValidLayout` (the placement check gives it for the loader's symbols,
`validLayout_of_placeOK`); the x64 table lists the sites' `nop`s as rows
of their own (the AArch64 table starts its site groups after the `nop`), so
the check skips them (`siteRow`) and `rowPhOk_of_phasesOk` holds for every
other row; the ranges avoid the program-numbered local
labels of `scc_rt_thread_init` (`.Lscc_rt_thread_init.x7` in `ret0`), naming
the byte offset from the function's label instead.
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64

/-! ## Code labels in the loaded thread -/

private theorem labelAddr_spec {l : String} : ∀ {cells : List (Directive × Nat)} {base a : Nat},
    codeLabel base cells l = some a →
    ∃ n z, cells[n]? = some (.label l, z) ∧ (∀ c ∈ cells.take n, c.1 ≠ .label l) ∧
      base + ((cells.take n).map (·.2)).sum = a
  | [], _, _, h => by cases h
  | c :: cs, base, a, h => by
    simp only [codeLabel, labelAddr] at h
    split at h
    · next hd =>
      cases h
      obtain ⟨d, z⟩ := c
      have hd' : d = .label l := by cases d <;> simp_all [labelName]
      subst hd'
      exact ⟨0, z, by simp, by simp, by simp⟩
    · next hd =>
      obtain ⟨n, z, h1, h2, h3⟩ := labelAddr_spec (cells := cs) h
      refine ⟨n + 1, z, by simpa using h1, ?_, ?_⟩
      · intro c' hc'
        simp only [List.take_succ_cons, List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · intro he; exact hd (by simp [he, labelName])
        · exact h2 c' hc'
      · simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega

/-- **A code label at its `codeLabel` address** in the canonical loader's
thread, for any data symbols none below the code
(`Link.X64.above_of_symsOk`, `Link.X64.above_of_loadOk`) giving a valid
layout. -/
theorem label_threadAt_of_codeLabel {E : Entry} {base : Nat} {cells : List (Directive × Nat)}
    {syms : List (String × Nat)} [Kraken.Executable.ValidLayout (threadAt E base cells syms).exe]
    {l : String} {a : Nat} (hs : ∀ p ∈ syms, base ≤ p.2) (h : codeLabel base cells l = some a) :
    (_root_.Executable.labels (threadAt E base cells syms).exe).label l = Int64.ofNat a := by
  obtain ⟨n, z, h1, h2, h3⟩ := labelAddr_spec h
  have hn : n < cells.length := by
    rcases Nat.lt_or_ge n cells.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h1; cases h1
  have hcells : (threadAt E base cells syms).exe.2 =
      cells ++ placeSyms (.byteArray (.mk #[])) .label (codeEnd base cells) syms := by
    rw [Link.X64.threadAt_exe_of_above hs]
  have hz' : (threadAt E base cells syms).exe.2[n]? = some (.label l, z) := by
    rw [hcells, List.getElem?_append_left hn, h1]
  have hz0 := Kraken.Executable.ValidLayout.label_size n l z hz'
  subst hz0
  have htake : (threadAt E base cells syms).exe.2.take n = cells.take n := by
    rw [hcells, List.take_append_of_le_length (Nat.le_of_lt hn)]
  rw [Kraken.Executable.label_addrOf _ l n hz' (by rw [htake]; exact h2)]
  unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
  rw [htake, Link.X64.threadAt_exe_of_above hs]
  rw [← Int64.ofNat_add, h3]

/-! ## The phase table -/

/-- **A code range** `[l1 + o1, l2 + o2)`: from `o1` bytes after the label
`l1` up to `o2` bytes after `l2`. -/
structure PhRange where
  l1 : String
  o1 : Nat
  l2 : String
  o2 : Nat

/-- **`scc_rt_pinned_next` is still `0`**: `_start` and `scc_rt_start` up
to the call of `scc_rt_alloc_tcb`, and that function up to and including
its counter's `lock xadd`. -/
def bPR : List PhRange :=
  [⟨"_start", 0, ".Lscc_rt_start.x0", 0⟩, ⟨"scc_rt_alloc_tcb", 0, ".Lscc_rt_alloc_tcb.len", 163⟩]

/-- **The stack lock is held**: past the `xchg` of `scc_rt_stack_take` up
to and including the store releasing it on its bump path. -/
def bLR : List PhRange :=
  [⟨".Lscc_rt_stack_take.spin14", 14, ".Lscc_rt_stack_take.bump", 31⟩]

/-- **`scc_rt_stack_next` is still `0`**: `scc_rt_start` up to the return
of its call of `scc_rt_thread_init`, `scc_rt_alloc_tcb` (and
`scc_rt_thread_reserve`), `scc_rt_thread_init` up to the return of its call
(24 bytes in: its local label there is numbered per program), and
`scc_rt_stack_take` up to and including the `lock xadd`. -/
def bNR : List PhRange :=
  [⟨"_start", 0, ".Lscc_rt_start.x1", 0⟩, ⟨"scc_rt_alloc_tcb", 0, "scc_rt_thread_reserve", 0⟩,
    ⟨"scc_rt_thread_init", 0, "scc_rt_thread_init", 24⟩,
    ⟨"scc_rt_stack_take", 0, ".Lscc_rt_stack_take.bump", 61⟩]

/-- **The stack is not taken yet**: as `bNR`, and `scc_rt_stack_take` up
to and including the take site. -/
def bTR : List PhRange :=
  [⟨"_start", 0, ".Lscc_rt_start.x1", 0⟩, ⟨"scc_rt_alloc_tcb", 0, "scc_rt_thread_reserve", 0⟩,
    ⟨"scc_rt_thread_init", 0, "scc_rt_thread_init", 24⟩, ⟨"scc_rt_stack_take", 0, "scc_rt_take_site", 1⟩]

/-- A range's bounds, its labels resolved by `code` (addresses modulo
`2 ^ 64`, as the pcs are). -/
def PhRange.resolve (code : String → Option Nat) (r : PhRange) : Option (Nat × Nat) :=
  match code r.l1, code r.l2 with
  | some a, some b => some ((a + r.o1) % 2 ^ 64, (b + r.o2) % 2 ^ 64)
  | _, _ => none

/-- **The resolved phase table**: the four bits' ranges. -/
structure PhTab where
  p : List (Nat × Nat)
  l : List (Nat × Nat)
  n : List (Nat × Nat)
  t : List (Nat × Nat)
  deriving DecidableEq

/-- The phase table, its labels resolved by `code`, if every one resolves. -/
def phTabBy (code : String → Option Nat) : Option PhTab := do
  let p ← bPR.mapM (PhRange.resolve code)
  let l ← bLR.mapM (PhRange.resolve code)
  let n ← bNR.mapM (PhRange.resolve code)
  let t ← bTR.mapM (PhRange.resolve code)
  pure ⟨p, l, n, t⟩

/-- The phase table of the cells at `lo`, if every label resolves. -/
def phTabOf (lo : Nat) (cells : List (Directive × Nat)) : Option PhTab := phTabBy (codeLabel lo cells)

/-- The pc is in one of the ranges. -/
def inRs (rs : List (Nat × Nat)) (pc : Nat) : Bool := rs.any fun r => r.1 ≤ pc && pc < r.2

/-- **The phase index of a pc** in a table: its four bits. -/
def PhTab.ph (T : PhTab) (pc : Nat) : Nat :=
  (inRs T.p pc).toNat + 2 * (inRs T.l pc).toNat + 4 * (inRs T.n pc).toNat + 8 * (inRs T.t pc).toNat

/-- **The phase index of a pc** of the cells at `lo` (`0` if a label of
the table is missing, and then `phasesOk` fails). -/
def phOf (lo : Nat) (cells : List (Directive × Nat)) : Nat → Nat :=
  match phTabOf lo cells with
  | some T => T.ph
  | none => fun _ => 0

/-! ## The sites -/

/-- **The marks' site labels**: the take and release sites, the five
abort stubs' (in the order of the hand proofs). -/
def siteLabels (Λ : Scc.Sem.Layout) : List String :=
  ["scc_rt_take_site", "scc_rt_release_site"] ++ [.overflow, .heap, .stack, .writeErr, .threads].map Λ.abortLbl

/-- The sites' addresses, their labels resolved by `code`, if every one
resolves. -/
def sitesBy (code : String → Option Nat) (Λ : Scc.Sem.Layout) : Option (List Nat) :=
  (siteLabels Λ).mapM code

/-- The sites' addresses in the cells at `lo`, if every label resolves. -/
def sitesOf (lo : Nat) (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) : Option (List Nat) :=
  sitesBy (codeLabel lo cells) Λ

/-- **The pcs off the sites** (none if a site label is missing, and then
`phasesOk` fails). -/
def okPcOf (lo : Nat) (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) (pc : Nat) : Bool :=
  match sitesOf lo cells Λ with
  | some ss => !(ss.contains pc)
  | none => false

/-! ## The labels, keyed

As `PhasesA64.lean`: the check resolves the labels of its rows, its phase
table and its sites in one table of the cells' labels built in one pass
(`labTab`: each label's `key` with its address, in program order), each
lookup comparing numbers (`lookupK`); `codeT_eq`: the first match is
`codeLabel`'s. -/

/-- `labTab` for the code generator. -/
def labTabImpl : List (Directive × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | c :: cs, base => match labelName c.1 with
    | some m => (key m, base) :: labTabImpl cs (base + c.2)
    | none => labTabImpl cs (base + c.2)

/-- **The cells' labels**: each label's `key` with its address, from the
code base `base`, in program order. -/
@[implemented_by labTabImpl] def labTab (cs : List (Directive × Nat)) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun c _ r base => match labelName c.1 with
      | some m => (key m, base) :: r (base + c.2)
      | none => r (base + c.2)) cs

/-- `lookupK` for the code generator. -/
def lookupKImpl (k : Nat) (T : List (Nat × Nat)) : Option Nat := T.lookup k

/-- The address of the first entry of key `k`. -/
@[implemented_by lookupKImpl] def lookupK (k : Nat) (T : List (Nat × Nat)) : Option Nat :=
  List.rec (motive := fun _ => Option Nat) none (fun p _ r => if Nat.beq k p.1 then some p.2 else r) T

/-- **The code labels of the cells at `lo`, keyed.** -/
def codeT (lo : Nat) (cells : List (Directive × Nat)) (l : String) : Option Nat := lookupK (key l) (labTab cells lo)

private theorem lookupK_labTab (l : String) : ∀ (cells : List (Directive × Nat)) (base : Nat),
    lookupK (key l) (labTab cells base) = codeLabel base cells l
  | [], _ => rfl
  | c :: cs, base => by
    have ih := lookupK_labTab l cs (base + c.2)
    simp only [codeLabel, labelAddr] at ih ⊢
    simp only [labTab] at ih ⊢
    cases hd : labelName c.1 with
    | none =>
      simp only [lookupK] at ih ⊢
      rw [ih]; simp
    | some m =>
      simp only [lookupK] at ih ⊢
      by_cases hm : m = l
      · subst hm; simp [Nat.beq_refl]
      · have hk : Nat.beq (key l) (key m) = false := by
          cases h : Nat.beq (key l) (key m)
          · rfl
          · exact absurd (key_inj (Nat.eq_of_beq_eq_true h)).symm hm
        rw [hk]
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, hm]
        exact ih

/-- **The keyed labels are `codeLabel`'s.** -/
theorem codeT_eq (lo : Nat) (cells : List (Directive × Nat)) : codeT lo cells = codeLabel lo cells := by
  funext l; exact lookupK_labTab l cells lo

/-! ## The check -/

/-- **A row's phase check** at its group's address `a`: every pc of the row
(`a` plus the row's byte offset plus the sizes of the cells before it) off
the sites and in the row's entry phase, every instruction covered. -/
def rowPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (a : Nat) (b : OBlk) : Bool :=
  (List.range b.blk.length).all (fun j =>
    okPc ((a + b.off + Spike.Lib.X64.cellOff b.blk j) % 2 ^ 64) &&
      ph ((a + b.off + Spike.Lib.X64.cellOff b.blk j) % 2 ^ 64) == ph ((a + b.off) % 2 ^ 64)) &&
  b.blk.all fun d => (Spike.Lib.X64.classify d.1).isSome

/-- **A site's instruction**: the one-byte `nop`. -/
def siteBlk : List (Directive × Nat) := [(Kraken.Promising.Lower.X64.op64 (.nop 1), 1)]

/-- **A site row** at its group's address `a`: the site's `nop` at one of
the sites `ss`. -/
def siteRow (ss : List Nat) (a : Nat) (b : OBlk) : Bool :=
  decide (b.blk = siteBlk) && ss.contains ((a + b.off) % 2 ^ 64)

/-- The rows' check with a resolved table and sites: every row but a site
row passes its phase check. -/
def phasesOkT (code : String → Option Nat) (T : PhTab) (ss : List Nat) (gs : List OGrp) : Bool :=
  gs.all fun g => match code g.l with
    | some a => g.bs.all fun b => siteRow ss a b || rowPhOk (fun pc => !(ss.contains pc)) T.ph a b
    | none => false

/-- The check with the labels resolved by `code`. -/
def phasesOkBy (code : String → Option Nat) (Λ : Scc.Sem.Layout) (gs : List OGrp) : Bool :=
  match phTabBy code, sitesBy code Λ with
  | some T, some ss => decide ss.Nodup && phasesOkT code T ss gs
  | _, _ => false

/-- **The phases** (component A6): the phase table and the sites resolve,
the sites are distinct, and every row but a site row passes its phase check
(`rowPhOk`); the labels resolved in one keyed table (`codeT`). -/
def phasesOk (lo : Nat) (cells : List (Directive × Nat)) (Λ : Scc.Sem.Layout) (gs : List OGrp) : Bool :=
  phasesOkBy (codeT lo cells) Λ gs

/-- **A row of a checked table**: its group's label resolves, and the row,
not a site's `nop` (`hs`), passes its phase check with `okPcOf` and
`phOf`. -/
theorem rowPhOk_of_phasesOk {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout} {gs : List OGrp}
    (h : phasesOk lo cells Λ gs = true) {g : OGrp} (hg : g ∈ gs) {b : OBlk} (hb : b ∈ g.bs)
    (hs : b.blk ≠ siteBlk) :
    ∃ a, codeLabel lo cells g.l = some a ∧ rowPhOk (okPcOf lo cells Λ) (phOf lo cells) a b = true := by
  unfold phasesOk at h
  rw [codeT_eq] at h
  unfold phasesOkBy at h
  split at h
  · next T ss hT hss =>
    have hg' := List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).2 g hg
    split at hg'
    · next a ha =>
      refine ⟨a, ha, ?_⟩
      have hr := List.all_eq_true.mp hg' b hb
      have hns : siteRow ss a b = false := by simp [siteRow, hs]
      rw [hns, Bool.false_or] at hr
      have hph : phOf lo cells = T.ph := by unfold phOf phTabOf; rw [hT]
      have hok : okPcOf lo cells Λ = fun pc => !(ss.contains pc) := by
        funext pc; unfold okPcOf sitesOf; rw [hss]
      rw [hph, hok]; exact hr
    · cases hg'
  · cases h

/-- **The sites are distinct** in a checked table. -/
theorem sites_nodup_of_phasesOk {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout} {gs : List OGrp}
    (h : phasesOk lo cells Λ gs = true) : ∃ ss, sitesOf lo cells Λ = some ss ∧ ss.Nodup := by
  unfold phasesOk at h
  rw [codeT_eq] at h
  unfold phasesOkBy at h
  split at h
  · next T ss hT hss =>
    exact ⟨ss, hss, of_decide_eq_true (Bool.and_eq_true _ _ ▸ h).1⟩
  · cases h

/-- **A row's pcs**: at `j < length` the pc `a + off + cellOff blk j` is off
the sites and in the entry's phase; every instruction is covered. -/
theorem rowPhOk_spec {okPc : Nat → Bool} {ph : Nat → Nat} {a : Nat} {b : OBlk} (h : rowPhOk okPc ph a b = true) :
    (∀ j < b.blk.length, okPc ((a + b.off + Spike.Lib.X64.cellOff b.blk j) % 2 ^ 64) = true ∧
      ph ((a + b.off + Spike.Lib.X64.cellOff b.blk j) % 2 ^ 64) = ph ((a + b.off) % 2 ^ 64)) ∧
    ∀ d ∈ b.blk, (Spike.Lib.X64.classify d.1).isSome = true := by
  simp only [rowPhOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨fun j hj => h.1 j hj, h.2⟩

end Scc.Cert.Rt.X64
