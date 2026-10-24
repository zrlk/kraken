import Scc.Cert.LinkA64
import Scc.Cert.Rt.OffsA64

/-!
# The phases of the runtime's thread start

The runtime's thread start owns four words (`scc_rt_pinned_next`, the stack
lock, `scc_rt_stack_next`, the take's word) whose values are functions of
the pc: a **phase index** `ph pc`, four bits, each set on a fixed set of
code ranges of the runtime (`phTab`: ranges between two code labels, each
plus a number of instructions). A block's proof needs its pcs off the
marks' sites (`okPc`) and in its entry's phase, and so every target but a
dead one (`Spike.Lib.A64Consumer.blkPh`).

The ranges and the sites are fixed by the runtime's code, the same in every
output: `phOf lo prog` and `okPcOf lo prog Λ` resolve them in the program at
the code base. `phasesOk` (the placement check's component A6) checks every
row of the block table: its group's label resolves, every pc of the row is
off the sites and in the row's entry phase, and every instruction of the row
is covered (`classify`). The rows' targets are not checked: a target in
another phase is a crossing (`crossOf`, `Spike/Lib/A64PhasesOfPlaceOK.lean`),
which the row's proof shows dead.

`label_threadAt_of_codeOf` (generic) puts a code label of `prog` at its
`codeOf` address in the canonical loader's thread, for any data symbols
none below the code.
-/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link.A64

/-! ## Code labels in the loaded thread -/

private theorem labelAddr_spec {l : String} : ∀ {prog : Program} {base a : Nat},
    labelAddr labelName Directive.fakeSize base l prog = some a →
    ∃ n, (prog.map fun d => (d, d.fakeSize))[n]? = some (.label l, 0) ∧
      (∀ dz ∈ (prog.map fun d => (d, d.fakeSize)).take n, dz.1 ≠ .label l) ∧
      base + (((prog.map fun d => (d, d.fakeSize)).take n).map (·.2)).sum = a
  | [], _, _, h => by cases h
  | d :: ds, base, a, h => by
    simp only [labelAddr] at h
    split at h
    · next hd =>
      cases h
      have hd' : d = .label l := by cases d <;> simp_all [labelName]
      subst hd'
      exact ⟨0, by simp [Directive.fakeSize], by simp, by simp⟩
    · next hd =>
      obtain ⟨n, h1, h2, h3⟩ := labelAddr_spec h
      refine ⟨n + 1, by simpa using h1, ?_, ?_⟩
      · intro dz hdz
        simp only [List.map_cons, List.take_succ_cons, List.mem_cons] at hdz
        rcases hdz with rfl | hdz
        · intro he; exact hd (by simp only at he; simp [he, labelName])
        · exact h2 dz hdz
      · simp only [List.map_cons, List.take_succ_cons, List.sum_cons]; omega

/-- **A code label at its `codeOf` address** in the canonical loader's
thread, for any data symbols none below the code (`above_of_symsOk`; the
loader's, with symbols below the code: `label_threadAt_of_codeOf_below`). -/
theorem label_threadAt_of_codeOf {E : Entry} {base : Nat} {prog : Program} {syms : List (String × Nat)}
    {l : String} {a : Nat} (hs : ∀ p ∈ syms, base ≤ p.2) (h : codeOf base prog l = some a) :
    (_root_.Executable.labels (threadAt E base prog syms).exe).label l = Int64.ofNat a := by
  obtain ⟨n, h1, h2, h3⟩ := labelAddr_spec h
  have hn : n < (prog.map fun d => (d, d.fakeSize)).length := by
    rcases Nat.lt_or_ge n (prog.map fun d => (d, d.fakeSize)).length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h1; cases h1
  have hcells : (threadAt E base prog syms).exe.2 =
      prog.map (fun d => (d, d.fakeSize)) ++ placeSyms (.byteArray (.mk #[])) .label (codeEnd base prog) syms := by
    rw [threadAt_exe_of_above hs]
  have htake : (threadAt E base prog syms).exe.2.take n = (prog.map fun d => (d, d.fakeSize)).take n := by
    rw [hcells, List.take_append_of_le_length (Nat.le_of_lt hn)]
  rw [Kraken.Executable.label_addrOf _ l n (by rw [hcells, List.getElem?_append_left hn]; exact h1)
    (by rw [htake]; exact h2)]
  unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
  rw [htake, threadAt_exe_of_above hs]
  rw [← Int64.ofNat_add, h3]

/-- **A code label at its `codeOf` address** in the canonical loader's
thread, the data symbols below the code before it (`lays_threadAt_below`):
no data symbol below the code is named `l`. -/
theorem label_threadAt_of_codeOf_below {E : Entry} {base : Nat} {prog : Program} {syms : List (String × Nat)}
    {l : String} {a : Nat} (hs : ∀ p ∈ symsBelow base syms, p.1 ≠ l) (h : codeOf base prog l = some a) :
    (_root_.Executable.labels (threadAt E base prog syms).exe).label l = Int64.ofNat a := by
  obtain ⟨n, h1, h2, h3⟩ := labelAddr_spec h
  have hn : n < (prog.map fun d => (d, d.fakeSize)).length := by
    rcases Nat.lt_or_ge n (prog.map fun d => (d, d.fakeSize)).length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h1; cases h1
  have hcells := threadAt_exe_cells E base prog syms
  generalize hB : placeBelow (Directive.byteArray (.mk #[])) Directive.label base syms = B at hcells
  have htake : (threadAt E base prog syms).exe.2.take (B.length + n) =
      B ++ (prog.map fun d => (d, d.fakeSize)).take n := by
    rw [hcells, List.take_add, List.take_left, List.drop_left, List.take_append_of_le_length (Nat.le_of_lt hn)]
  rw [Kraken.Executable.label_addrOf _ l (B.length + n)
    (by rw [hcells, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          List.getElem?_append_left hn]; exact h1)
    (by
      rw [htake]
      intro dz hdz
      rcases List.mem_append.mp hdz with hdz | hdz
      · rw [← hB] at hdz
        rcases (Scc.Cert.PlaceSyms.placeBelow_spec _ _ base syms).1 dz hdz with ⟨he, -⟩ | ⟨p, hp, rfl⟩
        · rw [he]; simp
        · intro he; exact hs p hp (by simpa using he)
      · exact h2 dz hdz)]
  have hBs := (Scc.Cert.PlaceSyms.placeBelow_spec (Directive.byteArray (.mk #[])) Directive.label base syms).2
  rw [hB] at hBs
  unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
  rw [htake, List.map_append, List.sum_append]
  show Int64.ofNat (exeStart base syms) + _ = _
  rw [← Int64.ofNat_add, ← h3]
  congr 1
  omega

/-! ## The phase table -/

/-- **A code range** `[l1 + 4 o1, l2 + 4 o2)`: from `o1` instructions
after the label `l1` up to `o2` instructions after `l2`. -/
structure PhRange where
  l1 : String
  o1 : Nat
  l2 : String
  o2 : Nat

/-- **`scc_rt_pinned_next` is still `0`**: `_start` and `scc_rt_start` up
to the call of `scc_rt_alloc_tcb`, and that function up to and including
its counter's add. -/
def bPR : List PhRange :=
  [⟨"_start", 0, ".L0_scc_rt_start.sp2", 0⟩, ⟨"scc_rt_alloc_tcb", 0, ".L3_scc_rt_alloc_tcb.1_len", 38⟩]

/-- **The stack lock is held**: past the `swpal` of `scc_rt_stack_take` up
to and including the `stlr` of its bump path. -/
def bLR : List PhRange :=
  [⟨".L6_scc_rt_stack_take.4_spin14", 3, ".L6_scc_rt_stack_take.7_bump", 6⟩]

/-- **`scc_rt_stack_next` is still `0`**: up to `.sp3` of `scc_rt_start`,
`scc_rt_alloc_tcb` (and `scc_rt_thread_reserve`), `scc_rt_thread_init` up
to the return of its call, and `scc_rt_stack_take` up to and including the
add. -/
def bNR : List PhRange :=
  [⟨"_start", 0, ".L0_scc_rt_start.sp3", 0⟩, ⟨"scc_rt_alloc_tcb", 0, "scc_rt_thread_reserve", 0⟩,
    ⟨"scc_rt_thread_init", 0, ".L5_scc_rt_thread_init.sp0", 0⟩,
    ⟨"scc_rt_stack_take", 0, ".L6_scc_rt_stack_take.7_bump", 12⟩]

/-- **The stack is not taken yet**: as `bNR`, and `scc_rt_stack_take` up
to and including the take site. -/
def bTR : List PhRange :=
  [⟨"_start", 0, ".L0_scc_rt_start.sp3", 0⟩, ⟨"scc_rt_alloc_tcb", 0, "scc_rt_thread_reserve", 0⟩,
    ⟨"scc_rt_thread_init", 0, ".L5_scc_rt_thread_init.sp0", 0⟩, ⟨"scc_rt_stack_take", 0, "scc_rt_take_site", 1⟩]

/-- A range's bounds, its labels resolved by `code` (addresses modulo
`2 ^ 64`, as the pcs are). -/
def PhRange.resolve (code : String → Option Nat) (r : PhRange) : Option (Nat × Nat) :=
  match code r.l1, code r.l2 with
  | some a, some b => some ((a + 4 * r.o1) % 2 ^ 64, (b + 4 * r.o2) % 2 ^ 64)
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

/-- The phase table of `prog` at `lo`, if every label resolves. -/
def phTabOf (lo : Nat) (prog : Program) : Option PhTab := phTabBy (codeOf lo prog)

/-- The pc is in one of the ranges. -/
def inRs (rs : List (Nat × Nat)) (pc : Nat) : Bool := rs.any fun r => r.1 ≤ pc && pc < r.2

/-- **The phase index of a pc** in a table: its four bits. -/
def PhTab.ph (T : PhTab) (pc : Nat) : Nat :=
  (inRs T.p pc).toNat + 2 * (inRs T.l pc).toNat + 4 * (inRs T.n pc).toNat + 8 * (inRs T.t pc).toNat

/-- **The phase index of a pc** of `prog` at `lo` (`0` if a label of the
table is missing, and then `phasesOk` fails). -/
def phOf (lo : Nat) (prog : Program) : Nat → Nat :=
  match phTabOf lo prog with
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

/-- The sites' addresses in `prog` at `lo`, if every label resolves. -/
def sitesOf (lo : Nat) (prog : Program) (Λ : Scc.Sem.Layout) : Option (List Nat) := sitesBy (codeOf lo prog) Λ

/-- **The pcs off the sites** (none if a site label is missing, and then
`phasesOk` fails). -/
def okPcOf (lo : Nat) (prog : Program) (Λ : Scc.Sem.Layout) (pc : Nat) : Bool :=
  match sitesOf lo prog Λ with
  | some ss => !(ss.contains pc)
  | none => false

/-! ## The labels, keyed

The check resolves the labels of its rows, its phase table and its sites in
one table of the program's labels built in one pass (`labTab`: each label's
`key` with its address, in program order), each lookup comparing numbers
(`lookupK`); `codeT_eq`: the first match is `codeOf`'s. -/

/-- `labTab` for the code generator. -/
def labTabImpl : List Directive → Nat → List (Nat × Nat)
  | [], _ => []
  | d :: ds, base => match labelName d with
    | some m => (key m, base) :: labTabImpl ds (base + d.fakeSize)
    | none => labTabImpl ds (base + d.fakeSize)

/-- **The program's labels**: each label's `key` with its address, from the
code base `base`, in program order. -/
@[implemented_by labTabImpl] def labTab (ds : List Directive) : Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun d _ r base => match labelName d with
      | some m => (key m, base) :: r (base + d.fakeSize)
      | none => r (base + d.fakeSize)) ds

/-- `lookupK` for the code generator. -/
def lookupKImpl (k : Nat) (T : List (Nat × Nat)) : Option Nat := T.lookup k

/-- The address of the first entry of key `k`. -/
@[implemented_by lookupKImpl] def lookupK (k : Nat) (T : List (Nat × Nat)) : Option Nat :=
  List.rec (motive := fun _ => Option Nat) none (fun p _ r => if Nat.beq k p.1 then some p.2 else r) T

/-- **The code labels of `prog` at `lo`, keyed.** -/
def codeT (lo : Nat) (prog : Program) (l : String) : Option Nat := lookupK (key l) (labTab prog lo)

private theorem lookupK_labTab (l : String) : ∀ (prog : Program) (base : Nat),
    lookupK (key l) (labTab prog base) = codeOf base prog l
  | [], _ => rfl
  | d :: ds, base => by
    have ih := lookupK_labTab l ds (base + d.fakeSize)
    simp only [codeOf, labelAddr] at ih ⊢
    simp only [labTab] at ih ⊢
    cases hd : labelName d with
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

/-- **The keyed labels are `codeOf`'s.** -/
theorem codeT_eq (lo : Nat) (prog : Program) : codeT lo prog = codeOf lo prog := by
  funext l; exact lookupK_labTab l prog lo

/-! ## The phases at the runtime's pcs

The consumers of the phases (the take's and the TCB allocation's phase
facts, `Spike/Lib/Rt/A64RtTake.lean`, `A64RtTcb.lean`) need the phase index
at fixed pcs of the runtime: those facts follow from the order of the
runtime's labels, which no row check gives. `phPins` lists those pcs (a
label, a number of instructions after it) with their phase index, the same
in every output (the runtime's code is fixed); `marksOkT` checks them, and
that the sites are distinct. -/

/-- The pins in `scc_rt_stack_take` (`.L6_scc_rt_stack_take.<l>` plus `k`
instructions): not taken (bit 3) up to the take site, the lock (bit 1) held
from the swap's next pc (`.4_spin14` + 3) up to the release
(`.7_bump` + 5), the stack counter (bit 2) at `0` up to its add
(`.7_bump` + 11). -/
def takePins : List (String × Nat × Nat) :=
  ([("0_entry", 0, 12), ("1_cls5", 0, 12), ("1_cls5", 4, 12), ("3_clsdone7", 0, 12), ("3_clsdone7", 1, 12),
    ("3_clsdone7", 2, 12), ("3_clsdone7", 7, 12), ("3_clsdone7", 8, 12), ("3_clsdone7", 9, 12),
    ("3_clsdone7", 14, 12), ("3_clsdone7", 15, 12), ("3_clsdone7", 16, 12), ("4_spin14", 0, 12),
    ("4_spin14", 2, 12), ("4_spin14", 3, 14), ("5_locked15", 0, 14), ("5_locked15", 1, 14), ("5_locked15", 2, 14),
    ("7_bump", 0, 14), ("7_bump", 1, 14), ("7_bump", 2, 14), ("7_bump", 5, 14), ("7_bump", 6, 12),
    ("7_bump", 7, 12), ("7_bump", 8, 12), ("7_bump", 11, 12), ("7_bump", 12, 8), ("7_bump", 21, 8),
    ("9_ok", 0, 8), ("9_ok", 1, 8), ("9_ok", 2, 8), ("10_taken", 0, 8)].map
      fun (l, k, v) => (".L6_scc_rt_stack_take." ++ l, k, v))

/-- The pins in `scc_rt_alloc_tcb` (`.L3_scc_rt_alloc_tcb.<l>` plus `k`
instructions): `scc_rt_pinned_next` (bit 0) at `0` up to and including its
add (`.1_len` + 37). -/
def tcbPins : List (String × Nat × Nat) :=
  ([("0_entry", 0, 13), ("0_entry", 4, 13), ("1_len", 0, 13), ("1_len", 32, 13), ("1_len", 33, 13),
    ("1_len", 34, 13), ("1_len", 37, 13), ("1_len", 38, 12), ("1_len", 47, 12), ("3_ok", 0, 12), ("3_ok", 1, 12),
    ("3_ok", 2, 12), ("3_ok", 29, 12), ("3_ok", 30, 12)].map fun (l, k, v) => (".L3_scc_rt_alloc_tcb." ++ l, k, v))

/-- **The pinned phases**: `_start` in the initial phase (`13`: bits 0, 2
and 3, no lock), the take site not taken (`8`) and its next pc taken with
the same owned words (`0`), the two functions' entries, and `takePins`,
`tcbPins`. -/
def phPins : List (String × Nat × Nat) :=
  [("_start", 0, 13), ("scc_rt_take_site", 0, 8), ("scc_rt_take_site", 1, 0), ("scc_rt_stack_take", 0, 12),
    ("scc_rt_alloc_tcb", 0, 13)] ++ takePins ++ tcbPins

/-- **The marks' check** with a resolved table and sites: the sites
distinct, every pin's label resolved and its pc in its phase. -/
def marksOkT (code : String → Option Nat) (T : PhTab) (ss : List Nat) : Bool :=
  decide ss.Nodup && phPins.all fun p => match code p.1 with
    | some a => T.ph ((a + 4 * p.2.1) % 2 ^ 64) == p.2.2
    | none => false

/-! ## The check -/

/-- **A row's phase check** at its group's address `a`: every pc of the row
off the sites and in the row's entry phase, every instruction covered. -/
def rowPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (a : Nat) (b : OBlk) : Bool :=
  (List.range b.blk.length).all (fun j =>
    okPc ((a + 4 * (b.k + j)) % 2 ^ 64) && ph ((a + 4 * (b.k + j)) % 2 ^ 64) == ph ((a + 4 * b.k) % 2 ^ 64)) &&
  b.blk.all fun d => (classify d).isSome

/-- The rows' check with a resolved table and sites. -/
def phasesOkT (code : String → Option Nat) (T : PhTab) (ss : List Nat) (gs : List OGrp) : Bool :=
  gs.all fun g => match code g.l with
    | some a => g.bs.all (rowPhOk (fun pc => !(ss.contains pc)) T.ph a)
    | none => false

/-- The check with the labels resolved by `code`. -/
def phasesOkBy (code : String → Option Nat) (Λ : Scc.Sem.Layout) (gs : List OGrp) : Bool :=
  match phTabBy code, sitesBy code Λ with
  | some T, some ss => marksOkT code T ss && phasesOkT code T ss gs
  | _, _ => false

/-- **The phases** (component A6): the phase table and the sites resolve,
the sites are distinct and the pins in their phases (`marksOkT`), and every
row passes its phase check (`rowPhOk`); the labels resolved in one keyed
table (`codeT`). -/
def phasesOk (lo : Nat) (prog : Program) (Λ : Scc.Sem.Layout) (gs : List OGrp) : Bool :=
  phasesOkBy (codeT lo prog) Λ gs

/-- **A row of a checked table**: its group's label resolves, and the row
passes its phase check with `okPcOf` and `phOf`. -/
theorem rowPhOk_of_phasesOk {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {gs : List OGrp}
    (h : phasesOk lo prog Λ gs = true) {g : OGrp} (hg : g ∈ gs) {b : OBlk} (hb : b ∈ g.bs) :
    ∃ a, codeOf lo prog g.l = some a ∧ rowPhOk (okPcOf lo prog Λ) (phOf lo prog) a b = true := by
  unfold phasesOk at h
  rw [codeT_eq] at h
  unfold phasesOkBy at h
  split at h
  · next T ss hT hs =>
    have hg' := List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).2 g hg
    split at hg'
    · next a ha =>
      refine ⟨a, ha, ?_⟩
      have hr := List.all_eq_true.mp hg' b hb
      have hph : phOf lo prog = T.ph := by unfold phOf phTabOf; rw [hT]
      have hok : okPcOf lo prog Λ = fun pc => !(ss.contains pc) := by
        funext pc; unfold okPcOf sitesOf; rw [hs]
      rw [hph, hok]; exact hr
    · cases hg'
  · cases h

/-- **A row's pcs**: at `j < length` the pc `a + 4 (k + j)` is off the
sites and in the entry's phase; every instruction is covered. -/
theorem rowPhOk_spec {okPc : Nat → Bool} {ph : Nat → Nat} {a : Nat} {b : OBlk} (h : rowPhOk okPc ph a b = true) :
    (∀ j < b.blk.length, okPc ((a + 4 * (b.k + j)) % 2 ^ 64) = true ∧
      ph ((a + 4 * (b.k + j)) % 2 ^ 64) = ph ((a + 4 * b.k) % 2 ^ 64)) ∧
    ∀ d ∈ b.blk, (classify d).isSome = true := by
  simp only [rowPhOk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact ⟨fun j hj => h.1 j hj, h.2⟩

/-- **The sites are distinct.** -/
theorem sites_nodup_of_phasesOk {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {gs : List OGrp}
    (h : phasesOk lo prog Λ gs = true) : ∃ ss, sitesOf lo prog Λ = some ss ∧ ss.Nodup := by
  unfold phasesOk at h
  rw [codeT_eq] at h
  unfold phasesOkBy at h
  split at h
  · next T ss _ hs =>
    simp only [marksOkT, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨ss, hs, h.1.1⟩
  · cases h

/-- **A pin's pc in its phase**: its label resolves, and `phOf` at the pc
`k` instructions after it is the pin's. -/
theorem pin_of_phasesOk {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {gs : List OGrp}
    (h : phasesOk lo prog Λ gs = true) {l : String} {k v : Nat} (hp : (l, k, v) ∈ phPins) :
    ∃ a, codeOf lo prog l = some a ∧ phOf lo prog ((a + 4 * k) % 2 ^ 64) = v := by
  unfold phasesOk at h
  rw [codeT_eq] at h
  unfold phasesOkBy at h
  split at h
  · next T ss hT _ =>
    simp only [marksOkT, Bool.and_eq_true, List.all_eq_true] at h
    have hq := h.1.2 _ hp
    simp only at hq
    split at hq
    · next a ha =>
      have hph : phOf lo prog = T.ph := by unfold phOf phTabOf; rw [hT]
      exact ⟨a, ha, by rw [hph]; simpa using hq⟩
    · cases hq
  · cases h

end Scc.Cert.Rt.A64
