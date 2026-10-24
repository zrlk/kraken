import Scc.Cert.Rt.LaysX64

/-!
# Every block of an emitted x64 program at its place

The x64 twin of `Scc/Cert/Rt/CodeA64.lean`, for code cells with the
assembler's sizes. A block's **place** is a label, a cell count and a byte
offset: the block is the run of cells starting `k` cells after the first
`label l` of the code, and those `k` cells take `off` bytes (`blockAt`,
`Scc/Cert/Rt/LayoutX64.lean`). A table groups the blocks by label (`Grp`:
the label, then each block with its count and offset); each block is its
cells with their sizes.

`blocksIn cells gs` checks a whole table at once, by one theorem per program
(`kernel_rfl`); `codeAt_of_blocksIn` gives Spike's sized `CodeAt` at
`label l + off` for every block of the table, in every state of any valid
layout of `cells` halting at their end (`Lays`, `endOf`,
`Scc/Cert/Rt/LaysX64.lean`), the canonical loader's thread included.

The check is the same single pass as AArch64's (`slices`): the groups in
program order, each label encoded once into a number (`key`), and the
blocks with their offsets compared with the program's cells by the
kernel's definitional equality as terms.
-/

namespace Scc.Cert.Rt.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **The blocks after a label**: each block's cells with the number of
cells before it in the run after the first `label l`, and their size. -/
structure Grp where
  l : Label
  bs : List (Nat × Nat × List (Directive × Nat))

/-! ## A cheaper check (as `CodeA64.lean`) -/

/-- `d` is `label l`, by its constructor first. -/
def isLab (l : Label) : Directive → Bool
  | .label m => m == l
  | _ => false

theorem isLab_iff {l : Label} {d : Directive} : isLab l d = true ↔ d = .label l := by
  cases d <;> simp [isLab]

/-- A cell that is not a label, by its constructor. -/
def notLab : Directive × Nat → Bool
  | (.label _, _) => false
  | _ => true

theorem notLab_eq (c : Directive × Nat) : notLab c = !c.1.isLabel := by
  obtain ⟨d, z⟩ := c; cases d <;> rfl

/-- `after` for the code generator. -/
def afterImpl (l : Label) : List (Directive × Nat) → Option (List (Directive × Nat))
  | [] => none
  | c :: cs => if isLab l c.1 then some cs else afterImpl l cs

/-- `cellRun` for the code generator. -/
def cellRunImpl : List (Directive × Nat) → List (Directive × Nat)
  | [] => []
  | c :: cs => if notLab c then c :: cellRunImpl cs else []

/-- The cells after the first `label l`. -/
@[implemented_by afterImpl] def after (l : Label) (cells : List (Directive × Nat)) :
    Option (List (Directive × Nat)) :=
  List.rec (motive := fun _ => Option (List (Directive × Nat))) none
    (fun c cs r => if isLab l c.1 then some cs else r) cells

/-- The non-label cells at the head of a list. -/
@[implemented_by cellRunImpl] def cellRun (cs : List (Directive × Nat)) : List (Directive × Nat) :=
  List.rec (motive := fun _ => List (Directive × Nat)) [] (fun c _ r => if notLab c then c :: r else []) cs

theorem after_eq (l : Label) : ∀ cells : List (Directive × Nat),
    after l cells = (labelIdx cells l).map fun n => cells.drop (n + 1)
  | [] => rfl
  | c :: cs => by
    by_cases h : c.1 = .label l
    · have h' : isLab l c.1 = true := isLab_iff.mpr h
      simp [after, labelIdx, h, isLab]
    · have h' : isLab l c.1 = false := by
        cases hb : isLab l c.1
        · rfl
        · exact absurd (isLab_iff.mp hb) h
      have ih := after_eq l cs
      simp only [after] at ih
      simp [after, labelIdx, h, h', ih, Option.map_map, Function.comp_def]

theorem cellRun_eq : ∀ cs : List (Directive × Nat), cellRun cs = cs.takeWhile (fun c => !c.1.isLabel)
  | [] => rfl
  | c :: cs => by
    have ih := cellRun_eq cs
    simp only [cellRun] at ih
    rw [List.takeWhile_cons, ← notLab_eq]
    cases h : notLab c <;> simp [cellRun, h, ih]

/-- `sizeSum` for the code generator. -/
def sizeSumImpl (cs : List (Directive × Nat)) : Nat := (cs.map (·.2)).sum

/-- The sizes of cells, as `List.rec`. -/
@[implemented_by sizeSumImpl] def sizeSum (cs : List (Directive × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ r => c.2 + r) cs

theorem sizeSum_eq : ∀ cs : List (Directive × Nat), sizeSum cs = (cs.map (·.2)).sum
  | [] => rfl
  | c :: cs => by
    have ih := sizeSum_eq cs
    simp only [sizeSum] at ih
    simp [sizeSum, ih]

/-- What a block's place names in the cells `t` after its label: the size
of the `k` cells before it and the `b.length` cells from there. -/
def slice (t : List (Directive × Nat)) (kb : Nat × Nat × List (Directive × Nat)) :
    Nat × List (Directive × Nat) :=
  (sizeSum ((cellRun t).take kb.1), ((cellRun t).drop kb.1).take kb.2.2.length)

/-- `blockAt` through `after`, `cellRun` and `slice`. -/
def blockAt' (cells : List (Directive × Nat)) (l : Label) (k off : Nat) (b : List (Directive × Nat)) : Bool :=
  match after l cells with
  | some t => (slice t (k, off, b)).1 == off && decide ((slice t (k, off, b)).2 = b)
  | none => false

theorem blockAt'_eq (cells : List (Directive × Nat)) (l : Label) (k off : Nat) (b : List (Directive × Nat)) :
    blockAt' cells l k off b = blockAt cells l k off b := by
  unfold blockAt' blockAt run
  rw [after_eq]
  cases labelIdx cells l <;> simp [slice, cellRun_eq, sizeSum_eq, List.map_take]

/-! ## One pass (as `CodeA64.lean`) -/

/-- `key` for the code generator. -/
def keyImpl (l : Label) : Nat :=
  l.toByteArray.data.toList.foldr (fun b r => r * 257 + (b.toNat + 1)) 0

/-- **A label as a number**: its bytes as digits base 257 (each byte plus
one, so no digit is zero). -/
@[implemented_by keyImpl] def key (l : Label) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun b _ r => r * 257 + (b.toNat + 1)) l.toByteArray.data.toList

private noncomputable def bkey (bs : List UInt8) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun b _ r => r * 257 + (b.toNat + 1)) bs

private theorem bkey_inj : ∀ {bs cs : List UInt8}, bkey bs = bkey cs → bs = cs
  | [], [], _ => rfl
  | [], c :: cs, h => by simp only [bkey] at h; omega
  | b :: bs, [], h => by simp only [bkey] at h; omega
  | b :: bs, c :: cs, h => by
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    simp only [bkey] at h
    have h1 : b.toNat = c.toNat := by omega
    have h2 : bkey bs = bkey cs := by simp only [bkey]; omega
    rw [UInt8.toNat_inj.mp h1, bkey_inj h2]

theorem key_inj {l m : Label} (h : key l = key m) : l = m := by
  have := bkey_inj (bs := l.toByteArray.data.toList) (cs := m.toByteArray.data.toList) h
  exact String.toByteArray_inj.mp (ByteArray.ext (Array.ext' this))

/-- `memR` for the code generator. -/
def memRImpl (n : Nat) (ns : List Nat) : Bool :=
  ns.any (Nat.beq n)

/-- `n` among `ns`, by `Nat.beq`. -/
@[implemented_by memRImpl] def memR (n : Nat) (ns : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ r => Nat.beq n x || r) ns

theorem memR_iff {n : Nat} : ∀ {ns : List Nat}, memR n ns = true ↔ n ∈ ns
  | [] => by simp [memR]
  | x :: xs => by
    have ih := @memR_iff n xs
    simp only [memR] at ih
    simp [memR, ih]

/-- The places' results in `t` of a group's blocks, before `rest`. -/
def grpSlicesImpl (t : List (Directive × Nat)) (bs : List (Nat × Nat × List (Directive × Nat)))
    (rest : List (Option (Nat × List (Directive × Nat)))) : List (Option (Nat × List (Directive × Nat))) :=
  bs.map (fun kb => some (slice t kb)) ++ rest

@[implemented_by grpSlicesImpl] def grpSlices (t : List (Directive × Nat))
    (bs : List (Nat × Nat × List (Directive × Nat))) (rest : List (Option (Nat × List (Directive × Nat)))) :
    List (Option (Nat × List (Directive × Nat))) :=
  List.rec (motive := fun _ => List (Option (Nat × List (Directive × Nat)))) rest
    (fun kb _ r => some (slice t kb) :: r) bs

theorem grpSlices_eq (t : List (Directive × Nat)) (rest : List (Option (Nat × List (Directive × Nat)))) :
    ∀ bs, grpSlices t bs rest = bs.map (fun kb => some (slice t kb)) ++ rest
  | [] => rfl
  | kb :: bs => by
    have ih := grpSlices_eq t rest bs
    simp only [grpSlices] at ih
    simp [grpSlices, ih]

/-- One step of `slices`: at a label, the next group's results if the keys
agree. -/
def slicesStep (c : Directive × Nat) (cs : List (Directive × Nat))
    (r : List Nat → List Grp → List (Option (Nat × List (Directive × Nat))))
    (seen : List Nat) (gs : List Grp) : List (Option (Nat × List (Directive × Nat))) :=
  match c.1 with
  | .label m =>
    match gs with
    | [] => r (key m :: seen) []
    | g :: gs' =>
      cond (Nat.beq (key m) (key g.l))
        (cond (memR (key g.l) seen) [none] (grpSlices cs g.bs (r (key m :: seen) gs')))
        (r (key m :: seen) (g :: gs'))
  | _ => r seen gs

/-- `slices` for the code generator. -/
def slicesImpl : List (Directive × Nat) → List Nat → List Grp → List (Option (Nat × List (Directive × Nat)))
  | [], _, gs => cond gs.isEmpty [] [none]
  | c :: cs, seen, gs => slicesStep c cs (slicesImpl cs) seen gs

/-- **One pass over the code**: what each block's place names, the groups
in program order, each at the first label of its name (none before it among
`seen`); `none` where that fails. -/
@[implemented_by slicesImpl]
def slices (cells : List (Directive × Nat)) : List Nat → List Grp → List (Option (Nat × List (Directive × Nat))) :=
  List.rec (motive := fun _ => List Nat → List Grp → List (Option (Nat × List (Directive × Nat))))
    (fun _ gs => cond gs.isEmpty [] [none]) (fun c cs r => slicesStep c cs r) cells

/-- `want` for the code generator. -/
def wantImpl (gs : List Grp) : List (Option (Nat × List (Directive × Nat))) :=
  gs.flatMap fun g => g.bs.map fun kb => some (kb.2.1, kb.2.2)

/-- The blocks of a table with their offsets, as `slices` should find them. -/
@[implemented_by wantImpl] def want (gs : List Grp) : List (Option (Nat × List (Directive × Nat))) :=
  List.rec (motive := fun _ => List (Option (Nat × List (Directive × Nat)))) []
    (fun g _ r => List.rec (motive := fun _ => List (Option (Nat × List (Directive × Nat)))) r
      (fun kb _ u => some (kb.2.1, kb.2.2) :: u) g.bs) gs

theorem want_eq : ∀ gs : List Grp, want gs = gs.flatMap fun g => g.bs.map fun kb => some (kb.2.1, kb.2.2)
  | [] => rfl
  | g :: gs => by
    have ih := want_eq gs
    simp only [want] at ih
    have hg : ∀ (bs : List (Nat × Nat × List (Directive × Nat))) (r : List (Option (Nat × List (Directive × Nat)))),
        List.rec (motive := fun _ => List (Option (Nat × List (Directive × Nat)))) r
          (fun kb _ u => some (kb.2.1, kb.2.2) :: u) bs = bs.map (fun kb => some (kb.2.1, kb.2.2)) ++ r := by
      intro bs r; induction bs with
      | nil => rfl
      | cons kb bs ihb => simp only [List.map_cons, List.cons_append, ← ihb]
    simp only [hg] at ih
    simp only [want, List.flatMap_cons, hg, ih]

theorem none_not_mem_want (gs : List Grp) : none ∉ want gs := by
  simp [want_eq]

/-- **Every block of the table at its place in `cells`**, the groups in
program order. A closed instance is checked by `kernel_rfl`; it is also
decidable. -/
def blocksIn (cells : List (Directive × Nat)) (gs : List Grp) : Prop :=
  slices cells [] gs = want gs

instance (cells : List (Directive × Nat)) (gs : List Grp) : Decidable (blocksIn cells gs) :=
  inferInstanceAs (Decidable (_ = _))

open Lean Elab Tactic Meta in
/-- `kernel_rfl` closes `a = b` (up to unfolding the goal's head) by `Eq.refl a`
without the elaborator's definitional equality check: the kernel checks it
when the declaration is added (as `Scc/Cert/Rt/CodeA64.lean`'s, which an x64
module does not import). -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let some (α, a, _) := (← whnfR (← g.getType)).eq? <|> (← whnf (← g.getType)).eq?
    | throwError "kernel_rfl: the goal is not an equation"
  g.assign (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α a)
  replaceMainGoal []

theorem after_cons (l : Label) (c : Directive × Nat) (cs : List (Directive × Nat)) :
    after l (c :: cs) = if isLab l c.1 then some cs else after l cs := rfl

theorem after_append {l : Label} : ∀ {pre : List (Directive × Nat)} (s : List (Directive × Nat)),
    (∀ c ∈ pre, c.1 ≠ .label l) → after l (pre ++ s) = after l s
  | [], _, _ => rfl
  | c :: pre, s, h => by
    have hd : isLab l c.1 = false := by
      cases hb : isLab l c.1
      · rfl
      · exact absurd (isLab_iff.mp hb) (h c List.mem_cons_self)
    rw [List.cons_append, after_cons, hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact after_append s (fun c' h' => h c' (List.mem_cons_of_mem _ h'))

theorem slices_sound : ∀ (s pre : List (Directive × Nat)) (seen : List Nat) (gs : List Grp),
    (∀ m, ∀ c ∈ pre, c.1 = .label m → key m ∈ seen) → slices s seen gs = want gs →
    ∀ g ∈ gs, ∃ t, after g.l (pre ++ s) = some t ∧ ∀ kb ∈ g.bs, slice t kb = (kb.2.1, kb.2.2)
  | [], _, _, gs, _, h, g, hg => by
    cases gs with
    | nil => simp at hg
    | cons g₀ gs' =>
      change [none] = want (g₀ :: gs') at h
      exact absurd (h ▸ List.mem_singleton_self _) (none_not_mem_want _)
  | c :: cs, pre, seen, gs, hpre, h, g, hg => by
    have ih := slices_sound cs (pre ++ [c])
    have happ : pre ++ [c] ++ cs = pre ++ c :: cs := by simp
    rw [← happ]
    change slicesStep c cs (slices cs) seen gs = want gs at h
    unfold slicesStep at h
    split at h
    next m hc =>
      have hpre' : ∀ m', ∀ c' ∈ pre ++ [c], c'.1 = .label m' → key m' ∈ key m :: seen := by
        intro m' c' hc' he
        rcases List.mem_append.mp hc' with hc' | hc'
        · exact List.mem_cons_of_mem _ (hpre m' c' hc' he)
        · simp only [List.mem_singleton] at hc'; subst hc'
          rw [hc, Directive.label.injEq] at he; simp [he]
      split at h
      next => simp at hg
      next g₀ gs' =>
        cases hk : Nat.beq (key m) (key g₀.l)
        · rw [hk, Bool.cond_false] at h
          exact ih _ _ hpre' h g hg
        · rw [hk, Bool.cond_true] at h
          have hm : m = g₀.l := key_inj (Nat.beq_eq_true_eq _ _ ▸ hk)
          cases hs : memR (key g₀.l) seen
          · rw [hs, Bool.cond_false, grpSlices_eq, want_eq, List.flatMap_cons, ← want_eq] at h
            obtain ⟨hb, hr⟩ := List.append_inj h (by simp)
            rcases List.mem_cons.mp hg with rfl | hg
            · refine ⟨cs, ?_, fun kb hkb => Option.some.inj (List.map_inj_left.mp hb kb hkb)⟩
              rw [List.append_assoc, List.singleton_append, after_append]
              · simp [after_cons, isLab, hc, hm]
              · intro c' hc' he
                have := memR_iff.mpr (hpre _ c' hc' he)
                rw [this] at hs; cases hs
            · exact ih _ _ hpre' hr g hg
          · rw [hs, Bool.cond_true] at h
            exact absurd (h ▸ List.mem_singleton_self _) (none_not_mem_want _)
    next hnl =>
      refine ih _ _ ?_ h g hg
      intro m' c' hc' he
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact hpre m' c' hc' he
      · simp only [List.mem_singleton] at hc'; subst hc'; exact absurd he (hnl m')

theorem blockAt_of_blocksIn {cells : List (Directive × Nat)} {gs : List Grp} (h : blocksIn cells gs) {g : Grp}
    (hg : g ∈ gs) {k off : Nat} {b : List (Directive × Nat)} (hb : (k, off, b) ∈ g.bs) :
    blockAt cells g.l k off b = true := by
  obtain ⟨t, ht, ha⟩ := slices_sound cells [] [] gs (by simp) h g hg
  rw [← blockAt'_eq]
  unfold blockAt'
  rw [List.nil_append] at ht
  rw [ht]
  simp [ha (k, off, b) hb]

/-- **The code of every block of a checked table**, at its label plus its
offset. -/
theorem codeAt_of_blocksIn {exe : _root_.Executable} [Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe cells kp) {gs : List Grp} (h : blocksIn cells gs)
    {g : Grp} (hg : g ∈ gs) {k off : Nat} {b : List (Directive × Nat)} (hb : (k, off, b) ∈ g.bs) :
    Spike.Lib.X64.CodeAt st ((_root_.Executable.labels exe).label g.l + Int64.ofNat off) b :=
  codeAt_blockAt_lays hp he hend (blockAt_of_blocksIn h hg hb)

/-! ## Places by byte offset

A node's pc is a label plus a byte offset (`lab l + 22`); `blockAtB` finds
the block's cell count itself, walking the run after the label until the
sizes reach the offset (`dropBytes`), and `labelGapB` takes the run's
length as the cell count of a label gap. -/

/-- The cells after the first `off` bytes of `cs` (whole cells), if `off`
falls on a cell boundary. -/
def dropBytes : List (Directive × Nat) → Nat → Option (List (Directive × Nat))
  | cs, 0 => some cs
  | [], _ + 1 => none
  | c :: cs, n + 1 => if c.2 ≤ n + 1 then dropBytes cs (n + 1 - c.2) else none

theorem dropBytes_sound : ∀ (cs : List (Directive × Nat)) (off : Nat) {r : List (Directive × Nat)},
    dropBytes cs off = some r → ∃ k, ((cs.take k).map (·.2)).sum = off ∧ cs.drop k = r
  | cs, 0, r, h => ⟨0, by simp, by simp [dropBytes] at h; simpa using h⟩
  | [], _ + 1, _, h => by simp [dropBytes] at h
  | c :: cs, n + 1, r, h => by
    unfold dropBytes at h
    split at h
    · obtain ⟨k, hk, hr⟩ := dropBytes_sound cs _ h
      exact ⟨k + 1, by simp only [List.take_succ_cons, List.map_cons, List.sum_cons, hk]; omega,
        by simpa using hr⟩
    · cases h

/-- **`b` is the block `off` bytes after the first `label l`** (`blockAt`
with the cell count found). -/
def blockAtB (cells : List (Directive × Nat)) (l : Label) (off : Nat) (b : List (Directive × Nat)) : Bool :=
  match after l cells with
  | some t =>
    match dropBytes (cellRun t) off with
    | some r => decide (r.take b.length = b)
    | none => false
  | none => false

theorem blockAt_of_blockAtB {cells : List (Directive × Nat)} {l : Label} {off : Nat} {b : List (Directive × Nat)}
    (h : blockAtB cells l off b = true) : ∃ k, blockAt cells l k off b = true := by
  unfold blockAtB at h
  rw [after_eq] at h
  cases hn : labelIdx cells l with
  | none => simp [hn] at h
  | some n =>
    simp only [hn, Option.map_some] at h
    split at h
    next r hr =>
      obtain ⟨k, hk, hd⟩ := dropBytes_sound _ _ hr
      refine ⟨k, ?_⟩
      rw [cellRun_eq] at hk hd
      simp only [blockAt, run, hn, Option.isSome_some, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      exact ⟨hk, by rw [hd]; simpa using h⟩
    next => cases h

/-- **`label b` is `off` bytes after `label a`**: the run after `a`, then
`b` (`labelGap` with the run's length as the cell count). -/
def labelGapB (cells : List (Directive × Nat)) (a b : Label) (off : Nat) : Bool :=
  labelGap cells a b (run cells a).length off

/-- A block found by `blockAtB` is code at `label l + off`. -/
theorem codeAt_blockAtB {exe : _root_.Executable} [Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe cells kp) {l : Label} {off : Nat} {b : List (Directive × Nat)}
    (h : blockAtB cells l off b = true) :
    Spike.Lib.X64.CodeAt st ((_root_.Executable.labels exe).label l + Int64.ofNat off) b := by
  obtain ⟨k, hk⟩ := blockAt_of_blockAtB h
  exact codeAt_blockAt_lays hp he hend hk

/-- A field of a Spike `Code` from `blockAtB`: the block's code at
`label l + off`, in every state of the executable. -/
theorem code_field {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)}
    {kp : Nat} (hp : Lays exe cells kp) {endPc : Int64} (hend : endPc = endOf exe cells kp)
    {l : Label} {off : Nat} {b : List (Directive × Nat)} (h : blockAtB cells l off b = true) {q : Int64}
    (e : (_root_.Executable.labels exe).label l + Int64.ofNat off = q) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s q b :=
  fun _ hs hn => e ▸ codeAt_blockAtB hp hs (hn.trans hend) h

/-- The distance between two labels from `labelGapB`. -/
theorem label_labelGapB {exe : _root_.Executable} [Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) {a b : Label} {off : Nat}
    (h : labelGapB cells a b off = true) :
    (_root_.Executable.labels exe).label b = (_root_.Executable.labels exe).label a + Int64.ofNat off :=
  label_labelGap_lays hp h

/-- info: [true, false, false, true] -/
#guard_msgs in
#eval [decide (blocksIn [(.label "a", 0), (.label "b", 0), (.label "a", 0)] [⟨"a", [(0, 0, [])]⟩, ⟨"b", [(0, 0, [])]⟩]),
  decide (blocksIn [(.label "a", 0), (.label "b", 0)] [⟨"b", [(0, 0, [])]⟩, ⟨"a", [(0, 0, [])]⟩]),
  decide (blocksIn [(.label "a", 0)] [⟨"c", []⟩]), key "ab" != key "ba"]

example : blocksIn [(.label "x", 0), (.label "y", 0)] [⟨"y", [(0, 0, [])]⟩] := by kernel_rfl

end Scc.Cert.Rt.X64
