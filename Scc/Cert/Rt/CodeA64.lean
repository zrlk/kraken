import Scc.Cert.Rt.LayoutA64

/-!
# Every block of an emitted AArch64 program at its place

The block data of a program (`scc --blocks`, `Spike/Lib/A64Hello.lean`)
names each block by its instructions; a function's proof needs each block
as code at its node's pc (`Spike.Lib.A64.CodeAt`). A block's **place**
is a label and an instruction count: the block is the run of instructions
starting `k` instructions after the first `label l` of the program
(`blockAt`, `Scc/Cert/Rt/LayoutA64.lean`). A table groups the blocks by
label (`Grp`: the label, then each block with its count).

`blocksIn prog gs` checks a whole table at once, by one theorem per program
(`kernel_rfl`); `codeAt_of_blocksIn` gives `CodeAt` at `label l + 4k`
for every block of the table, in every state of any valid layout of `prog`.
The table is meant to be emitted per program next to the `block_spec` lines
(the seed of `scc --cert`), its groups in program order.

The check is linear: one pass over the program (`slices`) taking the groups
in order, each label encoded once into a number (`key`), and the blocks
compared with the program's instructions by the kernel's definitional
equality as terms (`blocksIn` is an equation, not a `Bool`). For `hello.w`
(358 blocks, 238 labels, about 2000 instructions) the check takes 2.4 s and
0.5 GB over its file's tables; most of it is the labels' UTF-8 encoding.
-/

namespace Scc.Cert.Rt.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64

/-- **The blocks after a label**: each block's instructions with the number
of instructions before it in the run after the first `label l`. -/
structure Grp where
  l : Label
  bs : List (Nat × List Directive)

/-! ## A cheaper check

`blockAt` finds the label by its index (`labelIdx`, `List.drop`) with
`Directive`'s decidable equality, by structural recursion; in the kernel a
scan of a whole program that way costs about a second per block. `blockAt'`
is the same function (`blockAt'_eq`) written with `List.rec` (no `brecOn`):
it keeps the tail after the label (`after`) instead of its index, tests the
constructor first (`isLab`), and takes the run with `insRun`. -/

/-- `d` is `label l`, by its constructor first. -/
def isLab (l : Label) : Directive → Bool
  | .label m => m == l
  | _ => false

theorem isLab_iff {l : Label} {d : Directive} : isLab l d = true ↔ d = .label l := by
  cases d <;> simp [isLab]

/-- `after` for the code generator. -/
def afterImpl (l : Label) : List Directive → Option (List Directive)
  | [] => none
  | d :: ds => if isLab l d then some ds else afterImpl l ds

/-- `insRun` for the code generator. -/
def insRunImpl : List Directive → List Directive
  | [] => []
  | d :: ds => if isIns d then d :: insRunImpl ds else []

/-- The directives after the first `label l`. -/
@[implemented_by afterImpl] def after (l : Label) (prog : List Directive) : Option (List Directive) :=
  List.rec (motive := fun _ => Option (List Directive)) none (fun d ds r => if isLab l d then some ds else r) prog

/-- The instructions at the head of a list. -/
@[implemented_by insRunImpl] def insRun (ds : List Directive) : List Directive :=
  List.rec (motive := fun _ => List Directive) [] (fun d _ r => if isIns d then d :: r else []) ds

theorem after_eq (l : Label) : ∀ prog : List Directive,
    after l prog = (labelIdx prog l).map fun n => prog.drop (n + 1)
  | [] => rfl
  | d :: ds => by
    by_cases h : d = .label l
    · simp [after, labelIdx, h, isLab]
    · have h' : isLab l d = false := by
        cases hb : isLab l d
        · rfl
        · exact absurd (isLab_iff.mp hb) h
      have ih := after_eq l ds
      simp only [after] at ih
      simp [after, labelIdx, h, h', ih, Option.map_map, Function.comp_def]

theorem insRun_eq : ∀ ds : List Directive, insRun ds = ds.takeWhile isIns
  | [] => rfl
  | d :: ds => by
    have ih := insRun_eq ds
    simp only [insRun] at ih
    cases h : isIns d <;> simp [insRun, h, ih]

/-- `blockAt` through `after` and `insRun`. -/
def blockAt' (prog : List Directive) (l : Label) (k : Nat) (b : List Directive) : Bool :=
  match after l prog with
  | some t => decide ((((insRun t).drop k).take b.length) = b)
  | none => false

theorem blockAt'_eq (prog : List Directive) (l : Label) (k : Nat) (b : List Directive) :
    blockAt' prog l k b = blockAt prog l k b := by
  unfold blockAt' blockAt run
  rw [after_eq]
  cases labelIdx prog l <;> simp [insRun_eq]

/-! ## Tables -/

/-! ## One pass

A label's string comparison costs the kernel its UTF-8 encoding
(`String.ofList`, `List.utf8Encode`) byte by byte; a search from the
program's start per group pays it for every label before the group's. The
check is instead one pass over the program (`walk`) taking the groups in
program order: each label of the program is encoded once, into a number
(`key`, injective: its bytes as digits base 257), and the rest are
comparisons of numbers (`Nat.beq`, by GMP in the kernel). A group's label
must be the first of its name (`label` is the first occurrence), so the pass
keeps the keys of the labels before (`seen`). -/

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

/-- The run a block names in the directives `t` after its label: `kb.2.length`
instructions after the first `kb.1`. -/
def slice (t : List Directive) (kb : Nat × List Directive) : List Directive :=
  ((insRun t).drop kb.1).take kb.2.length

/-- `grpSlices` for the code generator. -/
def grpSlicesImpl (t : List Directive) (bs : List (Nat × List Directive)) (rest : List (Option (List Directive))) :
    List (Option (List Directive)) :=
  bs.map (fun kb => some (slice t kb)) ++ rest

/-- The runs a group's blocks name in `t`, before `rest`. -/
@[implemented_by grpSlicesImpl] def grpSlices (t : List Directive) (bs : List (Nat × List Directive))
    (rest : List (Option (List Directive))) : List (Option (List Directive)) :=
  List.rec (motive := fun _ => List (Option (List Directive))) rest (fun kb _ r => some (slice t kb) :: r) bs

theorem grpSlices_eq (t : List Directive) (rest : List (Option (List Directive))) :
    ∀ bs, grpSlices t bs rest = bs.map (fun kb => some (slice t kb)) ++ rest
  | [] => rfl
  | kb :: bs => by
    have ih := grpSlices_eq t rest bs
    simp only [grpSlices] at ih
    simp [grpSlices, ih]

/-- One step of `slices`: at a label, the next group's runs if the keys
agree. -/
def slicesStep (d : Directive) (ds : List Directive) (r : List Nat → List Grp → List (Option (List Directive)))
    (seen : List Nat) (gs : List Grp) : List (Option (List Directive)) :=
  match d with
  | .label m =>
    match gs with
    | [] => r (key m :: seen) []
    | g :: gs' =>
      cond (Nat.beq (key m) (key g.l))
        (cond (memR (key g.l) seen) [none] (grpSlices ds g.bs (r (key m :: seen) gs')))
        (r (key m :: seen) (g :: gs'))
  | _ => r seen gs

/-- `slices` for the code generator. -/
def slicesImpl : List Directive → List Nat → List Grp → List (Option (List Directive))
  | [], _, gs => cond gs.isEmpty [] [none]
  | d :: ds, seen, gs => slicesStep d ds (slicesImpl ds) seen gs

/-- **One pass over the program**: the run each block of the groups names,
the groups in program order, each at the first label of its name (none
before it among `seen`); `none` where that fails. -/
@[implemented_by slicesImpl]
def slices (prog : List Directive) : List Nat → List Grp → List (Option (List Directive)) :=
  List.rec (motive := fun _ => List Nat → List Grp → List (Option (List Directive)))
    (fun _ gs => cond gs.isEmpty [] [none]) (fun d ds r => slicesStep d ds r) prog

/-- `want` for the code generator. -/
def wantImpl (gs : List Grp) : List (Option (List Directive)) :=
  gs.flatMap fun g => g.bs.map fun kb => some kb.2

/-- The blocks of a table, as `slices` should find them. -/
@[implemented_by wantImpl] def want (gs : List Grp) : List (Option (List Directive)) :=
  List.rec (motive := fun _ => List (Option (List Directive))) []
    (fun g _ r => List.rec (motive := fun _ => List (Option (List Directive))) r (fun kb _ u => some kb.2 :: u) g.bs) gs

theorem want_eq : ∀ gs : List Grp, want gs = gs.flatMap fun g => g.bs.map fun kb => some kb.2
  | [] => rfl
  | g :: gs => by
    have ih := want_eq gs
    simp only [want] at ih
    have hg : ∀ (bs : List (Nat × List Directive)) (r : List (Option (List Directive))),
        List.rec (motive := fun _ => List (Option (List Directive))) r (fun kb _ u => some kb.2 :: u) bs =
          bs.map (fun kb => some kb.2) ++ r := by
      intro bs r; induction bs with
      | nil => rfl
      | cons kb bs ihb => simp only [List.map_cons, List.cons_append, ← ihb]
    simp only [hg] at ih
    simp only [want, List.flatMap_cons, hg, ih]

theorem none_not_mem_want (gs : List Grp) : none ∉ want gs := by
  simp [want_eq]

/-- **Every block of the table at its place in `prog`**, the groups in
program order: what one pass finds is the table's blocks. A closed instance
is checked by `kernel_rfl` (the kernel's definitional equality compares the
program's instructions with the table's as terms, without evaluating
`Directive`'s decidable equality); it is also decidable. -/
def blocksIn (prog : List Directive) (gs : List Grp) : Prop :=
  slices prog [] gs = want gs

instance (prog : List Directive) (gs : List Grp) : Decidable (blocksIn prog gs) :=
  inferInstanceAs (Decidable (_ = _))

open Lean Elab Tactic Meta in
/-- `kernel_rfl` closes `a = b` (up to unfolding the goal's head) by `Eq.refl a`
without the elaborator's definitional equality check: the kernel checks it
when the declaration is added. For `blocksIn` of a whole program, where the
elaborator's check would cost more than the kernel's. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let some (α, a, _) := (← whnfR (← g.getType)).eq? <|> (← whnf (← g.getType)).eq?
    | throwError "kernel_rfl: the goal is not an equation"
  g.assign (mkApp2 (mkConst ``Eq.refl [← getLevel α]) α a)
  replaceMainGoal []

/-- info: [true, false, false, true] -/
#guard_msgs in
#eval [decide (blocksIn [.label "a", .label "b", .label "a"] [⟨"a", [(0, [])]⟩, ⟨"b", [(0, [])]⟩]),
  decide (blocksIn [.label "a", .label "b"] [⟨"b", [(0, [])]⟩, ⟨"a", [(0, [])]⟩]),
  decide (blocksIn [.label "a"] [⟨"c", []⟩]), key "ab" != key "ba"]

example : blocksIn [.label "x", .label "y"] [⟨"y", [(0, [])]⟩] := by kernel_rfl

theorem after_cons (l : Label) (d : Directive) (ds : List Directive) :
    after l (d :: ds) = if isLab l d then some ds else after l ds := rfl

theorem after_append {l : Label} : ∀ {pre : List Directive} (s : List Directive),
    Directive.label l ∉ pre → after l (pre ++ s) = after l s
  | [], _, _ => rfl
  | d :: pre, s, h => by
    have hd : isLab l d = false := by
      cases hb : isLab l d
      · rfl
      · exact absurd (isLab_iff.mp hb ▸ List.mem_cons_self) h
    rw [List.cons_append, after_cons, hd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact after_append s (fun h' => h (List.mem_cons_of_mem _ h'))

theorem slices_sound : ∀ (s pre : List Directive) (seen : List Nat) (gs : List Grp),
    (∀ m, Directive.label m ∈ pre → key m ∈ seen) → slices s seen gs = want gs →
    ∀ g ∈ gs, ∃ t, after g.l (pre ++ s) = some t ∧ ∀ kb ∈ g.bs, slice t kb = kb.2
  | [], _, _, gs, _, h, g, hg => by
    cases gs with
    | nil => simp at hg
    | cons g₀ gs' =>
      change [none] = want (g₀ :: gs') at h
      exact absurd (h ▸ List.mem_singleton_self _) (none_not_mem_want _)
  | d :: ds, pre, seen, gs, hpre, h, g, hg => by
    have ih := slices_sound ds (pre ++ [d])
    have happ : pre ++ [d] ++ ds = pre ++ d :: ds := by simp
    rw [← happ]
    change slicesStep d ds (slices ds) seen gs = want gs at h
    unfold slicesStep at h
    split at h
    next m =>
      have hpre' : ∀ m', Directive.label m' ∈ pre ++ [.label m] → key m' ∈ key m :: seen := by
        intro m' hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact List.mem_cons_of_mem _ (hpre m' hm')
        · simp only [List.mem_singleton, Directive.label.injEq] at hm'; simp [hm']
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
            · refine ⟨ds, ?_, fun kb hkb => Option.some.inj (List.map_inj_left.mp hb kb hkb)⟩
              rw [List.append_assoc, List.singleton_append, hm, after_append]
              · simp [after_cons, isLab]
              · intro hl
                have := memR_iff.mpr (hpre _ hl)
                simp [this] at hs
            · exact ih _ _ hpre' hr g hg
          · rw [hs, Bool.cond_true] at h
            exact absurd (h ▸ List.mem_singleton_self _) (none_not_mem_want _)
    next hnl =>
      refine ih _ _ ?_ h g hg
      intro m' hm'
      rcases List.mem_append.mp hm' with hm' | hm'
      · exact hpre m' hm'
      · simp only [List.mem_singleton] at hm'; exact absurd hm'.symm (hnl m')

theorem blockAt_of_blocksIn {prog : List Directive} {gs : List Grp} (h : blocksIn prog gs) {g : Grp}
    (hg : g ∈ gs) {k : Nat} {b : List Directive} (hb : (k, b) ∈ g.bs) : blockAt prog g.l k b = true := by
  obtain ⟨t, ht, ha⟩ := slices_sound prog [] [] gs (by simp) h g hg
  rw [← blockAt'_eq]
  unfold blockAt'
  rw [List.nil_append] at ht
  rw [ht]
  exact decide_eq_true (ha (k, b) hb)

/-- **The code of every block of a checked table**, at its label plus four
bytes per instruction before it. -/
theorem codeAt_of_blocksIn {exe : Executable} [Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {st : State} (he : st.exe = exe)
    (hend : st.endPc = endOf exe prog) {gs : List Grp} (h : blocksIn prog gs)
    {g : Grp} (hg : g ∈ gs) {k : Nat} {b : List Directive} (hb : (k, b) ∈ g.bs) :
    CodeAt st ((_root_.Executable.labels exe).label g.l + Int64.ofNat (4 * k)) b :=
  codeAt_blockAt hp he hend (blockAt_of_blocksIn h hg hb)

end Scc.Cert.Rt.A64
