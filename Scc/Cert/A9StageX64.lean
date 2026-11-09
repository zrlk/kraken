import Scc.Cert.PlaceOKX64

/-!
# A9 by keyed lookups (x86-64)

`a9` (`Scc/Cert/PlaceOKX64.lean`) checks every lowered function's prologue,
body and phase facts. Written for the proofs, it finds a label at every
block (`blockAtB`, `sizesAt`, `labelGapB`: `after`/`labelIdx` by
`Directive`'s decidable equality, a string comparison per label of the
program), recomputes the function's frame (`frOf`: `List.eraseDups` on
strings) and its slots (`Frame.slotOff`: `List.find?` on strings), and reads
a code address at every label (`codeLabel`); in the kernel those scans are
most of `prog_placeOK_9`'s cost.

`a9fast` is the same check (`a9fast_eq`) written for the kernel:

* each label of the program is encoded once, into a number (`key`), in one
  table of its index and the cells after it (`tailTab`); a lookup compares
  numbers (`findT`, `findT_tailTab`);
* a body's blocks are read from the runs its labels delimit, each label
  found by key (`bodyInK`, `bodyBlksK`), and the body's blocks are computed
  once in the phase part (`fnPh1S`);
* the frame's registers are deduplicated by their keys (`dedupK`,
  `frOfK`), and a register's slot is found by its key (`kslots`, `rsK`);
* the code addresses come from the keyed table of `Scc/Cert/Rt/PhasesX64.lean`
  (`codeT`, `codeT_eq`).

A certificate proves `prog_placeOK_9` by `a9_of_fast` and the kernel's
evaluation of `a9fast`.
-/

namespace Scc.Cert.PlaceOK.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.LowerX64 (proL ovfL ovfBlk stDir addDirs retDirs tearDirs retL sizesAt blkAt bodyIn bodyBlks isAddChk frOf
  proInC proInS fnCodeOk getOp rsOf slotOff_state proLabs proPhOk blkLabs fnPh1 fnPhAll fnPhOk labC raL bodyPhOk)
open Spike.Lib.X64.Flow (prologueIn)
open Scc.Emit.X64 (Frame Item frameOf labelOf instRegs termRegs outWords i64 xr om mem)
open Scc.Cert.Rt.X64 (key key_inj memR memR_iff after after_eq cellRun cellRun_eq dropBytes blockAtB labelGapB
  labelIdx run labelGap lookupK codeT codeT_eq)

/-! ## The labels' table -/

/-- `tailTab` for the code generator. -/
def tailTabImpl : List (Directive × Nat) → Nat → List (Nat × Nat × List (Directive × Nat))
  | [], _ => []
  | (.label m, _) :: cs, i => (key m, i, cs) :: tailTabImpl cs (i + 1)
  | _ :: cs, i => tailTabImpl cs (i + 1)

/-- **The program's labels**: each label's `key` with its index (from `i`)
and the cells after it, in program order. -/
@[implemented_by tailTabImpl] def tailTab (cells : List (Directive × Nat)) :
    Nat → List (Nat × Nat × List (Directive × Nat)) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat × List (Directive × Nat))) (fun _ => [])
    (fun c cs r i => match c.1 with
      | .label m => (key m, i, cs) :: r (i + 1)
      | _ => r (i + 1)) cells

/-- `findT` for the code generator. -/
def findTImpl (k : Nat) : List (Nat × Nat × List (Directive × Nat)) → Option (Nat × List (Directive × Nat))
  | [] => none
  | p :: T => if k == p.1 then some p.2 else findTImpl k T

/-- The index and tail of the first entry of key `k`. -/
@[implemented_by findTImpl] def findT (k : Nat) (T : List (Nat × Nat × List (Directive × Nat))) :
    Option (Nat × List (Directive × Nat)) :=
  List.rec (motive := fun _ => Option (Nat × List (Directive × Nat))) none
    (fun p _ r => if Nat.beq k p.1 then some p.2 else r) T

theorem findT_tailTab (l : Label) : ∀ (cells : List (Directive × Nat)) (i : Nat),
    findT (key l) (tailTab cells i) = (labelIdx cells l).map fun n => (i + n, cells.drop (n + 1))
  | [], _ => rfl
  | (d, z) :: cs, i => by
    have ih := findT_tailTab l cs (i + 1)
    simp only [findT, tailTab] at ih ⊢
    cases d with
    | label m =>
      by_cases hm : m = l
      · subst hm; simp [Scc.Cert.Rt.X64.labelIdx, Nat.beq_refl]
      · have hk : Nat.beq (key l) (key m) = false := by
          cases h : Nat.beq (key l) (key m)
          · rfl
          · exact absurd (key_inj (Nat.eq_of_beq_eq_true h)).symm hm
        simp only [hk, ih, Scc.Cert.Rt.X64.labelIdx, Directive.label.injEq, hm, ite_false, Option.map_map,
          Function.comp_def, Bool.false_eq_true, List.drop_succ_cons]
        congr 1; funext n; simp only [Prod.mk.injEq, and_true]; omega
    | _ =>
      simp only [ih, Scc.Cert.Rt.X64.labelIdx, reduceCtorEq, ite_false, Option.map_map, Function.comp_def, List.drop_succ_cons]
      congr 1; funext n; simp only [Prod.mk.injEq, and_true]; omega

/-- **The run after a label, keyed.** -/
def runK (T : List (Nat × Nat × List (Directive × Nat))) (l : Label) : Option (List (Directive × Nat)) :=
  (findT (key l) T).map fun p => cellRun p.2

theorem runK_eq (cells : List (Directive × Nat)) (l : Label) :
    runK (tailTab cells 0) l = (after l cells).map cellRun := by
  unfold runK
  rw [findT_tailTab, after_eq]
  cases labelIdx cells l <;> rfl

/-! ## Blocks and gaps in a run -/

/-- `dropBytes` as `List.rec` (`dropBK_eq`). -/
@[implemented_by dropBytes] def dropBK (cs : List (Directive × Nat)) : Nat → Option (List (Directive × Nat)) :=
  List.rec (motive := fun _ => Nat → Option (List (Directive × Nat))) (fun n => if Nat.beq n 0 then some [] else none)
    (fun c cs r n => if Nat.beq n 0 then some (c :: cs) else if Nat.ble c.2 n then r (n - c.2) else none) cs

theorem dropBK_eq : ∀ (cs : List (Directive × Nat)) (n : Nat), dropBK cs n = dropBytes cs n
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | c :: cs, n + 1 => by
    have ih := dropBK_eq cs (n + 1 - c.2)
    simp only [dropBK] at ih
    cases hb : Nat.ble c.2 (n + 1) with
    | true =>
      have h : c.2 ≤ n + 1 := Nat.le_of_ble_eq_true hb
      simp only [dropBK, dropBytes, h, ite_true, hb, ← ih]
      rfl
    | false =>
      have h : ¬ c.2 ≤ n + 1 := fun h' => by rw [Nat.ble_eq_true_of_le h'] at hb; cases hb
      simp only [dropBK, dropBytes, h, ite_false, hb]
      rfl

/-- The sizes of the `n` cells `off` bytes into the run `r` (`sizesAt`). -/
def sizesR (r : List (Directive × Nat)) (off n : Nat) : List Nat :=
  match dropBK r off with
  | some r' => (r'.take n).map (·.2)
  | none => []

/-- `b` is the run `r` from `off` bytes on (a prefix; `blockAtB`). -/
def blkD (r : List (Directive × Nat)) (off : Nat) (b : List (Directive × Nat)) : Bool :=
  match dropBK r off with
  | some r' => decide (r'.take b.length = b)
  | none => false

/-- The directives `ds` are the run `r` from `off` bytes on (`blkAt`). -/
def blkAtR (r : List (Directive × Nat)) (off : Nat) (ds : List Directive) : Bool :=
  (sizesR r off ds.length).length == ds.length && blkD r off (ds.zip (sizesR r off ds.length))

/-- **`sizesAt` at a label, keyed**: the run after the label found once. -/
def szK (T : List (Nat × Nat × List (Directive × Nat))) (l : Label) : Nat → Nat → List Nat :=
  match runK T l with
  | some r => sizesR r
  | none => fun _ _ => []

theorem szK_eq (cells : List (Directive × Nat)) (l : Label) : szK (tailTab cells 0) l = sizesAt cells l := by
  funext off n
  unfold szK sizesAt sizesR
  rw [runK_eq]
  cases after l cells <;> simp [dropBK_eq] <;> rfl

/-- **`blockAtB` at a label, keyed.** -/
def blkBK (T : List (Nat × Nat × List (Directive × Nat))) (l : Label) : Nat → List (Directive × Nat) → Bool :=
  match runK T l with
  | some r => blkD r
  | none => fun _ _ => false

theorem blkBK_eq (cells : List (Directive × Nat)) (l : Label) : blkBK (tailTab cells 0) l = blockAtB cells l := by
  funext off b
  unfold blkBK blockAtB blkD
  rw [runK_eq]
  cases after l cells <;> simp [dropBK_eq] <;> rfl

/-- **`blkAt` at a label, keyed.** -/
def chkK (T : List (Nat × Nat × List (Directive × Nat))) (l : Label) : Nat → List Directive → Bool :=
  match runK T l with
  | some r => blkAtR r
  | none => fun _ _ => false

theorem chkK_eq (cells : List (Directive × Nat)) (l : Label) : chkK (tailTab cells 0) l = blkAt cells l := by
  funext off ds
  unfold chkK blkAt blkAtR sizesAt sizesR blockAtB blkD
  rw [runK_eq]
  cases after l cells <;> simp [dropBK_eq] <;> rfl

/-- **`labelGapB`, keyed.** -/
def labelGapBK (T : List (Nat × Nat × List (Directive × Nat))) (a b : Label) (off : Nat) : Bool :=
  match findT (key a) T, findT (key b) T with
  | some (i, t), some (j, _) =>
    j == i + 1 + (cellRun t).length && (t.take (cellRun t).length).all (fun c => !c.1.isLabel) &&
      ((t.take (cellRun t).length).map (·.2)).sum == off
  | _, _ => false

theorem labelGapBK_eq (cells : List (Directive × Nat)) (a b : Label) (off : Nat) :
    labelGapBK (tailTab cells 0) a b off = labelGapB cells a b off := by
  unfold labelGapBK labelGapB labelGap run
  rw [findT_tailTab, findT_tailTab]
  cases labelIdx cells a <;> cases labelIdx cells b <;> simp [cellRun_eq]

/-! ## The prologue -/

/-- **`prologueIn`, keyed.** -/
def prologueInK (T : List (Nat × Nat × List (Directive × Nat))) (fn sc entry : Label) (Z lim : Int64) (L : Label)
    (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) : Bool :=
  labelGapBK T fn sc 4 && blkBK T fn 0 Spike.Lib.X64.Flow.xHead && blkBK T sc 0 (Spike.Lib.X64.Flow.xLea Z zl) &&
  blkBK T sc zl [(Spike.Lib.X64.fsDir .r11 lim, zf)] && blkBK T sc (zl + zf) (Spike.Lib.X64.Flow.xCmp L z1 z2) &&
  blkBK T sc (zl + zf + z1 + z2) (Spike.Lib.X64.Flow.xFr Z zs ps) &&
  labelGapBK T sc entry (zl + zf + z1 + z2 + zs + Spike.Lib.X64.Flow.szSum ps)

theorem prologueInK_eq (cells : List (Directive × Nat)) (fn sc entry : Label) (Z lim : Int64) (L : Label)
    (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) :
    prologueInK (tailTab cells 0) fn sc entry Z lim L zl zf z1 z2 zs ps =
      prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps := by
  simp only [prologueInK, prologueIn, labelGapBK_eq, blkBK_eq]

/-- **`proInS`, keyed.** -/
def proInSK (T : List (Nat × Nat × List (Directive × Nat))) (fr : Frame) (fn entry : String) : Bool :=
  match szK T (labelOf fr.fn "chk") 0 5 with
  | [zl, zf, z1, z2, zs] =>
    prologueInK T fn (labelOf fr.fn "chk") entry (Int64.ofInt fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL fr) zl zf z1 z2 zs []
  | _ => false

theorem proInSK_eq (cells : List (Directive × Nat)) (fr : Frame) (fn entry : String) :
    proInSK (tailTab cells 0) fr fn entry = proInS cells fr fn entry := by
  simp only [proInSK, proInS, proInC, szK_eq, prologueInK_eq]
  rfl

/-! ## The frame and its slots, keyed

The frame (`frameOf`) removes repeated registers by `List.eraseDups` on
strings, and `Frame.slotOff` finds a register's slot by `List.find?`; each
string comparison costs the kernel both strings' UTF-8 encodings. `frOfK`
and `rsK` are the same functions (`frOfK_eq`, `rsK_eq`) comparing the
registers' `key`s. -/

/-- `frameOf`'s registers before removing repeats. -/
def regsAll (f : Scc.IR.Func) : List Scc.IR.Reg :=
  f.params ++ f.blocks.flatMap fun b => b.insts.flatMap instRegs ++ termRegs b.term

/-- `dedupK` for the code generator. -/
def dedupKImpl : List Scc.IR.Reg → List Nat → List Scc.IR.Reg → List Scc.IR.Reg
  | [], _, acc => acc
  | r :: rs, ks, acc =>
    if memR (key r) ks then dedupKImpl rs ks acc else dedupKImpl rs (key r :: ks) (acc ++ [r])

/-- **The first occurrences** of `rs`' registers after `acc`, `ks` the keys of
`acc`'s. -/
@[implemented_by dedupKImpl] def dedupK (rs : List Scc.IR.Reg) : List Nat → List Scc.IR.Reg → List Scc.IR.Reg :=
  List.rec (motive := fun _ => List Nat → List Scc.IR.Reg → List Scc.IR.Reg) (fun _ acc => acc)
    (fun r _ ih ks acc => if memR (key r) ks then ih ks acc else ih (key r :: ks) (acc ++ [r])) rs

theorem dedupK_eq : ∀ (rs : List Scc.IR.Reg) (ks : List Nat) (acc : List Scc.IR.Reg),
    (∀ k, k ∈ ks ↔ ∃ r ∈ acc, key r = k) →
    dedupK rs ks acc = List.eraseDupsBy.loop (· == ·) rs acc.reverse
  | [], _, acc, _ => by simp [dedupK, List.eraseDupsBy.loop]
  | r :: rs, ks, acc, h => by
    have hm : memR (key r) ks = acc.reverse.any (fun b => r == b) := by
      apply Bool.eq_iff_iff.mpr
      rw [memR_iff, h, List.any_eq_true]
      simp only [List.mem_reverse, beq_iff_eq]
      exact ⟨fun ⟨m, hm, hk⟩ => ⟨m, hm, (key_inj hk).symm⟩, fun ⟨m, hm, he⟩ => ⟨m, hm, by rw [he]⟩⟩
    have ih1 := dedupK_eq rs ks acc h
    have ih2 := dedupK_eq rs (key r :: ks) (acc ++ [r]) (by
      intro k
      simp only [List.mem_cons, h, List.mem_append, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | ⟨m, hm, rfl⟩)
        · exact ⟨r, .inr rfl, rfl⟩
        · exact ⟨m, .inl hm, rfl⟩
      · rintro ⟨m, hm | rfl, rfl⟩
        · exact .inr ⟨m, hm, rfl⟩
        · exact .inl rfl)
    simp only [dedupK] at ih1 ih2 ⊢
    rw [List.eraseDupsBy.loop, ← hm]
    cases hb : memR (key r) ks
    · simpa using ih2
    · simpa using ih1

theorem dedupK_nil (rs : List Scc.IR.Reg) : dedupK rs [] [] = rs.eraseDups := by
  rw [dedupK_eq _ _ _ (by simp)]; rfl

/-- **`frameOf`, keyed** (`frameOfK_eq`). -/
def frameOfK (areas : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func) : Frame :=
  let regs := dedupK (regsAll f) [] []
  let n := regs.length
  { fn := f.name, slots := regs.zipIdx, size := (8 * n + 15) / 16 * 16 + 8 * outWords areas f,
    inArea := ((areas.find? (·.1 == f.name)).map (·.2)).getD 0 }

theorem frameOfK_eq (areas : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func) : frameOfK areas f = frameOf areas f := by
  simp only [frameOfK, frameOf, regsAll, dedupK_nil]

/-- **`frOf`, keyed** (`frOfK_eq`). -/
def frOfK (ir : Scc.IR.Program) (f : Scc.IR.Func) : Frame :=
  { frameOfK (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length) f with maps := ir.growth.isSome }

theorem frOfK_eq (ir : Scc.IR.Program) (f : Scc.IR.Func) : frOfK ir f = frOf ir f := by
  simp only [frOfK, frOf, frameOfK_eq]

/-- **A frame's slots by key**: each register's `key` with its slot index. -/
def kslots (fr : Frame) : List (Nat × Nat) := fr.slots.map fun p => (key p.1, p.2)

/-- **`rsOf`, keyed**: `T` a frame's `kslots`. -/
def rsK (T : List (Nat × Nat)) (r : Scc.IR.Reg) : Option Int :=
  (lookupK (key r) T).map fun k => -(8 * ((k : Int) + 1))

theorem lookupK_kslots (r : Scc.IR.Reg) : ∀ slots : List (Scc.IR.Reg × Nat),
    lookupK (key r) (slots.map fun p => (key p.1, p.2)) = (slots.find? (·.1 == r)).map (·.2)
  | [] => rfl
  | p :: ps => by
    have ih := lookupK_kslots r ps
    by_cases h : p.1 = r
    · simp [lookupK, h]
    · have hk : Nat.beq (key r) (key p.1) = false := by
        cases hb : Nat.beq (key r) (key p.1)
        · rfl
        · exact absurd (key_inj (Nat.eq_of_beq_eq_true hb)).symm h
      have hf : (p :: ps).find? (·.1 == r) = ps.find? (·.1 == r) := by simp [h]
      rw [hf, ← ih, List.map_cons]
      show (if Nat.beq (key r) (key p.1) = true then _ else _) = _
      rw [hk]; rfl

theorem rsK_eq (fr : Frame) : rsK (kslots fr) = rsOf fr := by
  funext r
  simp only [rsK, kslots, lookupK_kslots, rsOf, Scc.Emit.X64.Frame.slotOff]
  cases fr.slots.find? (·.1 == r) with
  | none => rfl
  | some p => rfl

/-- **`getOp` at a slot map `so`**, its value only (`getOpS_eq`). -/
def getOpS (so : Scc.IR.Reg → Option Int) (t : Reg64) : Scc.IR.Operand → Option (List Item)
  | .reg x => (so x).map fun off => [.d (i64 (.mov (xr t) (om (mem .rbp off))))]
  | .imm v => some [.d (i64 (.mov (xr t) (.imm (.int64 v.toInt64))))]

theorem getOpS_eq (fr : Frame) (t : Reg64) (a : Scc.IR.Operand) : getOpS (rsOf fr) t a = (getOp fr t a).toOption := by
  cases a with
  | reg x =>
    cases hs : fr.slotOff x {} with
    | error e =>
      simp only [getOpS, rsOf, hs, getOp, Scc.Emit.X64.ld, Scc.Emit.X64.Frame.slot, bind, StateT.bind,
        Except.bind, Option.map_none]
      rfl
    | ok p =>
      obtain ⟨off, s'⟩ := p
      have h0 := slotOff_state hs {}
      simp only [getOpS, rsOf, h0, getOp, Scc.Lower.InvX64.ld_reg h0, Option.map_some]
      rfl
  | imm v => rfl

/-! ## The body

The body's blocks lie in the runs its labels delimit (P5): the entry
label's, then each fresh label's (`retL fr.fn n`). `bodyInG` and
`bodyBlksG` read them through a block check, sizes and a gap check per
label; keyed (`bodyInK`, `bodyBlksK`) each label's run is found in `T`. A
run holds at most two of the body's blocks (a store and the next add, or
the return's teardown), so the blocks are found from the run's start. -/

/-- **`bodyIn` at a block check `blk`, sizes `sz`, a gap check `gap` and a
slot map `so`** (`bodyIn cells fr` at `blkAt cells`, `sizesAt cells`,
`labelGapB cells` and `rsOf fr`, `bodyIn_eq_G`). -/
def bodyInG (blk : Label → Nat → List Directive → Bool) (sz : Label → Nat → Nat → List Nat)
    (gap : Label → Label → Nat → Bool) (fr : Frame) (so : Scc.IR.Reg → Option Int) :
    Label → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → Bool
  | L, n, o, [], [w] =>
    match getOpS so .rax w with
    | some lw =>
      blk L o (tearDirs lw) &&
        gap L (retL fr.fn n) (o + (sz L o (tearDirs lw).length).sum) &&
        blk (retL fr.fn n) 0 [i64 .ret]
    | none => false
  | L, n, o, .addChk d a b :: is, ws =>
    match getOpS so .rax a, getOpS so .rcx b, so d with
    | some la, some lb, some off =>
      blk L o (addDirs fr la lb) &&
        gap L (retL fr.fn n) (o + (sz L o (addDirs fr la lb).length).sum) &&
        blk (retL fr.fn n) 0 [stDir off] &&
        bodyInG blk sz gap fr so (retL fr.fn n) (n + 1) (sz (retL fr.fn n) 0 1).sum is ws
    | _, _, _ => false
  | _, _, _, _, _ => false

theorem bodyIn_eq_G (cells : List (Directive × Nat)) (fr : Frame) :
    bodyIn cells fr = bodyInG (blkAt cells) (sizesAt cells) (labelGapB cells) fr (rsOf fr) := by
  funext L n o is ws
  induction is generalizing L n o with
  | nil => cases ws with
    | nil => simp [bodyIn, bodyInG]
    | cons w ws => cases ws <;> simp only [bodyIn, bodyInG, getOpS_eq] <;> cases getOp fr .rax w <;> rfl
  | cons i is ih =>
    cases i <;> simp only [bodyIn, bodyInG, ih, getOpS_eq] <;>
      cases getOp fr .rax _ <;> cases getOp fr .rcx _ <;> cases rsOf fr _ <;> rfl

/-- **`bodyBlks` at sizes `sz` and a slot map `so`** (`bodyBlks_eq_G`). -/
def bodyBlksG (sz : Label → Nat → Nat → List Nat) (fr : Frame) (so : Scc.IR.Reg → Option Int) :
    Label → Nat → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → List (Nat × List (Directive × Nat))
  | L, n, e, o, [], [w] =>
    match getOpS so .rax w with
    | some lw => [(e + o, (tearDirs lw).zip (sz L o (tearDirs lw).length) ++
        [i64 .ret].zip (sz (retL fr.fn n) 0 1))]
    | none => []
  | L, n, e, o, .addChk d a b :: is, ws =>
    match getOpS so .rax a, getOpS so .rcx b, so d with
    | some la, some lb, some off =>
      (e + o, (addDirs fr la lb).zip (sz L o (addDirs fr la lb).length)) ::
        (e + o + (sz L o (addDirs fr la lb).length).sum,
          [stDir off].zip (sz (retL fr.fn n) 0 1)) ::
        bodyBlksG sz fr so (retL fr.fn n) (n + 1) (e + o + (sz L o (addDirs fr la lb).length).sum)
          (sz (retL fr.fn n) 0 1).sum is ws
    | _, _, _ => []
  | _, _, _, _, _, _ => []

theorem bodyBlks_eq_G (cells : List (Directive × Nat)) (fr : Frame) :
    bodyBlks cells fr = bodyBlksG (sizesAt cells) fr (rsOf fr) := by
  funext L n e o is ws
  induction is generalizing L n e o with
  | nil => cases ws with
    | nil => simp [bodyBlks, bodyBlksG]
    | cons w ws => cases ws <;> simp only [bodyBlks, bodyBlksG, getOpS_eq] <;> cases getOp fr .rax w <;> rfl
  | cons i is ih =>
    cases i <;> simp only [bodyBlks, bodyBlksG, ih, getOpS_eq] <;>
      cases getOp fr .rax _ <;> cases getOp fr .rcx _ <;> cases rsOf fr _ <;> rfl

/-- **`bodyIn`, keyed** (`bodyInK_eq`). -/
def bodyInK (T : List (Nat × Nat × List (Directive × Nat))) (fr : Frame) (so : Scc.IR.Reg → Option Int) :
    Label → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → Bool :=
  bodyInG (chkK T) (szK T) (labelGapBK T) fr so

theorem bodyInK_eq (cells : List (Directive × Nat)) (fr : Frame) :
    bodyInK (tailTab cells 0) fr (rsOf fr) = bodyIn cells fr := by
  have h1 : chkK (tailTab cells 0) = blkAt cells := funext (chkK_eq cells)
  have h2 : szK (tailTab cells 0) = sizesAt cells := funext (szK_eq cells)
  have h3 : labelGapBK (tailTab cells 0) = labelGapB cells := by
    funext a b off; exact labelGapBK_eq cells a b off
  rw [bodyInK, h1, h2, h3, bodyIn_eq_G]

/-- **`bodyBlks`, keyed** (`bodyBlksK_eq`). -/
def bodyBlksK (T : List (Nat × Nat × List (Directive × Nat))) (fr : Frame) (so : Scc.IR.Reg → Option Int) :
    Label → Nat → Nat → Nat → List Scc.IR.Inst → List Scc.IR.Operand → List (Nat × List (Directive × Nat)) :=
  bodyBlksG (szK T) fr so

theorem bodyBlksK_eq (cells : List (Directive × Nat)) (fr : Frame) :
    bodyBlksK (tailTab cells 0) fr (rsOf fr) = bodyBlks cells fr := by
  have h2 : szK (tailTab cells 0) = sizesAt cells := funext (szK_eq cells)
  rw [bodyBlksK, h2, bodyBlks_eq_G]

/-! ## The code part -/

/-- **`fnCodeOk`, keyed** at a labels' table `T`. -/
def fnCodeOkK (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) : Bool :=
  (Scc.Cert.Code1X64.starts ir 0 ir.funcs).all fun (f, n) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        let fr := frOfK ir f
        proInSK T fr f.name (labelOf f.name "entry") &&
          bodyInK T fr (rsK (kslots fr)) (labelOf f.name "entry") n 0 is [w] &&
          (is.isEmpty || blkBK T (ovfL fr) 0 ovfBlk)
      else true
    | _, _, _ => true

theorem fnCodeOkK_eq (cells : List (Directive × Nat)) (ir : Scc.IR.Program) :
    fnCodeOkK (tailTab cells 0) ir = fnCodeOk cells ir := by
  simp only [fnCodeOkK, fnCodeOk, frOfK_eq, rsK_eq, bodyInK_eq, proInSK_eq, blkBK_eq]
  rfl

/-! ## The phase part -/

/-- **`fnPh1` at the prologue's sizes `zs5` and the body's blocks `bs`**, the
body's blocks computed once (`fnPh1S_eq`). -/
def fnPh1S (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (zs5 : List Nat) (bs : List (Nat × List (Directive × Nat))) (fr : Frame) (fn : String)
    (is : List Scc.IR.Inst) (ra : Int64) : Bool :=
  match zs5 with
  | [zl, zf, z1, z2, zs] =>
    res fn && res (labelOf fr.fn "chk") && res (labelOf fn "entry") &&
      (proLabs (Int64.ofInt fr.size) (proL fr) zl z1 z2 zs []).all res &&
      bs.all (fun x => (blkLabs x.2).all res) &&
      proPhOk okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs [] &&
      (is.isEmpty || (res (ovfL fr) && (blkLabs ovfBlk).all res &&
        Spike.Lib.X64Consumer.blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 ovfBlk)) &&
      bs.all fun x =>
        Spike.Lib.X64Consumer.blkPh okPc ph (fun _ => false) lab (lab (labelOf fn "entry") + Int64.ofNat x.1) ra x.2
  | _ => false

theorem fnPh1S_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (fr : Frame) (fn : String) (n : Nat) (is : List Scc.IR.Inst)
    (w : Scc.IR.Operand) (ra : Int64) :
    fnPh1S okPc ph lab res (sizesAt cells (labelOf fr.fn "chk") 0 5)
      (bodyBlks cells fr (labelOf fn "entry") n 0 0 is [w]) fr fn is ra =
      fnPh1 okPc ph lab res cells fr fn n is w ra := by
  simp only [fnPh1S, fnPh1, bodyPhOk]
  rfl

/-- **`fnPhAll`, keyed** (the frames by `frOfK`, the slots by `rsK`, the
sizes by `szK`, the body's blocks by `bodyBlksK`). -/
def fnPhAllK (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  (Scc.Cert.Code1X64.starts ir 0 ir.funcs).all fun (f, n) =>
    match f.params, f.checkStack, f.blocks with
    | [], true, [⟨"entry", is, .ret [w]⟩] =>
      if is.all isAddChk then
        let fr := frOfK ir f
        fnPh1S okPc ph lab res (szK T (labelOf fr.fn "chk") 0 5)
          (bodyBlksK T fr (rsK (kslots fr)) (labelOf f.name "entry") n 0 0 is [w]) fr f.name is ra
      else true
    | _, _, _ => true

theorem fnPhAllK_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) (ra : Int64) :
    fnPhAllK okPc ph lab res (tailTab cells 0) ir ra = fnPhAll okPc ph lab res cells ir ra := by
  simp only [fnPhAllK, fnPhAll, frOfK_eq, rsK_eq, bodyBlksK_eq, szK_eq, fnPh1S_eq]
  rfl

/-- **`fnPhOk`, keyed**: the code labels by `codeT`, the blocks' sizes by `T`. -/
def fnPhOkK (T : List (Nat × Nat × List (Directive × Nat))) (lo : Nat) (Λ : Scc.Sem.Layout)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) : Bool :=
  match Scc.Cert.Rt.X64.phTabBy (codeT lo cells), Scc.Cert.Rt.X64.sitesBy (codeT lo cells) Λ with
  | some P, some ss =>
    (codeT lo cells raL).isSome &&
      fnPhAllK (fun pc => !ss.contains pc) P.ph (fun l => Int64.ofNat ((codeT lo cells l).getD 0))
        (fun l => (codeT lo cells l).isSome) T ir (Int64.ofNat ((codeT lo cells raL).getD 0))
  | _, _ => false

theorem fnPhOkK_eq (lo : Nat) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (ir : Scc.IR.Program) :
    fnPhOkK (tailTab cells 0) lo Λ cells ir = fnPhOk lo Λ cells ir := by
  simp only [fnPhOkK, fnPhAllK_eq, codeT_eq]
  rfl

/-! ## A9 -/

/-- **A9 for the kernel** (`a9fast_eq`). -/
def a9fast (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir =>
    let T := tailTab o.prog 0
    fnCodeOkK T ir && fnPhOkK T t.Λ.code.lo t.Λ o.prog ir
  | none => false

theorem a9fast_eq (o : Out) (t : Tables) : a9fast o t = a9 o t := by
  unfold a9fast a9
  cases o.place.ir with
  | some ir => simp only [fnCodeOkK_eq, fnPhOkK_eq]
  | none => rfl

/-- **A9 from `a9fast`** (a certificate's `prog_placeOK_9`). -/
theorem a9_of_fast {o : Out} {t : Tables} (h : a9fast o t = true) : a9 o t = true :=
  a9fast_eq o t ▸ h

end Scc.Cert.PlaceOK.X64
