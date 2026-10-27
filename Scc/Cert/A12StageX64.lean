import Scc.Cert.A9StageX64

/-!
# A12 by keyed lookups (x86-64)

`a12` (`Scc/Cert/PlaceOKX64.lean`) checks every stack-checked function's
code (`Scc.Cert.Code1X64.fnCode1Ok`) and phase facts
(`Scc.Cert.Ph1X64.fnPh1Ok`). Written for the proofs, it finds a label at
every segment and at every label inside one (`segIn`, `labelsAt`:
`labelIdx` by `Directive`'s decidable equality, a string comparison per
label of the program), recomputes the function's frame by comparing strings
(`frOf`) and its slots (`rsOf`), and resolves a code address at every label
read (`codeLabel`).

`a12fast` is the same check (`a12fast_eq`) on A9's keyed tables
(`Scc/Cert/A9StageX64.lean`):

* the labels by `tailTab`/`findT` (`segInK`, `labelsAtK`, `segCellsK`,
  `szK`, `prologueInK`, `blkBK`);
* the frames by `frOfK`, the slots by `rsK`;
* the code addresses by `codeT` (`Scc/Cert/Rt/PhasesX64.lean`).

A certificate decides `a9fast`, A12's code part (`a12code`) and its phase
part (`a12ph`) in three declarations; `a12_of_split` gives
`prog_placeOK_12`. The kernel's memory is held per declaration, so the peak
is the largest of the three rather than their sum.
-/

namespace Scc.Cert.PlaceOK.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.LowerX64 (proL ovfL ovfBlk stkHead sizesAt frOf rsOf proPhOk proLabs blkLabs labC raL)
open Spike.Lib.X64.Flow (prologueIn)
open Scc.Emit.X64 (Frame Item labelOf directives)
open Scc.Cert.Rt.X64 (key labelIdx after after_eq blockAtB codeT codeT_eq phTabBy sitesBy PhTab labTab lookupK)
open Scc.Cert.Code1X64 (labelsAt segIn blocksOk blockItems spills hasAddChk needOk1 chkL fnOk1 fnCode1Ok starts)
open Scc.Cert.Ph1X64 (segCells runs runPh blocksPh fnPhF fnPhAll1 fnPh1Ok)

/-! ## The code part -/

/-- **`labelsAt`, keyed.** -/
def labelsAtK (T : List (Nat × Nat × List (Directive × Nat))) : Nat → List Directive → Bool
  | _, [] => true
  | j, .label l :: ds => ((findT (key l) T).map (·.1) == some j) && labelsAtK T (j + 1) ds
  | j, _ :: ds => labelsAtK T (j + 1) ds

theorem labelsAtK_eq (cells : List (Directive × Nat)) :
    ∀ (j : Nat) (ds : List Directive), labelsAtK (tailTab cells 0) j ds = labelsAt cells j ds
  | _, [] => rfl
  | j, .label l :: ds => by
    simp only [labelsAtK, labelsAt, labelsAtK_eq cells (j + 1) ds, findT_tailTab]
    cases labelIdx cells l <;> simp
  | j, .instr _ :: ds => by simp only [labelsAtK, labelsAt, labelsAtK_eq cells (j + 1) ds]
  | j, .byteArray _ :: ds => by simp only [labelsAtK, labelsAt, labelsAtK_eq cells (j + 1) ds]

/-- **`segIn`, keyed**: the cells after the label found once. -/
def segInK (T : List (Nat × Nat × List (Directive × Nat))) (l : Label) (ds : List Directive) : Bool :=
  match findT (key l) T with
  | some (i, t) => decide ((t.take ds.length).map (·.1) = ds) && labelsAtK T (i + 1) ds
  | none => false

theorem segInK_eq (cells : List (Directive × Nat)) (l : Label) (ds : List Directive) :
    segInK (tailTab cells 0) l ds = segIn cells l ds := by
  unfold segInK segIn
  rw [findT_tailTab]
  cases labelIdx cells l <;> simp [labelsAtK_eq]

/-- **`blocksOk`, keyed.** -/
def blocksOkK (T : List (Nat × Nat × List (Directive × Nat))) (fr : Frame) :
    Nat → List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) → Bool
  | _, [] => true
  | n, (b, ms) :: bs =>
    match blockItems fr n b ms with
    | .ok (code, n') => segInK T (labelOf fr.fn b.label) (directives code) && blocksOkK T fr n' bs
    | .error _ => false

theorem blocksOkK_eq (cells : List (Directive × Nat)) (fr : Frame) :
    ∀ (n : Nat) (bs : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))),
      blocksOkK (tailTab cells 0) fr n bs = blocksOk cells fr n bs
  | _, [] => rfl
  | n, (b, ms) :: bs => by
    simp only [blocksOkK, blocksOk]
    cases blockItems fr n b ms with
    | error => rfl
    | ok r => simp only [segInK_eq, blocksOkK_eq cells fr _ bs]

/-- **`spills`, keyed**: the slots by `rsK`. -/
def spillsK (so : Scc.IR.Reg → Option Int) (ps : List Scc.IR.Reg) (zs : List Nat) :
    Option (List (Reg64 × Int64 × Nat)) :=
  if ps.length ≤ Scc.Emit.X64.argRegs.length && zs.length == ps.length then
    ((ps.zip Scc.Emit.X64.argRegs).zip zs).mapM fun ((p, r), z) => (so p).map fun o => (r, Int64.ofInt o, z)
  else none

theorem spillsK_eq (fr : Frame) (ps : List Scc.IR.Reg) (zs : List Nat) :
    spillsK (rsOf fr) ps zs = spills fr ps zs := rfl

/-- **`fnOk1`, keyed** (the frame by `frOfK`, the slots by `rsK`, the
sizes by `szK`, the blocks by `blkBK`, the prologue by `prologueInK`). -/
def fnOk1K (T : List (Nat × Nat × List (Directive × Nat))) (tbl : List NeedX64.Row) (ir : Scc.IR.Program)
    (n : Nat) (f : Scc.IR.Func) : Bool :=
  let fr := frOfK ir f
  match f.blocks, szK T (chkL f) 0 (5 + f.params.length) with
  | b0 :: _, zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spillsK (rsK (kslots fr)) f.params zps with
    | some ps =>
      ir.growth.isSome &&
      prologueInK T f.name (chkL f) (labelOf f.name b0.label) (Int64.ofInt fr.size)
        (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps &&
      decide (fr.size < 2 ^ 31) && decide (fr.size % 16 = 0) &&
      blocksOkK T fr n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (ir.abortFn == "scc_rt_abort" && blkBK T (ovfL fr) 0 ovfBlk)) &&
      needOk1 tbl f.name fr.size f &&
      blkBK T (proL fr) 0 stkHead
    | none => false
  | _, _ => false

theorem fnOk1K_eq (cells : List (Directive × Nat)) (tbl : List NeedX64.Row) (ir : Scc.IR.Program)
    (n : Nat) (f : Scc.IR.Func) : fnOk1K (tailTab cells 0) tbl ir n f = fnOk1 cells tbl ir n f := by
  simp only [fnOk1K, fnOk1, frOfK_eq, rsK_eq, spillsK_eq, szK_eq, prologueInK_eq, blocksOkK_eq, blkBK_eq]
  rfl

/-- **`fnCode1Ok`, keyed** at a labels' table `T`. -/
def fnCode1OkK (T : List (Nat × Nat × List (Directive × Nat))) (tbl : List NeedX64.Row) (ir : Scc.IR.Program) :
    Bool :=
  (starts ir 0 ir.funcs).all fun (f, n) => !f.checkStack || fnOk1K T tbl ir n f

theorem fnCode1OkK_eq (cells : List (Directive × Nat)) (tbl : List NeedX64.Row) (ir : Scc.IR.Program) :
    fnCode1OkK (tailTab cells 0) tbl ir = fnCode1Ok cells tbl ir := by
  simp only [fnCode1OkK, fnCode1Ok, fnOk1K_eq]

/-! ## The phase part -/

/-- **`segCells`, keyed.** -/
def segCellsK (T : List (Nat × Nat × List (Directive × Nat))) (l : Label) (n : Nat) : List (Directive × Nat) :=
  match findT (key l) T with
  | some (_, t) => t.take n
  | none => []

theorem segCellsK_eq (cells : List (Directive × Nat)) (l : Label) (n : Nat) :
    segCellsK (tailTab cells 0) l n = segCells cells l n := by
  unfold segCellsK segCells
  rw [findT_tailTab, after_eq]
  cases labelIdx cells l <;> rfl

/-- **`blocksPh`, keyed.** -/
def blocksPhK (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (fr : Frame) (ra : Int64) :
    Nat → List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) → Bool
  | _, [] => true
  | n, (b, ms) :: bs =>
    match blockItems fr n b ms with
    | .ok (code, n') =>
      (runs (labelOf fr.fn b.label)
          (segCellsK T (labelOf fr.fn b.label) (directives code).length)).all (fun r =>
            runPh okPc ph lab res ra r && ph (lab r.1).toBitVec.toNat == ph ra.toBitVec.toNat) &&
        blocksPhK okPc ph lab res T fr ra n' bs
    | .error _ => false

theorem blocksPhK_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (fr : Frame) (ra : Int64) :
    ∀ (n : Nat) (bs : List (Scc.IR.Block × List (Option Scc.IR.StackMap.Entry))),
      blocksPhK okPc ph lab res (tailTab cells 0) fr ra n bs = blocksPh okPc ph lab res cells fr ra n bs
  | _, [] => rfl
  | n, (b, ms) :: bs => by
    simp only [blocksPhK, blocksPh]
    cases blockItems fr n b ms with
    | error => rfl
    | ok r => simp only [segCellsK_eq, blocksPhK_eq okPc ph lab res cells fr ra _ bs]

/-- **`fnPhF`, keyed.** -/
def fnPhFK (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (n : Nat) (f : Scc.IR.Func)
    (ra : Int64) : Bool :=
  let fr := frOfK ir f
  match szK T (chkL f) 0 (5 + f.params.length) with
  | zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spillsK (rsK (kslots fr)) f.params zps with
    | some ps =>
      res f.name && res (chkL f) &&
      (proLabs (Int64.ofInt fr.size) (proL fr) zl z1 z2 zs ps).all res &&
      proPhOk okPc ph lab f.name (chkL f) (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs ps &&
      blocksPhK okPc ph lab res T fr ra n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (res (ovfL fr) && (blkLabs ovfBlk).all res &&
        Spike.Lib.X64Consumer.blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 ovfBlk))
    | none => false
  | _ => false

theorem fnPhFK_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) (n : Nat) (f : Scc.IR.Func) (ra : Int64) :
    fnPhFK okPc ph lab res (tailTab cells 0) ir n f ra = fnPhF okPc ph lab res cells ir n f ra := by
  simp only [fnPhFK, fnPhF, frOfK_eq, rsK_eq, spillsK_eq, szK_eq, blocksPhK_eq]
  rfl

/-- **`fnPhAll1`, keyed.** -/
def fnPhAll1K (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  (starts ir 0 ir.funcs).all fun (f, n) => !f.checkStack || fnPhFK okPc ph lab res T ir n f ra

theorem fnPhAll1K_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) (ra : Int64) :
    fnPhAll1K okPc ph lab res (tailTab cells 0) ir ra = fnPhAll1 okPc ph lab res cells ir ra := by
  simp only [fnPhAll1K, fnPhAll1, fnPhFK_eq]

/-- **`fnPh1Ok`, keyed**: the code labels by `codeT`, the segments by `T`. -/
def fnPh1OkK (T : List (Nat × Nat × List (Directive × Nat))) (lo : Nat) (Λ : Scc.Sem.Layout)
    (cells : List (Directive × Nat)) (ir : Scc.IR.Program) : Bool :=
  match phTabBy (codeT lo cells), sitesBy (codeT lo cells) Λ with
  | some P, some ss =>
    (codeT lo cells raL).isSome &&
      fnPhAll1K (fun pc => !ss.contains pc) P.ph (fun l => Int64.ofNat ((codeT lo cells l).getD 0))
        (fun l => (codeT lo cells l).isSome) T ir (Int64.ofNat ((codeT lo cells raL).getD 0))
  | _, _ => false

theorem fnPh1OkK_eq (lo : Nat) (Λ : Scc.Sem.Layout) (cells : List (Directive × Nat)) (ir : Scc.IR.Program) :
    fnPh1OkK (tailTab cells 0) lo Λ cells ir = fnPh1Ok lo Λ cells ir := by
  simp only [fnPh1OkK, fnPhAll1K_eq, codeT_eq]
  rfl

/-! ## A12 -/

/-- **A12 for the kernel** (`a12fast_eq`). -/
def a12fast (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir =>
    let T := tailTab o.prog 0
    fnCode1OkK T o.place.need ir && fnPh1OkK T t.Λ.code.lo t.Λ o.prog ir
  | none => false

theorem a12fast_eq (o : Out) (t : Tables) : a12fast o t = a12 o t := by
  unfold a12fast a12
  cases o.place.ir with
  | some ir => simp only [fnCode1OkK_eq, fnPh1OkK_eq]
  | none => rfl

/-- **A12 from `a12fast`.** -/
theorem a12_of_fast {o : Out} {t : Tables} (h : a12fast o t = true) : a12 o t = true :=
  a12fast_eq o t ▸ h

/-! ## A12 in two declarations -/

/-- **A12's code part for the kernel** (`fnCode1OkK` on the labels' table). -/
def a12code (o : Out) : Bool :=
  match o.place.ir with
  | some ir => fnCode1OkK (tailTab o.prog 0) o.place.need ir
  | none => false

/-- **A12's phase part for the kernel** (`fnPh1OkK` on the labels' table
and the code labels). -/
def a12ph (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => fnPh1OkK (tailTab o.prog 0) t.Λ.code.lo t.Λ o.prog ir
  | none => false

/-- **A12 from its two parts**, decided in two declarations: the kernel's
peak memory is the larger of the two, not their sum. -/
theorem a12_of_split {o : Out} {t : Tables} (hc : a12code o = true) (hp : a12ph o t = true) :
    a12 o t = true := by
  refine a12_of_fast ?_
  unfold a12fast
  unfold a12code at hc
  unfold a12ph at hp
  cases h : o.place.ir with
  | some ir => simp only [h] at hc hp; simp [hc, hp]
  | none => simp [h] at hc

/-! ## A12 one function at a time, on literal tables

As on AArch64 (`Scc/Cert/A12StageA64.lean`): on a large program each part
is a conjunction over the IR's functions, and a certificate decides function
`k`'s conjunct of each part in a declaration of its own (`a12codeAtL`,
`a12phAtL`), chained over `zipIdx.drop k` (`a12From_cons`; a run of
functions that are not stack-checked by one range check, `a12Skip`) down to
a decided end. The tables the conjuncts share are stated once, as a literal
`X` (`A12Tabs`, checked by `a12TabsOk`): the labels' indices (`idxTab`, the
labels' table rebuilt by `tailOf`), the code labels (`labTab`), A6's phase
table and sites, the argument areas (the frames by `frOfA`) and each
function's first local label number (`starts`). Recomputing them in each
declaration would cost each one the whole program. -/

/-- **`frOfK` at given argument areas** (`frOfA_eq`). -/
def frOfA (ir : Scc.IR.Program) (areas : List (Scc.IR.Sym × Nat)) (f : Scc.IR.Func) : Frame :=
  { frameOfK areas f with maps := ir.growth.isSome }

theorem frOfA_eq (ir : Scc.IR.Program) (f : Scc.IR.Func) :
    frOfA ir (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length) f = frOfK ir f := rfl

/-- **`fnOk1K` at given argument areas** (`fnOk1A_eq`). -/
def fnOk1A (T : List (Nat × Nat × List (Directive × Nat))) (tbl : List NeedX64.Row) (ir : Scc.IR.Program)
    (areas : List (Scc.IR.Sym × Nat)) (n : Nat) (f : Scc.IR.Func) : Bool :=
  let fr := frOfA ir areas f
  match f.blocks, szK T (chkL f) 0 (5 + f.params.length) with
  | b0 :: _, zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spillsK (rsK (kslots fr)) f.params zps with
    | some ps =>
      ir.growth.isSome &&
      prologueInK T f.name (chkL f) (labelOf f.name b0.label) (Int64.ofInt fr.size)
        (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps &&
      decide (fr.size < 2 ^ 31) && decide (fr.size % 16 = 0) &&
      blocksOkK T fr n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (ir.abortFn == "scc_rt_abort" && blkBK T (ovfL fr) 0 ovfBlk)) &&
      needOk1 tbl f.name fr.size f &&
      blkBK T (proL fr) 0 stkHead
    | none => false
  | _, _ => false

theorem fnOk1A_eq (T : List (Nat × Nat × List (Directive × Nat))) (tbl : List NeedX64.Row) (ir : Scc.IR.Program)
    (n : Nat) (f : Scc.IR.Func) :
    fnOk1A T tbl ir (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length) n f = fnOk1K T tbl ir n f := rfl

/-- **`fnPhFK` at given argument areas** (`fnPhFA_eq`). -/
def fnPhFA (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (areas : List (Scc.IR.Sym × Nat))
    (n : Nat) (f : Scc.IR.Func) (ra : Int64) : Bool :=
  let fr := frOfA ir areas f
  match szK T (chkL f) 0 (5 + f.params.length) with
  | zl :: zf :: z1 :: z2 :: zs :: zps =>
    match spillsK (rsK (kslots fr)) f.params zps with
    | some ps =>
      res f.name && res (chkL f) &&
      (proLabs (Int64.ofInt fr.size) (proL fr) zl z1 z2 zs ps).all res &&
      proPhOk okPc ph lab f.name (chkL f) (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs ps &&
      blocksPhK okPc ph lab res T fr ra n (f.blocks.zip (Scc.IR.StackMap.callMaps f)) &&
      (!hasAddChk f || (res (ovfL fr) && (blkLabs ovfBlk).all res &&
        Spike.Lib.X64Consumer.blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 ovfBlk))
    | none => false
  | _ => false

theorem fnPhFA_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (T : List (Nat × Nat × List (Directive × Nat))) (ir : Scc.IR.Program) (n : Nat) (f : Scc.IR.Func)
    (ra : Int64) :
    fnPhFA okPc ph lab res T ir (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length) n f ra =
      fnPhFK okPc ph lab res T ir n f ra := rfl

/-- **The labels' indices**: `tailTab` without the tails. -/
def idxTab (cells : List (Directive × Nat)) : List (Nat × Nat) :=
  (tailTab cells 0).map fun p => (p.1, p.2.1)

/-- The labels' table from the labels' indices (`tailOf_idxTab`). -/
def tailOf (cells : List (Directive × Nat)) (L : List (Nat × Nat)) : List (Nat × Nat × List (Directive × Nat)) :=
  L.map fun p => (p.1, p.2, cells.drop (p.2 + 1))

private theorem tailTab_mem : ∀ (cells : List (Directive × Nat)) (i : Nat), ∀ p ∈ tailTab cells i,
    i ≤ p.2.1 ∧ p.2.2 = cells.drop (p.2.1 + 1 - i)
  | [], _, p, hp => by simp [tailTab] at hp
  | (d, z) :: cs, i, p, hp => by
    have step : ∀ q ∈ tailTab cs (i + 1), i ≤ q.2.1 ∧ q.2.2 = ((d, z) :: cs).drop (q.2.1 + 1 - i) := by
      intro q hq
      obtain ⟨h1, h2⟩ := tailTab_mem cs (i + 1) q hq
      refine ⟨by omega, ?_⟩
      rw [h2, show q.2.1 + 1 - i = (q.2.1 + 1 - (i + 1)) + 1 by omega, List.drop_succ_cons]
    cases d with
    | label m =>
      simp only [tailTab, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · exact step p hp
    | instr _ => exact step p (by simpa [tailTab] using hp)
    | byteArray _ => exact step p (by simpa [tailTab] using hp)

/-- **The labels' table is rebuilt from its indices.** -/
theorem tailOf_idxTab (cells : List (Directive × Nat)) : tailOf cells (idxTab cells) = tailTab cells 0 := by
  unfold tailOf idxTab
  rw [List.map_map]
  conv => rhs; rw [← List.map_id (tailTab cells 0)]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨-, h⟩ := tailTab_mem cells 0 p hp
  simp only [Function.comp_apply, id_eq, Nat.sub_zero] at h ⊢
  rw [← h]

/-- `starts` numbers the functions it is given, in order. -/
theorem starts_fst (ir : Scc.IR.Program) : ∀ (n : Nat) (fs : List Scc.IR.Func), (starts ir n fs).map (·.1) = fs
  | _, [] => rfl
  | n, f :: fs => by simp only [starts, List.map_cons, starts_fst ir _ fs]

/-- A list of pairs from its first components, indexed, and its second
components looked up by index. -/
theorem zipIdx_lookup {α β : Type} (l : List (α × β)) (d : β) :
    ((l.map (·.1)).zipIdx.map fun p => (p.1, ((l.map (·.2))[p.2]?).getD d)) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, List.getElem?_eq_getElem h2]

deriving instance Inhabited for PhTab

/-- **A12's tables**, for a certificate to state once as a literal. -/
structure A12Tabs where
  /-- The labels' indices (`idxTab`). -/
  idx : List (Nat × Nat)
  /-- The code labels (`labTab` at the code base). -/
  lab : List (Nat × Nat)
  /-- A6's phase table, its labels resolved. -/
  ph : PhTab
  /-- The marks' sites. -/
  ss : List Nat
  /-- The argument areas of the IR's functions. -/
  areas : List (Scc.IR.Sym × Nat)
  /-- Each function's first local label number (`starts`), in order. -/
  starts : List Nat
  deriving Inhabited

/-- The code labels of a table, as a resolver. -/
def A12Tabs.code (X : A12Tabs) (l : String) : Option Nat := lookupK (key l) X.lab

/-- **`X` is A12's tables of `o` at `t`** (a certificate decides it once). -/
def a12TabsOk (o : Out) (t : Tables) (X : A12Tabs) : Bool :=
  match o.place.ir with
  | some ir =>
    decide (idxTab o.prog = X.idx) && decide (labTab o.prog t.Λ.code.lo = X.lab) &&
    decide (phTabBy X.code = some X.ph) && decide (sitesBy X.code t.Λ = some X.ss) &&
    (X.code raL).isSome && decide (Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length = X.areas) &&
    decide ((starts ir 0 ir.funcs).map (·.2) = X.starts)
  | none => false

/-- A12's tables of `o` at `t`, for the code generator (`a12TabsOk`). -/
def a12Tabs (o : Out) (t : Tables) : Option A12Tabs :=
  match o.place.ir, phTabBy (codeT t.Λ.code.lo o.prog), sitesBy (codeT t.Λ.code.lo o.prog) t.Λ with
  | some ir, some T, some ss =>
    some ⟨idxTab o.prog, labTab o.prog t.Λ.code.lo, T, ss, Scc.IR.StackMap.argAreas ir Scc.Emit.X64.argRegs.length,
      (starts ir 0 ir.funcs).map (·.2)⟩
  | _, _, _ => none

/-- `List.all` over `l.zipIdx` from index `k` on, from its element at `k`
and the rest. -/
theorem all_zipIdx_drop_cons {α : Type} {l : List α} {p : α × Nat → Bool} {k : Nat} {x : α}
    (hx : l[k]? = some x) (h : p (x, k) = true) (t : (l.zipIdx.drop (k + 1)).all p = true) :
    (l.zipIdx.drop k).all p = true := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  rw [List.drop_eq_getElem_cons (by simpa using hk), List.all_cons, List.getElem_zipIdx]
  simp only [Nat.zero_add] at *
  rw [h, t]
  rfl

/-- A12's code part at one function, on the tables `X`. -/
def code12L (o : Out) (X : A12Tabs) (ir : Scc.IR.Program) : Scc.IR.Func × Nat → Bool := fun (f, fi) =>
  !f.checkStack || fnOk1A (tailOf o.prog X.idx) o.place.need ir X.areas ((X.starts[fi]?).getD 0) f

/-- A12's phase part at one function, on the tables `X`. -/
def ph12L (o : Out) (X : A12Tabs) (ir : Scc.IR.Program) : Scc.IR.Func × Nat → Bool := fun (f, fi) =>
  !f.checkStack || fnPhFA (fun pc => !X.ss.contains pc) X.ph.ph (fun l => Int64.ofNat ((X.code l).getD 0))
    (fun l => (X.code l).isSome) (tailOf o.prog X.idx) ir X.areas ((X.starts[fi]?).getD 0) f
    (Int64.ofNat ((X.code raL).getD 0))

/-- `ph12L` (named as on AArch64, where it does not read `o`). -/
abbrev ph12O (o : Out) (X : A12Tabs) : Scc.IR.Program → Scc.IR.Func × Nat → Bool := ph12L o X

/-- A conjunct of A12's parts at function `k` of `o`'s IR. -/
def a12At (o : Out) (P : Scc.IR.Program → Scc.IR.Func × Nat → Bool) (k : Nat) : Bool :=
  match o.place.ir with
  | some ir => match ir.funcs[k]? with
    | some f => P ir (f, k)
    | none => false
  | none => false

/-- The conjuncts from function `k` on. -/
def a12From (o : Out) (P : Scc.IR.Program → Scc.IR.Func × Nat → Bool) (k : Nat) : Bool :=
  match o.place.ir with
  | some ir => (ir.funcs.zipIdx.drop k).all (P ir)
  | none => false

/-- **A12's code part at function `k`.** -/
abbrev a12codeAtL (o : Out) (X : A12Tabs) (k : Nat) : Bool := a12At o (code12L o X) k

/-- **A12's phase part at function `k`.** -/
abbrev a12phAtL (o : Out) (X : A12Tabs) (k : Nat) : Bool := a12At o (ph12L o X) k

/-- **`a12From` from function `k` and the rest.** -/
theorem a12From_cons {o : Out} {P : Scc.IR.Program → Scc.IR.Func × Nat → Bool} {k j : Nat} (hj : k + 1 = j)
    (h : a12At o P k = true) (t : a12From o P j = true) : a12From o P k = true := by
  subst hj
  unfold a12At at h
  unfold a12From at t ⊢
  cases hir : o.place.ir with
  | none => simp [hir] at h
  | some ir =>
    simp only [hir] at h t ⊢
    cases hf : ir.funcs[k]? with
    | none => simp [hf] at h
    | some f => simp only [hf] at h; exact all_zipIdx_drop_cons hf h t

/-- **Functions `k` to `j` (exclusive, `k ≤ j`) are not stack-checked**:
their conjuncts of either part hold without a check of their own
(`a12codeFrom_skip`, `a12phFrom_skip`). -/
def a12Skip (o : Out) (k j : Nat) : Bool :=
  match o.place.ir with
  | some ir => decide (k ≤ j) && ((ir.funcs.zipIdx.drop k).take (j - k)).all fun p => !p.1.checkStack
  | none => false

/-- **`a12From` over functions that are not stack-checked**, for a part
whose conjunct holds at those. -/
theorem a12From_skip {o : Out} {P : Scc.IR.Program → Scc.IR.Func × Nat → Bool} {k j : Nat}
    (hP : ∀ ir p, p.1.checkStack = false → P ir p = true)
    (h : a12Skip o k j = true) (t : a12From o P j = true) : a12From o P k = true := by
  unfold a12Skip at h
  unfold a12From at t ⊢
  cases hir : o.place.ir with
  | none => simp [hir] at h
  | some ir =>
    simp only [hir, Bool.and_eq_true, decide_eq_true_eq] at h t ⊢
    obtain ⟨hkj, h⟩ := h
    rw [← List.take_append_drop (j - k) (ir.funcs.zipIdx.drop k), List.all_append, List.drop_drop,
      show k + (j - k) = j by omega, t, Bool.and_true]
    rw [List.all_eq_true] at h ⊢
    intro p hp
    exact hP ir p (by simpa using h p hp)

/-- **A12's code part over functions that are not stack-checked.** -/
theorem a12codeFrom_skip {o : Out} {X : A12Tabs} {k j : Nat} (h : a12Skip o k j = true)
    (t : a12From o (code12L o X) j = true) : a12From o (code12L o X) k = true :=
  a12From_skip (fun _ p hc => by obtain ⟨f, fi⟩ := p; simp only at hc; simp [code12L, hc]) h t

/-- **A12's phase part over functions that are not stack-checked.** -/
theorem a12phFrom_skip {o : Out} {X : A12Tabs} {k j : Nat} (h : a12Skip o k j = true)
    (t : a12From o (ph12L o X) j = true) : a12From o (ph12L o X) k = true :=
  a12From_skip (fun _ p hc => by obtain ⟨f, fi⟩ := p; simp only at hc; simp [ph12L, hc]) h t

/-- `List.all` over `starts` from `List.all` over the functions, indexed,
with their numbers looked up by index. -/
private theorem all_starts (ir : Scc.IR.Program) (P : Scc.IR.Func × Nat → Bool)
    (h : ir.funcs.zipIdx.all (fun p => P (p.1, (((starts ir 0 ir.funcs).map (·.2))[p.2]?).getD 0)) = true) :
    (starts ir 0 ir.funcs).all P = true := by
  rw [← zipIdx_lookup (starts ir 0 ir.funcs) 0, List.all_map, starts_fst]
  exact h

/-- **A12 from its tables and its functions' conjuncts**: `X` is A12's
tables (`a12TabsOk`, one decision), and every function's code and phase
conjuncts hold (`a12From … 0`, chained by `a12From_cons` from one decision
per function and part). -/
theorem a12_of_tabs {o : Out} {t : Tables} {X : A12Tabs} (hX : a12TabsOk o t X = true)
    (hc : a12From o (code12L o X) 0 = true) (hp : a12From o (ph12L o X) 0 = true) : a12 o t = true := by
  unfold a12From at hc hp
  unfold a12TabsOk at hX
  refine a12_of_split ?_ ?_
  · unfold a12code fnCode1OkK
    cases hir : o.place.ir with
    | none => simp [hir] at hX
    | some ir =>
      simp only [hir, Bool.and_eq_true, decide_eq_true_eq, List.drop_zero] at hX hc
      obtain ⟨⟨⟨⟨⟨⟨hidx, -⟩, -⟩, -⟩, -⟩, har⟩, hst⟩ := hX
      unfold code12L at hc
      rw [← hidx, tailOf_idxTab, ← har, ← hst] at hc
      exact all_starts ir _ hc
  · unfold a12ph fnPh1OkK fnPhAll1K
    cases hir : o.place.ir with
    | none => simp [hir] at hX
    | some ir =>
      simp only [hir, Bool.and_eq_true, decide_eq_true_eq, List.drop_zero] at hX hp
      obtain ⟨⟨⟨⟨⟨⟨hidx, hlab⟩, hph⟩, hss⟩, hra⟩, har⟩, hst⟩ := hX
      have hc : codeT t.Λ.code.lo o.prog = X.code := by
        funext l; unfold codeT A12Tabs.code; rw [hlab]
      unfold ph12L at hp
      rw [← hidx, tailOf_idxTab, ← har, ← hst] at hp
      rw [hc, hph, hss]
      simp only [hra, Bool.true_and]
      exact all_starts ir _ hp

end Scc.Cert.PlaceOK.X64
