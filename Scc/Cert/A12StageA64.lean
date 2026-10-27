import Scc.Cert.A9StageA64
import Scc.Cert.Ph1A64

/-!
# A12 by keyed lookups (AArch64)

`a12` (`Scc/Cert/PlaceOKA64.lean`) checks every stack-checked function's
code (`Scc.Cert.Code1A64.fnCode1Ok`) and phase facts
(`Scc.Cert.Ph1A64.fnPh1Ok`). Written for the proofs, it finds a label at
every segment and at every label inside one (`segIn`, `labelsAt`:
`labelIdx` by `Directive`'s decidable equality, a string comparison per
label of the program), dedups a function's registers by comparing strings
(`funcRegs`), and resolves a code address at every label read (`codeOf`).

`a12fast` is the same check (`a12fast_eq`) on A9's keyed tables
(`Scc/Cert/A9StageA64.lean`):

* the labels by `tailTab`/`findT` (`segInK`, `labelsAtK`, `prologueInK`,
  `chkK`);
* the functions' contexts by `fnCtxK`;
* the code addresses by `codeT` (`Scc/Cert/Rt/PhasesA64.lean`).

A certificate decides `a9fast`, A12's code part (`a12code`) and its phase
part (`a12ph`) in three declarations; `a12_of_split` gives
`prog_placeOK_12`. The kernel's memory is held per declaration, so the peak
is the largest of the three rather than their sum. Recomputing the tables
they share in each costs a little time.
-/

namespace Scc.Cert.PlaceOK.A64

open Kraken Spike.Lib.A64.Flow Scc.Emit.A64 Spike.Lib.LowerA64 Scc.Cert.Link.A64
open Scc.Cert.Rt.A64 (key labelIdx blockAt codeT codeT_eq phTabBy sitesBy PhTab labTab lookupK)
open Scc.Cert.Code1A64 (labelsAt segIn blocksOk blockItems spills hasAddChk needOk1 fnOk1 fnCode1Ok ctxOf)
open Scc.Cert.Ph1A64 (fnPhF fnPhAll1 fnPh1Ok)

/-! ## The code part -/

/-- **`labelsAt`, keyed.** -/
def labelsAtK (T : List (Nat × Nat × List Directive)) : Nat → List Directive → Bool
  | _, [] => true
  | j, .label l :: ds => ((findT (key l) T).map (·.1) == some j) && labelsAtK T (j + 1) ds
  | j, _ :: ds => labelsAtK T (j + 1) ds

theorem labelsAtK_eq (prog : List Directive) :
    ∀ (j : Nat) (ds : List Directive), labelsAtK (tailTab prog 0) j ds = labelsAt prog j ds
  | _, [] => rfl
  | j, .label l :: ds => by
    simp only [labelsAtK, labelsAt, labelsAtK_eq prog (j + 1) ds, findT_tailTab]
    cases labelIdx prog l <;> simp
  | j, .instr _ :: ds => by simp only [labelsAtK, labelsAt, labelsAtK_eq prog (j + 1) ds]
  | j, .byteArray _ :: ds => by simp only [labelsAtK, labelsAt, labelsAtK_eq prog (j + 1) ds]

/-- **`segIn`, keyed**: the run after the label found once. -/
def segInK (T : List (Nat × Nat × List Directive)) (l : Label) (ds : List Directive) : Bool :=
  match findT (key l) T with
  | some (i, t) => decide (t.take ds.length = ds) && labelsAtK T (i + 1) ds
  | none => false

theorem segInK_eq (prog : List Directive) (l : Label) (ds : List Directive) :
    segInK (tailTab prog 0) l ds = segIn prog l ds := by
  unfold segInK segIn
  rw [findT_tailTab]
  cases labelIdx prog l <;> simp [labelsAtK_eq]

/-- **`blocksOk`, keyed.** -/
def blocksOkK (T : List (Nat × Nat × List Directive)) (c : FnCtx) : Nat → List Scc.IR.Block → Bool
  | _, [] => true
  | k, b :: bs =>
    (match c.blockLabel b.label, blockItems c k b with
     | .ok l, .ok code => segInK T l (directives code)
     | _, _ => false) &&
    blocksOkK T c (k + b.insts.length + 1) bs

theorem blocksOkK_eq (prog : List Directive) (c : FnCtx) :
    ∀ (k : Nat) (bs : List Scc.IR.Block), blocksOkK (tailTab prog 0) c k bs = blocksOk prog c k bs
  | _, [] => rfl
  | k, b :: bs => by
    simp only [blocksOkK, blocksOk, segInK_eq, blocksOkK_eq prog c _ bs]
    cases c.blockLabel b.label <;> cases blockItems c k b <;> rfl

/-- **`fnOk1`, keyed.** -/
def fnOk1K (T : List (Nat × Nat × List Directive)) (tbl : List NeedA64.Row) (c : FnCtx) (f : Scc.IR.Func) :
    Bool :=
  match f.blocks, spills c f.params with
  | b0 :: _, some ps =>
    (match c.blockLabel b0.label with
     | .ok entry => prologueInK T f.name (c.local "stack_check") entry (Int64.ofInt c.frame)
         (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL c) ps
     | .error _ => false) &&
    decide (c.frame ≤ 4095) && decide (c.frame % 16 = 0) &&
    blocksOkK T c 0 f.blocks &&
    (!hasAddChk f || chkK T (c.local "abort_overflow") 0 ovfBlk) &&
    needOk1 tbl f.name c.frame f &&
    chkK T (proL c) 0 (stkHead c)
  | _, _ => false

theorem fnOk1K_eq (prog : List Directive) (tbl : List NeedA64.Row) (c : FnCtx) (f : Scc.IR.Func) :
    fnOk1K (tailTab prog 0) tbl c f = fnOk1 prog tbl c f := by
  simp only [fnOk1K, fnOk1, prologueInK_eq, blocksOkK_eq, chkK_eq]
  rcases f.blocks with _ | ⟨b0, _⟩ <;> cases spills c f.params <;> try rfl

/-- **`fnCode1Ok`, keyed** at a labels' table `T` (the contexts by `fnCtxK`). -/
def fnCode1OkK (T : List (Nat × Nat × List Directive)) (tbl : List NeedA64.Row) (ir : Scc.IR.Program) : Bool :=
  let areas := Scc.IR.StackMap.argAreas ir argRegs.length
  ir.funcs.zipIdx.all fun (f, fi) => !f.checkStack || fnOk1K T tbl (fnCtxK ir.abortFn ir.growth areas fi f) f

theorem fnCode1OkK_eq (prog : List Directive) (tbl : List NeedA64.Row) (ir : Scc.IR.Program) :
    fnCode1OkK (tailTab prog 0) tbl ir = fnCode1Ok prog tbl ir := by
  simp only [fnCode1OkK, fnCode1Ok, fnOk1K_eq, fnCtxK_eq, ctxOf]

/-! ## The phase part -/

/-- **`fnPhAll1`, keyed** (the contexts by `fnCtxK`). -/
def fnPhAll1K (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : Bool :=
  let areas := Scc.IR.StackMap.argAreas ir argRegs.length
  ir.funcs.zipIdx.all fun (f, fi) =>
    !f.checkStack || fnPhF okPc ph lab res (fnCtxK ir.abortFn ir.growth areas fi f) f ra

theorem fnPhAll1K_eq (okPc : Nat → Bool) (ph : Nat → Nat) (lab : Label → Int64) (res : String → Bool)
    (ir : Scc.IR.Program) (ra : Int64) : fnPhAll1K okPc ph lab res ir ra = fnPhAll1 okPc ph lab res ir ra := by
  simp only [fnPhAll1K, fnPhAll1, fnCtxK_eq, ctxOf]

/-- **`fnPh1Ok`, keyed**: the code labels by `codeT`. -/
def fnPh1OkK (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) : Bool :=
  match phTabBy (codeT lo prog), sitesBy (codeT lo prog) Λ with
  | some T, some ss =>
    (codeT lo prog raL).isSome &&
      fnPhAll1K (fun pc => !ss.contains pc) T.ph (fun l => Int64.ofNat ((codeT lo prog l).getD 0))
        (fun l => (codeT lo prog l).isSome) ir (Int64.ofNat ((codeT lo prog raL).getD 0) + 4)
  | _, _ => false

theorem fnPh1OkK_eq (lo : Nat) (Λ : Scc.Sem.Layout) (prog : Program) (ir : Scc.IR.Program) :
    fnPh1OkK lo Λ prog ir = fnPh1Ok lo Λ prog ir := by
  simp only [fnPh1OkK, fnPhAll1K_eq, codeT_eq]
  rfl

/-! ## A12 -/

/-- **A12 for the kernel** (`a12fast_eq`). -/
def a12fast (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => fnCode1OkK (tailTab o.prog 0) o.place.need ir && fnPh1OkK t.Λ.code.lo t.Λ o.prog ir
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

/-- **A12's phase part for the kernel** (`fnPh1OkK` on the code labels). -/
def a12ph (o : Out) (t : Tables) : Bool :=
  match o.place.ir with
  | some ir => fnPh1OkK t.Λ.code.lo t.Λ o.prog ir
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

On a large program each part is a conjunction over the IR's functions
(`ir.funcs.zipIdx`). A certificate decides function `k`'s conjunct of each
part in a declaration of its own (`a12codeAtL`, `a12phAtL`), so that the
kernel keeps one function's terms alive at a time, and chains them over
`zipIdx.drop k` (`a12codeFromL_cons`, `a12phFromL_cons`) down to a decided
end. The tables the conjuncts share are stated once, as a literal `X`
(`A12Tabs`, checked by `a12TabsOk`): the labels' indices (`idxTab`; the
labels' table `tailTab` is rebuilt from them by `tailOf`, as a table of
tails it would be quadratic as a literal), the code labels (`labTab`), A6's
phase table and sites, and the argument areas. Recomputing them in each
declaration would cost each one the whole program. -/

/-- **The labels' indices**: `tailTab` without the tails. -/
def idxTab (prog : List Directive) : List (Nat × Nat) := (tailTab prog 0).map fun p => (p.1, p.2.1)

/-- The labels' table from the labels' indices (`tailOf_idxTab`). -/
def tailOf (prog : List Directive) (L : List (Nat × Nat)) : List (Nat × Nat × List Directive) :=
  L.map fun p => (p.1, p.2, prog.drop (p.2 + 1))

private theorem tailTab_mem : ∀ (prog : List Directive) (i : Nat), ∀ p ∈ tailTab prog i,
    i ≤ p.2.1 ∧ p.2.2 = prog.drop (p.2.1 + 1 - i)
  | [], _, p, hp => by simp [tailTab] at hp
  | d :: ds, i, p, hp => by
    have step : ∀ q ∈ tailTab ds (i + 1), i ≤ q.2.1 ∧ q.2.2 = (d :: ds).drop (q.2.1 + 1 - i) := by
      intro q hq
      obtain ⟨h1, h2⟩ := tailTab_mem ds (i + 1) q hq
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
theorem tailOf_idxTab (prog : List Directive) : tailOf prog (idxTab prog) = tailTab prog 0 := by
  unfold tailOf idxTab
  rw [List.map_map]
  conv => rhs; rw [← List.map_id (tailTab prog 0)]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨-, h⟩ := tailTab_mem prog 0 p hp
  simp only [Function.comp_apply, id_eq, Nat.sub_zero] at h ⊢
  rw [← h]

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
  deriving Inhabited

/-- The code labels of a table, as a resolver. -/
def A12Tabs.code (X : A12Tabs) (l : String) : Option Nat := lookupK (key l) X.lab

/-- **`X` is A12's tables of `o` at `t`** (a certificate decides it once). -/
def a12TabsOk (o : Out) (t : Tables) (X : A12Tabs) : Bool :=
  match o.place.ir with
  | some ir =>
    decide (idxTab o.prog = X.idx) && decide (labTab o.prog t.Λ.code.lo = X.lab) &&
    decide (phTabBy X.code = some X.ph) && decide (sitesBy X.code t.Λ = some X.ss) &&
    (X.code raL).isSome && decide (Scc.IR.StackMap.argAreas ir argRegs.length = X.areas)
  | none => false

/-- A12's tables of `o` at `t`, for the code generator (`a12TabsOk`). -/
def a12Tabs (o : Out) (t : Tables) : Option A12Tabs :=
  match o.place.ir, phTabBy (codeT t.Λ.code.lo o.prog), sitesBy (codeT t.Λ.code.lo o.prog) t.Λ with
  | some ir, some T, some ss =>
    some ⟨idxTab o.prog, labTab o.prog t.Λ.code.lo, T, ss, Scc.IR.StackMap.argAreas ir argRegs.length⟩
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
  !f.checkStack || fnOk1K (tailOf o.prog X.idx) o.place.need (fnCtxK ir.abortFn ir.growth X.areas fi f) f

/-- A12's phase part at one function, on the tables `X`. -/
def ph12L (X : A12Tabs) (ir : Scc.IR.Program) : Scc.IR.Func × Nat → Bool := fun (f, fi) =>
  !f.checkStack || fnPhF (fun pc => !X.ss.contains pc) X.ph.ph (fun l => Int64.ofNat ((X.code l).getD 0))
    (fun l => (X.code l).isSome) (fnCtxK ir.abortFn ir.growth X.areas fi f) f
    (Int64.ofNat ((X.code raL).getD 0) + 4)

/-- `ph12L` at `o` (unused: the x86-64 twin's phase conjunct reads `o`'s
labels' table), for the code generator to name either ISA's alike. -/
abbrev ph12O (_o : Out) (X : A12Tabs) : Scc.IR.Program → Scc.IR.Func × Nat → Bool := ph12L X

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
abbrev a12phAtL (o : Out) (X : A12Tabs) (k : Nat) : Bool := a12At o (ph12L X) k

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
    (t : a12From o (ph12L X) j = true) : a12From o (ph12L X) k = true :=
  a12From_skip (fun _ p hc => by obtain ⟨f, fi⟩ := p; simp only at hc; simp [ph12L, hc]) h t

/-- **A12 from its tables and its functions' conjuncts**: `X` is A12's
tables (`a12TabsOk`, one decision), and every function's code and phase
conjuncts hold (`a12From … 0`, chained by `a12From_cons` from one decision
per function and part). -/
theorem a12_of_tabs {o : Out} {t : Tables} {X : A12Tabs} (hX : a12TabsOk o t X = true)
    (hc : a12From o (code12L o X) 0 = true) (hp : a12From o (ph12L X) 0 = true) : a12 o t = true := by
  unfold a12From at hc hp
  unfold a12TabsOk at hX
  refine a12_of_split ?_ ?_
  · unfold a12code fnCode1OkK
    cases hir : o.place.ir with
    | none => simp [hir] at hX
    | some ir =>
      simp only [hir, Bool.and_eq_true, decide_eq_true_eq, List.drop_zero] at hX hc
      obtain ⟨⟨⟨⟨⟨hidx, -⟩, -⟩, -⟩, -⟩, har⟩ := hX
      unfold code12L at hc
      rw [← hidx, tailOf_idxTab, ← har] at hc
      exact hc
  · unfold a12ph fnPh1OkK fnPhAll1K
    cases hir : o.place.ir with
    | none => simp [hir] at hX
    | some ir =>
      simp only [hir, Bool.and_eq_true, decide_eq_true_eq, List.drop_zero] at hX hp
      obtain ⟨⟨⟨⟨⟨-, hlab⟩, hph⟩, hss⟩, hra⟩, har⟩ := hX
      have hc : codeT t.Λ.code.lo o.prog = X.code := by
        funext l; unfold codeT A12Tabs.code; rw [hlab]
      unfold ph12L at hp
      rw [hc, hph, hss]
      simp only [hra, Bool.true_and]
      rw [har]
      exact hp

end Scc.Cert.PlaceOK.A64
