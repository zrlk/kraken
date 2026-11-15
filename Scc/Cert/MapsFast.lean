import Scc.Cert.MapsCompute

/-!
# Structural forms of the table computation, for the kernel

`leaders`, `fnSuccs`, `fnMapsW` and `computeW` (`Scc.Cert.MapsCompute`) index the body's
instruction array (`is[k]!`, `is[k + 1]!`, `is[k - 1]!`, `live[k]!`) inside loops over
`List.range`. The kernel evaluates each index by walking the array's list from the start, so a
certificate's `kernel_rfl` checks of a function's maps, successors and tables (`gc_ms_eq_i`,
`gc_fs_eq_i`, `tables_c_i`) take time and memory quadratic in the function's length.

This file gives each of them a structural form (`leadersK`, `fnSuccsK`, `fnMapsWK`,
`computeWK`) that walks the instruction list once, with a one-instruction lookahead (and the
previous instruction's flow carried along), and proves it equal to the original for all inputs
(`leaders_eq_K`, `fnSuccs_eq_K`, `fnMapsW_eq_K`, `computeW_eq_K`). A certificate states its
theorems about the originals and proves them as `(…_eq_K …).trans (by kernel_rfl)`: the kernel
evaluates only the structural form. The originals stay the specification.
-/

namespace Scc.Cert.Maps

/-! ## Lists -/

/-- The head of `l.drop k` is `l[k]!`. -/
theorem getElem!_of_drop_eq_cons {α : Type} [Inhabited α] {l : List α} {k : Nat} {x : α} {r : List α}
    (h : l.drop k = x :: r) : l[k]! = x := by
  induction l generalizing k with
  | nil => simp at h
  | cons y ys ih =>
    cases k with
    | zero => simp at h; simp [h.1]
    | succ k => simp at h; simpa using ih h

/-- The head of `is.toList.drop k` is `is[k]!`. -/
theorem arr_getElem!_of_drop_eq_cons {α : Type} [Inhabited α] {is : Array α} {k : Nat} {x : α} {r : List α}
    (h : is.toList.drop k = x :: r) : is[k]! = x := by
  rw [← Array.getElem!_toList]; exact getElem!_of_drop_eq_cons h

/-- The tail of `l.drop k` is `l.drop (k + 1)`. -/
theorem drop_succ_of_drop_eq_cons {α : Type} {l : List α} {k : Nat} {x : α} {r : List α}
    (h : l.drop k = x :: r) : l.drop (k + 1) = r := by
  rw [← List.drop_drop, h]; rfl

/-! ## Leaders -/

/-- `leaders`' `after` part from instruction `k` (the suffix of the body's instructions from `k`
on; `tg`: the branch targets), by one pass with a one-instruction lookahead. -/
def afterK (tg : List Nat) : Nat → List (Nat × Nat × Ins) → List Nat
  | _, [] => []
  | k, (_, _, i) :: rest =>
    let r := afterK tg (k + 1) rest
    let push := match rest with | [] => r | _ :: _ => (k + 1) :: r
    match i.flow with
    | .call _ => push
    | .jcc _ =>
      let jj := match rest with
        | (_, _, j) :: _ => !tg.contains (k + 1) && (match j.flow with | .jmp _ => true | _ => false)
        | [] => false
      if jj then r else push
    | _ => r

/-- **`leaders`, structurally** (`leaders_eq_K`). -/
def leadersK (body : List Item) : List Nat :=
  let l := (insOf body).toList
  let tg := targets body
  sortStable (fun a b => decide (a ≤ b)) ((if l.length = 0 then [] else [0]) ++ tg ++ afterK tg 0 l).eraseDups

/-- The filter of `leaders`' `after` part. -/
def afterP (is : Array (Nat × Nat × Ins)) (tg : List Nat) (k : Nat) : Bool :=
  match (is[k]!).2.2.flow with
  | .call _ => true
  | .jcc _ => !jccJmp is tg k
  | _ => false

/-- `leaders`, with its `after` filter named. -/
theorem leaders_unfold (body : List Item) : leaders body =
    sortStable (fun a b => decide (a ≤ b)) ((if (insOf body).size = 0 then [] else [0]) ++ targets body ++
      ((((List.range (insOf body).size).filter (afterP (insOf body) (targets body))).map (· + 1)).filter
        (· < (insOf body).size))).eraseDups := rfl

/-- `afterK` from `k` is `leaders`' `after` part restricted to the indices from `k` on. -/
theorem afterK_eq (tg : List Nat) (is : Array (Nat × Nat × Ins)) :
    ∀ (suf : List (Nat × Nat × Ins)) (k : Nat), is.toList.drop k = suf →
    afterK tg k suf =
      (((List.range' k suf.length).filter (afterP is tg)).map (· + 1)).filter (· < is.size) := by
  intro suf
  induction suf with
  | nil => intro k _; simp [afterK]
  | cons x rest ih =>
    intro k h
    obtain ⟨a, z, i⟩ := x
    have hk := arr_getElem!_of_drop_eq_cons h
    have h1 := drop_succ_of_drop_eq_cons h
    have hlen : is.size = k + 1 + rest.length := by
      have := congrArg List.length h; simp at this; omega
    rw [List.length_cons, List.range'_succ, List.filter_cons]
    simp only [afterK]; rw [ih (k + 1) h1]; clear ih
    cases rest with
    | nil =>
      cases i.flow <;> simp [hlen]
    | cons y rest' =>
      obtain ⟨b, w, j⟩ := y
      have hk1 := arr_getElem!_of_drop_eq_cons h1
      have hlt : k + 1 < is.size := by simp [hlen]
      have hk1' : is[k + 1]'hlt = (b, w, j) := by rw [← getElem!_pos is (k + 1) hlt]; exact hk1
      cases hf : i.flow <;> cases hj : j.flow <;> by_cases hm : k + 1 ∈ tg <;>
        simp [afterP, jccJmp, hk, hk1', hf, hj, hm, hlt]

/-- **`leaders` is `leadersK`.** -/
theorem leaders_eq_K (body : List Item) : leaders body = leadersK body := by
  rw [leaders_unfold, leadersK, afterK_eq (targets body) (insOf body) _ 0 List.drop_zero,
    List.range_eq_range']
  simp

/-! ## Label addresses -/

/-- `labelIdx`, structurally: the labels with the index of the next instruction, from index `c`. -/
def labelIdxGo : List Item → Nat → List (String × Nat)
  | [], _ => []
  | .label _ l :: rest, c => (l, c) :: labelIdxGo rest c
  | .ins _ _ _ :: rest, c => labelIdxGo rest (c + 1)

/-- `labelIdx`'s fold, from an accumulator, is `labelIdxGo`. -/
theorem labelIdx_foldl (f : List (String × Nat) × Nat → Item → List (String × Nat) × Nat)
    (hl : ∀ acc c a l, f (acc, c) (.label a l) = ((l, c) :: acc, c))
    (hi : ∀ acc c a z i, f (acc, c) (.ins a z i) = (acc, c + 1)) :
    ∀ (body : List Item) (acc : List (String × Nat)) (c : Nat),
    (body.foldl f (acc, c)).1.reverse = acc.reverse ++ labelIdxGo body c
  | [], acc, c => by simp [labelIdxGo]
  | .label _ l :: rest, acc, c => by
    simp only [List.foldl_cons, labelIdxGo, hl]; rw [labelIdx_foldl f hl hi rest]; simp
  | .ins _ _ _ :: rest, acc, c => by
    simp only [List.foldl_cons, labelIdxGo, hi]; rw [labelIdx_foldl f hl hi rest]

/-- `labelIdx` is `labelIdxGo` from index 0. -/
theorem labelIdx_eq (body : List Item) : labelIdx body = labelIdxGo body 0 := by
  unfold labelIdx
  rw [labelIdx_foldl _ (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)]; simp

/-- Label → address of the first body instruction at or after it (only labels with one). -/
def labelAddrK.go : List Item → List String → List (String × Nat)
  | [], _ => []
  | .label _ l :: rest, pend => go rest (l :: pend)
  | .ins a _ _ :: rest, pend => (pend.reverse.map fun l => (l, a)) ++ go rest []

/-- The address of each label of a body that has an instruction at or after it. -/
def labelAddrK (body : List Item) : List (String × Nat) := labelAddrK.go body []

/-- The instructions of a body, as a list. -/
def insL (body : List Item) : List (Nat × Nat × Ins) :=
  body.filterMap fun | .ins a z i => some (a, z, i) | _ => none

/-- `insOf` as a list. -/
theorem insOf_toList (body : List Item) : (insOf body).toList = insL body := by
  unfold insOf insL; congr

/-- Looking up a name among names all mapped to `b`. -/
theorem lookup_map_const {β : Type} (s : String) (b : β) :
    ∀ xs : List String, (xs.map fun l => (l, b)).lookup s = if s ∈ xs then some b else none
  | [] => by simp
  | x :: xs => by
    rw [List.map_cons, List.lookup_cons, lookup_map_const s b xs]
    by_cases h : s = x
    · simp [h]
    · have h' : (s == x) = false := by simpa using h
      simp [h', h]

/-- The index targets of `succIdx` for a label. -/
def tgtI (lix : List (String × Nat)) (n : Nat) (s : String) : List Nat :=
  match lix.lookup s with | some j => if j < n then [j] else [] | none => []

/-- `tgtI` over `labelIdxGo` from index `c` (labels `pend` pending at `c`), mapped to
addresses, is the lookup in `labelAddrK.go`. -/
theorem tgtI_go (L : List (Nat × Nat × Ins)) (s : String) :
    ∀ (body : List Item) (pend : List String) (c : Nat), L.drop c = insL body →
    (tgtI ((pend.reverse.map fun l => (l, c)) ++ labelIdxGo body c) L.length s).map
      (fun j => (L[j]!).1) = ((labelAddrK.go body pend).lookup s).toList
  | [], pend, c, h => by
    have hc : L.length ≤ c := by
      have := congrArg List.length h; simp [insL] at this; omega
    simp only [tgtI, labelIdxGo, labelAddrK.go, List.append_nil, lookup_map_const]
    split <;> simp_all <;> omega
  | .label _ l :: rest, pend, c, h => by
    have := tgtI_go L s rest (l :: pend) c (by simpa [insL] using h)
    simpa [labelIdxGo, labelAddrK.go] using this
  | .ins a z i :: rest, pend, c, h => by
    have h' : L.drop c = (a, z, i) :: insL rest := by simpa [insL] using h
    have ih := tgtI_go L s rest [] (c + 1) (drop_succ_of_drop_eq_cons h')
    have hc : c < L.length := by
      have := congrArg List.length h'; simp at this; omega
    have ha : L[c] = (a, z, i) := by rw [← getElem!_pos L c hc]; exact getElem!_of_drop_eq_cons h'
    simp only [List.reverse_nil, List.map_nil, List.nil_append] at ih
    simp only [labelIdxGo, labelAddrK.go, tgtI, List.lookup_append, lookup_map_const] at ih ⊢
    by_cases hs : s ∈ pend.reverse
    · simp [hs, hc, ha]
    · simpa [hs] using ih

/-- A label's `succIdx` targets, mapped to addresses, are its `labelAddrK` address. -/
theorem tgtI_eq (body : List Item) (s : String) :
    (tgtI (labelIdx body) (insOf body).size s).map (fun j => ((insOf body)[j]!).1) =
      ((labelAddrK body).lookup s).toList := by
  have := tgtI_go (insL body) s body [] 0 (by simp)
  simp only [List.reverse_nil, List.map_nil, List.nil_append] at this
  have hs : (insOf body).size = (insL body).length := by rw [← insOf_toList]; simp
  have hg : ∀ j : Nat, (insOf body)[j]! = (insL body)[j]! := by
    intro j; rw [← insOf_toList, Array.getElem!_toList]
  rw [labelIdx_eq, labelAddrK, ← this, hs]; simp only [hg]

/-! ## Block successors -/

/-- `fnSuccs`' walk from instruction `k` (the suffix `suf` of the body's instructions from `k` on),
structurally. -/
def fnSuccsWalkK (lxa : List (String × Nat)) (ls tg : List Nat) :
    Nat → List (Nat × Nat × Ins) → List Nat × List String
  | _, [] => ([], [])
  | k, (a, z, i) :: rest =>
    let nxtA : List Nat := match rest with | (b, _, _) :: _ => [b] | [] => []
    let tgt (l : String) : List Nat := (lxa.lookup l).toList
    match i.flow with
    | .call _ => ([a + z], [])
    | .ret => ([a], [])
    | .stop => ([], [])
    | .jcc l =>
      match rest with
      | (_, _, j) :: _ =>
        if !tg.contains (k + 1) && (match j.flow with | .jmp _ => true | _ => false) then
          let tl := match j.flow with
            | .jmp m => if (tgt m).isEmpty then [m] else []
            | _ => []
          (tgt l ++ (match j.flow with | .jmp m => tgt m | _ => []), tl)
        else (tgt l ++ nxtA, [])
      | [] => (tgt l, [])
    | .jmp l => match tgt l with
      | [] => ([], [l])
      | js => (js, [])
    | .fall => if ls.contains (k + 1) then (nxtA, []) else fnSuccsWalkK lxa ls tg (k + 1) rest

/-- **`fnSuccs`, structurally** (`fnSuccs_eq_K`). -/
def fnSuccsK (t : FnTags) (items : List Item) : List Succs :=
  let body := bodyOf t items
  let l := (insOf body).toList
  let ls := leadersK body
  let tg := targets body
  let lxa := labelAddrK body
  ls.map fun k =>
    let suf := l.drop k
    let a := match suf with | (a, _, _) :: _ => a | [] => 0
    let (nx, tl) := fnSuccsWalkK lxa ls tg k suf
    ⟨a, nx, tl⟩

/-- `succIdx` with its label targets as `tgtI`. -/
theorem succIdx_eq (lix : List (String × Nat)) (n k : Nat) (i : Ins) : succIdx lix n k i =
    match i.flow with
    | .fall | .call _ => if k + 1 < n then [k + 1] else []
    | .jmp l => tgtI lix n l
    | .jcc l => tgtI lix n l ++ (if k + 1 < n then [k + 1] else [])
    | .ret | .stop => [] := by
  unfold succIdx tgtI; cases i.flow <;> rfl

/-- `fnSuccs`' walk from `k`, with enough fuel, is `fnSuccsWalkK` on the suffix from `k`. -/
theorem fnSuccs_walk_eq_K (is : Array (Nat × Nat × Ins)) (lix : List (String × Nat)) (ls tg : List Nat)
    (lxa : List (String × Nat))
    (hT : ∀ s, (tgtI lix is.size s).map (fun j => (is[j]!).1) = (lxa.lookup s).toList) :
    ∀ (suf : List (Nat × Nat × Ins)) (k f : Nat), is.toList.drop k = suf → suf.length < f →
    fnSuccs.walk is is.size lix ls tg (fun j => (is[j]!).1) f k = fnSuccsWalkK lxa ls tg k suf := by
  intro suf
  induction suf with
  | nil =>
    intro k f h hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hk : is.size ≤ k := by
      have := congrArg List.length h; simp at this; omega
    rw [fnSuccs.walk]; simp [hk, fnSuccsWalkK]
  | cons x rest ih =>
    intro k f h hf
    obtain ⟨a, z, i⟩ := x
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hlen : is.size = k + 1 + rest.length := by
      have := congrArg List.length h; simp at this; omega
    have hk : is[k]! = (a, z, i) := arr_getElem!_of_drop_eq_cons h
    have h1 := drop_succ_of_drop_eq_cons h
    have hn : ¬ is.size ≤ k := by omega
    rw [fnSuccs.walk]; simp only [hn, ite_false, hk]
    cases rest with
    | nil =>
      simp only [List.length_nil] at hlen
      have hn1 : ¬ k + 1 < is.size := by omega
      have ih' := ih (k + 1) f h1 (by simp at hf ⊢; omega)
      simp only [fnSuccsWalkK] at ih'
      clear ih
      cases hf' : i.flow
      case jmp l =>
        simp only [fnSuccsWalkK, hf', succIdx_eq]
        have e := hT l
        cases hti : tgtI lix is.size l <;> rw [hti] at e <;> rw [← e] <;> rfl
      all_goals simp [fnSuccsWalkK, hf', succIdx_eq, jccJmp, hn1, hT, ih', hk]
    | cons y rest' =>
      obtain ⟨b, w, j⟩ := y
      simp only [List.length_cons] at hlen
      have hn1 : k + 1 < is.size := by omega
      have hk1 : is[k + 1] = (b, w, j) := by
        rw [← getElem!_pos is (k + 1) hn1]; exact arr_getElem!_of_drop_eq_cons h1
      have hk1' : is[k + 1]! = (b, w, j) := by rw [getElem!_pos is (k + 1) hn1]; exact hk1
      have hk0 : is[k] = (a, z, i) := by rw [← getElem!_pos is k (by omega)]; exact hk
      have ih' := ih (k + 1) f h1 (by simp at hf ⊢; omega)
      clear ih
      have hE : ∀ s, tgtI lix is.size s = [] ↔ (lxa.lookup s).toList = [] := by
        intro s; rw [← hT s, List.map_eq_nil_iff]
      cases hf' : i.flow
      case jmp l =>
        simp only [fnSuccsWalkK, hf', succIdx_eq]
        have e := hT l
        cases hti : tgtI lix is.size l <;> rw [hti] at e <;> rw [← e] <;> rfl
      case jcc l =>
        simp only [fnSuccsWalkK, hf', jccJmp, hk, hk1', succIdx_eq]
        cases hj : j.flow <;> by_cases hm : k + 1 ∈ tg <;>
          simp [hm, hk1, hn1, hT] <;> simp only [hE, List.isEmpty_iff]
      all_goals simp [fnSuccsWalkK, hf', ih', hk1, hn1]

/-- **`fnSuccs` is `fnSuccsK`.** -/
theorem fnSuccs_eq_K (t : FnTags) (items : List Item) : fnSuccs t items = fnSuccsK t items := by
  unfold fnSuccs fnSuccsK
  simp only [leaders_eq_K]
  apply List.map_congr_left
  intro k _
  have hw := fnSuccs_walk_eq_K (insOf (bodyOf t items)) (labelIdx (bodyOf t items))
    (leadersK (bodyOf t items))
    (targets (bodyOf t items)) (labelAddrK (bodyOf t items)) (tgtI_eq (bodyOf t items))
    ((insOf (bodyOf t items)).toList.drop k) k ((insOf (bodyOf t items)).size + 1) rfl
    (by simp; omega)
  rw [hw]
  cases hd : (insOf (bodyOf t items)).toList.drop k with
  | nil =>
    have hk : (insOf (bodyOf t items)).size ≤ k := by
      have := congrArg List.length hd; simp at this; omega
    have h0 : (insOf (bodyOf t items))[k]! = default :=
      getElem!_neg (insOf (bodyOf t items)) k (by omega)
    simp [h0]; rfl
  | cons x rest =>
    obtain ⟨a, z, i⟩ := x
    simp [arr_getElem!_of_drop_eq_cons hd]

/-! ## Root maps -/

/-- `fnMapsW`' maps over the body, structurally: from instruction `k` (the suffix of the body's
instructions from `k` on), the previous instruction's flow `prev` and the liveness from `k` on. -/
def msK (t : FnTags) (rs : List (Nat × List (Loc × Tag))) (ls : List Nat) :
    Nat → Option Flow → List (Nat × Nat × Ins) → List (List Int) → Except String (List (List RootMap))
  | _, _, [], _ => pure []
  | k, prev, (a, z, i) :: rest, lv => do
    let (l0, lr) := match lv with | [] => (([] : List Int), ([] : List (List Int))) | x :: xs => (x, xs)
    let res : List (Loc × Tag) := match prev with
      | some (.call _) => (rs.lookup a).getD []
      | _ => []
    let entry : List RootMap :=
      if ls.contains k then [{ pt := ⟨.blockEntry, a⟩, roots := res ++ liveRoots t l0 }]
      else []
    let own : List RootMap ← match i.flow with
      | .call _ => do
        let sl ← callRoots t (a + z)
        pure [{ pt := ⟨.call, a + z⟩, roots := sl ++ (rs.lookup (a + z)).getD [] }]
      | .ret => pure [{ pt := ⟨.ret, a⟩, roots := t.result, frameless := true }]
      | _ => pure []
    let tl ← msK t rs ls (k + 1) (some i.flow) rest lr
    pure ((entry ++ own) :: tl)

/-- **`fnMapsW`, structurally** (`fnMapsW_eq_K`). -/
def fnMapsWK (t : FnTags) (items : List Item) (live : Array (List Int)) :
    Except String (List RootMap) := do
  let pre ← t.paramPts.zipIdx.mapM fun (l, j) => match labelAddr items l with
    | some a => pure { pt := ⟨.blockEntry, a⟩, roots := t.params, frameless := j == 0 }
    | none => throw s!"{t.bodyStart}: no label {l}"
  let body := bodyOf t items
  let is := insOf body
  let ls := leadersK body
  let grow ← match t.growStub with
    | none => pure none
    | some l => match growCall items l with
      | some c => pure (some c)
      | none => throw s!"{t.bodyStart}: no call after the grow stub {l}"
  let rs ← siteRes t is
  let calls := rs.map (·.1) ++ (grow.map fun (a, z, _) => a + z).toList
  for (ra, _) in t.stackmap do
    unless calls.contains ra do throw s!"{t.bodyStart}: scc_stackmap entry at {ra} is no call's return address"
  let ms ← msK t rs ls 0 none is.toList live.toList
  let gm ← match grow with
    | some (a, z, _) => do
      let sl ← callRoots t (a + z)
      pure [{ pt := ⟨.call, a + z⟩, roots := sl : RootMap }]
    | none => pure []
  pure (pre ++ ms.flatten ++ gm)

/-- `fnMapsW`' maps over the body from `k` are `msK` on the suffix from `k`. -/
theorem msK_eq (t : FnTags) (rs : List (Nat × List (Loc × Tag))) (ls : List Nat)
    (is : Array (Nat × Nat × Ins)) (live : Array (List Int)) :
    ∀ (suf : List (Nat × Nat × Ins)) (k : Nat) (prev : Option Flow), is.toList.drop k = suf →
    prev = (if k = 0 then none else some (is[k - 1]!).2.2.flow) →
    (List.range' k suf.length).mapM (fun k => do
      let (a, z, i) := is[k]!
      let res : List (Loc × Tag) := if k = 0 then [] else match (is[k - 1]!).2.2.flow with
        | .call _ => (rs.lookup a).getD []
        | _ => []
      let entry : List RootMap :=
        if ls.contains k then [{ pt := ⟨.blockEntry, a⟩, roots := res ++ liveRoots t (live[k]!) }]
        else []
      let own : List RootMap ← match i.flow with
        | .call _ => do
          let sl ← callRoots t (a + z)
          pure [{ pt := ⟨.call, a + z⟩, roots := sl ++ (rs.lookup (a + z)).getD [] }]
        | .ret => pure [{ pt := ⟨.ret, a⟩, roots := t.result, frameless := true }]
        | _ => pure []
      pure (entry ++ own)) = msK t rs ls k prev suf (live.toList.drop k) := by
  intro suf
  induction suf with
  | nil => intro k prev _ _; simp [msK]
  | cons x rest ih =>
    intro k prev h hp
    obtain ⟨a, z, i⟩ := x
    have hk := arr_getElem!_of_drop_eq_cons h
    have h1 := drop_succ_of_drop_eq_cons h
    rw [List.length_cons, List.range'_succ, List.mapM_cons, ih (k + 1) (some i.flow) h1 (by simp [hk])]
    have hl : live[k]! = (live.toList.drop k).headD [] := by
      rw [getElem!_eq_getD_toList, headD_drop]
    have hlr : (live.toList.drop k).tail = live.toList.drop (k + 1) := by
      rw [List.tail_drop]
    subst hp
    simp only [msK, hk, hl]
    cases hd : live.toList.drop k with
    | nil =>
      have : live.toList.drop (k + 1) = [] := by rw [← hlr, hd]; rfl
      rw [this]
      cases k with
      | zero => cases i.flow <;> simp [bind_map_left]
      | succ n =>
        cases hq : (is[n]!).2.2.flow <;> cases i.flow <;> simp [hq, bind_map_left]
    | cons x xs =>
      have : live.toList.drop (k + 1) = xs := by rw [← hlr, hd]; rfl
      rw [this]
      cases k with
      | zero => cases i.flow <;> simp [bind_map_left]
      | succ n =>
        cases hq : (is[n]!).2.2.flow <;> cases i.flow <;> simp [hq, bind_map_left]

/-- `msK` over the whole body is `fnMapsW`' maps over the body. -/
theorem msK_eq0 (t : FnTags) (rs : List (Nat × List (Loc × Tag))) (ls : List Nat)
    (is : Array (Nat × Nat × Ins)) (live : Array (List Int)) :
    msK t rs ls 0 none is.toList live.toList = (List.range is.size).mapM (fun k => do
      let (a, z, i) := is[k]!
      let res : List (Loc × Tag) := if k = 0 then [] else match (is[k - 1]!).2.2.flow with
        | .call _ => (rs.lookup a).getD []
        | _ => []
      let entry : List RootMap :=
        if ls.contains k then [{ pt := ⟨.blockEntry, a⟩, roots := res ++ liveRoots t (live[k]!) }]
        else []
      let own : List RootMap ← match i.flow with
        | .call _ => do
          let sl ← callRoots t (a + z)
          pure [{ pt := ⟨.call, a + z⟩, roots := sl ++ (rs.lookup (a + z)).getD [] }]
        | .ret => pure [{ pt := ⟨.ret, a⟩, roots := t.result, frameless := true }]
        | _ => pure []
      pure (entry ++ own)) := by
  have h := msK_eq t rs ls is live is.toList 0 none (by simp) (by simp)
  rw [List.drop_zero, Array.length_toList] at h
  rw [List.range_eq_range']; exact h.symm

/-- **`fnMapsW` is `fnMapsWK`.** -/
theorem fnMapsW_eq_K (t : FnTags) (items : List Item) (live : Array (List Int)) :
    fnMapsW t items live = fnMapsWK t items live := by
  unfold fnMapsW fnMapsWK
  simp only [leaders_eq_K, msK_eq0]
  rfl

/-! ## The tables -/

/-- **`computeW`, structurally** (`computeW_eq_K`). -/
def computeWK (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) :
    Except String Tables := do
  stubsOk fns items
  unless ws.length == fns.length do throw s!"{ws.length} liveness witnesses for {fns.length} functions"
  let ms ← (fns.zip ws).mapM fun (t, w) => fnMapsWK t items w
  let os ← (fns.zip ms).mapM fun (t, m) => outSuccs t items (m.map (·.pt.addr))
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) ms.flatten,
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr))
           (fns.flatMap (fun t => fnSuccsK t items) ++ os.flatten) }

/-- **`computeW` is `computeWK`.** -/
theorem computeW_eq_K (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) :
    computeW fns items ws = computeWK fns items ws := by
  unfold computeW computeWK
  simp only [fnMapsW_eq_K, fnSuccs_eq_K]

/-- info: 'Scc.Cert.Maps.leaders_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leaders_eq_K
/-- info: 'Scc.Cert.Maps.fnSuccs_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSuccs_eq_K
/-- info: 'Scc.Cert.Maps.fnMapsW_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnMapsW_eq_K
/-- info: 'Scc.Cert.Maps.computeW_eq_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms computeW_eq_K

/-! # Second round: numbered labels, leader pointers, one-pass witness entries

The forms above still compare labels as strings (`List.lookup` on `String` keys walks the UTF-8
bytes of every entry), test leaders with `ls.contains k` at every instruction, drop each leader's
suffix from the start, and look witness entries up with `getD`; `maxRank` and `fuelOf` fold lazily.
On a function of 1300 instructions those checks need more than 6 GB. The `…E` forms below number
the labels (`enc`), walk the sorted leaders with a pointer (the order is checked, `sortedLt`, with
the form above as the fallback), drop incrementally, carry each successor's witness and rank
entries (`labelWE`, `succE`), take the maximum rank strictly and decide the fuel bound by the
instruction count when it suffices. Each is proved equal to the original for all inputs
(`fnSuccs_eq_E`, `fnMapsW_eq_E`, `computeW_eq_E`, `stubsOk_eq_E`, `liveOk_eq_E`, `leastOk_eq_E`). -/

/-! ## Labels as numbers -/

/-- The digit step of `enc`. -/
def encStep (n : Nat) (b : UInt8) : Nat := n * 256 + b.toNat

/-- **A label as a number**: its UTF-8 bytes as base-256 digits after a leading 1 (injective,
`enc_inj`). The kernel compares two such numbers in one step, two strings byte by byte. -/
def enc (s : String) : Nat := s.toUTF8.data.toList.foldl encStep 1

theorem foldl_encStep_pos : ∀ (l : List UInt8) (n : Nat), 1 ≤ n → 1 ≤ l.foldl encStep n
  | [], _, h => h
  | b :: l, n, h => foldl_encStep_pos l _ (by unfold encStep; omega)

/-- `enc`'s fold, on the reversed digits. -/
def encR (n : Nat) : List UInt8 → Nat
  | [] => n
  | b :: l => encR n l * 256 + b.toNat

theorem foldl_encStep_eq (l : List UInt8) (n : Nat) : l.foldl encStep n = encR n l.reverse := by
  rw [List.foldl_eq_foldr_reverse]
  induction l.reverse with
  | nil => rfl
  | cons b l ih => rw [List.foldr_cons, encR, ih]; rfl

theorem encR_pos : ∀ (l : List UInt8), 1 ≤ encR 1 l
  | [] => Nat.le_refl _
  | b :: l => by have := encR_pos l; simp only [encR]; omega

theorem encR_inj : ∀ (l l' : List UInt8), encR 1 l = encR 1 l' → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by have := encR_pos l'; simp only [encR] at h; omega
  | b :: l, [], h => by have := encR_pos l; simp only [encR] at h; omega
  | b :: l, b' :: l', h => by
    simp only [encR] at h
    have hb := b.toNat_lt
    have hb' := b'.toNat_lt
    have h1 : encR 1 l = encR 1 l' := by omega
    have h2 : b.toNat = b'.toNat := by omega
    rw [encR_inj l l' h1, UInt8.toNat_inj.mp h2]

theorem enc_inj {s t : String} (h : enc s = enc t) : s = t := by
  unfold enc at h
  rw [foldl_encStep_eq, foldl_encStep_eq] at h
  have h1 := List.reverse_inj.mp (encR_inj _ _ h)
  have h2 : s.toByteArray = t.toByteArray := ByteArray.ext (Array.toList_inj.mp h1)
  exact String.toByteArray_inj.mp h2

theorem enc_beq (s t : String) : (enc s == enc t) = (s == t) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨enc_inj, congrArg enc⟩

/-- Looking up a label's number in a table keyed by numbers is looking up the label. -/
theorem lookup_map_enc {β γ : Type} (g : β → γ) (s : String) :
    ∀ l : List (String × β), (l.map fun p => (enc p.1, g p.2)).lookup (enc s) = (l.lookup s).map g
  | [] => rfl
  | (x, b) :: l => by
    simp only [List.map_cons, List.lookup_cons, enc_beq]
    cases s == x
    · exact lookup_map_enc g s l
    · rfl

/-- `labelIdxGo` with numbered labels. -/
def labelIdxE : List Item → Nat → List (Nat × Nat)
  | [], _ => []
  | .label _ l :: rest, c => (enc l, c) :: labelIdxE rest c
  | .ins _ _ _ :: rest, c => labelIdxE rest (c + 1)

theorem labelIdxE_eq : ∀ (body : List Item) (c : Nat),
    labelIdxE body c = (labelIdxGo body c).map fun p => (enc p.1, p.2)
  | [], _ => rfl
  | .label _ l :: rest, c => by simp only [labelIdxE, labelIdxGo, List.map_cons, labelIdxE_eq rest c]
  | .ins _ _ _ :: rest, c => by simp only [labelIdxE, labelIdxGo, labelIdxE_eq rest (c + 1)]

/-- `labelAddrK.go` with numbered labels. -/
def labelAddrE : List Item → List String → List (Nat × Nat)
  | [], _ => []
  | .label _ l :: rest, pend => labelAddrE rest (l :: pend)
  | .ins a _ _ :: rest, pend => (pend.reverse.map fun l => (enc l, a)) ++ labelAddrE rest []

theorem labelAddrE_eq : ∀ (body : List Item) (pend : List String),
    labelAddrE body pend = (labelAddrK.go body pend).map fun p => (enc p.1, p.2)
  | [], _ => rfl
  | .label _ l :: rest, pend => by simp only [labelAddrE, labelAddrK.go, labelAddrE_eq rest (l :: pend)]
  | .ins a _ _ :: rest, pend => by
    simp only [labelAddrE, labelAddrK.go, List.map_append, List.map_map, labelAddrE_eq rest []]
    rfl

/-- `targets` with numbered labels. -/
def targetsE (body : List Item) : List Nat :=
  let is := insL body
  let lix := labelIdxE body 0
  (is.filterMap fun (_, _, i) => match i.flow with
    | .jmp l | .jcc l => lix.lookup (enc l) | _ => none).filter (· < is.length)

theorem targets_eq_E (body : List Item) : targets body = targetsE body := by
  unfold targets targetsE
  have hs : (insOf body).size = (insL body).length := by rw [← insOf_toList]; simp
  simp only [insOf_toList, hs, labelIdx_eq, labelIdxE_eq]
  congr 2
  funext x
  obtain ⟨a, z, i⟩ := x
  cases i.flow <;> simp [lookup_map_enc (fun x => x)]

/-- **`leadersK` with numbered labels** (`leadersK_eq_E`). -/
def leadersE (body : List Item) : List Nat :=
  let l := insL body
  let tg := targetsE body
  sortStable (fun a b => decide (a ≤ b)) ((if l.length = 0 then [] else [0]) ++ tg ++ afterK tg 0 l).eraseDups

theorem leadersK_eq_E (body : List Item) : leadersK body = leadersE body := by
  unfold leadersK leadersE
  simp only [insOf_toList, targets_eq_E]

/-! ## Sorted leaders -/

/-- `l` is strictly increasing (checked, so that the forms below can rely on it). -/
def sortedLt : List Nat → Bool
  | a :: b :: r => Nat.blt a b && sortedLt (b :: r)
  | _ => true

theorem sortedLt_pairwise : ∀ {l : List Nat}, sortedLt l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: r, h => by
    simp only [sortedLt, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := sortedLt_pairwise h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

/-! ## Block successors -/

/-- `fnSuccsWalkK` with numbered labels, the next leader `nxt` (0: none) in place of the
leaders. -/
def fnSuccsWalkE (lxa : List (Nat × Nat)) (nxt : Nat) (tg : List Nat) :
    Nat → List (Nat × Nat × Ins) → List Nat × List String
  | _, [] => ([], [])
  | k, (a, z, i) :: rest =>
    let nxtA : List Nat := match rest with | (b, _, _) :: _ => [b] | [] => []
    let tgt (l : String) : List Nat := (lxa.lookup (enc l)).toList
    match i.flow with
    | .call _ => ([a + z], [])
    | .ret => ([a], [])
    | .stop => ([], [])
    | .jcc l =>
      match rest with
      | (_, _, j) :: _ =>
        if !tg.contains (k + 1) && (match j.flow with | .jmp _ => true | _ => false) then
          let tl := match j.flow with
            | .jmp m => if (tgt m).isEmpty then [m] else []
            | _ => []
          (tgt l ++ (match j.flow with | .jmp m => tgt m | _ => []), tl)
        else (tgt l ++ nxtA, [])
      | [] => (tgt l, [])
    | .jmp l => match tgt l with
      | [] => ([], [l])
      | js => (js, [])
    | .fall => if k + 1 == nxt then (nxtA, []) else fnSuccsWalkE lxa nxt tg (k + 1) rest

theorem fnSuccsWalkE_eq (lxaK : List (String × Nat)) (ls tg : List Nat) (nxt : Nat) :
    ∀ (suf : List (Nat × Nat × Ins)) (k : Nat), (nxt = 0 ∨ k < nxt) →
    (∀ j, k < j → (nxt = 0 ∨ j ≤ nxt) → (j ∈ ls ↔ j = nxt)) →
    fnSuccsWalkE (lxaK.map fun p => (enc p.1, p.2)) nxt tg k suf = fnSuccsWalkK lxaK ls tg k suf := by
  intro suf
  induction suf with
  | nil => intro k _ _; rfl
  | cons x rest ih =>
    intro k hn hH
    obtain ⟨a, z, i⟩ := x
    have hl : ∀ l, ((lxaK.map fun p => (enc p.1, p.2)).lookup (enc l)) = lxaK.lookup l := fun l => by
      simpa using lookup_map_enc (fun x => x) l lxaK
    have hc : (k + 1 == nxt) = ls.contains (k + 1) := by
      have h1 := hH (k + 1) (Nat.lt_succ_self k) (by omega)
      rw [Bool.eq_iff_iff, beq_iff_eq, List.contains_iff_mem]
      exact h1.symm
    cases hf : i.flow with
    | fall =>
      simp only [fnSuccsWalkE, fnSuccsWalkK, hf, hc]
      split
      · rfl
      · rename_i hnot
        apply ih (k + 1)
        · have : k + 1 ≠ nxt := by
            intro e; apply hnot; rw [← hc, e]; simp
          omega
        · intro j hj hj'
          exact hH j (by omega) hj'
    | jmp l =>
      simp only [fnSuccsWalkE, fnSuccsWalkK, hf, hl]
      all_goals cases (lxaK.lookup l).toList <;> rfl
    | jcc l =>
      simp only [fnSuccsWalkE, fnSuccsWalkK, hf, hl]
      all_goals
        rcases rest with _ | ⟨⟨b, w, j⟩, rest'⟩
        · rfl
        · cases j.flow <;> rfl
    | _ => simp only [fnSuccsWalkE, fnSuccsWalkK, hf]

/-- `fnSuccsK`'s map over the leaders, from leader to leader: each leader's suffix is dropped from
the previous one's (`prev`), and its walk stops at the next leader. -/
def succsGo (lxa : List (Nat × Nat)) (tg : List Nat) :
    Nat → List (Nat × Nat × Ins) → List Nat → List Succs
  | _, _, [] => []
  | prev, suf, k :: rest =>
    let s := suf.drop (k - prev)
    let a := match s with | (a, _, _) :: _ => a | [] => 0
    let (nx, tl) := fnSuccsWalkE lxa (rest.headD 0) tg k s
    ⟨a, nx, tl⟩ :: succsGo lxa tg k s rest

theorem succsGo_eq (L : List (Nat × Nat × Ins)) (lxaK : List (String × Nat)) (ls0 tg : List Nat)
    (hs : ls0.Pairwise (· < ·)) :
    ∀ (ls pre : List Nat) (prev : Nat), ls0 = pre ++ ls → (∀ x ∈ pre, x ≤ prev) →
    (∀ x ∈ ls, prev ≤ x) →
    succsGo (lxaK.map fun p => (enc p.1, p.2)) tg prev (L.drop prev) ls =
      ls.map fun k =>
        let suf := L.drop k
        let a := match suf with | (a, _, _) :: _ => a | [] => 0
        let (nx, tl) := fnSuccsWalkK lxaK ls0 tg k suf
        ⟨a, nx, tl⟩
  | [], _, _, _, _, _ => rfl
  | k :: rest, pre, prev, h0, hpre, hge => by
    have hk : prev ≤ k := hge k (List.mem_cons_self ..)
    have hd : (L.drop prev).drop (k - prev) = L.drop k := by
      rw [List.drop_drop]; congr 1; omega
    have hs' : (pre ++ k :: rest).Pairwise (· < ·) := h0 ▸ hs
    rw [List.pairwise_append] at hs'
    obtain ⟨_, hsr, hx⟩ := hs'
    have hkr : ∀ x ∈ rest, k < x := fun x hx' => List.rel_of_pairwise_cons hsr hx'
    have hpk : ∀ x ∈ pre, x < k := fun x hx' => hx x hx' k (List.mem_cons_self ..)
    have hw : fnSuccsWalkE (lxaK.map fun p => (enc p.1, p.2)) (rest.headD 0) tg k (L.drop k) =
        fnSuccsWalkK lxaK ls0 tg k (L.drop k) := by
      apply fnSuccsWalkE_eq
      · cases rest with
        | nil => left; rfl
        | cons h t => right; exact hkr h (List.mem_cons_self ..)
      · intro j hj hjn
        rw [h0, List.mem_append, List.mem_cons]
        constructor
        · rintro (hp | rfl | hr)
          · exact absurd (hpk j hp) (by omega)
          · omega
          · cases rest with
            | nil => simp at hr
            | cons h t =>
              rcases List.mem_cons.mp hr with rfl | ht
              · rfl
              · have h2 := (List.pairwise_cons.mp (List.pairwise_cons.mp hsr).2).1 j ht
                have hh := hkr h (List.mem_cons_self ..)
                have e : (h :: t).headD 0 = h := rfl
                rw [e] at hjn
                omega
        · intro e
          cases rest with
          | nil =>
            have e' : ([] : List Nat).headD 0 = 0 := rfl
            rw [e'] at e; omega
          | cons h t =>
            have e' : (h :: t).headD 0 = h := rfl
            rw [e'] at e; right; right; exact e ▸ List.mem_cons_self ..
    simp only [succsGo, List.map_cons, hd, hw]
    congr 1
    apply succsGo_eq L lxaK ls0 tg hs rest (pre ++ [k]) k (by simp [h0])
    · intro x hx'
      rcases List.mem_append.mp hx' with hp | hk'
      · exact Nat.le_of_lt (hpk x hp)
      · simp at hk'; omega
    · intro x hx'; exact Nat.le_of_lt (hkr x hx')

/-- **`fnSuccsK` with numbered labels, walking from leader to leader** (`fnSuccsK_eq_E`); the
leaders' order is checked (`sortedLt`), `fnSuccsK` itself if it fails (it does not: `leaders`
sorts them). -/
def fnSuccsE (t : FnTags) (items : List Item) : List Succs :=
  let body := bodyOf t items
  let ls := leadersE body
  match sortedLt ls with
  | true => succsGo (labelAddrE body []) (targetsE body) 0 (insL body) ls
  | false => fnSuccsK t items

theorem fnSuccsK_eq_E (t : FnTags) (items : List Item) : fnSuccsK t items = fnSuccsE t items := by
  cases h : sortedLt (leadersE (bodyOf t items))
  · simp only [fnSuccsE, h]
  · simp only [fnSuccsE, h]
    unfold fnSuccsK
    simp only [leadersK_eq_E, targets_eq_E, insOf_toList, labelAddrK, labelAddrE_eq]
    rw [← List.drop_zero (l := insL (bodyOf t items))]
    exact (succsGo_eq _ _ _ _ (sortedLt_pairwise h) _ [] 0 rfl (by simp) (fun _ _ => Nat.zero_le _)).symm

theorem fnSuccs_eq_E (t : FnTags) (items : List Item) : fnSuccs t items = fnSuccsE t items :=
  (fnSuccs_eq_K t items).trans (fnSuccsK_eq_E t items)

/-! ## Root maps -/

/-- Whether instruction `k` is the next leader `ptr` points at, and the pointer after `k`. -/
def ptrStep (ptr : List Nat) (k : Nat) : Bool × List Nat :=
  match ptr with
  | h :: tl => if h == k then (true, tl) else (false, ptr)
  | [] => (false, [])

/-- `msK` with the leaders from `k` on as a pointer (`ptr`, increasing) in place of
`ls.contains k`. -/
def msE (t : FnTags) (rs : List (Nat × List (Loc × Tag))) :
    List Nat → Nat → Option Flow → List (Nat × Nat × Ins) → List (List Int) →
      Except String (List (List RootMap))
  | _, _, _, [], _ => pure []
  | ptr, k, prev, (a, z, i) :: rest, lv => do
    let (l0, lr) := match lv with | [] => (([] : List Int), ([] : List (List Int))) | x :: xs => (x, xs)
    let res : List (Loc × Tag) := match prev with
      | some (.call _) => (rs.lookup a).getD []
      | _ => []
    let entry : List RootMap :=
      if (ptrStep ptr k).1 then [{ pt := ⟨.blockEntry, a⟩, roots := res ++ liveRoots t l0 }]
      else []
    let own : List RootMap ← match i.flow with
      | .call _ => do
        let sl ← callRoots t (a + z)
        pure [{ pt := ⟨.call, a + z⟩, roots := sl ++ (rs.lookup (a + z)).getD [] }]
      | .ret => pure [{ pt := ⟨.ret, a⟩, roots := t.result, frameless := true }]
      | _ => pure []
    let tl ← msE t rs (ptrStep ptr k).2 (k + 1) (some i.flow) rest lr
    pure ((entry ++ own) :: tl)

theorem ptrStep_spec (ls ptr : List Nat) (k : Nat) (hp : ptr.Pairwise (· < ·))
    (hge : ∀ x ∈ ptr, k ≤ x) (hm : ∀ j, k ≤ j → (j ∈ ls ↔ j ∈ ptr)) :
    (ptrStep ptr k).1 = ls.contains k ∧ (ptrStep ptr k).2.Pairwise (· < ·) ∧
      (∀ x ∈ (ptrStep ptr k).2, k + 1 ≤ x) ∧
      (∀ j, k + 1 ≤ j → (j ∈ ls ↔ j ∈ (ptrStep ptr k).2)) := by
  have hc : ls.contains k = decide (k ∈ ptr) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_iff]; exact hm k (Nat.le_refl _)
  rw [hc]
  cases ptr with
  | nil =>
    simp only [ptrStep, List.not_mem_nil, decide_false, true_and, List.Pairwise.nil]
    refine ⟨fun x hx => hx.elim, fun j hj => ?_⟩
    simpa using hm j (by omega)
  | cons h tl =>
    have hh : k ≤ h := hge h (List.mem_cons_self ..)
    have htl : ∀ x ∈ tl, h < x := fun x hx => List.rel_of_pairwise_cons hp hx
    by_cases e : h = k
    · subst e
      simp only [ptrStep, beq_self_eq_true, ite_true, List.mem_cons_self, decide_true, true_and]
      refine ⟨(List.pairwise_cons.mp hp).2, fun x hx => htl x hx, fun j hj => ?_⟩
      rw [hm j (by omega), List.mem_cons]
      constructor
      · rintro (rfl | hj'); · omega
        · exact hj'
      · exact Or.inr
    · have hne : (h == k) = false := by simpa using e
      have hk : k ∉ h :: tl := by
        intro hk; rcases List.mem_cons.mp hk with e' | hk
        · exact e e'.symm
        · have := htl k hk; omega
      simp only [ptrStep, hne, Bool.false_eq_true, ite_false, hk, decide_false, true_and]
      refine ⟨hp, fun x hx => ?_, fun j hj => hm j (by omega)⟩
      have := hge x hx
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · omega
      · exact absurd (h1 ▸ hx) hk

theorem msE_eq (t : FnTags) (rs : List (Nat × List (Loc × Tag))) (ls : List Nat) :
    ∀ (suf : List (Nat × Nat × Ins)) (ptr : List Nat) (k : Nat) (prev : Option Flow) (lv : List (List Int)),
    ptr.Pairwise (· < ·) → (∀ x ∈ ptr, k ≤ x) → (∀ j, k ≤ j → (j ∈ ls ↔ j ∈ ptr)) →
    msE t rs ptr k prev suf lv = msK t rs ls k prev suf lv := by
  intro suf
  induction suf with
  | nil => intro _ _ _ _ _ _ _; rfl
  | cons x rest ih =>
    intro ptr k prev lv hp hge hm
    obtain ⟨a, z, i⟩ := x
    obtain ⟨h1, h2, h3, h4⟩ := ptrStep_spec ls ptr k hp hge hm
    simp only [msE, msK, h1]
    cases lv <;> simp only [ih _ (k + 1) _ _ h2 h3 h4] <;> cases i.flow <;> rfl

/-- `msK` from the first instruction, with the leaders' order checked (`sortedLt`) for the
pointer form. -/
def msSel (t : FnTags) (rs : List (Nat × List (Loc × Tag))) (ls : List Nat)
    (is : List (Nat × Nat × Ins)) (lv : List (List Int)) : Except String (List (List RootMap)) :=
  match sortedLt ls with
  | true => msE t rs ls 0 none is lv
  | false => msK t rs ls 0 none is lv

theorem msK_eq_sel (t : FnTags) (rs : List (Nat × List (Loc × Tag))) (ls : List Nat)
    (is : List (Nat × Nat × Ins)) (lv : List (List Int)) :
    msK t rs ls 0 none is lv = msSel t rs ls is lv := by
  cases h : sortedLt ls
  · simp only [msSel, h]
  · simp only [msSel, h]
    exact (msE_eq t rs ls is ls 0 none lv (sortedLt_pairwise h) (fun _ _ => Nat.zero_le _)
      (fun _ _ => Iff.rfl)).symm

/-- **`fnMapsWK` with numbered labels and the leaders as a pointer** (`fnMapsWK_eq_E`). -/
def fnMapsWE (t : FnTags) (items : List Item) (live : Array (List Int)) :
    Except String (List RootMap) := do
  let pre ← t.paramPts.zipIdx.mapM fun (l, j) => match labelAddr items l with
    | some a => pure { pt := ⟨.blockEntry, a⟩, roots := t.params, frameless := j == 0 }
    | none => throw s!"{t.bodyStart}: no label {l}"
  let body := bodyOf t items
  let is := insOf body
  let ls := leadersE body
  let grow ← match t.growStub with
    | none => pure none
    | some l => match growCall items l with
      | some c => pure (some c)
      | none => throw s!"{t.bodyStart}: no call after the grow stub {l}"
  let rs ← siteRes t is
  let calls := rs.map (·.1) ++ (grow.map fun (a, z, _) => a + z).toList
  for (ra, _) in t.stackmap do
    unless calls.contains ra do throw s!"{t.bodyStart}: scc_stackmap entry at {ra} is no call's return address"
  let ms ← msSel t rs ls is.toList live.toList
  let gm ← match grow with
    | some (a, z, _) => do
      let sl ← callRoots t (a + z)
      pure [{ pt := ⟨.call, a + z⟩, roots := sl : RootMap }]
    | none => pure []
  pure (pre ++ ms.flatten ++ gm)

theorem fnMapsWK_eq_E (t : FnTags) (items : List Item) (live : Array (List Int)) :
    fnMapsWK t items live = fnMapsWE t items live := by
  unfold fnMapsWK fnMapsWE
  simp only [leadersK_eq_E, msK_eq_sel]
  all_goals rfl

theorem fnMapsW_eq_E (t : FnTags) (items : List Item) (live : Array (List Int)) :
    fnMapsW t items live = fnMapsWE t items live :=
  (fnMapsW_eq_K t items live).trans (fnMapsWK_eq_E t items live)

/-! ## Stubs -/

/-- The items after each label of `items`, keyed by the label's number, in order. -/
def labelTails : List Item → List (Nat × List Item)
  | [] => []
  | .label _ m :: r => (enc m, r) :: labelTails r
  | .ins _ _ _ :: r => labelTails r

theorem labelTails_lookup (l : String) (p : Item → Bool)
    (hl : ∀ a m, p (.label a m) = (m != l)) (hi : ∀ a z i, p (.ins a z i) = true) :
    ∀ items : List Item, (labelTails items).lookup (enc l) = (items.dropWhile p).tail?
  | [] => rfl
  | .label a m :: r => by
    rw [List.dropWhile_cons, hl, labelTails, List.lookup_cons, enc_beq]
    by_cases h : l = m
    · subst h
      rw [beq_self_eq_true, bne_self_eq_false]
      rfl
    · have h1 : (l == m) = false := by simpa using h
      have h2 : (m != l) = true := by rw [bne_iff_ne]; exact fun e => h e.symm
      simp only [h1, h2, ↓reduceIte]
      exact labelTails_lookup l p hl hi r
  | .ins a z i :: r => by
    rw [List.dropWhile_cons, hi, labelTails]
    simp only [↓reduceIte]
    exact labelTails_lookup l p hl hi r

/-- `badStub?` with numbered labels, the stubs found in `tails` (`labelTails items`). -/
def badStubE (t : FnTags) (items : List Item) (tails : List (Nat × List Item)) : Option (Nat × String) :=
  let body := bodyOf t items
  let is := insL body
  let lix := labelIdxE body 0
  is.findSome? fun (a, _, i) => match i.flow with
    | .jcc l =>
      if (match lix.lookup (enc l) with | some j => decide (j < is.length) | none => false) then none
      else match tails.lookup (enc l) with
        | some after => if stubShape l after then none else some (a, l)
        | none => some (a, l)
    | _ => none

/-- **`stubsOk` with numbered labels** (`stubsOk_eq_E`). -/
def stubsOkE (fns : List FnTags) (items : List Item) : Except String Unit :=
  let tails := labelTails items
  match fns.findSome? fun t => (badStubE t items tails).map fun p => (t.bodyStart, p) with
  | some (b, a, l) => .error s!"{b}: the conditional branch at {a} leaves the body to {l}, no abort or child stub"
  | none => .ok ()

theorem badStub?_eq_E (t : FnTags) (items : List Item) :
    badStub? t items = badStubE t items (labelTails items) := by
  unfold badStub? badStubE
  have hs : (insOf (bodyOf t items)).size = (insL (bodyOf t items)).length := by rw [← insOf_toList]; simp
  simp only [insOf_toList, hs, labelIdx_eq, labelIdxE_eq]
  congr 1
  funext x
  obtain ⟨a, z, i⟩ := x
  cases i.flow with
  | jcc l =>
    simp only [lookup_map_enc (fun x => x) l, Option.map_id']
    congr 1
    split
    · rename_i h after heq
      rw [labelTails_lookup l _ ?hl ?hi items, heq]
      · rfl
      · intros; rfl
      · intros; rfl
    · rename_i heq
      rw [labelTails_lookup l _ ?hl2 ?hi2 items, heq]
      · rfl
      · intros; rfl
      · intros; rfl
  | _ => rfl

theorem stubsOk_eq_E (fns : List FnTags) (items : List Item) : stubsOk fns items = stubsOkE fns items := by
  unfold stubsOk stubsOkE
  simp only [badStub?_eq_E]
  all_goals rfl

/-! ## The tables -/

/-- **`computeWK` with the forms above** (`computeWK_eq_E`). -/
def computeWE (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) :
    Except String Tables := do
  stubsOkE fns items
  unless ws.length == fns.length do throw s!"{ws.length} liveness witnesses for {fns.length} functions"
  let ms ← (fns.zip ws).mapM fun (t, w) => fnMapsWE t items w
  let os ← (fns.zip ms).mapM fun (t, m) => outSuccs t items (m.map (·.pt.addr))
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) ms.flatten,
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr))
           (fns.flatMap (fun t => fnSuccsE t items) ++ os.flatten) }

theorem computeWK_eq_E (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) :
    computeWK fns items ws = computeWE fns items ws := by
  unfold computeWK computeWE
  simp only [stubsOk_eq_E, fnMapsWK_eq_E, fnSuccsK_eq_E]

theorem computeW_eq_E (fns : List FnTags) (items : List Item) (ws : List (Array (List Int))) :
    computeW fns items ws = computeWE fns items ws :=
  (computeW_eq_K fns items ws).trans (computeWK_eq_E fns items ws)

/-! ## Liveness witnesses -/

/-- Each label's number with the index of the next instruction and the witness entry and rank
entry there (`ws`, `rs`: the entries from that instruction on), in one pass. -/
def labelWE : List Item → Nat → List (List Int) → List (List Nat) →
    List (Nat × Nat × List Int × List Nat)
  | [], _, _, _ => []
  | .label _ l :: rest, c, ws, rs => (enc l, c, ws.headD [], rs.headD []) :: labelWE rest c ws rs
  | .ins _ _ _ :: rest, c, ws, rs => labelWE rest (c + 1) ws.tail rs.tail

theorem labelWE_eq (wl : List (List Int)) (rl : List (List Nat)) :
    ∀ (body : List Item) (c : Nat), labelWE body c (wl.drop c) (rl.drop c) =
      (labelIdxGo body c).map fun p => (enc p.1, p.2, wl.getD p.2 [], rl.getD p.2 [])
  | [], _ => rfl
  | .label _ l :: rest, c => by
    simp only [labelWE, labelIdxGo, List.map_cons, headD_drop, labelWE_eq wl rl rest c]
  | .ins _ _ _ :: rest, c => by
    simp only [labelWE, labelIdxGo, List.tail_drop, labelWE_eq wl rl rest (c + 1)]

/-- `succIdx` with each successor's witness and rank entries (`wn`, `rn`: the next
instruction's), the targets' from `tab` (`labelWE`). -/
def succE (tab : List (Nat × Nat × List Int × List Nat)) (n k : Nat) (i : Ins)
    (wn : List Int) (rn : List Nat) : List (Nat × List Int × List Nat) :=
  let nxt := if k + 1 < n then [(k + 1, wn, rn)] else []
  let tgt (l : String) := match tab.lookup (enc l) with
    | some (j, w, r) => if j < n then [(j, w, r)] else []
    | none => []
  match i.flow with
  | .fall | .call _ => nxt
  | .jmp l => tgt l
  | .jcc l => tgt l ++ nxt
  | .ret | .stop => []

theorem succE_eq (lix : List (String × Nat)) (wl : List (List Int)) (rl : List (List Nat))
    (n k : Nat) (i : Ins) :
    succE (lix.map fun p => (enc p.1, p.2, wl.getD p.2 [], rl.getD p.2 [])) n k i
      (wl.getD (k + 1) []) (rl.getD (k + 1) []) =
      (succIdx lix n k i).map fun j => (j, wl.getD j [], rl.getD j []) := by
  have ht : ∀ l, (match (lix.map fun p => (enc p.1, p.2, wl.getD p.2 [], rl.getD p.2 [])).lookup (enc l) with
      | some (j, w, r) => if j < n then [(j, w, r)] else []
      | none => []) =
      (match lix.lookup l with | some j => if j < n then [j] else [] | none => []).map
        fun j => (j, wl.getD j [], rl.getD j []) := by
    intro l
    rw [lookup_map_enc (fun j => (j, wl.getD j [], rl.getD j [])) l lix]
    cases lix.lookup l with
    | none => rfl
    | some j => by_cases h : j < n <;> simp [h]
  unfold succE succIdx
  cases i.flow with
  | fall => by_cases h : k + 1 < n <;> simp [h]
  | call _ => by_cases h : k + 1 < n <;> simp [h]
  | jmp l => simp only [ht]; rfl
  | jcc l =>
    simp only [ht, List.map_append]
    by_cases h : k + 1 < n <;> simp [h] <;> rfl
  | ret => rfl
  | stop => rfl

/-- `liveOkGo` on the successors' entries from `succE` (no lookup in the witness; `rs`: the rank
entries from `k` on, passed along for `succE`). -/
def liveGoE (taken : List Int) (tab : List (Nat × Nat × List Int × List Nat)) (n : Nat) :
    List (Nat × Nat × Ins) → List (List Int) → List (List Nat) → Nat → Bool
  | [], [], _, _ => true
  | (_, _, i) :: is, wk :: ws, rs, k =>
    subI taken wk && subI i.reads wk &&
      (succE tab n k i (ws.headD []) (rs.tail.headD [])).all (fun (_, e, _) =>
        subI (e.filter fun o => !i.writes.contains o) wk) &&
      liveGoE taken tab n is ws rs.tail (k + 1)
  | _, _, _, _ => false

theorem liveGoE_eq (taken : List Int) (lix : List (String × Nat)) (n : Nat) (wl : List (List Int))
    (rl : List (List Nat)) :
    ∀ (is : List (Nat × Nat × Ins)) (ws : List (List Int)) (k : Nat), ws = wl.drop k →
    liveGoE taken (lix.map fun p => (enc p.1, p.2, wl.getD p.2 [], rl.getD p.2 [])) n is ws (rl.drop k) k =
      liveOkGo taken lix n wl is ws k
  | [], [], _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | (a, z, i) :: is, wk :: ws, k, hws => by
    have hws' : ws = wl.drop (k + 1) := by
      have := congrArg List.tail hws; simpa [List.tail_drop] using this
    have hh : ws.headD [] = wl.getD (k + 1) [] := by rw [hws', headD_drop]
    have hr : (rl.drop k).tail.headD [] = rl.getD (k + 1) [] := by rw [List.tail_drop, headD_drop]
    simp only [liveGoE, liveOkGo, hh, List.tail_drop, headD_drop, succE_eq, List.all_map,
      liveGoE_eq taken lix n wl rl is ws (k + 1) hws']
    congr 3
    funext j
    by_cases e : j = k + 1 <;> simp [e]

/-- **`liveOk` on `succE`'s entries** (`liveOk_eq_E`). -/
def liveOkE (body : List Item) (w : Array (List Int)) : Bool :=
  let is := insL body
  let taken := is.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  let wl := w.toList
  liveGoE taken (labelWE body 0 wl []) is.length is wl [] 0

theorem liveOk_eq_E (body : List Item) (w : Array (List Int)) : liveOk body w = liveOkE body w := by
  unfold liveOk liveOkE
  have ht := labelWE_eq w.toList [] body 0
  simp only [List.drop_zero, List.drop_nil] at ht
  have hg := liveGoE_eq ((insL body).foldl (fun acc (_, _, i) => unionI acc i.takes) [])
    (labelIdxGo body 0) (insL body).length w.toList [] (insL body) w.toList 0 List.drop_zero.symm
  simp only [List.drop_nil] at hg
  simp only [insOf_toList, labelIdx_eq, ht, hg]

/-- `justGo` on `succE`'s entries. -/
def justGoE (taken : List Int) (tab : List (Nat × Nat × List Int × List Nat)) (n : Nat) :
    List (Nat × Nat × Ins) → List (List Int) → List (List Nat) → Nat → Bool
  | [], [], [], _ => true
  | (_, _, i) :: is, wk :: ws, rk :: rs, k =>
    Nat.beq wk.length rk.length &&
    (wk.zip rk).all (fun (o, r) => taken.contains o || i.reads.contains o ||
      (!i.writes.contains o && (succE tab n k i (ws.headD []) (rs.headD [])).any fun (_, we, re) =>
        lowerIn o r we re)) &&
    justGoE taken tab n is ws rs (k + 1)
  | _, _, _, _ => false

theorem justGoE_eq (taken : List Int) (lix : List (String × Nat)) (n : Nat) (wl : List (List Int))
    (rl : List (List Nat)) :
    ∀ (is : List (Nat × Nat × Ins)) (ws : List (List Int)) (rs : List (List Nat)) (k : Nat),
    ws = wl.drop k → rs = rl.drop k →
    justGoE taken (lix.map fun p => (enc p.1, p.2, wl.getD p.2 [], rl.getD p.2 [])) n is ws rs k =
      justGo taken lix n wl rl is ws rs k
  | [], [], [], _, _, _ => rfl
  | [], [], _ :: _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _ => rfl
  | (a, z, i) :: is, wk :: ws, rk :: rs, k, hws, hrs => by
    have hws' : ws = wl.drop (k + 1) := by
      have := congrArg List.tail hws; simpa [List.tail_drop] using this
    have hrs' : rs = rl.drop (k + 1) := by
      have := congrArg List.tail hrs; simpa [List.tail_drop] using this
    have hh : ws.headD [] = wl.getD (k + 1) [] := by rw [hws', headD_drop]
    have hr : rs.headD [] = rl.getD (k + 1) [] := by rw [hrs', headD_drop]
    simp only [justGoE, justGo, hh, hr, succE_eq, List.any_map,
      justGoE_eq taken lix n wl rl is ws rs (k + 1) hws' hrs']
    congr 3
    funext p
    obtain ⟨o, r⟩ := p
    congr 3
    funext j
    by_cases e : j = k + 1 <;> simp [e]

/-- `maxRank`'s inner fold, with the comparison taken before the recursion. -/
def maxGo : Nat → List Nat → Nat
  | m, [] => m
  | m, b :: bs => match Nat.ble m b with
    | true => maxGo b bs
    | false => maxGo m bs

/-- **`maxRank`, strict** (`maxRank_eq_S`): the kernel otherwise builds the folded `max` terms
before comparing. -/
def maxRankS : Nat → List (List Nat) → Nat
  | m, [] => m
  | m, l :: ls => maxRankS (maxGo m l) ls

theorem maxGo_eq : ∀ (m : Nat) (l : List Nat), maxGo m l = l.foldl max m
  | _, [] => rfl
  | m, b :: bs => by
    simp only [maxGo, List.foldl_cons, Nat.max_def]
    cases h : Nat.ble m b
    · have : ¬ m ≤ b := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; exact Bool.noConfusion h
      simp only [this, ite_false]; exact maxGo_eq m bs
    · have : m ≤ b := Nat.le_of_ble_eq_true h
      simp only [this, ite_true]; exact maxGo_eq b bs

theorem maxRankS_eq : ∀ (m : Nat) (r : List (List Nat)),
    maxRankS m r = r.foldl (fun m l => l.foldl max m) m
  | _, [] => rfl
  | m, l :: ls => by simp only [maxRankS, List.foldl_cons, maxGo_eq, maxRankS_eq _ ls]

theorem maxRank_eq_S (r : List (List Nat)) : maxRank r = maxRankS 0 r := by
  rw [maxRankS_eq]; rfl

theorem lt_fuelOf_of_le (body : List Item) (m : Nat) (h : m < (insL body).length + 1) :
    m < fuelOf body := by
  unfold fuelOf
  have hs : (insOf body).size = (insL body).length := by rw [← insOf_toList]; simp
  simp only [hs]
  exact Nat.lt_of_lt_of_le h (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

/-- **`leastOk` on `succE`'s entries, the maximum rank strict and the fuel bound decided by the
instruction count when it suffices** (`leastOk_eq_E`). -/
def leastOkE (body : List Item) (w : Array (List Int)) (r : List (List Nat)) : Bool :=
  let is := insL body
  let taken := is.foldl (fun acc (_, _, i) => unionI acc i.takes) []
  let wl := w.toList
  let tab := labelWE body 0 wl r
  let m := maxRankS 0 r
  liveGoE taken tab is.length is wl r 0 && justGoE taken tab is.length is wl r 0 &&
    (Nat.blt m (is.length + 1) || decide (m < fuelOf body))

theorem leastOk_eq_E (body : List Item) (w : Array (List Int)) (r : List (List Nat)) :
    leastOk body w r = leastOkE body w r := by
  unfold leastOk leastOkE liveOk justified
  have ht := labelWE_eq w.toList r body 0
  simp only [List.drop_zero] at ht
  have hg := liveGoE_eq ((insL body).foldl (fun acc (_, _, i) => unionI acc i.takes) [])
    (labelIdxGo body 0) (insL body).length w.toList r (insL body) w.toList 0 List.drop_zero.symm
  have hj := justGoE_eq ((insL body).foldl (fun acc (_, _, i) => unionI acc i.takes) [])
    (labelIdxGo body 0) (insL body).length w.toList r (insL body) w.toList r 0
    List.drop_zero.symm List.drop_zero.symm
  simp only [List.drop_zero] at hg
  have hf : (Nat.blt (maxRankS 0 r) ((insL body).length + 1) || decide (maxRankS 0 r < fuelOf body)) =
      decide (maxRankS 0 r < fuelOf body) := by
    cases h : Nat.blt (maxRankS 0 r) ((insL body).length + 1)
    · rfl
    · have := lt_fuelOf_of_le body _ (by simpa [Nat.blt_eq] using h)
      simp [this]
  simp only [insOf_toList, labelIdx_eq, ht, hg, hj, hf, maxRank_eq_S]

/-- info: 'Scc.Cert.Maps.fnSuccs_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnSuccs_eq_E
/-- info: 'Scc.Cert.Maps.fnMapsW_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnMapsW_eq_E
/-- info: 'Scc.Cert.Maps.computeW_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms computeW_eq_E
/-- info: 'Scc.Cert.Maps.stubsOk_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stubsOk_eq_E
/-- info: 'Scc.Cert.Maps.liveOk_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms liveOk_eq_E
/-- info: 'Scc.Cert.Maps.leastOk_eq_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms leastOk_eq_E

end Scc.Cert.Maps
