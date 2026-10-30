/-
**Each function's label in scc's x86-64 code cells, in order**
(`Scc.Emit.X64`): the emitter's items for a function stay in `.text`
(`textN`: no raw lines, no section or alignment directives), so
`textDirectives` keeps them in order, and the code cells
(`cellsOfEmitted`) are the header's directives, every function's (one
block per function, holding its label), then the rest. With `PlaceOK`'s
distinct labels (`labelsNodupL`), two functions of one name are one.

- `PreP`, `textN`: an action appending only items with a property, and the
  items that keep `.text`;
- `emitFunc_prep`, `emitFunc_label`: a function's items keep `.text` and
  hold its label;
- `emitFuncs_labels`: `emitFuncs`'s blocks, one per function;
- `textDirectives_append`: `textDirectives` of `.text` items then any;
- `lowerAll_cells`: the label cells of `cellsOfEmitted` are the header's,
  each function's block's in order, then the rest's;
- `labs_nodup_of_labelsNodupL`, `index_inj`: distinct labels, one index
  per function name.
-/
import Spike.Lib.LowerX64.EmitOut
import Scc.Lower.SpecX64
import Scc.Cert.PlaceDataX64

namespace Spike.Lib.LowerX64

open Scc.Emit.X64

/-- **`x` only appends items with `P`**: from any state it succeeds from,
the new output is some items (last first), each with `P`, followed by the
old one. -/
structure PreP (P : Item → Bool) {α : Type} (x : E α) : Prop where
  out : ∀ (s : S) (a : α) (s' : S), x s = .ok (a, s') →
    ∃ c : List Item, s'.out = c ++ s.out ∧ ∀ it ∈ c, P it = true

namespace PreP

variable {P : Item → Bool}

theorem pure' {α : Type} (a : α) : PreP P (pure a : E α) := by
  refine ⟨fun s b s' h => ?_⟩
  cases h
  exact ⟨[], rfl, by simp⟩

theorem bind' {α β : Type} {x : E α} {f : α → E β} (hx : PreP P x) (hf : ∀ a, PreP P (f a)) :
    PreP P (x >>= f) := by
  refine ⟨fun s b s' h => ?_⟩
  obtain ⟨a, s1, h1, h2⟩ := bind_inv_E h
  obtain ⟨c1, e1, p1⟩ := hx.out s a s1 h1
  obtain ⟨c2, e2, p2⟩ := (hf a).out s1 b s' h2
  refine ⟨c2 ++ c1, by rw [e2, e1, List.append_assoc], fun it hi => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact p2 it hi
  · exact p1 it hi

theorem throw' {α : Type} (e : String) : PreP P (throw e : E α) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h

theorem item' {it : Item} (hp : P it = true) : PreP P (item it) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h
  exact ⟨[it], rfl, by simpa using hp⟩

theorem get' : PreP P (get : E S) := by
  refine ⟨fun s a s' h => ?_⟩
  cases h
  exact ⟨[], rfl, by simp⟩

theorem forIn' {β σ : Type} (f : β → σ → E (ForInStep σ)) (hf : ∀ b st, PreP P (f b st)) :
    ∀ (l : List β) (init : σ), PreP P (forIn l init f)
  | [], init => by simpa using pure' init
  | b :: l, init => by
    rw [List.forIn_cons]
    refine bind' (hf b init) fun r => ?_
    cases r with
    | done st => exact pure' st
    | yield st => exact forIn' f hf l st

theorem mapM' {β γ : Type} (f : β → E γ) (hf : ∀ b, PreP P (f b)) : ∀ l : List β, PreP P (l.mapM f)
  | [] => by simpa using pure' ([] : List γ)
  | b :: l => by
    rw [List.mapM_cons]
    exact bind' (hf b) fun c => bind' (mapM' f hf l) fun cs => pure' _

/-- Actions leaving the output alone. -/
theorem of_out {α : Type} {x : E α} (h : ∀ s a s', x s = .ok (a, s') → s'.out = s.out) : PreP P x :=
  ⟨fun s a s' e => ⟨[], by rw [h s a s' e]; rfl, by simp⟩⟩
end PreP

/-- **An item `textDirectives` reads in a `.text` section without leaving
it**: a directive item, a comment, a blank, or a directive line that starts
`.text` or none of the section and alignment prefixes (`secPfx`). -/
def textN : Item → Bool
  | .d _ | .comment _ | .blank => true
  | .raw _ => false
  | .dir s => Scc.Lower.lineStarts s ".text" ||
      !(Scc.Lower.lineStarts s ".data" || Scc.Lower.lineStarts s ".bss" ||
        Scc.Lower.lineStarts s ".section" || Scc.Lower.lineStarts s ".rodata" ||
        Scc.Lower.lineStarts s ".p2align" || Scc.Lower.lineStarts s ".balign")

/-! ## The function's items stay in `.text` -/

theorem freshL_prep (fn : String) : PreP textN (freshL fn) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem recordMap_prep (l : String) (st hp : List Int) : PreP textN (recordMap l st hp) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem slotOff_prep (fr : Frame) (r : Scc.IR.Reg) : PreP textN (fr.slotOff r) := by
  unfold Frame.slotOff
  split
  · exact PreP.pure' _
  · exact PreP.throw' _
theorem slot_prep (fr : Frame) (r : Scc.IR.Reg) : PreP textN (fr.slot r) := by
  unfold Frame.slot
  exact PreP.bind' (slotOff_prep fr r) fun _ => PreP.pure' _

/-- One step of a `PreP textN` proof of an emitter action. -/
macro "prep_step" : tactic => `(tactic| first
  | (with_reducible exact PreP.pure' _) | (with_reducible exact PreP.throw' _)
  | (with_reducible exact PreP.item' rfl) | (with_reducible exact PreP.get')
  | (with_reducible exact freshL_prep _) | (with_reducible exact recordMap_prep _ _ _)
  | (with_reducible exact slotOff_prep _ _) | (with_reducible exact slot_prep _ _)
  | (unfold ins) | (unfold lbl) | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply PreP.bind') | (with_reducible apply PreP.forIn') | (with_reducible apply PreP.mapM')
  | (intro _) | (split))

/-- `PreP textN` of an emitter action, step by step. -/
macro "prep_tac" : tactic => `(tactic| repeat prep_step)

/-- An instruction's code stays in `.text`. -/
theorem emitInst_prep (fr : Frame) (sm : Option Scc.IR.StackMap.Entry) (i : Scc.IR.Inst) :
    PreP textN (emitInst fr sm i) := by
  cases i <;> simp only [emitInst] <;> prep_tac

/-- A terminator's code stays in `.text`. -/
theorem emitTerm_prep (fr : Frame) (t : Scc.IR.Term) : PreP textN (emitTerm fr t) := by
  cases t <;> simp only [emitTerm] <;> prep_tac

theorem PreP.ite' {α : Type} {P : Item → Bool} {c : Prop} [Decidable c] {x y : E α} (hx : PreP P x) (hy : PreP P y) :
    PreP P (if c then x else y) := by
  split
  · exact hx
  · exact hy


/-- A list mismatching `P` within `P`'s length does not start with `P`. -/
theorem isPrefixOf_append_mis {α : Type} [BEq α] : ∀ {P A : List α} (l : List α),
    ((P.zip A).any fun q => q.1 != q.2) = true → P.isPrefixOf (A ++ l) = false
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | p :: P, a :: A, l, h => by
    simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_true] at h
    simp only [List.isPrefixOf, List.cons_append, Bool.and_eq_false_iff]
    rcases h with h | h
    · exact .inl (by cases hpa : p == a <;> simp_all [bne])
    · exact .inr (isPrefixOf_append_mis l h)

/-- A line from a non-blank start `a` mismatching `p` does not start with `p`. -/
theorem lineStarts_mis (a x p : String)
    (hws : (a.toByteArray.data.toList.head?.map Scc.Lower.wsByte) = some false)
    (hp : ((p.toByteArray.data.toList.zip a.toByteArray.data.toList).any fun q => q.1 != q.2) = true) :
    Scc.Lower.lineStarts (a ++ x) p = false := by
  unfold Scc.Lower.lineStarts
  rw [String.toByteArray_append]
  cases hb : a.toByteArray.data.toList with
  | nil => rw [hb] at hws; cases hws
  | cons b bs =>
    rw [hb] at hws hp
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hws
    simp only [ByteArray.data_append, Array.toList_append, hb, List.cons_append, List.dropWhile_cons, hws]
    have := isPrefixOf_append_mis (A := b :: bs) x.toByteArray.data.toList hp
    simpa using this

/-- `p` and `a` differ at a byte within both. -/
def misB (p a : String) : Bool := (p.toByteArray.data.toList.zip a.toByteArray.data.toList).any fun q => q.1 != q.2

/-- The directive prefixes `textDirectives` reads, other than `.text`. -/
def secPfx : List String := [".data", ".bss", ".section", ".rodata", ".p2align", ".balign"]

/-- A directive line from a non-blank start that mismatches every `secPfx` is `textN`. -/
theorem textN_dir (a x : String) (hws : (a.toByteArray.data.toList.head?.map Scc.Lower.wsByte) = some false)
    (h : secPfx.all (misB · a) = true) : textN (.dir (a ++ x)) = true := by
  have hm := List.all_eq_true.mp h
  have e : ∀ q ∈ secPfx, Scc.Lower.lineStarts (a ++ x) q = false := fun q hq => lineStarts_mis a x q hws (hm q hq)
  simp only [textN, e ".data" (by simp [secPfx]), e ".bss" (by simp [secPfx]), e ".section" (by simp [secPfx]),
    e ".rodata" (by simp [secPfx]), e ".p2align" (by simp [secPfx]), e ".balign" (by simp [secPfx])]
  simp

/-! The emitter's `.text` lines. -/

theorem item_d (x : Directive) : PreP textN (item (.d x)) := PreP.item' rfl
theorem item_comment (x : String) : PreP textN (item (.comment x)) := PreP.item' rfl
theorem item_blank : PreP textN (item .blank) := PreP.item' rfl
theorem dir_globl (x : String) : PreP textN (dir (toString ".globl " ++ toString x)) :=
  PreP.item' (textN_dir ".globl " x (by decide) (by decide))
theorem dir_type (x : String) : PreP textN (dir (toString ".type " ++ toString x ++ toString ", @function")) := by
  show PreP textN (item (.dir (".type " ++ x ++ ", @function")))
  rw [String.append_assoc]
  exact PreP.item' (textN_dir ".type " _ (by decide) (by decide))
theorem dir_size (x : String) :
    PreP textN (dir (toString ".size " ++ toString x ++ toString ", .-" ++ toString x)) := by
  show PreP textN (item (.dir (".size " ++ x ++ ", .-" ++ x)))
  rw [String.append_assoc, String.append_assoc]
  exact PreP.item' (textN_dir ".size " _ (by decide) (by decide))

/-- One step of a `PreP textN` proof of `emitFunc`. -/
macro "prep_fn_step" : tactic => `(tactic| first
  | (with_reducible exact item_d _) | (with_reducible exact item_comment _) | (with_reducible exact item_blank)
  | (with_reducible exact dir_globl _) | (with_reducible exact dir_type _) | (with_reducible exact dir_size _)
  | (with_reducible exact PreP.pure' _) | (with_reducible exact PreP.throw' _)
  | (with_reducible exact PreP.get')
  | (with_reducible exact freshL_prep _) | (with_reducible exact recordMap_prep _ _ _)
  | (with_reducible exact slotOff_prep _ _) | (with_reducible exact slot_prep _ _)
  | (with_reducible exact emitInst_prep _ _ _) | (with_reducible exact emitTerm_prep _ _)
  | (unfold ins) | (unfold lbl) | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold ld) | (unfold st) | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym)
  | (unfold jmpTo) | (unfold cmpAB) | (unfold loadArgs) | (unfold callArgs) | (unfold safepoint)
  | (unfold epilogue)
  | (with_reducible apply PreP.bind') | (with_reducible apply PreP.forIn') | (with_reducible apply PreP.mapM')
  | (intro _) | (split))

/-- **A function's items stay in `.text`.** -/
theorem emitFunc_prep (a g ar) (f : Scc.IR.Func) : PreP textN (emitFunc a g ar f) := by
  simp only [emitFunc]
  apply PreP.ite'
  all_goals repeat prep_fn_step

/-- An item in the output after `x` is in it after `x >>= f`. -/
theorem PreP.mem_bind {P : Item → Bool} {β : Type} {x : E Unit} {f : Unit → E β} (hf : ∀ a, PreP P (f a))
    {it : Item} {s s' : S} {b : β} (h : (x >>= f) s = .ok (b, s'))
    (hx : ∀ s1, x s = .ok ((), s1) → it ∈ s1.out) : it ∈ s'.out := by
  obtain ⟨_, s1, h1, h2⟩ := bind_inv_E h
  obtain ⟨c, hc, -⟩ := (hf _).out _ _ _ h2
  rw [hc]
  exact List.mem_append_right _ (hx s1 h1)

/-- **A function's items hold its label.** -/
theorem emitFunc_label {a g ar} {f : Scc.IR.Func} {s s' : S} {u : Unit}
    (h : emitFunc a g ar f s = .ok (u, s')) : Item.d (.label f.name) ∈ s'.out := by
  unfold emitFunc at h
  split at h
  · obtain ⟨_, _, h1, -⟩ := bind_inv_E h
    cases h1
  · obtain ⟨_, s1, -, h⟩ := bind_inv_E h
    obtain ⟨_, s2, -, h⟩ := bind_inv_E h
    obtain ⟨_, s3, -, h⟩ := bind_inv_E h
    refine PreP.mem_bind (P := textN) (fun _ => ?_) h fun s4 h4 => ?_
    · repeat prep_fn_step
    · cases h4
      exact List.mem_cons_self ..

/-! ## The labels of the functions -/

/-- The directives of items, in order. -/
def dOf (items : List Item) : List Directive := items.filterMap fun | .d x => some x | _ => none
/-- A label directive's name. -/
def dirLabel : Directive → Option String
  | .label l => some l
  | _ => none
/-- The label names of directives, in order. -/
def labs (ds : List Directive) : List String := ds.filterMap dirLabel

/-- `emitFuncAt`'s items stay in `.text` and hold the function's label. -/
theorem emitFuncAt_labels {p : Scc.IR.Program} {areas} {f : Scc.IR.Func} {n : Nat} {r}
    (h : emitFuncAt p areas f n = .ok r) :
    (∀ it ∈ r.1, textN it = true) ∧ Item.d (.label f.name) ∈ r.1 := by
  unfold emitFuncAt at h
  cases hr : (emitFunc p.abortFn p.growth areas f).run { next := n } with
  | error e => rw [hr] at h; cases h
  | ok v =>
    obtain ⟨⟨⟩, s⟩ := v
    rw [hr] at h
    cases h
    have h' : emitFunc p.abortFn p.growth areas f { next := n } = .ok ((), s) := hr
    obtain ⟨c, hc, hp⟩ := (emitFunc_prep _ _ _ f).out _ _ _ h'
    refine ⟨fun it hi => hp it ?_, List.mem_reverse.mpr (emitFunc_label h')⟩
    simp only [List.append_nil] at hc
    rw [hc] at hi
    exact List.mem_reverse.mp hi

/-- **`emitFuncs`'s blocks**: one per function, each in `.text` holding its function's label. -/
theorem emitFuncs_labels {p : Scc.IR.Program} {areas} : ∀ {fs : List Scc.IR.Func} {n : Nat} {rs},
    emitFuncs p areas fs n = .ok rs →
    ∃ hl : rs.length = fs.length, ∀ i (hi : i < fs.length),
      (∀ it ∈ (rs[i]'(hl ▸ hi)).1, textN it = true) ∧ Item.d (.label fs[i].name) ∈ (rs[i]'(hl ▸ hi)).1
  | [], n, rs, h => by
    cases h
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | f :: fs, n, rs, h => by
    unfold emitFuncs at h
    cases h1 : emitFuncAt p areas f n with
    | error e => rw [h1] at h; cases h
    | ok r =>
      obtain ⟨items, n', ms⟩ := r
      rw [h1] at h
      change (emitFuncs p areas fs n' >>= fun rest => pure ((items, ms) :: rest)) = Except.ok rs at h
      cases h2 : emitFuncs p areas fs n' with
      | error e => rw [h2] at h; cases h
      | ok rest =>
        rw [h2] at h
        cases h
        obtain ⟨hl, hi⟩ := emitFuncs_labels h2
        obtain ⟨t0, l0⟩ := emitFuncAt_labels h1
        refine ⟨by simp [hl], fun i hlt => ?_⟩
        cases i with
        | zero => exact ⟨t0, l0⟩
        | succ k => exact hi k (by simpa using hlt)

/-! ## `textDirectives` over `.text` items -/

open Scc.Lower Scc.Lower.X64 in
/-- `textDirectives`'s step. -/
def tdStep (acc : Option (Bool × List Directive)) (it : Item) : Option (Bool × List Directive) :=
    acc.bind fun (txt, ds) =>
      match it with
      | .dir s =>
        let pre := lineStarts s
        if pre ".text" then some (true, ds)
        else if pre ".data" || pre ".bss" || pre ".section" || pre ".rodata" then some (false, ds)
        else if txt then
          match if pre ".p2align" || pre ".balign" then alignOf (lineChars s) else none with
          | some n => some (true, .instr (Kraken.X64.Parser.toInstr .none (w := .W64) (.nopalign n none)) :: ds)
          | none => some (true, ds)
        else some (txt, ds)
      | .d x => if txt then some (true, x :: ds) else some (txt, ds)
      | .raw _ => if txt then none else some (txt, ds)
      | .comment _ | .blank => some (txt, ds)

/-- `textDirectives` as a fold of `tdStep`. -/
theorem textDirectives_eq (items : List Item) :
    Scc.Lower.X64.textDirectives items = (items.foldl tdStep (some (true, []))).map (·.2.reverse) := rfl

/-- A `textN` item keeps `.text` and adds its directive. -/
theorem tdStep_textN {it : Item} (h : textN it = true) (ds : List Directive) :
    tdStep (some (true, ds)) it = some (true, (dOf [it]).reverse ++ ds) := by
  cases it with
  | d x => rfl
  | comment _ => rfl
  | blank => rfl
  | raw _ => cases h
  | dir s =>
    simp only [textN, Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h
    rcases h with h | ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    · simp [tdStep, h, dOf]
    · simp [tdStep, h1, h2, h3, h4, h5, h6, dOf]

/-- `textN` items from `.text` add their directives. -/
theorem foldl_textN : ∀ {items : List Item}, (∀ it ∈ items, textN it = true) → ∀ ds : List Directive,
    items.foldl tdStep (some (true, ds)) = some (true, (dOf items).reverse ++ ds)
  | [], _, ds => rfl
  | it :: items, h, ds => by
    rw [List.foldl_cons, tdStep_textN (h it (List.mem_cons_self ..)),
      foldl_textN (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [dOf, List.filterMap_cons]
    cases it <;> simp

/-- A step fails or extends the directives. -/
theorem tdStep_ext (b : Bool) (ds : List Directive) (it : Item) :
    tdStep (some (b, ds)) it = none ∨ ∃ b' z, tdStep (some (b, ds)) it = some (b', z ++ ds) := by
  unfold tdStep
  simp only [Option.bind_some]
  split <;> (repeat' split) <;>
    first | exact .inl rfl | exact .inr ⟨_, [], rfl⟩ | exact .inr ⟨_, [_], rfl⟩

/-- A failed fold stays failed. -/
theorem foldl_none : ∀ items : List Item, items.foldl tdStep none = none
  | [] => rfl
  | _ :: items => foldl_none items

/-- The fold fails or extends the directives. -/
theorem foldl_ext : ∀ (items : List Item) (b : Bool) (ds : List Directive),
    items.foldl tdStep (some (b, ds)) = none ∨ ∃ b' z, items.foldl tdStep (some (b, ds)) = some (b', z ++ ds)
  | [], b, ds => .inr ⟨b, [], rfl⟩
  | it :: items, b, ds => by
    rw [List.foldl_cons]
    rcases tdStep_ext b ds it with e | ⟨b', z, e⟩
    · rw [e, foldl_none]; exact .inl rfl
    · rw [e]
      rcases foldl_ext items b' (z ++ ds) with e' | ⟨b'', z', e'⟩
      · exact .inl e'
      · exact .inr ⟨b'', z' ++ z, by rw [e', List.append_assoc]⟩

/-- **`textDirectives` of `textN` items, then any**: their directives first. -/
theorem textDirectives_append {A B C : List Item} (hA : ∀ it ∈ A, textN it = true)
    (hB : ∀ it ∈ B, textN it = true) {prog : List Directive}
    (h : Scc.Lower.X64.textDirectives (A ++ B ++ C) = some prog) : ∃ Z, prog = dOf A ++ dOf B ++ Z := by
  rw [textDirectives_eq, List.foldl_append, List.foldl_append, foldl_textN hA, foldl_textN hB] at h
  rcases foldl_ext C true ((dOf B).reverse ++ ((dOf A).reverse ++ [])) with e | ⟨b, z, e⟩
  · rw [e] at h; cases h
  · rw [e] at h
    cases h
    exact ⟨z.reverse, by simp⟩

/-- A successful `Except` bind from its parts. -/
theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A literal `.text` directive line. -/
theorem dir_lit (s : String) (h : textN (.dir s) = true) : PreP textN (dir s) := PreP.item' h

/-- The header stays in `.text`. -/
theorem emitHead_prep (p : Scc.IR.Program) : PreP textN (emitHead p) := by
  simp only [emitHead]
  repeat (first | exact dir_lit _ (by decide) | prep_fn_step)

/-- `emitItemsMaps`'s items: `.text` header items, the functions' blocks, the rest. -/
theorem emitItemsMaps_items {ir : Scc.IR.Program} {items : List Item} {sps : List Map}
    (h : emitItemsMaps ir = .ok (items, sps)) :
    ∃ areas rs H T, emitFuncs ir areas ir.funcs 0 = .ok rs ∧ (∀ it ∈ H, textN it = true) ∧
      items = H ++ rs.flatMap (·.1) ++ T := by
  obtain ⟨areas, -, h⟩ := except_bind_ok h
  obtain ⟨rs, hrs, h⟩ := except_bind_ok h
  obtain ⟨⟨⟨⟩, hs⟩, hh, h⟩ := except_bind_ok h
  obtain ⟨⟨⟨⟩, ts⟩, -, h⟩ := except_bind_ok h
  cases h
  obtain ⟨c, hc, hp⟩ := (emitHead_prep ir).out _ _ _ hh
  refine ⟨areas, rs, _, _, hrs, fun it hi => hp it ?_, rfl⟩
  simp only [List.append_nil] at hc
  rw [hc] at hi
  exact List.mem_reverse.mp hi

/-- **The cells of scc's x86-64 output, in order** (where there are any):
the header's directives, the functions' (`emitFuncs`'s blocks, in order),
then the rest. -/
theorem lowerAll_cells {cfg : Scc.Config} {p : CoreTerm.Prog} {sizes : List Nat}
    (hne : Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes ≠ []) :
    ∃ areas rs H Z, emitFuncs (Scc.Lower.X64.lowerAll cfg p).low.ir areas
        (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs 0 = .ok rs ∧
      (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes).map (·.1) =
        H ++ rs.flatMap (fun r => dOf r.1) ++ Z := by
  cases hl : Scc.Lower.X64.lowerAll? cfg p with
  | error e =>
    have : Scc.Lower.X64.lowerAll cfg p = default := by unfold Scc.Lower.X64.lowerAll; rw [hl]
    rw [this] at hne
    exact absurd rfl hne
  | ok e =>
    have he : Scc.Lower.X64.lowerAll cfg p = e := by unfold Scc.Lower.X64.lowerAll; rw [hl]
    rw [he] at hne ⊢
    obtain ⟨l, -, hl⟩ := except_bind_ok hl
    obtain ⟨⟨items, sps⟩, hE, hl⟩ := except_bind_ok hl
    cases hl
    obtain ⟨areas, rs, H, T, hf, hH, hi⟩ := emitItemsMaps_items hE
    refine ⟨areas, rs, ?_⟩
    unfold Scc.Cert.PlaceOK.X64.cellsOfEmitted at hne ⊢
    dsimp only at hne ⊢
    cases hp : Scc.Lower.X64.textDirectives items with
    | none => rw [hp] at hne; exact absurd rfl hne
    | some prog =>
      cases hs : Kraken.Promising.X64.sizedCells prog sizes with
      | none => rw [hp] at hne; simp [hs] at hne
      | some cells =>
        simp only [Option.bind_some, hs, Option.getD_some]
        rw [Kraken.Promising.X64.sizedCells_fst hs]
        rw [hi] at hp
        have hB : ∀ it ∈ rs.flatMap (·.1), textN it = true := fun it hit => by
          obtain ⟨r, hr, hit⟩ := List.mem_flatMap.mp hit
          obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hr
          obtain ⟨hlen, hall⟩ := emitFuncs_labels hf
          exact (hall i (hlen ▸ hi')).1 it hit
        obtain ⟨Z, hZ⟩ := textDirectives_append hH hB hp
        refine ⟨dOf H, Z, hf, ?_⟩
        rw [hZ]
        simp only [dOf, List.filterMap_flatMap]

/-! ## Distinct labels -/

open Scc.Cert.Link.X64 in
/-- `cellsWalk`'s labels are the cells' label names, in order. -/
theorem cellsWalk_labels (base : Int64) : ∀ (cells : List (Directive × Nat)) (acc : Nat) (ls : List (String × Nat))
    (n : Nat), cellsWalk base cells acc = some (ls, n) → ls.map (·.1) = labs (cells.map (·.1))
  | [], acc, ls, n, h => by
    simp only [cellsWalk, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | (.label l, z) :: cs, acc, ls, n, h => by
    simp only [cellsWalk] at h
    split at h
    · obtain ⟨⟨ls', n'⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases e
      show l :: ls'.map (·.1) = l :: labs (cs.map (·.1))
      rw [cellsWalk_labels base cs acc ls' n' hr]
    · cases h
  | (.instr i, z) :: cs, acc, ls, n, h => by
    simp only [cellsWalk] at h
    split at h
    · exact cellsWalk_labels base cs _ ls n h
    · cases h
  | (.byteArray a, z) :: cs, acc, ls, n, h => by
    simp only [cellsWalk] at h
    split at h
    · exact cellsWalk_labels base cs _ ls n h
    · cases h

/-- `keysNodupB` lists are pairwise distinct. -/
theorem keysNodupB_pairwise' : ∀ {l : List Nat}, Scc.Cert.Link.X64.keysNodupB l = true → l.Pairwise (· ≠ ·)
  | [], _ => .nil
  | a :: l, h => by
    simp only [Scc.Cert.Link.X64.keysNodupB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    exact .cons (fun b hb e => h.1 b hb e.symm) (keysNodupB_pairwise' h.2)

/-- **`labelsNodupL` makes the cells' label names distinct.** -/
theorem labs_nodup_of_labelsNodupL {base : Int64} {cells : List (Directive × Nat)}
    (h : Scc.Cert.Link.X64.labelsNodupL base cells = true) : (labs (cells.map (·.1))).Nodup := by
  unfold Scc.Cert.Link.X64.labelsNodupL at h
  split at h
  · next ls n hw =>
    have hp := List.pairwise_map.mp (keysNodupB_pairwise' h)
    rw [← cellsWalk_labels base cells 0 ls n hw]
    exact List.pairwise_map.mpr (hp.imp fun hne e => hne (congrArg _ e))
  · cases h

/-- A label item's name is among the items' labels. -/
theorem mem_labs {items : List Item} {l : String} (h : Item.d (.label l) ∈ items) : l ∈ labs (dOf items) :=
  List.mem_filterMap.mpr ⟨.label l, List.mem_filterMap.mpr ⟨_, h, rfl⟩, rfl⟩

/-- Distinct labels around the blocks are distinct within and across blocks. -/
theorem labs_blocks_nodup {H Z : List Directive} {rs : List (List Item × List Map)}
    (h : (labs (H ++ rs.flatMap (fun r => dOf r.1) ++ Z)).Nodup) : (rs.flatMap fun r => labs (dOf r.1)).Nodup := by
  rw [labs, List.filterMap_append, List.filterMap_append, List.filterMap_flatMap] at h
  exact h.sublist (List.infix_append _ _ _).sublist

/-- **Blocks with distinct labels name their functions distinctly**: one name, one index. -/
theorem index_inj {fs : List Scc.IR.Func} {rs : List (List Item × List Map)} (hl : rs.length = fs.length)
    (hlab : ∀ i (hi : i < fs.length), Item.d (.label fs[i].name) ∈ (rs[i]'(hl ▸ hi)).1)
    (hnd : (rs.flatMap fun r => labs (dOf r.1)).Nodup) {a b : Nat} (ha : a < fs.length) (hb : b < fs.length)
    (he : fs[a].name = fs[b].name) : a = b := by
  have hp := List.pairwise_iff_getElem.mp (List.pairwise_flatMap.mp hnd).2
  have mem : ∀ i (hi : i < fs.length), fs[i].name ∈ labs (dOf (rs[i]'(hl ▸ hi)).1) := fun i hi =>
    mem_labs (hlab i hi)
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd rfl (hp a b (hl ▸ ha) (hl ▸ hb) hab _ (mem a ha) _ (by rw [he]; exact mem b hb))
  · exact hab
  · exact absurd rfl (hp b a (hl ▸ hb) (hl ▸ ha) hab _ (mem b hb) _ (by rw [← he]; exact mem a ha))

end Spike.Lib.LowerX64
