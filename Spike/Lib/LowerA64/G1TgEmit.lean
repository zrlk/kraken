/-
**The shape of scc's AArch64 output** (`Scc.Emit.A64`, `Scc.Lower.A64`):
the emitter's items for a function are its two assembler lines, its name's
label, the prologue, the parameters' stores, each block's label and code and
the stubs (`emitFunc_items`); the program's items are the header, the
functions' items in order, the grow trampoline, the text's end label and the
data (`emitItemsMaps_items`); the instruction list `textDirectives` keeps
the directives of the `.text` items and drops the data's
(`textDirectives_split`). So the output's instruction list is the header's
directives, each function's and the trampoline's (`lowerAll_prog`).

- `forIn_inv`: a loop invariant in `Except`;
- `codesFromN`, `forIn_appendsN`: a loop appending each element's code and
  advancing its counter by the element's weight;
- `blockCode`, `fnBody`: a block's label and code, a function's blocks';
- `allocOf`, `saveOf`, `stubsOf`, `emitFunc_items`: a function's items;
- `textN`, `dataN`, `textDirectives_split`: the instruction list of `.text`
  items then data items;
- `emitPost_items`, `emitItemsMaps_items`, `lowerAll_prog`: the program.
-/
import Scc.Lower.SpecA64
import Scc.Lower.LowerBodyA64
import Scc.Cert.Code1A64
import Spike.Lib.LowerA64.G1TgSeg

namespace Spike.Lib.LowerA64

open Kraken
open Scc.Emit.A64
open Scc.Lower.InvA64 (codesFrom forIn_appends' codesFrom_zip_fst)
open Scc.Cert.Code1A64 (instsItems blockItems)
open Scc.Cert.Rt.A64 (isIns)

/-! ## Loops -/

/-- The state a loop step leaves. -/
def stepState {σ : Type} : ForInStep σ → σ
  | .done s => s
  | .yield s => s

/-- **A loop invariant** in `Except`: holding at the start and kept by every
step, it holds at the end. -/
theorem forIn_inv {α σ : Type} (Inv : σ → Prop) :
    ∀ {l : List α} {init : σ} {body : α → σ → Except String (ForInStep σ)} {res : σ},
      forIn l init body = .ok res → Inv init →
      (∀ x ∈ l, ∀ s, Inv s → ∀ r, body x s = .ok r → Inv (stepState r)) → Inv res
  | [], init, _, res, h, hi, _ => by
    rw [List.forIn_nil] at h
    cases h; exact hi
  | x :: l, init, body, res, h, hi, hs => by
    rw [List.forIn_cons] at h
    cases hx : body x init with
    | error e => rw [hx] at h; cases h
    | ok r =>
      rw [hx] at h
      have hr := hs x List.mem_cons_self init hi r hx
      cases r with
      | done s =>
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h; exact hr
      | yield s =>
        exact forIn_inv Inv h hr (fun y hy => hs y (List.mem_cons_of_mem _ hy))

/-- The codes `g k x` of the elements `x` of a list, the counter advancing
by `adv x` per element. -/
def codesFromN {α : Type} (g : Nat → α → Except String (List Item)) (adv : α → Nat) :
    Nat → List α → Except String (List (List Item))
  | _, [] => .ok []
  | k, x :: l => do
    let ys ← g k x
    let xs ← codesFromN g adv (k + adv x) l
    pure (ys :: xs)

/-- **A loop that appends each element's code**, advancing its counter by
the element's weight (`Scc.Lower.InvA64.forIn_appends` with the code first
in the state and a weight per element). -/
theorem forIn_appendsN {α σ : Type} (g : Nat → α → Except String (List Item)) (adv : α → Nat)
    (body : α → List Item × σ × Nat → Except String (ForInStep (List Item × σ × Nat))) :
    ∀ (l : List α), (∀ x ∈ l, ∀ code s k y, body x (code, s, k) = .ok y →
      ∃ ys s', g k x = .ok ys ∧ y = .yield (code ++ ys, s', k + adv x)) →
    ∀ (code : List Item) (s : σ) (k : Nat) (res : List Item × σ × Nat),
      forIn l (code, s, k) body = .ok res →
      ∃ xs, codesFromN g adv k l = .ok xs ∧ res.1 = code ++ xs.flatten
  | [], _, code, s, k, res, h => by
    rw [List.forIn_nil] at h
    cases h; exact ⟨[], rfl, by simp⟩
  | x :: l, hb, code, s, k, res, h => by
    rw [List.forIn_cons] at h
    cases hx : body x (code, s, k) with
    | error e => rw [hx] at h; cases h
    | ok y =>
      obtain ⟨ys, s', hg, rfl⟩ := hb x List.mem_cons_self code s k y hx
      rw [hx] at h
      obtain ⟨xs, hm, h2⟩ := forIn_appendsN g adv body l (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        (code ++ ys) s' (k + adv x) res h
      refine ⟨ys :: xs, ?_, by simp [h2]⟩
      simp only [codesFromN, hg, hm, bind, Except.bind, pure, Except.pure]

/-! ## The instruction list of the items -/

/-- `textDirectives`'s step. -/
def tdStep (acc : Bool × List Directive) : Item → Bool × List Directive
  | .raw s =>
    let pre := Scc.Lower.lineStarts s
    if pre ".text" then (true, acc.2)
    else if pre ".data" || pre ".bss" || pre ".section" || pre ".rodata" then (false, acc.2)
    else acc
  | .d x => if acc.1 then (true, x :: acc.2) else acc
  | .comment _ => acc

/-- `textDirectives` as a fold of `tdStep`. -/
theorem textDirectives_eq (items : List Item) :
    Scc.Lower.A64.textDirectives items = (items.foldl tdStep (true, [])).2.reverse := rfl

/-- **An item that keeps `.text`**: a directive, a comment, or a raw line
opening no data section. -/
def textN : Item → Bool
  | .d _ | .comment _ => true
  | .raw s => !(Scc.Lower.lineStarts s ".data" || Scc.Lower.lineStarts s ".bss" ||
      Scc.Lower.lineStarts s ".section" || Scc.Lower.lineStarts s ".rodata")

/-- **An item that keeps a data section**: anything but a `.text` line. -/
def dataN : Item → Bool
  | .raw s => !Scc.Lower.lineStarts s ".text"
  | _ => true

/-- `textN` items from `.text` add their directives. -/
theorem foldl_textN : ∀ {items : List Item}, (∀ it ∈ items, textN it = true) → ∀ ds : List Directive,
    items.foldl tdStep (true, ds) = (true, (directives items).reverse ++ ds)
  | [], _, ds => by simp [directives]
  | it :: items, h, ds => by
    have h1 := h it List.mem_cons_self
    have ih := foldl_textN (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.foldl_cons]
    cases it with
    | d x =>
      rw [show tdStep (true, ds) (.d x) = (true, x :: ds) from rfl, ih]
      simp [directives]
    | comment s =>
      rw [show tdStep (true, ds) (.comment s) = (true, ds) from rfl, ih]
      simp [directives]
    | raw s =>
      simp only [textN, Bool.not_eq_true', Bool.or_eq_false_iff] at h1
      obtain ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩ := h1
      have hs : tdStep (true, ds) (.raw s) = (true, ds) := by
        simp only [tdStep, h2, h3, h4, h5, Bool.or_self, Bool.false_eq_true, ite_false]
        split <;> rfl
      rw [hs, ih]
      simp [directives]

/-- `dataN` items from a data section add nothing. -/
theorem foldl_dataN : ∀ {items : List Item}, (∀ it ∈ items, dataN it = true) → ∀ ds : List Directive,
    items.foldl tdStep (false, ds) = (false, ds)
  | [], _, _ => rfl
  | it :: items, h, ds => by
    have h1 := h it List.mem_cons_self
    have ih := foldl_dataN (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.foldl_cons]
    cases it with
    | d x => rw [show tdStep (false, ds) (.d x) = (false, ds) from rfl, ih]
    | comment s => rw [show tdStep (false, ds) (.comment s) = (false, ds) from rfl, ih]
    | raw s =>
      simp only [dataN, Bool.not_eq_true'] at h1
      have hs : tdStep (false, ds) (.raw s) = (false, ds) := by
        simp only [tdStep, h1, Bool.false_eq_true, ite_false]
        split <;> rfl
      rw [hs, ih]

/-- The `.data` line opens a data section. -/
theorem tdStep_data (b : Bool) (ds : List Directive) : tdStep (b, ds) (.raw ".data") = (false, ds) := by
  have h1 : Scc.Lower.lineStarts ".data" ".text" = false := by decide
  have h2 : Scc.Lower.lineStarts ".data" ".data" = true := by decide
  simp [tdStep, h1, h2]

/-- **The instruction list of `.text` items, then a `.data` line and data
items**: the `.text` items' directives. -/
theorem textDirectives_split {A B : List Item} (hA : ∀ it ∈ A, textN it = true)
    (hB : ∀ it ∈ B, dataN it = true) :
    Scc.Lower.A64.textDirectives (A ++ .raw ".data" :: B) = directives A := by
  rw [textDirectives_eq, List.foldl_append, foldl_textN hA, List.foldl_cons, tdStep_data, foldl_dataN hB]
  simp

/-! ### Raw lines -/

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
def misB (p a : String) : Bool :=
  (p.toByteArray.data.toList.zip a.toByteArray.data.toList).any fun q => q.1 != q.2

/-- The data prefixes `textDirectives` reads. -/
def secPfx : List String := [".data", ".bss", ".section", ".rodata"]

/-- A raw line from a non-blank start that mismatches every `secPfx` is `textN`. -/
theorem textN_raw (a x : String) (hws : (a.toByteArray.data.toList.head?.map Scc.Lower.wsByte) = some false)
    (h : secPfx.all (misB · a) = true) : textN (.raw (a ++ x)) = true := by
  have hm := List.all_eq_true.mp h
  have e : ∀ q ∈ secPfx, Scc.Lower.lineStarts (a ++ x) q = false := fun q hq => lineStarts_mis a x q hws (hm q hq)
  simp only [textN, e ".data" (by simp [secPfx]), e ".bss" (by simp [secPfx]), e ".section" (by simp [secPfx]),
    e ".rodata" (by simp [secPfx])]
  rfl

/-- A raw line from a non-blank start that mismatches `.text` is `dataN`. -/
theorem dataN_raw (a x : String) (hws : (a.toByteArray.data.toList.head?.map Scc.Lower.wsByte) = some false)
    (h : misB ".text" a = true) : dataN (.raw (a ++ x)) = true := by
  simp only [dataN, lineStarts_mis a x ".text" hws h]
  rfl

theorem textN_d (x : Directive) : textN (.d x) = true := rfl
theorem textN_comment (s : String) : textN (.comment s) = true := rfl
theorem dataN_d (x : Directive) : dataN (.d x) = true := rfl
theorem dataN_comment (s : String) : dataN (.comment s) = true := rfl

/-- The `.type` line of a function. -/
theorem textN_type (x : String) : textN (.raw (toString ".type " ++ toString x ++ toString ", %function")) = true := by
  show textN (.raw (".type " ++ x ++ ", %function")) = true
  rw [String.append_assoc]
  exact textN_raw ".type " _ (by decide) (by decide)

/-- One step discharging `dataN` of an emitted data item. -/
macro "data_step" : tactic => `(tactic| first
  | exact dataN_d _ | exact dataN_comment _
  | exact dataN_raw _ _ (by decide) (by decide)
  | (rw [String.append_assoc]; exact dataN_raw _ _ (by decide) (by decide))
  | (rw [String.append_assoc, String.append_assoc]; exact dataN_raw _ _ (by decide) (by decide))
  | (rw [String.append_assoc, String.append_assoc, String.append_assoc]; exact dataN_raw _ _ (by decide) (by decide))
  | (rw [String.append_assoc, String.append_assoc, String.append_assoc, String.append_assoc];
     exact dataN_raw _ _ (by decide) (by decide))
  | (simp only [String.append_assoc]; exact dataN_raw _ _ (by decide) (by decide))
  | decide)

/-! ## The program's items -/

/-- A successful `Except` bind from its parts. -/
theorem ok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The `.byte` lines are data items. -/
theorem byteLines_go_dataN : ∀ (fuel : Nat) (bs : List UInt8), ∀ it ∈ byteLines.go fuel bs, dataN it = true
  | 0, _, it, h => by simp [byteLines.go] at h
  | _ + 1, [], it, h => by simp [byteLines.go] at h
  | fuel + 1, b :: bs, it, h => by
    simp only [byteLines.go, List.mem_cons] at h
    rcases h with rfl | h
    · data_step
    · exact byteLines_go_dataN fuel _ it h

/-- **A data item's lines are data items.** -/
theorem emitData_dataN {d : Scc.IR.Data} {its : List Item} (h : emitData d = .ok its) :
    ∀ it ∈ its, dataN it = true := by
  unfold emitData at h
  dsimp only at h
  split at h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro it hit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
      rcases hit with rfl | rfl | rfl | rfl | rfl | rfl <;> data_step
    · next bs _ =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro it hit
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hit
      rcases hit with rfl | rfl | rfl | hit
      · data_step
      · data_step
      · data_step
      · split at hit
        · simp only [List.mem_singleton] at hit; subst hit; data_step
        · exact byteLines_go_dataN _ _ it hit
  · obtain ⟨_, h', -⟩ := ok_bind h
    cases h'

/-- The stack-map table's entry lines are data items. -/
theorem mapEntries_dataN (sps : List Safepoint) :
    ∀ (acc : List Item) (first : Nat), (∀ it ∈ acc, dataN it = true) →
      ∀ it ∈ (sps.foldl (fun (acc, first) (l, st, hp) =>
          (acc ++ [Item.raw s!".quad {l} - {Scc.IR.StackMap.textStartSym}, {st.length}, {hp.length}, {first}"],
           first + st.length + hp.length)) (acc, first)).1, dataN it = true := by
  induction sps with
  | nil => intro acc first h; simpa using h
  | cons s sps ih =>
    intro acc first h
    obtain ⟨l, st, hp⟩ := s
    rw [List.foldl_cons]
    refine ih _ _ fun it hit => ?_
    rw [List.mem_append, List.mem_singleton] at hit
    rcases hit with hit | rfl
    · exact h it hit
    · data_step

/-- **The stack-map table's items are data items.** -/
theorem mapItems_dataN (sps : List Safepoint) : ∀ it ∈ mapItems sps, dataN it = true := by
  intro it hit
  unfold mapItems at hit
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hit
  rcases hit with rfl | rfl | rfl | rfl | hit | hit
  · data_step
  · data_step
  · data_step
  · data_step
  · exact mapEntries_dataN sps [] 0 (by simp) it hit
  · obtain ⟨⟨l, st, hp⟩, -, hit⟩ := List.mem_flatMap.mp hit
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hit
    data_step

/-- The header of a Linux program. -/
def linuxHead (p : Scc.IR.Program) : List Item :=
  [.comment "generated by scc (arm: AArch64 FEAT_LSE2, Linux)",
    .raw ".arch armv8.4-a", .raw ".text", .raw ".globl _start", .raw ".p2align 4",
    lbl Scc.IR.StackMap.textStartSym, lbl "_start", jmp p.start]

/-- **The rest of the program's items** (`emitPost`), on a Linux program
with growth: the header, the functions' items, the grow trampoline, the
text's end label, then a `.data` line and data items. -/
theorem emitPost_items {p : Scc.IR.Program} {g : Scc.IR.Growth} (hg : p.growth = some g) (hh : p.host = .linux)
    {rs : List (List Item × List Safepoint)} {items : List Item} {sps : List Safepoint}
    (h : emitPost p rs = .ok (items, sps)) :
    ∃ ds, (∀ it ∈ ds, dataN it = true) ∧
      items = linuxHead p ++ rs.flatMap (·.1) ++ morestack g ++ [lbl Scc.IR.StackMap.textEndSym] ++
        .raw ".data" :: ds := by
  unfold emitPost at h
  simp only [bind, Except.bind] at h
  generalize hF : forIn (m := Except String) p.data
    [Item.raw ".data", .raw ".balign 16", .raw ".bss", .raw ".balign 16"] _ = F at h
  cases F with
  | error e => cases h
  | ok ds =>
    have hinit : ∀ it ∈ [Item.raw ".balign 16", .raw ".bss", .raw ".balign 16"], dataN it = true := by
      intro it hit
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hit
      rcases hit with rfl | rfl | rfl <;> data_step
    have hinv := forIn_inv (fun ds : List Item => ∃ ds', ds = .raw ".data" :: ds' ∧ ∀ it ∈ ds', dataN it = true) hF
      ⟨_, rfl, hinit⟩
      (by
        intro d _ s hs r hr
        try simp only [bind, Except.bind] at hr
        cases hd : emitData d with
        | error e => rw [hd] at hr; cases hr
        | ok its =>
          rw [hd] at hr
          simp only [pure, Except.pure, Except.ok.injEq] at hr
          subst hr
          obtain ⟨ds', rfl, hds'⟩ := hs
          refine ⟨ds' ++ its, rfl, fun it hit => ?_⟩
          rcases List.mem_append.mp hit with hit | hit
          · exact hds' it hit
          · exact emitData_dataN hd it hit)
    obtain ⟨ds', rfl, hds'⟩ := hinv
    simp only [hg, hh, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine ⟨ds' ++ mapItems (rs.flatMap (·.2)), fun it hit => ?_, by simp [linuxHead]⟩
    rcases List.mem_append.mp hit with hit | hit
    · exact hds' it hit
    · exact mapItems_dataN _ it hit

/-- **The program's items from their stages** (`emitItemsMaps`). -/
theorem emitItemsMaps_items {p : Scc.IR.Program} {items : List Item} {sps : List Safepoint}
    (h : emitItemsMaps p = .ok (items, sps)) :
    ∃ areas rs, emitPre p = .ok areas ∧ p.funcs.zipIdx.mapM (emitFuncAt p areas) = .ok rs ∧
      emitPost p rs = .ok (items, sps) := by
  unfold emitItemsMaps at h
  obtain ⟨areas, h1, h⟩ := ok_bind h
  obtain ⟨rs, h2, h3⟩ := ok_bind h
  exact ⟨areas, rs, h1, h2, h3⟩

/-- **The output's instruction list is `textDirectives` of the emitter's
items** where the lowering succeeds. -/
theorem lowerAll?_prog {cfg : Scc.Config} {p : CoreTerm.Prog} {e : Scc.Lower.A64.Emitted}
    (h : Scc.Lower.A64.lowerAll? cfg p = .ok e) :
    ∃ items sps, emitItemsMaps e.low.ir = .ok (items, sps) ∧ e.prog = Scc.Lower.A64.textDirectives items := by
  unfold Scc.Lower.A64.lowerAll? at h
  obtain ⟨l, -, h⟩ := ok_bind h
  obtain ⟨items, sps, hm, rfl⟩ := Scc.Lower.A64.emitAll_ok h
  exact ⟨items, sps, hm, rfl⟩

/-! ## A function's items -/

/-- **A block's label and code** (`blockItems`), its first instruction
numbered `k`. -/
def blockCode (c : FnCtx) (k : Nat) (b : Scc.IR.Block) : Except String (List Item) := do
  let l ← c.blockLabel b.label
  let code ← blockItems c k b
  pure (lbl l :: code)

/-- The weight of a block in the emitter's instruction counter: its
instructions and its terminator. -/
def blockAdv (b : Scc.IR.Block) : Nat := b.insts.length + 1

/-- **The prologue's frame allocation** (`emitFunc`'s `alloc`). -/
def allocOf (c : FnCtx) (checkStack : Bool) : List Item :=
  if checkStack then
    (if c.maps then [lbl (c.local "stack_check")] else []) ++
    addImm (xs .X9) spW64 (-(c.frame : Int)) ++
    [readTp .X10] ++ ldrOff .W64 .X10 (xs .X10) Scc.IR.Tcb.stackLimit ++
    [cmpReg .W64 .X9 .X10, jcc .CC (c.local (if c.maps then "stack_grow" else "abort_stack")),
     movSp spW64 (xs .X9)]
  else addImm spW64 spW64 (-(c.frame : Int))

/-- **The prologue's frame record** (`emitFunc`'s `save`). -/
def saveOf (c : FnCtx) : List Item :=
  strOff .W64 .X29 spW64 (c.frame - 16) ++ strOff .W64 .X30 spW64 (c.frame - 8) ++
    addImm (xs .X29) spW64 (c.frame - 16)

/-- **An abort stub** (`emitFunc`'s `abortStub`). -/
def abortStubOf (c : FnCtx) (abortFn : String) (suffix : String) (kind : Scc.IR.AbortKind) : List Item :=
  [lbl (c.local suffix)] ++ movImm .X0 kind.code ++ [call abortFn] ++ halt (c.local (suffix ++ "_halt"))

/-- **The grow stub** (`emitFunc`'s `growStub`). -/
def growStubOf (c : FnCtx) : List Item :=
  [lbl (c.local "stack_grow")] ++ addImm spW64 spW64 (-80) ++
  (argRegs.zipIdx.flatMap fun (r, i) => strOff .W64 r spW64 (8 * i)) ++
  strOff .W64 .X29 spW64 64 ++ strOff .W64 .X30 spW64 72 ++ addImm (xs .X29) spW64 64 ++
  movImm .X0 c.frame ++ [call Scc.IR.StackMap.morestackSym, lbl (c.local "sp_check")] ++
  (argRegs.zipIdx.flatMap fun (r, i) => ldrOff .W64 r spW64 (8 * i)) ++
  ldrOff .W64 .X29 spW64 64 ++ ldrOff .W64 .X30 spW64 72 ++ addImm spW64 spW64 80 ++
  [jmp (c.local "stack_check")]

/-- **The stubs after a function's code** (`emitFunc`'s `stubs`). -/
def stubsOf (c : FnCtx) (f : Scc.IR.Func) (abortFn : String) (growth : Option Scc.IR.Growth) : List Item :=
  (if f.checkStack then
    (if growth.isSome then growStubOf c else abortStubOf c abortFn "abort_stack" .stack) else []) ++
  ((if Scc.Cert.Code1A64.hasAddChk f then abortStubOf c abortFn "abort_overflow" .overflow else []) ++
    (cloneSites f).flatMap fun (k, e) => c.childStub k e)

/-- The safepoint entries of a function have one list per block. -/
theorem callMaps_length (f : Scc.IR.Func) : (Scc.IR.StackMap.callMaps f).length = f.blocks.length := by
  simp [Scc.IR.StackMap.callMaps, Scc.IR.StackMap.callLives]

/-- Each block's safepoint entries have one per instruction. -/
theorem callMaps_inner_length (f : Scc.IR.Func) (j : Nat) (hj : j < f.blocks.length) :
    ((Scc.IR.StackMap.callMaps f)[j]'(by rw [callMaps_length]; exact hj)).length = f.blocks[j].insts.length := by
  simp only [Scc.IR.StackMap.callMaps, Scc.IR.StackMap.callLives, List.getElem_map, List.length_map]
  generalize f.blocks[j] = b
  generalize Scc.IR.StackMap.liveIns f = ins
  generalize (List.foldl _ [] _ : List Scc.IR.Reg) = out
  generalize Scc.IR.StackMap.union _ out = z
  suffices ∀ (l : List Scc.IR.Inst) (z : List Scc.IR.Reg),
      (List.foldr (fun i (x : List Scc.IR.Reg × List (Option (List Scc.IR.Reg))) =>
        (Scc.IR.StackMap.liveBefore i x.1, (match i with
          | Scc.IR.Inst.call ds _ _ => some (List.filter (fun r => !ds.contains r) x.1)
          | _ => none) :: x.2)) (z, []) l).2.length = l.length from this b.insts z
  intro l z
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, List.length_cons, ih]

/-! ## Plain instructions -/

/-- **Plain instruction items**: instructions with no direct branch
target. -/
def PlainI (its : List Item) : Prop :=
  ∀ it ∈ its, ∃ d, it = .d d ∧ isIns d = true ∧ dirTgt d = none

theorem PlainI.nil : PlainI [] := fun _ h => by simp at h

theorem PlainI.append {A B : List Item} (hA : PlainI A) (hB : PlainI B) : PlainI (A ++ B) := fun it h =>
  (List.mem_append.mp h).elim (hA it) (hB it)

theorem PlainI.cons {it : Item} {A : List Item} (h : ∃ d, it = .d d ∧ isIns d = true ∧ dirTgt d = none)
    (hA : PlainI A) : PlainI (it :: A) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h
  · exact hA x hx

theorem PlainI.single {w : RegWidth} (op : Operation w) (h : dirTgt (.instr ⟨w, op⟩) = none) :
    PlainI [Scc.Emit.A64.ins op] :=
  .cons ⟨_, rfl, rfl, h⟩ .nil

theorem PlainI.ite {c : Prop} [Decidable c] {A B : List Item} (hA : PlainI A) (hB : PlainI B) :
    PlainI (if c then A else B) := by
  split
  · exact hA
  · exact hB

/-- A plain instruction item: no label, no direct branch target. -/
theorem PlainI.one {w : RegWidth} (op : Operation w) (h : dirTgt (.instr ⟨w, op⟩) = none) :
    ∃ d, Scc.Emit.A64.ins op = Item.d d ∧ isIns d = true ∧ dirTgt d = none := ⟨_, rfl, rfl, h⟩

/-- One step of a `PlainI` proof of an emitter helper. -/
macro "plain_step" : tactic => `(tactic| first
  | exact PlainI.nil
  | (refine PlainI.single _ ?_; first | rfl | (rename_i w; cases w <;> rfl))
  | (refine PlainI.cons (PlainI.one _ ?_) ?_; first | rfl | (rename_i w; cases w <;> rfl) | skip)
  | apply PlainI.append
  | apply PlainI.ite)

macro "plain_tac" : tactic => `(tactic| repeat plain_step)

theorem movImm_plain (d : XReg) (n : Int) : PlainI (movImm d n) := by
  unfold movImm
  dsimp only
  split
  · plain_tac
  · refine PlainI.cons ⟨_, rfl, rfl, rfl⟩ fun it hit => ?_
    obtain ⟨⟨h, k⟩, -, rfl⟩ := List.mem_map.mp hit
    exact ⟨_, rfl, rfl, rfl⟩

theorem addImm_plain (d s : RegOrSp .W64) (n : Int) : PlainI (addImm d s n) := by
  unfold addImm
  split
  · plain_tac
  · plain_tac
  · exact (movImm_plain _ _).append (by plain_tac)

theorem addrOf_plain (d : XReg) (l : Label) : PlainI (addrOf d l) := by unfold addrOf; plain_tac

theorem ldrOff_plain (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) :
    PlainI (ldrOff w rt base off) := by
  unfold ldrOff
  split
  · cases w <;> plain_tac
  · split
    · cases w <;> plain_tac
    · refine (movImm_plain _ _).append ?_
      cases w <;> plain_tac

theorem strOff_plain (w : RegWidth) (rt : XReg) (base : RegOrSp .W64) (off : Int) :
    PlainI (strOff w rt base off) := by
  unfold strOff
  split
  · cases w <;> plain_tac
  · split
    · cases w <;> plain_tac
    · refine (movImm_plain _ _).append ?_
      cases w <;> plain_tac

theorem strZeroOff_plain (w : RegWidth) (base : RegOrSp .W64) (off : Int) : PlainI (strZeroOff w base off) := by
  unfold strZeroOff
  split
  · cases w <;> plain_tac
  · split
    · cases w <;> plain_tac
    · refine (movImm_plain _ _).append ?_
      cases w <;> plain_tac

theorem ldrbOff_plain (rt : XReg) (base : RegOrSp .W64) (off : Int) : PlainI (ldrbOff rt base off) := by
  unfold ldrbOff
  split
  · plain_tac
  · split
    · plain_tac
    · exact (movImm_plain _ _).append (by plain_tac)

theorem subWordStoreDyn_plain (w : Scc.IR.Width) (release : Bool) : PlainI (subWordStoreDyn w release) := by
  unfold subWordStoreDyn
  refine PlainI.append (PlainI.append (by plain_tac) (movImm_plain _ _)) ?_
  refine PlainI.cons (PlainI.one _ rfl) (PlainI.cons (PlainI.one _ rfl) (PlainI.cons (PlainI.one _ rfl)
    (PlainI.cons (PlainI.one _ rfl) (PlainI.cons (PlainI.one _ rfl) (PlainI.cons ?_ .nil)))))
  split
  · exact PlainI.one _ rfl
  · exact PlainI.one _ rfl

theorem cmpImm_plain (w : RegWidth) (a : XReg) (n : Int) : PlainI (cmpImm w a n) := by
  unfold cmpImm
  split
  · cases w <;> plain_tac
  · refine (movImm_plain _ _).append ?_
    cases w <;> plain_tac

theorem syscall_plain (nr : Nat) : PlainI (syscall nr) := by
  unfold syscall
  exact (movImm_plain _ _).append (by plain_tac)

theorem binOp_plain (op : Scc.IR.BinOp) : PlainI (binOp op) := by
  cases op <;> simp only [binOp] <;> plain_tac

theorem unOp_plain (op : Scc.IR.UnOp) : PlainI (unOp op) := by
  cases op <;> simp only [unOp]
  · plain_tac
  · plain_tac
  · plain_tac
  · exact PlainI.append (PlainI.append (by plain_tac) (movImm_plain _ _)) (by plain_tac)

theorem extOp_plain (s : Bool) (w : Scc.IR.Width) : PlainI (extOp s w) := by
  cases w <;> simp only [extOp] <;> first | exact PlainI.nil | (split <;> plain_tac)

theorem plainLoad_plain (w : Scc.IR.Width) (disp : Int) : PlainI (plainLoad w disp) := by
  cases w <;> simp only [plainLoad]
  · exact ldrbOff_plain _ _ _
  · split
    · plain_tac
    · split
      · plain_tac
      · exact (movImm_plain _ _).append (by plain_tac)
  · exact ldrOff_plain _ _ _ _
  · exact ldrOff_plain _ _ _ _

theorem subSat_plain (d a b : XReg) : PlainI (subSat d a b) := by unfold subSat; plain_tac

theorem leave_plain (c : FnCtx) : PlainI c.leave := by
  unfold FnCtx.leave
  exact ((ldrOff_plain _ _ _ _).append (ldrOff_plain _ _ _ _)).append (addImm_plain _ _ _)

/-! ### The context's loads and stores -/

theorem getReg_plain {c : FnCtx} {t : XReg} {r : Scc.IR.Reg} {l : List Item} (h : c.getReg t r = .ok l) :
    PlainI l := by
  unfold FnCtx.getReg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ldrOff_plain _ _ _ _

theorem setReg_plain {c : FnCtx} {r : Scc.IR.Reg} {t : XReg} {l : List Item} (h : c.setReg r t = .ok l) :
    PlainI l := by
  unfold FnCtx.setReg at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact strOff_plain _ _ _ _

theorem getOp_plain {c : FnCtx} {t : XReg} {o : Scc.IR.Operand} {l : List Item} (h : c.getOp t o = .ok l) :
    PlainI l := by
  cases o with
  | reg r => exact getReg_plain h
  | imm v =>
    simp only [FnCtx.getOp, Except.ok.injEq] at h
    subst h
    exact movImm_plain _ _

theorem getAddr_plain {c : FnCtx} {t : XReg} {a : Scc.IR.Addr} {l : List Item} (h : c.getAddr t a = .ok l) :
    PlainI l := by
  unfold FnCtx.getAddr at h
  simp only [bind, Except.bind] at h
  cases hb : c.getReg t a.base with
  | error e => rw [hb] at h; cases h
  | ok base =>
    rw [hb] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (getReg_plain hb).append (PlainI.ite .nil (addImm_plain _ _ _))

theorem getArgs_plain {c : FnCtx} {args : List Scc.IR.Operand} {l : List Item} (h : c.getArgs args = .ok l) :
    PlainI l := by
  unfold FnCtx.getArgs at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · generalize hF : forIn (m := Except String) (args.zip argRegs) ([] : List Item) _ = F at h
    cases F with
    | error e => cases h
    | ok out =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine forIn_inv PlainI hF .nil ?_
      intro x _ s hs r hr
      try simp only [bind, Except.bind] at hr
      cases ho : c.getOp x.2 x.1 with
      | error e => rw [ho] at hr; cases hr
      | ok l' =>
        rw [ho] at hr
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        exact hs.append (getOp_plain ho)

theorem callArgs_plain {c : FnCtx} {args : List Scc.IR.Operand} {base : Nat} {l : List Item}
    (h : c.callArgs args base = .ok l) : PlainI l := by
  unfold FnCtx.callArgs at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · generalize hF : forIn (m := Except String) ((args.drop argRegs.length).zipIdx) ([] : List Item) _ = F at h
    cases F with
    | error e => cases h
    | ok out =>
      cases hg : c.getArgs (args.take argRegs.length) with
      | error e => simp [hg] at h
      | ok l2 =>
        simp only [hg, pure, Except.pure, Except.ok.injEq] at h
        subst h
        refine PlainI.append (forIn_inv PlainI hF .nil ?_) (getArgs_plain hg)
        intro x _ s hs r hr
        try simp only [bind, Except.bind] at hr
        cases ho : c.getOp .X9 x.1 with
        | error e => rw [ho] at hr; cases hr
        | ok l' =>
          rw [ho] at hr
          simp only [pure, Except.pure, Except.ok.injEq] at hr
          subst hr
          exact (hs.append (getOp_plain ho)).append (strOff_plain _ _ _ _)

theorem setResults_plain {c : FnCtx} {ds : List Scc.IR.Reg} {l : List Item} (h : c.setResults ds = .ok l) :
    PlainI l := by
  unfold FnCtx.setResults at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · generalize hF : forIn (m := Except String) (ds.zip argRegs) ([] : List Item) _ = F at h
    cases F with
    | error e => cases h
    | ok out =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine forIn_inv PlainI hF .nil ?_
      intro x _ s hs r hr
      try simp only [bind, Except.bind] at hr
      cases ho : c.setReg x.1 x.2 with
      | error e => rw [ho] at hr; cases hr
      | ok l' =>
        rw [ho] at hr
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        exact hs.append (setReg_plain ho)

/-! ## A function's items, assembled -/

/-- `instsItems` is the flattened `codesFrom` of the instructions. -/
theorem instsItems_eq (c : FnCtx) : ∀ (k : Nat) (is : List Scc.IR.Inst),
    instsItems c k is = (codesFrom c.inst k is).map List.flatten
  | _, [] => rfl
  | k, i :: is => by
    simp only [instsItems, codesFrom, bind, Except.bind]
    cases c.inst k i with
    | error e => rfl
    | ok ys =>
      rw [instsItems_eq c (k + 1) is]
      cases codesFrom c.inst (k + 1) is <;> rfl

/-- **A function's items** (`emitFunc`): its two assembler lines and its
name's label, the frame allocation, the frame record, the parameters'
stores (plain instructions), each block's label and code
(`blockCode`, numbered as the emitter numbers them) and the stubs. -/
theorem emitFunc_items {abortFn : String} {growth : Option Scc.IR.Growth} {areas : List (Scc.IR.Sym × Nat)}
    {fi : Nat} {f : Scc.IR.Func} {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi f = .ok (items, sps)) :
    ∃ params bodyL, PlainI params ∧
      codesFromN (fun k b => blockCode (fnCtx abortFn growth areas fi f) k b) blockAdv 0 f.blocks = .ok bodyL ∧
      items = [.raw ".p2align 2", .raw s!".type {f.name}, %function", lbl f.name] ++
        allocOf (fnCtx abortFn growth areas fi f) f.checkStack ++ saveOf (fnCtx abortFn growth areas fi f) ++
        params ++ bodyL.flatten ++ stubsOf (fnCtx abortFn growth areas fi f) f abortFn growth := by
  unfold emitFunc at h
  generalize hc : fnCtx abortFn growth areas fi f = c at h ⊢
  dsimp only at h
  by_cases hlab : labelOk f.name = true
  · by_cases hlen : f.params.length > Scc.IR.maxArgs
    · simp [hlab, hlen, bind, Except.bind] at h
    · simp only [hlab, hlen, ite_true, ite_false, bind, Except.bind] at h
      -- the parameters' stores
      generalize hP1 : forIn (m := Except String) (f.params.zip argRegs) ([] : List Item) _ = P1 at h
      cases P1 with
      | error e => cases h
      | ok p1 =>
        dsimp only at h
        have hp1 : PlainI p1 := by
          refine forIn_inv PlainI hP1 .nil ?_
          intro x _ s hs r hr
          cases hs' : c.setReg x.1 x.2 with
          | error e => rw [hs'] at hr; cases hr
          | ok v =>
            rw [hs'] at hr
            simp only [pure, Except.pure, Except.ok.injEq] at hr
            subst hr
            exact hs.append (setReg_plain hs')
        generalize hP2 : forIn (m := Except String) (f.params.drop argRegs.length).zipIdx p1 _ = P2 at h
        cases P2 with
        | error e => cases h
        | ok params =>
          dsimp only at h
          have hparams : PlainI params := by
            refine forIn_inv PlainI hP2 hp1 ?_
            intro x _ s hs r hr
            cases hs' : c.setReg x.1 .X9 with
            | error e => rw [hs'] at hr; cases hr
            | ok v =>
              rw [hs'] at hr
              simp only [pure, Except.pure, Except.ok.injEq] at hr
              subst hr
              exact (hs.append (ldrOff_plain _ _ _ _)).append (setReg_plain hs')
          -- the blocks
          generalize hB : forIn (m := Except String) (f.blocks.zip (Scc.IR.StackMap.callMaps f))
            (([] : List Item), ([] : List Safepoint), 0) _ = B at h
          cases B with
          | error e => cases h
          | ok res =>
            dsimp only at h
            have key := forIn_appendsN
              (fun k (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) => blockCode c k x.1)
              (fun x => blockAdv x.1) _ (f.blocks.zip (Scc.IR.StackMap.callMaps f)) ?step [] [] 0 res hB
            case step =>
              intro x hx code s k y hy
              have hlen : x.2.length = x.1.insts.length := by
                obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
                simp only [List.getElem_zip]
                exact callMaps_inner_length f j (by simpa [callMaps_length] using hj)
              dsimp only at hy
              cases hbl : c.blockLabel x.1.label with
              | error e => rw [hbl] at hy; dsimp only at hy; cases hy
              | ok l =>
                rw [hbl] at hy
                dsimp only at hy
                generalize hF : forIn (m := Except String) (x.1.insts.zip x.2) (s, k, [lbl l]) _ = F at hy
                cases F with
                | error e => cases hy
                | ok v =>
                  have ikey := forIn_appends'
                    (fun k (x : Scc.IR.Inst × Option Scc.IR.StackMap.Entry) => c.inst k x.1) hF ?istep
                  case istep =>
                    intro x' _ s' k' code' y' hy'
                    try dsimp only at hy'
                    cases hi : c.inst k' x'.1 with
                    | error e => rw [hi] at hy'; dsimp only at hy'; cases hy'
                    | ok ys =>
                      rw [hi] at hy'
                      dsimp only at hy'
                      split at hy'
                      · split at hy'
                        · split at hy'
                          · cases hy'
                          · split at hy'
                            · cases hy'
                            · cases hy'; exact ⟨ys, _, rfl, rfl⟩
                        · cases hy'; exact ⟨ys, _, rfl, rfl⟩
                      · cases hy'; exact ⟨ys, _, rfl, rfl⟩
                  obtain ⟨cs, hcs, hk, hcode⟩ := ikey
                  rw [codesFrom_zip_fst (fun k i => c.inst k i) k x.1.insts x.2 hlen] at hcs
                  dsimp only at hy
                  have hk' : v.2.1 = k + x.1.insts.length := by rw [hk, List.length_zip, hlen, Nat.min_self]
                  rw [hk'] at hy
                  cases ht : c.term (k + x.1.insts.length) x.1.term with
                  | error e => rw [ht] at hy; dsimp only at hy; cases hy
                  | ok t =>
                    rw [ht] at hy
                    simp only [pure, Except.pure, Except.ok.injEq] at hy
                    subst hy
                    refine ⟨lbl l :: (cs.flatten ++ t), v.1, ?_, ?_⟩
                    · simp only [blockCode, blockItems, instsItems_eq, hbl, hcs, ht, bind, Except.bind,
                        Except.map, pure, Except.pure]
                    · rw [hcode]
                      simp only [blockAdv, List.cons_append, List.nil_append, Nat.add_assoc]
            obtain ⟨xs, hxs, hres⟩ := key
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine ⟨params, xs, hparams, ?_, ?_⟩
            · rw [← hxs]
              clear hxs hres hB hP2 hP1 hparams hp1
              have hl := callMaps_length f
              generalize Scc.IR.StackMap.callMaps f = ms at hl
              suffices ∀ (k : Nat) (bs : List Scc.IR.Block) (ms : List (List (Option Scc.IR.StackMap.Entry))),
                  ms.length = bs.length →
                  codesFromN (fun k b => blockCode c k b) blockAdv k bs =
                    codesFromN (fun k (x : Scc.IR.Block × List (Option Scc.IR.StackMap.Entry)) => blockCode c k x.1)
                      (fun x => blockAdv x.1) k (bs.zip ms) from this 0 f.blocks ms hl
              intro k bs
              induction bs generalizing k with
              | nil => intro ms _; cases ms <;> rfl
              | cons b bs ih =>
                intro ms hms
                cases ms with
                | nil => simp at hms
                | cons m ms =>
                  simp only [List.zip_cons_cons, codesFromN, ih (k + blockAdv b) ms (by simpa using hms)]
            · rw [hres]
              simp only [List.nil_append, allocOf, saveOf, stubsOf, growStubOf, abortStubOf,
                Scc.Cert.Code1A64.hasAddChk, List.append_assoc]
              try rfl
  · simp [hlab, bind, Except.bind] at h

end Spike.Lib.LowerA64
