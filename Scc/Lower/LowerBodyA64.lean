import Scc.Lower.InvBodyA64

/-!
# The AArch64 items of an `Accepted0` body

The items `emitFunc` (`Scc/Emit/A64.lean`) emits for `func0 name r`
(`Scc/Lower/Inv.lean`), the function `lowerAll` makes of an `Accepted0`
program's `main`: one block `entry` holding the body's instructions, all
`addChk`, and `ret r.ret`.

* `blockLabel_func0`: the entry block's label is `c.prefix ++ "0_entry"`;
* `bodyItems c r`: the code of the body, its instructions' (`FnCtx.inst`),
  in order and numbered from 0 (`codesFrom`), then its `ret`'s
  (`FnCtx.term`, numbered after them);
* `emitFunc_func0_items`: the function's items are a prologue, the entry
  block's label, `bodyItems c r`, then the stubs. Nothing comes between the
  label and the body: a call's safepoint goes to the separate safepoint
  list (an `addChk`'s fall-through label and the `ret`'s label are part of
  their codes, numbered by the instruction counter, `x{k}`);
* `addChkOk_func0`: in that context every instruction of the body emits
  (its registers are the function's slots, `funcRegs_func0_eq`), and so
  does every returned operand;
* `bodyItems_eq_flatMap`: in a frame of at most 32 KiB, `bodyItems` is per
  instruction the operands' loads into `x9`/`x10`, `adds x9, x9, x10`,
  `b.cs` to the overflow abort, the fall-through's label and `str x9` into
  the destination's slot (`addChkCode`, `inst_addChk`), then the result
  into `x0`, the frame's exit, the return site's label and `ret`
  (`term_ret1`).
-/

open Scc.IR Scc.Lower Scc.Lower.Inv

namespace Scc.Lower.InvA64

open Scc.Emit.A64
open StackMap (instUses instDefs opRegs)

/-! ## The body's code -/

/-- The codes `g k x` of the elements `x` of a list, the counter `k` from
`k` on, advancing by one per element (as `emitFunc`'s instruction counter
does). -/
def codesFrom {α : Type} (g : Nat → α → Except String (List Item)) :
    Nat → List α → Except String (List (List Item))
  | _, [] => .ok []
  | k, x :: l => do
    let ys ← g k x
    let xs ← codesFrom g (k + 1) l
    pure (ys :: xs)

/-- **The code of an `Accepted0` body** in context `c`: its instructions',
in order, numbered from 0, then its `ret`'s, numbered after them (the
emitter's instruction counter: an `addChk`'s and a `ret`'s labels read
it). -/
def bodyItems (c : FnCtx) (r : Res) : Except String (List Item) := do
  let xs ← codesFrom c.inst 0 r.insts
  let t ← c.term r.insts.length (.ret r.ret)
  pure (xs.flatten ++ t)

theorem sanitize_entry : sanitize "entry" = "entry" := by
  rw [sanitize, String.map_eq_internal]; decide

/-- **The entry block's label** in the context of `func0 name r`. -/
theorem blockLabel_func0 (abortFn : String) (growth : Option IR.Growth)
    (areas : List (IR.Sym × Nat)) (fi : Nat) (name : IR.Sym) (r : Res) :
    (fnCtx abortFn growth areas fi (func0 name r)).blockLabel "entry" =
      .ok ((fnCtx abortFn growth areas fi (func0 name r)).prefix ++ "0_entry") := by
  generalize hc : fnCtx abortFn growth areas fi (func0 name r) = c
  have hb : c.blocks = ["entry"] := by rw [← hc]; rfl
  simp only [FnCtx.blockLabel, hb]
  rw [show (["entry"] : List IR.Label).idxOf? "entry" = some 0 by decide, sanitize_entry]
  simp only [toString, String.append_assoc]
  rfl

/-! ## `emitFunc`'s loops -/

/-- **A loop that appends each element's code**: if each step on `x` at
counter `k` appends `g k x` to the code and advances the counter by one
(whatever else it does to its state `σ`), the loop over `l` appends the
codes of `l` in order, numbered from its counter, and advances the counter
by its length. -/
theorem forIn_appends {α σ : Type} (g : Nat → α → Except String (List Item))
    (body : α → σ × Nat × List Item → Except String (ForInStep (σ × Nat × List Item))) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s k code y, body x (s, k, code) = .ok y →
      ∃ ys s', g k x = .ok ys ∧ y = .yield (s', k + 1, code ++ ys)) →
    ∀ (s : σ) (k : Nat) (code : List Item) (res : σ × Nat × List Item),
      forIn l (s, k, code) body = .ok res →
      ∃ xs, codesFrom g k l = .ok xs ∧ res.2.1 = k + l.length ∧ res.2.2 = code ++ xs.flatten
  | [], _, s, k, code, res, h => by
    rw [List.forIn_nil] at h
    cases h; exact ⟨[], rfl, by simp, by simp⟩
  | x :: l, hb, s, k, code, res, h => by
    rw [List.forIn_cons] at h
    cases hx : body x (s, k, code) with
    | error e => rw [hx] at h; cases h
    | ok y =>
      obtain ⟨ys, s', hg, rfl⟩ := hb x List.mem_cons_self s k code y hx
      rw [hx] at h
      obtain ⟨xs, hm, h1, h2⟩ := forIn_appends g body l (fun x hx => hb x (List.mem_cons_of_mem _ hx))
        s' (k + 1) (code ++ ys) res h
      refine ⟨ys :: xs, ?_, by simp [h1]; omega, by simp [h2]⟩
      simp only [codesFrom, hg, hm, bind, Except.bind, pure, Except.pure]

/-- `forIn_appends` with the loop's result first. -/
theorem forIn_appends' {α σ : Type} (g : Nat → α → Except String (List Item))
    {body : α → σ × Nat × List Item → Except String (ForInStep (σ × Nat × List Item))}
    {l : List α} {s : σ} {k : Nat} {code : List Item} {res : σ × Nat × List Item}
    (h : forIn l (s, k, code) body = .ok res)
    (hb : ∀ x ∈ l, ∀ s k code y, body x (s, k, code) = .ok y →
      ∃ ys s', g k x = .ok ys ∧ y = .yield (s', k + 1, code ++ ys)) :
    ∃ xs, codesFrom g k l = .ok xs ∧ res.2.1 = k + l.length ∧ res.2.2 = code ++ xs.flatten :=
  forIn_appends g body l hb s k code res h

/-- The safepoint maps of `func0 name r`: one block, one entry per
instruction. -/
theorem callMaps_func0 (name : IR.Sym) (r : Res) :
    ∃ ms : List (Option IR.StackMap.Entry), IR.StackMap.callMaps (func0 name r) = [ms] ∧
      ms.length = r.insts.length := by
  refine ⟨_, rfl, ?_⟩
  simp only [func0, List.length_map]
  generalize IR.StackMap.liveIns _ = ins
  generalize IR.StackMap.union _ _ = z
  generalize r.insts = l
  suffices ∀ l : List IR.Inst, ∀ z, (List.foldr (fun i (x : List IR.Reg × List (Option (List IR.Reg))) =>
      (IR.StackMap.liveBefore i x.1, (match i with
          | IR.Inst.call ds _ _ => some (List.filter (fun r => !ds.contains r) x.1)
          | _ => none) :: x.2)) (z, []) l).2.length = l.length from this l z
  intro l z
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, List.length_cons, ih]

/-- The codes over a zip with a function of the first components. -/
theorem codesFrom_zip_fst {α β : Type} (g : Nat → α → Except String (List Item)) :
    ∀ (k : Nat) (l : List α) (ms : List β), ms.length = l.length →
      codesFrom (fun k x => g k x.1) k (l.zip ms) = codesFrom g k l
  | _, [], _, _ => rfl
  | k, a :: l, b :: ms, h => by
    simp only [List.zip_cons_cons, codesFrom, codesFrom_zip_fst g (k + 1) l ms (by simpa using h)]
  | _, _ :: _, [], h => by simp at h

/-! ## The function's items -/

/-- **The items of `func0 name r`**: a prologue, the entry block's label,
the body's code `bodyItems`, then the stubs, with nothing between the label
and the body. -/
theorem emitFunc_func0_items {abortFn : String} {growth : Option IR.Growth}
    {areas : List (IR.Sym × Nat)} {fi : Nat} {name : IR.Sym} {r : Res}
    {items : List Item} {sps : List Safepoint}
    (h : emitFunc abortFn growth areas fi (func0 name r) = .ok (items, sps))
    (hAll : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) :
    ∃ pre stubs body, bodyItems (fnCtx abortFn growth areas fi (func0 name r)) r = .ok body ∧
      items = pre ++ [lbl ((fnCtx abortFn growth areas fi (func0 name r)).prefix ++ "0_entry")] ++
        body ++ stubs := by
  obtain ⟨ms, hm, hlen⟩ := callMaps_func0 name r
  have hlab := blockLabel_func0 abortFn growth areas fi name r
  unfold emitFunc at h
  generalize hc : fnCtx abortFn growth areas fi (func0 name r) = c at h hlab ⊢
  rw [hm] at h
  by_cases hn : labelOk name = true
  · simp only [func0, hn, ite_true, List.length_nil, gt_iff_lt,
      show ¬ (IR.maxArgs < 0) from Nat.not_lt_zero _, ite_false, List.zip_nil_left, List.drop_nil,
      List.zipIdx_nil, List.forIn_nil, List.zip_cons_cons, List.zip_nil_right, List.forIn_cons, bind,
      Except.bind, pure, Except.pure, hlab] at h
    split at h
    · cases h
    · rename_i res hres
      revert hres
      generalize hF : forIn (m := Except String) (r.insts.zip ms) (([] : List Safepoint), 0, [lbl (c.prefix ++ "0_entry")]) _ = F
      intro hres
      cases F with
      | error e => cases hres
      | ok v =>
        obtain ⟨xs, hxs, hk, hcode⟩ := forIn_appends' (fun k (x : IR.Inst × Option IR.StackMap.Entry) =>
          c.inst k x.1) hF (by
          intro x hx s k code y hy
          obtain ⟨d, a, b, hdab⟩ := hAll x.1 (List.of_mem_zip hx).1
          simp only [hdab] at hy ⊢
          cases hi : c.inst k (.addChk d a b) with
          | error e => rw [hi] at hy; cases hy
          | ok ys =>
            rw [hi] at hy
            dsimp only at hy
            split at hy
            · split at hy
              · split at hy
                · cases hy
                · split at hy
                  · cases hy
                  · cases hy; exact ⟨ys, _, rfl, rfl⟩
              · cases hy; exact ⟨ys, _, rfl, rfl⟩
            · cases hy; exact ⟨ys, _, rfl, rfl⟩)
        rw [codesFrom_zip_fst (fun k i => c.inst k i) 0 r.insts ms hlen] at hxs
        have hk' : v.2.1 = r.insts.length := by rw [hk]; simp [hlen]
        dsimp only at hres
        rw [hk'] at hres
        cases ht : c.term r.insts.length (.ret r.ret) with
        | error e => rw [ht] at hres; cases hres
        | ok t =>
          rw [ht] at hres
          cases hres
          cases h
          rw [hcode]
          generalize hP : (_ : List Item) ++ _ ++ _ ++ ([] : List Item) = P
          generalize hS : ((if growth.isSome = true then _ else _) ++ _ : List Item) = S
          refine ⟨P, S, xs.flatten ++ t, by simp only [bodyItems, hxs, ht, bind, Except.bind, pure,
            Except.pure], ?_⟩
          simp only [List.nil_append, List.append_assoc]
  · simp [func0, hn, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-! ## The body's code, instruction by instruction -/

/-- The items of a successful emission (`[]` on an error, which the lemmas'
hypotheses exclude). -/
def okL (e : Except String (List Item)) : List Item := match e with | .ok l => l | .error _ => []

/-- The offset of a successful slot lookup (`0` on an error). -/
def okI (e : Except String Int) : Int := match e with | .ok n => n | .error _ => 0

/-- The code of an `addChk` at counter `k` with its operands' loads and its
destination's offset (`inst_addChk`); any other instruction has none here. -/
def addChkCode (c : FnCtx) (k : Nat) : IR.Inst → List Item
  | .addChk d a b => okL (c.getOp .X9 a) ++ okL (c.getOp .X10 b) ++
      addChecked .X9 .X9 .X10 (c.local "abort_overflow") ++ [lbl (c.local s!"x{k}")] ++
      [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 (okI (c.slotOff d)), none⟩⟩)]
  | _ => []

/-- An instruction is an `addChk` whose operands load and whose
destination has a slot. -/
def AddChkOk (c : FnCtx) (i : IR.Inst) : Prop :=
  ∃ d a b la lb off, i = .addChk d a b ∧ c.getOp .X9 a = .ok la ∧ c.getOp .X10 b = .ok lb ∧
    c.slotOff d = .ok off

/-- The code of an `addChk` that emits is `addChkCode`. -/
theorem inst_addChkCode {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) (k : Nat)
    {i : IR.Inst} (h : AddChkOk c i) : c.inst k i = .ok (addChkCode c k i) := by
  obtain ⟨d, a, b, la, lb, off, rfl, ha, hb, hd⟩ := h
  rw [inst_addChk hf hs k ha hb hd]
  simp only [addChkCode, ha, hb, hd, okL, okI]

/-- The codes of instructions that all emit, numbered from `k`. -/
theorem codesFrom_addChkCode {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) :
    ∀ (l : List IR.Inst) (k : Nat), (∀ i ∈ l, AddChkOk c i) →
      codesFrom c.inst k l = .ok ((l.zipIdx k).map fun (i, j) => addChkCode c j i)
  | [], _, _ => rfl
  | i :: l, k, h => by
    simp only [codesFrom, inst_addChkCode hf hs k (h i List.mem_cons_self),
      codesFrom_addChkCode hf hs l (k + 1) (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      List.zipIdx_cons, List.map_cons, bind, Except.bind, pure, Except.pure]

/-- **The body's code as one list**: per instruction the operands' loads
into `x9`/`x10`, `adds x9, x9, x10`, `b.cs` to the overflow abort, `str x9`
into the destination's slot (`addChkCode`, the `j`th with its label `x{j}`); then `v` into
`x0`, the frame's exit, the return site's label `x{n}` (`n` the number of instructions) and
`ret`. -/
theorem bodyItems_eq_flatMap {c : FnCtx} (hf : FrameOk c) (hs : c.frame ≤ 32768) {r : Res}
    (hI : ∀ i ∈ r.insts, AddChkOk c i) {v : IR.Operand} (hr : r.ret = [v]) {lv : List Item}
    (hv : c.getOp .X0 v = .ok lv) :
    bodyItems c r = .ok (r.insts.zipIdx.flatMap (fun (i, j) => addChkCode c j i) ++
      (lv ++ c.leave ++ [lbl (c.local s!"x{r.insts.length}"), ret])) := by
  simp only [bodyItems, codesFrom_addChkCode hf hs r.insts 0 hI, hr, term_ret1 _ hv, bind,
    Except.bind, pure, Except.pure, List.flatMap_def]

/-! ## Every instruction emits -/

/-- An operand whose registers are slots loads. -/
theorem getOp_ok {c : FnCtx} {t : XReg} {o : IR.Operand} (h : ∀ x ∈ opRegs o, x ∈ c.slots) :
    ∃ l, c.getOp t o = .ok l := by
  cases o with
  | imm v => exact ⟨_, rfl⟩
  | reg x =>
    obtain ⟨i, hi, -, hoff⟩ := slotOff_ok (h x (by simp [opRegs]))
    exact ⟨_, by simp only [FnCtx.getOp, FnCtx.getReg, hoff, bind, Except.bind, pure, Except.pure]; rfl⟩

/-- **Every instruction of the body is an `addChk` that emits** in the
context of `func0 name r` (its registers are the function's slots). -/
theorem addChkOk_func0 (abortFn : String) (growth : Option IR.Growth)
    (areas : List (IR.Sym × Nat)) (fi : Nat) (name : IR.Sym) {r : Res}
    (hAll : ∀ i ∈ r.insts, ∃ d a b, i = .addChk d a b) :
    (∀ i ∈ r.insts, AddChkOk (fnCtx abortFn growth areas fi (func0 name r)) i) ∧
      ∀ v ∈ r.ret, ∃ l, (fnCtx abortFn growth areas fi (func0 name r)).getOp .X0 v = .ok l := by
  have hs : ∀ x, x ∈ (r.insts.flatMap (fun i => instDefs i ++ instUses i) ++ r.ret.flatMap opRegs) →
      x ∈ (fnCtx abortFn growth areas fi (func0 name r)).slots := fun x hx => by
    rw [fnCtx_slots, funcRegs_func0_eq name hAll, mem_foldl_dstep]; exact .inr hx
  refine ⟨fun i hi => ?_, fun v hv => getOp_ok fun x hx => hs x (by simp; exact .inr ⟨v, hv, hx⟩)⟩
  obtain ⟨d, a, b, rfl⟩ := hAll i hi
  have hm : ∀ x ∈ instDefs (.addChk d a b) ++ instUses (.addChk d a b), x ∈ _ := fun x hx =>
    hs x (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hi, hx⟩))
  obtain ⟨la, ha⟩ := getOp_ok (t := .X9) (o := a) fun x hx => hm x (by simp [instUses, instDefs, hx])
  obtain ⟨lb, hb⟩ := getOp_ok (t := .X10) (o := b) fun x hx => hm x (by simp [instUses, instDefs, hx])
  obtain ⟨_, _, -, hd⟩ := slotOff_ok (hm d (by simp [instDefs]))
  exact ⟨d, a, b, la, lb, _, rfl, ha, hb, hd⟩

end Scc.Lower.InvA64
