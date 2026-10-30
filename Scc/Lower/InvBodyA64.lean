import Scc.Lower.InvBody
import Scc.Lower.InvA64

/-!
# The AArch64 context of an `Accepted0` body

What the per-construct code lemmas of `Scc/Lower/InvA64.lean` and the
per-step lemmas of `Scc/Lower/InvBody.lean` assume of the context
`A64.ctxOf p fi (func0 name r)` an `Accepted0` body is emitted in, proved
from the closed form `lower0 … = some r`:

* `mem_funcRegs_func0`: the function's registers (its frame slots) are
  exactly the registers its instructions write; `funcRegs_length_func0`:
  there are at most `r.next` of them (one per `+`);
* `ctxOf_func0_out`: no outgoing argument area (the body makes no call);
  `ctxOf_frame_mod16`: every frame is a multiple of 16 bytes;
  `ctxOf_func0_frame`: the frame of the body is `align16 (8 * n + 16)`
  bytes for its `n` slots; `ctxOf_func0_frame_le`: at most 4095 bytes (so
  that `addImm sp sp ±frame` is one `add`/`sub` immediate) when the body has
  at most 508 `+`; `accepted0_frame_le`: so it is for every `Accepted0`
  body (`maxAdds0`);
* `bodyInv_func0`: `BodyInv` at the start of the body with the slots as
  `S`, and the registers the body writes and returns among the slots;
* `main_inv_a64`: on an `Accepted0` program that lowers and emits, the
  lowered IR, the closed form of `main`'s body and all of the above for the
  context `main` is emitted in.

The frame bound `c.frame ≤ 4095` the code of the prologue and the exit
needs follows from `Accepted0`'s bound on the body's `+`s (`maxAdds0`):
`accepted0_frame_le`, through `ctxOf_func0_frame_le` (the bound on the
body's length).
-/

open CoreLang CoreTerm
open Scc.IR Scc.Lower Scc.Lower.Inv

namespace Scc.Lower.InvA64

open Scc.Emit.A64
open StackMap (instUses instDefs opRegs)

/-! ## Removing repeats -/

/-- `funcRegs`'s fold keeps exactly the members of the accumulator and the list. -/
theorem mem_foldl_dstep {x : Reg} : ∀ (l acc : List Reg), x ∈ l.foldl dstep acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc => by simp
  | y :: l, acc => by
    rw [List.foldl_cons, mem_foldl_dstep l]
    unfold dstep
    by_cases h : acc.contains y = true
    · have : y ∈ acc := by simpa using h
      simp only [h, ite_true, List.mem_cons]
      constructor
      · rintro (h1 | h1)
        · exact .inl h1
        · exact .inr (.inr h1)
      · rintro (h1 | rfl | h1)
        · exact .inl h1
        · exact .inl this
        · exact .inr h1
    · simp only [h, Bool.false_eq_true, ite_false, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_assoc]

theorem nodup_foldl_dstep : ∀ (l acc : List Reg), acc.Nodup → (l.foldl dstep acc).Nodup
  | [], _, h => h
  | y :: l, acc, h => by
    rw [List.foldl_cons]
    refine nodup_foldl_dstep l _ ?_
    unfold dstep
    by_cases hy : acc.contains y = true
    · simp only [hy, ite_true]; exact h
    · simp only [hy, Bool.false_eq_true, ite_false]
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hy (by simpa using ha)

/-- A function's registers are pairwise distinct. -/
theorem funcRegs_nodup (f : Func) : (funcRegs f).Nodup :=
  nodup_foldl_dstep _ [] List.nodup_nil

/-! ## The registers of `func0` -/

theorem flatMap_eq_of {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ i ∈ l, f i = g i) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | i :: l, h => by
    simp only [List.flatMap_cons, h i (by simp), flatMap_eq_of l fun j hj => h j (by simp [hj])]

/-- The registers of `func0 name r` whose instructions are all `addChk`,
before removing repeats: each instruction's written and read registers,
then the returned ones. -/
theorem funcRegs_func0_eq (name : Sym) {r : Res} (hr : ∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) :
    funcRegs (func0 name r) =
      (r.insts.flatMap (fun i => instDefs i ++ instUses i) ++ r.ret.flatMap opRegs).foldl dstep [] := by
  unfold funcRegs
  show List.foldl dstep [] _ = _
  congr 1
  have hop : ∀ o : Operand, (match o with | .reg r => [r] | .imm _ => []) = opRegs o := by
    intro o; cases o <;> rfl
  simp only [func0, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  all_goals first
    | exact flatMap_eq_of _ fun i hi => by obtain ⟨d, p, q, rfl⟩ := hr i hi; cases p <;> cases q <;> rfl
    | simp [hop]

/-- **The registers of an `Accepted0` body's function are the registers its
instructions write.** -/
theorem mem_funcRegs_func0 (name : Sym) {arg : String} {e : Expr} {r : Res}
    (hr : lower0 [(arg, .unit, [])] 0 e = some r) (x : Reg) :
    x ∈ funcRegs (func0 name r) ↔ x ∈ defsOf r.insts := by
  rw [funcRegs_func0_eq name (lower0_insts_addChk _ _ _ _ hr).1, mem_foldl_dstep]
  obtain ⟨hu, hret⟩ := lower0_uses_defs hr
  constructor
  · rintro (h | h)
    · cases h
    · simp only [List.mem_append, List.mem_flatMap] at h
      rcases h with ⟨i, hi, hx⟩ | hx
      · rcases hx with hx | hx
        · exact List.mem_flatMap.mpr ⟨i, hi, hx⟩
        · exact hu i hi x hx
      · exact hret x (List.mem_flatMap.mpr hx)
  · intro h
    refine .inr (List.mem_append.mpr (.inl ?_))
    obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp h
    exact List.mem_flatMap.mpr ⟨i, hi, List.mem_append.mpr (.inl hx)⟩

/-- **At most one register per `+`.** -/
theorem funcRegs_length_func0 (name : Sym) {arg : String} {e : Expr} {r : Res}
    (hr : lower0 [(arg, .unit, [])] 0 e = some r) :
    (funcRegs (func0 name r)).length ≤ r.next := by
  obtain ⟨ha, hn⟩ := lower0_insts_addChk _ _ _ _ hr
  have hle := (funcRegs_nodup (func0 name r)).length_le_of_subset
    (l₂ := defsOf r.insts) fun x hx => (mem_funcRegs_func0 name hr x).mp hx
  rw [defsOf_length_addChk _ ha] at hle
  omega

/-! ## The frame -/

/-- **No outgoing argument area**: the body makes no call. -/
theorem ctxOf_func0_out (p : IR.Program) (fi : Nat) (name : Sym) {r : Res}
    (hr : ∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) : (A64.ctxOf p fi (func0 name r)).out = 0 := by
  show outWords _ _ = 0
  unfold outWords
  simp only [func0, List.foldl_cons, List.foldl_nil]
  obtain ⟨insts, ret, next, marked, here⟩ := r
  simp only at hr ⊢
  induction insts with
  | nil => simp
  | cons i is ih =>
    obtain ⟨d, p, q, rfl⟩ := hr i (by simp)
    simp only [List.foldl_cons]
    exact ih fun j hj => hr j (by simp [hj])

/-- **Every frame is a multiple of 16 bytes** (the outgoing area has an even
number of words). -/
theorem ctxOf_frame_mod16 (p : IR.Program) (fi : Nat) (f : Func) :
    (A64.ctxOf p fi f).frame % 16 = 0 := by
  show (8 * outWords _ f + align16 (8 * (funcRegs f).length + 16)) % 16 = 0
  have hm := align16_mod (8 * (funcRegs f).length + 16)
  have ho : outWords (StackMap.argAreas p argRegs.length) f % 2 = 0 := by
    unfold outWords; dsimp only; omega
  omega

/-- The frame of an `Accepted0` body: its slots and the saved `x29`/`x30`. -/
theorem ctxOf_func0_frame (p : IR.Program) (fi : Nat) (name : Sym) {r : Res}
    (hr : ∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) :
    (A64.ctxOf p fi (func0 name r)).frame =
      align16 (8 * (A64.ctxOf p fi (func0 name r)).slots.length + 16) := by
  rw [ctxOf_frameOk p fi (func0 name r), ctxOf_func0_out p fi name hr]
  simp

/-- **The frame bound from the body's length**: at most 4095 bytes when the
body has at most 508 `+`. -/
theorem ctxOf_func0_frame_le (p : IR.Program) (fi : Nat) (name : Sym) {arg : String} {e : Expr}
    {r : Res} (hr : lower0 [(arg, .unit, [])] 0 e = some r) (hn : r.next ≤ 508) :
    (A64.ctxOf p fi (func0 name r)).frame ≤ 4095 := by
  rw [ctxOf_func0_frame p fi name (lower0_insts_addChk _ _ _ _ hr).1]
  have hl := funcRegs_length_func0 name hr
  show align16 (8 * (funcRegs (func0 name r)).length + 16) ≤ 4095
  unfold align16
  omega

/-! ## The invariant at the start of the body -/

/-- **`BodyInv` at the start of an `Accepted0` body**, with the slots of its
context as `S`; the registers the body writes and returns are slots. -/
theorem bodyInv_func0 (p : IR.Program) (fi : Nat) (name : Sym) {arg : String} {e : Expr}
    {r : Res} (hr : lower0 [(arg, .unit, [])] 0 e = some r) :
    BodyInv (A64.ctxOf p fi (func0 name r)).slots 0 [(arg, .unit, [])] ∧
      (∀ d ∈ defsOf r.insts, d ∈ (A64.ctxOf p fi (func0 name r)).slots) ∧
      ∀ x ∈ r.ret.flatMap opRegs, x ∈ (A64.ctxOf p fi (func0 name r)).slots := by
  have hm := mem_funcRegs_func0 name hr
  refine ⟨bodyInv_init _ arg, fun d hd => (hm d).mpr hd, fun x hx => (hm x).mpr ?_⟩
  exact (lower0_uses_defs hr).2 x hx

/-! ## The whole program -/

/-- The counter at the end of an `Accepted0` body is at most `maxAdds0`
(508): one step per checked `+`. -/
theorem accepted0_next {d : Decl} (hd : Accepted0 [d] = true) {r : Res}
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) : r.next ≤ 508 := by
  have := lower0_next_adds _ _ _ _ hr
  have := accepted0_adds hd
  simp only [maxAdds0] at this
  omega

/-- **The frame of an `Accepted0` body is at most 4095 bytes**, in any
program and at any index: `addImm sp sp ±frame` is one immediate. -/
theorem accepted0_frame_le (p : IR.Program) (fi : Nat) (name : Sym) {d : Decl}
    (hd : Accepted0 [d] = true) {r : Res} (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) :
    (A64.ctxOf p fi (func0 name r)).frame ≤ 4095 :=
  ctxOf_func0_frame_le p fi name hr (accepted0_next hd hr)

/-- **The invariants of `main`'s context** (AArch64): on an `Accepted0`
program that lowers and emits, `main`'s body has the closed form `r`, the
lowered IR is the runtime functions `rt` then `func0 main r` (the
`rt.length`th function), and its context `c` has a frame of the size
`fnCtx` gives, a multiple of 16, no outgoing area, at most `r.next` slots,
which are exactly the registers the body writes (pairwise distinct, and
every register read is one of them), and `BodyInv` holds at the start of
the body; the frame is at most 4095 bytes (`Accepted0` bounds the body's
`+`s by `maxAdds0`). -/
theorem main_inv_a64 (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    {em : Scc.Lower.A64.Emitted} (h : Scc.Lower.A64.lowerAll? cfg [d] = .ok em) :
    ∃ r rt, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.arch cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      (Scc.Lower.A64.lowerAll cfg [d]).low.ir = progOf cfg.layout rt [func0 (Names.user "main") r] ∧
      (func0 (Names.user "main") r, rt.length) ∈
        (progOf cfg.layout rt [func0 (Names.user "main") r]).funcs.zipIdx ∧
      let c := A64.ctxOf (progOf cfg.layout rt [func0 (Names.user "main") r]) rt.length
        (func0 (Names.user "main") r)
      FrameOk c ∧ c.out = 0 ∧ c.frame % 16 = 0 ∧
      c.frame = align16 (8 * c.slots.length + 16) ∧ c.slots.length ≤ r.next ∧
      (∀ x, x ∈ c.slots ↔ x ∈ defsOf r.insts) ∧ (defsOf r.insts).Nodup ∧
      (∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) ∧ r.next = r.insts.length ∧
      BodyInv c.slots 0 [(d.arg, .unit, [])] ∧
      (∀ x ∈ r.ret.flatMap opRegs, x ∈ c.slots) ∧
      c.frame ≤ 4095 := by
  obtain ⟨r, rt, hr, hrt, hir⟩ := lowerAll_accepted0_a64 cfg hd h
  obtain ⟨ha, hn⟩ := lower0_insts_addChk _ _ _ _ hr
  refine ⟨r, rt, hr, hrt, hir, ?_, ?_⟩
  · simp [progOf, List.mem_zipIdx_iff_getElem?]
  · intro c
    obtain ⟨hI, -, hret⟩ := bodyInv_func0 (progOf cfg.layout rt [func0 (Names.user "main") r])
      rt.length (Names.user "main") hr
    exact ⟨ctxOf_frameOk .., ctxOf_func0_out _ _ _ ha, ctxOf_frame_mod16 .., ctxOf_func0_frame _ _ _ ha,
      funcRegs_length_func0 _ hr, mem_funcRegs_func0 _ hr, (dests_nodup _ _ 0 r hr).2.1, ha,
      by omega, hI, hret, ctxOf_func0_frame_le _ _ _ hr (accepted0_next hd hr)⟩

end Scc.Lower.InvA64
