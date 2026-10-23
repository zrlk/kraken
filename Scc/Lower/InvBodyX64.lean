import Scc.Lower.InvBody
import Scc.Lower.InvX64

/-!
# The x86-64 frame of an `Accepted0` body

The x86-64 twin of `Scc/Lower/InvBodyA64.lean`: what the per-construct code
lemmas of `Scc/Lower/InvX64.lean` and the per-step lemmas of
`Scc/Lower/InvBody.lean` assume of the frame `frameOf areas (func0 name r)`
an `Accepted0` body is emitted with, proved from the closed form
`lower0 … = some r`:

* `mem_slots_func0`: the registers with a slot are exactly the registers the
  body's instructions write; `slots_length_func0`: at most `r.next` of them;
  `slotOff_ok`: each register with a slot is found, at `-8 * (k + 1)` for
  its number `k`;
* `outWords_func0`: no outgoing argument area (the body makes no call), so
  the frame is `align16 (8 * n)` bytes below the frame record for its `n`
  slots (`frameOf_size_func0`), a multiple of 16;
* `bodyInv_func0_x64`: `BodyInv` at the start of the body with the
  registers with a slot as `S`, and the registers the body writes and
  returns among them;
* `main_inv_x64`: on an `Accepted0` program that lowers and emits, the
  lowered IR, the closed form of `main`'s body and all of the above for the
  frame `main` is emitted with.

No frame bound is needed here: a slot access is one `movq` whatever the
displacement (`Scc/Lower/InvX64.lean`).
-/

open CoreLang CoreTerm
open Scc.IR Scc.Lower Scc.Lower.Inv

namespace Scc.Lower.InvX64

open Scc.Emit.X64

/-- The registers with a slot in a frame. -/
def slotRegs (fr : Frame) : List IR.Reg := fr.slots.map (·.1)

/-- **A register with a slot is found**, at `-8 * (k + 1)` for its number. -/
theorem slotOff_ok {fr : Frame} {x : IR.Reg} (h : x ∈ slotRegs fr) (s : S) :
    ∃ k, (x, k) ∈ fr.slots ∧ fr.slotOff x s = .ok (-(8 * ((k : Int) + 1)), s) := by
  have hs : (fr.slots.find? (·.1 == x)).isSome := by
    rw [List.find?_isSome]
    obtain ⟨⟨y, k⟩, hm, rfl⟩ := List.mem_map.mp h
    exact ⟨_, hm, by simp⟩
  cases hf : fr.slots.find? (·.1 == x) with
  | none => rw [hf] at hs; cases hs
  | some v =>
    obtain ⟨y, k⟩ := v
    have he : (y == x) = true := by simpa using List.find?_some hf
    simp only [beq_iff_eq] at he
    subst he
    exact ⟨k, List.mem_of_find?_eq_some hf, slotOff_find hf s⟩

/-! ## The slots of `func0` -/

theorem flatMap_eq_of {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ i ∈ l, f i = g i) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | i :: l, h => by
    simp only [List.flatMap_cons, h i (by simp), flatMap_eq_of l fun j hj => h j (by simp [hj])]

/-- The registers with a slot in the frame of `func0 name r` whose
instructions are all `addChk`: each instruction's written and read
registers, then the returned ones, without repeats. -/
theorem slotRegs_func0_eq (areas : List (Sym × Nat)) (name : Sym) {r : Res}
    (hr : ∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) :
    slotRegs (frameOf areas (func0 name r)) =
      (r.insts.flatMap (fun i => StackMap.instDefs i ++ StackMap.instUses i) ++
        r.ret.flatMap StackMap.opRegs).eraseDups := by
  unfold slotRegs
  rw [frameOf_slots, List.zipIdx_map_fst]
  congr 1
  simp only [func0, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, termRegs]
  congr 1
  all_goals first
    | exact flatMap_eq_of _ fun i hi => by obtain ⟨d, p, q, rfl⟩ := hr i hi; cases p <;> cases q <;> rfl
    | exact flatMap_eq_of _ fun o _ => by cases o <;> rfl

/-- **The registers with a slot are the registers the body writes.** -/
theorem mem_slots_func0 (areas : List (Sym × Nat)) (name : Sym) {arg : String} {e : Expr}
    {r : Res} (hr : lower0 [(arg, .unit, [])] 0 e = some r) (x : IR.Reg) :
    x ∈ slotRegs (frameOf areas (func0 name r)) ↔ x ∈ defsOf r.insts := by
  rw [slotRegs_func0_eq areas name (lower0_insts_addChk _ _ _ _ hr).1, List.mem_eraseDups]
  obtain ⟨hu, hret⟩ := lower0_uses_defs hr
  constructor
  · intro h
    simp only [List.mem_append, List.mem_flatMap] at h
    rcases h with ⟨i, hi, hx | hx⟩ | hx
    · exact List.mem_flatMap.mpr ⟨i, hi, hx⟩
    · exact hu i hi x hx
    · exact hret x (List.mem_flatMap.mpr hx)
  · intro h
    obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp h
    exact List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨i, hi, List.mem_append.mpr (.inl hx)⟩))

theorem nodup_eraseDups' {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨by simp, nodup_eraseDups' n _ ?_⟩
    have := List.length_filter_le (fun b => !b == a) as
    simp at h
    omega

/-- **At most one slot per `+`.** -/
theorem slots_length_func0 (areas : List (Sym × Nat)) (name : Sym) {arg : String} {e : Expr}
    {r : Res} (hr : lower0 [(arg, .unit, [])] 0 e = some r) :
    (frameOf areas (func0 name r)).slots.length ≤ r.next := by
  obtain ⟨ha, hn⟩ := lower0_insts_addChk _ _ _ _ hr
  have hnd : (slotRegs (frameOf areas (func0 name r))).Nodup := by
    rw [slotRegs_func0_eq areas name ha]; exact nodup_eraseDups' _ _ (Nat.le_refl _)
  have hle := hnd.length_le_of_subset (l₂ := defsOf r.insts)
    fun x hx => (mem_slots_func0 areas name hr x).mp hx
  rw [defsOf_length_addChk _ ha] at hle
  simp only [slotRegs, List.length_map] at hle
  omega

/-! ## The frame -/

/-- **No outgoing argument area**: the body makes no call. -/
theorem outWords_func0 (areas : List (Sym × Nat)) (name : Sym) {r : Res}
    (hr : ∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) : outWords areas (func0 name r) = 0 := by
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

/-- The frame of an `Accepted0` body: its slots, rounded up to 16 bytes. -/
theorem frameOf_size_func0 (areas : List (Sym × Nat)) (name : Sym) {r : Res}
    (hr : ∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) :
    (frameOf areas (func0 name r)).size =
      (8 * (frameOf areas (func0 name r)).slots.length + 15) / 16 * 16 ∧
      (frameOf areas (func0 name r)).size % 16 = 0 := by
  rw [frameOf_size, outWords_func0 areas name hr]
  omega

/-! ## The invariant at the start of the body -/

/-- **`BodyInv` at the start of an `Accepted0` body**, with the registers
with a slot as `S`; the registers the body writes and returns have slots. -/
theorem bodyInv_func0_x64 (areas : List (Sym × Nat)) (name : Sym) {arg : String} {e : Expr}
    {r : Res} (hr : lower0 [(arg, .unit, [])] 0 e = some r) :
    BodyInv (slotRegs (frameOf areas (func0 name r))) 0 [(arg, .unit, [])] ∧
      (∀ d ∈ defsOf r.insts, d ∈ slotRegs (frameOf areas (func0 name r))) ∧
      ∀ x ∈ r.ret.flatMap StackMap.opRegs, x ∈ slotRegs (frameOf areas (func0 name r)) := by
  have hm := mem_slots_func0 areas name hr
  exact ⟨bodyInv_init _ arg, fun d hd => (hm d).mpr hd,
    fun x hx => (hm x).mpr ((lower0_uses_defs hr).2 x hx)⟩

/-! ## The whole program -/

/-- **The invariants of `main`'s frame** (x86-64): on an `Accepted0`
program that lowers and emits, `main`'s body has the closed form `r`, the
lowered IR is the runtime functions `rt` then `func0 main r`, and the frame
`fr` `main` is emitted with has no outgoing area, a size of its slots
rounded up to 16 bytes, at most `r.next` slots, whose registers are exactly
the registers the body writes (pairwise distinct, and every register read
is one of them), and `BodyInv` holds at the start of the body. -/
theorem main_inv_x64 (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    {em : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.lowerAll? cfg [d] = .ok em) :
    ∃ r rt, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      (Scc.Lower.X64.lowerAll cfg [d]).low.ir = progOf cfg.layout rt [func0 (Names.user "main") r] ∧
      let p := progOf cfg.layout rt [func0 (Names.user "main") r]
      let areas := StackMap.argAreas p argRegs.length
      let fr : Frame := { frameOf areas (func0 (Names.user "main") r) with maps := p.growth.isSome }
      outWords areas (func0 (Names.user "main") r) = 0 ∧
      fr.size = (8 * fr.slots.length + 15) / 16 * 16 ∧ fr.size % 16 = 0 ∧
      fr.slots.length ≤ r.next ∧
      (∀ x, x ∈ slotRegs fr ↔ x ∈ defsOf r.insts) ∧ (defsOf r.insts).Nodup ∧
      (∀ i ∈ r.insts, ∃ d p q, i = .addChk d p q) ∧ r.next = r.insts.length ∧
      BodyInv (slotRegs fr) 0 [(d.arg, .unit, [])] ∧
      (∀ x ∈ r.ret.flatMap StackMap.opRegs, x ∈ slotRegs fr) := by
  obtain ⟨r, rt, hr, hrt, hir⟩ := lowerAll_accepted0_x64 cfg hd h
  obtain ⟨ha, hn⟩ := lower0_insts_addChk _ _ _ _ hr
  refine ⟨r, rt, hr, hrt, hir, ?_⟩
  intro p areas fr
  obtain ⟨hI, -, hret⟩ := bodyInv_func0_x64 areas (Names.user "main") hr
  obtain ⟨hs1, hs2⟩ := frameOf_size_func0 areas (Names.user "main") ha
  exact ⟨outWords_func0 _ _ ha, hs1, hs2, slots_length_func0 areas _ hr, mem_slots_func0 areas _ hr,
    (dests_nodup _ _ 0 r hr).2.1, ha, by omega, hI, hret⟩

end Scc.Lower.InvX64
