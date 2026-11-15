/-
**The shape of scc's x86-64 code cells for the branch-target check**
(x86-64): where the cells are not empty, their directives are the header's,
then each function's (`emitFuncs`'s items, `dOf`), then a tail that starts
with a label; neither the header nor the tail holds a user label (`WcL`),
the tail's data labels being none where the program's data names are none.

- `labNW`, `PreP.forIn_mem`: items with no user label, a loop whose body
  appends such items at each element of the list;
- `emitHead_nw`, `emitTail_nw`: the header and the tail hold no user label;
- `emitTail_head`: the tail's items start with `.text` items whose only
  directive is a label (`scc_rt_morestack`'s or `scc_text_end`);
- `tdStep_labels`, `textDirectives_append_labs`: `textDirectives` of
  `.text` items then any, the rest's labels among the last items';
- `emitItemsMaps_parts`, `lowerAll_parts`: the header, the functions, the
  tail.
-/
import Spike.Lib.LowerX64.G1TgSeg
import Spike.Lib.LowerX64.EmitLabels

namespace Spike.Lib.LowerX64

open Kraken
open Scc.Emit.X64

/-! ## Items with no user label -/

/-- **An item with no user label**: no label, or a label off `WcL`. -/
def labNW : Item → Bool
  | .d (.label l) => !decide (WcL l)
  | _ => true

/-- A label off `WcL` has `labNW`. -/
theorem labNW_label {l : String} (h : ¬ WcL l) : labNW (.d (.label l)) = true := by
  simp [labNW, h]

/-- The labels of `labNW` items are off `WcL`. -/
theorem not_wcL_of_labNW {items : List Item} (h : ∀ it ∈ items, labNW it = true) :
    ∀ L, Directive.label L ∈ dOf items → ¬ WcL L := by
  intro L hL
  obtain ⟨it, hit, e⟩ := List.mem_filterMap.mp hL
  cases it with
  | d x =>
    simp only [Option.some.injEq] at e
    subst e
    simpa [labNW] using h _ hit
  | _ => cases e

/-- **A loop whose body appends `P` items at each element of the list.** -/
theorem PreP.forIn_mem {P : Item → Bool} {β σ : Type} (f : β → σ → E (ForInStep σ)) :
    ∀ (l : List β), (∀ b ∈ l, ∀ st, PreP P (f b st)) → ∀ (init : σ), PreP P (forIn l init f)
  | [], _, init => by simpa using PreP.pure' init
  | b :: l, hf, init => by
    rw [List.forIn_cons]
    refine PreP.bind' (hf b (List.mem_cons_self ..) init) fun r => ?_
    cases r with
    | done st => exact PreP.pure' st
    | yield st => exact PreP.forIn_mem f l (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb')) st

theorem freshL_nw (fn : String) : PreP labNW (freshL fn) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem recordMap_nw (l : String) (st hp : List Int) : PreP labNW (recordMap l st hp) :=
  PreP.of_out fun s a s' h => by cases h; rfl
theorem slotOff_nw (fr : Frame) (r : Scc.IR.Reg) : PreP labNW (fr.slotOff r) := by
  unfold Frame.slotOff
  split
  · exact PreP.pure' _
  · exact PreP.throw' _
theorem slot_nw (fr : Frame) (r : Scc.IR.Reg) : PreP labNW (fr.slot r) := by
  unfold Frame.slot
  exact PreP.bind' (slotOff_nw fr r) fun _ => PreP.pure' _

/-- One step of a `PreP labNW` proof of the header or the tail. -/
macro "nw_step" : tactic => `(tactic| first
  | (with_reducible exact PreP.pure' _) | (with_reducible exact PreP.throw' _)
  | (with_reducible exact PreP.item' rfl) | (with_reducible exact PreP.item' (by decide))
  | (with_reducible exact PreP.get')
  | (with_reducible exact freshL_nw _) | (with_reducible exact recordMap_nw _ _ _)
  | (with_reducible exact slotOff_nw _ _) | (with_reducible exact slot_nw _ _)
  | (unfold ins) | (unfold lbl) | (unfold dir) | (unfold sysc) | (unfold ud2) | (unfold movFs)
  | (unfold movRR) | (unfold movl) | (unfold zero32) | (unfold callSym) | (unfold jmpTo)
  | (with_reducible apply PreP.bind') | (with_reducible apply PreP.forIn') | (with_reducible apply PreP.mapM')
  | (intro _) | (split))

/-- The trampolines' symbols are off `WcL`. -/
theorem kabiSlots_nw : ∀ b ∈ Scc.IR.Tcb.kabiSlots, ¬ WcL b.1 := by decide

/-- **The header holds no user label.** -/
theorem emitHead_nw (p : Scc.IR.Program) : PreP labNW (emitHead p) := by
  simp only [emitHead, emitKabi]
  repeat (first
    | (refine PreP.forIn_mem _ _ (fun b hb _ => ?_) _
       repeat (first | (with_reducible exact PreP.item' (labNW_label (kabiSlots_nw b hb))) | nw_step))
    | nw_step)

/-- A data item's code holds no user label where its name is none. -/
theorem emitData_nw {d : Scc.IR.Data} (hd : ¬ WcL d.name) : PreP labNW (emitData d) := by
  unfold emitData
  split
  all_goals repeat (first | (with_reducible exact PreP.item' (labNW_label hd)) | nw_step)

/-- **The tail holds no user label** where the program's data names are
none. -/
theorem emitTail_nw {p : Scc.IR.Program} (hd : ∀ d ∈ p.data, ¬ WcL d.name) : PreP labNW (emitTail p) := by
  unfold emitTail
  dsimp only
  repeat (first
    | (refine PreP.forIn_mem _ _ (fun d hdm _ => PreP.bind' (emitData_nw (hd d hdm)) fun _ => PreP.pure' _) _)
    | (unfold emitMaps) | (unfold emitMorestack) | nw_step)

/-! ## The tail's first items -/

/-- **The tail's items start with `.text` items whose only directive is a
label off `WcL`.** -/
theorem emitTail_head {p : Scc.IR.Program} {s s' : S} (h : emitTail p s = .ok ((), s')) :
    ∃ T0 L c, (∀ it ∈ T0, textN it = true) ∧ dOf T0 = [.label L] ∧ ¬ WcL L ∧
      s'.out = c ++ T0.reverse ++ s.out := by
  unfold emitTail at h
  cases hg : p.growth with
  | some g =>
    simp only [hg] at h
    obtain ⟨u, s1, h1, h2⟩ := bind_inv_E h
    obtain ⟨c2, hc2⟩ := ((by (try dsimp only); repeat (first | (unfold emitData) | (unfold emitMaps) | pre_step)) :
      Pre _).out _ _ _ h2
    simp only [emitMorestack] at h1
    obtain ⟨_, t1, e1, h1⟩ := bind_inv_E h1
    obtain ⟨_, t2, e2, h1⟩ := bind_inv_E h1
    obtain ⟨_, t3, e3, h1⟩ := bind_inv_E h1
    cases e1; cases e2; cases e3
    obtain ⟨c1, hc1⟩ := ((by repeat pre_step) : Pre _).out _ _ _ h1
    refine ⟨[.blank, .dir s!".type {Scc.IR.StackMap.morestackSym}, @function",
      .d (.label Scc.IR.StackMap.morestackSym)], _, c2 ++ c1, by decide, rfl, by decide, ?_⟩
    rw [hc2, hc1]
    simp
  | none =>
    simp only [hg] at h
    obtain ⟨_, t1, e1, h2⟩ := bind_inv_E h
    cases e1
    obtain ⟨c3, hc3⟩ := ((by (try dsimp only); repeat (first | (unfold emitData) | (unfold emitMaps) | pre_step)) :
      Pre _).out _ _ _ h2
    refine ⟨[.d (.label Scc.IR.StackMap.textEndSym)], _, c3, by decide, rfl, by decide, ?_⟩
    rw [hc3]
    simp

/-! ## `textDirectives` with the rest's labels -/

/-- **A step's new directives**: a label among them is the item's. -/
theorem tdStep_labels {b b' : Bool} {ds ds' : List Directive} {it : Item}
    (h : tdStep (some (b, ds)) it = some (b', ds')) :
    ∃ w, ds' = w ++ ds ∧ ∀ L, Directive.label L ∈ w → it = .d (.label L) := by
  unfold tdStep at h
  simp only [Option.bind_some] at h
  split at h <;> (repeat' split at h) <;>
    first
    | (cases h; exact ⟨[], rfl, by simp⟩)
    | (cases h; refine ⟨[_], rfl, fun L hL => ?_⟩
       simp only [List.mem_singleton] at hL
       first | (subst hL; rfl) | cases hL)
    | cases h

/-- **The fold's new directives**: a label among them is an item's. -/
theorem foldl_labels : ∀ (items : List Item) (b : Bool) (ds : List Directive) (res : Bool × List Directive),
    items.foldl tdStep (some (b, ds)) = some res →
    ∃ z, res.2 = z ++ ds ∧ ∀ L, Directive.label L ∈ z → Item.d (.label L) ∈ items
  | [], b, ds, res, h => by
    cases h
    exact ⟨[], rfl, by simp⟩
  | it :: items, b, ds, res, h => by
    rw [List.foldl_cons] at h
    cases e : tdStep (some (b, ds)) it with
    | none => rw [e, foldl_none] at h; cases h
    | some v =>
      obtain ⟨b', ds'⟩ := v
      rw [e] at h
      obtain ⟨w, rfl, hw⟩ := tdStep_labels e
      obtain ⟨z, hz, hzl⟩ := foldl_labels items b' (w ++ ds) res h
      refine ⟨z ++ w, by rw [hz, List.append_assoc], fun L hL => ?_⟩
      rcases List.mem_append.mp hL with hL | hL
      · exact List.mem_cons_of_mem _ (hzl L hL)
      · rw [hw L hL]; exact List.mem_cons_self ..

/-- **`textDirectives` of `.text` items then any**: their directives first,
then directives whose labels are among the last items'. -/
theorem textDirectives_append_labs {A B C : List Item} (hA : ∀ it ∈ A, textN it = true)
    (hB : ∀ it ∈ B, textN it = true) {prog : List Directive}
    (h : Scc.Lower.X64.textDirectives (A ++ B ++ C) = some prog) :
    ∃ Z, prog = dOf A ++ dOf B ++ Z ∧ ∀ L, Directive.label L ∈ Z → Item.d (.label L) ∈ C := by
  rw [textDirectives_eq, List.foldl_append, List.foldl_append, foldl_textN hA, foldl_textN hB] at h
  cases e : C.foldl tdStep (some (true, (dOf B).reverse ++ ((dOf A).reverse ++ []))) with
  | none => rw [e] at h; cases h
  | some res =>
    rw [e] at h
    cases h
    obtain ⟨z, hz, hzl⟩ := foldl_labels C _ _ res e
    refine ⟨z.reverse, by simp [hz], fun L hL => hzl L (List.mem_reverse.mp hL)⟩

/-! ## The parts of the output -/

/-- **`emitItemsMaps`'s items**: `.text` header items with no user label,
the functions' items, the tail's first `.text` items whose one directive is
a label off `WcL`, then items with no user label (the program's data names
off `WcL`). -/
theorem emitItemsMaps_parts {ir : Scc.IR.Program} {items : List Item} {sps : List Map}
    (h : emitItemsMaps ir = .ok (items, sps)) (hd : ∀ d ∈ ir.data, ¬ WcL d.name) :
    ∃ areas rs H T0 L T1, emitFuncs ir areas ir.funcs 0 = .ok rs ∧ (∀ it ∈ H, textN it = true) ∧
      (∀ it ∈ H, labNW it = true) ∧ (∀ it ∈ T0, textN it = true) ∧ dOf T0 = [.label L] ∧ ¬ WcL L ∧
      (∀ it ∈ T1, labNW it = true) ∧ items = H ++ rs.flatMap (·.1) ++ T0 ++ T1 := by
  obtain ⟨areas, -, h⟩ := except_bind_ok h
  obtain ⟨rs, hrs, h⟩ := except_bind_ok h
  obtain ⟨⟨⟨⟩, hs⟩, hh, h⟩ := except_bind_ok h
  obtain ⟨⟨⟨⟩, ts⟩, ht, h⟩ := except_bind_ok h
  cases h
  obtain ⟨c, hc, hp⟩ := (emitHead_prep ir).out _ _ _ hh
  obtain ⟨cn, hcn, hpn⟩ := (emitHead_nw ir).out _ _ _ hh
  obtain ⟨T0, L, c1, hT0, hdT0, hL, hc1⟩ := emitTail_head ht
  obtain ⟨c2, hc2, hp2⟩ := (emitTail_nw hd).out _ _ _ ht
  simp only [List.append_nil] at hc hcn hc1 hc2
  refine ⟨areas, rs, hs.out.reverse, T0, L, c1.reverse, hrs, fun it hi => hp it ?_, fun it hi => hpn it ?_,
    hT0, hdT0, hL, fun it hi => hp2 it ?_, ?_⟩
  · rw [hc] at hi; exact List.mem_reverse.mp hi
  · rw [hcn] at hi; exact List.mem_reverse.mp hi
  · rw [← hc2, hc1]; exact List.mem_append_left _ (List.mem_reverse.mp hi)
  · rw [hc1]
    simp

/-- **The cells of scc's x86-64 output, as the check reads them** (where
there are any, the program's data names off `WcL`): the header's
directives, with no user label, the functions' (`emitFuncs`'s items, in
order), then a tail starting with a label, with no user label. -/
theorem lowerAll_parts {cfg : Scc.Config} {p : CoreTerm.Prog} {sizes : List Nat}
    (hne : Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes ≠ [])
    (hd : ∀ d ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.data, ¬ WcL d.name) :
    ∃ areas rs H Tl, emitFuncs (Scc.Lower.X64.lowerAll cfg p).low.ir areas
        (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs 0 = .ok rs ∧
      (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes).map (·.1) =
        H ++ (rs.map (fun (r : List Item × List Map) => dOf r.1) ++ [Tl]).flatten ∧
      (∀ L, Directive.label L ∈ H → ¬ WcL L) ∧ (∀ L, Directive.label L ∈ Tl → ¬ WcL L) ∧
      ∃ L, Tl.head? = some (.label L) := by
  cases hl : Scc.Lower.X64.lowerAll? cfg p with
  | error e =>
    have : Scc.Lower.X64.lowerAll cfg p = default := by unfold Scc.Lower.X64.lowerAll; rw [hl]
    rw [this] at hne
    exact absurd rfl hne
  | ok e =>
    have he : Scc.Lower.X64.lowerAll cfg p = e := by unfold Scc.Lower.X64.lowerAll; rw [hl]
    rw [he] at hne hd ⊢
    obtain ⟨l, -, hl⟩ := except_bind_ok hl
    obtain ⟨⟨items, sps⟩, hE, hl⟩ := except_bind_ok hl
    cases hl
    obtain ⟨areas, rs, H, T0, L, T1, hf, hH, hHn, hT0, hdT0, hL, hT1, hi⟩ := emitItemsMaps_parts hE hd
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
        rw [hi, show H ++ rs.flatMap (·.1) ++ T0 ++ T1 = H ++ (rs.flatMap (·.1) ++ T0) ++ T1 by
          simp only [List.append_assoc]] at hp
        have hB : ∀ it ∈ rs.flatMap (·.1) ++ T0, textN it = true := fun it hit => by
          rcases List.mem_append.mp hit with hit | hit
          · obtain ⟨r, hr, hit⟩ := List.mem_flatMap.mp hit
            obtain ⟨i, hi', rfl⟩ := List.mem_iff_getElem.mp hr
            obtain ⟨hlen, hall⟩ := emitFuncs_labels hf
            exact (hall i (hlen ▸ hi')).1 it hit
          · exact hT0 it hit
        obtain ⟨Z, hZ, hZl⟩ := textDirectives_append_labs hH hB hp
        refine ⟨dOf H, .label L :: Z, hf, ?_, not_wcL_of_labNW hHn, ?_, ⟨L, rfl⟩⟩
        · have e1 : dOf (rs.flatMap (·.1) ++ T0) =
              (rs.map fun (r : List Item × List Map) => dOf r.1).flatten ++ [.label L] := by
            rw [show dOf (rs.flatMap (·.1) ++ T0) = dOf (rs.flatMap (·.1)) ++ dOf T0 from
              List.filterMap_append, hdT0]
            congr 1
            simp only [dOf, List.filterMap_flatMap]
            rfl
          rw [hZ, e1]
          simp
        · intro L' hL'
          rcases List.mem_cons.mp hL' with e | hL'
          · cases e; exact hL
          · exact not_wcL_of_labNW hT1 L' (List.mem_filterMap.mpr ⟨_, hZl L' hL', rfl⟩)

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.lowerAll_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.lowerAll_parts
