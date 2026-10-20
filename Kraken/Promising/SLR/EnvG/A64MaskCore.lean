/-
**Masked executables for AArch64: a thread's own code inside a whole
image**. The AArch64 copy of
`EnvG/X64MaskCore.lean`, which cannot be imported here (the two
ISAs' `Syntax` clash); the statements are the same, except
`ValidLayout.of_mask` (AArch64's `ValidLayout` has `data_size` and no
alignment field) and the local `directive_of_codeAt`.

A `.kl` program's threads all run one image: the AArch64 runner lays out
the whole `code` block (`Kraken.Litmus.AArch64.prepareProgram`, no data
trailer). A thread runs only its own role's cells, from its entry label to
its exit label. Two things in the existing links read the *whole* image and
fail there:

- the halt (`hstuck`): no instruction may step at the exit address `endPc`,
  but an exit label followed by code (`pdone: NOP` in `spsc_queue.kl`) has
  an instruction there (the machine itself halts at `endPc`: `exec` checks
  it first);
- the phase-1 shape (`Phase1Tree`, `Phase1TreeF`, …) of *every* cell, while
  the image holds the other roles' code.

Both are fixed by one device. The **mask** `e'` of the image `e` has the
same start and sizes, and each cell either equal to `e`'s or, for a
non-label cell, replaced by a data cell `.byteArray` (`MaskOf e e'`). A
`Safely` judgment is proved over the mask (`vcgen` runs in the mask as its
ambient code). Then:

- every step of the mask is a step of the image, at a cell the two share
  (`instrStepEnv_of_mask`), so the judgment transfers;
- at a masked cell the mask has no step (a data cell is `unimplemented`):
  masking the exit cell gives the halt, masking the other roles' code
  restricts the shape obligation to the thread's own cells (a thread state
  with a mask step has the tree of the masked state: `exec_of_mask`).

The labels, addresses and validity of the layout are the image's
(`labels_mask`, `addrOf_mask`, `ValidLayout.of_mask`). `Program.maskKeep`
builds the mask of a laid-out program from a predicate on cell indices
(`maskOf_layout`).

Contents: `CellMask`, `MaskOf`, `Program.maskKeep`, `maskOf_layout`,
`codeAt_mask`, `labels_mask`, `addrOf_mask`, `ValidLayout.of_mask`,
`instrStepEnv_of_mask`, `Safely.of_mask`, `exec_of_mask`.

The ISA-neutral statements (`Forall2`, the `forall₂_*` list
helpers, `evTree_map_map`) live in `EnvG/MaskCommon.lean`; the names here
are aliases of them.
-/
import Kraken.Promising.SLR.EnvG.A64NoFault
import Kraken.Promising.SLR.EnvG.MaskCommon

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The mask relation -/

-- `Forall2`, `Forall2.imp`, `Forall2.map` (`EnvG/MaskCommon.lean`): two lists
-- related cell by cell (core Lean has no `List.Forall₂`).
hoist_alias [Kraken.Promising.SLR.EnvG.MaskCommon.Forall2 ↦ Kraken.Promising.AArch64.EnvG.Forall2,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.nil ↦ Kraken.Promising.AArch64.EnvG.Forall2.nil,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.cons ↦ Kraken.Promising.AArch64.EnvG.Forall2.cons,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.imp ↦ Kraken.Promising.AArch64.EnvG.Forall2.imp,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.map ↦ Kraken.Promising.AArch64.EnvG.Forall2.map]

-- The auto-generated recursors of the copy, kept under their names.
hoist_alias [Kraken.Promising.SLR.EnvG.MaskCommon.Forall2 ↦ Kraken.Promising.AArch64.EnvG.Forall2,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.nil ↦ Kraken.Promising.AArch64.EnvG.Forall2.nil,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.cons ↦ Kraken.Promising.AArch64.EnvG.Forall2.cons,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.rec ↦ Kraken.Promising.AArch64.EnvG.Forall2.rec,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.casesOn ↦ Kraken.Promising.AArch64.EnvG.Forall2.casesOn,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.recOn ↦ Kraken.Promising.AArch64.EnvG.Forall2.recOn,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.below ↦ Kraken.Promising.AArch64.EnvG.Forall2.below,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.below.nil ↦ Kraken.Promising.AArch64.EnvG.Forall2.below.nil,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.below.cons ↦ Kraken.Promising.AArch64.EnvG.Forall2.below.cons,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.below.rec ↦ Kraken.Promising.AArch64.EnvG.Forall2.below.rec,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.below.casesOn ↦ Kraken.Promising.AArch64.EnvG.Forall2.below.casesOn,
  Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.brecOn ↦ Kraken.Promising.AArch64.EnvG.Forall2.brecOn]

/-- A cell of the mask: the image's cell, or, for a non-label cell, a data
cell of the same size. -/
def CellMask (c c' : Directive × Nat) : Prop :=
  c' = c ∨ (c.1.isLabel = false ∧ (∃ b, c'.1 = .byteArray b) ∧ c'.2 = c.2)

theorem CellMask.size {c c' : Directive × Nat} (h : CellMask c c') : c'.2 = c.2 := by
  rcases h with rfl | ⟨-, -, h⟩
  · rfl
  · exact h

theorem CellMask.isLabel {c c' : Directive × Nat} (h : CellMask c c') : c'.1.isLabel = c.1.isLabel := by
  rcases h with rfl | ⟨h, ⟨b, hb⟩, -⟩
  · rfl
  · rw [hb, h]; rfl

/-- **`e'` masks `e`**: the same start, and cell by cell the image's cell or
a data cell in place of a non-label one. -/
structure MaskOf (e e' : Kraken.Executable Directive) : Prop where
  start : e'.1 = e.1
  cells : Forall2 CellMask e.2 e'.2

/-- Every executable masks itself (no cell masked). -/
theorem MaskOf.refl (e : Kraken.Executable Directive) : MaskOf e e :=
  ⟨rfl, go e.2⟩
where
  go : ∀ l : List (Directive × Nat), Forall2 CellMask l l
    | [] => .nil
    | _ :: l => .cons (.inl rfl) (go l)

/-! ## List helpers -/

-- `forall₂_dropWhile`, `forall₂_findSome?`, `forall₂_of_getElem`, `forall₂_getElem?`
-- (`EnvG/MaskCommon.lean`).
hoist_alias [Kraken.Promising.SLR.EnvG.MaskCommon.Forall2 ↦ Kraken.Promising.AArch64.EnvG.Forall2,
  Kraken.Promising.SLR.EnvG.MaskCommon.forall₂_dropWhile ↦ Kraken.Promising.AArch64.EnvG.forall₂_dropWhile,
  Kraken.Promising.SLR.EnvG.MaskCommon.forall₂_findSome? ↦ Kraken.Promising.AArch64.EnvG.forall₂_findSome?,
  Kraken.Promising.SLR.EnvG.MaskCommon.forall₂_of_getElem ↦ Kraken.Promising.AArch64.EnvG.forall₂_of_getElem,
  Kraken.Promising.SLR.EnvG.MaskCommon.forall₂_getElem? ↦ Kraken.Promising.AArch64.EnvG.forall₂_getElem?]

/-! ## Addresses, cells and labels of the mask -/

theorem sizes_mask : ∀ {ds ds' : List (Directive × Nat)}, Forall2 CellMask ds ds' →
    ds'.map (·.2) = ds.map (·.2)
  | _, _, Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.nil => rfl
  | _, _, Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.cons h hl => by simp only [List.map_cons, h.size, sizes_mask hl]

theorem withAddresses_mask : ∀ {ds ds' : List (Directive × Nat)} (a : Int64), Forall2 CellMask ds ds' →
    Forall2 (fun x y => x.1 = y.1 ∧ CellMask x.2 y.2)
      (Kraken.Executable.withAddresses (a, ds)) (Kraken.Executable.withAddresses (a, ds'))
  | _, _, a, Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.nil => by rw [withAddresses_nil]; exact .nil
  | c :: _, _ :: _, a, Kraken.Promising.SLR.EnvG.MaskCommon.Forall2.cons h hl => by
    rw [withAddresses_cons, withAddresses_cons, h.size]
    exact .cons ⟨rfl, h⟩ (withAddresses_mask _ hl)

/-- **The cells from an address in the mask mask the image's.** -/
theorem directivesFromAddress_mask {e e' : Kraken.Executable Directive} (hm : MaskOf e e') (pc : Int64) :
    Forall2 CellMask (e.directivesFromAddress pc) (e'.directivesFromAddress pc) := by
  obtain ⟨a, ds⟩ := e
  obtain ⟨a', ds'⟩ := e'
  obtain ⟨ha, hc⟩ := hm
  simp only at ha hc
  subst ha
  unfold Kraken.Executable.directivesFromAddress
  have h := forall₂_dropWhile (p := fun x => decide (x.1 ≠ pc)) (q := fun x => decide (x.1 ≠ pc))
    (fun x y hxy => by rw [hxy.1]) (withAddresses_mask a' hc)
  simp only
  exact h.map fun _ _ hxy => hxy.2

/-- **The mask's code at an address masks the image's.** -/
theorem codeAt_mask {e e' : Kraken.Executable Directive} (hm : MaskOf e e') (pc : Int64) :
    Forall2 CellMask (e.codeAt pc) (e'.codeAt pc) :=
  forall₂_dropWhile (fun _ _ h => h.isLabel.symm) (directivesFromAddress_mask hm pc)

/-- **The mask has the image's labels.** -/
theorem labels_mask {e e' : Kraken.Executable Directive} (hm : MaskOf e e') :
    _root_.Executable.labels e' = _root_.Executable.labels e := by
  obtain ⟨a, ds⟩ := e
  obtain ⟨a', ds'⟩ := e'
  obtain ⟨ha, hc⟩ := hm
  simp only at ha hc
  subst ha
  unfold _root_.Executable.labels
  congr 1
  funext l
  congr 1
  refine (forall₂_findSome? ?_ (withAddresses_mask a' hc)).symm
  rintro ⟨p, d, z⟩ ⟨p', d', z'⟩ ⟨hp, hcm⟩
  simp only at hp hcm ⊢
  subst hp
  rcases hcm with h | ⟨hl, ⟨b, hb⟩, -⟩
  · simp only [Prod.mk.injEq] at h
    rw [h.1]
  · simp only at hb hl
    subst hb
    have : d ≠ .label l := by rintro rfl; simp [Directive.isLabel] at hl
    simp [this]

/-- The mask has the image's addresses. -/
theorem addrOf_mask {e e' : Kraken.Executable Directive} (hm : MaskOf e e') (i : Nat) :
    e'.addrOf i = e.addrOf i := by
  unfold Kraken.Executable.addrOf Kraken.Executable.sizeBefore
  rw [hm.start, List.map_take, List.map_take, sizes_mask hm.cells]

/-- **The mask of a valid layout is valid.** -/
theorem ValidLayout.of_mask {e e' : Kraken.Executable Directive} [hv : Kraken.Executable.ValidLayout e]
    (hm : MaskOf e e') : Kraken.Executable.ValidLayout e' where
  label_size i l z h := by
    obtain ⟨c, hc, hcm⟩ := forall₂_getElem? hm.cells i h
    rcases hcm with h' | ⟨-, ⟨b, hb⟩, -⟩
    · rw [← h'] at hc; exact hv.label_size i l z hc
    · cases hb
  instr_size i ins z h := by
    obtain ⟨c, hc, hcm⟩ := forall₂_getElem? hm.cells i h
    rcases hcm with h' | ⟨-, ⟨b, hb⟩, -⟩
    · rw [← h'] at hc; exact hv.instr_size i ins z hc
    · cases hb
  data_size i a z h := by
    obtain ⟨c, hc, hcm⟩ := forall₂_getElem? hm.cells i h
    rcases hcm with h' | ⟨hl, -, hz⟩
    · rw [← h'] at hc; exact hv.data_size i a z hc
    · simp only at hz
      subst hz
      exact Kraken.Executable.ValidLayout.size_pos i c.1 c.2 hc (by rintro l h; rw [h] at hl; cases hl)
  no_wrap := by rw [sizes_mask hm.cells]; exact hv.no_wrap

/-! ## Steps of the mask -/

/-- A data cell does not step. -/
theorem not_stepAtEnv_byteArray {e : Kraken.Executable Directive} {env : SharedEnv} {b : ByteArray} {z : Nat}
    {x : MachineState × env.State} {R : MachineState × env.State → Prop} :
    ¬ e.stepAtEnv env (.byteArray b) z x R := by
  intro h
  rcases h with h | h <;> simp [Directive.interp, Effects.AllEnv] at h

/-- **A step of the mask is a step of the image, at a cell they share.** -/
theorem instrStepEnv_of_mask {e e' : Kraken.Executable Directive} (hm : MaskOf e e') {env : SharedEnv}
    {x : MachineState × env.State} {R : MachineState × env.State → Prop} (h : e'.instrStepEnv env x R) :
    e.instrStepEnv env x R ∧
      ∃ d z r r', e.codeAt x.1.2 = (d, z) :: r ∧ e'.codeAt x.1.2 = (d, z) :: r' := by
  obtain ⟨d, z, r', hc', hs⟩ := h
  have hf := codeAt_mask hm x.1.2
  rw [hc'] at hf
  obtain ⟨c, r, hcm, -, hc⟩ : ∃ c r, CellMask c (d, z) ∧ Forall2 CellMask r r' ∧
      e.codeAt x.1.2 = c :: r := by
    cases hce : e.codeAt x.1.2 with
    | nil => rw [hce] at hf; cases hf
    | cons c r => rw [hce] at hf; cases hf with | cons h1 h2 => exact ⟨c, r, h1, h2, rfl⟩
  rcases hcm with h' | ⟨-, ⟨b, hb⟩, -⟩
  · rw [← h'] at hc
    unfold Kraken.Executable.stepAtEnv at hs
    rw [labels_mask hm] at hs
    exact ⟨⟨d, z, r, hc, hs⟩, d, z, r, r', hc, hc'⟩
  · simp only at hb
    subst hb
    exact absurd hs not_stepAtEnv_byteArray

/-- **A `Safely` judgment over the mask is one over the image.** -/
theorem Safely.of_mask {e e' : Kraken.Executable Directive} (hm : MaskOf e e') {env : SharedEnv}
    {post : MachineState × env.State → Prop} {x : MachineState × env.State}
    (h : Safely (e'.instrStepEnv env) post x) : Safely (e.instrStepEnv env) post x := by
  have hs := h.sim (fun x y => x = y) (fun x y R hxy hT => by
    subst hxy
    have hR : (fun y' => ∃ x', x' = y' ∧ R x') = R := funext fun y' => propext ⟨fun ⟨_, h1, h2⟩ => h1 ▸ h2,
      fun h => ⟨y', rfl, h⟩⟩
    rw [hR]
    exact (instrStepEnv_of_mask hm hT).1) rfl
  exact hs.mono fun _ ⟨_, h1, h2⟩ => h1 ▸ h2

/-- At an address whose first cell in the mask is a data cell, the mask has
no step. -/
theorem not_instrStepEnv_mask_of_codeAt {e' : Kraken.Executable Directive} {env : SharedEnv} {pc : Int64}
    {b : ByteArray} {z : Nat} {r : List (Directive × Nat)} (hc : e'.codeAt pc = (.byteArray b, z) :: r) :
    ∀ x R, x.1.2 = pc → ¬ e'.instrStepEnv env x R := by
  rintro x R rfl ⟨d, z', r', hc', hs⟩
  rw [hc] at hc'
  simp only [List.cons.injEq, Prod.mk.injEq] at hc'
  obtain ⟨⟨rfl, rfl⟩, -⟩ := hc'
  exact not_stepAtEnv_byteArray hs

/-! ## The thread's tree at a cell the mask shares -/

-- `evTree_map_map` (`EnvG/MaskCommon.lean`): `EvTree.map` composes.
hoist_alias [Kraken.Promising.SLR.EnvG.MaskCommon.evTree_map_map ↦ Kraken.Promising.AArch64.EnvG.evTree_map_map]

/-- A thread state's directive is its code's first cell (`X64Link`'s
`directive_of_codeAt`, for AArch64). -/
theorem directive_of_codeAt {st : State} {d : Directive} {z : Nat} {rest : List (Directive × Nat)}
    (hcode : Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest) : st.directive = some d := by
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  unfold State.directive
  simp only at hcode ⊢
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- **A thread at a cell the mask shares with the image has the masked
thread's tree**, up to the executable in its states: the tree is the cell's
interpretation under the labels, and those agree. -/
theorem exec_of_mask {e e' : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e]
    (hm : MaskOf e e') {st : State} (he : st.exe = e) {d : Directive} {z : Nat}
    {r r' : List (Directive × Nat)} (hc : e.codeAt st.st.2 = (d, z) :: r)
    (hc' : e'.codeAt st.st.2 = (d, z) :: r') {tree : EvTree State} (hex : isa.exec st = some tree) :
    ∃ tree', isa.exec { st with exe := e' } = some tree' ∧ tree = tree'.map fun s => { s with exe := e } := by
  haveI : Kraken.Executable.ValidLayout e' := ValidLayout.of_mask hm
  have hdir : st.directive = some d := directive_of_codeAt (by rw [he]; exact hc)
  have hdir' : ({ st with exe := e' } : State).directive = some d := directive_of_codeAt hc'
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hc
  obtain ⟨ls', hat', hls'⟩ := directivesAtAddress_of_codeAt hc'
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hc hc' hat hat' hdir hdir' hex ⊢
  subst he
  have hex' : exec _ = some tree := hex
  show ∃ tree', exec _ = some tree' ∧ _
  unfold exec at hex' ⊢
  rw [hdir] at hex'
  rw [hdir']
  simp only [Option.isNone_some, Bool.or_false] at hex' ⊢
  split at hex'
  · cases hex'
  · next hne =>
    simp only [hne]
    cases hex'
    refine ⟨_, rfl, ?_⟩
    have hstep : Executable.step exe (s, pc) (fun s' => .done s') =
        Executable.step e' (s, pc) (fun s' => .done s') := by
      unfold Executable.step
      rw [labels_mask hm, hat, hat']
      letI := Executable.labels exe
      simp only
      rw [Directives.interp_label_prefix ls _ _ _ _ hls, Directives.interp_label_prefix ls' _ _ _ _ hls']
    rw [hstep]
    exact (evTree_map_map (fun st : MachineState =>
      ({ exe := e', endPc := endPc, st := st, showPc := showPc, decls := decls } : State))
      (fun s : State => { s with exe := exe }) _).symm

/-! ## The mask of a laid-out program -/

/-- **The mask of a program keeping the cells at the indices `keep`** (and
every label): every other cell becomes an empty data cell. -/
def _root_.Program.maskKeep (keep : Nat → Bool) (p : Program) : Program :=
  p.mapIdx fun i d => if keep i || d.isLabel then d else .byteArray (.mk #[])

/-- **`Program.maskKeep` lays out to a mask.** -/
theorem maskOf_layout [layout : _root_.Layout] (keep : Nat → Bool) (p : Program) :
    MaskOf (layout p) (layout (p.maskKeep keep)) := by
  refine ⟨rfl, forall₂_of_getElem (by simp [Layout.apply, Program.maskKeep]) fun i h h' => ?_⟩
  have hi : i < p.length := by simpa [Layout.apply] using h
  simp only [Layout.apply, Program.maskKeep, List.getElem_mapIdx]
  by_cases hk : keep i || p[i].isLabel
  · left; simp [hk]
  · right
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hk
    simp [hk.1, hk.2]

/-- Keep the cells at the indices `lo ≤ i < hi`. -/
def keepRange (lo hi : Nat) : Nat → Bool := fun i => decide (lo ≤ i) && decide (i < hi)

/-- **A per-directive property of a mask keeping `lo ≤ i < hi`**: of the
kept range, of every label, and of the empty data cell. -/
theorem mem_maskKeep_range {Φd : Directive → Prop} {p : Program} {lo hi : Nat}
    (hk : ∀ d ∈ (p.drop lo).take (hi - lo), Φd d) (hl : ∀ l, Φd (.label l))
    (hb : Φd (.byteArray (.mk #[]))) : ∀ d ∈ p.maskKeep (keepRange lo hi), Φd d := by
  intro d hd
  obtain ⟨i, hi', rfl⟩ := List.mem_mapIdx.mp hd
  by_cases hkeep : keepRange lo hi i = true
  · simp only [hkeep, Bool.true_or, ↓reduceIte]
    simp only [keepRange, Bool.and_eq_true, decide_eq_true_eq] at hkeep
    refine hk _ ?_
    have h1 : i - lo < ((p.drop lo).take (hi - lo)).length := by
      simp only [List.length_take, List.length_drop]; omega
    have h2 : ((p.drop lo).take (hi - lo))[i - lo] = p[i] := by
      simp only [List.getElem_take, List.getElem_drop]
      congr 1; omega
    rw [← h2]
    exact List.getElem_mem h1
  · simp only [Bool.not_eq_true] at hkeep
    simp only [hkeep, Bool.false_or]
    split
    · next h =>
      cases hpi : p[i] with
      | label l => exact hl l
      | _ => rw [hpi] at h; cases h
    · exact hb

end Kraken.Promising.AArch64.EnvG
