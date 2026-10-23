import WeakCore.TermMain

/-! # TermMemTyped: memory value typing along runs

A corollary of the typedness final `reachable_typedF` (`TermMain`), with **no new premise**:
along every run `TermStep.Steps p k arch c0 c` of a program meeting `ObligationsF`, from an
`InitOK` start (or a `TermInit.InitShape` start, `_init` forms), memory values are typed.

Caveats:
* **Observer's cut.** The statement is per observing thread `i`: it speaks about the cells of that
  thread's typing environment `Cut Eg i S` (its `η.sto`).
* **Own promises excluded.** Messages that are thread `i`'s own outstanding promises
  (`t ∈ th.promises`) are not covered; another observing thread covers them at shared cells; promises to the
  thread's own unshared cells are not covered.
* **Pointee up to `Fd`.** In the pointer forms the target cell's type matches the pointee type up to
  `Fd` (μ-folding), not syntactically.
* **Inherited assumptions.** `ObligationsF` has the fields `certWinC : CertWinCN …` and
  `certWin : CertWinPN …`, which are named assumptions proved nowhere; every theorem here inherits
  them through its `ObligationsF` hypothesis.
-/

namespace TermMemTyped

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The memory typing of one observer `i` at configuration `c`: every message not among `th`'s own
outstanding promises, at a label with a cell `cl` in the observer's cut `E`, holds `undef` or a word
of a value of `cl.ty` at its offset. -/
def MemTypedAt (E : TEnv) (c : Cfg) (th : TTh) : Prop :=
  ∀ (t : Ts) (m : Msg) (cl : Cell), t ∉ th.promises → c.mem[t]? = some m → E.sto m.loc.label = some cl →
    m.val = .undef ∨ WordOK E cl.ty m.loc.offset (mw m)

/-- `FrameTie` gives every observer's memory typing (the first conjunct of `MemInv`, `MemOKP`). -/
theorem memTyped_of_frameTie {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {Eg : GEnv}
    {Tot : Nat → Res} (h : FrameTie p k arch c Eg Tot) :
    ∀ i th, c.ths[i]? = some th → ∃ S, MemTypedAt (Cut Eg i S) c th := by
  intro i th hth
  obtain ⟨S, ρ, η, cx, Rf, Rs, hCE, -, -, -, -, hM⟩ := h i th hth
  refine ⟨S, fun t m cl ht hm hs => ?_⟩
  rw [← hCE] at hs ⊢
  exact hM.1.1 t m cl ht hm hs

/-- **Memory value typing along runs** (from `reachable_typedF`; caveats in the module doc: the
observer's cut, its own promises excluded, `CertWinCN`/`CertWinPN` inherited via `ObligationsF`). -/
theorem reachable_memTyped {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    ∃ Eg : GEnv, ∀ i th, c.ths[i]? = some th → ∃ S, MemTypedAt (Cut Eg i S) c th := by
  obtain ⟨Eg, Tot, h⟩ := reachable_typedF O hk h0 hr
  exact ⟨Eg, memTyped_of_frameTie h⟩

/-- **Memory value typing along runs, at a standard initial configuration** (`TermInit.InitShape`;
from `reachable_typedF_init`; same caveats). -/
theorem reachable_memTyped_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hs : TermInit.InitShape p c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    ∃ Eg : GEnv, ∀ i th, c.ths[i]? = some th → ∃ S, MemTypedAt (Cut Eg i S) c th := by
  obtain ⟨Eg, Tot, h⟩ := reachable_typedF_init O hk hs hr
  exact ⟨Eg, memTyped_of_frameTie h⟩

/-! ## The pointer forms -/

/-- What a pointer word in memory is: `null` (only for `ptrOpt`), or a location at offset `0` of a
cell of the observer's cut whose type is the pointee's closure up to `Fd`, and is accessible. -/
def PtrTarget (E : TEnv) (u : Ty) (v : WeakMem.Val) : Prop :=
  ∃ (a : Address) (c' : Cell), v = .loc a 0 ∧ a.offset = 0 ∧ E.sto a.label = some c' ∧
    Fd c'.ty (cl (fun _ => 0) (CE E.unsee).wit 0 0 u) ∧ accs c'.ty ≠ none

/-- The segment of a cell of reference type is the whole cell. -/
theorem segOf_ref {T S : Ty} {b : Nat} (hT : ∀ N e, T ≠ .array N e) (h : SegOf T b S) : b = 0 ∧ S = T := by
  rcases h with ⟨hb, hS, -⟩ | ⟨N, us, j, hA, -⟩
  · exact ⟨hb, hS⟩
  · exact absurd hA (hT _ _)

/-- A one-word value: its only word is at index `0` and carries the value. -/
theorem single_word {ws : List Word} {x : WeakMem.Val} {o' : Nat} {w0 w : Word}
    (hx : ws.map (·.val) = [x]) (hw0 : ws[o']? = some w0) (hle : WLe1 w0 w) : o' = 0 ∧ w.val = x := by
  match ws, hx with
  | [y], hx =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hx
    cases o' with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0
      subst hw0; exact ⟨rfl, hle.1.symm.trans hx⟩
    | succ n => simp at hw0

/-- A word of a value of `ptrOpt μ u` (a one-word cell): `null` or a pointer target, at offset `0`. -/
theorem ptrOpt_of_wordOK {E : TEnv} {μ : Mode} {u : Ty} {o : Nat} {w : Word}
    (h : WordOK E (.ptrOpt μ u) o w) : o = 0 ∧ (w.val = .null ∨ PtrTarget E u w.val) := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hv, -⟩, -⟩, hw0, hle, ho⟩ := h
  obtain ⟨rfl, rfl⟩ := segOf_ref (fun _ _ h => by cases h) hseg
  simp only [VR] at hv
  rcases hv with hn | ⟨a, c', hm, ha, hs, hF, -, hacc⟩
  · obtain ⟨h1, h2⟩ := single_word hn hw0 hle
    exact ⟨by omega, .inl h2⟩
  · obtain ⟨h1, h2⟩ := single_word hm hw0 hle
    exact ⟨by omega, .inr ⟨a, c', h2, ha, hs, hF, hacc⟩⟩

/-- A word of a value of `ptr μ u` (a one-word cell): a pointer target, at offset `0`. -/
theorem ptr_of_wordOK {E : TEnv} {μ : Mode} {u : Ty} {o : Nat} {w : Word}
    (h : WordOK E (.ptr μ u) o w) : o = 0 ∧ PtrTarget E u w.val := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hv, -⟩, -⟩, hw0, hle, ho⟩ := h
  obtain ⟨rfl, rfl⟩ := segOf_ref (fun _ _ h => by cases h) hseg
  simp only [VR] at hv
  obtain ⟨a, c', hm, ha, hs, hF, -, hacc⟩ := hv
  obtain ⟨h1, h2⟩ := single_word hm hw0 hle
  exact ⟨by omega, a, c', h2, ha, hs, hF, hacc⟩

/-- The pointer typing of one observer: at a cell of type `ptrOpt μ u` (resp. `ptr μ u`) every message
not among `th`'s own promises is `undef`, `null` (`ptrOpt` only), or a pointer target. -/
def PtrTypedAt (E : TEnv) (c : Cfg) (th : TTh) : Prop :=
  ∀ (t : Ts) (m : Msg) (cl : Cell) (μ : Mode) (u : Ty),
    t ∉ th.promises → c.mem[t]? = some m → E.sto m.loc.label = some cl →
    (cl.ty = .ptrOpt μ u → m.val = .undef ∨ m.val = .null ∨ PtrTarget E u m.val) ∧
    (cl.ty = .ptr μ u → m.val = .undef ∨ PtrTarget E u m.val)

theorem ptrTypedAt_of {E : TEnv} {c : Cfg} {th : TTh} (h : MemTypedAt E c th) : PtrTypedAt E c th := by
  intro t m cl μ u ht hm hs
  refine ⟨fun hty => ?_, fun hty => ?_⟩ <;> rcases h t m cl ht hm hs with hu | hw
  · exact .inl hu
  · rw [hty] at hw; exact .inr (ptrOpt_of_wordOK hw).2
  · exact .inl hu
  · rw [hty] at hw; exact .inr (ptr_of_wordOK hw).2

/-- **Pointer typing along runs**: at an observer's cell of type `ptrOpt μ u` / `ptr μ u`, every message
not among the observer's own promises is `undef`, `null` (`ptrOpt` only), or a location at offset `0`
of a cell of the observer's cut typed by `u` up to `Fd`.  Caveats as `reachable_memTyped`. -/
theorem reachable_ptrTyped {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    ∃ Eg : GEnv, ∀ i th, c.ths[i]? = some th → ∃ S, PtrTypedAt (Cut Eg i S) c th := by
  obtain ⟨Eg, h⟩ := reachable_memTyped O hk h0 hr
  exact ⟨Eg, fun i th hth => have ⟨S, hS⟩ := h i th hth; ⟨S, ptrTypedAt_of hS⟩⟩

/-- **Pointer typing along runs, at a standard initial configuration** (`TermInit.InitShape`). -/
theorem reachable_ptrTyped_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {c0 : Cfg}
    (O : ObligationsF p k arch Init (fun _ => True) c0) (hk : k.storeDepRts = true)
    (hs : TermInit.InitShape p c0) {c : Cfg} (hr : TermStep.Steps p k arch c0 c) :
    ∃ Eg : GEnv, ∀ i th, c.ths[i]? = some th → ∃ S, PtrTypedAt (Cut Eg i S) c th := by
  obtain ⟨Eg, h⟩ := reachable_memTyped_init O hk hs hr
  exact ⟨Eg, fun i th hth => have ⟨S, hS⟩ := h i th hth; ⟨S, ptrTypedAt_of hS⟩⟩

end TermMemTyped

#print axioms TermMemTyped.memTyped_of_frameTie
#print axioms TermMemTyped.reachable_memTyped
#print axioms TermMemTyped.reachable_memTyped_init
#print axioms TermMemTyped.segOf_ref
#print axioms TermMemTyped.single_word
#print axioms TermMemTyped.ptrOpt_of_wordOK
#print axioms TermMemTyped.ptr_of_wordOK
#print axioms TermMemTyped.ptrTypedAt_of
#print axioms TermMemTyped.reachable_ptrTyped
#print axioms TermMemTyped.reachable_ptrTyped_init
