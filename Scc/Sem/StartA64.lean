/-
**The components of `R` at load, AArch64, one thread** (`Scc/Sem/Correct.lean`,
`Components`): the canonical AArch64 target's loaded configuration
(`A64.loadProg`, kernel hooks) and the source start (`SrcStart.start`)
are related, witnessed by `Witness.start`.

At the source start nothing is live: the one thread enters `main` on a unit
argument, which has no word, and memory is empty (`not_live_start`). So
every memory clause of `Components` is vacuous, and so are the environment
clauses. What is left:

- the thread map, source thread 0 to target slot 0, which is the only slot
  that runs at load (`KState.init`: slot 0 running, the others dormant);
- the layout injection, `Λ.static` placed by the static link's image check
  (`Scc/Sem/Start1.lean`, `StaticSyms`);
- the stack map: no range is held at load, so no thread has a stack range.

The initial value of a word is its image word (`wordAt_load`, through
the link image's `wordOf`; for an 8-aligned item, `image_word` gives it as the
item's little-endian word). It is not needed at the start, where no source
message exists, but a later read of a static cell needs it.

The ISA-free half (`not_live_start`, `Witness.start`,
`Kernel.KState.init_runs`, the initial words over `wordsList`) is in
`Scc/Sem/StartLoad.lean`, shared with `Scc/Sem/StartX64.lean`.

- `A64.init_runs`, `A64.init_stackRange`, `A64.components_load`;
- `A64.find?_wordsMem`, `A64.initVal_wordsMem`, `A64.wordAt_load`,
  `A64.loadProg_init`: the target's initial word at an image address.
-/
import Scc.Sem.StartLoad
import Scc.Sem.TargetA64

namespace Scc.Sem

open Kraken Kraken.Promising

namespace A64

/-- At load only slot 0 runs (`Kernel.KState.init_runs`). -/
theorem init_runs {n : Nat} {E : Entry} {Λ : Layout} {j : Nat} (h : (Kernel.KState.init n E Λ).runs j = true) :
    j = 0 :=
  Kernel.KState.init_runs h

/-- At load no thread has a stack range: no range is held. -/
theorem init_stackRange {n : Nat} {E : Entry} {Λ : Layout} {prog : _root_.Program}
    {syms : List (String × Nat)} {mem : List (Loc × Val)} (j : Nat) :
    (machine (kernel n)).stackRange (loadProg (kernel n) E Λ prog syms mem) j = none := by
  show Kernel.stackRangeOf abi (loadProg (kernel n) E Λ prog syms mem) j = none
  unfold Kernel.stackRangeOf
  split <;> simp [loadProg, kernel, Kernel.hooks, Kernel.KState.init]

open Scc.Cert.Link in
/-- **The components of `R` at load**: the canonical AArch64 target's
loaded configuration and the source start, witnessed by `Witness.start`,
given the static link's image check and the static labels at their
symbols. -/
theorem components_load {n : Nat} {E : Entry} {Λ : Layout} {prog : _root_.Program}
    {syms : List (String × Nat)} {mem : List (Loc × Val)} {cap : Nat} {lsize : WeakMem.AllocLabel → Nat}
    {secs : DataSecs} {code : String → Option Nat} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name) :
    Components (machine (kernel n)) Λ (Witness.start _ Λ lsize) (loadProg (kernel n) E Λ prog syms mem)
      (SrcStart.start cap) where
  thr_total i hi := by
    have : i = 0 := by simpa [SrcStart.start, SrcSem.mainStart] using hi
    subst this
    exact ⟨0, rfl, by simp only [loadProg, Config.init, List.size_toArray, List.length_map]; exact Nat.zero_lt_succ _⟩
  thr_inj i i' j h h' := by
    simp only [Witness.start] at h h'
    split at h <;> split at h' <;> simp_all
  thr_onto j tt hr _ := by
    obtain ⟨-, -, hd⟩ := hr
    have hj : j = 0 := init_runs (n := n) (E := E) (Λ := Λ) (by
      simp only [machine, ExtMachine.ofHooks, loadProg, kernel, Kernel.hooks, Bool.not_eq_false] at hd
      exact hd)
    subst hj
    exact ⟨0, by simp [SrcStart.start, SrcSem.mainStart], rfl⟩
  lbl_static _ _ h := h
  lbl_range := hss.range himg
  lbl_disj _ _ _ _ _ hl := absurd hl not_live_start
  lbl_mem _ _ hl := absurd hl not_live_start
  epoch_fixed _ _ := rfl
  mem_rep _ _ _ hl := absurd hl not_live_start
  ts_first _ _ _ hl := absurd hl not_live_start
  ts_mono _ _ _ _ _ _ _ _ _ hl := absurd hl not_live_start
  mem_onto _ _ _ h := absurd h.choose_spec.choose_spec.1 not_live_start
  pre_alloc _ _ _ _ h := absurd h.choose_spec.choose_spec.1 not_live_start
  env_rep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he := nomatch he
  env_total i th hth d e xs he hxs _hxf x _ ty ws hws k hk := by
    exfalso
    obtain ⟨-, rfl⟩ := SrcStart.start_ths hth
    match d, he with
    | 0, he =>
      simp only [frameEnvs, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      simp only [TermRun.lookupE, List.find?_cons, List.find?_nil] at hws
      split at hws <;> simp_all
  stack_pool j rg h := by rw [init_stackRange] at h; cases h
  stack_disj j _ rg _ _ h := by rw [init_stackRange] at h; cases h
  stack_owned j rg h := by rw [init_stackRange] at h; cases h
  stack_private j rg h := by rw [init_stackRange] at h; cases h
  stack_marked _ _ h := h.elim
  stack_unmarked _ _ _ _ _ _ _ _ _ _ h := h
  env_imm _ _ _ _ _ _ _ _ _ h := nomatch h

/-! ## The initial words -/

/-- Looking up a word address among `wordsMem ws` is looking it up in `ws`,
when every address fits in 64 bits (`find?_wordsList`). -/
theorem find?_wordsMem {ws : List (Nat × Nat)} (hlt : ∀ p ∈ ws, p.1 < 2 ^ 64) {a : Nat} (ha : a < 2 ^ 64) :
    (wordsMem ws).find? (·.1 == wordLoc a) =
      (ws.find? (·.1 == a)).map fun p => ((⟨BitVec.ofNat 64 p.1, 8⟩ : Loc), BitVec.ofNat 128 p.2) :=
  find?_wordsList hlt ha

/-- **The initial value of an image word** (`initVal_wordsList`). -/
theorem initVal_wordsMem {Λ : Layout} (hwf : Λ.WF) {rest : List (Loc × Val)} {tm : Memory}
    (hinit : tm.init = imageMem Λ ++ rest) {a v : Nat} (hav : (a, v) ∈ Λ.image) :
    (tm.initVal (wordLoc a)).toNat = Scc.Cert.Link.wordOf Λ.image a :=
  initVal_wordsList hwf hinit hav

/-- **The target's initial word at an image address** is its image word
(`wordAt` at timestamp 0; `wordAt_wordsList`). With `image_word`, for an
8-aligned item it is the item's little-endian word. -/
theorem wordAt_load {Λ : Layout} (hwf : Λ.WF) {rest : List (Loc × Val)} {tm : Memory}
    (hinit : tm.init = imageMem Λ ++ rest) {a v : Nat} (hav : (a, v) ∈ Λ.image) :
    wordAt tm a 0 = some (Scc.Cert.Link.wordOf Λ.image a) :=
  wordAt_wordsList hwf hinit hav

/-- The loaded memory's initial values are the image, then `.rodata`. -/
theorem loadProg_init {n : Nat} {E : Entry} {Λ : Layout} {prog : _root_.Program}
    {syms : List (String × Nat)} (rest : List (Loc × Val)) :
    (loadProg (kernel n) E Λ prog syms (imageMem Λ ++ rest)).1.mem.init = imageMem Λ ++ rest := rfl

end A64

end Scc.Sem
