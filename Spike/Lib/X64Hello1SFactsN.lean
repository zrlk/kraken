/-
**`hello1`'s per-pair facts at a node state with frames** (x86-64; the twin
of `Spike/Lib/A64Hello1SFactsN.lean`): `SFactsA` (`Spike/Lib/X64SegInstA.lean`)
at a pair of a node's fragment at fixed frames (`(At …).at fs`, the levels'
node states at `fs = []` or under the setup block's frame), from the node's
`SFacts` (`Wr`, as the node lemmas give it) and the facts of the pair the
frames add, at any placement extending the static one and any fragment `J`.

- `RunOk`: the obligations of `SFactsA` quantified over the frame runs from
  the pair (`cell`, `zero`); `RunOk.run` (kept by a frame run),
  `RunOk.ofGood1` (at a `Good1` pair of an `Accepted1` program, no load,
  store or allocation is reached); `runOk_hello1`, `runOk_of_term`: at
  `hello1Src`'s pairs (`Good1H`, `Spike/Lib/Hello1Runs.lean`: no load or
  store, and only `LanesU8` buffers, which the zero check accepts).
  `runOk_ho`, `runOk_hello1o`: the same at a checked program's pairs
  (`Good1Ho`, `Spike/Lib/Hello1oRuns.lean`) and at `hello1o`'s, `print`
  linked.
- `NoArenaWr`: every location the instruction writes is off the arena and
  not the counter word; `wrOkA_of_noArenaWr` (`WrOkA` at any memory side
  and landing), `noArenaWr_of_noWr`, `noArenaWr_store`.
- `locRep_mono`, `wordPlaceRep_mono`, `Placed.mono`, `FramesPlaced.mono`:
  placing more labels keeps the placements; `framesPlaced_nil`;
  `static_le_upd`: the static placement is below one more label's.
- `sfactsA_of` (`NoArenaWr`), `sfactsA_of'` (a raw write obligation):
  `SFactsA` at frames `fs` from `SFacts` at a smaller placement, the
  suspended frames placed and small, `AbSt`, `RunOk`; generic in the layout
  and the marks.
- `sfactsA_wr`, `sfactsA_wr'`: the same at `hello1`'s marks from `Wr`.
- `sfactsA_node`, `sfactsA_node'`: at every pair of a node's fragment at
  frames `fs`, from the node's `NodeW` into `Wr` and the per-state facts.
-/
import Spike.Lib.X64Hello1I
import Spike.Lib.X64SFactsA
import Spike.Lib.X64StubFacts
import Spike.Lib.X64PlacedS
import Spike.Lib.Frames1
import Spike.Lib.Hello1Runs
import Spike.Lib.Hello1oRuns

namespace Spike.Lib.X64.Flow.Hello1.SFactsN

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FrameRun Good1 good1_run)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (At NodeW ND)
open Spike.Lib.X64.Flow.Hello1.Inst (Wr Kr μ0 hello1_marks own Tk)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)
open SccCode (hello1Asm hello1Λ hello1Cells)

/-! ## The frame runs' obligations -/

/-- **The obligations at the controls the frame runs reach** from `(c, fs)`
(`SFactsA.cell`, `SFactsA.zero`): the loads and stores access single-word
cells, and every buffer allocated has a type the zero check accepts. -/
structure RunOk (p : Prog) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  zero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true

variable {p : Prog} {c c' : Ctl} {fs fs' : List TermRun.Frame}

/-- **A frame run keeps `RunOk`.** -/
theorem RunOk.run (h : RunOk p c fs) (hr : FrameRun p (c, fs) (c', fs')) : RunOk p c' fs' :=
  ⟨fun _ _ hr' => h.cell _ _ (hr.trans hr'), fun _ _ hr' => h.zero _ _ (hr.trans hr')⟩

/-- **`RunOk` at a `Good1` pair** of an `Accepted1` program: no control a
frame run reaches loads, stores or allocates. -/
theorem RunOk.ofGood1 (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, fs)) : RunOk p c fs where
  cell := fun _ _ hr x a e _ _ hc => by
    have hg' := good1_run hp hr hg
    rcases hc with hc | ⟨b, hc⟩
    · exact (hg'.not_load x true a e hc).elim
    · exact (hg'.not_store x true a b none e hc).elim
  zero := fun _ _ hr x a τ e hc => ((good1_run hp hr hg).not_newBuf x a τ e hc).elim

/-- **`RunOk` at a pair of `hello1.w`'s runs** (`Good1H`): no control a
frame run reaches loads or stores, and every buffer it allocates is
`LanesU8`. -/
theorem runOk_hello1 (hg : Spike.Lib.Hello1Runs.Good1H (c, fs)) : RunOk Spike.Lib.Hello1Src.hello1Src c fs where
  cell := fun _ _ hr x a e _ _ hc => by
    have hg' := Spike.Lib.Hello1Runs.good1H_run hr hg
    rcases hc with hc | ⟨b, hc⟩
    · exact (hg'.not_load x true a e hc).elim
    · exact (hg'.not_store x true a b none e hc).elim
  zero := fun _ _ hr _ _ _ _ hc => by
    rw [(Spike.Lib.Hello1Runs.good1H_run hr hg).newBuf_ty hc]
    exact zeroOkTy_lanes false .w8

/-- **`RunOk` at a pair whose term and frame bodies are among `hello1.w`'s
runs' terms** (`runOk_hello1`; decidable on a concrete term). -/
theorem runOk_of_term (ht : c.term ∈ Spike.Lib.Hello1Runs.hello1Terms)
    (hfs : ∀ f ∈ fs, f.body ∈ Spike.Lib.Hello1Runs.hello1Terms) : RunOk Spike.Lib.Hello1Src.hello1Src c fs :=
  runOk_hello1 ⟨ht, hfs⟩

/-- **`RunOk` at a pair of a checked program's runs** (`Good1Ho`,
`Spike/Lib/Hello1oRuns.lean`): no control a frame run reaches loads or
stores, and every buffer it allocates is `LanesU8`. -/
theorem runOk_ho (hp : Spike.Lib.Hello1oRuns.ProgOk p) (hg : Spike.Lib.Hello1oRuns.Good1Ho p (c, fs)) :
    RunOk p c fs where
  cell := fun _ _ hr x a e _ _ hc => by
    have hg' := Spike.Lib.Hello1oRuns.good1Ho_run hp hr hg
    rcases hc with hc | ⟨b, hc⟩
    · exact (hg'.not_load hp x true a e hc).elim
    · exact (hg'.not_store hp x true a b none e hc).elim
  zero := fun _ _ hr _ _ _ _ hc => by
    rw [(Spike.Lib.Hello1oRuns.good1Ho_run hp hr hg).newBuf_ty hp hc]
    exact zeroOkTy_lanes false .w8

/-- **`RunOk` at a pair of `hello1o`'s runs** (`hello1.w` with `print`
linked) whose term and frame bodies are among `hello1oTerms` (decidable on
a concrete term). -/
theorem runOk_hello1o (ht : c.term ∈ Spike.Lib.Hello1oRuns.hello1oTerms)
    (hfs : ∀ f ∈ fs, f.body ∈ Spike.Lib.Hello1oRuns.hello1oTerms) :
    RunOk Spike.Test.Hello1MainSrc.hello1o c fs :=
  runOk_ho Spike.Lib.Hello1oRuns.hello1o_ok (Spike.Lib.Hello1oRuns.good1Ho_of_mem ht hfs)

/-! ## Writes off the arena -/

/-- **The instruction at `s` writes off the arena**: every location it
writes (`WrAt`) is outside the heap arena's cells and not its counter
word. -/
def NoArenaWr (ar : Arena) (s : State) : Prop :=
  ∀ L, WrAt s L → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) ∧ L ≠ ar.ctrLoc

variable {ar : Arena} {s : State}

/-- **`WrOkA` from writes off the arena**, at any placement, sizes, memory
side and landing: every write is `ArenaW`'s off-arena case, and none is the
counter word. -/
theorem wrOkA_of_noArenaWr {lbl : Lbl} {lsize : Lsize} {ms : Spike.Lib.MemSide isa} {X : Spike.Lib.Frag isa}
    (h : NoArenaWr ar s) : WrOkA ar lbl lsize ms X s c :=
  ⟨fun L hL => .inr (.inl (h L hL).1), fun hL => ((h _ hL).2 rfl).elim⟩

/-- An instruction writing nothing writes off the arena. -/
theorem noArenaWr_of_noWr (h : ∀ L, ¬ WrAt s L) : NoArenaWr ar s :=
  fun L hL => (h L hL).elim

/-- **A store off the arena, not the counter word**, writes off the arena. -/
theorem noArenaWr_store {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : State}
    (he : isa.exec s = some (.store kr false L V fun _ => .done s'))
    (hoff : ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells)) (hne : L ≠ ar.ctrLoc) :
    NoArenaWr ar s :=
  fun _ hL => wrAt_store he hL ▸ ⟨hoff, hne⟩

/-! ## More labels placed -/

variable {lbl lbl' : Lbl}

/-- Placing more labels keeps every locative pair's representation. -/
theorem locRep_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) {x : WeakMem.Val} {vb vo : Nat}
    (h : LocRep lbl x vb vo) : LocRep lbl' x vb vo := by
  cases x with
  | loc a g => exact ⟨h.1, hl _ _ h.2.1, h.2.2⟩
  | _ => exact h

/-- Placing more labels keeps every word place's representation. -/
theorem wordPlaceRep_mono (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    {wp : WordPlace (machine (kernel 1)).I.RegId} {v : WeakMem.Val}
    (h : WordPlaceRep (machine (kernel 1)) lbl s wp v) : WordPlaceRep (machine (kernel 1)) lbl' s wp v := by
  cases wp with
  | one pl => obtain ⟨v', hv, hr⟩ := h; exact ⟨v', hv, Scc.Sem.MemRel.valRep_mono hl hr⟩
  | loc pb po => obtain ⟨vb, vo, hb, ho, hr⟩ := h; exact ⟨vb, vo, hb, ho, locRep_mono hl hr⟩
  | imm n => exact Scc.Sem.MemRel.valRep_mono hl h

/-- **Placing more labels keeps a control placed.** -/
theorem Placed.mono {Λ : Scc.Sem.Layout} (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    (h : Placed Λ lbl s c) : Placed Λ lbl' s c := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm, fun x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono hl (hrep x ty ws hx k wd wp hwd hwp),
    htot, himm⟩

/-- **Placing more labels keeps the suspended frames placed.** -/
theorem FramesPlaced.mono {Λ : Scc.Sem.Layout} (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    (h : FramesPlaced Λ lbl s fs) : FramesPlaced Λ lbl' s fs := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono hl (hrep d f hf x ty ws hx k wd wp hwd hwp),
    htot, himm⟩

/-- No suspended frame is placed anywhere. -/
theorem framesPlaced_nil {Λ : Scc.Sem.Layout} : FramesPlaced Λ lbl s [] :=
  ⟨fun _ _ _ => none, fun _ _ hf => by simp at hf, fun _ _ hf => by simp at hf, fun _ _ _ _ _ hf => by simp at hf⟩

/-- **The static placement is below one more label's**, at a label it does
not place. -/
theorem static_le_upd {L : Lbl} {l : WeakMem.AllocLabel} {b : Nat} (hl : L l = none) :
    ∀ l' b', L l' = some b' → Spike.Lib.X64ConsumerA.upd L l b l' = some b' := by
  intro l' b' h
  unfold Spike.Lib.X64ConsumerA.upd
  split
  · subst l'; rw [hl] at h; cases h
  · exact h

/-! ## `SFactsA` at frames from `SFacts` -/

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own0 : Own}
  {rS : Range} {Tk0 : State → Prop} {J : InvS} {lbl0 : Lbl} {lsize : Lsize} {Dt Ab : State → Prop}

/-- **`SFactsA` at the frames `fs` from `SFacts`** at a smaller placement
`lbl0` (`hle`) and a raw write obligation `hwr` at the controls the frame
runs reach: the current control's facts, the suspended frames placed
(`hfp`) and small (`hes`, with the current environment's from
`SFacts.abortOk`, the overflow site's `EnvSmallS`), the abort phase
(`hab`), the frame runs' obligations (`hrun`). -/
theorem sfactsA_of' (h : SFacts Λ μ own0 rS Tk0 lbl0 s c Dt) (hle : ∀ l b, lbl0 l = some b → lbl l = some b)
    (hfp : FramesPlaced Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ Ab s) (hrun : RunOk p c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own0 s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') :
    SFactsA Λ μ p rd G (fun s _ => own0 s) rS Tk0 ar J lbl lsize s c fs Dt Ab :=
  SFactsA.ofSt h.toSt hab (fun _ => h.noRet) hrun.cell
    (.of_placedS (PlacedS.ofFrames (Placed.mono hle h.place) hfp)) hwr hrun.zero fun k a ha hpc => by
      obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
      exact ⟨.inr (.inl ⟨hk, ho, he, hes⟩), hx⟩

/-- **`SFactsA` at the frames `fs` from `SFacts`**, the instruction writing
off the arena (`NoArenaWr`). -/
theorem sfactsA_of (h : SFacts Λ μ own0 rS Tk0 lbl0 s c Dt) (hle : ∀ l b, lbl0 l = some b → lbl l = some b)
    (hfp : FramesPlaced Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ Ab s) (hrun : RunOk p c fs)
    (hwr : NoArenaWr ar s) :
    SFactsA Λ μ p rd G (fun s _ => own0 s) rS Tk0 ar J lbl lsize s c fs Dt Ab :=
  sfactsA_of' h hle hfp hes hab hrun fun _ _ _ _ => wrOkA_of_noArenaWr hwr

/-! ## At `hello1`'s marks -/

/-- **`SFactsA` at `hello1`'s marks from `Wr`**, with a raw write
obligation (`sfactsA_of'` at `μ0`, the marks by the loader's parse
`hpa`). -/
theorem sfactsA_wr' (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells) (h : Wr rS s c)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b)
    (hfp : FramesPlaced hello1Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ0 Ab s)
    (hrun : RunOk p c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') :
    SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab := by
  rw [hello1_marks hpa] at hwr ⊢
  exact sfactsA_of' (h.dt_mono fun _ h => h.elim) hle hfp hes hab hrun hwr

/-- **`SFactsA` at `hello1`'s marks from `Wr`**, the instruction writing
off the arena. -/
theorem sfactsA_wr (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells) (h : Wr rS s c)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b)
    (hfp : FramesPlaced hello1Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ0 Ab s)
    (hrun : RunOk p c fs) (hwr : NoArenaWr ar s) :
    SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab :=
  sfactsA_wr' hpa h hle hfp hes hab hrun fun _ _ _ _ => wrOkA_of_noArenaWr hwr

/-! ## At a node's states -/

variable {R : Region} {F : MachineData → Prop} {n : ND}

/-- **`SFactsA` at every pair of a node's fragment at the frames `fs`**,
with a raw write obligation: the node's states inside `Wr` (`hN`, as the
node lemmas give it), and at each of them the suspended frames placed, the
abort phase, the frame runs' obligations and the write obligation. -/
theorem sfactsA_node' (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells)
    (hN : NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b)
    (hfp : ∀ s c, At hello1Exe hello1End R F n s c → FramesPlaced hello1Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : ∀ s c, At hello1Exe hello1End R F n s c → AbSt μ0 Ab s)
    (hrun : ∀ s c, At hello1Exe hello1End R F n s c → RunOk p c fs)
    (hwr : ∀ s c, At hello1Exe hello1End R F n s c → ∀ c' fs', FrameRun p (c, fs) (c', fs') →
      abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') :
    ∀ s c fs', (At hello1Exe hello1End R F n).at fs s c fs' →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs' Dt Ab := by
  rintro s c _ ⟨hA, rfl⟩
  exact sfactsA_wr' hpa (hN s c hA).1 hle (hfp s c hA) hes (hab s c hA) (hrun s c hA) (hwr s c hA)

/-- **`SFactsA` at every pair of a node's fragment at the frames `fs`**,
each state's instruction writing off the arena. -/
theorem sfactsA_node (hpa : Scc.Sem.X64.cellsOf hello1Asm = some hello1Cells)
    (hN : NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b)
    (hfp : ∀ s c, At hello1Exe hello1End R F n s c → FramesPlaced hello1Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : ∀ s c, At hello1Exe hello1End R F n s c → AbSt μ0 Ab s)
    (hrun : ∀ s c, At hello1Exe hello1End R F n s c → RunOk p c fs)
    (hwr : ∀ s c, At hello1Exe hello1End R F n s c → NoArenaWr ar s) :
    ∀ s c fs', (At hello1Exe hello1End R F n).at fs s c fs' →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs' Dt Ab :=
  sfactsA_node' hpa hN hle hfp hes hab hrun fun s c hA _ _ _ _ => wrOkA_of_noArenaWr (hwr s c hA)

end Spike.Lib.X64.Flow.Hello1.SFactsN
