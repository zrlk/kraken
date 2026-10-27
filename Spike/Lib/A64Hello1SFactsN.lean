/-
**`hello1.w` on AArch64: `SFactsA` at a node's states** (the per-pair
facts of the allocation-capable consumer, `Spike/Lib/A64SegInstA.lean`, at
the levels' fragments `W0`, `W1` of `Spike/Test/A64Hello1LevelsA.lean`),
from the node lemmas' `SFacts` (`Spike/Lib/A64Hello1I.lean`).

- **The placement grows** (`wordPlaceRep_mono`, `Placed.mono`,
  `FramesPlaced.mono`, `static_le_upd`): a placement of more labels
  represents every word a smaller one does, so the static placement's facts
  hold at `upd hello1Λ.static l b`.
- **The source's runs** (`RunOk`, `RunOk.ofGood1`): the cell and zero
  obligations at every control a frame run reaches, a fact of the source
  pair alone; `runOk_hello1`, `runOk_of_term`: at `hello1Src`'s pairs
  (`Good1H`, `Spike/Lib/Hello1Runs.lean`: no load or store, and only
  `LanesU8` buffers, which the zero check accepts).
  `runOk_ho`, `runOk_hello1o`: the same at a checked program's pairs
  (`Good1Ho`, `Spike/Lib/Hello1oRuns.lean`) and at `hello1o`'s, `print`
  linked.
- **No write into the arena** (`NoArenaWr`, `wrOkA_of_noArenaWr`,
  `noArenaWr_of_noWr`, `noArenaWr_store`): an instruction writing no arena
  word and not the counter meets the write obligation at every frame run.
- **`SFactsA` from `SFacts`** (`sfactsA_of`): at any frames placed with small
  environments, any write tail, an abort phase `Ab` the state keeps
  (`AbSt`); the abort sites from `SFacts.abortOk`.
- **At `hello1`'s marks** (`sfactsA_wr`, `sfactsA_wr'`): from `Wr` under
  the loader's parse (`hpa`); **at a node's states** (`sfactsA_node`,
  `sfactsA_node'`): from a node lemma's `NodeW`, at the frames `fs` (`[]`,
  `framesPlaced_nil`, or a setup frame), the per-state premises over the
  node's states. The primed forms take the write obligation itself (the
  allocator's counter add, a header store).
-/
import Spike.Lib.A64SFactsA
import Spike.Lib.A64PlacedS
import Spike.Lib.A64StubFacts
import Spike.Lib.Frames1
import Spike.Lib.Hello1Runs
import Spike.Lib.Hello1oRuns
import Spike.Lib.A64Hello1I

namespace Spike.Lib.A64.Flow.Hello1.SFactsN

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)
open SccCode (hello1Λ hello1Prog hello1Asm)

/-! ## The placement grows -/

/-- A pair representation under a placement of more labels. -/
theorem locRep_mono {lbl lbl' : WeakMem.AllocLabel → Option Nat} (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    {x : WeakMem.Val} {vb vo : Nat} (h : LocRep lbl x vb vo) : LocRep lbl' x vb vo := by
  cases x with
  | loc a g => exact ⟨h.1, hl _ _ h.2.1, h.2.2⟩
  | _ => exact h

/-- **A word place's representation under a placement of more labels.** -/
theorem wordPlaceRep_mono {M : ExtMachine} {lbl lbl' : WeakMem.AllocLabel → Option Nat}
    (hl : ∀ l b, lbl l = some b → lbl' l = some b) {st : M.I.State} {wp : WordPlace M.I.RegId} {x : WeakMem.Val}
    (h : WordPlaceRep M lbl st wp x) : WordPlaceRep M lbl' st wp x := by
  cases wp with
  | one pl =>
    obtain ⟨v, hv, hr⟩ := h
    exact ⟨v, hv, MemRel.valRep_mono hl hr⟩
  | loc pb po =>
    obtain ⟨vb, vo, hb, ho, hr⟩ := h
    exact ⟨vb, vo, hb, ho, locRep_mono hl hr⟩
  | imm n => exact MemRel.valRep_mono hl h

variable {Λ : Scc.Sem.Layout} {lbl lbl' : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **A control placed under a placement of more labels.** -/
theorem Placed.mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) (h : Placed Λ lbl s c) : Placed Λ lbl' s c := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm, fun x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono hl (hrep x ty ws hx k wd wp hwd hwp), htot, himm⟩

/-- **Suspended frames placed under a placement of more labels.** -/
theorem FramesPlaced.mono (hl : ∀ l b, lbl l = some b → lbl' l = some b) (h : FramesPlaced Λ lbl s fs) :
    FramesPlaced Λ lbl' s fs := by
  obtain ⟨envm, hrep, htot, himm⟩ := h
  exact ⟨envm, fun d f hf x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono hl (hrep d f hf x ty ws hx k wd wp hwd hwp),
    htot, himm⟩

/-- No suspended frame is placed. -/
theorem framesPlaced_nil : FramesPlaced Λ lbl s [] :=
  (FramesPlacedIn.nil (fun _ => False)).toFramesPlaced

/-- **Placing a fresh label keeps the others.** -/
theorem static_le_upd {L : Lbl} {l : WeakMem.AllocLabel} {b : Nat} (h : L l = none) :
    ∀ l' b', L l' = some b' → Spike.Lib.A64ConsumerA.upd L l b l' = some b' := by
  intro l' b' h'
  unfold Spike.Lib.A64ConsumerA.upd
  split
  · subst l'; rw [h] at h'; cases h'
  · exact h'

/-! ## The source's runs -/

/-- **The source pair's run obligations** (`SFactsA.cell`, `SFactsA.zero`):
at every control a frame run from `(c, fs)` reaches, a one-cell access type
at a load or store, a zero-able type at a buffer allocation. -/
structure RunOk (p : Prog) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  zero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true

/-- `RunOk` along a frame run. -/
theorem RunOk.run {p : Prog} {c₁ : Ctl} {fs₁ : List TermRun.Frame} (h : RunOk p c fs)
    (hr : FrameRun p (c, fs) (c₁, fs₁)) : RunOk p c₁ fs₁ :=
  ⟨fun _ _ hr' => h.cell _ _ (hr.trans hr'), fun _ _ hr' => h.zero _ _ (hr.trans hr')⟩

/-- **`RunOk` at a `Good1` pair of an `Accepted1` program**: no load, store
or buffer allocation is reached. -/
theorem RunOk.ofGood1 {p : Prog} (hp : Scc.Lower.Accepted1 p = true) (hg : Good1 p (c, fs)) : RunOk p c fs where
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
theorem runOk_ho {p : Prog} (hp : Spike.Lib.Hello1oRuns.ProgOk p) (hg : Spike.Lib.Hello1oRuns.Good1Ho p (c, fs)) :
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

/-! ## No write into the arena -/

/-- **The instruction at `s` writes no arena word and not the counter.** -/
def NoArenaWr (ar : Arena) (s : State) : Prop :=
  ∀ L, WrAt s L → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) ∧ L ≠ ar.ctrLoc

/-- **The write obligation off the arena**, at every placement, memory
side, landing and control. -/
theorem wrOkA_of_noArenaWr {ar : Arena} {lsize : Lsize} {ms : MemSide isaLSE2} {X : Frag isaLSE2}
    (h : NoArenaWr ar s) : WrOkA ar lbl lsize ms X s c :=
  ⟨fun L hL => .inr (.inl (h L hL).1), fun hL => ((h _ hL).2 rfl).elim⟩

/-- An instruction writing nothing writes no arena word. -/
theorem noArenaWr_of_noWr {ar : Arena} (h : ∀ L, ¬ WrAt s L) : NoArenaWr ar s :=
  fun L hL => (h L hL).elim

/-- **A store off the arena, not the counter word.** -/
theorem noArenaWr_store {ar : Arena} {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : State}
    (he : isaLSE2.exec s = some (.store kr false L V fun _ => .done s'))
    (hoff : ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells)) (hne : L ≠ ar.ctrLoc) :
    NoArenaWr ar s :=
  fun _ hL => wrAt_store he hL ▸ ⟨hoff, hne⟩

/-! ## `SFactsA` from `SFacts` -/

section Gen

variable {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own} {rS : Range}
  {Tk : State → Prop} {ar : Arena} {J : InvS} {lbl0 : Lbl} {lsize : Lsize} {Dt Ab : State → Prop}

/-- **`SFactsA` from `SFacts`** at a placement `lbl0` within `lbl`: the
suspended frames placed (`hfp`) with small environments (`hes`), the abort
phase kept (`hab`), the source's runs (`hrun`) and the write obligation at
the controls they reach (`hwr`); any write tail. -/
theorem sfactsA_of' (h : SFacts Λ μ own rS Tk lbl0 s c) (hle : ∀ l b, lbl0 l = some b → lbl l = some b)
    (hfp : FramesPlaced Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ Ab s) (hrun : RunOk p c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') :
    SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab :=
  SFactsA.ofSt (SFacts.dt_mono (Dt' := Dt) h fun _ h => h.elim).toSt hab (fun _ => h.noRet) hrun.cell
    (.of_placedS (PlacedS.ofFrames (Placed.mono hle h.place) hfp)) hwr hrun.zero fun k a ha hpc => by
      obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
      exact ⟨.inr (.inl ⟨hk, ho, he, hes⟩), hx⟩

/-- **`SFactsA` from `SFacts`** at an instruction writing no arena word. -/
theorem sfactsA_of (h : SFacts Λ μ own rS Tk lbl0 s c) (hle : ∀ l b, lbl0 l = some b → lbl l = some b)
    (hfp : FramesPlaced Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ Ab s) (hrun : RunOk p c fs)
    (hwr : NoArenaWr ar s) :
    SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab :=
  sfactsA_of' h hle hfp hes hab hrun fun _ _ _ _ => wrOkA_of_noArenaWr hwr

end Gen

/-! ## At `hello1`'s marks and nodes -/

section Hello1

variable {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
  {lsize : Lsize} {Dt Ab : State → Prop} {R : Region} {F : MachineData → Prop} {n : ND}

/-- **`SFactsA` at `hello1`'s marks from `Wr`**, the write obligation given. -/
theorem sfactsA_wr' (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog) (h : Wr rS s c)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b) (hfp : FramesPlaced hello1Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ0 Ab s) (hrun : RunOk p c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') :
    SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab := by
  rw [hello1_marks hpa] at hwr ⊢
  exact sfactsA_of' h hle hfp hes hab hrun hwr

/-- **`SFactsA` at `hello1`'s marks from `Wr`** at an instruction writing
no arena word. -/
theorem sfactsA_wr (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog) (h : Wr rS s c)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b) (hfp : FramesPlaced hello1Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ0 Ab s) (hrun : RunOk p c fs) (hwr : NoArenaWr ar s) :
    SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab :=
  sfactsA_wr' hpa h hle hfp hes hab hrun fun _ _ _ _ => wrOkA_of_noArenaWr hwr

/-- **`SFactsA` at a node's states at the frames `fs`** from the node's
`NodeW` (a node lemma of `Spike/Lib/A64Hello1I.lean`), the write obligation
given; the frames' placement, the abort phase and the source's runs over
the node's states. -/
theorem sfactsA_node' (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog)
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

/-- **`SFactsA` at a node's states at the frames `fs`** from the node's
`NodeW`, its instruction writing no arena word. -/
theorem sfactsA_node (hpa : Scc.Sem.A64.textProgram hello1Asm = .ok hello1Prog)
    (hN : NodeW (Wr rS) (Kr rS) hello1Exe hello1End R F n)
    (hle : ∀ l b, hello1Λ.static l = some b → lbl l = some b)
    (hfp : ∀ s c, At hello1Exe hello1End R F n s c → FramesPlaced hello1Λ lbl s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : ∀ s c, At hello1Exe hello1End R F n s c → AbSt μ0 Ab s)
    (hrun : ∀ s c, At hello1Exe hello1End R F n s c → RunOk p c fs)
    (hwr : ∀ s c, At hello1Exe hello1End R F n s c → NoArenaWr ar s) :
    ∀ s c fs', (At hello1Exe hello1End R F n).at fs s c fs' →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs' Dt Ab :=
  sfactsA_node' hpa hN hle hfp hes hab hrun fun s c hA _ _ _ _ => wrOkA_of_noArenaWr (hwr s c hA)

end Hello1

end Spike.Lib.A64.Flow.Hello1.SFactsN
