/-
**The invariants of `hello1.w`'s two levels on AArch64**
(`Spike/Lib/A64Hello1Levels.lean`): `hello1_correctKLS`'s `inv0`, `inv1`,
`h0`, `h1` and `hst` from the levels' closed segments (`SegWS`), with no
invariant written out.

- `segInvS_mono_xa`: a segment under a memory side with a larger allocation
  fragment (`OutS.mono_xa` at every pair).
- `xa_of_land`: `msOfA`'s allocation fragment at the rodata block's landing
  (`rd_land`'s data) from `inv1` at the landing's label, base and size.
- `exists_inv1`: the post-allocation family `inv1` with `h1`'s form, each
  member containing its level's start.
- `exists_inv0`: `inv0` with `h0`'s form, the greatest closed invariant
  inside `W0` (`GfpS`, `Spike/Test/A64Hello1Gfp.lean`), from the
  pre-allocation level at `Ih lsize ⊥ inv1` (the level's `xa` only reaches `inv1`), lifted to
  `Ih lsize inv0 inv1` by `segInvS_mono_xa`.
- `hello1_correctKLS_levels`: `hello1_correctKLS` with `inv0`, `inv1` chosen
  so, `hst` from the loaded thread at the pre-allocation level's start.
-/
import Spike.Lib.A64Hello1Levels
import Spike.Test.A64Hello1SetupChain
import Spike.Test.A64Hello1StartA
import Spike.Test.A64Hello1Gfp

namespace Spike.Test.A64Hello1LevelsA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Arena FragS OutS KOutS SegWS MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Test.A64ArenaHello1 (ar off_bytes2 units_bytes2)
open Spike.Test.A64Hello1CorrectA (Ih)
open SccCode (hello1Asm hello1Λ hello1Prog hello1Secs)
open Spike.Test.A64Hello1Gfp (gfpS_of_segWS le_gfpS segInvS_gfpS)

/-! ## Segments under a larger allocation fragment -/

/-- **A segment under a memory side with a larger allocation fragment**:
`ms'` is `ms` but for `xa`, which contains `ms`'s at every frame list. -/
theorem segInvS_mono_xa {p : Prog} {W inv : FragS isaLSE2} {K : State → State → Prop} {lbl : Lbl}
    {ms ms' : List TermRun.Frame → MemSide isaLSE2} (h : SegInvS W K p lbl ms inv)
    (he : ∀ fs, ms' fs = { ms fs with xa := (ms' fs).xa })
    (hxa : ∀ fs l b n s c, (ms fs).xa l b n s c → (ms' fs).xa l b n s c) : SegInvS W K p lbl ms' inv :=
  fun s c fs hi =>
    have h := h s c fs hi
    ⟨h.1, fun hk => OutS.mono_xa (h.2.1 hk) he hxa, h.2.2⟩

/-- `msOfA` at two fragments differs only in `xa`. -/
theorem msOfA_with_xa {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I I' : InvS} {lbl : Lbl} {lsize : Lsize} (fs : List TermRun.Frame) :
    msOfA Λ μ rd G own ar I' lbl lsize fs = { msOfA Λ μ rd G own ar I lbl lsize fs with
      xa := (msOfA Λ μ rd G own ar I' lbl lsize fs).xa } := rfl

/-- `msOfA`'s `xa` is monotone in the fragment. -/
theorem msOfA_xa_mono {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {I I' : InvS} {lbl : Lbl} {lsize : Lsize}
    (hI : ∀ lbl lsize s c fs, I lbl lsize s c fs → I' lbl lsize s c fs) (fs : List TermRun.Frame)
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : (msOfA Λ μ rd G own ar I lbl lsize fs).xa l b n s c) :
    (msOfA Λ μ rd G own ar I' lbl lsize fs).xa l b n s c :=
  ⟨h.1, hI _ _ _ _ _ h.2⟩

/-! ## The landing of the rodata block -/

/-- **`msOfA`'s allocation fragment at the rodata block's landing**: at the
base and size `rd_land` gives (`b` the heap plus `16 * old` plus the 2-byte
offset, `old` plus its units within the cells, `w = 2`), a fresh label `l`
whose `inv1 l b 2` holds is in `Ih`'s post-allocation branch. -/
theorem xa_of_land {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {lsize : Lsize} {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {fs : List TermRun.Frame} {l : WeakMem.AllocLabel} {b old : Nat} {s : State} {c : Spike.Lib.Ctl}
    (hb : b = (msOfA Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs).heap + 16 * old +
      (msOfA Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs).off 2 Spike.Lib.Hello1RodataSrc.τ8)
    (hold : old + (msOfA Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs).units 2
      Spike.Lib.Hello1RodataSrc.τ8 ≤ (msOfA Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs).cells)
    (hl : hello1Λ.static l = none) (h : inv1 l b 2 s c fs) :
    (msOfA Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize fs).xa l b 2 s c := by
  change b = ar.heap + 16 * old + ar.off 2 (.lanes false .w8) at hb
  change old + ar.units 2 (.lanes false .w8) ≤ ar.cells at hold
  rw [off_bytes2] at hb
  rw [units_bytes2] at hold
  have hAL : AllocLand ar.heap ar.cells b 2 := ⟨by omega, by omega, by omega⟩
  exact ⟨hAL, .inr ⟨l, b, 2, hl, hAL, rfl, rfl, h⟩⟩

/-! ## The invariants -/

section Invs

variable {p : Prog} {K : State → State → Prop} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {lsize : Lsize}

/-- **The post-allocation family**: from each fresh label's closed level
(`SegWS` from `P1 l b n`), a family `inv1` with `hello1_correctKLS`'s `h1`
form, each member containing its level's start. Off the fresh landings the
member is `⊥`. -/
theorem exists_inv1 {W1 P1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h1W : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegWS (W1 l b n) K p (upd hello1Λ.static l b)
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n))
        (P1 l b n) (fun _ _ _ => False)) :
    ∃ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2,
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1 l b n s c fs → inv1 l b n s c fs) ∧
      ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        SegInvS (W1 l b n) K p (upd hello1Λ.static l b)
          (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n))
          (inv1 l b n) := by
  have hx : ∀ l b n, ∃ inv : FragS isaLSE2, (hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      (∀ s c fs, P1 l b n s c fs → inv s c fs) ∧
      SegInvS (W1 l b n) K p (upd hello1Λ.static l b)
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n)) inv) := by
    intro l b n
    by_cases hp : hello1Λ.static l = none ∧ AllocLand ar.heap ar.cells b n
    · obtain ⟨inv, hP, hS⟩ := SegInvS.ofSegWS (h1W l b n hp.1 hp.2)
      exact ⟨inv, fun _ _ => ⟨hP, hS⟩⟩
    · exact ⟨fun _ _ _ => False, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  refine ⟨fun l b n => Classical.choose (hx l b n), fun l b n hl ha => ?_, fun l b n hl ha => ?_⟩
  · exact (Classical.choose_spec (hx l b n) hl ha).1
  · exact (Classical.choose_spec (hx l b n) hl ha).2

/-- **The pre-allocation invariant**: from the closed pre-allocation level
(`SegWS` from `P0`) at `Ih lsize ⊥ inv1`, an `inv0` containing `P0` and
every explicit-invariant segment inside `W0` at `Ih lsize ⊥ inv1` (`GfpS`,
the greatest), with `hello1_correctKLS`'s `h0` form at `Ih lsize inv0 inv1`
(`segInvS_mono_xa`: `Ih lsize ⊥ inv1` is in `Ih lsize inv0 inv1`). -/
theorem exists_inv0 {W0 P0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h0W : SegWS W0 K p hello1Λ.static
      (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) P0
      (fun _ _ _ => False)) :
    ∃ inv0 : FragS isaLSE2, (∀ s c fs, P0 s c fs → inv0 s c fs) ∧
      (∀ inv, SegInvS W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) inv →
        ∀ s c fs, inv s c fs → inv0 s c fs) ∧
      SegInvS W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize) inv0 := by
  refine ⟨_, gfpS_of_segWS h0W, fun _ h => le_gfpS h,
    segInvS_mono_xa segInvS_gfpS (fun fs => msOfA_with_xa fs) fun fs _ _ _ _ _ h => ?_⟩
  refine msOfA_xa_mono (fun _ _ _ _ _ hI => ?_) fs h
  rcases hI with ⟨-, -, hF⟩ | h1
  · exact hF.elim
  · exact .inr h1

/-- **Both invariants**: `exists_inv1`, then `exists_inv0` at the chosen
`inv1` (`inv0` the greatest closed invariant inside `W0` there); the
pre-allocation level may use that each post-allocation start is in `inv1`
(as its `xa`, through `xa_of_land`, needs). -/
theorem exists_invs {W0 P0 : FragS isaLSE2} {W1 P1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h1W : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegWS (W1 l b n) K p (upd hello1Λ.static l b)
        (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n))
        (P1 l b n) (fun _ _ _ => False))
    (h0W : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2,
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1 l b n s c fs → inv1 l b n s c fs) →
      SegWS W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) P0
        (fun _ _ _ => False)) :
    ∃ (inv0 : FragS isaLSE2) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2),
      (∀ s c fs, P0 s c fs → inv0 s c fs) ∧
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1 l b n s c fs → inv1 l b n s c fs) ∧
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        SegInvS (W1 l b n) K p (upd hello1Λ.static l b)
          (msOfA hello1Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n))
          (inv1 l b n)) ∧
      (∀ inv, SegInvS W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) inv →
        ∀ s c fs, inv s c fs → inv0 s c fs) ∧
      SegInvS W0 K p hello1Λ.static
        (msOfA hello1Λ μ rd G own ar (Ih lsize inv0 inv1) hello1Λ.static lsize) inv0 := by
  obtain ⟨inv1, hP1, h1⟩ := exists_inv1 h1W
  obtain ⟨inv0, hP0, hmax, h0⟩ := exists_inv0 (h0W inv1 hP1)
  exact ⟨inv0, inv1, hP0, hP1, h1, hmax, h0⟩

end Invs

/-! ## Correctness from the levels -/

open Spike.Lib.A64.Flow.Hello1.Inst in
open Spike.Test.A64Hello1Load in
/-- **`hello1.w` is correct on AArch64 from its two closed levels**
(`hello1_correctKLS` at `exists_invs`'s `inv0`, `inv1`): `hst` is the loaded
thread at the pre-allocation level's start `P0` at `setupTerm`'s pair. The
per-pair facts, the abort phase and the source safety are at the chosen
invariants, each of which contains its level's start; `inv0` contains
every explicit-invariant segment inside `W0` (the pre-allocation level's
`SFactsA` is asked at its pairs only). -/
theorem hello1_correctKLS_levels {p : Prog} {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)}
    {lsize : Lsize} {rS : Range} {W0 P0 : FragS isaLSE2} {W1 P1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {meW : TermRun.Word}
    (h1W : ∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
      SegWS (W1 l b n) (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p (upd hello1Λ.static l b)
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (fun _ _ _ _ _ => False) (upd hello1Λ.static l b) (updN lsize l n))
        (P1 l b n) (fun _ _ _ => False))
    (h0W : ∀ inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2,
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1 l b n s c fs → inv1 l b n s c fs) →
      SegWS W0 (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) P0 (fun _ _ _ => False))
    (hst : P0 (threadAt Entry.linux hello1Λ.code.lo hello1Prog (loadSyms hello1Λ hello1Secs.rodata))
      ⟨Scc.Sem.SrcSem.setupTerm, [("me", .ptr .pub .void, [meW]), ("u", .unit, [])], none⟩ []) :
    ∃ (inv0 : FragS isaLSE2) (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2),
      (∀ s c fs, P0 s c fs → inv0 s c fs) ∧
      (∀ l b n, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n →
        ∀ s c fs, P1 l b n s c fs → inv1 l b n s c fs) ∧
      (∀ inv, SegInvS W0 (TakeK (labT Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS) p hello1Λ.static
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize (fun _ _ _ => False) inv1) hello1Λ.static lsize) inv →
        ∀ s c fs, inv s c fs → inv0 s c fs) ∧
      ∀ (P : SrcSem.SrcParams) (B : Budget) (Dt Ab : State → Prop), B.cells = ar.cells →
        textProgram hello1Asm = .ok hello1Prog → dataSections hello1Asm = some hello1Secs →
        (∀ a w, (a, w) ∈ Fix → a < 2 ^ 64 ∧ ¬ hello1Λ.heap.contains a ∧ ¬ hello1Λ.data.contains a) →
        P.hooks = SrcSem.SrcHooks.none → P.init (Scc.Sem.SrcSem.setupStart P.cap meW) →
        (∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW) →
        (∀ w, rd w) →
        (∀ s c fs, inv0 s c fs → W0 s c fs →
          SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
            (Ih lsize inv0 inv1) hello1Λ.static lsize s c fs Dt Ab) →
        (∀ l b n s c fs, hello1Λ.static l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
          SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
            (Ih lsize inv0 inv1) (upd hello1Λ.static l b) (updN lsize l n) s c fs Dt Ab) →
        ¬ Ab (threadAt Entry.linux hello1Λ.code.lo hello1Prog (loadSyms hello1Λ hello1Secs.rodata)) →
        SrcSafeS P p (Ih lsize inv0 inv1) →
        Correct T (SrcSem.source P p) hello1Λ B hello1Asm := by
  obtain ⟨inv0, inv1, hP0, hP1, h1, hmax, h0⟩ := exists_invs h1W h0W
  exact ⟨inv0, inv1, hP0, hP1, hmax, fun P B Dt Ab hB hpa hd hFix hP hinit hinitC hrd hW0 hW1 hab0 hsafe =>
    Spike.Test.A64Hello1CorrectA.hello1_correctKLS (P := P) (B := B) (Dt := Dt) (Ab := Ab) hB hpa hd
      (hP0 _ _ _ hst) hFix hP hinit hinitC hrd h1 h0 hW0 hW1 hab0 hsafe⟩

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1LevelsA.segInvS_mono_xa' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms segInvS_mono_xa

/--
info: 'Spike.Test.A64Hello1LevelsA.xa_of_land' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms xa_of_land

/--
info: 'Spike.Test.A64Hello1LevelsA.exists_inv1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_inv1

/--
info: 'Spike.Test.A64Hello1LevelsA.exists_inv0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_inv0

/--
info: 'Spike.Test.A64Hello1LevelsA.exists_invs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_invs

/--
info: 'Spike.Test.A64Hello1LevelsA.hello1_correctKLS_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hello1_correctKLS_levels

end Spike.Test.A64Hello1LevelsA
