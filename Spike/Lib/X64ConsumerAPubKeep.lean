/-
**The source's publication alone keeps the arena consumer's relation**
(x86-64; no AArch64 twin): from `PreJAH` over a fragment `J` whose every
control admits the source's publication (`PubStep .st`) into a fragment
`J'`, the source takes its publication step (`src_publish_stepS`) and lands
in `PreJAH` over `J'` at the same target configuration. The publication
changes the source thread's views only (`fenceS _ .st`); `PreJAH` reads no
source view, so every other clause carries over: the hold is none at a
publication (`pubStep_landing`), the allocation invariant is retargeted
(`AllocInvAt.idle_of_term`, `AllocInvAt.retarget`), the heap use, the fresh
labels and the reach are kept (`HeapPres.heapUse_set`, `freshInv_one`,
`reach_run`).

- `preJAH_pub`, `preJA_pub`: the step from `PreJAH` / `PreJA`.
- `rsaAH_pub`, `rsaA_pub`: lifted to `RSAH` / `RSA` (after the exit the
  source does not move: `PostSAH` is kept by the empty run).

Where x86-64 differs from AArch64: on AArch64 hello's publication rides a
`dmb ishst` fence row (`Out.fence`, `FenceRun.pub`). x86-64 hello's
`wc_rodata` has no fence, and its two stores come before `wc_main`'s
`mfence`, so the publication is taken where the target does not fence (a
source stutter step, used by `Spike/Lib/X64SegPub.lean`); this module is the
consumer-side half of that step and is ISA-row-agnostic.
-/
import Spike.Lib.X64ConsumerAH
import Spike.Lib.X64ConsumerAPub

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS}
  {μ : Marks} {ar : Arena}

/-- **The source's publication from `PreJAH`**: where every control of `J`
admits the publication (`PubStep .st`) into `J'`, at the same stack, the
landing off `ret` at depth 0, the source publishes (one step of thread 0, no
event) and lands in `PreJAH` over `J'` at the same target configuration. -/
theorem preJAH_pub (hP : HookOK P p) {J J' : InvS} {H : State → List (Nat × Range) → Prop}
    (hJ : ∀ lbl lsize st c fs, J lbl lsize st c fs →
      ∃ c₁, PubStep .st c c₁ ∧ J' lbl lsize st c₁ fs ∧ (fs = [] → ∀ a, c₁.term ≠ .ret a))
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreJAH Λ P p G own J H μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreJAH Λ P p G own J' H μ ar t s' := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, hk, hz, hH, hwr, hc, hs0, hσ, hp, hJ0, -, hw, hb,
    hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  obtain ⟨c₁, hps, hJ1, hnr⟩ := hJ _ _ _ _ _ hJ0
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  obtain ⟨th', hstep, hte, hen, hp', hσ', hsk, hna, htl⟩ :=
    src_publish_stepS (p := p) (c := s) (th := th0) hP h0 hp hps rfl rfl hnr
  obtain ⟨-, hc1⟩ := pubStep_landing hps
  have hs2 : ({ s with ths := s.ths.set! 0 th' } : TermRun.Cfg).ths = #[th'] := by simp [hs0]
  have hheap : heapUse ({ s with ths := s.ths.set! 0 th' } : TermRun.Cfg) = heapUse s :=
    Spike.Lib.HeapPres.heapUse_set h0 rfl rfl hna htl
  refine ⟨_, run_one hstep, th, th', j, lbl, lsize, ts, hl, pm, none, hth, hk, hz, hH, hwr, hc, hs2,
    hσ'.trans hσ, hp', ?_, .inl trivial, hw, hb, hinv, hown, hmi, hfi, hgi, ?_, ?_,
    freshInv_one hs0 hs2 rfl rfl hna hfr, hco, _, reach_run hreach (run_one hstep)⟩
  · rw [hte, hen, hsk, ← hc1]; exact hJ1
  · rw [hsk]; exact hoo
  · rw [hheap]
    exact hai.retarget (hai.idle_of_term (pubStep_notAlloc hps)) fun w h => by cases h

/-- `preJAH_pub` at `HeldOk` (`PreJA_eq`). -/
theorem preJA_pub (hP : HookOK P p) {J J' : InvS} {rS : Range} {Tk : State → Prop}
    (hJ : ∀ lbl lsize st c fs, J lbl lsize st c fs →
      ∃ c₁, PubStep .st c c₁ ∧ J' lbl lsize st c₁ fs ∧ (fs = [] → ∀ a, c₁.term ≠ .ret a))
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : PreJA Λ P p G own J rS Tk μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreJA Λ P p G own J' rS Tk μ ar t s' :=
  preJAH_pub hP hJ h

/-- **The source's publication in `RSAH`**: before the exit by
`preJAH_pub`; after it the source does not move. -/
theorem rsaAH_pub (hP : HookOK P p) {J J' : InvS} {H : State → List (Nat × Range) → Prop}
    (hJ : ∀ lbl lsize st c fs, J lbl lsize st c fs →
      ∃ c₁, PubStep .st c c₁ ∧ J' lbl lsize st c₁ fs ∧ (fs = [] → ∀ a, c₁.term ≠ .ret a))
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSAH Λ P p G own J H μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ RSAH Λ P p G own J' H μ ar t s' := by
  rcases h with h | h
  · obtain ⟨s', hr, h'⟩ := preJAH_pub hP hJ h
    exact ⟨s', hr, .inl h'⟩
  · exact ⟨s, .refl _, .inr h⟩

/-- `rsaAH_pub` at `HeldOk` (`RSA_eq`). -/
theorem rsaA_pub (hP : HookOK P p) {J J' : InvS} {rS : Range} {Tk : State → Prop}
    (hJ : ∀ lbl lsize st c fs, J lbl lsize st c fs →
      ∃ c₁, PubStep .st c c₁ ∧ J' lbl lsize st c₁ fs ∧ (fs = [] → ∀ a, c₁.term ≠ .ret a))
    {t : T.M.Cfg} {s : TermRun.Cfg} (h : RSA Λ P p G own J rS Tk μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ RSA Λ P p G own J' rS Tk μ ar t s' :=
  rsaAH_pub hP hJ h

/-! ## Inhabitation

The fragment hypothesis `hJ` of `preJAH_pub` is met by a concrete pair of
fragments: `J` the controls at `let s = publish b in let y = publish s in
ret y` with `b : ptr own unit`, `J'` the controls just past the first
publication. (A whole `PreJAH` instance needs a target run; this exhibits
only the source-side hypothesis, the part this module adds.) -/

/-- The control at the publication. -/
def pubC : Ctl :=
  ⟨.let_ "s" (.publish (.var "b")) (.let_ "y" (.publish (.var "s")) (.ret (.var "y"))),
    [("b", .ptr .own .unit, [])], none⟩

/-- The control past it. -/
def pubC₁ : Ctl :=
  ⟨.let_ "y" (.publish (.var "s")) (.ret (.var "y")),
    [("s", .ptr .pub .unit, []), ("b", .ptr .own .unit, [])], none⟩

example : PubStep .st pubC pubC₁ :=
  ⟨.inl rfl, rfl, "s", .var "b", _, _, _, [], .inl ⟨rfl, rfl⟩, rfl, rfl⟩

/-- The fragment at the publication. -/
def pubJ : InvS := fun _ _ _ c _ => c = pubC

/-- The fragment past it. -/
def pubJ₁ : InvS := fun _ _ _ c _ => c = pubC₁

/-- `preJAH_pub`'s fragment hypothesis at `pubJ`, `pubJ₁`. -/
example : ∀ lbl lsize st c fs, pubJ lbl lsize st c fs →
    ∃ c₁, PubStep .st c c₁ ∧ pubJ₁ lbl lsize st c₁ fs ∧ (fs = [] → ∀ a, c₁.term ≠ .ret a) := by
  rintro _ _ _ c _ rfl
  exact ⟨pubC₁, ⟨.inl rfl, rfl, "s", .var "b", _, _, _, [], .inl ⟨rfl, rfl⟩, rfl, rfl⟩, rfl,
    fun _ a h => by cases h⟩

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.preJAH_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.preJAH_pub

/-- info: 'Spike.Lib.X64ConsumerA.preJA_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.preJA_pub

/-- info: 'Spike.Lib.X64ConsumerA.rsaAH_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.rsaAH_pub

/-- info: 'Spike.Lib.X64ConsumerA.rsaA_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.rsaA_pub
