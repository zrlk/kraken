/-
**The allocation-capable consumer's obligations from segments at every
reachable placement** on the canonical AArch64 target (`inst_of_segWA2`,
`Spike/Lib/A64SegInstA.lean`, for any number of allocations): a program
has a segment at every placement reachable from the labels' placement
`L0`, `ls0` by allocations (`AllocReach.Reach`), each with its invariant
explicit (`SegInvS`) and its rows under the memory side over the
multi-level fragment `AllocReach.IN` (with or without the output's byte
step: `msOfAX … ab`). An allocation row lands in `IN` at the next placement,
so no level needs its allocation fragment widened (`OutS.mono_xa`). With
every pair of every level carrying `SFactsA`, `IN` is the fragment `I` of
`correctKA`/`correctKOnAE` with `NodesA … ab`, `TakePathS` and
`AbortPathS` at any abort phase `Ab`.

- `inst_of_segWAN`: the obligations, as in `inst_of_segWA2` with its two
  levels one.
-/
import Spike.Lib.A64SegInstA
import Spike.Lib.AllocReach

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow.Ret0 (TakeK TakeK.pc)
open Spike.Lib.AllocReach (Reach IN)

variable {p : Prog}

/-- **`NodesA`, `TakePathS`, `AbortPathS` and `WrInS` from a segment at
every reachable placement** (`inst_of_segWA2` with any number of
allocations): the fragment `IN ar L0 ls0 inv`, each level `inv L ls` a
segment inside `W L ls` closed under the take (`hseg`) under the memory side
over `IN` at its placement, every pair of every level carrying `SFactsA`
(`hW`). -/
theorem inst_of_segWAN {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64}
    {W inv : Lbl → Lsize → FragS isaLSE2} {Dt Ab : State → Prop} {ab : Option (State → Prop)}
    (hseg : ∀ L ls, Reach ar L0 ls0 L ls →
      SegInvS (W L ls) (TakeK a rS) p L (msOfAX Λ μ p rd G own ar (IN ar L0 ls0 inv) ab L ls) (inv L ls))
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW : ∀ L ls s c fs, Reach ar L0 ls0 L ls → inv L ls s c fs → W L ls s c fs →
      SFactsA Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) L ls s c fs Dt Ab) :
    NodesA Λ p μ rd G own ar (IN ar L0 ls0 inv) ab ∧ TakePathS Λ p μ (IN ar L0 ls0 inv) rS Tk ∧
      AbortPathS μ (IN ar L0 ls0 inv) Ab ar.cells ar.ctr ∧ WrInS (IN ar L0 ls0 inv) Dt := by
  have hF : ∀ lbl lsize s c fs, IN ar L0 ls0 inv lbl lsize s c fs →
      SFactsA Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) lbl lsize s c fs Dt Ab :=
    fun lbl lsize s c fs ⟨hR, hi⟩ => hW lbl lsize s c fs hR hi (hseg lbl lsize hR s c fs hi).1
  have hR : ∀ lbl lsize s c fs, IRun p (IN ar L0 ls0 inv) lbl lsize s c fs →
      ∃ c₀ fs₀, SFactsA Λ μ p rd G own rS Tk ar (IN ar L0 ls0 inv) lbl lsize s c₀ fs₀ Dt Ab ∧
        FrameRun p (c₀, fs₀) (c, fs) := by
    rintro lbl lsize s c fs ⟨c₀, fs₀, hi, hr⟩
    exact ⟨c₀, fs₀, hF _ _ _ _ _ hi, hr⟩
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  -- every level's rows off the take site, under the memory side over `IN`
  have hOut : ∀ lbl lsize s c fs, IN ar L0 ls0 inv lbl lsize s c fs → (∀ s', ¬ TakeK a rS s s') →
      OutS p lbl (msOfAX Λ μ p rd G own ar (IN ar L0 ls0 inv) ab lbl lsize)
        (Pend p (IN ar L0 ls0 inv lbl lsize)) s c fs := by
    rintro lbl lsize s c fs ⟨hRe, hi⟩ hk
    exact ((hseg lbl lsize hRe s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ h => ⟨hRe, h⟩
  -- an `Out` row at every fragment state off a system call (the take site's `nop`)
  have hRow : ∀ lbl lsize s c fs, IN ar L0 ls0 inv lbl lsize s c fs →
      ∃ (c₁ : Ctl) (ms' : MemSide isaLSE2) (Y : Frag isaLSE2), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ := by
    intro lbl lsize s c fs hi
    have hdone : ∀ s', isaLSE2.exec s = some (.done s') →
        ∃ (c₁ : Ctl) (ms' : MemSide isaLSE2) (Y : Frag isaLSE2), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ :=
      fun s' he => ⟨c, msOfA Λ μ rd G own ar (IN ar L0 ls0 inv) lbl lsize fs, fun _ _ => True, rfl,
        .silent s' c he (.refl c) trivial⟩
    by_cases hpc : pcOf s = a.toBitVec.toNat
    · obtain ⟨-, ⟨sz, hcn⟩, -⟩ := (hF lbl lsize s c fs hi).site _ hμ hpc
      exact hdone _ (Kraken.Promising.Lower.A64.exec_nop hcn)
    · have hk : ∀ s', ¬ TakeK a rS s s' := fun s' hk => hpc (pcOf_eq_iff.mpr (TakeK.pc hk))
      cases hOut lbl lsize s c fs hi hk with
      | pre c₁ fs₁ _ h => exact ⟨c₁, _, _, by cases ab <;> rfl, h⟩
      | frame s' _ _ he _ _ => exact hdone s' he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).wrTail⟩
  -- `NodesA`
  · intro lbl lsize s c fs hi hoff
    exact hOut lbl lsize s c fs hi fun s' hk => hoff _ hμ (pcOf_eq_iff.mpr (TakeK.pc hk))
  · exact fun lbl lsize s c hi => (hF lbl lsize s c [] hi).noRet rfl
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.cell c fs hr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).noSite
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).mapped
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).place
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).svc
  · rintro lbl lsize s c fs c' fs' hr (hi | hi)
    · exact (hF _ _ _ _ _ hi).ownRun c fs c' fs' hr (.inl ⟨rfl, rfl⟩)
    · exact (hF _ _ _ _ _ hi).ownRun c fs c' fs' hr (.inr ⟨rfl, rfl⟩)
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.ownInstr c fs hr
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.ownSys c fs hr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).ownTake
  · intro lbl lsize s c fs hi hns t mem outs o hst hstep ho hW
    obtain ⟨c₀, fs₀, hi₀, hr⟩ := hi
    obtain ⟨c₁, ms', Y, hK, hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀
    exact ((hF _ _ _ _ _ hi₀).wr c fs hr hns).ctrRow hout hK hns hst hstep ho hW
  · intro lbl lsize s c fs hi hns t mem outs o L hst hstep ho hW
    obtain ⟨c₀, fs₀, hi₀, hr⟩ := hi
    obtain ⟨c₁, ms', Y, hK, hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀
    exact ((hF _ _ _ _ _ hi₀).wr c fs hr hns).arena_of hout hK hns hst hstep ho hW
  · intro lbl lsize s c fs hi x a' τ e ht
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact zero_of_zeroOkTy (hf.zero c fs hr x a' τ e ht)
  -- `TakePathS`
  · intro lbl lsize s c fs hi a' ha' hpc
    obtain ⟨h1', h2, h3, h4, h5, h6, h7⟩ := (hF lbl lsize s c fs hi).site a' ha' hpc
    refine ⟨h1', h2, h3, h4, h5, h6, h7, fun pm => ?_⟩
    have hk : TakeK a rS s (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) :=
      ⟨pcOf_eq_iff.mp (hsite ha' ▸ hpc), pm, rfl⟩
    have htk := (hF lbl lsize s c fs hi).tkTake a' ha' hpc (Kernel.copyRange pm (abi.dmem s) rS)
    obtain ⟨hRe, hi⟩ := hi
    obtain ⟨c', fs', hr, hi'⟩ := (hseg lbl lsize hRe s c fs hi).2.2 _ hk
    exact ⟨c', fs', hr, ⟨hRe, hi'⟩, htk⟩
  · exact fun lbl lsize s c fs hi hn => (hF lbl lsize s c fs hi).tkInstr hn
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).tkSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).owned
  -- `AbortPathS` at the phase `Ab`
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abortOk
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abInstr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abTake

/--
info: 'Spike.Lib.A64ConsumerA.inst_of_segWAN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inst_of_segWAN

end Spike.Lib.A64ConsumerA
