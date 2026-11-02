/-
**The allocation-capable consumer's obligations from three segment levels**
(x86-64; the twin of `Spike/Lib/A64SegInstA3.lean`, generic):
`inst_of_segWA2CH` (`Spike/Lib/X64SFactsACH.lean`) for a program that
allocates twice before its outside moves end (hello.w: rodata's buffer, then
main's box), over the fragment of two allocations `I3`. No program fact
appears here.

- `inst_of_fragCH`: the obligations (`NodesA … Cl`, `TakeSiteS`,
  `AbortPathSC`, `WrInS`, `ClonePathS`) over any fragment `I` whose pairs
  carry `SFactsACH` (`hF`), whose outside moves land in it (`hK`) and whose
  rows off them land in it under `msOfA … I` (`hOut`, `OutSP`: a row may
  start after the source's publication into `I`, `NodesA.out`'s `PubOut`):
  the part of `inst_of_segWA2CH`'s proof after those three facts.
- `I3 ar L0 ls0 inv0 inv1 inv2`: before the first allocation at `L0`, `ls0`
  (`inv0`); after it, a fresh `l` at `b` with `n` words where the arena
  lands it (`inv1 l b n`, at `upd L0 l b`); after the second, a label `l'`
  fresh there at `b'` with `n'` words (`inv2 l b n l' b' n'`, at
  `upd (upd L0 l b) l' b'`).
- `inst_of_segWA3CH`: from the three levels' segments, `h0` and `h1` with
  the allocation fragment `I3` (each may allocate, landing in the next
  level), `h2` with none (each a `SegInvSP`, `Spike/Lib/X64SegWPub.lean`;
  a `SegInvS` gives one by `SegInvS.toP`), and their `SFactsACH`;
  `inst_of_segWA3CH2`: with
  `HeldPathS … (HeldOk2 Λ r0 r1)` from the take-site split.
- `land_I3a`, `land_I3b`: an allocation's landing in `h0`'s and `h1`'s
  memory side (`msOfA`'s `xa`) is in `I3` at the next level.

**Where this differs from AArch64**: the machine is x86-64's (`isa`,
`Scc.Sem.X64`, `Scc.Cert.WideX64`, the `X64Consumer*` namespaces), and the
take site's cell is a sized `nop` (`SFactsSt2.site` gives its size; the step
is `Lower.X64.exec_nop`), and the rows are `OutSP` rows (`SegInvSP` levels):
x86-64 has no fence instruction to carry the source's publication, which is
taken as a stutter before the next row. The statements and proofs are
otherwise the same.
-/
import Spike.Lib.X64SFactsACH
import Spike.Lib.X64SegWPub

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64SegWPub (OutSP SegInvSP out_or_pub)

variable {p : Prog}

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ar : Arena} {Dt Ab Cl Ac : State → Prop}

/-! ## Over any fragment -/

/-- **The consumer's obligations over a fragment** `I` whose pairs carry
`SFactsACH` (`hF`), whose outside moves (`TakeCKS a Cl`) land in it
(`hK`), and whose rows off them land in it under `msOfA … I` (`hOut`). -/
theorem inst_of_fragCH {I : InvS} {a : Int64}
    (hF : ∀ lbl lsize s c fs, I lbl lsize s c fs →
      SFactsACH Λ μ p rd G own ar I lbl lsize s c fs Dt Ab Cl Ac)
    (hK : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ s', TakeCKS a Cl s s' →
      ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧ I lbl lsize s' c' fs')
    (hOut : ∀ lbl lsize s c fs, I lbl lsize s c fs → (∀ s', ¬ TakeCKS a Cl s s') →
      OutSP p lbl (msOfA Λ μ rd G own ar I lbl lsize) (I lbl lsize) (Pend p (I lbl lsize)) s c fs)
    (hμ : μ.site .take = some a.toBitVec.toNat) :
    NodesA Λ p μ rd G own ar I none Cl ∧ TakeSiteS p μ I ∧
      AbortPathSC μ I Cl Ab Ac ar.cells ar.ctr ∧ WrInS I Dt ∧ ClonePathS p I Cl := by
  have hR : ∀ lbl lsize s c fs, IRun p I lbl lsize s c fs →
      ∃ c₀ fs₀, SFactsACH Λ μ p rd G own ar I lbl lsize s c₀ fs₀ Dt Ab Cl Ac ∧
        FrameRun p (c₀, fs₀) (c, fs) := by
    rintro lbl lsize s c fs ⟨c₀, fs₀, hi, hr⟩
    exact ⟨c₀, fs₀, hF _ _ _ _ _ hi, hr⟩
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  -- no outside move off the take site and off `Cl`
  have hnk : ∀ lbl lsize s c fs, I lbl lsize s c fs → pcOf s ≠ a.toBitVec.toNat → ¬ Cl s →
      ∀ s', ¬ TakeCKS a Cl s s' := by
    rintro lbl lsize s c fs - hpc hcl s' (hk | ⟨hc, -⟩)
    · exact hpc (pcOf_eq_iff.mpr hk.1)
    · exact hcl hc
  -- an `Out` row at every fragment state off a system call (the take site's `nop`)
  have hRow : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = false →
      ∃ (c₁ : Ctl) (ms' : MemSide isa) (Y : Frag isa), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ := by
    intro lbl lsize s c fs hi hns
    have hdone : ∀ s', isa.exec s = some (.done s') →
        ∃ (c₁ : Ctl) (ms' : MemSide isa) (Y : Frag isa), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ :=
      fun s' he => ⟨c, msOfA Λ μ rd G own ar I lbl lsize fs, fun _ _ => True, rfl,
        .silent s' c he (.refl c) trivial⟩
    by_cases hpc : pcOf s = a.toBitVec.toNat
    · obtain ⟨⟨_, sz, hcn⟩, -⟩ := (hF lbl lsize s c fs hi).site _ hμ hpc
      exact hdone _ (Kraken.Promising.Lower.X64.exec_nop hcn)
    · have hcl : ¬ Cl s := fun hc => by
        have := ((hF lbl lsize s c fs hi).clSvc hc).1
        rw [hns] at this; cases this
      have hrow : ∀ c₀, OutS p lbl (msOfA Λ μ rd G own ar I lbl lsize) (Pend p (I lbl lsize)) s c₀ fs →
          ∃ (c₁ : Ctl) (ms' : MemSide isa) (Y : Frag isa), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ := by
        intro c₀ h
        cases h with
        | pre c₁ fs₁ _ h => exact ⟨c₁, _, _, rfl, h⟩
        | frame s' _ _ he _ _ => exact hdone s' he
      rcases hOut lbl lsize s c fs hi (hnk lbl lsize s c fs hi hpc hcl) with h | ⟨-, -, c₁, -, -, h⟩
      · exact hrow c h
      · exact hrow c₁ h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).wrTail, ?_, ?_⟩
  -- `NodesA`
  · intro lbl lsize s c fs hi hoff hncl
    refine out_or_pub (fun _ _ _ h => h) id
      (hOut lbl lsize s c fs hi (hnk lbl lsize s c fs hi (fun hpc => hoff _ hμ hpc) fun hc => ?_))
    exact hncl ((hF lbl lsize s c fs hi).clSvc hc).1 hc
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
    obtain ⟨c₁, ms', Y, hK', hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀ hns
    rcases out_eff hout hK' hns hst hstep ho with ⟨hm, hp⟩ | ⟨L, hL, he⟩
    · exact absurd hW (not_writes_of_same hm hp)
    · rw [← loc_of_writes he hW] at hL
      exact (hF _ _ _ _ _ hi₀).wr c fs hr hns hL
  · intro lbl lsize s c fs hi hns t mem outs o L hst hstep ho hW
    obtain ⟨c₀, fs₀, hi₀, hr⟩ := hi
    obtain ⟨c₁, ms', Y, hK', hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀ hns
    rcases out_eff hout hK' hns hst hstep ho with ⟨hm, hp⟩ | ⟨L', hL, he⟩
    · exact absurd hW (not_writes_of_same hm hp)
    · rw [← loc_of_writes he hW] at hL
      exact (hF _ _ _ _ _ hi₀).arena c fs hr hns L hL
  · intro lbl lsize s c fs hi x a' τ e ht
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact zero_of_zeroOkTy (hf.zero c fs hr x a' τ e ht)
  -- `TakeSiteS`
  · intro lbl lsize s c fs hi a' ha' hpc
    obtain ⟨h2, h3⟩ := (hF lbl lsize s c fs hi).site a' ha' hpc
    refine ⟨h2, h3, fun pm => ?_⟩
    have hk : TakeKS a s (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) (Kernel.siteRange abi s)))) :=
      ⟨pcOf_eq_iff.mp (hsite ha' ▸ hpc), pm, rfl⟩
    exact hK lbl lsize s c fs hi _ (.inl hk)
  -- `AbortPathSC` at the phases `Ab`, `Ac`
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abortOk
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abInstr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).abTake
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).acSt.acInstr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).acSt.acSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).acSt.acTake
  -- `ClonePathS`
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).clSvc
  · intro lbl lsize s c fs hi hcl r hr
    exact hK lbl lsize s c fs hi _ (.inr ⟨hcl, r, hr, rfl⟩)

/-! ## The fragment of two allocations -/

/-- **The fragment of two allocations**: before the first at `L0`, `ls0`
(`inv0`); after it, for a fresh `l` placed at `b` with `n` words where the
arena lands it (`inv1 l b n`); after the second, for a label `l'` fresh
there placed at `b'` with `n'` words (`inv2 l b n l' b' n'`). -/
def I3 (ar : Arena) (L0 : Lbl) (ls0 : Lsize) (inv0 : FragS isa)
    (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
    (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa) : InvS :=
  fun lbl lsize s c fs =>
    (lbl = L0 ∧ lsize = ls0 ∧ inv0 s c fs) ∨
    (∃ l b n, L0 l = none ∧ AllocLand ar.heap ar.cells b n ∧ lbl = upd L0 l b ∧ lsize = updN ls0 l n ∧
      inv1 l b n s c fs) ∨
    ∃ l b n l' b' n', L0 l = none ∧ AllocLand ar.heap ar.cells b n ∧ upd L0 l b l' = none ∧
      AllocLand ar.heap ar.cells b' n' ∧ lbl = upd (upd L0 l b) l' b' ∧
      lsize = updN (updN ls0 l n) l' n' ∧ inv2 l b n l' b' n' s c fs

section I3

variable {L0 : Lbl} {ls0 : Lsize} {a : Int64}
  {W0 inv0 : FragS isa} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {W2 inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

/-- **The first allocation's landing is in `I3`** at the extended
placement (`h0`'s `msOfA` `xa`). -/
theorem land_I3a {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hi : inv1 l b n s c fs) :
    I3 ar L0 ls0 inv0 inv1 inv2 (upd L0 l b) (updN ls0 l n) s c fs :=
  .inr (.inl ⟨l, b, n, hl, hb, rfl, rfl, hi⟩)

/-- **The second allocation's landing is in `I3`** at the twice extended
placement (`h1`'s `msOfA` `xa`). -/
theorem land_I3b {l l' : WeakMem.AllocLabel} {b n b' n' : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hl : L0 l = none) (hb : AllocLand ar.heap ar.cells b n) (hl' : upd L0 l b l' = none)
    (hb' : AllocLand ar.heap ar.cells b' n') (hi : inv2 l b n l' b' n' s c fs) :
    I3 ar L0 ls0 inv0 inv1 inv2 (upd (upd L0 l b) l' b') (updN (updN ls0 l n) l' n') s c fs :=
  .inr (.inr ⟨l, b, n, l', b', n', hl, hb, hl', hb', rfl, rfl, hi⟩)

/-- **The consumer's obligations from three segment levels with a `clone`
refusal, over a held predicate**: every pair of each level carrying
`SFactsACH` at its placement over `I3`; `h0`, `h1` under the allocation
fragment `I3`, `h2` under none. -/
theorem inst_of_segWA3CH
    (h2 : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n → upd L0 l b l' = none →
      AllocLand ar.heap ar.cells b' n' →
      SegInvSP (W2 l b n l' b' n') (TakeCKS a Cl) p (upd (upd L0 l b) l' b')
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd (upd L0 l b) l' b') (updN (updN ls0 l n) l' n'))
        (inv2 l b n l' b' n'))
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvSP (W1 l b n) (TakeCKS a Cl) p (upd L0 l b)
        (msOfA Λ μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (upd L0 l b) (updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvSP W0 (TakeCKS a Cl) p L0 (msOfA Λ μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) L0 ls0) inv0)
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsACH Λ μ p rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsACH Λ μ p rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (upd L0 l b) (updN ls0 l n) s c fs Dt Ab Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → upd L0 l b l' = none →
      AllocLand ar.heap ar.cells b' n' → W2 l b n l' b' n' s c fs →
      SFactsACH Λ μ p rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (upd (upd L0 l b) l' b')
        (updN (updN ls0 l n) l' n') s c fs Dt Ab Cl Ac) :
    NodesA Λ p μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) none Cl ∧ TakeSiteS p μ (I3 ar L0 ls0 inv0 inv1 inv2) ∧
      AbortPathSC μ (I3 ar L0 ls0 inv0 inv1 inv2) Cl Ab Ac ar.cells ar.ctr ∧
      WrInS (I3 ar L0 ls0 inv0 inv1 inv2) Dt ∧ ClonePathS p (I3 ar L0 ls0 inv0 inv1 inv2) Cl := by
  refine inst_of_fragCH ?_ ?_ ?_ hμ
  · rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩ |
      ⟨l, b, n, l', b', n', hl, hland, hl', hland', rfl, rfl, hi⟩)
    · exact hW0 s c fs hi (h0 s c fs hi).1
    · exact hW1 l b n s c fs hl hland (h1 l b n hl hland s c fs hi).1
    · exact hW2 l b n l' b' n' s c fs hl hland hl' hland' (h2 l b n l' b' n' hl hland hl' hland' s c fs hi).1
  · rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩ |
      ⟨l, b, n, l', b', n', hl, hland, hl', hland', rfl, rfl, hi⟩) s' hk
    · obtain ⟨c', fs', hr, hi'⟩ := (h0 s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inl ⟨rfl, rfl, hi'⟩⟩
    · obtain ⟨c', fs', hr, hi'⟩ := (h1 l b n hl hland s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, land_I3a hl hland hi'⟩
    · obtain ⟨c', fs', hr, hi'⟩ := (h2 l b n l' b' n' hl hland hl' hland' s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, land_I3b hl hland hl' hland' hi'⟩
  · rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩ |
      ⟨l, b, n, l', b', n', hl, hland, hl', hland', rfl, rfl, hi⟩) hk
    · exact ((h0 s c fs hi).2.1 hk).mono (fun _ _ _ h => .inl ⟨rfl, rfl, h⟩)
        fun _ _ _ h => h.mono fun _ _ _ h => .inl ⟨rfl, rfl, h⟩
    · exact ((h1 l b n hl hland s c fs hi).2.1 hk).mono (fun _ _ _ h => land_I3a hl hland h)
        fun _ _ _ h => h.mono fun _ _ _ h => land_I3a hl hland h
    · refine (Spike.Lib.X64SegWPub.OutSP.mono_xa ((h2 l b n l' b' n' hl hland hl' hland' s c fs hi).2.1 hk)
        (fun _ => rfl) fun _ _ _ _ _ _ h => h.2.elim).mono (fun _ _ _ h => land_I3b hl hland hl' hland' h)
        fun _ _ _ h => h.mono fun _ _ _ h => land_I3b hl hland hl' hland' h

/-- **The obligations at the two-range held predicate** (`inst_of_segWA3CH`
with `heldPathS_ok2`). -/
theorem inst_of_segWA3CH2
    (h2 : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n → upd L0 l b l' = none →
      AllocLand ar.heap ar.cells b' n' →
      SegInvSP (W2 l b n l' b' n') (TakeCKS a Cl) p (upd (upd L0 l b) l' b')
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd (upd L0 l b) l' b') (updN (updN ls0 l n) l' n'))
        (inv2 l b n l' b' n'))
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvSP (W1 l b n) (TakeCKS a Cl) p (upd L0 l b)
        (msOfA Λ μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (upd L0 l b) (updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvSP W0 (TakeCKS a Cl) p L0 (msOfA Λ μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) L0 ls0) inv0)
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsACH Λ μ p rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsACH Λ μ p rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (upd L0 l b) (updN ls0 l n) s c fs Dt Ab Cl Ac)
    (hW2 : ∀ l b n l' b' n' s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → upd L0 l b l' = none →
      AllocLand ar.heap ar.cells b' n' → W2 l b n l' b' n' s c fs →
      SFactsACH Λ μ p rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) (upd (upd L0 l b) l' b')
        (updN (updN ls0 l n) l' n') s c fs Dt Ab Cl Ac)
    {r0 r1 : Range}
    (hsplit : ∀ lbl lsize s c fs hl, I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize s c fs → HeldOk2 Λ r0 r1 s hl →
      ∀ a, μ.site .take = some a → pcOf s = a →
        (hl = [] ∧ Kernel.siteRange abi s = r0) ∨ (hl = [(0, r0)] ∧ Kernel.siteRange abi s = r1))
    (hs0 : r0.Sub Λ.stackPool) (hs1 : r1.Sub Λ.stackPool) (hz0 : 0 < r0.size) (hz1 : 0 < r1.size)
    (hro : Λ.rodata.Disjoint Λ.stackPool) (hd : r1.Disjoint r0)
    (hw0 : r0.lo + r0.size ≤ 2 ^ 64) (hw1 : r1.lo + r1.size ≤ 2 ^ 64) :
    NodesA Λ p μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) none Cl ∧
      HeldPathS Λ p μ (I3 ar L0 ls0 inv0 inv1 inv2) (HeldOk2 Λ r0 r1) ∧
      AbortPathSC μ (I3 ar L0 ls0 inv0 inv1 inv2) Cl Ab Ac ar.cells ar.ctr ∧
      WrInS (I3 ar L0 ls0 inv0 inv1 inv2) Dt ∧ ClonePathS p (I3 ar L0 ls0 inv0 inv1 inv2) Cl := by
  obtain ⟨hN, hts, hA, hWr, hC⟩ := inst_of_segWA3CH h2 h1 h0 hμ hW0 hW1 hW2
  exact ⟨hN, heldPathS_ok2 hts hsplit hs0 hs1 hz0 hz1 hro hd hw0 hw1, hA, hWr, hC⟩

end I3

/-- info: 'Spike.Lib.X64ConsumerA.inst_of_fragCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inst_of_fragCH

/-- info: 'Spike.Lib.X64ConsumerA.inst_of_segWA3CH2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inst_of_segWA3CH2

end Spike.Lib.X64ConsumerA
