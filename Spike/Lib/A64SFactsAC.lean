/-
**The allocation-capable consumer's obligations with a `clone` refusal**
(AArch64): `inst_of_segWA2` (`Spike/Lib/A64SegInstA.lean`) for a program
whose fragment reaches a `clone` system call, refused on the one-slot
configuration (`ClonePathS`, `Spike/Lib/A64ConsumerAStep.lean`), and whose
`threads` abort site is reached only after the refusal (`AbortPathSC`'s
phase `Ac`, `Spike/Lib/A64ConsumerACorrect.lean`).

At a state `Cl` marks the segments have no row (`Out.sys` excludes a
`clone`); the refusals are an outside move of the segments, beside the take
(`CloneErrK`, `TakeCK`), and their landing is `ClonePathS.err`.

- `CloneErrK`, `TakeCK`: the refusals' move, and it with the take's.
- `SFactsAC`: `SFactsA` with the `threads` abort case at an abort site
  (`abortOk`), the phase `Ac` kept off `Cl` (`acSt`, `AcSt`,
  `Spike/Lib/A64AcSt.lean`) and every `Cl` state at a `clone` (`clSvc`).
- `SFactsA.toC`: `SFactsA` with no `threads` case is `SFactsAC`;
  `SFactsAC.ofSt`: `SFactsA.ofSt` with the `clone` phase.
- `inst_of_segWA2C`: the obligations, `NodesA … Cl`, `TakePathS`,
  `AbortPathSC`, `WrInS` and `ClonePathS`.
-/
import Spike.Lib.A64AcSt
import Spike.Lib.HeapAbortBox

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow.Ret0 (TakeK TakeK.pc)
open Spike.Lib.HeapLand (AllocLand)

variable {p : Prog}

/-! ## The refusals' move -/

/-- **The `clone` refusals' move**: from a state `Cl` marks to the state
with either refusal returned (`-EAGAIN`, `-ENOMEM`; `ClonePathS.err`). -/
def CloneErrK (Cl : State → Prop) (s s' : State) : Prop :=
  Cl s ∧ ∃ r, (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) ∧ s' = abi.ret s r

/-- **The take of `rS` at `a` or a `clone` refusal at `Cl`**: the segments'
outside moves. -/
def TakeCK (a : Int64) (rS : Range) (Cl : State → Prop) (s s' : State) : Prop :=
  TakeK a rS s s' ∨ CloneErrK Cl s s'

/-! ## The per-pair facts -/

/-- **Per-pair facts with allocation and a `clone` refusal**: `SFactsA`'s
fields, with at an abort site also the `threads` case in the phase `Ac`
and the heap case at either allocation (`HeapAbortOblA`, a buffer's or a
box's; `abortOk`, `AbortPathSC.at_`); off `Ac`, no instruction, no take and no
system call off `Cl` enters it (`acSt`); a state `Cl` marks is at a `clone`
(`clSvc`, `ClonePathS.svc`). -/
structure SFactsAC (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (rS : Range) (Tk : State → Prop) (ar : Arena) (J : InvS) (lbl : Lbl) (lsize : Lsize) (s : State)
    (c : Ctl) (fs : List TermRun.Frame) (Dt Ab Cl Ac : State → Prop) : Prop where
  noRet : fs = [] → ∀ a, c.term ≠ .ret a
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : PlacedSE Λ lbl s c fs
  svc : abi.atSys s = true → ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  ownRun : ∀ c₁ fs₁ c₂ fs₂, FrameRun p (c₁, fs₁) (c₂, fs₂) → ((c₁ = c ∧ fs₁ = fs) ∨ (c₂ = c ∧ fs₂ = fs)) →
    own s fs₂ = own s fs₁
  ownInstr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → OwnTree (own · fs') (own s fs') tree
  ownSys : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
      own s' fs' = own s fs'
  ownTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, own (abi.skip (abi.setDmem s m)) fs = own s fs
  site : ∀ a, μ.site .take = some a → pcOf s = a →
    ¬ Tk s ∧ (∃ sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) ∧ abi.atSys s = false ∧
      Kernel.siteRange abi s = rS ∧ rS.Sub Λ.stackPool ∧ 0 < rS.size ∧ Λ.rodata.Disjoint Λ.stackPool
  tkTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, Tk (abi.skip (abi.setDmem s m))
  tkInstr : Kernel.siteAt abi μ s = none → abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)
  tkSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, (Tk s' ↔ Tk s)
  owned : Tk s → Owned Λ rS s
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s
  wr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
    WrOkA ar lbl lsize (msOfA Λ μ rd G own ar J lbl lsize fs') (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c'
  zero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true
  abortOk : ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortOblA ar.cells ar.ctr c) ∨ (k = .threads ∧ Ac s)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  abInstr : ¬ Ab s → abi.atSys s = false → ∀ tree,
    isaLSE2.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  abSys : ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  abTake : ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))
  acSt : AcSt μ Cl Ac s
  clSvc : Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl}
  {fs : List TermRun.Frame} {Dt Ab Cl Ac : State → Prop}

/-- **`SFactsA` is `SFactsAC`** with the phase's facts at the state (`AcSt`)
and every `Cl` state at a `clone` (`hcl`): no `threads` case is needed. -/
theorem SFactsA.toC (h : SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab) (hac : AcSt μ Cl Ac s)
    (hcl : Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab Cl Ac where
  noRet := h.noRet
  cell := h.cell
  noSite := h.noSite
  mapped := h.mapped
  place := h.place
  svc := h.svc
  ownRun := h.ownRun
  ownInstr := h.ownInstr
  ownSys := h.ownSys
  ownTake := h.ownTake
  site := h.site
  tkTake := h.tkTake
  tkInstr := h.tkInstr
  tkSys := h.tkSys
  owned := h.owned
  wrTail := h.wrTail
  wr := h.wr
  zero := h.zero
  abortOk k a ha hpc := by
    obtain ⟨h1, h2⟩ := h.abortOk k a ha hpc
    refine ⟨?_, h2⟩
    rcases h1 with h1 | h1 | h1
    · exact .inl h1
    · exact .inr (.inl h1)
    · exact .inr (.inr (.inl ⟨h1.1, h1.2.toA⟩))
  abInstr := h.abInstr
  abSys := h.abSys
  abTake := h.abTake
  acSt := hac
  clSvc := hcl

/-- **`SFactsAC` from the state's facts and the pair's** (`SFactsA.ofSt`
with the `clone` phase): at owned words with no frame dependence, the
state's (`SFactsSt`, `AbSt`, `AcSt`, `hcl`) and the pair's, the abort sites
with the `threads` case (`habort`). -/
theorem SFactsAC.ofSt {own : Own} (h : SFactsSt Λ μ own rS Tk s Dt) (hab : AbSt μ Ab s) (hac : AcSt μ Cl Ac s)
    (hcl : Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hcell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
      (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
      TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty)
    (hpl : PlacedSE Λ lbl s c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c')
    (hzero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
      ZeroOkTy τ = true)
    (habort : ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortOblA ar.cells ar.ctr c) ∨ (k = .threads ∧ Ac s)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    SFactsAC Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab Cl Ac where
  noRet := hnr
  cell := hcell
  noSite := h.noSite
  mapped := h.mapped
  place := hpl
  svc := h.svc
  ownRun := fun _ _ _ _ _ _ => rfl
  ownInstr := fun _ _ _ hs tree he => h.ownInstr hs tree he
  ownSys := fun _ _ _ hs call hd s' hs' => h.ownSys hs call hd s' hs'
  ownTake := h.ownTake
  site := h.site
  tkTake := h.tkTake
  tkInstr := h.tkInstr
  tkSys := h.tkSys
  owned := h.owned
  wrTail := h.wrTail
  wr := hwr
  zero := hzero
  abortOk := habort
  abInstr := hab.abInstr
  abSys := hab.abSys
  abTake := hab.abTake
  acSt := hac
  clSvc := hcl

/-! ## The obligations -/

/-- **The consumer's obligations from two segment levels with a `clone`
refusal** (`inst_of_segWA2` with the refusals an outside move beside the
take, `TakeCK`): every pair of either level carrying `SFactsAC` at its
placement over `I2` (`hW0`, `hW1`), `I2` is a fragment with `NodesA … Cl`
(the rows off the take site and off `Cl`), `TakePathS`, `AbortPathSC` at the
phases `Ab`, `Ac`, `WrInS`, and the `clone` path `ClonePathS` (a `Cl` state
at a `clone` by `clSvc`, the refusals' landing by the segments' outside
move). -/
theorem inst_of_segWA2C {L0 : Lbl} {ls0 : Lsize} {a : Int64}
    {W0 inv0 : FragS isaLSE2} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeCK a rS Cl) p (upd L0 l b)
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd L0 l b) (updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeCK a rS Cl) p L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0) inv0)
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsAC Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsAC Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) (upd L0 l b) (updN ls0 l n) s c fs Dt Ab Cl Ac) :
    NodesA Λ p μ rd G own ar (I2 ar L0 ls0 inv0 inv1) none Cl ∧ TakePathS Λ p μ (I2 ar L0 ls0 inv0 inv1) rS Tk ∧
      AbortPathSC μ (I2 ar L0 ls0 inv0 inv1) Cl Ab Ac ar.cells ar.ctr ∧ WrInS (I2 ar L0 ls0 inv0 inv1) Dt ∧
      ClonePathS p (I2 ar L0 ls0 inv0 inv1) Cl := by
  have hF : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs →
      SFactsAC Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) lbl lsize s c fs Dt Ab Cl Ac := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩)
    · exact hW0 s c fs hi (h0 s c fs hi).1
    · exact hW1 l b n s c fs hl hland (h1 l b n hl hland s c fs hi).1
  have hR : ∀ lbl lsize s c fs, IRun p (I2 ar L0 ls0 inv0 inv1) lbl lsize s c fs →
      ∃ c₀ fs₀, SFactsAC Λ μ p rd G own rS Tk ar (I2 ar L0 ls0 inv0 inv1) lbl lsize s c₀ fs₀ Dt Ab Cl Ac ∧
        FrameRun p (c₀, fs₀) (c, fs) := by
    rintro lbl lsize s c fs ⟨c₀, fs₀, hi, hr⟩
    exact ⟨c₀, fs₀, hF _ _ _ _ _ hi, hr⟩
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  -- the outside moves' landings in `I2`
  have hK : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → ∀ s', TakeCK a rS Cl s s' →
      ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧ I2 ar L0 ls0 inv0 inv1 lbl lsize s' c' fs' := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩) s' hk
    · obtain ⟨c', fs', hr, hi'⟩ := (h0 s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inl ⟨rfl, rfl, hi'⟩⟩
    · obtain ⟨c', fs', hr, hi'⟩ := (h1 l b n hl hland s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inr ⟨l, b, n, hl, hland, rfl, rfl, hi'⟩⟩
  -- either level's rows off the outside moves, under the memory side over `I2`
  have hOut : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → (∀ s', ¬ TakeCK a rS Cl s s') →
      OutS p lbl (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize)
        (Pend p (I2 ar L0 ls0 inv0 inv1 lbl lsize)) s c fs := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩) hk
    · exact ((h0 s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ h => .inl ⟨rfl, rfl, h⟩
    · refine (OutS.mono_xa ((h1 l b n hl hland s c fs hi).2.1 hk) (fun _ => rfl)
        fun _ _ _ _ _ _ h => h.2.elim).mono fun _ _ _ h => h.mono fun _ _ _ h => ?_
      exact .inr ⟨l, b, n, hl, hland, rfl, rfl, h⟩
  -- no outside move off the take site and off `Cl`
  have hnk : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → pcOf s ≠ a.toBitVec.toNat → ¬ Cl s →
      ∀ s', ¬ TakeCK a rS Cl s s' := by
    rintro lbl lsize s c fs - hpc hcl s' (hk | ⟨hc, -⟩)
    · exact hpc (pcOf_eq_iff.mpr (TakeK.pc hk))
    · exact hcl hc
  -- an `Out` row at every fragment state off a system call (the take site's `nop`)
  have hRow : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → abi.atSys s = false →
      ∃ (c₁ : Ctl) (ms' : MemSide isaLSE2) (Y : Frag isaLSE2), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ := by
    intro lbl lsize s c fs hi hns
    have hdone : ∀ s', isaLSE2.exec s = some (.done s') →
        ∃ (c₁ : Ctl) (ms' : MemSide isaLSE2) (Y : Frag isaLSE2), ms'.K = some abi ∧ Out p lbl ms' Y s c₁ :=
      fun s' he => ⟨c, msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize fs, fun _ _ => True, rfl,
        .silent s' c he (.refl c) trivial⟩
    by_cases hpc : pcOf s = a.toBitVec.toNat
    · obtain ⟨-, ⟨sz, hcn⟩, -⟩ := (hF lbl lsize s c fs hi).site _ hμ hpc
      exact hdone _ (Kraken.Promising.Lower.A64.exec_nop hcn)
    · have hcl : ¬ Cl s := fun hc => by
        have := ((hF lbl lsize s c fs hi).clSvc hc).1
        rw [hns] at this; cases this
      cases hOut lbl lsize s c fs hi (hnk lbl lsize s c fs hi hpc hcl) with
      | pre c₁ fs₁ _ h => exact ⟨c₁, _, _, rfl, h⟩
      | frame s' _ _ he _ _ => exact hdone s' he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).wrTail, ?_, ?_⟩
  -- `NodesA`
  · intro lbl lsize s c fs hi hoff hncl
    refine hOut lbl lsize s c fs hi (hnk lbl lsize s c fs hi (fun hpc => hoff _ hμ hpc) fun hc => ?_)
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
    exact ((hF _ _ _ _ _ hi₀).wr c fs hr hns).ctrRow hout hK' hns hst hstep ho hW
  · intro lbl lsize s c fs hi hns t mem outs o L hst hstep ho hW
    obtain ⟨c₀, fs₀, hi₀, hr⟩ := hi
    obtain ⟨c₁, ms', Y, hK', hout⟩ := hRow lbl lsize s c₀ fs₀ hi₀ hns
    exact .inl (((hF _ _ _ _ _ hi₀).wr c fs hr hns).arena_of hout hK' hns hst hstep ho hW)
  · intro lbl lsize s c fs hi x a' τ e ht
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact zero_of_zeroOkTy (hf.zero c fs hr x a' τ e ht)
  -- `TakePathS`
  · intro lbl lsize s c fs hi a' ha' hpc
    obtain ⟨h1', h2, h3, h4, h5, h6, h7⟩ := (hF lbl lsize s c fs hi).site a' ha' hpc
    refine ⟨h1', h2, h3, h4, h5, h6, h7, fun pm => ?_⟩
    have hk : TakeK a rS s (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) :=
      ⟨pcOf_eq_iff.mp (hsite ha' ▸ hpc), pm, rfl⟩
    obtain ⟨c', fs', hr, hi'⟩ := hK lbl lsize s c fs hi _ (.inl hk)
    exact ⟨c', fs', hr, hi', (hF lbl lsize s c fs hi).tkTake a' ha' hpc (Kernel.copyRange pm (abi.dmem s) rS)⟩
  · exact fun lbl lsize s c fs hi hn => (hF lbl lsize s c fs hi).tkInstr hn
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).tkSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).owned
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

/-- info: 'Spike.Lib.A64ConsumerA.inst_of_segWA2C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inst_of_segWA2C

end Spike.Lib.A64ConsumerA
