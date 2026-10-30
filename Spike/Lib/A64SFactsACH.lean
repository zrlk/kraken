/-
**The allocation-capable consumer's obligations with a `clone` refusal,
over a held predicate** (AArch64): `inst_of_segWA2C`
(`Spike/Lib/A64SFactsAC.lean`) for a fragment that takes more than one
stack range (wake's main: `r0` at its own `scc_rt_thread_init`, `r1` at
the second thread's), so with no single range `rS` and phase `Tk`: the
take path is `HeldPathS` (`Spike/Lib/A64ConsumerS.lean`) over a held
predicate, here `HeldOk2 Λ r0 r1` (`heldPathS_ok2`,
`Spike/Lib/A64HeldPath2.lean`).

- `TakeKS`, `TakeCKS`: the take of the range the site's registers name
  (`TakeK` at `siteRange`), and it or a `clone` refusal; `SegInvS.congrK`,
  `SegInvS.toCKS`: a segment built with `TakeCK a rS Cl` is one with
  `TakeCKS a Cl` where every take of its fragment names `rS`.
- `SFactsSt2`: `SFactsSt` (`Spike/Lib/A64SFactsA.lean`) with no range and
  phase: at the take site only the `nop` off a system call;
  `SFactsSt.toSt2`.
- `SFactsACH`: `SFactsAC` with `SFactsSt2`'s take site and `WrOkA` split
  into the counter's row (`wr`) and every write the arena's or the box's
  initialising store (`arena`, `NodesA.arena`'s two disjuncts);
  `SFactsAC.toH`, `SFactsACH.ofSt`.
- `inst_of_segWA2CH`: the obligations, `NodesA … Cl`, `TakeSiteS`,
  `AbortPathSC`, `WrInS` and `ClonePathS`; `inst_of_segWA2CH2`: with
  `HeldPathS … (HeldOk2 Λ r0 r1)` from the take-site split.
-/
import Spike.Lib.A64SFactsAC
import Spike.Lib.A64HeldPath2

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Spike.Lib.HeapLand (AllocLand)

variable {p : Prog}

/-! ## The outside moves -/

/-- **The take at `a` of the range the site's registers name.** -/
def TakeKS (a : Int64) (s s' : State) : Prop := TakeK a (Kernel.siteRange abi s) s s'

/-- **The take at `a` or a `clone` refusal at `Cl`**, with no fixed range. -/
def TakeCKS (a : Int64) (Cl : State → Prop) (s s' : State) : Prop := TakeKS a s s' ∨ CloneErrK Cl s s'

/-- `SegInvS` depends on the outside move only at the fragment's states. -/
theorem SegInvS.congrK {W inv : FragS isaLSE2} {K K' : State → State → Prop} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} (h : SegInvS W K p lbl ms inv)
    (hK : ∀ s c fs, inv s c fs → ∀ s', K s s' ↔ K' s s') : SegInvS W K' p lbl ms inv := by
  intro s c fs hi
  obtain ⟨hW, hO, hk⟩ := h s c fs hi
  exact ⟨hW, fun hn => hO fun s' hs => hn s' ((hK s c fs hi s').mp hs),
    fun s' hs => hk s' ((hK s c fs hi s').mpr hs)⟩

/-- **A segment with `TakeCK a rS Cl` is one with `TakeCKS a Cl`** where
every fragment state at the take site names `rS`. -/
theorem SegInvS.toCKS {W inv : FragS isaLSE2} {a : Int64} {rS : Range} {Cl : State → Prop} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} (h : SegInvS W (TakeCK a rS Cl) p lbl ms inv)
    (hr : ∀ s c fs, inv s c fs → s.st.2 = a → Kernel.siteRange abi s = rS) :
    SegInvS W (TakeCKS a Cl) p lbl ms inv := by
  refine h.congrK fun s c fs hi s' => or_congr_left ⟨fun hk => ?_, fun hk => ?_⟩
  · have e := hr s c fs hi hk.1
    unfold TakeKS; rw [e]; exact hk
  · have e := hr s c fs hi hk.1
    unfold TakeKS at hk; rw [e] at hk; exact hk

/-! ## The per-state and per-pair facts -/

/-- **`SFactsSt` with no range and phase**: at the take site only the `nop`
off a system call (the range and the held list are `HeldPathS`'s). -/
structure SFactsSt2 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (s : State) (Dt : State → Prop := fun _ => False) :
    Prop where
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  svc : abi.atSys s = true → ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  ownInstr : abi.atSys s = false → ∀ tree, isaLSE2.exec s = some tree → OwnTree own (own s) tree
  ownSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s
  ownTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, own (abi.skip (abi.setDmem s m)) = own s
  site : ∀ a, μ.site .take = some a → pcOf s = a →
    (∃ sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) ∧ abi.atSys s = false
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s

/-- `SFactsSt` forgets its range and phase. -/
theorem SFactsSt.toSt2 {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {s : State}
    {Dt : State → Prop} (h : SFactsSt Λ μ own rS Tk s Dt) : SFactsSt2 Λ μ own s Dt :=
  ⟨h.noSite, h.mapped, h.svc, h.ownInstr, h.ownSys, h.ownTake,
    fun a ha hpc => let ⟨_, h2, h3, _⟩ := h.site a ha hpc; ⟨h2, h3⟩, h.wrTail⟩

/-- **`SFactsAC` over a held predicate**: `SFactsAC`'s fields with the take
site's as `SFactsSt2`'s (no `site` range, no `tkTake`, `tkInstr`, `tkSys`,
`owned`). -/
structure SFactsACH (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (ar : Arena) (J : InvS) (lbl : Lbl) (lsize : Lsize) (s : State)
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
    (∃ sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) ∧ abi.atSys s = false
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s
  /-- The counter's write is its add's row (`WrOkA.ctr`). -/
  wr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → WrAt s ar.ctrLoc →
    CtrRow (msOfA Λ μ rd G own ar J lbl lsize fs') (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c'
  /-- Every write is one the arena allows (`WrOkA.arena`) or the box's
  initialising store (`NodesA.arena`'s two disjuncts). -/
  arena : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → ∀ L, WrAt s L →
    ArenaW ar lbl lsize c' L ∨ NewStM p lbl (msOfA Λ μ rd G own ar J lbl lsize fs') s c'
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

/-- `SFactsAC` forgets its range and phase. -/
theorem SFactsAC.toH (h : SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab Cl Ac) :
    SFactsACH Λ μ p rd G own ar J lbl lsize s c fs Dt Ab Cl Ac :=
  ⟨h.noRet, h.cell, h.noSite, h.mapped, h.place, h.svc, h.ownRun, h.ownInstr, h.ownSys, h.ownTake,
    fun a ha hpc => let ⟨_, h2, h3, _⟩ := h.site a ha hpc; ⟨h2, h3⟩, h.wrTail,
    fun c' fs' hr hns => (h.wr c' fs' hr hns).ctr, fun c' fs' hr hns L hL => .inl ((h.wr c' fs' hr hns).arena L hL),
    h.zero, h.abortOk,
    h.abInstr, h.abSys, h.abTake, h.acSt, h.clSvc⟩

/-- **`SFactsACH` from the state's facts and the pair's** (`SFactsAC.ofSt`
over a held predicate). -/
theorem SFactsACH.ofSt {own : Own} (h : SFactsSt2 Λ μ own s Dt) (hab : AbSt μ Ab s) (hac : AcSt μ Cl Ac s)
    (hcl : Cl s → abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hcell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
      (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
      TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty)
    (hpl : PlacedSE Λ lbl s c fs)
    (hwr : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → WrAt s ar.ctrLoc →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs') (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c')
    (harena : ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false → ∀ L, WrAt s L →
      ArenaW ar lbl lsize c' L ∨ NewStM p lbl (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs') s c')
    (hzero : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
      ZeroOkTy τ = true)
    (habort : ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortOblA ar.cells ar.ctr c) ∨ (k = .threads ∧ Ac s)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    SFactsACH Λ μ p rd G (fun s _ => own s) ar J lbl lsize s c fs Dt Ab Cl Ac :=
  ⟨hnr, hcell, h.noSite, h.mapped, hpl, h.svc, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ hs tree he => h.ownInstr hs tree he, fun _ _ _ hs call hd s' hs' => h.ownSys hs call hd s' hs',
    h.ownTake, h.site, h.wrTail, hwr, harena, hzero, habort, hab.abInstr, hab.abSys, hab.abTake, hac, hcl⟩

/-! ## The obligations -/

/-- **The consumer's obligations from two segment levels with a `clone`
refusal, over a held predicate** (`inst_of_segWA2C` with the take of the
range the site names, `TakeCKS`): every pair of either level carrying
`SFactsACH` at its placement over `I2`, `I2` is a fragment with
`NodesA … Cl`, `TakeSiteS`, `AbortPathSC`, `WrInS` and `ClonePathS`. -/
theorem inst_of_segWA2CH {L0 : Lbl} {ls0 : Lsize} {a : Int64}
    {W0 inv0 : FragS isaLSE2} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeCKS a Cl) p (upd L0 l b)
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd L0 l b) (updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeCKS a Cl) p L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0) inv0)
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsACH Λ μ p rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsACH Λ μ p rd G own ar (I2 ar L0 ls0 inv0 inv1) (upd L0 l b) (updN ls0 l n) s c fs Dt Ab Cl Ac) :
    NodesA Λ p μ rd G own ar (I2 ar L0 ls0 inv0 inv1) none Cl ∧ TakeSiteS p μ (I2 ar L0 ls0 inv0 inv1) ∧
      AbortPathSC μ (I2 ar L0 ls0 inv0 inv1) Cl Ab Ac ar.cells ar.ctr ∧ WrInS (I2 ar L0 ls0 inv0 inv1) Dt ∧
      ClonePathS p (I2 ar L0 ls0 inv0 inv1) Cl := by
  have hF : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs →
      SFactsACH Λ μ p rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize s c fs Dt Ab Cl Ac := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩)
    · exact hW0 s c fs hi (h0 s c fs hi).1
    · exact hW1 l b n s c fs hl hland (h1 l b n hl hland s c fs hi).1
  have hR : ∀ lbl lsize s c fs, IRun p (I2 ar L0 ls0 inv0 inv1) lbl lsize s c fs →
      ∃ c₀ fs₀, SFactsACH Λ μ p rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize s c₀ fs₀ Dt Ab Cl Ac ∧
        FrameRun p (c₀, fs₀) (c, fs) := by
    rintro lbl lsize s c fs ⟨c₀, fs₀, hi, hr⟩
    exact ⟨c₀, fs₀, hF _ _ _ _ _ hi, hr⟩
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  -- the outside moves' landings in `I2`
  have hK : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → ∀ s', TakeCKS a Cl s s' →
      ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧ I2 ar L0 ls0 inv0 inv1 lbl lsize s' c' fs' := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩) s' hk
    · obtain ⟨c', fs', hr, hi'⟩ := (h0 s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inl ⟨rfl, rfl, hi'⟩⟩
    · obtain ⟨c', fs', hr, hi'⟩ := (h1 l b n hl hland s c fs hi).2.2 _ hk
      exact ⟨c', fs', hr, .inr ⟨l, b, n, hl, hland, rfl, rfl, hi'⟩⟩
  -- either level's rows off the outside moves, under the memory side over `I2`
  have hOut : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → (∀ s', ¬ TakeCKS a Cl s s') →
      OutS p lbl (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) lbl lsize)
        (Pend p (I2 ar L0 ls0 inv0 inv1 lbl lsize)) s c fs := by
    rintro lbl lsize s c fs (⟨rfl, rfl, hi⟩ | ⟨l, b, n, hl, hland, rfl, rfl, hi⟩) hk
    · exact ((h0 s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ h => .inl ⟨rfl, rfl, h⟩
    · refine (OutS.mono_xa ((h1 l b n hl hland s c fs hi).2.1 hk) (fun _ => rfl)
        fun _ _ _ _ _ _ h => h.2.elim).mono fun _ _ _ h => h.mono fun _ _ _ h => ?_
      exact .inr ⟨l, b, n, hl, hland, rfl, rfl, h⟩
  -- no outside move off the take site and off `Cl`
  have hnk : ∀ lbl lsize s c fs, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → pcOf s ≠ a.toBitVec.toNat → ¬ Cl s →
      ∀ s', ¬ TakeCKS a Cl s s' := by
    rintro lbl lsize s c fs - hpc hcl s' (hk | ⟨hc, -⟩)
    · exact hpc (pcOf_eq_iff.mpr hk.1)
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
    · obtain ⟨⟨sz, hcn⟩, -⟩ := (hF lbl lsize s c fs hi).site _ hμ hpc
      exact hdone _ (Kraken.Promising.Lower.A64.exec_nop hcn)
    · have hcl : ¬ Cl s := fun hc => by
        have := ((hF lbl lsize s c fs hi).clSvc hc).1
        rw [hns] at this; cases this
      cases hOut lbl lsize s c fs hi (hnk lbl lsize s c fs hi hpc hcl) with
      | pre c₁ fs₁ _ h => exact ⟨c₁, _, _, rfl, h⟩
      | frame s' _ _ he _ _ => exact hdone s' he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_⟩,
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

/-- **The obligations at the two-range held predicate** (`inst_of_segWA2CH`
with `heldPathS_ok2`): `HeldPathS … (HeldOk2 Λ r0 r1)` from the ranges'
facts and the take-site split (`hsplit`: a fragment state at the take site
holding `hl` takes `r0` with none held or `r1` with `r0` held). -/
theorem inst_of_segWA2CH2 {L0 : Lbl} {ls0 : Lsize} {a : Int64}
    {W0 inv0 : FragS isaLSE2} {W1 inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (h1 : ∀ l b n, L0 l = none → AllocLand ar.heap ar.cells b n →
      SegInvS (W1 l b n) (TakeCKS a Cl) p (upd L0 l b)
        (msOfA Λ μ rd G own ar (fun _ _ _ _ _ => False) (upd L0 l b) (updN ls0 l n)) (inv1 l b n))
    (h0 : SegInvS W0 (TakeCKS a Cl) p L0 (msOfA Λ μ rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0) inv0)
    (hμ : μ.site .take = some a.toBitVec.toNat)
    (hW0 : ∀ s c fs, inv0 s c fs → W0 s c fs →
      SFactsACH Λ μ p rd G own ar (I2 ar L0 ls0 inv0 inv1) L0 ls0 s c fs Dt Ab Cl Ac)
    (hW1 : ∀ l b n s c fs, L0 l = none → AllocLand ar.heap ar.cells b n → W1 l b n s c fs →
      SFactsACH Λ μ p rd G own ar (I2 ar L0 ls0 inv0 inv1) (upd L0 l b) (updN ls0 l n) s c fs Dt Ab Cl Ac)
    {r0 r1 : Range}
    (hsplit : ∀ lbl lsize s c fs hl, I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs → HeldOk2 Λ r0 r1 s hl →
      ∀ a, μ.site .take = some a → pcOf s = a →
        (hl = [] ∧ Kernel.siteRange abi s = r0) ∨ (hl = [(0, r0)] ∧ Kernel.siteRange abi s = r1))
    (hs0 : r0.Sub Λ.stackPool) (hs1 : r1.Sub Λ.stackPool) (hz0 : 0 < r0.size) (hz1 : 0 < r1.size)
    (hro : Λ.rodata.Disjoint Λ.stackPool) (hd : r1.Disjoint r0)
    (hw0 : r0.lo + r0.size ≤ 2 ^ 64) (hw1 : r1.lo + r1.size ≤ 2 ^ 64) :
    NodesA Λ p μ rd G own ar (I2 ar L0 ls0 inv0 inv1) none Cl ∧
      HeldPathS Λ p μ (I2 ar L0 ls0 inv0 inv1) (HeldOk2 Λ r0 r1) ∧
      AbortPathSC μ (I2 ar L0 ls0 inv0 inv1) Cl Ab Ac ar.cells ar.ctr ∧ WrInS (I2 ar L0 ls0 inv0 inv1) Dt ∧
      ClonePathS p (I2 ar L0 ls0 inv0 inv1) Cl := by
  obtain ⟨hN, hts, hA, hWr, hC⟩ := inst_of_segWA2CH h1 h0 hμ hW0 hW1
  exact ⟨hN, heldPathS_ok2 hts hsplit hs0 hs1 hz0 hz1 hro hd hw0 hw1, hA, hWr, hC⟩

/-- info: 'Spike.Lib.A64ConsumerA.inst_of_segWA2CH2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inst_of_segWA2CH2

/-- info: 'Spike.Lib.A64ConsumerA.SegInvS.toCKS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SegInvS.toCKS

end Spike.Lib.A64ConsumerA
