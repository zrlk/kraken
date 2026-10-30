/-
**The consumer's obligations at any call depth from one segment inside
`W`** (the frames twin of `Spike/Lib/A64SegInst.lean`): a `SegWS W (TakeK a
rS)` from the start fragment to `False` (the program never leaves it), with
every pair of `W` at its frames carrying the per-pair facts of `NodesS`,
`TakePathS` and an `AbortPathS` with an empty phase (`SFactsS`), gives the
fragment `I` of `correctKS` (`Spike/Lib/A64ConsumerS.lean`) with `NodesS`,
`TakePathS` and `AbortPathS` (`Ab` false).

- `SFactsS`: `SFacts` at the frames `fs`: `noRet` only at depth 0; `cell`,
  `noAlloc`, `ownInstr`, `ownSys` at every pair a frame run reaches from
  `(c, fs)` (`NodesS` asks them over `IRun`); `ownRun`, a frame run from or
  into `(c, fs)` keeps the words owned at `s`; `place`, every frame placed
  (`PlacedS`); at an abort site the overflow case with every frame's
  environment small (`EnvSmallS`) or the heap case (`abortOk`).
- `abortOk_of_neS`: `abortOk` off every abort site.
- `IOfS`: the fragment at the labels' placement `L0` and sizes `ls0`.
- `WrInS`: every fragment pair at a `write` in `Dt`; `writeNoPromS_of_wrIn`:
  `WriteNoPromS` from it and `Dt` closed under certification keeping the
  promise set (`TailNoFul.step`, e.g. `tailNoFul_ovf`'s).
- `inst_of_segWS`: the obligations. `NodesS.out` is the segment's `OutS`
  closure off the take site (rows landing with a pending frame run); `TakePathS.site`'s landing after the take is
  its closure under the take (`KOutS`, a frame run); `AbortPathS.at_` from
  `SFactsS.abortOk`; `WrInS` from `SFactsS.wrTail`.
- `correctKSPE`: `correctKOnS` on the target on parsed texts at an entry
  state `E` (`TParE E`, the load by `rfl`; `correctA64PE`'s twin).
-/
import Spike.Lib.A64ConsumerS
import Spike.Lib.A64TailNoFul
import Spike.Lib.A64Correct

namespace Spike.Lib.A64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow.Ret0 (TakeK TakeK.pc)

/-- **The per-pair facts at the frames `fs`** of a thread state `s` paired
with `c`, at the labels' placement `lbl` (`SFacts` with the frames): `noRet`
at depth 0; `cell`, `noAlloc`, `ownInstr`, `ownSys` at every pair a frame run
reaches from `(c, fs)`; `ownRun`, a frame run from or into `(c, fs)` keeps
the words owned at `s`; `place`, every frame placed; at the take site
`TakePathS.site`'s static half and the take landing in the phase `Tk`, kept
by every instruction off the transfer sites and every system call; `rS` owned
in the phase; at an abort site the overflow case with every frame's
environment small or the heap case at the arena's `cells` and the counter
word `ctr`, with the abort status at an `exit_group` (`abortOk`); at a `write`
only states of the write tail `Dt` (`wrTail`).

As with `SFacts`, `Dt` defaults to false (no `write`); **whenever the write
tail is live, `Dt` must be given explicitly**. -/
structure SFactsS (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (own : OwnS) (rS : Range) (Tk : State → Prop)
    (lbl : Lbl) (cells ctr : Nat) (s : State) (c : Ctl) (fs : List TermRun.Frame)
    (Dt : State → Prop := fun _ => False) : Prop where
  noRet : fs = [] → ∀ a, c.term ≠ .ret a
  cell : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  place : PlacedS Λ lbl s c fs
  svc : abi.atSys s = true → ∃ imm sz, Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .SVC imm⟩) sz
  noAlloc : ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ x a τ e, c'.term ≠ .let_ x (.newBuf a τ) e
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
  /-- The heap case is a buffer allocation's only (`HeapReady`, guarded on
  `newBuf`), by design: it feeds `AbortPathS`, whose consumer's relation
  carries the buffer-only heap clause. Programs with box allocations use the
  `SFactsACH` path (`HeapAbortOblA`, `AbortPathSC`). -/
  abortOk : ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ ∀ old, ((∃ x a τ e, c.term = .let_ x (.newBuf a τ) e) →
        old ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num old)) → HeapReady cells old c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s

/-- **`SFactsS.abortOk` off every abort site.** -/
theorem abortOk_of_neS {μ : Marks} {s : State} {c : Ctl} {fs : List TermRun.Frame} {cells ctr : Nat}
    (h : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a) :
    ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ ∀ old, ((∃ x a τ e, c.term = .let_ x (.newBuf a τ) e) →
          old ≤ cells ∧ ∀ w, c.hold = some (ctr, w) → w = TermRun.cst (.num old)) → HeapReady cells old c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus :=
  fun k a ha hpc => (h k a ha hpc).elim

/-- **The fragment with frames at one placement**: the labels' placement
`L0` and sizes `ls0`, and the pair at its frames in `inv`. -/
def IOfS (L0 : Lbl) (ls0 : Lsize) (inv : FragS isaLSE2) : InvS :=
  fun lbl lsize s c fs => lbl = L0 ∧ lsize = ls0 ∧ inv s c fs

/-- **Every fragment pair at a `write` is in `Dt`** (`WrIn` with the
frames). -/
def WrInS (I : InvS) (Dt : State → Prop) : Prop :=
  ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ fd buf n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s

/-- **`WriteNoPromS` from a closed tail** (`writeNoProm_of_tail` with the
frames): in `PreS` thread 0 is certified; at a `write` its state is in `Dt`
(`WrInS`), which the certifying run never leaves keeping the promise set
(`hs`, `TailNoFul.step`), so the set is empty (`prom_nil_of_closed`). -/
theorem writeNoPromS_of_wrIn {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop}
    {own : OwnS} {I : InvS} {rS : Range} {Tk : State → Prop} {μ : Marks} {cells ctr : Nat} {Dt : State → Prop}
    (h : WrInS I Dt)
    (hs : ∀ x (p q : Thread isaLSE2 × Memory), Dt p.1.st →
      ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 p q → Dt q.1.st ∧ q.1.prom = p.1.prom) :
    WriteNoPromS Λ P p G own I rS Tk μ cells ctr := by
  rintro t s th ⟨th', _, _, lbl, lsize, _, _, _, _, hth, -, -, -, -, hc, -, -, -, hI, -⟩ hth1 hat ⟨fd, buf, n, hw⟩
  rw [hth] at hth1
  cases Option.some.inj (show some th' = some th from congrArg (·[0]?) hth1)
  exact prom_nil_of_closed (Q := fun x => Dt x.1.st) (t := th) (mem := t.1.mem)
    (fun x y hx hs' => hs _ x y hx hs') (h _ _ th.st _ _ hI hat fd buf n hw) hc

/-- **The consumer's obligations at any call depth from one segment inside
`W`**, the take of `rS` at `a` its outside move: the segment's hidden
invariant at the placement `L0`, `ls0` is the fragment, with `NodesS`,
`TakePathS` and `AbortPathS` with an empty phase, given every pair of `W` at
its frames carries `SFactsS` (`hW`) and the take site is `a` (`hμ`); every
fragment pair at a `write` is in `Dt` (`WrInS`). -/
theorem inst_of_segWS {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : OwnS} {L0 : Lbl} {ls0 : Lsize} {rS : Range} {Tk : State → Prop} {a : Int64} {p : Prog}
    {cells ctr : Nat} {W P : FragS isaLSE2}
    (h : SegWS W (TakeK a rS) p L0 (msOfS Λ μ rd G own L0 ls0) P (fun _ _ _ => False))
    (hμ : μ.site .take = some a.toBitVec.toNat)
    {Dt : State → Prop} (hW : ∀ s c fs, W s c fs → SFactsS Λ μ p own rS Tk L0 cells ctr s c fs Dt) :
    ∃ inv : FragS isaLSE2, (∀ s c fs, P s c fs → inv s c fs) ∧ NodesS Λ p μ rd G own (IOfS L0 ls0 inv) ∧
      TakePathS Λ p μ (IOfS L0 ls0 inv) rS Tk ∧ AbortPathS μ (IOfS L0 ls0 inv) (fun _ => False) cells ctr ∧
      WrInS (IOfS L0 ls0 inv) Dt := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  have hF : ∀ lbl lsize s c fs, IOfS L0 ls0 inv lbl lsize s c fs →
      SFactsS Λ μ p own rS Tk lbl cells ctr s c fs Dt := by
    rintro lbl lsize s c fs ⟨rfl, rfl, hi⟩
    exact hW s c fs (hiW s c fs hi)
  have hR : ∀ lbl lsize s c fs, IRun p (IOfS L0 ls0 inv) lbl lsize s c fs →
      ∃ c₀ fs₀, SFactsS Λ μ p own rS Tk lbl cells ctr s c₀ fs₀ Dt ∧ FrameRun p (c₀, fs₀) (c, fs) := by
    rintro lbl lsize s c fs ⟨c₀, fs₀, hi, hr⟩
    exact ⟨c₀, fs₀, hF _ _ _ _ _ hi, hr⟩
  have hsite : ∀ {a'}, μ.site .take = some a' → a' = a.toBitVec.toNat := fun h' => by
    rw [hμ] at h'; exact (Option.some.inj h').symm
  refine ⟨inv, hP, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).wrTail⟩
  -- `NodesS`
  · rintro lbl lsize s c fs ⟨rfl, rfl, hi⟩ hoff
    have hk : ∀ s', ¬ TakeK a rS s s' := fun s' hk =>
      hoff _ hμ (pcOf_eq_iff.mpr (TakeK.pc hk))
    exact ((hcl s c fs hi).1 hk).mono fun _ _ _ h => h.mono fun s c fs h => h.elim (fun h => ⟨rfl, rfl, h⟩) False.elim
  · exact fun lbl lsize s c hi => (hF lbl lsize s c [] hi).noRet rfl
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.cell c fs hr
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).noSite
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).mapped
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).place
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).svc
  · intro lbl lsize s c fs hi
    obtain ⟨c₀, fs₀, hf, hr⟩ := hR lbl lsize s c fs hi
    exact hf.noAlloc c fs hr
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
  -- `TakePathS`
  · rintro lbl lsize s c fs hi a' ha' hpc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := (hF lbl lsize s c fs hi).site a' ha' hpc
    refine ⟨h1, h2, h3, h4, h5, h6, h7, fun pm => ?_⟩
    obtain ⟨rfl, rfl, hi⟩ := hi
    have hk : TakeK a rS s (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) rS))) :=
      ⟨pcOf_eq_iff.mp (hsite ha' ▸ hpc), pm, rfl⟩
    obtain ⟨c', fs', hr, hi'⟩ := (hcl s c fs hi).2 _ hk
    exact ⟨c', fs', hr, ⟨rfl, rfl, hi'.elim id False.elim⟩, (hW s c fs (hiW s c fs hi)).tkTake a' ha' hpc _⟩
  · exact fun lbl lsize s c fs hi hn => (hF lbl lsize s c fs hi).tkInstr hn
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).tkSys
  · exact fun lbl lsize s c fs hi => (hF lbl lsize s c fs hi).owned
  -- `AbortPathS`, with an empty phase: the overflow and heap cases
  · intro lbl lsize s c fs hi k a' ha' hpc
    obtain ⟨hk, hv⟩ := (hF lbl lsize s c fs hi).abortOk k a' ha' hpc
    exact ⟨.inr hk, hv⟩
  · exact fun _ _ _ _ _ _ _ _ tree _ => (allInv_true tree).mono fun _ _ h => h
  · exact fun _ _ _ _ _ _ _ _ _ _ _ _ h => h.elim
  · exact fun _ _ _ _ _ _ _ _ _ _ _ h => h

open Scc.Cert.Link in
/-- **`correctKOnS` on parsed texts at an entry state `E`**: `Correct` over
the target on parsed texts (`TParE E`) at `(prog, secs)`, with no parse
equation (the load by `rfl`; `correctA64PE`'s twin at any call depth).
`correct_of_parsed` carries it to a text parsing to these values. -/
theorem correctKSPE {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {I : InvS} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {cells ctr : Nat}
    {E : Entry} {B : Budget} (hB : B.cells = cells) {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, (TParE E).load (prog, secs) Λ = some t0) (hP : HookOK P p)
    (hinit : P.init (s0 P.cap))
    (hN : NodesS Λ p ((TParE E).marks (prog, secs) Λ) rd G own I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((TParE E).marks (prog, secs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TParE E).load (prog, secs) Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hsvc : WriteNoPromS Λ P p G own I rS Tk ((TParE E).marks (prog, secs) Λ) cells ctr)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TParE E).load (prog, secs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((TParE E).marks (prog, secs) Λ) I Ab cells ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct (TParE E) (SrcSem.source P p) Λ B (prog, secs) :=
  correctKOnS (ld := (TParE E).load) (rs := (TParE E).resolve) (asm := (prog, secs)) hB rfl himg hss hw hst hfr0
    hload hP hinit hN hsafe hT htk0 hown0 hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.A64ConsumerS
