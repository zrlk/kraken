/-
**`SFactsA` from state facts** (x86-64; the twin of `Spike/Lib/A64SFactsA.lean`):
the per-pair facts of the
allocation-capable consumer (`SFactsA`, `Spike/Lib/X64SegInstA.lean`) split
into what depends on the target state alone and what depends on the source
pair, for owned words that do not depend on the frames.

- `SFactsSt`: the fields of `SFacts` (`Spike/Lib/X64SegInst.lean`) that are
  facts of the state alone (sites, mapping, `svc`, owned words, the take's
  phase, the write tail); `SFacts.toSt`: them from `SFacts`.
- `AbSt`: `SFactsA`'s abort-phase fields off the phase (`abInstr`, `abSys`,
  `abTake`), facts of the state alone; `AbSt.false`: with no phase.
- `abortOkA_of_ne`: `SFactsA.abortOk` off every abort site.
- `SFactsA.ofSt`: `SFactsA` at owned words with no frame dependence
  (`fun s _ => own s`) from `SFactsSt`, `AbSt` and the pair's facts: no
  `ret` of `main`, the cell, write and zero obligations at the controls the
  frame runs reach, the frames placed (`PlacedS`), the abort sites.
- `SFactsA.ofSFacts`: the same from `SFacts` at a pair with no frame.
-/
import Spike.Lib.X64SegInstA

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {p : Prog}

/-- **The per-state facts of the target state alone**: `SFacts`' fields
but those about the source control (`noRet`, `cell`, `place`, `noAlloc`)
and the abort sites (`abortOk`). -/
structure SFactsSt (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (rS : Range) (Tk : State → Prop) (s : State)
    (Dt : State → Prop := fun _ => False) : Prop where
  noSite : ∀ a, μ.site .release = some a → pcOf s ≠ a
  mapped : abi.atSys s = false → ∀ e, isa.exec s = some e →
    ¬ Kernel.Touches (fun l w => Kernel.mapped (K0 Λ) w l = false) e
  svc : abi.atSys s = true → ∃ sz, Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 .syscall) sz
  ownInstr : abi.atSys s = false → ∀ tree, isa.exec s = some tree → OwnTree own (own s) tree
  ownSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s
  ownTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, own (abi.skip (abi.setDmem s m)) = own s
  site : ∀ a, μ.site .take = some a → pcOf s = a →
    ¬ Tk s ∧ (∃ n sz, Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 (.nop n)) sz) ∧
      abi.atSys s = false ∧ Kernel.siteRange abi s = rS ∧ rS.Sub Λ.stackPool ∧ 0 < rS.size ∧
      Λ.rodata.Disjoint Λ.stackPool
  tkTake : ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, Tk (abi.skip (abi.setDmem s m))
  tkInstr : Kernel.siteAt abi μ s = none → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => Tk s' ↔ Tk s)
  tkSys : abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, (Tk s' ↔ Tk s)
  owned : Tk s → Owned Λ rS s
  wrTail : abi.atSys s = true → ∀ fd buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) →
    Dt s

/-- **`SFacts`' facts of the state alone.** -/
theorem _root_.Spike.Lib.X64Consumer.SFacts.toSt {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range}
    {Tk : State → Prop} {lbl : Lbl} {s : State} {c : Ctl} {Dt : State → Prop} (h : SFacts Λ μ own rS Tk lbl s c Dt) :
    SFactsSt Λ μ own rS Tk s Dt :=
  ⟨h.noSite, h.mapped, h.svc, h.ownInstr, h.ownSys, h.ownTake, h.site, h.tkTake, h.tkInstr, h.tkSys, h.owned,
    h.wrTail⟩

/-- **The abort phase's fields of the state alone**: off the phase `Ab`,
no instruction and no take enters it, and a system call only as a refused
`write` (`SFactsA.abInstr`, `abSys`, `abTake`). -/
structure AbSt (μ : Marks) (Ab : State → Prop) (s : State) : Prop where
  abInstr : ¬ Ab s → abi.atSys s = false → ∀ tree,
    isa.exec s = some tree → tree.AllInv (fun _ _ => True) (fun s' => ¬ Ab s')
  abSys : ¬ Ab s → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call, Ab s' →
      ∃ fd buf n, call = .write fd buf n ∧ ∀ r, abi.ret s r = s' → Refusal n r
  abTake : ¬ Ab s → ∀ a, μ.site .take = some a → pcOf s = a → ∀ m, ¬ Ab (abi.skip (abi.setDmem s m))

/-- `AbSt` with no abort phase. -/
theorem AbSt.false {μ : Marks} {s : State} : AbSt μ (fun _ => False) s :=
  ⟨abInstr_false, abSys_false, abTake_false⟩

/-- **`SFactsA.abortOk` off every abort site.** -/
theorem abortOkA_of_ne {μ : Marks} {s : State} {c : Ctl} {fs : List TermRun.Frame} {cells ctr : Nat}
    {Ab : State → Prop} (h : ∀ k a, μ.abortAt k = some a → pcOf s ≠ a) :
    ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortObl cells ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus :=
  fun k a ha hpc => (h k a ha hpc).elim

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Own}
  {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl}
  {fs : List TermRun.Frame} {Dt Ab : State → Prop}

/-- **`SFactsA` from the state's facts and the pair's**, at owned words
with no frame dependence: the state's (`SFactsSt`, `AbSt`), and at the
pair `main`'s `ret` excluded at no frame (`hnr`), the one-cell types of the
loads and stores the frame runs reach (`hcell`), the frames placed
(`hpl`), the arena's write obligation (`hwr`) and the zero check (`hzero`)
at the controls they reach, and the abort sites (`habort`). -/
theorem SFactsA.ofSt (h : SFactsSt Λ μ own rS Tk s Dt) (hab : AbSt μ Ab s)
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
        (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab where
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

/-- **`SFactsA` at no frame from `SFacts`**: its state facts, `noRet` and
`place`; the run-quantified obligations, the abort sites and the phase as
`SFactsA.ofSt`'s. -/
theorem SFactsA.ofSFacts (h : SFacts Λ μ own rS Tk lbl s c Dt) (hab : AbSt μ Ab s)
    (hcell : ∀ c' fs', FrameRun p (c, []) (c', fs') → ∀ x a e ty w,
      (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
      TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty)
    (hwr : ∀ c' fs', FrameRun p (c, []) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c')
    (hzero : ∀ c' fs', FrameRun p (c, []) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
      ZeroOkTy τ = true)
    (habort : ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env []) ∨
        (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus) :
    SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c [] Dt Ab :=
  SFactsA.ofSt h.toSt hab (fun _ => h.noRet) hcell (.of_placedS (PlacedS.ofNil h.place)) hwr hzero habort

end Spike.Lib.X64ConsumerA
