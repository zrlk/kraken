/-
**A block's states inside `W2`** (AArch64; the twin of
`Spike/Lib/LowerX64/W2Blk.lean`): the producers of `BlkW` and `NodeW` at
`W2` (`Spike/Lib/LowerA64/SFactsA2.lean`) from their parts.

`W2`'s state facts (`SFactsSt`) come from `SFacts` at the source start's
control (`dumN`, `BlkW.st`), as the phase table's producers give it
(`blkW_postO'`); at that control no abort site is reached (`A64Consumer.c0`
is not about to overflow), so `W2.abort` holds vacuously. The pair's facts
`noRet` and `run` are facts of the node's controls (`FrOk2`, `runOk2_of`);
the abort phase (`AbSt`), the frames' placement (`PlacedS`) and the write
obligation are the remaining part, a `BlkW` of their own.

- `SFactsSt.dt_mono`: a larger write tail;
- `noAbort_of_sfacts_c0`: no abort site at `SFacts` at `A64Consumer.c0`;
- `W2Part`: the abort phase, the placement and the write obligation;
- `BlkW.w2`, `NodeW.w2`: `W2` from the parts.
- `W2PartE`, `W2Part.toE`, `w2_of_partsE`, `BlkW.w2E`, `NodeW.w2E`: the same
  with the placement at `PlacedSE` (the current frame possibly in the
  output extern's model, as at `print`'s argument block).
-/
import Spike.Lib.LowerA64.SFactsA2
import Spike.Lib.A64AllocGSt

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.AllocG (dumN BlkW.st NodeW.st)
open Spike.Lib.LowerNode (FrOk2 ZBad runOk2_of)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **A larger write tail keeps the state's facts.** -/
theorem _root_.Spike.Lib.A64ConsumerA.SFactsSt.dt_mono {Dt' : State → Prop} (h : SFactsSt Λ μ own rS Tk s Dt)
    (hD : ∀ s, Dt s → Dt' s) :
    SFactsSt Λ μ own rS Tk s Dt' :=
  ⟨h.noSite, h.mapped, h.svc, h.ownInstr, h.ownSys, h.ownTake, h.site, h.tkTake, h.tkInstr, h.tkSys, h.owned,
    fun hs fd buf n hd => hD _ (h.wrTail hs fd buf n hd)⟩

/-- **No abort site at `SFacts` at the source start's control**: its term
is a `tail`, not about to overflow. -/
theorem noAbort_of_sfacts_c0 {Dt' : State → Prop} (h : SFacts Λ μ own rS Tk lbl0 s A64Consumer.c0 Dt') :
    ∀ k a, μ.abortAt k = some a → pcOf s ≠ a := fun k a ha hpc => by
  obtain ⟨-, ⟨x, a', b, e, -, -, -, -, -, -, ht, -⟩, -⟩ := h.abortOk k a ha hpc
  cases ht

/-- **`W2`'s part not given by the phase table nor by the node's
controls**: the abort phase (`AbSt`), the frames placed (`PlacedS`), the
arena's write obligation at the controls the frame runs reach, and at an
output `write(1, …)` the source at `print`'s loop top (`PrintSvc`). -/
def W2Part (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (ar : Arena) (J : InvS) (Ab : State → Prop) (lbl : Lbl) (lsize : Lsize)
    (fs : List TermRun.Frame) : Frag isaLSE2 := fun s c =>
  AbSt μ Ab s ∧ PlacedS Λ lbl s c fs ∧
    (∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') ∧
    (abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) →
      Spike.Lib.PrintSvc.PrintSvc c fs)

/-- **`W2` from its parts**: `SFacts` at the source start's control and
`W2Part` at the state, `main`'s `ret` excluded and `FrOk2` at the
control. -/
theorem w2_of_parts (hp : ProgNoS ZBad p) (hS : SFacts Λ μ own rS Tk lbl0 s A64Consumer.c0)
    (hP : W2Part Λ μ p rd G own ar J Ab lbl lsize fs s c) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hf : FrOk2 c fs) : W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs :=
  w2_of hp hf (hS.toSt.dt_mono fun _ h => h.elim) hP.1 hnr (.of_placedS hP.2.1) hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts_c0 hS)) hP.2.2.2

/-- **`W2Part` with the placement at `PlacedSE`**: the frames placed, or
the current frame in the output extern's model. -/
def W2PartE (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : Own) (ar : Arena) (J : InvS) (Ab : State → Prop) (lbl : Lbl) (lsize : Lsize)
    (fs : List TermRun.Frame) : Frag isaLSE2 := fun s c =>
  AbSt μ Ab s ∧ PlacedSE Λ lbl s c fs ∧
    (∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      WrOkA ar lbl lsize (msOfA Λ μ rd G (fun s _ => own s) ar J lbl lsize fs')
        (fun s' c'' => PendA p J lbl lsize s' c'' fs') s c') ∧
    (abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) →
      Spike.Lib.PrintSvc.PrintSvc c fs)

theorem W2Part.toE (h : W2Part Λ μ p rd G own ar J Ab lbl lsize fs s c) :
    W2PartE Λ μ p rd G own ar J Ab lbl lsize fs s c :=
  ⟨h.1, .of_placedS h.2.1, h.2.2⟩

/-- **`W2` from its parts at `PlacedSE`** (`w2_of_parts` at `W2PartE`). -/
theorem w2_of_partsE (hp : ProgNoS ZBad p) (hS : SFacts Λ μ own rS Tk lbl0 s A64Consumer.c0)
    (hP : W2PartE Λ μ p rd G own ar J Ab lbl lsize fs s c) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hf : FrOk2 c fs) : W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs :=
  w2_of hp hf (hS.toSt.dt_mono fun _ h => h.elim) hP.1 hnr hP.2.1 hP.2.2.1
    (abortOkA_of_ne (noAbort_of_sfacts_c0 hS)) hP.2.2.2

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop}

/-- **A block's states inside `W2`** at the frames `fs`: `SFacts` at the
source start's control (`dumN`, as `blkW_postO'` gives it) not moved by
`K`, `W2Part` at the states, and at every control of the node's invariant
`main`'s `ret` excluded and `FrOk2`. -/
theorem BlkW.w2 (hp : ProgNoS ZBad p) {n : ND} {blk : List Directive}
    (hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (dumN n) blk)
    (hP : BlkW (W2Part Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJn k hk m hA' hD =>
    let h1 := hS s σ _ he hn hd hpc hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
    ⟨w2_of_parts hp h1.1 (hP s σ c he hn hd hpc hA hF hJn k hk m hA' hD).1 (hJ σ c hJn).1 (hJ σ c hJn).2, h1.2⟩

/-- **A node's states inside `W2`** at the frames `fs` (as `BlkW.w2`). -/
theorem NodeW.w2 (hp : ProgNoS ZBad p) {n : ND}
    (hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (dumN n))
    (hP : NodeW (W2Part Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F n)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  fun s c hA => by
    obtain ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩ := hA
    have hS' := hS s _ ⟨h1, h2, h3, h4, σ, hAb, hF, rfl, c, hJn⟩
    exact ⟨w2_of_parts hp hS'.1 (hP s c ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩).1 (hJ σ c hJn).1 (hJ σ c hJn).2,
      hS'.2⟩

/-- **A block's states inside `W2` at `PlacedSE`** (`BlkW.w2` at `W2PartE`). -/
theorem BlkW.w2E (hp : ProgNoS ZBad p) {n : ND} {blk : List Directive}
    (hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (dumN n) blk)
    (hP : BlkW (W2PartE Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJn k hk m hA' hD =>
    let h1 := hS s σ _ he hn hd hpc hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
    ⟨w2_of_partsE hp h1.1 (hP s σ c he hn hd hpc hA hF hJn k hk m hA' hD).1 (hJ σ c hJn).1 (hJ σ c hJn).2, h1.2⟩

/-- **A node's states inside `W2` at `PlacedSE`** (`NodeW.w2` at `W2PartE`). -/
theorem NodeW.w2E (hp : ProgNoS ZBad p) {n : ND}
    (hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (dumN n))
    (hP : NodeW (W2PartE Λ μ p rd G own ar J Ab lbl lsize fs) (fun _ _ => False) exe endPc R F n)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  fun s c hA => by
    obtain ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩ := hA
    have hS' := hS s _ ⟨h1, h2, h3, h4, σ, hAb, hF, rfl, c, hJn⟩
    exact ⟨w2_of_partsE hp hS'.1 (hP s c ⟨h1, h2, h3, h4, σ, hAb, hF, hJn⟩).1 (hJ σ c hJn).1 (hJ σ c hJn).2,
      hS'.2⟩

/--
info: 'Spike.Lib.LowerA64.BlkW.w2E' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BlkW.w2E

/--
info: 'Spike.Lib.LowerA64.BlkW.w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BlkW.w2

end Spike.Lib.LowerA64
