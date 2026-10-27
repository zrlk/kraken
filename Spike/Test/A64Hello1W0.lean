/-
**`hello1.w`'s states before the allocation** (`W0`): the fragment the
levels' cut A (`hello1_correctKLS_levelsB`, `Spike/Test/A64Hello1LevelsB.lean`)
takes its segments under, and its `SFactsA` (`hW0`).

- `ArenaWr0`, `W0 p rS Dt Ctx`: the state's facts (`SFactsSt`, `Spike/Lib/A64SFactsA.lean`)
  at the write tail `Dt` (the heap abort stub's message `write` is in it),
  the write abort's phase kept (`AbSt` at `WriteAb.Ab labT`,
  `Spike/Lib/A64WriteAb.lean`), no `ret` of `main` at no frame, the
  control and frames placed at the static placement (`PlacedS`), the
  arena's writes off the counter allowed (`ArenaWr0`), a counter write only
  in a context `Ctx`, the source's runs from the pair (`RunOk`) and the
  abort sites (`AbortW`). Not `Wr` (`SFacts`): `rodata`'s states before the
  allocation are at its `newBuf`, which `SFacts.noAlloc` excludes.
- `hW0`: `SFactsA` at the static placement, the write tail `Dt`, the
  write abort's phase `Ab := WriteAb.Ab labT`, from `SFactsA.ofSt`, given
  the consumer's counter row in the context `Ctx` (`hctr`).
-/
import Spike.Test.A64Hello1SFactsN
import Spike.Test.A64Hello1RtW
import Spike.Lib.A64WriteAb

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (FragS EnvSmall OvfReady HeapAbortObl FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.SFactsN
open Spike.Test.A64Hello1Load (hello1M0)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Test.A64Hello1CorrectA (Ih)
open SccCode (hello1Λ hello1Prog hello1Asm)

/-- **The abort sites at a pair before the allocation**: the overflow's,
its control ready with small environments, or the heap's, its obligation
met; the exit status the abort status. -/
def AbortW (μ : Marks) (s : State) (c : Spike.Lib.Ctl) (fs : List TermRun.Frame) : Prop :=
  ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨ (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus

/-- **The arena's writes at a pair before the allocation**: every word the
instruction writes, the counter's aside, is one the arena allows from every
control the source's frames run to (`ArenaW` at the static placement, any
sizes: off the arena or a header below a held count). -/
def ArenaWr0 (p : Prog) (s : State) (c : Spike.Lib.Ctl) (fs : List TermRun.Frame) : Prop :=
  ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ L, WrAt s L → L ≠ ar.ctrLoc → ∀ lsize : Lsize,
    ArenaW ar hello1Λ.static lsize c' L

/-- **`hello1.w`'s states before the allocation**: the state's facts at the
write tail `Dt`, the write abort's phase kept (`AbSt` at `WriteAb.Ab`), no
`ret` of `main` at no frame, the control and the frames placed at the
static placement, the arena's writes off the counter allowed (`ArenaWr0`),
a write of the counter only in the context `Ctx`, the source's runs from
the pair (`RunOk`), the abort sites (`AbortW`). -/
def W0 (p : Prog) (rS : Range) (Dt : State → Prop) (Ctx : FragS isaLSE2) : FragS isaLSE2 := fun s c fs =>
  SFactsSt hello1Λ μ0 own rS Tk s Dt ∧ AbSt μ0 (Spike.Lib.A64.WriteAb.Ab labT) s ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧
    PlacedS hello1Λ hello1Λ.static s c fs ∧ ArenaWr0 p s c fs ∧ (WrAt s ar.ctrLoc → Ctx s c fs) ∧ RunOk p c fs ∧
    AbortW μ0 s c fs

/-- **`W0`'s `SFactsA`**, the levels' `hW0`, at its write tail and the
write abort's phase `WriteAb.Ab`, the counter's add in the context `Ctx`
giving the consumer's row (`hctr`). -/
theorem hW0 {p : Prog} {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range}
    {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {Dt : State → Prop}
    {Ctx : FragS isaLSE2} (hpa : textProgram hello1Asm = .ok hello1Prog)
    (hctr : ∀ s c fs, Ctx s c fs → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
        (Ih lsize inv0 inv1) hello1Λ.static lsize fs')
        (fun s' c'' => PendA p (Ih lsize inv0 inv1) hello1Λ.static lsize s' c'' fs') s c') :
    ∀ s c fs, W0 p rS Dt Ctx s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) hello1Λ.static lsize s c fs Dt (Spike.Lib.A64.WriteAb.Ab labT) := by
  rintro s c fs ⟨hst, has, hnr, hpl, hn, hcx, hr, hab⟩
  have hwr := fun c' fs' (hrun : FrameRun p (c, fs) (c', fs')) (hsys : abi.atSys s = false) =>
    (⟨fun L hL => (Classical.em (L = ar.ctrLoc)).elim .inl fun h => hn c' fs' hrun L hL h lsize,
      fun hL => hctr s c fs (hcx hL) c' fs' hrun hsys⟩ :
      WrOkA ar hello1Λ.static lsize
        (msOfA hello1Λ (T.marks hello1Asm hello1Λ) rd (FixG Fix hello1M0) (fun s _ => own s) ar
          (Ih lsize inv0 inv1) hello1Λ.static lsize fs')
        (fun s' c'' => PendA p (Ih lsize inv0 inv1) hello1Λ.static lsize s' c'' fs') s c')
  rw [hello1_marks hpa] at hwr ⊢
  exact SFactsA.ofSt hst has hnr hr.cell
    (.of_placedS hpl) hwr hr.zero fun k a ha hpc =>
      ⟨(hab k a ha hpc).1.elim (fun h => .inr (.inl h)) fun h => .inr (.inr h), (hab k a ha hpc).2⟩

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.A64Hello1W0.hW0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hW0

end Spike.Test.A64Hello1W0
