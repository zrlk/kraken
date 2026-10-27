/-
**The states before and after the allocation at any layout** (AArch64):
`W0`, `W1` of `hello1.w`'s levels (`Spike/Test/A64Hello1W0.lean`,
x64's `Spike/Test/X64Hello1W1.lean`) with the layout `Λ`, the marks `μ`,
the owned words `own`, the take's phase `Tk`, the write abort's phase `Ab`
and the arena `ar` as parameters (no layout constant).

- `AbortW0 μ ar`, `ArenaWr0 ar lbl p`, `W0 Λ μ own Tk Ab ar p rS Dt Ctx`:
  as `hello1.w`'s `AbortW`, `ArenaWr0`, `W0`; `hW0`: its `SFactsA` at the
  static placement `Λ.static`, the counter's add in the context `Ctx`
  giving the consumer's row (`hctr`).
- `WrIn1 ar b n`, `AbortW1 μ Ab ar`, `W1 Λ μ own Tk Ab ar Dt l b n p rS`:
  after the allocation of the fresh `l` at `b` with `n` words, the
  placement `upd Λ.static l b`; `wrOkA_of_wrIn1`, `hW1`.
- **Oracle**: `hello1.w`'s `W0` is `W0 hello1Λ μ0 own Tk (WriteAb.Ab labT) ar`
  (`Spike/Test/A64W0GHello1.lean`).
-/
import Spike.Lib.A64Hello1SFactsN

namespace Spike.Lib.A64.W0G

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (FragS Arena OvfReady HeapAbortObl FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Hello1.SFactsN (RunOk)

/-! ## Before the allocation -/

/-- **The abort sites at a pair before the allocation**: the overflow's,
its control ready with small environments, or the heap's, its obligation
met at the arena `ar`; the exit status the abort status. -/
def AbortW0 (μ : Marks) (ar : Arena) (s : State) (c : Spike.Lib.Ctl) (fs : List TermRun.Frame) : Prop :=
  ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨ (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus

/-- **The arena's writes at a pair before the allocation**: every word the
instruction writes, the counter's aside, is one the arena `ar` allows from
every control the source's frames run to (`ArenaW` at the placement `lbl`,
any sizes). -/
def ArenaWr0 (ar : Arena) (lbl : Lbl) (p : Prog) (s : State) (c : Spike.Lib.Ctl) (fs : List TermRun.Frame) :
    Prop :=
  ∀ c' fs', FrameRun p (c, fs) (c', fs') → ∀ L, WrAt s L → L ≠ ar.ctrLoc → ∀ lsize : Lsize,
    ArenaW ar lbl lsize c' L

/-- **The states before the allocation**: the state's facts at the write
tail `Dt`, the write abort's phase `Ab` kept, no `ret` of `main` at no
frame, the control and the frames placed at the static placement, the
arena's writes off the counter allowed (`ArenaWr0`), a write of the counter
only in the context `Ctx`, the source's runs from the pair (`RunOk`), the
abort sites (`AbortW0`). -/
def W0 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (Tk Ab : State → Prop) (ar : Arena) (p : Prog) (rS : Range)
    (Dt : State → Prop) (Ctx : FragS isaLSE2) : FragS isaLSE2 := fun s c fs =>
  SFactsSt Λ μ own rS Tk s Dt ∧ AbSt μ Ab s ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧
    PlacedS Λ Λ.static s c fs ∧ ArenaWr0 ar Λ.static p s c fs ∧ (WrAt s ar.ctrLoc → Ctx s c fs) ∧
    RunOk p c fs ∧ AbortW0 μ ar s c fs

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {Tk Ab : State → Prop} {ar : Arena} {p : Prog}
  {rS : Range} {Dt : State → Prop}

/-- **`W0`'s `SFactsA`** at the static placement, the write tail `Dt` and
the write abort's phase `Ab`, the counter's add in the context `Ctx`
giving the consumer's row (`hctr`). -/
theorem hW0 {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lsize : Lsize} {I : InvS}
    {Ctx : FragS isaLSE2}
    (hctr : ∀ s c fs, Ctx s c fs → ∀ c' fs', FrameRun p (c, fs) (c', fs') → abi.atSys s = false →
      CtrRow (msOfA Λ μ rd G (fun s _ => own s) ar I Λ.static lsize fs')
        (fun s' c'' => PendA p I Λ.static lsize s' c'' fs') s c') :
    ∀ s c fs, W0 Λ μ own Tk Ab ar p rS Dt Ctx s c fs →
      SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar I Λ.static lsize s c fs Dt Ab := by
  rintro s c fs ⟨hst, has, hnr, hpl, hn, hcx, hr, hab⟩
  exact SFactsA.ofSt hst has hnr hr.cell (.of_placedS hpl)
    (fun c' fs' hrun hsys =>
      ⟨fun L hL => (Classical.em (L = ar.ctrLoc)).elim .inl fun h => hn c' fs' hrun L hL h lsize,
        fun hL => hctr s c fs (hcx hL) c' fs' hrun hsys⟩) hr.zero
    fun k a ha hpc =>
      ⟨(hab k a ha hpc).1.elim (fun h => .inr (.inl h)) fun h => .inr (.inr h), (hab k a ha hpc).2⟩

/-! ## After the allocation -/

/-- **The writes after the allocation of `n` words at `b`**: every
location the instruction writes is off the arena or inside `[b, b + 8 n)`,
and not the counter word. -/
def WrIn1 (ar : Arena) (b n : Nat) (s : State) : Prop :=
  ∀ L, WrAt s L → (¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) ∨
    (b ≤ L.addr.toNat ∧ L.addr.toNat < b + 8 * n)) ∧ L ≠ ar.ctrLoc

/-- **`WrOkA` from `WrIn1`** at the placement placing `l` at `b` with `n`
words, any memory side and landing: an off-arena write is `ArenaW`'s
off-arena case, one in `[b, b + 8 n)` its placed label's at `l`. -/
theorem wrOkA_of_wrIn1 {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    {ms : Spike.Lib.MemSide isaLSE2} {X : Spike.Lib.Frag isaLSE2} {s : State} {c : Spike.Lib.Ctl}
    (h : WrIn1 ar b n s) : WrOkA ar (A64ConsumerA.upd L0 l b) (updN ls0 l n) ms X s c := by
  refine ⟨fun L hL => ?_, fun hL => ((h _ hL).2 rfl).elim⟩
  rcases (h L hL).1 with hoff | ⟨hlo, hhi⟩
  · exact .inr (.inl hoff)
  · exact .inr (.inr (.inl ⟨l, b, by simp [A64ConsumerA.upd], by simp [lrange, updN, Range.contains]; omega⟩))

/-- **The abort sites at a pair after the allocation**: the write abort's,
in its phase `Ab`; the overflow's, its control ready with small
environments; or the heap's, its obligation met at the arena `ar`; the
exit status the abort status. -/
def AbortW1 (μ : Marks) (Ab : State → Prop) (ar : Arena) (s : State) (c : Spike.Lib.Ctl)
    (fs : List TermRun.Frame) : Prop :=
  ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus

/-- **The states after the allocation** of the fresh `l` at `b` with `n`
words: the state's facts at the write tail `Dt`, the write abort's phase
`Ab` kept, no `ret` of `main` at no frame, the control and the frames
placed at `upd Λ.static l b`, the writes off the arena or in `l`'s range
(`WrIn1`), the source's runs from the pair (`RunOk`), the abort sites
(`AbortW1`). -/
def W1 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (Tk Ab : State → Prop) (ar : Arena) (Dt : State → Prop)
    (l : WeakMem.AllocLabel) (b n : Nat) (p : Prog) (rS : Range) : FragS isaLSE2 := fun s c fs =>
  SFactsSt Λ μ own rS Tk s Dt ∧ AbSt μ Ab s ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧
    PlacedS Λ (A64ConsumerA.upd Λ.static l b) s c fs ∧ WrIn1 ar b n s ∧ RunOk p c fs ∧ AbortW1 μ Ab ar s c fs

/-- **`W1`'s `SFactsA`** at `upd Λ.static l b`, `updN lsize l n`, the
write tail `Dt` and the write abort's phase `Ab`. -/
theorem hW1 {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {lsize : Lsize} {I : InvS} :
    ∀ l b n s c fs, W1 Λ μ own Tk Ab ar Dt l b n p rS s c fs →
      SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar I (A64ConsumerA.upd Λ.static l b) (updN lsize l n) s c fs Dt
        Ab := by
  rintro l b n s c fs ⟨hst, has, hnr, hpl, hn, hr, hab⟩
  exact SFactsA.ofSt hst has hnr hr.cell (.of_placedS hpl) (fun _ _ _ _ => wrOkA_of_wrIn1 hn) hr.zero hab

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.W0G.hW0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hW0

/-- info: 'Spike.Lib.A64.W0G.wrOkA_of_wrIn1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wrOkA_of_wrIn1

/-- info: 'Spike.Lib.A64.W0G.hW1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hW1

end Spike.Lib.A64.W0G
