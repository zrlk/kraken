/-
**`hello1.x`'s states after the allocation** (`W1`): the fragment the
levels' cut B (`hello1_correctKLS_levelsB`, `Spike/Test/X64Hello1LevelsB.lean`)
takes its segments under for the fresh label `l` placed at `b` with `n`
words, and its `SFactsA` (`hW1`). The sibling of `W0`
(`Spike/Test/X64Hello1W0.lean`).

- `WrIn ar b n s`: every location the instruction writes is off the arena or
  inside `[b, b + 8 n)` (the new label's range), and not the counter word.
  `wrOkA_of_wrIn`: `WrOkA` at the placement placing `l` at `b` with `n`
  words, any memory side and landing; `wrIn_of_noArenaWr`.
- `AbortW1`: the abort sites, with the write abort's (`Ab` its phase).
- `W1 Dt l b n p rS`: the state's facts at the write tail `Dt`, the write
  abort's phase kept (`AbSt` at `WriteAb.Ab labT`), no `ret` of `main` at
  no frame, the control and frames placed at `upd hello1Λ.static l b`, the
  writes in `WrIn`, the source's runs from the pair (`RunOk`) and the abort
  sites (`AbortW1`). Nothing of the levels' invariants.
- `hW1`: `SFactsA` at `upd hello1Λ.static l b`, `updN lsize l n`, the
  write tail `Dt`, the write abort's phase, from `SFactsA.ofSt`.
-/
import Spike.Test.X64Hello1SFactsN
import Spike.Test.X64Hello1RtW
import Spike.Lib.X64WriteAb

namespace Spike.Test.X64Hello1W1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (FragS OvfReady HeapAbortObl Arena)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.SFactsN
open Spike.Test.X64Hello1Load (hello1M0)
open Spike.Test.X64ArenaHello1 (ar)
open Spike.Test.X64Hello1CorrectA (Ih)
open SccCode (hello1Λ hello1Cells hello1Asm)

/-- **The writes after the allocation of `n` words at `b`**: every
location the instruction writes is off the arena or inside `[b, b + 8 n)`,
and not the counter word. -/
def WrIn (ar : Arena) (b n : Nat) (s : State) : Prop :=
  ∀ L, WrAt s L → (¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) ∨
    (b ≤ L.addr.toNat ∧ L.addr.toNat < b + 8 * n)) ∧ L ≠ ar.ctrLoc

/-- **`WrOkA` from `WrIn`** at the placement placing `l` at `b` with `n`
words, any memory side and landing: an off-arena write is `ArenaW`'s
off-arena case, one in `[b, b + 8 n)` its placed label's at `l`. -/
theorem wrOkA_of_wrIn {ar : Arena} {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    {ms : Spike.Lib.MemSide isa} {X : Spike.Lib.Frag isa} {s : State} {c : Spike.Lib.Ctl} (h : WrIn ar b n s) :
    WrOkA ar (upd L0 l b) (updN ls0 l n) ms X s c := by
  refine ⟨fun L hL => ?_, fun hL => ((h _ hL).2 rfl).elim⟩
  rcases (h L hL).1 with hoff | ⟨hlo, hhi⟩
  · exact .inr (.inl hoff)
  · exact .inr (.inr (.inl ⟨l, b, by simp [upd], by simp [lrange, updN, Range.contains]; omega⟩))

/-- Writes off the arena are in `WrIn`. -/
theorem wrIn_of_noArenaWr {ar : Arena} {b n : Nat} {s : State} (h : NoArenaWr ar s) : WrIn ar b n s :=
  fun L hL => ⟨.inl (h L hL).1, (h L hL).2⟩

/-- **The abort sites at a pair after the allocation**: the write abort's,
in its phase `Ab`; the overflow's, its control ready with small
environments; or the heap's, its obligation met; the exit status the abort
status. -/
def AbortW1 (μ : Marks) (Ab : State → Prop) (s : State) (c : Spike.Lib.Ctl) (fs : List TermRun.Frame) : Prop :=
  ∀ k a, μ.abortAt k = some a → pcOf s = a →
    ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
      (k = .heap ∧ HeapAbortObl ar.cells ar.ctr c)) ∧
      ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus

/-- **`hello1.x`'s states after the allocation** of the fresh `l` at `b`
with `n` words: the state's facts at the write tail `Dt`, the write
abort's phase kept (`AbSt` at `WriteAb.Ab`), no `ret` of `main` at no
frame, the control and the frames placed at `upd hello1Λ.static l b`, the
writes off the arena or in `l`'s range (`WrIn`), the source's runs from the
pair (`RunOk`), the abort sites (`AbortW1`). -/
def W1 (Dt : State → Prop) (l : WeakMem.AllocLabel) (b n : Nat) (p : Prog) (rS : Range) : FragS isa :=
  fun s c fs =>
    SFactsSt hello1Λ μ0 own rS Tk s Dt ∧ AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s ∧
      (fs = [] → ∀ a, c.term ≠ .ret a) ∧ PlacedS hello1Λ (upd hello1Λ.static l b) s c fs ∧ WrIn ar b n s ∧
      RunOk p c fs ∧ AbortW1 μ0 (Spike.Lib.X64.WriteAb.Ab labT) s c fs

/-- **`W1`'s `SFactsA`**, the levels' `hW1`, at the write tail `Dt` and
the write abort's phase `WriteAb.Ab`. -/
theorem hW1 {p : Prog} {rd : TermRun.Word → Prop} {Fix : List (Nat × Val)} {lsize : Lsize} {rS : Range}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (hpa : cellsOf hello1Asm = some hello1Cells) :
    ∀ l b n s c fs, W1 Dt l b n p rS s c fs →
      SFactsA hello1Λ (T.marks hello1Asm hello1Λ) p rd (FixG Fix hello1M0) (fun s _ => own s) rS Tk ar
        (Ih lsize inv0 inv1) (upd hello1Λ.static l b) (updN lsize l n) s c fs Dt
        (Spike.Lib.X64.WriteAb.Ab labT) := by
  rintro l b n s c fs ⟨hst, has, hnr, hpl, hn, hr, hab⟩
  rw [hello1_marks hpa]
  exact SFactsA.ofSt hst has hnr hr.cell (.of_placedS hpl) (fun _ _ _ _ => wrOkA_of_wrIn hn) hr.zero hab

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1W1.wrOkA_of_wrIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wrOkA_of_wrIn

/--
info: 'Spike.Test.X64Hello1W1.hW1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hW1

end Spike.Test.X64Hello1W1
