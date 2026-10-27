/-
**`hello1.w`'s states after the allocation at its nodes** (x86-64): `W1`
(`Spike/Test/X64Hello1W1.lean`) from a node lemma's `Wr` (`SFacts`) and the
per-state facts `Wr` does not carry; the after-allocation twin of
`w0_of_wr` (`Spike/Test/X64Hello1W0N.lean`).

- `w1_of_wr`: `W1 Dt l b n p rS` at a state of `Wr`, its frames placed at
  `upd hello1Λ.static l b` (a label the static placement does not place)
  with small environments, the write abort's phase kept, the source's runs,
  its writes off the arena or in `l`'s range (`WrIn`).
- `w1_of_st`: `W1` from the state's facts (`SFactsSt`, as `BlkW.st` and
  `NodeW.st` give them) and the control's.
-/
import Spike.Test.X64Hello1W1
import Spike.Test.X64Hello1W0N

namespace Spike.Test.X64Hello1W1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (FragS EnvSmall FrameRun Frag Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.SFactsN
open Spike.Test.X64ArenaHello1 (ar)
open SccCode (hello1Λ)

variable {p : Prog} {rS : Range} {Dt : State → Prop} {l : WeakMem.AllocLabel} {b n : Nat} {s : State}
  {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}

/-- **`W1` from `Wr`**: the frames placed at `upd hello1Λ.static l b` (`l`
not statically placed, so `Wr`'s static placement grows to it) with small
environments, the write abort's phase kept, the source's runs from the
pair, the writes off the arena or in `l`'s range. -/
theorem w1_of_wr (h : Wr rS s c) (hl : hello1Λ.static l = none)
    (hfp : FramesPlaced hello1Λ (upd hello1Λ.static l b) s fs) (hes : ∀ f ∈ fs, EnvSmall f.env)
    (hab : AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s) (hrun : RunOk p c fs) (hwr : WrIn ar b n s) :
    W1 Dt l b n p rS s c fs :=
  ⟨(SFacts.dt_mono (Dt' := Dt) h fun _ h => h.elim).toSt, hab, fun _ => h.noRet,
    PlacedS.ofFrames (Placed.mono (static_le_upd hl) h.place) hfp, hwr, hrun, fun k a ha hpc => by
      obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
      exact ⟨.inr (.inl ⟨hk, ho, he, hes⟩), hx⟩⟩

/-- **`W1` from the state's facts** (`SFactsSt` at no write tail) and the
control's: no `ret` of `main` at no frame, placed with its frames at
`upd hello1Λ.static l b`; the write abort's phase kept, the writes off the
arena or in `l`'s range, the source's runs, the abort sites. -/
theorem w1_of_st (h : SFactsSt hello1Λ μ0 own rS Tk s) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hpl : PlacedS hello1Λ (upd hello1Λ.static l b) s c fs) (hab : AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s)
    (hwr : WrIn ar b n s) (hrun : RunOk p c fs) (hao : AbortW1 μ0 (Spike.Lib.X64.WriteAb.Ab labT) s c fs) :
    W1 Dt l b n p rS s c fs :=
  ⟨{ h with wrTail := fun h1 _ _ _ h2 => (h.wrTail h1 _ _ _ h2).elim }, hab, hnr, hpl, hwr, hrun, hao⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64Hello1W1.w1_of_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w1_of_wr

/-- info: 'Spike.Test.X64Hello1W1.w1_of_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w1_of_st

end Spike.Test.X64Hello1W1
