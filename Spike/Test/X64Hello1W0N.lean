/-
**`hello1.w`'s states before the allocation at its nodes** (x86-64): `W0`
(`Spike/Test/X64Hello1W0.lean`) from a node lemma's `Wr` (`SFacts`) and the
per-state facts `Wr` does not carry. The twin of
`Spike/Test/A64Hello1W0N.lean`; the two-obligation lemmas (`NodeW.imp`, …)
are in `Spike/Lib/X64Hello1WImp.lean`.

- `w0_of_wr`: `W0 p rS Dt Ctx` at a state of `Wr`, its frames placed with small
  environments, the write abort's phase kept, the source's runs, its writes
  off the counter off the arena, a counter write in the context.
- `dumN`, `BlkW.st`, `NodeW.st`: the state's facts (`SFactsSt`) at a node's
  states at any control, from `Wr` at the source start's control (`Wr`'s
  `CFacts` fail at `rodata`'s allocation, a `newBuf`); `w0_of_st`: `W0`
  from them and the control's facts.
- `wr_of_noArenaWr`: `NoArenaWr`'s writes off the counter are off the arena.
-/
import Spike.Test.X64Hello1W0

namespace Spike.Test.X64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (FragS EnvSmall FrameRun Frag Region)
open Spike.Lib.X64 (NodeW BlkW At ND AS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.SFactsN
open Spike.Test.X64ArenaHello1 (ar)
open SccCode (hello1Λ)

variable {p : Prog} {rS : Range} {Dt : State → Prop} {Ctx : FragS isa} {s : State} {c : Spike.Lib.Ctl}
  {fs : List TermRun.Frame}

/-- **`W0` from `Wr`**: the frames placed at the static placement with small
environments, the write abort's phase kept, the source's runs from the
pair, the writes off the counter off the arena, a counter write in the
context `Ctx`. -/
theorem w0_of_wr (h : Wr rS s c) (hfp : FramesPlaced hello1Λ hello1Λ.static s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s) (hrun : RunOk p c fs)
    (hwr : ∀ L, WrAt s L → L ≠ ar.ctrLoc → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells))
    (hcx : WrAt s ar.ctrLoc → Ctx s c fs) : W0 p rS Dt Ctx s c fs :=
  ⟨(SFacts.dt_mono (Dt' := Dt) h fun _ h => h.elim).toSt, hab, fun _ => h.noRet, PlacedS.ofFrames h.place hfp,
    fun _ _ _ L hL hne _ => .inr (.inl (hwr L hL hne)), hcx, hrun, fun k a ha hpc => by
      obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
      exact ⟨.inl ⟨hk, ho, he, hes⟩, hx⟩⟩

/-! ## The state's facts at any control -/

section St

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop}

/-- **A node at the source start's control** (`X64Consumer.c0`, whose
`CFacts` hold, `cfacts_c0`): `n`'s pc and offsets, for the abstract states
of `n`'s invariant. -/
def dumN (n : ND) : ND := ⟨n.pc, n.o, fun σ c' => c' = Spike.Lib.X64Consumer.c0 ∧ ∃ c, n.J σ c⟩

/-- **A block's states carry the state's facts** (`SFactsSt`) at any
control of `n`'s invariant, from `Wr` at the source start's control
(`dumN`, as `BlkW.mapC`): `SFacts`' state fields read no control. -/
theorem BlkW.st {n : ND} {blk : List (Directive × Nat)} (h : BlkW (Wr rS) K exe endPc R F (dumN n) blk) :
    BlkW (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) K exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    let h' := h s σ _ he hn hd hp hA hF ⟨rfl, c, hJ⟩ k hk m hA' hD
    ⟨h'.1.toSt, h'.2⟩

/-- **A node's states carry the state's facts** (as `BlkW.st`). -/
theorem NodeW.st {n : ND} (h : NodeW (Wr rS) K exe endPc R F (dumN n)) :
    NodeW (fun s _ => SFactsSt hello1Λ μ0 own rS Tk s) K exe endPc R F n :=
  fun s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩ =>
    let h' := h s _ ⟨h1, h2, h3, h4, σ, hA, hF, rfl, c, hJ⟩
    ⟨h'.1.toSt, h'.2⟩

end St

/-- **`W0` from the state's facts** (`SFactsSt` at no write tail) and the
control's: no `ret` of `main` at no frame, placed with its frames, the
abort sites; the write abort's phase kept, the source's runs, the writes
off the counter off the arena, a counter write in the context `Ctx`. -/
theorem w0_of_st (h : SFactsSt hello1Λ μ0 own rS Tk s) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hpl : PlacedS hello1Λ hello1Λ.static s c fs) (hab : AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s)
    (hrun : RunOk p c fs)
    (hwr : ∀ L, WrAt s L → L ≠ ar.ctrLoc → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells))
    (hcx : WrAt s ar.ctrLoc → Ctx s c fs) (hao : AbortW μ0 s c fs) : W0 p rS Dt Ctx s c fs :=
  ⟨{ h with wrTail := fun h1 _ _ _ h2 => (h.wrTail h1 _ _ _ h2).elim }, hab, hnr, hpl,
    fun _ _ _ L hL hne _ => .inr (.inl (hwr L hL hne)), hcx, hrun, hao⟩

/-- `NoArenaWr`'s writes off the counter are off the arena. -/
theorem wr_of_noArenaWr (h : NoArenaWr ar s) :
    ∀ L, WrAt s L → L ≠ ar.ctrLoc → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells) :=
  fun L hL _ => (h L hL).1

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64Hello1W0.w0_of_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w0_of_wr

/-- info: 'Spike.Test.X64Hello1W0.wr_of_noArenaWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wr_of_noArenaWr

/-- info: 'Spike.Test.X64Hello1W0.BlkW.st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BlkW.st

/-- info: 'Spike.Test.X64Hello1W0.NodeW.st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeW.st

/-- info: 'Spike.Test.X64Hello1W0.w0_of_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w0_of_st

end Spike.Test.X64Hello1W0
