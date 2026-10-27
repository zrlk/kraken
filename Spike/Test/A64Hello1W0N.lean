/-
**`hello1.w`'s states before the allocation at its nodes** (AArch64): `W0`
(`Spike/Test/A64Hello1W0.lean`) from a node lemma's `Wr` (`SFacts`) and the
per-state facts `Wr` does not carry.

- `w0_of_wr`: `W0 p rS Dt Ctx` at a state of `Wr`, its frames placed with small
  environments, the write abort's phase kept, the source's runs, its writes
  off the counter off the arena, a counter write in the context.
- `dumN`, `BlkW.st`, `NodeW.st`: the state's facts (`SFactsSt`) at a node's
  states at any control, from `Wr` at the source start's control (`Wr`'s
  `CFacts` fail at `rodata`'s allocation, a `newBuf`); `w0_of_st`: `W0`
  from them and the control's facts.
- `NodeW.imp`, `BlkW.imp`, `ProW.imp`, `AllocW.imp`, `RdPreW.imp`,
  `MainPreW.imp`: an obligation inside `W` from one inside `W1` (with the
  outside moves) and one inside `W2` (none), `W1 ∧ W2` inside `W`.
-/
import Spike.Test.A64Hello1W0

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (FragS EnvSmall FrameRun Frag MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW At ND AS)
open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.SFactsN
open Spike.Lib (Region)
open Spike.Test.A64ArenaHello1 (ar)
open SccCode (hello1Λ hello1Prog hello1Asm)

variable {p : Prog} {rS : Range} {Dt : State → Prop} {Ctx : FragS isaLSE2} {s : State} {c : Spike.Lib.Ctl}
  {fs : List TermRun.Frame}

/-- **`W0` from `Wr`**: the frames placed at the static placement with small
environments, the write abort's phase kept, the source's runs from the
pair, the writes off the counter off the arena, a counter write in the
context `Ctx`. -/
theorem w0_of_wr (h : Wr rS s c) (hfp : FramesPlaced hello1Λ hello1Λ.static s fs)
    (hes : ∀ f ∈ fs, EnvSmall f.env) (hab : AbSt μ0 (Spike.Lib.A64.WriteAb.Ab labT) s) (hrun : RunOk p c fs)
    (hwr : ∀ L, WrAt s L → L ≠ ar.ctrLoc → ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells))
    (hcx : WrAt s ar.ctrLoc → Ctx s c fs) : W0 p rS Dt Ctx s c fs :=
  ⟨(SFacts.dt_mono (Dt' := Dt) h fun _ h => h.elim).toSt, hab, fun _ => h.noRet, PlacedS.ofFrames h.place hfp,
    fun _ _ _ L hL hne _ => .inr (.inl (hwr L hL hne)), hcx, hrun, fun k a ha hpc => by
      obtain ⟨hk, ho, he, hx⟩ := h.abortOk k a ha hpc
      exact ⟨.inl ⟨hk, ho, he, hes⟩, hx⟩⟩

/-! ## Two node obligations into one -/

section Imp

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W1 W2 : Frag isaLSE2} {K : State → State → Prop}

/-- **A node inside `W`** from one inside `W1` not moved by `K` and one
inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem NodeW.imp {n : ND} (h1 : NodeW W1 K exe endPc R F n) (h2 : NodeW W2 (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : NodeW W K exe endPc R F n := fun s c hA =>
  ⟨hw s c (h1 s c hA).1 (h2 s c hA).1, (h1 s c hA).2⟩

/-- **A block node inside `W`** from one inside `W1` not moved by `K` and
one inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem BlkW.imp {n : ND} {blk : List Directive} (h1 : BlkW W1 K exe endPc R F n blk)
    (h2 : BlkW W2 (fun _ _ => False) exe endPc R F n blk) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    BlkW W K exe endPc R F n blk := fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
  ⟨hw _ c (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1 (h2 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
    (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩

/-- **A prologue inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem ProW.imp {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Spike.Lib.Ctl → Prop} (h1 : Spike.Lib.A64.Flow.ProW W1 K exe endPc R F ms pc0 Z lim L ps J)
    (h2 : Spike.Lib.A64.Flow.ProW W2 (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.A64.Flow.ProW W K exe endPc R F ms pc0 Z lim L ps J :=
  ⟨BlkW.imp h1.w0 h2.w0 hw, NodeW.imp h1.w1 h2.w1 hw, BlkW.imp h1.w2 h2.w2 hw, BlkW.imp h1.w3 h2.w3 hw⟩

/-- **`scc_rt_alloc` inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem AllocW.imp {ms : MemSide isaLSE2} {q : Spike.Lib.A64.Alloc.Call}
    (h1 : Spike.Lib.A64.Alloc.AllocW ms q W1 K exe endPc R F)
    (h2 : Spike.Lib.A64.Alloc.AllocW ms q W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.A64.Alloc.AllocW ms q W K exe endPc R F :=
  ⟨BlkW.imp h1.e h2.e hw, BlkW.imp h1.entry h2.entry hw, BlkW.imp h1.n2 h2.n2 hw, NodeW.imp h1.cnt h2.cnt hw,
    NodeW.imp h1.cnt1 h2.cnt1 hw, BlkW.imp h1.cnt2 h2.cnt2 hw, NodeW.imp h1.rmw h2.rmw hw,
    BlkW.imp h1.n4 h2.n4 hw, BlkW.imp h1.n5 h2.n5 hw, BlkW.imp h1.slow h2.slow hw, BlkW.imp h1.n7 h2.n7 hw,
    BlkW.imp h1.full h2.full hw, BlkW.imp h1.ok h2.ok hw, NodeW.imp h1.ok1 h2.ok1 hw,
    NodeW.imp h1.ok2 h2.ok2 hw, BlkW.imp h1.n12 h2.n12 hw, NodeW.imp h1.hdr h2.hdr hw,
    BlkW.imp h1.n13 h2.n13 hw, NodeW.imp h1.ret h2.ret hw⟩

/-- **`wc_rodata` up to the allocator's return inside `W`** from two. -/
theorem RdPreW.imp {ms : MemSide isaLSE2} {J0 Jc : AS → Spike.Lib.Ctl → Prop}
    (h1 : Spike.Lib.A64.Flow.Hello1.RdPreW W1 K exe endPc R F ms J0 Jc)
    (h2 : Spike.Lib.A64.Flow.Hello1.RdPreW W2 (fun _ _ => False) exe endPc R F ms J0 Jc)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.A64.Flow.Hello1.RdPreW W K exe endPc R F ms J0 Jc :=
  ⟨ProW.imp h1.pro h2.pro hw, BlkW.imp h1.e h2.e hw, fun q hok hq =>
    AllocW.imp (h1.alloc q hok hq) (h2.alloc q hok hq) hw⟩

/-- **`scc_rt_main` up to the allocator's return inside `W`** from two. -/
theorem MainPreW.imp {ms : MemSide isaLSE2} {J : AS → Spike.Lib.Ctl → Prop}
    (h1 : Spike.Lib.A64.Flow.Hello1.MainPreW W1 K exe endPc R F ms J)
    (h2 : Spike.Lib.A64.Flow.Hello1.MainPreW W2 (fun _ _ => False) exe endPc R F ms J)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.A64.Flow.Hello1.MainPreW W K exe endPc R F ms J :=
  ⟨ProW.imp h1.pro h2.pro hw, BlkW.imp h1.call h2.call hw, fun m0 σC => RdPreW.imp (h1.rd m0 σC) (h2.rd m0 σC) hw⟩

end Imp

/-! ## The state's facts at any control -/

section St

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop}

/-- **A node at the source start's control** (`A64Consumer.c0`, whose
`CFacts` hold, `cfacts_c0`): `n`'s pc and offsets, for the abstract states
of `n`'s invariant. -/
def dumN (n : ND) : ND := ⟨n.pc, n.o, fun σ c' => c' = Spike.Lib.A64Consumer.c0 ∧ ∃ c, n.J σ c⟩

/-- **A block's states carry the state's facts** (`SFactsSt`) at any
control of `n`'s invariant, from `Wr` at the source start's control
(`dumN`, as `BlkW.mapC`): `SFacts`' state fields read no control. -/
theorem BlkW.st {n : ND} {blk : List Directive} (h : BlkW (Wr rS) K exe endPc R F (dumN n) blk) :
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
    (hpl : PlacedS hello1Λ hello1Λ.static s c fs) (hab : AbSt μ0 (Spike.Lib.A64.WriteAb.Ab labT) s)
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

/-- info: 'Spike.Test.A64Hello1W0.w0_of_wr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w0_of_wr

/-- info: 'Spike.Test.A64Hello1W0.NodeW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeW.imp

/-- info: 'Spike.Test.A64Hello1W0.BlkW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BlkW.imp

/-- info: 'Spike.Test.A64Hello1W0.ProW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ProW.imp

/-- info: 'Spike.Test.A64Hello1W0.AllocW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocW.imp

/-- info: 'Spike.Test.A64Hello1W0.RdPreW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RdPreW.imp

/-- info: 'Spike.Test.A64Hello1W0.MainPreW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MainPreW.imp

/-- info: 'Spike.Test.A64Hello1W0.BlkW.st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BlkW.st

/-- info: 'Spike.Test.A64Hello1W0.NodeW.st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms NodeW.st

/-- info: 'Spike.Test.A64Hello1W0.w0_of_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w0_of_st

end Spike.Test.A64Hello1W0
