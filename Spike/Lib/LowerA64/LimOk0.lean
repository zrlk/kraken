/-
**The stack-limit word's facts from the placement check** (AArch64): the
`LimOk` premises of a stack-checked prologue (`mainCtxB`'s `hL`,
`proEdge2_ofCallee`'s `hlim`) at the first thread's TCB.

`LimOk ms F exe endPc a Z` needs four facts of the limit word `a = limA tp`:

- `rt`: `a` is a runtime word (not under a label: `RtFree`);
- `mp`: `a` is mapped for a read (`mp_rt`, the layout's `words_mapped`);
- `unmapped`: under the frame condition `F`, thread-private memory has no
  value at `a` (`F` within `rtF`);
- `room`: every value the value invariant allows at `a` is at most `Z`.
  At the placement's invariant `G0` the word holds the first stack's limit
  `stacksA + 4096` or its initial `0` (`room_of_le`), so any `Z` at least
  the limit has room.

The first three do not depend on `Z`, so at every depth only the bound
`stacksA + 4096 ≤ Z` and `F ⊆ rtF` remain.

- `limOk_tpidr`: the limit word at a state's `TPIDR_EL0`, the first
  thread's pointer, is `limA` of it (`proEdge2_ofCallee`'s address form).
- `limOk_msOfS`: `LimOk` at the memory side at any frames from any other.
- `limOk0_ofPlaceOK`: `LimOk` at the first TCB's limit word at the
  placement's memory side at the empty frame list, for any `Z` past the
  limit.
- `limOk0_ofPlaceOK_none`: the same with no static label (`RtFree` from
  `rtFree_none`).
- `limOk_callee_ofPlaceOK`: `proEdge2_ofCallee`'s `hlim` at a state of the
  first thread at any frames, given the new frame's `sp` past the limit
  (the remaining stack-depth fact).
-/
import Spike.Lib.LowerA64.MainC
import Spike.Lib.LowerA64.CorrectS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (msOfS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.PhRec (μ)

/-- **The limit word at a state's `TPIDR_EL0`**: at the thread pointer
`tp`, `proEdge2_ofCallee`'s address form of `LimOk` is `limA tp`'s. -/
theorem limOk_tpidr {ms : MemSide isaLSE2} {F : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {Z : BitVec 64} {σ : AS} {tp : UInt64} (htp : σ.regs.TPIDR_EL0 = tp)
    (h : Ret0.LimOk ms F exe endPc (Ret0.limA tp) Z) :
    Ret0.LimOk ms F exe endPc (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) Z := by
  rw [show tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit) = Ret0.limA tp from Ret0.tcbA_limA htp]
  exact h

/-- **`LimOk` does not depend on the frames**: the memory side at the frames
(`msOfS`) changes only ownership and placement, not the runtime words, the
mapping or the value invariant. -/
theorem limOk_msOfS {Λ : Scc.Sem.Layout} {μ' : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {lbl : Spike.Lib.A64Consumer.Lbl} {lsize : Spike.Lib.A64Consumer.Lsize}
    {fs fs' : List TermRun.Frame} {F : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {a Z : BitVec 64} (h : Ret0.LimOk (msOfS Λ μ' rd G own lbl lsize fs) F exe endPc a Z) :
    Ret0.LimOk (msOfS Λ μ' rd G own lbl lsize fs') F exe endPc a Z :=
  ⟨h.rt, h.mp, h.unmapped, h.room⟩

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : Prog}

set_option quotPrecheck false

/-- The lowering's output. -/
local notation "O" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

/-- The runtime's layout of the output, at the lowering's immediates. -/
local notation "Ly" h => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms1Of p)

/-- The value invariant: the first TCB's limit word holds its loaded value or the limit. -/
local notation "G0" h:max => Spike.Lib.A64.PhRec.GOf (Ly h) (Spike.Lib.A64.PhRec.m0Of (Ly h).Λ (O).prog (O).secs)

/-- The placement's memory side at the frames. -/
local notation "MSS" h:max => msOfS (Ly h).Λ (μ (Ly h)) (fun _ => True) (G0 h)
  (fun s _ => Spike.Lib.A64.PhRec.own (Ly h) s) (Ly h).Λ.static (fun _ => 0)

/-- The first thread's pointer. -/
local notation "TP0" h:max => UInt64.ofBitVec (Ret0.pinA (Ly h).lab + 0#64 + 8#64)

/-- **The first TCB's limit word's facts at depth `0`** (`mainCtxB`'s `hL`):
at the placement's memory side at no frames, under a frame condition within
`rtF` (`hF`), for any bound `Z` at least the first stack's limit `stacksA +
4096` (`hZ`), given no label covers a runtime word (`hfree`). -/
theorem limOk0_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly h) (Ly h).Λ.static (fun _ => 0))
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly h) m)
    {Z : BitVec 64} (hZ : (Ly h).stacksA.toNat + 4096 ≤ Z.toNat) :
    Ret0.LimOk ((MSS h) []) F (Ly h).exe (Ly h).endPc (Ret0.limA (TP0 h)) Z := by
  rw [msOfS_nil]
  have e : TP0 h = UInt64.ofBitVec ((Ly h).pinA + 0#64 + 8#64) := by
    rw [Spike.Lib.A64.Rt.pinA_lab0 (Ly h)]
  rw [e]
  exact (Spike.Lib.A64.Rt.rt_limOk (L := Ly h) hfree fun v hv =>
    Nat.le_trans (Spike.Lib.A64.PhRec.room_of_le h (Scc.Lower.imms1Of p) (Nat.le_refl _) v hv) hZ).mono hF

/-- **`limOk0_ofPlaceOK` with no static label.** -/
theorem limOk0_ofPlaceOK_none {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hs : ∀ l, (Ly h).Λ.static l = none)
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly h) m)
    {Z : BitVec 64} (hZ : (Ly h).stacksA.toNat + 4096 ≤ Z.toNat) :
    Ret0.LimOk ((MSS h) []) F (Ly h).exe (Ly h).endPc (Ret0.limA (TP0 h)) Z :=
  limOk0_ofPlaceOK h (Spike.Lib.A64.Rt.rtFree_none _ hs) hF hZ

/-- **A stack-checked prologue's limit facts at the first thread, from the
placement check** (`proEdge2_ofCallee`'s `hlim` at a state): at any frames
`fs`, at a state whose `TPIDR_EL0` is the first thread's pointer (`htp`),
the new frame's `sp` (`sp` less the frame `fsz`) at least the first stack's
limit (`hZ`). -/
theorem limOk_callee_ofPlaceOK {Λ : Scc.Sem.Layout} (h : placeOKAt pcfg Λ (O) = true)
    (hfree : Spike.Lib.A64.Rt.RtFree (Ly h) (Ly h).Λ.static (fun _ => 0))
    {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly h) m) (fs : List TermRun.Frame)
    {σ : AS} (htp : σ.regs.TPIDR_EL0 = TP0 h) {fsz : Int}
    (hZ : (Ly h).stacksA.toNat + 4096 ≤ (σ.regs.SP.toBitVec - (Int64.ofInt fsz).toBitVec).toNat) :
    Ret0.LimOk ((MSS h) fs) F (Ly h).exe (Ly h).endPc (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit))
      (σ.regs.SP.toBitVec - (Int64.ofInt fsz).toBitVec) :=
  limOk_tpidr htp (limOk_msOfS (limOk0_ofPlaceOK h hfree hF hZ))

end Place

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.limOk0_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limOk0_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.limOk_callee_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limOk_callee_ofPlaceOK
