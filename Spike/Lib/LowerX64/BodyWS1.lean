/-
**An `Accepted1` body's blocks inside the consumer's facts at depth**
(x86-64, H7a calls): `BodyW0` (`Spike/Lib/LowerX64/BodyW.lean`) over the
source's real pairs with frames, the facts at the held-back pair `(c0, [])`
(`c_design.md`'s lag of the whole user code), and its lag (`SegWS.lag`).

- `BodyWS0`: at a real pair `(c, fs)` a frame run of the program reaches
  (`Good1`), with no hold, the state in `SFactsS` at `(c0, [])` (the owned
  words not depending on the frames).
- `blkW_bodyS1`: a construct's block at `Cd1` at any node with the frame's
  offsets whose pairs at the frames `fs` are `Good1` with no hold, the saved
  pair in their cells, is inside `BodyWS0` at `fs` (`blkW_body1` at the
  held-back control, `SFactsS.ofSFacts0`).
- `bodyWS0_lag`: a segment inside `BodyWS0` with the pairs held back at
  `(c0, [])` is inside `SFactsS` (`SegWS.lag` with `C := (· = c0)`).
-/
import Spike.Lib.LowerX64.BodyW1
import Spike.Lib.X64SFactsS1

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl)
open Spike.Lib.X64ConsumerS (SFactsS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)

/-- **The body's fragment at depth before the lag**: a pair a frame run of
`p` reaches (`Good1`), its control holding nothing, the state in `SFactsS`
at the function's entry control `c0` with no frame. -/
def BodyWS0 (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (own : Own) (rS : Range) (Tk : State → Prop) (lbl : Lbl)
    (cells ctr : Nat) (c0 : Ctl) : FragS isa :=
  fun s c fs => Good1 p (c, fs) ∧ c.hold = none ∧ SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cells ctr s c0 []

/-- **The lag of a segment inside `BodyWS0`**: with the pairs held back at
`(c0, [])`, the segment is inside `SFactsS` at the empty frames
(`SegWS.lag`, `C := (· = c0)`), under memory sides agreeing with depth 0's
(`hms`) whose kernel model is `Scc.Sem.X64.abi` (`hK`: `SFactsS`' default
write tail rules out a `write`), the words owned at the frames a run reaches
owned at depth 0 where a row reads the runtime's memory (`hown`, e.g.
`ownIncl_of_indep` for owned words not depending on the frames). -/
theorem bodyWS0_lag {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {own : Own} {rS : Range} {Tk : State → Prop}
    {lbl : Lbl} {cells ctr : Nat} {c0 : Ctl} {K : State → State → Prop} {al : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {P Q : FragS isa} (hp : Scc.Lower.Accepted1 p = true)
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hms : MsAgree ms)
    (hown : ∀ s c fs, BodyWS0 Λ μ p own rS Tk lbl cells ctr c0 s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms []).own s)
    (h : SegWS (BodyWS0 Λ μ p own rS Tk lbl cells ctr c0) K p al ms P Q) :
    SegWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cells ctr s c fs) K p al ms
      (LagS p (· = c0) P) (LagS p (· = c0) Q) :=
  h.lag (fun _ _ _ h _ _ hr => Good1.quiet_run hp h.1 h.2.1 hr)
    (fun _ _ _ h K' hK' ha buf n hd => by
      rw [hK] at hK'; cases hK'
      exact h.2.2.wrTail ha 1 buf n hd)
    hms hown fun _ _ _ _ h _ hc => hc ▸ h.2.2

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl} {fr : Scc.Emit.X64.Frame}
  {fp ra : BitVec 64}

/-- **A construct's block of an `Accepted1` body is inside `BodyWS0`** at
the frames `fs`, at any node with the frame's offsets (`hno`) whose pairs at
`fs` are `Good1` with no hold, the saved pair in their cells (`hJ`): the
block at `Cd1` (`blkW_body1` at the held-back control `c0`, whose runs are
`Quiet` by `Good1.quiet_run`), the facts at `c0` lifted to `SFactsS` at the
empty frames (`SFactsS.ofSFacts0`, `c0` `Good1` with no frame). -/
theorem blkW_bodyS1 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hf : FrameOk fr)
    (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) (hh0 : c0.hold = none) {cl ctr : Nat} {fs : List TermRun.Frame}
    {n : ND} (hno : n.o = oB fr) (hJ : ∀ σ c, n.J σ c → (Good1 p (c, fs) ∧ c.hold = none) ∧ FrJ fp ra σ.slot)
    {blk : List (Directive × Nat)} (hcd : Cd1 cells okPc ph lab fr (Int64.ofBitVec ra) n.pc blk) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n blk := by
  let n₂ : ND := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
  have H := blkW_body1 (n := n₂) (p := p) hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hC0
    (fun _ hr => Good1.quiet_run hp hg0 hh0 (FrameRun.ofLocal hr []))
    hno (fun σ c ⟨hc, c1, hJ1⟩ => ⟨hc ▸ .refl _, (hJ σ c1 hJ1).2⟩) hcd
  intro s σ c he hn hd hpc hA hF hJn k hk m hA' hD
  obtain ⟨⟨-, hW⟩, hK⟩ := H s σ c0 he hn hd hpc hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨(hJ σ c hJn).1.1, (hJ σ c hJn).1.2, SFactsS.ofSFacts0 hW hp hg0⟩, hK⟩

end W

end Spike.Lib.LowerX64
