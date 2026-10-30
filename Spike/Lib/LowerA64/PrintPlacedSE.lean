/-
**`print`'s states at `PlacedSE`** (AArch64; the twin of
`Spike/Lib/LowerX64/PrintPlacedSE.lean`): the placement premises `hP` of
`printBlkW_w2C` (`Spike/Lib/LowerA64/PrintArgW2.lean`) and `hpl` of
`printW2`, `printSvc_w2` (`Spike/Lib/LowerA64/PrintW2.lean`), at the right
disjunct of `PlacedSE`: the source's control inside the call of `print` is
at a model term of the output extern (`Scc.Sem.externModelTerms`: `print`'s
body, `printL`'s loop top) or reads no variable, and the suspended frames
(`printFrame :: fs`) are placed under the frame condition (`hfp`, as
`blkW_placedS`'s).

- `printBody_ext`: `print`'s body is a model term;
- `PlacedSE.of_printTop`, `printC_top`: a control of `printL`'s body (every
  `PrintC`) at `PlacedSE`, the suspended frames placed;
- `BlkW.ofJF`, `PrintAW.ofJF`: a block's (`print`'s) obligation read off the
  node's control and the frame condition, kept off the region (`FStable`);
- `blkW_placedSE`: a block's states at `PlacedSE`, its controls at model
  terms (`printBlkW_w2C`'s `hP` at `printJ`'s `cE`);
- `blkW_placedSE'`, `BlkW.framesOfF`: the same with the frames placed
  only at the block's states (knowing the node's invariant);
- `printAW_placedSE`: `print`'s states at `PlacedSE` (`printW2`'s `hpl`);
- `printSvc_placedSE`: at `print`'s system call (`printSvc_w2`'s `hpl`).
-/
import Spike.Lib.LowerA64.PrintArgW2
import Spike.Lib.PrintTopExt
import Spike.Lib.A64FramesPlacedI

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At AS FStable)
open Spike.Lib.A64.Flow.PrintCall (pN pcS)
open Spike.Lib.PrintSrc (PrintC printN)
open Spike.Lib.PrintSvc (PrintTop printTop_ext self_mem_printTerms)
open Spike.Lib.A64.PrintA (PrintAW N)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **`print`'s body is a model term** of the output extern. -/
theorem printBody_ext : Spike.Lib.PrintSrc.printBody ∈ externModelTerms := by
  have e : Scc.Frontend.printBody = Spike.Lib.PrintSrc.printBody := rfl
  unfold externModelTerms
  rw [e]
  exact List.mem_append_left _ (by simp [Spike.Lib.PrintSrc.printBody, modelTerms])

/-- **A control of `printL`'s body is at `PlacedSE`**, the suspended frames
placed. -/
theorem _root_.Spike.Lib.A64ConsumerS.PlacedSE.of_printTop (h : PrintTop c) (hf : FramesPlaced Λ lbl s fs) :
    PlacedSE Λ lbl s c fs :=
  .of_ext (printTop_ext h) hf

/-- **`printL`'s loop top is in its body.** -/
theorem printC_top {pw wn : TermRun.Word} {n m k : Nat} (h : PrintC pw wn n m k c) : PrintTop c := by
  obtain ⟨_, _, ht, -⟩ := h
  unfold PrintTop
  rw [ht]
  exact self_mem_printTerms _

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A block whose obligation reads the node's control and the frame
condition**, kept off the region (`FStable`). -/
theorem BlkW.ofJF (hFS : FStable R F) {n : ND} {blk : List Directive} {V : State → Ctl → Prop}
    (h : ∀ σ c s, n.J σ c → F s.st.1 → V s c) : BlkW V (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ hF hJ _ _ _ _ hD => ⟨h σ c _ hJ (hFS _ _ hF hD), fun _ hk => hk⟩

/-- A node whose obligation reads the node's control and the frame
condition only (`BlkW.ofJF`'s node twin; `At` holds the frame condition). -/
theorem NodeW.ofJF {n : ND} {V : State → Ctl → Prop} (h : ∀ σ c s, n.J σ c → F s.st.1 → V s c) :
    NodeW V (fun _ _ => False) exe endPc R F n :=
  fun s c ⟨_, _, _, _, σ, _, hF, hJ⟩ => ⟨h σ c s hJ hF, fun _ hk => hk⟩

/-- **A block's states at `PlacedSE`**: the node's controls at model terms
of the output extern or reading no variable (`hext`), the suspended frames
placed at every state of the frame condition (`hfp`, kept off the region,
`FStable`). -/
theorem blkW_placedSE (hFS : FStable R F) {n : ND} {blk : List Directive}
    (hext : ∀ σ c, n.J σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk :=
  BlkW.ofJF hFS fun σ c s hJ hF => .of_ext (hext σ c hJ) (hfp s hF).choose_spec.toFramesPlaced

/-- **A block's states at `PlacedSE`, the frames placed knowing the
block** (`blkW_placedSE` with `hfp` asked only at the block's states, which
carry the node's invariant and the abstract state, e.g. the caller's frame
in its slots): the node's controls at model terms of the output extern or
reading no variable (`hext`), the suspended frames placed at every state of
the block (`hfpJ`). -/
theorem blkW_placedSE' {n : ND} {blk : List Directive}
    (hext : ∀ σ c, n.J σ c → c.term ∈ externModelTerms ∨ exprFv c.term = [])
    (hfpJ : BlkW (fun s _ => ∃ B, FramesPlacedInI Λ lbl s fs B) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJ k hk m hA' hD =>
    ⟨.of_ext (hext σ c hJ) (hfpJ s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1.choose_spec.toFramesPlaced,
      fun _ h => h⟩

/-- **The frames placed under the frame condition are placed at a block's
states** (`blkW_placedSE`'s `hfp` gives `blkW_placedSE'`'s `hfpJ`). -/
theorem BlkW.framesOfF (hFS : FStable R F) {n : ND} {blk : List Directive}
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    BlkW (fun s _ => ∃ B, FramesPlacedInI Λ lbl s fs B) (fun _ _ => False) exe endPc R F n blk :=
  BlkW.ofJF hFS fun _ _ s _ hF => hfp s hF

variable {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- **`print` inside a predicate of the node's control and the frame
condition**, not moved (`PrintAW.ofJ` with the frame condition). -/
theorem _root_.Spike.Lib.A64.PrintA.PrintAW.ofJF (hFS : FStable R F) {V : State → Ctl → Prop}
    (h : ∀ j c s, P j c ∨ Q j c → F s.st.1 → V s c) :
    PrintAW x29 ra buf0 len0 P Q V (fun _ _ => False) exe endPc R F := by
  have hJ : ∀ n σ c s, (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q n).J σ c → F s.st.1 → V s c :=
    fun n σ c s hn hF => let ⟨j, hj⟩ := N_pq n hn; h j c s hj hF
  exact ⟨BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _),
    NodeW.ofJF (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _),
    BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _),
    BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _), BlkW.ofJF hFS (hJ _)⟩

/-- **`print`'s states at `PlacedSE`** (`printW2`'s `hpl`): the source's
`P`, `Q` controls in `printL`'s body (`hPQ`, e.g. `printC_top`), the
suspended frames placed at every state of the frame condition (`hfp`). -/
theorem printAW_placedSE (hFS : FStable R F) (hPQ : ∀ j c, P j c ∨ Q j c → PrintTop c)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) :
    PrintAW x29 ra buf0 len0 P Q (fun s c => PlacedSE Λ lbl s c fs) (fun _ _ => False) exe endPc R F :=
  PrintAW.ofJF hFS fun j c s hj hF => .of_printTop (hPQ j c hj) (hfp s hF).choose_spec.toFramesPlaced

/-- **At `print`'s system call the state is at `PlacedSE`**
(`printSvc_w2`'s `hpl`): the source at `printL`'s loop top
(`printSys_src`), the suspended frames placed at the call's frame
condition (`hfp`). -/
theorem printSvc_placedSE {R' : Region} {F' : MachineData → Prop} {σC : AS} {pw wn : TermRun.Word}
    {nv mv : Nat}
    (hAt : At exe endPc R' F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c)
    (hN : σC.regs.X1.toBitVec.toNat = printN nv mv)
    (hfp : ∀ s : State, F' s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B) : PlacedSE Λ lbl s c fs := by
  obtain ⟨k, hk, -⟩ := printSys_src hAt hN
  obtain ⟨-, -, -, -, -, -, hF, -⟩ := hAt
  exact .of_printTop (printC_top hk) (hfp s hF).choose_spec.toFramesPlaced

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.printAW_placedSE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printAW_placedSE

/-- info: 'Spike.Lib.LowerA64.printSvc_placedSE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printSvc_placedSE

/-- info: 'Spike.Lib.LowerA64.blkW_placedSE'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_placedSE'
