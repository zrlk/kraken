/-
**An `Accepted2` body's abort exits inside `W2`** (AArch64): the premises
of `ovfSeg2` and `heapAbSeg2` (`Spike/Lib/LowerA64/AbortSeg2.lean`) at
`W := W2 … fs` (`Spike/Lib/LowerA64/SFactsA2.lean`) and `K := TakeK a rS`.
The twin of `Spike/Lib/LowerX64/AbortW2.lean`.

The abort paths' states have the consumer's facts from the stubs' proofs
(`stubW_sfacts`'s `SFacts`, `stubHW_sfactsA`'s `SFactsA` with no phase);
`W2` adds the write abort's phase kept (`AbSt`, a premise per node:
`StubOAb`, `StubHAb`), the suspended frames placed, no write of the arena
and no output `write(1, …)` (from the code: a covered block is off a system
call and writes nothing, the stubs' `write` is to the error output, their
exit call is `exit_group`).

- `NoW1`, `AbPartW2`, `CtlW2`: the part of `W2` at an abort path's state
  `SFacts` does not give, and the source control's;
- `w2_of_sfacts`, `BlkW.w2_sfacts`, `NodeW.w2_sfacts`: `W2` from `SFacts`;
- `w2_of_sfactsA`, `BlkW.w2_sfactsA`, `NodeW.w2_sfactsA`: `W2` from
  `SFactsA` with no phase;
- `ovf_hKR_take`: `ovfSeg2`'s `hKR` at `TakeK` (its `hFK` is
  `Ret0.TakeK.kstable`);
- `blkW_framesPlaced`, `nodeW_framesPlaced`: the suspended frames placed on a block, a node;
- `ovf_hW_w2`: `ovfSeg2`'s `hW`, the function's overflow block inside `W2`;
- `blkW_abPartW2`, `nodeW_abPartW2_si`, `nodeW_abPartW2_svc`, `blkW_abNoW1`, `nodeW_abNoW1_si`,
  `svcCall_ne_write1`, `svcCall_ne_write1_ex`: `AbPartW2` and `NoW1` on the stubs' blocks, nodes;
- `StubOAb`, `stubW_sfacts_svc`, `stubON_w2`: `StubON` inside `W2` (`ovfSeg2`'s `hstub`);
- `StubHAb`, `stubHW_sfactsA_svc`, `stubHN_w2`: `StubHN` inside `W2` (`heapAbSeg2`'s `hstub`).
-/
import Spike.Lib.LowerA64.AbortSeg2
import Spike.Lib.LowerA64.W2Body
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.LowerA64.AbortCall
import Spike.Lib.A64StubHA
import Spike.Lib.A64RunPc
import Spike.Lib.LowerA64.LaneW2
import Spike.Lib.LowerA64.OvfCode

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun OvfReady EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable KStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff TakeK takeMem loadInt_takeMem)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt runOk2_of)
open Scc.Cert.Rt.A64 (blockAt)

/-! ## `W2` from the stubs' facts -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}

/-- **No output `write(1, …)` at `s`**: at a system call the decoded call is
no `write` to the standard output. -/
def NoW1 (s : State) : Prop :=
  abi.atSys s = true → ∀ b n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 b n)

/-- **`W2`'s part at an abort path's state that `SFacts` does not give**:
the abort phase kept (`AbSt`), the suspended frames placed, off a system
call no write, and no output `write(1, …)`. -/
def AbPartW2 (Λ : Scc.Sem.Layout) (μ : Marks) (Ab : State → Prop) (lbl : Lbl) (fs : List TermRun.Frame) :
    Frag isaLSE2 := fun s _ =>
  AbSt μ Ab s ∧ FramesPlaced Λ lbl s fs ∧ (abi.atSys s = false → ∀ L, ¬ WrAt s L) ∧ NoW1 s

/-- **`W2`'s facts of an abort path's source control** at the frames `fs`:
`main`'s `ret` excluded, free of `ZBad`, the suspended frames' environments
small. -/
def CtlW2 (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs ∧ ∀ f ∈ fs, EnvSmall f.env

/-- **`W2` from `SFacts`**, its part (`AbPartW2`) and the control's facts
(`CtlW2`). -/
theorem w2_of_sfacts (hp : ProgNoS ZBad p) (hS : SFacts Λ μ own rS Tk lbl s c Dt)
    (hP : AbPartW2 Λ μ Ab lbl fs s c) (hc : CtlW2 c fs) : W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs :=
  w2_of hp hc.2.1 hS.toSt hP.1 hc.1 (.of_placedS (PlacedS.ofFrames hS.place hP.2.1))
    (fun _ _ _ hs => wrOkA_of_noWr (hP.2.2.1 hs))
    (fun k a ha hpc =>
      have h := hS.abortOk k a ha hpc
      ⟨.inr (.inl ⟨h.1, h.2.1, h.2.2.1, hc.2.2⟩), h.2.2.2⟩)
    (fun hs b n hd => (hP.2.2.2 hs b n hd).elim)

/-- **`W2` from `SFactsA` with no phase** (at owned words with no frame
dependence), the phase kept (`hab`) and no output `write(1, …)` (`hw1`). -/
theorem w2_of_sfactsA
    (h : SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt (fun _ => False))
    (hab : AbSt μ Ab s) (hw1 : NoW1 s) : W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs where
  st := ⟨h.noSite, h.mapped, h.svc, h.ownInstr c fs (.refl _), h.ownSys c fs (.refl _), h.ownTake, h.site,
    h.tkTake, h.tkInstr, h.tkSys, h.owned, h.wrTail⟩
  ab := hab
  noRet := h.noRet
  run := ⟨h.cell, h.zero⟩
  place := h.place
  wr := h.wr
  abort k a ha hpc := by
    obtain ⟨h1 | h1 | h1, h2⟩ := h.abortOk k a ha hpc
    · exact h1.2.elim
    · exact ⟨.inr (.inl h1), h2⟩
    · exact ⟨.inr (.inr h1), h2⟩
  svc1 hs b n hd := (hw1 hs b n hd).elim

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop}

/-- **A block's states inside `W2`** from `SFacts`, `W2`'s part and, at
every control of the node's invariant, `CtlW2`. -/
theorem BlkW.w2_sfacts (hp : ProgNoS ZBad p) {n : ND} {blk : List Directive}
    (hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n blk)
    (hP : BlkW (AbPartW2 Λ μ Ab lbl fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → CtlW2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  fun s σ c he hn hd hpc hA hF hJn k hk m hA' hD =>
    have h1 := hS s σ c he hn hd hpc hA hF hJn k hk m hA' hD
    ⟨w2_of_sfacts hp h1.1 (hP s σ c he hn hd hpc hA hF hJn k hk m hA' hD).1 (hJ σ c hJn), h1.2⟩

/-- **A node's states inside `W2`** from `SFacts` (as `BlkW.w2_sfacts`). -/
theorem NodeW.w2_sfacts (hp : ProgNoS ZBad p) {n : ND}
    (hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F n)
    (hP : NodeW (AbPartW2 Λ μ Ab lbl fs) (fun _ _ => False) exe endPc R F n)
    (hJ : ∀ σ c, n.J σ c → CtlW2 c fs) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  fun s c hA =>
    have h1 := hS s c hA
    ⟨w2_of_sfacts hp h1.1 (hP s c hA).1 (hJ _ c hA.2.2.2.2.choose_spec.2.2), h1.2⟩

/-- **A block's states inside `W2`** from `SFactsA` with no phase, the
phase kept and no output `write(1, …)`. -/
theorem BlkW.w2_sfactsA {n : ND} {blk : List Directive}
    (hS : BlkW (fun s c => SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt (fun _ => False))
      K exe endPc R F n blk)
    (hP : BlkW (fun s _ => AbSt μ Ab s ∧ NoW1 s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  Spike.Lib.A64.AllocG.BlkW.imp hS hP fun _ _ h1 h2 => w2_of_sfactsA h1 h2.1 h2.2

/-- **A node's states inside `W2`** from `SFactsA` with no phase (as
`BlkW.w2_sfactsA`). -/
theorem NodeW.w2_sfactsA {n : ND}
    (hS : NodeW (fun s c => SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt (fun _ => False))
      K exe endPc R F n)
    (hP : NodeW (fun s _ => AbSt μ Ab s ∧ NoW1 s) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  Spike.Lib.A64.AllocG.NodeW.imp hS hP fun _ _ h1 h2 => w2_of_sfactsA h1 h2.1 h2.2

end State

/-! ## The take's moves -/

/-- **`ovfSeg2`'s `hKR` at the take**: a take of `rS` keeps every cell of
the region off `rS` (`hRS`). `ovfSeg2`'s `hFK` at the take is
`Ret0.TakeK.kstable`. -/
theorem ovf_hKR_take {a : Int64} {rS : Range} {R : Region} {F : MachineData → Prop} {kb lo hi : Int}
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Kernel.addrs rS) :
    ∀ s s', TakeK a rS s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee kb lo hi).Off (k - kb) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
  fun _ _ hk _ k hk' _ => by
    obtain ⟨pm, he⟩ := hk.mem
    rw [he]; exact loadInt_takeMem (hRS k hk')

/-! ## The suspended frames at an abort path's states -/

section Frames

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {fs : List TermRun.Frame} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **A block's states have the suspended frames placed** when the frame
condition, kept outside the region (`hFS`), gives them (`hfp`). -/
theorem blkW_framesPlaced {n : ND} {blk : List Directive} (hFS : FStable R F)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) :
    BlkW (fun s _ => FramesPlaced Λ lbl s fs) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ hF _ _ _ _ _ hD => ⟨hfp _ (hFS _ _ hF hD), fun _ h => h⟩

/-- **A node's states have the suspended frames placed** when the frame
condition gives them (`hfp`). -/
theorem nodeW_framesPlaced {n : ND} (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) :
    NodeW (fun s _ => FramesPlaced Λ lbl s fs) (fun _ _ => False) exe endPc R F n :=
  fun s _ ⟨_, _, _, _, _, _, hF, _⟩ => ⟨hfp s hF, fun _ h => h⟩

end Frames

/-! ## The function's overflow block -/

section Ovf

open Spike.Lib.A64.Flow (arun dstep AI ofNat4_zero)
open Spike.Lib.A64.Flow.Ret0 (ofNat4_succ')
open Spike.Lib.A64.AllocG (abLabs)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {rs : Scc.IR.Reg → Option Int} {c0 : Ctl}

/-- **`ovfSeg2`'s `hW`: the function's overflow block inside `W2`** at the
frames `fs` (`blkW_w2B` at `Abort.Local.lb`, its code from the check
`hblk`): its phase check (`hph`), the abort phase kept (`blkW_abSt_pos`:
its fall-through after its label off `abLabs`, `hL`, e.g.
`local_not_abLabs`; its call `scc_rt_abort` at `x0 = 1`), at a node whose
controls are placed in the slot file (`hJp`, `hrs`), exclude `main`'s `ret`
and are free of `ZBad` (`hJ`), the suspended frames placed under the frame
condition (`hfp`). -/
theorem ovf_hW_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {cx : Scc.Emit.A64.FnCtx} {fp ra : BitVec 64}
    (hblk : blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true) (hL : cx.local "abort_overflow" ∉ abLabs)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra' : Int64}
    (hph : blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow")) ra' A64.Abort.Local.lb = true)
    (hJp : ∀ σ c, (abortN2 i T p lbl cx lab fp ra c0).J σ c → SlotRepAt Λ.imms lbl rs σ.slot c)
    (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, (abortN2 i T p lbl cx lab fp ra c0).J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K exe endPc
      R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) A64.Abort.Local.lb := by
  have hlab := hI.labOk
  subst hlab
  rw [ovfBlk_eq_lb] at hblk
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hblk
    (q := (_root_.Executable.labels exe).label (cx.local "abort_overflow")) (ofNat4_zero _)
  have hok := A64.Abort.Local.lb_ok R.lo R.hi cx.frame
  have hab : BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s)
      (fun _ _ => False) exe endPc R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0)
      A64.Abort.Local.lb := by
    refine blkW_abSt_pos hI hpr habt hcode hok hR hal (Int.le_refl _) (Int.le_refl _) hph lb_noRet ?_
    intro σ c _ k hk a ha t ht
    rcases k with _ | _ | k
    · left
      simp [A64.Abort.Local.lb, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly] at ha
      subst ha
      simp only [aiTgts, List.mem_singleton] at ht
      subst ht
      exact ⟨cx.local "abort_overflow", 1, Scc.Cert.Rt.A64.inRun_of_blockAt hblk (i := 1) (by decide), hL,
        (ofNat4_succ' _ 0).symm⟩
    · right
      obtain rfl : a = .bl "scc_rt_abort" :=
        Option.some.inj (ha.symm.trans
          (rfl : Spike.Lib.A64.Flow.classify (A64.Abort.Local.lb[1]'hk) = some (.bl "scc_rt_abort")))
      refine ⟨rfl, ?_⟩
      have h1 : (arun (_root_.Executable.labels exe).label (A64.Abort.Local.lb.take 1)
          ⟨(abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).pc,
            (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).o, σ⟩).σ.regs.X0 = 1 := by
        simp [A64.Abort.Local.lb, arun, dstep, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.AI.tgt,
          Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step, Spike.Lib.A64.Flow.regRes] <;> rfl
      rw [h1]; decide
    · simp [A64.Abort.Local.lb] at hk
      omega
  exact blkW_w2B hI hR hal (Int.le_refl _) (Int.le_refl _) hl hh hsub hfit hFO hFS hp hblk (ofNat4_zero _) hph hok
    lb_noRet (by decide) hab hJp hrs hfp hJ

end Ovf

/-! ## The abort paths' single instructions and system calls -/

section Parts

open Spike.Lib.A64.Flow (SI svcDir svcCall exec_si ofNat4_zero)
open Spike.Lib.A64 (CodeAt)
open Scc.Sem.A64 (atSvc_of_cellAt atSvc_false_of_cellAt)

variable {exe : _root_.Executable} {endPc : Int64} {μ : Marks} {Λ : Scc.Sem.Layout} {R : Region}
  {F : MachineData → Prop} {Ab : State → Prop} {lbl : Lbl} {fs : List TermRun.Frame}

/-- **`W2`'s part at a covered block of an abort path**: the phase kept
(`hab`), the suspended frames placed (`blkW_framesPlaced`), no write
(`blkW_noWr'`) and off a system call (`blkW_noSys'`). -/
theorem blkW_abPartW2 {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hFS : FStable R F) (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (AbPartW2 Λ μ Ab lbl fs) (fun _ _ => False) exe endPc R F n blk := by
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp (blkW_noWr' hcode hok hR hal hlo hhi) (blkW_noSys' hcode hok)
      fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s _ => FramesPlaced Λ lbl s fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp (blkW_framesPlaced hFS hfp) hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  exact Spike.Lib.A64.AllocG.BlkW.imp hab hPW
    fun _ _ h1 h2 => ⟨h1, h2.1, fun _ => h2.2.1, fun hs => absurd hs (by rw [h2.2.2]; decide)⟩

/-- **`W2`'s part at a single instruction without an event** (`SI`) of an
abort path: no write (`exec_si`), off a system call. -/
theorem nodeW_abPartW2_si {n : ND} {si : SI}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [si.toDir])
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs)
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n) :
    NodeW (AbPartW2 Λ μ Ab lbl fs) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -, -, hF, -⟩ := id hA
  have hc := (hcode s hs hn).cell (j := 0) rfl rfl rfl (hpc.trans (ofNat4_zero _).symm)
  refine ⟨⟨(hab s c hA).1, hfp s hF, fun _ => noWr_done (exec_si hc), fun hs' => ?_⟩, fun _ h => h⟩
  rw [show abi.atSys s = false from atSvc_false_of_cellAt hc (by cases si <;> intro _ h <;> cases h)] at hs'
  cases hs'

/-- **`W2`'s part at an `svc` of an abort path** whose call is no output
`write(1, …)` (`hw`): at a system call, the off-call part vacuous. -/
theorem nodeW_abPartW2_svc {n : ND}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [svcDir])
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs)
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, At exe endPc R F n s c → ∀ b k, svcCall s.st.1.regs ≠ some (.write 1 b k)) :
    NodeW (AbPartW2 Λ μ Ab lbl fs) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -, -, hF, -⟩ := id hA
  have hc := (hcode s hs hn).cell (j := 0) rfl rfl rfl (hpc.trans (ofNat4_zero _).symm)
  have hsy : abi.atSys s = true := atSvc_of_cellAt (imm := 0) hc
  exact ⟨⟨(hab s c hA).1, hfp s hF, fun h => absurd hsy (by rw [h]; decide), fun _ b k => hw s c hA b k⟩,
    fun _ h => h⟩

/-- **The phase kept and no output `write(1, …)` at a covered block** of an
abort path (`hab`; off a system call, `blkW_noSys'`). -/
theorem blkW_abNoW1 {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s _ => AbSt μ Ab s ∧ NoW1 s) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64.AllocG.BlkW.imp hab (blkW_noSys' hcode hok)
    fun _ _ h1 h2 => ⟨h1, fun hs => absurd hs (by rw [h2]; decide)⟩

/-- **The phase kept and no output `write(1, …)` at a single instruction
without an event** (`SI`) of an abort path. -/
theorem nodeW_abNoW1_si {n : ND} {si : SI}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [si.toDir])
    (hab : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s _ => AbSt μ Ab s ∧ NoW1 s) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -⟩ := id hA
  have hc := (hcode s hs hn).cell (j := 0) rfl rfl rfl (hpc.trans (ofNat4_zero _).symm)
  refine ⟨⟨(hab s c hA).1, fun hs' => ?_⟩, fun _ h => h⟩
  rw [show abi.atSys s = false from atSvc_false_of_cellAt hc (by cases si <;> intro _ h <;> cases h)] at hs'
  cases hs'

/-- **No output `write(1, …)` at a stub's `write` call** (`x0 = 2`,
`x8 = 64`: a `write` to the error output). -/
theorem svcCall_ne_write1 {s : State} {σ : Spike.Lib.A64.Flow.AS} (hr : s.st.1.regs = σ.regs)
    (h0 : σ.regs.X0 = 2) (h8 : σ.regs.X8 = 64) (b k : Nat) : svcCall s.st.1.regs ≠ some (.write 1 b k) := by
  obtain ⟨b', k', hw'⟩ := Spike.Lib.A64.StubW.svcCall_write (r := s.st.1.regs) (by rw [hr]; exact h0)
    (by rw [hr]; exact h8)
  rw [hw']
  intro h
  cases h

/-- **No output `write(1, …)` at a stub's exit call** (`x8 = 94`:
`exit_group`). -/
theorem svcCall_ne_write1_ex {s : State} {σ : Spike.Lib.A64.Flow.AS} (hr : s.st.1.regs = σ.regs)
    (h8 : σ.regs.X8 = 94) (b k : Nat) : svcCall s.st.1.regs ≠ some (.write 1 b k) := by
  rw [Spike.Lib.A64.Flow.svcCall_exitGroup (by rw [hr, h8]; rfl)]
  intro h
  cases h

end Parts

/-! ## The overflow abort path -/

/-- **The write abort's phase at the overflow abort path's nodes**: each of
`StubON`'s nodes' states in `AbSt` (moved by no outside step). -/
structure StubOAb (μ : Marks) (Ab : State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (c0 : Ctl) : Prop where
  de : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .e) A64.Abort.Disp.d0
  dt1 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .t1) A64.Abort.Disp.t1
  dg1 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .g1) A64.Abort.Disp.g1
  se : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .e) A64.Abort.b0
  sn1 : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .n1)
  sn1b : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .n1b)
  sn2 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .n2) A64.Abort.b1Overflow
  hsvc : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .svc)
  sn5 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .n5) A64.Abort.b2
  sex : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .ex)

section Stub

open Spike.Lib.A64.StubW (stubW_sfacts abortPhOk phOne)
open Scc.Cert.Rt.A64.Print (code_field add4 add0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl}

/-- **The overflow stub's `write` call's states in `SFacts`** (as in
`stubW_sfacts`, whose `StubW` gives that call as a segment). -/
theorem stubW_sfacts_svc {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    (hwr : ∀ s c, At exe endPc R F (A64.Abort.N lab A64.Abort.overflow c0 .svc) s c → Dt s) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c Dt) K exe endPc R F
      (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .svc) := by
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.1.1.1
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, -, hsvcIn, -⟩ := hst
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, -, -, o7, q7, -⟩ := hphs
  have he7 : (_root_.Executable.labels exe).label A64.Abort.overflow.entry + Int64.ofNat (4 * 7) =
      (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .svc).pc := by
    simp only [A64.Abort.N, A64.Abort.pcSvc, add4, add0]
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
  have hc0 : c = c0 := hJ
  rw [← he7] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
  have hown : Tk s → Owned Λ rS s := fun _ =>
    Spike.Lib.A64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  exact ⟨hc0 ▸ sfacts_svcOvf hc (hpl s hD) hP.1.noSite hP.1.noTake (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc)
    (Spike.Lib.A64.Rt.next_same hI hpc q7) hown (abortOk_of_ne hP.1.noAbort) (fun _ _ _ _ => hwr s c hAt), hP.2⟩

/-- **`ovfSeg2`'s `hstub`: `StubON` inside `W2`** at the frames `fs`, from
`stubW_sfacts`'s premises (the stub's states in `SFacts`), the write
abort's phase at each node (`hab`), the suspended frames placed under the
frame condition (`hfp`) and the source control's `W2` facts (`hcw`): the
stubs' blocks write nothing and are off a system call, the `write` is to
the error output (`x0 = 2`), the exit call `exit_group`. -/
theorem stubON_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hp : ProgNoS ZBad p)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : OvfReady c0) (hsm : EnvSmall c0.env)
    (hpl : ∀ s : State, F s.st.1 → Placed Λ lbl s c0)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isaLSE2} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (A64.Abort.N lab A64.Abort.overflow c0 .svc) s c → Dt s)
    (hfp : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hcw : CtlW2 c0 fs)
    (hab : StubOAb μ Ab exe endPc R F c0) :
    StubON (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K ms exe endPc R F c0 := by
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hS := stubW_sfacts (p := p) (al := lbl) hI hprog hphs hR hal hlo hhi hl hh hF hsub hfit hFO hc hsm
    hpl hrel htk hk hKex hms hK hwr
  have hSv := stubW_sfacts_svc hI hprog hphs hR hR8 hl hh hsub hFO hc hpl hwr
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hsc := Scc.Cert.Rt.A64.Abort.code_stub (c0 := c0) hI.lays hI.endOk hsd.1.1.1.1.1
  have hdc := Scc.Cert.Rt.A64.Abort.code_disp (c0 := c0) hI.lays hI.endOk hsd.2
  have hJ : ∀ n : ND, (∀ σ c, n.J σ c → c = c0) → ∀ σ c, n.J σ c → CtlW2 c fs :=
    fun _ h σ c hj => h σ c hj ▸ hcw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hS.ab⟩
  · exact BlkW.w2_sfacts hp hS.de
      (blkW_abPartW2 hdc.e A64.Abort.Disp.d0_ok hR hal (by omega) hhi hF hfp hab.de) (hJ _ fun _ _ h => h.1)
  · exact BlkW.w2_sfacts hp hS.dt1
      (blkW_abPartW2 hdc.t1 A64.Abort.Disp.t1_ok hR hal (by omega) hhi hF hfp hab.dt1) (hJ _ fun _ _ h => h.1)
  · exact BlkW.w2_sfacts hp hS.dg1
      (blkW_abPartW2 hdc.g1 A64.Abort.Disp.g1_ok hR hal (by omega) hhi hF hfp hab.dg1) (hJ _ fun _ _ h => h)
  · exact BlkW.w2_sfacts hp hS.se (blkW_abPartW2 hsc.e A64.Abort.b0_ok hR hal hlo hhi hF hfp hab.se)
      (hJ _ fun _ _ h => h)
  · exact NodeW.w2_sfacts hp hS.sn1 (nodeW_abPartW2_si hsc.n1 hfp hab.sn1) (hJ _ fun _ _ h => h)
  · exact NodeW.w2_sfacts hp hS.sn1b (nodeW_abPartW2_si hsc.n1b hfp hab.sn1b) (hJ _ fun _ _ h => h)
  · exact BlkW.w2_sfacts hp hS.sn2 (blkW_abPartW2 hsc.n2 A64.Abort.b1Overflow_ok hR hal hlo hhi hF hfp hab.sn2)
      (hJ _ fun _ _ h => h)
  · refine NodeW.w2_sfacts hp hSv (nodeW_abPartW2_svc hsc.svc hfp hab.hsvc ?_) (hJ _ fun _ _ h => h.1)
    rintro s c ⟨-, -, -, -, σ, hA, -, -, h0, h8⟩
    exact svcCall_ne_write1 hA.regs h0 h8
  · exact BlkW.w2_sfacts hp hS.sn5 (blkW_abPartW2 hsc.n5 A64.Abort.b2_ok hR hal hlo hhi hF hfp hab.sn5)
      (hJ _ fun _ _ h => h)
  · refine NodeW.w2_sfacts hp hS.sex (nodeW_abPartW2_svc hsc.ex hfp hab.sex ?_) (hJ _ fun _ _ h => h.1)
    rintro s c ⟨-, -, -, -, σ, hA, -, -, h8, -⟩
    exact svcCall_ne_write1_ex hA.regs h8

end Stub

/-! ## The heap abort path -/

/-- **The write abort's phase at the heap abort path's nodes**: each of
`StubHN`'s nodes' states in `AbSt` (moved by no outside step). -/
structure StubHAb (μ : Marks) (Ab : State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (c0 : Ctl) : Prop where
  de : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .e) A64.Abort.Disp.d0
  dt1 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .t1) A64.Abort.Disp.t1
  dj1 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .j1) A64.Abort.Disp.j1
  dt2 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .t2) A64.Abort.Disp.t2
  dg2 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .g2) A64.Abort.Disp.g2
  se : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .e) A64.Abort.b0
  sn1 : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .n1)
  sn1b : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .n1b)
  sn2 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .n2) A64.Abort.b1Heap
  hsvc : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .svc)
  sn5 : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .n5) A64.Abort.b2
  sex : NodeW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
    (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .ex)

section Heap

open Spike.Lib.A64.StubW (stubHW_sfactsA abortPhHeapOk phOne NbCtl sfactsA_svc)
open Spike.Lib.A64ConsumerS (OwnS)
open Scc.Cert.Rt.A64.Print (add4 add0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl}

/-- **The heap stub's `write` call's states in `SFactsA`** (as in
`stubHW_sfactsA`, whose `StubHW` gives that call as a segment). -/
theorem stubHW_sfactsA_svc {kp : Nat} {own : OwnS} {frs : List TermRun.Frame}
    (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhHeapOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) (hc : NbCtl Λ p own lbl F c0 frs)
    (hwr : ∀ s c, At exe endPc R F (A64.Abort.N lab A64.Abort.heap c0 .svc) s c → Dt s) :
    NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False)) K exe
      endPc R F (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .svc) := by
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, -, hsvcIn, -⟩ := hst
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, o7, q7, -⟩ := hphs
  have he7 : (_root_.Executable.labels exe).label A64.Abort.heap.entry + Int64.ofNat (4 * 7) =
      (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.heap c0 .svc).pc := by
    simp only [A64.Abort.N, A64.Abort.pcSvc, add4, add0]
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
  have hc0 : c = c0 := hJ
  subst hc0
  rw [← he7] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
  have hown : Tk s → Owned Λ rS s := fun _ =>
    Spike.Lib.A64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  exact ⟨sfactsA_svc hc.nb hc.zero (hc.place s hD) (hc.runIn s) hP.1.noSite hP.1.noTake
    (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc) (Spike.Lib.A64.Rt.next_same hI hpc q7) hown
    (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt), hP.2⟩

/-- **`heapAbSeg2`'s `hstub`: `StubHN` inside `W2`** at the frames `fs`,
from `stubHW_sfactsA`'s premises at the owned words `fun s _ => own s`
(the stub's states in `SFactsA` with no phase) and the write abort's phase
at each node (`hab`): the stubs' blocks are off a system call, the `write`
is to the error output (`x0 = 2`), the exit call `exit_group`. -/
theorem stubHN_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhHeapOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : NbCtl Λ p (fun s _ => own s) lbl F c0 fs)
    (hobl : HeapAbortObl ar.cells ar.ctr c0)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.heap.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.heap.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.heap.exit).toBitVec.toNat = a → k = .heap)
    (hKex : ∀ s s', pcOf s = (lab A64.Abort.heap.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isaLSE2} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.heap.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (A64.Abort.N lab A64.Abort.heap c0 .svc) s c → Dt s)
    (hab : StubHAb μ Ab exe endPc R F c0) :
    StubHN (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K ms exe endPc R F c0 := by
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hS := stubHW_sfactsA (p := p) (al := lbl) (own := fun s _ => own s) (frs := fs) (rd := rd) (G := G)
    (ar := ar) (J := J) (lsize := lsize) hI hprog hphs hR hal hlo hhi hl hh hF hsub hfit hFO hc hobl hrel htk hk
    hKex hms hK hwr
  have hSv := stubHW_sfactsA_svc (own := fun s _ => own s) (frs := fs) (rd := rd) (G := G) (ar := ar) (J := J)
    (lsize := lsize) hI hprog hphs hR hR8 hl hh hsub hFO hc hwr
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hsc := Scc.Cert.Rt.A64.Abort.code_stub (c0 := c0) hI.lays hI.endOk hsd.1.1.1.1.2
  have hdc := Scc.Cert.Rt.A64.Abort.code_disp (c0 := c0) hI.lays hI.endOk hsd.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hS.ab⟩
  · exact BlkW.w2_sfactsA hS.de (blkW_abNoW1 hdc.e A64.Abort.Disp.d0_ok hab.de)
  · exact BlkW.w2_sfactsA hS.dt1 (blkW_abNoW1 hdc.t1 A64.Abort.Disp.t1_ok hab.dt1)
  · exact BlkW.w2_sfactsA hS.dj1 (blkW_abNoW1 hdc.j1 A64.Abort.Disp.j1_ok hab.dj1)
  · exact BlkW.w2_sfactsA hS.dt2 (blkW_abNoW1 hdc.t2 A64.Abort.Disp.t2_ok hab.dt2)
  · exact BlkW.w2_sfactsA hS.dg2 (blkW_abNoW1 hdc.g2 A64.Abort.Disp.g2_ok hab.dg2)
  · exact BlkW.w2_sfactsA hS.se (blkW_abNoW1 hsc.e A64.Abort.b0_ok hab.se)
  · exact NodeW.w2_sfactsA hS.sn1 (nodeW_abNoW1_si hsc.n1 hab.sn1)
  · exact NodeW.w2_sfactsA hS.sn1b (nodeW_abNoW1_si hsc.n1b hab.sn1b)
  · exact BlkW.w2_sfactsA hS.sn2 (blkW_abNoW1 hsc.n2 A64.Abort.b1Heap_ok hab.sn2)
  · refine NodeW.w2_sfactsA hSv fun s c hA => ⟨⟨(hab.hsvc s c hA).1, fun _ b k => ?_⟩, fun _ h => h⟩
    obtain ⟨-, -, -, -, σ, hA', -, -, h0, h8⟩ := hA
    exact svcCall_ne_write1 hA'.regs h0 h8 b k
  · exact BlkW.w2_sfactsA hS.sn5 (blkW_abNoW1 hsc.n5 A64.Abort.b2_ok hab.sn5)
  · refine NodeW.w2_sfactsA hS.sex fun s c hA => ⟨⟨(hab.sex s c hA).1, fun _ b k => ?_⟩, fun _ h => h⟩
    obtain ⟨-, -, -, -, σ, hA', -, -, h8, -⟩ := hA
    exact svcCall_ne_write1_ex hA'.regs h8 b k

end Heap

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.w2_of_sfacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2_of_sfacts

/-- info: 'Spike.Lib.LowerA64.w2_of_sfactsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2_of_sfactsA

/-- info: 'Spike.Lib.LowerA64.ovf_hKR_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovf_hKR_take

/-- info: 'Spike.Lib.LowerA64.ovf_hW_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovf_hW_w2

/-- info: 'Spike.Lib.LowerA64.stubON_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubON_w2

/-- info: 'Spike.Lib.LowerA64.stubHN_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHN_w2

end Spike.Lib.LowerA64
