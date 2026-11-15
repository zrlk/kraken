/-
**A callee's prologue inside `W2`, placed only under its frame condition**
(AArch64): `proW_placedS` and `proW_w2C` (`Spike/Lib/LowerA64/ProW2.lean`)
with the placement premise `hPl` asked only at states in the frame
condition `F`. A callee at nonempty frames places its suspended frames from
`F` (the caller's cells), so a placement at every state is not available.

- `proW_placedSF`: the prologue's states placed, from the entry's argument
  registers at states in `F` (`F` stable over the region, `hFS`: the
  prologue's intermediate states keep the memory outside the region);
- `proW_w2_ofF`: `proW_w2` at the restricted placement;
- `proW_w2F`: `proW_w2C` at the restricted placement.
-/
import Spike.Lib.LowerA64.ProW2

namespace Spike.Lib.LowerA64

set_option linter.unusedSimpArgs false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (abi)
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (CFacts SFacts blkPh noRetBlk Own Lbl Lsize aiTgts)
open Spike.Lib.A64ConsumerS (PlacedS InvS envsOf)
open Spike.Lib.A64ConsumerA (AbSt WrAt noWr_load wrOkA_of_noWr)
open Spike.Lib.A64.Rt (InstOk argX)
open Spike.Lib.A64.Flow.Ret0 (StackOff limA tcbA_limA)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.LowerNode (FrOk2 ZBad)

section Comb

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
  {JE : AS → Ctl → Prop} {Λ : Scc.Sem.Layout} {lbl : Lbl} {fs : List TermRun.Frame}

/-- **A prologue's states placed under the frame condition** at the frames
`fs`: as `proW_placedS`, every control of the entry invariant `JE` placed
only at states in `F` agreeing with the entry's on `x0`…`x7` (`hPl`); the
prologue's states are in `F` (a node's state by `At`, a block's
intermediate one by `F` stable over the region, `hFS`). -/
theorem proW_placedSF (hFS : FStable R F)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, F s.st.1 →
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) → PlacedS Λ lbl s c fs) :
    ProW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps JE := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ hF hJ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs]
    exact argEq_arun_take _ (dstep_chkHead _ Z) k _ i hi
  · rintro s c ⟨-, -, -, -, σ1, hA, hF, σ, hJ, rfl⟩
    refine ⟨hPl σ c hJ _ hF fun i hi => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact argEq_chkRegs Z σ.regs i hi
  · rintro s σ2 c _ _ _ _ _ hF ⟨σ, v, hJ, -, rfl⟩ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs]
    exact ((argEq_chkRegs Z σ.regs).trans (argEq_ldStep _ _)).trans
      (argEq_arun_take _ (dstep_chkBr _ L) k _) i hi
  · rintro s σ3 c _ _ _ _ _ hF ⟨σ, v, hJ, -, he, -⟩ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.getXReg _ = _
    rw [hA'.regs]
    have h3 : ArgEq σ.regs σ3.regs := by
      rw [he]; exact (argEq_chkRegs Z σ.regs).trans (argEq_ldStep _ _)
    exact (h3.trans (argEq_arun_take _ (dstep_frameSet _ Z ps) k _)) i hi

end Comb

section Pro

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A stack-checked prologue is inside `W2`, placed under the frame
condition**: `proW_w2` with the placement `hPl` asked only at states in
`F` (`proW_placedSF`, `F` stable over the region, `hFS`). -/
theorem proW_w2_ofF {ms : MemSide isaLSE2} {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {ps : List (XReg × Int64)}
    (hin : prologueIn prog fn sc entry Z 8 L ps = true)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    (hph : ProPh okPc ph lab sc Z L ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p) (hFS : FStable R F)
    (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, F s.st.1 →
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) → PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L ps JE := by
  have hS := proW_sfactsP (lbl := lbl) (ms := ms) (J := fun σ c => c = A64Consumer.c0 ∧ ∃ c', JE σ c') hI hin hps
    cfacts_c0 (fun _ _ h => h.1) (fun σ _ ⟨_, c', h⟩ => htp σ c' h) hph hR hal hlo hhi hl hh h16 hZ hmr hun hsub
    hfit hFO
  exact ProW.w2 hp hS (ProW.w2Part hab (proW_placedSF hFS hPl)
    (proW_noWr hI hin hps htp hR hal hlo hhi h16 hZ hun)) hJ

end Pro

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A compiled block's prologue inside `W2`, placed under the frame
condition**: `proW_w2C` with the placement `hPl` asked only at states in
`F` (`proW_w2_ofF`, `F` stable over the region, `hFS`). -/
theorem proW_w2F (c : FnCode2 exe prog endPc RaOk Cd i T d) {ms : MemSide isaLSE2} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.TPIDR_EL0 = tp)
    (hph : ProPh okPc ph lab (c.cx.local "stack_check") (Int64.ofInt c.cx.frame) (proL c.cx) c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p) (hFS : FStable R F)
    (hab : ProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, F s.st.1 →
      (∀ i < 8, s.st.1.regs.getXReg (argX i) = σ.regs.getXReg (argX i)) → PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    ProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.cx) c.ps JE := by
  have hge := frame_ge16 c.hf
  have h1 := c.h1
  have h16 := c.h16
  have hF64 : (Int64.ofInt c.cx.frame).toInt = c.cx.frame := toInt_ofInt_small (by omega) (by omega)
  exact proW_w2_ofF hI c.hpro c.hps htp hph hR hal (by rw [hF64]; exact hlo) hhi hl hh (by rw [hF64]; omega)
    (by rw [hF64]; omega) hmr hun hsub hfit hFO hp hFS hab hPl hJ

end Code

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.proW_placedSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_placedSF
/-- info: 'Spike.Lib.LowerA64.proW_w2_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_w2_ofF
/-- info: 'Spike.Lib.LowerA64.proW_w2F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proW_w2F
