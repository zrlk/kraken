/-
**A callee's prologue inside `W2`, placed only under its frame condition**
(x86-64; the twin of `Spike/Lib/LowerA64/G1ProW.lean`): `proW_placedS` and
`proW_w2C` (`Spike/Lib/LowerX64/ProW2.lean`) with the placement premise
`hPl` asked only at states in the frame condition `F`. A callee at nonempty
frames places its suspended frames from `F` (the caller's cells), so a
placement at every state is not available.

- `proW_placedSF`: the prologue's states placed, from the entry's argument
  registers at states in `F` (`F` stable over the region, `hFS`: the
  prologue's intermediate states keep the memory outside the region);
- `proW_w2_ofF`: `proW_w2` at the restricted placement;
- `proW_w2F`: `proW_w2C` at the restricted placement.
-/
import Spike.Lib.LowerX64.ProW2

namespace Spike.Lib.LowerX64

set_option linter.unusedSimpArgs false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (abi)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW xHead xLea xCmp xFr xS1 xS2 xS3 prologueIn)
open Spike.Lib.X64Consumer (SFacts Own Lbl Lsize K0)
open Spike.Lib.X64ConsumerS (PlacedS InvS)
open Spike.Lib.X64ConsumerA (AbSt)
open Spike.Lib.X64.Rt (InstOk argXs)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)
open Spike.Lib.LowerNode (FrOk2 ZBad)

section Comb

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isa} {pc0 Z lim : Int64} {L : Label} {zl zf z1 z2 zs : Nat}
  {ps : List (Reg64 × Int64 × Nat)} {JE : AS → Ctl → Prop} {Λ : Scc.Sem.Layout} {lbl : Lbl}
  {fs : List TermRun.Frame}

/-- **A prologue's states placed under the frame condition** at the frames
`fs`: as `proW_placedS`, every control of the entry invariant `JE` placed
only at states in `F` agreeing with the entry's on `%rdi`…`%r9` (`hPl`); the
prologue's states are in `F` (a node's state by `At`, a block's
intermediate one by `F` stable over the region, `hFS`). -/
theorem proW_placedSF (hFS : FStable R F)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, F s.st.1 →
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS Λ lbl s c fs) :
    XProW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps JE := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ hF hJ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    exact argEq_arun_take _ (dstep_xHead _) k _ i hi
  · rintro s σ1 c _ _ _ _ _ hF ⟨σ, hJ, rfl⟩ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    exact ((argEq_xS1 σ).trans (argEq_arun_take _ (dstep_xLea _ Z zl) k _)) i hi
  · rintro s c ⟨-, -, -, -, σ2, hA, hF, σ, hJ, rfl⟩
    refine ⟨hPl σ c hJ _ hF fun i hi => ?_, fun _ h => h⟩
    rw [hA.regs]
    exact argEq_xS2 Z σ i hi
  · rintro s σ3 c _ _ _ _ _ hF ⟨σ, v, hJ, -, rfl⟩ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    exact ((argEq_xS3 Z _ σ).trans (argEq_arun_take _ (dstep_xCmp _ L z1 z2) k _)) i hi
  · rintro s σ4 c _ _ _ _ _ hF ⟨σ, v, hJ, -, he, -⟩ k _ m hA' hD
    refine ⟨hPl σ c hJ _ (hFS _ _ hF hD) fun i hi => ?_, fun _ h => h⟩
    show m.regs.get64 _ = _
    rw [hA'.regs]
    have h4 : ArgEq σ.regs σ4.regs := by rw [he]; exact argEq_xS3 Z _ σ
    exact (h4.trans (argEq_arun_take _ (dstep_xFr _ Z zs ps) k _)) i hi

end Comb

section Pro

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A stack-checked prologue is inside `W2`, placed under the frame
condition**: `proW_w2` with the placement `hPl` asked only at states in
`F` (`proW_placedSF`, `F` stable over the region, `hFS`). -/
theorem proW_w2_ofF {ms : MemSide isa} {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fn sc entry : Label} {Z : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z 8 L zl zf z1 z2 zs ps = true)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    (hph : ProPh okPc ph lab fn sc Z L zl zf z1 z2 zs ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hZ : 0 ≤ Z.toInt)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p) (hFS : FStable R F)
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L zl zf z1 z2 zs ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, F s.st.1 →
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) Z 8 L zl zf z1 z2 zs ps JE := by
  have hS := proW_sfactsP (lbl := lbl) (ms := ms) (J := fun σ c => c = X64Consumer.c0 ∧ ∃ c', JE σ c') hI hin hps
    Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 (fun _ _ h => h.1) (fun σ _ ⟨_, c', h⟩ => htp σ c' h) hph hR hR8 hlo
    hhi hl hh hZ hmr hun hsub hfit hFO
  exact XProW.w2 hp hS (XProW.w2Part hab (proW_placedSF hFS hPl) (proW_noWr hI hin hps htp hR hlo hhi hZ hun)) hJ

end Pro

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **A compiled block's prologue inside `W2`, placed under the frame
condition**: `proW_w2C` with the placement `hPl` asked only at states in
`F` (`proW_w2_ofF`, `F` stable over the region, `hFS`). -/
theorem proW_w2F (c : FnCode2 exe cells endPc RaOk Cd i T d) {ms : MemSide isa} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {JE : AS → Ctl → Prop} {tp : UInt64} (htp : ∀ σ c, JE σ c → σ.regs.fsBase = tp)
    (hph : ProPh okPc ph lab c.fn (Scc.Emit.X64.labelOf c.fr.fn "chk") (Int64.ofInt c.fr.size) (proL c.fr)
      c.zl c.zf c.z1 c.z2 c.zs c.ps)
    {R : Region} {F : MachineData → Prop} (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hp : ProgNoS ZBad p) (hFS : FStable R F)
    (hab : XProW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE)
    (hPl : ∀ σ c, JE σ c → ∀ s : State, F s.st.1 →
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = σ.regs.get64 (argXs.getD i .rdi)) →
      PlacedS Λ lbl s c fs)
    (hJ : ∀ σ c, JE σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    XProW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label c.fn) (Int64.ofInt c.fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL c.fr) c.zl c.zf c.z1 c.z2 c.zs c.ps JE := by
  have h1 := c.h1
  have hZ : (Int64.ofInt c.fr.size).toInt = c.fr.size := toInt_ofInt_small (by omega) (by omega)
  exact proW_w2_ofF hI c.hpro c.hps htp hph hR hR8 (by rw [hZ]; exact hlo) hhi hl hh (by rw [hZ]; omega) hmr hun
    hsub hfit hFO hp hFS hab hPl hJ

end Code

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.proW_placedSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_placedSF
/-- info: 'Spike.Lib.LowerX64.proW_w2_ofF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_w2_ofF
/-- info: 'Spike.Lib.LowerX64.proW_w2F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.proW_w2F
