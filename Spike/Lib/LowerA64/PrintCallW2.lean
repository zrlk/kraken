/-
**An output call's `let` inside `W2`** (AArch64): `printCallC_of`'s `hWL`
(`Spike/Lib/LowerA64/PrintCallC2.lean`) at the per-pair facts `W2`
(`Spike/Lib/LowerA64/SFactsA2.lean`). The twin of
`Spike/Lib/LowerX64/PrintCallW2.lean`.

The `let`'s node is the first state of the argument block (`printInsts`'
code from `pc`, `print_code`), so it is a node of that block
(`BlkW.nodeW`): its state's facts by the block's phase check
(`blkW_postOc` at `print_ph`), the write abort's phase by `printBlkW_ab`,
nothing written and no system call (`blkW_noWrC`, `blkW_noSysC`), and,
nothing run yet, the control placed in the node's slot file
(`nodeW_placedS` at `bodyN2`'s `SlotRepAt`). The control is not `main`'s
`ret` (its local run reaches the `let`) and is free of `ZBad` (`FrOk2` at
the ghost, `hG0F`, along the node's local run).

- `printWL_w2`: `hWL` at the code predicates `CdCL`, `BlC` with positions
  off the write abort (e.g. `BlC2L`), the immediates `Λ.imms`.
-/
import Spike.Lib.LowerA64.PrintArgW2
import Spike.Lib.LowerA64.PrintCallC2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At FStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad ofEnv2)
open Spike.Lib.LowerShape (printInsts)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}

/-- **An output call's `let` inside `W2`** (`printCallC_of`'s `hWL`, the
immediates `Λ.imms`): at `printInsts`' code from `pc` (`InstsC2` at code
predicates inside `CdCL`, `hCd`, and `BlC` at positions off the write
abort, `hBl`), the node at the `let` is the argument block's first state:
inside `W2` by `NodeW.w2`, its state's facts from the block's phase check,
the write abort's phase from `printBlkW_ab`, placed by `nodeW_placedS`
(every slot a cell of the region, `hrs`; the suspended frames placed under
the frame condition, `hfp`). The node's controls exclude `main`'s `ret`
and `ZBad` (`FrOk2` at the ghost, `hG0F`, kept by the local run). The
states in `W2` lie in `W` (`hW₀`). -/
theorem printWL_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {W : FragS isaLSE2}
    (hW₀ : ∀ s c, W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs → W s c fs)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : CoreTerm.At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      LetAt p lbl lsize Λ.imms cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits
        cs bufs s c fs → W s c fs := by
  rintro c0 pc env lits cs bufs n x is a e b o m cw kk pc' s c hG0 - hi ⟨hA, -⟩
  have hCdC : ∀ pc blk, Cd pc blk → CdC prog okPc ph lab ra0 pc blk := fun _ _ h => (hCd _ _ h).toCdC
  have hBlC : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k := fun _ _ _ h => (hBl _ _ _ h).1
  obtain ⟨L, hL, hcode, -⟩ := print_code (fun _ _ h => cdOf_of_cdC hI (hCdC _ _ h))
    (fun _ _ _ h => cdOf_of_blC hI (hBlC _ _ _ h)) hi
  let nd : ND := (bodyN2 p lbl lsize Λ.imms cx fp ra c0 pc (.let_ x (.call "print" is a []) e) (ofEnv2 env) lits
    cs bufs).withTp tp
  have hne : directives L ++ blPrintD ≠ [] := by simp [blPrintD_eq]
  have hok := printCode_okBlk hf h1 h16 hL
  have hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN nd) :=
    BlkW.nodeW (blkW_postOc (n := dumN nd) (dead := fun _ => false) (ra := ra0) hI hcode hok hR hal hlo hhi
      (fun _ _ h => h.1 ▸ cfacts_c0) (print_ph hf h1 h16 hCdC hBlC hi hL)
      (fun _ _ _ k hk r hr => (noRet_false (printCode_noRet hf h1 h16 hL) k hk r hr).elim)
      (fun _ _ _ => rfl) hl hh hsub hfit hFO) hne
  have hab := BlkW.nodeW (printBlkW_ab (μ := μ) (R := R) (F := F) hI hpr habI hf h1 h16 hR hal hlo hhi hCd hBl hi
    hL (Jn := nd.J)) hne
  have hWr := BlkW.nodeW (blkW_noWrC (n := nd) (F := F) hcode hok hR hal hlo hhi) hne
  have hSy := BlkW.nodeW (blkW_noSysC (n := nd) (R := R) (F := F) hcode hok) hne
  have hPl := nodeW_placedS (n := nd) (exe := exe) (endPc := endPc) (fun _ _ h => h.1.2.2.2) hrs hfp
  have hJ : ∀ σ c, nd.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs := by
    rintro σ c ⟨⟨⟨-, -, -, c', hr, hj, -⟩, -, hc0, -⟩, -⟩
    exact ⟨fun _ => noRet_of_run hr (fun a' h' => by rw [hj.1] at h'; cases h'),
      Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hc0 fs) (hG0F c0 hG0)⟩
  refine hW₀ s c (NodeW.w2 (Dt := Dt) (J := Jv) (rd := rd) (G := G) (ar := ar) (lsize := lsize) hp hS
    (fun s c hA => ⟨⟨(hab s c hA).1, (hPl s c hA).1, fun _ _ _ _ => wrOkA_of_noWr (hWr s c hA).1,
      fun h => absurd h (by rw [(hSy s c hA).1]; decide)⟩, fun _ h => h⟩) hJ s c hA).1

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.printWL_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWL_w2
