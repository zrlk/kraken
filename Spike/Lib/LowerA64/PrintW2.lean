/-
**`print`'s system call inside `W2`** (AArch64): `PrintW`'s system-call
clause's states (`Spike/Lib/LowerA64/PrintCallC2.lean`) carry the per-pair
facts `W2` (`Spike/Lib/LowerA64/SFactsA2.lean`) at `print`'s frames, from
`scc_rt_print`'s facts at any instance (`printSvcStP`, `printSvcAb`,
`Spike/Lib/A64PrintGSvc.lean`) and the source at the call (`printSys_src`).

- `printSvc_src`: at the call the source is at `print`'s loop top inside a
  call (`PrintSvc`, `W2.svc1`).
- `printLBody_noZBad`, `frOk2_printC`: `FrOk2` at `printL`'s loop top
  inside the call (`hf`), from the caller's continuation and frames.
- `printSvc_abort`: the call is at no abort site (`W2.abort`).
- `printSvc_w2`: `W2` at the call, none moved by `K`, given the frames' run
  facts (`hf`), their placement at `PlacedSE` (`hpl`) and the write tail (`hDt`).
- `BlkW.ofJ`, `PrintAW.imp`, `PrintAW.ofJ`, `N_pq`: `print`'s blocks inside a
  conjunction, inside a predicate of the node's control (every node's
  control is the source's `P` or `Q` at some byte).
- `printW2`: `print`'s blocks inside `W2`, given the frames' placement
  (`hpl`) and `FrOk2` at the source's controls (`hf`).
-/
import Spike.Lib.A64PrintGSvc
import Spike.Lib.LowerA64.PrintCallC2
import Spike.Lib.LowerA64.SFactsA2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.LowerNode (FrOk2 ZBad runOk2_of)
open Spike.Lib.A64.Flow (NodeW At AS)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS)
open Spike.Lib.PrintSrc (PrintC printN)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.PrintG (printPhOkF)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F F' : MachineData → Prop}
  {σC : AS} {pw wn : TermRun.Word} {nv mv : Nat} {kc : Int} {s : State} {c : Ctl}

omit [Kraken.Executable.ValidLayout exe] in
/-- **At `print`'s system call the source is at its loop top** inside a
call (`W2.svc1`), when the call state's `x1` is the count. -/
theorem printSvc_src {fr : TermRun.Frame} {fs : List TermRun.Frame}
    (hAt : At exe endPc (pR kc R) F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c)
    (hN : σC.regs.X1.toBitVec.toNat = printN nv mv) :
    Spike.Lib.PrintSvc.PrintSvc c (fr :: fs) := by
  obtain ⟨k, hP, hk⟩ := printSys_src hAt hN
  exact ⟨List.cons_ne_nil _ _, pw, wn, nv, mv, k, hP, hk⟩

/-- **`printL`'s body is free of `ZBad`.** -/
theorem printLBody_noZBad : NoS ZBad Spike.Lib.PrintSrc.printLBody := by
  simp [Spike.Lib.PrintSrc.printLBody, Spike.Lib.PrintSrc.printAdv, Spike.Lib.PrintSrc.printLoad,
    Spike.Lib.PrintSrc.printLane, Spike.Lib.PrintSrc.printEmit, Spike.Lib.PrintSrc.printNext, NoS, ZBad]

/-- **`FrOk2` at `printL`'s loop top** inside the call: the caller's
continuation `e` and frames `fs` free of `ZBad`. -/
theorem frOk2_printC {pw wn : TermRun.Word} {n m k : Nat} {x : String} {e : Expr} {c1 : Ctl}
    {fs : List TermRun.Frame} (hP : PrintC pw wn n m k c) (he : NoS ZBad e) (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) :
    FrOk2 c (Spike.Lib.LowerNode.printFrame x e c1 :: fs) := by
  obtain ⟨i, j, ht, -⟩ := hP
  refine ⟨ht ▸ printLBody_noZBad, ?_⟩
  intro fr hfr
  rcases List.mem_cons.mp hfr with rfl | hfr
  · exact he
  · exact hfs fr hfr

/-- **`print`'s system call is at no abort site** (`W2.abort`). -/
theorem printSvc_abort (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hph : printPhOkF okPc ph lab = true)
    {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}
    (hAt : At exe endPc R F (Spike.Lib.A64.PrintA.N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc)
      s c) {fs : List TermRun.Frame} {cells ctr : Nat} {Ab : State → Prop} :
    ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortObl cells ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus := by
  obtain ⟨hs, hn, -, hpc, -⟩ := hAt
  obtain ⟨⟨hP, -⟩, -⟩ := Spike.Lib.A64.PrintG.svc_cell hI hin hph hs hn hpc
  exact abortOkA_of_ne hP.noAbort

/-- **`print`'s system call inside `W2`** at `print`'s frames `fr :: fs`,
none moved by `K`: the state's facts in `print`'s region at the call
(`printSvcStP`, the frame condition inside `print`'s, `hFF`), the write
abort's phase (`printSvcAb`), the source inside a call at the loop top
(`printSvc_src`), off the abort sites; given the frames' run facts (`hf`),
their placement at `PlacedSE` (`hpl`) and the write tail at the node (`hDt`). -/
theorem printSvc_w2 (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range}
    {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ kc + -48) (hkc : kc < R.hi) (hk16 : kc % 16 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) (hFF : ∀ m, F' m → pF kc R F m)
    (hN : σC.regs.X1.toBitVec.toNat = printN nv mv)
    {fr : TermRun.Frame} {fs : List TermRun.Frame}
    (hp : ProgNoS ZBad p) (hf : FrOk2 c (fr :: fs)) (hpl : PlacedSE Λ lbl s c (fr :: fs))
    (hDt : ∀ s c, At exe endPc (pR kc R) F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c → Dt s)
    (hAt : At exe endPc (pR kc R) F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) σC .svc) s c) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) lbl lsize s c
      (fr :: fs) ∧ ∀ s', ¬ K s s' := by
  have hst := Spike.Lib.A64.PrintG.printSvcStP (Λ := Λ) (rS := rS) (Dt := Dt) hI hin hph hR hal hl hh hlo hkc
    hk16 hsub hFO hFF hDt s c hAt
  have hab' := Spike.Lib.A64.PrintG.printSvcAb (F := F') hI hin hab hph
    (by simp [Region.callee]) (by simp [Region.callee]) s c hAt
  have hsy : abi.atSys s = true := by
    obtain ⟨hs, hn, -, hpc, -⟩ := hAt
    exact atSvc_of_cellAt (Spike.Lib.A64.PrintG.svc_cell hI hin hph hs hn hpc).2.1
  refine ⟨w2_of hp hf hst.1 hab'.1 (fun h => absurd h (List.cons_ne_nil _ _)) hpl
    (fun _ _ _ h => by rw [hsy] at h; cases h) (printSvc_abort hI hin hph hAt)
    (fun _ _ _ _ => printSvc_src hAt hN), hst.2⟩

/-! ## `print`'s blocks inside `W2` -/

section Blk

open Spike.Lib.A64.Flow (BlkW ND)
open Spike.Lib.A64.PrintA (PrintAW N JL JI JIlt RC0 RC1 RC2)

variable {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- A block whose obligation reads the node's control only. -/
theorem BlkW.ofJ {n : ND} {blk : List Directive} {V : Ctl → Prop} (h : ∀ σ c, n.J σ c → V c) :
    BlkW (fun _ c => V c) (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ, fun _ hk => hk⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- A node whose obligation reads the node's control only. -/
theorem NodeW.ofJ {n : ND} {V : Ctl → Prop} (h : ∀ σ c, n.J σ c → V c) :
    NodeW (fun _ c => V c) (fun _ _ => False) exe endPc R F n :=
  fun _ c ⟨_, _, _, _, σ, _, _, hJ⟩ => ⟨h σ c hJ, fun _ hk => hk⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`print` inside `W`** from two, the second not moved (`BlkW.imp`). -/
theorem PrintAW.imp {W1 W2 W : Frag isaLSE2}
    (h1 : PrintAW x29 ra buf0 len0 P Q W1 K exe endPc R F)
    (h2 : PrintAW x29 ra buf0 len0 P Q W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : PrintAW x29 ra buf0 len0 P Q W K exe endPc R F := by
  have I := @Spike.Lib.A64.AllocG.BlkW.imp
  exact ⟨I h1.e h2.e hw, I h1.n1 h2.n1 hw, I h1.loop h2.loop hw, I h1.n3 h2.n3 hw,
    Spike.Lib.A64.AllocG.NodeW.imp h1.fence h2.fence hw,
    I h1.write h2.write hw, I h1.n5 h2.n5 hw, I h1.n6 h2.n6 hw, I h1.n7 h2.n7 hw,
    I h1.chk2 h2.chk2 hw, I h1.n9 h2.n9 hw, I h1.n10 h2.n10 hw, I h1.chk3 h2.chk3 hw,
    I h1.n12 h2.n12 hw, I h1.adv h2.adv hw, I h1.fail h2.fail hw, I h1.done h2.done hw⟩

theorem rc2_pq {k : Nat} {r : BitVec 64} (h : RC2 len0 P Q k r c) : ∃ j, P j c ∨ Q j c := by
  rcases h with ⟨-, -, h⟩ | ⟨-, h⟩
  · exact ⟨_, .inl h⟩
  · exact ⟨_, .inr h⟩

theorem rc1_pq {k : Nat} {r : BitVec 64} (h : RC1 len0 P Q k r c) : ∃ j, P j c ∨ Q j c := by
  rcases h with ⟨-, h⟩ | h
  · exact ⟨_, .inl h⟩
  · exact rc2_pq h

theorem rc0_pq {k : Nat} {r : BitVec 64} (h : RC0 len0 P Q k r c) : ∃ j, P j c ∨ Q j c := by
  rcases h with ⟨-, h⟩ | h
  · exact ⟨_, .inl h⟩
  · exact rc1_pq h

/-- **Every node's control is the source's `P` or `Q` at some byte.** -/
theorem N_pq {lab : Label → Int64} {σ : AS} (n : Spike.Lib.A64.PrintD.PN)
    (h : (N lab x29 ra buf0 len0 P Q n).J σ c) : ∃ j, P j c ∨ Q j c := by
  cases n
  case e => exact ⟨_, .inl h.1⟩
  case n1 | loop => obtain ⟨_, -, h⟩ := h; exact ⟨_, .inl h⟩
  case n3 | fence | write => obtain ⟨_, -, -, h⟩ := h; exact ⟨_, .inl h⟩
  case svc => obtain ⟨⟨_, -, -, h⟩, -⟩ := h; exact ⟨_, .inl h⟩
  case n5 => obtain ⟨_, -, h⟩ := h; exact rc0_pq h
  case n6 => obtain ⟨⟨_, -, h⟩, -⟩ := h; exact rc0_pq h
  case n7 | chk2 => obtain ⟨_, -, h⟩ := h; exact rc1_pq h
  case n9 => obtain ⟨⟨_, -, h⟩, -⟩ := h; exact rc1_pq h
  case n10 | chk3 => obtain ⟨_, -, h⟩ := h; exact rc2_pq h
  case n12 | adv => obtain ⟨_, -, -, -, h⟩ := h; exact ⟨_, .inl h⟩
  case fail => obtain ⟨_, h⟩ := h; exact ⟨_, .inr h⟩
  case done => exact ⟨_, .inl h.2.2⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`print` inside a predicate of the node's control**, not moved. -/
theorem PrintAW.ofJ {V : Ctl → Prop} (h : ∀ j c, P j c ∨ Q j c → V c) :
    PrintAW x29 ra buf0 len0 P Q (fun _ c => V c) (fun _ _ => False) exe endPc R F := by
  have hJ : ∀ n σ c, (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q n).J σ c → V c :=
    fun n σ c hn => let ⟨j, hj⟩ := N_pq n hn; h j c hj
  exact ⟨BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), NodeW.ofJ (hJ _), BlkW.ofJ (hJ _),
    BlkW.ofJ (hJ _),
    BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _),
    BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _)⟩

/-- **`print`'s blocks inside `W2`** at `print`'s frames `fr :: fs`, none
moved by `K`: the state's facts (`printSt`), the write abort's phase
(`printAb`), no write and no system call (`printNoWr`), off the marks'
sites (`printPc`); given the frames' placement (`PlacedSE`) at the blocks' states
(`hpl`) and `FrOk2` at the source's `P`, `Q` controls (`hf`, e.g.
`frOk2_printC`). -/
theorem printW2 (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range}
    {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hlen : len0 < 2 ^ 63)
    (hra : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : Int64.ofBitVec ra ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    {fr : TermRun.Frame} {fs : List TermRun.Frame} (hp : ProgNoS ZBad p)
    (hf : ∀ j c, P j c ∨ Q j c → FrOk2 c (fr :: fs))
    (hpl : PrintAW x29 ra buf0 len0 P Q (fun s c => PlacedSE Λ lbl s c (fr :: fs)) (fun _ _ => False) exe endPc R F) :
    PrintAW x29 ra buf0 len0 P Q
      (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c (fr :: fs))
      K exe endPc R F := by
  have hst := Spike.Lib.A64.PrintG.printSt (Λ := Λ) (rS := rS) (x29 := x29) (ra := ra) (buf0 := buf0)
    (len0 := len0) (P := P) (Q := Q) (F := F) hI hin hph hR hal hlo hhi hl hh hsub hfit hFO hra
  have hab' := Spike.Lib.A64.PrintG.printAb (x29 := x29) (buf0 := buf0) (P := P) (Q := Q) (F := F)
    hI hin hab hph hR hal hlo hhi hlen hra hraAb
  have hnw := Spike.Lib.A64.PrintG.printNoWr (x29 := x29) (ra := ra) (buf0 := buf0) (len0 := len0) (P := P)
    (Q := Q) (F := F) hI hin hR hal hlo hhi
  have hpc := Spike.Lib.A64.PrintG.printPc (x29 := x29) (ra := ra) (buf0 := buf0) (len0 := len0) (P := P)
    (Q := Q) (R := R) (F := F) hI hph
  refine PrintAW.imp hst (PrintAW.imp hab' (PrintAW.imp hnw (PrintAW.imp hpc (PrintAW.imp hpl
    (PrintAW.ofJ hf) fun _ _ h1 h2 => And.intro h1 h2) fun _ _ h1 h2 => And.intro h1 h2)
    fun _ _ h1 h2 => And.intro h1 h2) fun _ _ h1 h2 => And.intro h1 h2) ?_
  rintro s c hS ⟨hA, ⟨hW, hsy⟩, hok, hP, hF⟩
  have hoff := (hI.off s hok).1
  exact w2_of hp hF (hS.dt_mono fun _ h => h.elim) hA (fun h => absurd h (List.cons_ne_nil _ _)) hP
    (fun _ _ _ _ => ⟨fun L h => (hW L h).elim, fun h => (hW _ h).elim⟩) (abortOkA_of_ne hoff.noAbort)
    (fun h => by rw [hsy] at h; cases h)

end Blk

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.printW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printW2

/-- info: 'Spike.Lib.LowerA64.printSvc_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvc_w2

end Spike.Lib.LowerA64
