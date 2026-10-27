/-
**`print`'s system call inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/PrintW2.lean`): `PrintW`'s system-call clause's states
(`Spike/Lib/LowerX64/PrintCallC2.lean`) carry the per-pair facts `W2`
(`Spike/Lib/LowerX64/SFactsA2.lean`) at `print`'s frames, from
`scc_rt_print`'s facts at any instance (`printSvcStP`, `printSvcAb`,
`Spike/Lib/X64PrintGSvc.lean`) and the source at the call (`printSys_src`).

- `printSvc_src`: at the call the source is at `print`'s loop top inside a
  call (`PrintSvc`, `W2.svc1`).
- `printLBody_noZBad`, `frOk2_printC`: `FrOk2` at `printL`'s loop top
  inside the call (`hf`), from the caller's continuation and frames.
- `printSvc_abort`: the call is at no abort site (`W2.abort`).
- `printSvc_w2`: `W2` at the call, none moved by `K`, given the frames' run
  facts (`hf`), their placement at `PlacedSE` (`hpl`) and the write tail (`hDt`).
- `BlkW.ofJ`, `PrintAW.imp`, `rc0_pq`, `rc1_pq`, `rc2_pq`, `N_pq`,
  `PrintAW.ofJ`: `print`'s block obligations combined, and read off the
  node's control (the source's `P` or `Q` at some byte).
- `printW2`: `print`'s blocks inside `W2` (`printSt`, `printAb`,
  `printNoWr`, `printPc`, `Spike/Lib/X64PrintGAb.lean`), given the frames'
  placement (`hpl`) and their run facts at `P`, `Q` (`hf`).

Where x86-64 differs from AArch64: the call state's count is `%rsi`, the
return address `print`'s at the caller's cell `ko`, and `print`'s region
`pR kb R` is entered at `kb = ko - 8` (`PrintW`'s `ko = -(fr.size) - 8`).
-/
import Spike.Lib.X64PrintGSvc
import Spike.Lib.X64PrintGAb
import Spike.Lib.LowerX64.PrintCallC2
import Spike.Lib.LowerX64.SFactsA2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.LowerNode (FrOk2 ZBad runOk2_of)
open Spike.Lib.X64 (NodeW At AS)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.PrintCall (pN pR pF pcS)
open Spike.Lib.PrintSrc (PrintC printN)
open Spike.Lib.X64.PrintG (printPhOk)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F F' : MachineData → Prop} {σC : AS} {pw wn : TermRun.Word} {nv mv : Nat} {ko kb : Int} {s : State}
  {c : Ctl}

omit [Kraken.Executable.ValidLayout exe] in
/-- **At `print`'s system call the source is at its loop top** inside a
call (`W2.svc1`), when the call state's `%rsi` is the count. -/
theorem printSvc_src {R' : Region} {fr : TermRun.Frame} {fs : List TermRun.Frame}
    (hAt : At exe endPc R' F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) ko σC .sys) s c)
    (hN : (σC.regs.get64 .rsi).toNat = printN nv mv) :
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
theorem printSvc_abort (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}
    (hAt : At exe endPc R F (Spike.Lib.X64.PrintA.N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys)
      s c) {fs : List TermRun.Frame} {cells' ctr : Nat} {Ab : State → Prop} :
    ∀ k a, μ.abortAt k = some a → pcOf s = a →
      ((k = .writeErr ∧ Ab s) ∨ (k = .overflow ∧ OvfReady c ∧ EnvSmallS c.env fs) ∨
        (k = .heap ∧ HeapAbortObl cells' ctr c)) ∧
        ∀ v, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) → v % 256 = Kernel.abortStatus := by
  obtain ⟨hs, hn, -, hpc, -⟩ := hAt
  obtain ⟨⟨hP, -⟩, -⟩ := Spike.Lib.X64.PrintG.sys_cell hI hin hph hs hn hpc
  exact abortOkA_of_ne hP.noAbort

/-- **`print`'s system call inside `W2`** at `print`'s frames `fr :: fs`,
none moved by `K`: the state's facts in `print`'s region at the call
(`printSvcStP`, the frame condition inside `print`'s, `hFF`), the write
abort's phase (`printSvcAb`), the source inside a call at the loop top
(`printSvc_src`), off the abort sites; given the frames' run facts (`hf`),
their placement at `PlacedSE` (`hpl`) and the write tail at the node (`hDt`). -/
theorem printSvc_w2 (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range}
    {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ kb + -40) (hkb : kb + 16 ≤ R.hi) (hk16 : kb % 16 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) (hFF : ∀ m, F' m → pF kb R F m)
    (hN : (σC.regs.get64 .rsi).toNat = printN nv mv)
    {fr : TermRun.Frame} {fs : List TermRun.Frame}
    (hp : ProgNoS ZBad p) (hf : FrOk2 c (fr :: fs)) (hpl : PlacedSE Λ lbl s c (fr :: fs))
    (hDt : ∀ s c, At exe endPc (pR kb R) F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) ko σC .sys) s c → Dt s)
    (hAt : At exe endPc (pR kb R) F' (pN (_root_.Executable.labels exe).label
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv))
      (pcS (fun _ => pw) (fun _ => wn) (fun _ => nv) (fun _ => mv)) ko σC .sys) s c) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) lbl lsize s c
      (fr :: fs) ∧ ∀ s', ¬ K s s' := by
  have hst := Spike.Lib.X64.PrintG.printSvcStP (Λ := Λ) (rS := rS) (Dt := Dt) hI hin hph hR hal hl hh hlo hkb
    hk16 hsub hFO hFF hDt s c hAt
  have hab' := Spike.Lib.X64.PrintG.printSvcAb (F := F') hI hin hab hph
    (by simp [Region.callee]) (by simp [Region.callee]) s c hAt
  have hsy : abi.atSys s = true := by
    obtain ⟨hs, hn, -, hpc, -⟩ := hAt
    exact atSyscall_of_cellAt (Spike.Lib.X64.PrintG.sys_cell hI hin hph hs hn hpc).2.1
  refine ⟨w2_of hp hf hst.1 hab'.1 (fun h => absurd h (List.cons_ne_nil _ _)) hpl
    (fun _ _ _ h => by rw [hsy] at h; cases h) (printSvc_abort hI hin hph hAt)
    (fun _ _ _ _ => printSvc_src hAt hN), hst.2⟩

section Blk

open Spike.Lib.X64 (BlkW ND)
open Spike.Lib.X64.PrintA (PrintAW N JL JI JIlt RC0 RC1 RC2)

variable {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- A block whose obligation reads the node's control only. -/
theorem BlkW.ofJ {n : ND} {blk : List (Directive × Nat)} {V : Ctl → Prop} (h : ∀ σ c, n.J σ c → V c) :
    BlkW (fun _ c => V c) (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ, fun _ hk => hk⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`print` inside `W`** from two, the second not moved (`BlkW.imp`). -/
theorem PrintAW.imp {W1 W2 W : Frag isa}
    (h1 : PrintAW rbp0 ra buf0 len0 P Q W1 K exe endPc R F)
    (h2 : PrintAW rbp0 ra buf0 len0 P Q W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : PrintAW rbp0 ra buf0 len0 P Q W K exe endPc R F := by
  have I := @Spike.Lib.X64.AllocG.BlkW.imp
  exact ⟨I h1.e h2.e hw, I h1.n1 h2.n1 hw, I h1.loop h2.loop hw, I h1.n3 h2.n3 hw,
    I h1.write h2.write hw, I h1.n5 h2.n5 hw, I h1.n6 h2.n6 hw, I h1.chk2 h2.chk2 hw,
    I h1.n8 h2.n8 hw, I h1.chk3 h2.chk3 hw, I h1.n10 h2.n10 hw, I h1.adv h2.adv hw,
    I h1.fail h2.fail hw, I h1.done h2.done hw⟩

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
theorem N_pq {lab : Label → Int64} {σ : AS} (n : Spike.Lib.X64.Print.PN)
    (h : (N lab rbp0 ra buf0 len0 P Q n).J σ c) : ∃ j, P j c ∨ Q j c := by
  cases n
  case e => exact ⟨_, .inl h.1⟩
  case n1 | loop => obtain ⟨_, -, h⟩ := h; exact ⟨_, .inl h⟩
  case n3 | write => obtain ⟨_, -, -, h⟩ := h; exact ⟨_, .inl h⟩
  case sys => obtain ⟨⟨_, -, -, h⟩, -⟩ := h; exact ⟨_, .inl h⟩
  case n5 => obtain ⟨_, -, h⟩ := h; exact rc0_pq h
  case n6 | chk2 => obtain ⟨_, -, h⟩ := h; exact rc1_pq h
  case n8 | chk3 => obtain ⟨_, -, h⟩ := h; exact rc2_pq h
  case n10 | adv => obtain ⟨_, -, -, -, h⟩ := h; exact ⟨_, .inl h⟩
  case fail => obtain ⟨_, h⟩ := h; exact ⟨_, .inr h⟩
  case done => exact ⟨_, .inl h.2.2⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **`print` inside a predicate of the node's control**, not moved. -/
theorem PrintAW.ofJ {V : Ctl → Prop} (h : ∀ j c, P j c ∨ Q j c → V c) :
    PrintAW rbp0 ra buf0 len0 P Q (fun _ c => V c) (fun _ _ => False) exe endPc R F := by
  have hJ : ∀ n σ c, (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q n).J σ c → V c :=
    fun n σ c hn => let ⟨j, hj⟩ := N_pq n hn; h j c hj
  exact ⟨BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _),
    BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _), BlkW.ofJ (hJ _),
    BlkW.ofJ (hJ _), BlkW.ofJ (hJ _)⟩

/-- **`print`'s blocks inside `W2`** at `print`'s frames `fr :: fs`, none
moved by `K`: the state's facts (`printSt`), the write abort's phase
(`printAb`), no write and no system call (`printNoWr`), off the marks'
sites (`printPc`); given the frames' placement (`PlacedSE`) at the blocks' states
(`hpl`) and `FrOk2` at the source's `P`, `Q` controls (`hf`, e.g.
`frOk2_printC`). -/
theorem printW2 (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range}
    {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hlen : len0 < 2 ^ 63)
    (hra : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : Int64.ofBitVec ra ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    {fr : TermRun.Frame} {fs : List TermRun.Frame} (hp : ProgNoS ZBad p)
    (hf : ∀ j c, P j c ∨ Q j c → FrOk2 c (fr :: fs))
    (hpl : PrintAW rbp0 ra buf0 len0 P Q (fun s c => PlacedSE Λ lbl s c (fr :: fs)) (fun _ _ => False) exe endPc R F) :
    PrintAW rbp0 ra buf0 len0 P Q
      (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize s c (fr :: fs))
      K exe endPc R F := by
  have hst := Spike.Lib.X64.PrintG.printSt (Λ := Λ) (rS := rS) (rbp0 := rbp0) (ra := ra) (buf0 := buf0)
    (len0 := len0) (P := P) (Q := Q) (F := F) hI hin hph hR hR8 hlo hhi hl hh hsub hfit hFO hra
  have hab' := Spike.Lib.X64.PrintG.printAb (rbp0 := rbp0) (buf0 := buf0) (P := P) (Q := Q) (F := F)
    hI hin hab hph hR hlo hhi hlen hra hraAb
  have hnw := Spike.Lib.X64.PrintG.printNoWr (rbp0 := rbp0) (ra := ra) (buf0 := buf0) (len0 := len0) (P := P)
    (Q := Q) (F := F) hI hin hR hlo hhi
  have hpc := Spike.Lib.X64.PrintG.printPc (rbp0 := rbp0) (ra := ra) (buf0 := buf0) (len0 := len0) (P := P)
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

/-- info: 'Spike.Lib.LowerX64.printSvc_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvc_w2

/-- info: 'Spike.Lib.LowerX64.printW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printW2

end Spike.Lib.LowerX64
