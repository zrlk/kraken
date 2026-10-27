/-
**An output call's `let` inside `W2`** (x86-64; the twin of
`Spike/Lib/LowerA64/PrintCallW2.lean`): `printCallC_of`'s `hWL`
(`Spike/Lib/LowerX64/PrintCallC2.lean`) at the per-pair facts `W2`
(`Spike/Lib/LowerX64/SFactsA2.lean`).

The `let`'s node is the first state of the argument block's cells before
the multiply (`PBlk.n0`, `print_codeC`), so it is a node of that block
(`BlkW.nodeW`): its state's facts by the block's phase check
(`blkW_postO'` at `print_ph`), the write abort's phase by `printArgW_ab`,
nothing written and no system call (`blkW_noWr'`, `blkW_noSys'`), and,
nothing run yet, the control placed in the node's slot file
(`nodeW_placedS` at `bodyN2`'s `SlotRepAt`). The control is not `main`'s
`ret` (its local run reaches the `let`) and is free of `ZBad` (`FrOk2` at
the ghost, `hG0F`, along the node's local run).

- `printWL_w2`: `hWL` at the code predicates `CdCL`, `BlC` with positions
  off the write abort (e.g. `BlC2L`), the immediates `Λ.imms`.
-/
import Spike.Lib.LowerX64.PrintArgW2
import Spike.Lib.LowerX64.PrintCallC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Lower.InvX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad ofEnv2)
open Spike.Lib.LowerShape (printInsts)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}

/-- **An output call's `let` inside `W2`** (`printCallC_of`'s `hWL`, the
immediates `Λ.imms`): at `printInsts`' code from `pc` (`InstsC2` at code
predicates inside `CdCL`, `hCd`, and `BlC` at positions off the write
abort, `hBl`), the node at the `let` is the first state of the cells before
the multiply: inside `W2` by `NodeW.w2`, its state's facts from their phase
check, the write abort's phase from `printArgW_ab`, placed by
`nodeW_placedS` (every slot a cell of the region, `hrs`; the suspended
frames placed under the frame condition, `hfp`). The node's controls
exclude `main`'s `ret` and `ZBad` (`FrOk2` at the ghost, `hG0F`, kept by
the local run). The states in `W2` lie in `W` (`hW₀`). -/
theorem printWL_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {W : FragS isa}
    (hW₀ : ∀ s c, W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs → W s c fs)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : CoreTerm.At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (kk kk' : Nat) (pc' : Int64) s c,
      G0 c0 → T (.let_ x (.call "print" is a []) e) →
      InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      LetAt p lbl lsize Λ.imms fr exe endPc R F fp ra tp c0 fs pc (.let_ x (.call "print" is a []) e) env lits
        cs bufs s c fs → W s c fs := by
  rintro c0 pc env lits cs bufs n x is a e b o m cw kk kk' pc' s c hG0 - hi ⟨hA, -⟩
  have hCdC : ∀ pc blk, Cd pc blk → CdC cells okPc ph lab ra0 pc blk := fun _ _ h => (hCd _ _ h).toCdC
  have hBlC : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k :=
    fun _ _ _ _ h => (hBl _ _ _ _ h).1
  obtain ⟨B, hB, -, -⟩ := print_codeC hi
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, zs1, zs2, zM, zc, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hz1, -, hBe⟩ := hB.toPrintCode
  have hpc0 : B.pc = pc := by rw [hBe]; rfl
  let Jn := ((bodyN2 p lbl lsize Λ.imms fr fp ra c0 pc (.let_ x (.call "print" is a []) e) (ofEnv2 env) lits
    cs bufs).withTp tp).J
  have hnd : (bodyN2 p lbl lsize Λ.imms fr fp ra c0 pc (.let_ x (.call "print" is a []) e) (ofEnv2 env) lits
      cs bufs).withTp tp = B.n0 fr Jn := by
    simp only [PBlk.n0, hpc0]; rfl
  rw [hnd] at hA
  obtain ⟨hph1, -, -, -, -⟩ := print_ph hf h1 hCdC hBlC hB
  obtain ⟨hc1, -, -, -⟩ := hB.cdOf (fun _ _ h => codeAt_cdC hI (hCdC _ _ h)) fun _ _ _ _ h => by
    obtain ⟨L, j, off, hpc, hb, -⟩ := hBlC _ _ _ _ h
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc] at this
  obtain ⟨hok1, -, hnt1, -⟩ := printArg_ok hf h1 hB
  have hne : B.pre ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [hBe]
    simp only [pblk, List.length_zip, hz1, Nat.min_self, preD, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have hS : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN (B.n0 fr Jn)) :=
    BlkW.nodeW (blkW_postO' (n := dumN (B.n0 fr Jn)) (dead := fun _ => false) (ra := ra0) hI hc1 hok1 hR
      (by omega) hhi hR8 hl hh (fun _ _ h => h.1 ▸ cfacts_c0) hph1
      (fun _ _ _ k hk hr => (noRet_false (noRet_of_noTerm hnt1) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO)
      hne
  have hab := (printArgW_ab (μ := μ) (R := R) (F := F) hI hpr habI hf h1 hR hlo hhi hCd hBl hB (Jn := Jn)).1
  have hab' := BlkW.nodeW hab hne
  have hWr := BlkW.nodeW (blkW_noWr' (n := B.n0 fr Jn) (F := F) hc1 hok1 hR (by omega) hhi) hne
  have hSy := BlkW.nodeW (blkW_noSys' (n := B.n0 fr Jn) (R := R) (F := F) hc1 hok1) hne
  have hPl := nodeW_placedS (n := B.n0 fr Jn) (exe := exe) (endPc := endPc) (fun _ _ h => h.1.2.2.2) hrs hfp
  have hJ : ∀ σ c, (B.n0 fr Jn).J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs := by
    rintro σ c ⟨⟨⟨-, -, -, c', hr, hj, -⟩, -, hc0, -⟩, -⟩
    exact ⟨fun _ => noRet_of_run hr (fun a' h' => by rw [hj.1] at h'; cases h'),
      Spike.Lib.LowerNode.FrOk2.run hp (FrameRun.ofLocal hc0 fs) (hG0F c0 hG0)⟩
  refine hW₀ s c (NodeW.w2 (Dt := Dt) (J := Jv) (rd := rd) (G := G) (ar := ar) (lsize := lsize) hp hS
    (fun s c hA => ⟨⟨(hab' s c hA).1, (hPl s c hA).1, fun _ _ _ _ => wrOkA_of_noWr (hWr s c hA).1,
      fun h => absurd h (by rw [(hSy s c hA).1]; decide)⟩, fun _ h => h⟩) hJ s c hA).1

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.printWL_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWL_w2
