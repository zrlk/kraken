/-
**Where an abort of `print` lands, as a segment with frames** (x86-64):
`printNA` (`scc_rt_abort` with `%rdi = 4`, `%rsp` 56 bytes below the
frame's floor) does not return, so at frames `fs` it is a segment (`SegWS`)
into any fragment, inside any `W` with frames. The code facts are
discharged from the abort code (`abortIn`); the nodes' states inside `W`
and the exit call at an abort site stay premises (`StubWN`). The twin of
`Spike/Lib/LowerA64/PrintAbW2.lean`.

- `StubWN`, `StubWN.stubWW`: the write abort path's obligations without its
  code (`Abort.Disp.StubWW`'s `W` fields), and `StubWW` from them and the
  abort code (`stubWW_of_code`);
- `printAbSeg2`: the landing `printNA` (`Disp.seg_jabort4W` lifted to frames
  by `SegWS.liftS`, the post empty); `printAbSeg2P` at `printNAS`;
- `w2_of_sfactsA_ab`, `BlkW.w2_sfactsAb`, `NodeW.w2_sfactsAb`, `blkW_noW1`,
  `nodeW_noW1_si`: `W2` from `SFactsA` in the same abort phase and no output
  `write(1, …)`;
- `stubWW_sfactsA_sys`, `stubWN_w2`: `StubWN` inside `W2 … (WriteAb.Ab lab)`
  (`printAbSeg2`'s `hstub`), from `stubWW_sfactsA`'s premises.

The write path's states are in the write abort's phase `WriteAb.Ab lab`
(`stubWW_sfactsA`), so `W2` is taken at that phase, as for the heap path's
consumers; the write tail `Dt` at the stub's `write` stays a premise
(`hwr`).
-/
import Spike.Lib.X64AbortHeapS
import Spike.Lib.X64AbortStubCode
import Spike.Lib.X64StubWA
import Spike.Lib.LowerX64.AbortW2
import Spike.Lib.LowerX64.PrintCallC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf)

section PrintAbW2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)}
  {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **The write abort path's obligations without its code** for one source
control `c0` in the dispatcher's region `R` and frame condition `F`: the
dispatcher's and the write stub's nodes' states inside `W` (moved by no `K`,
the stub's `write` call among them, `hsys`) and the exit call at an abort
site (`hab`); `Abort.Disp.StubWW` with the code fields dropped. -/
structure StubWN (W : Frag isa) (K : State → State → Prop) (ms : MemSide isa)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) : Prop where
  de : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .e) Abort.Disp.d0
  dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t1) Abort.Disp.t1
  dj1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j1) Abort.Disp.j1
  dt2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t2) Abort.Disp.t2
  dj2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j2) Abort.Disp.j2
  dt3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t3) Abort.Disp.t3
  dj3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .j3) Abort.Disp.j3
  dt4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .t4) Abort.Disp.t4
  dg4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd4 (_root_.Executable.labels exe).label c0 .g4) Abort.Disp.g4
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .e) Abort.x0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n1)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n2) Abort.x1Write
  hsys : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .sys)
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .n5) Abort.x2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex)
  hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) s c →
    ms.abortAt s

/-- **`StubWW` from `StubWN` and the abort code** (`stubWW_of_code`). -/
theorem StubWN.stubWW {W : Frag isa} {K : State → State → Prop} {ms : MemSide isa} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F)
    (h : StubWN W K ms exe endPc R F c0) : Abort.Disp.StubWW W K p lbl ms exe endPc R F c0 :=
  StubW.stubWW_of_code hp hend hprog hK hF h.de h.dt1 h.dj1 h.dt2 h.dj2 h.dt3 h.dj3 h.dt4 h.dg4 h.se h.sn1
    h.sn2 h.hsys h.sn5 h.sex h.hab

/-- **An abort of `print` is a segment with frames** into any fragment:
from `printNA` (the call of `scc_rt_abort` with `%rdi = 4`, `%rsp` 56 bytes
below the frame's floor in `R`) at frames `fs`, inside `W` at `fs`, given
the abort code (`hprog`) and, at each source control of the landing, the
write abort path's obligations without code (`StubWN`) in the dispatcher's
region and frame condition (`Disp.seg_jabort4W`'s). -/
theorem printAbSeg2 {W : FragS isa} {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isa}
    {fs : List TermRun.Frame} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {fr : Scc.Emit.X64.Frame}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 88)
    (hhi : -(fr.size : Int) - 48 ≤ R.hi) (h8 : (fr.size : Int) % 8 = 0)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, (printNA (_root_.Executable.labels exe).label fr).J σC c0 →
      StubWN (fun s c => W s c fs) K (ms fs) exe endPc (R.callee (-(fr.size : Int) - 56 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 56 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 56, []⟩ m0 σC) c0)
    (Q : FragS isa) :
    SegWS W K p lbl ms ((At exe endPc R F (printNA (_root_.Executable.labels exe).label fr)).at fs) Q := by
  refine (SegWS.liftS fs (Abort.Disp.seg_jabort4W (W := fun s c => W s c fs) (K := K) (exe := exe)
    (endPc := endPc) (p := p) (lbl := lbl) (Q := fun _ _ => False)
    (nC := printNA (_root_.Executable.labels exe).label fr) rfl
    (fun σ c hJ => hJ.1) hF hR (by simp only [printNA]; omega) (by simp only [printNA]; omega)
    (by simp only [printNA]; omega) hK (fun m0 σC c0 hJ => ?_)) fun _ _ h => h).mono_post
    fun _ _ _ h => h.1.elim
  refine (hstub m0 σC c0 hJ).stubWW hp hend hprog hK ?_
  exact fstable_enter (kb := -(fr.size : Int) - 56 - 8) hR hF (by omega) (by decide) (by omega) (by omega)
    (by omega) (by decide) (by decide)

/-- **`printAbSeg2` at `printNAS`**: `print`'s abort landing with the
caller's slots, `StubWN` asked at its source controls only. -/
theorem printAbSeg2P {W : FragS isa} {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isa}
    {fs : List TermRun.Frame} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {fr : Scc.Emit.X64.Frame}
    {it : Expr → String → Nat → Option Nat} {x : String} {e : Expr} {c1 : Ctl}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 88)
    (hhi : -(fr.size : Int) - 48 ≤ R.hi) (h8 : (fr.size : Int) % 8 = 0)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hstub : ∀ m0 σC c0, (printNAS (_root_.Executable.labels exe).label fr lbl it x e c1).J σC c0 →
      StubWN (fun s c => W s c fs) K (ms fs) exe endPc (R.callee (-(fr.size : Int) - 56 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-(fr.size : Int) - 56 - 8) (-24) 16 m0 m ∧
          Abs R ⟨-(fr.size : Int) - 56, []⟩ m0 σC) c0)
    (Q : FragS isa) :
    SegWS W K p lbl ms
      ((At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl it x e c1)).at fs) Q := by
  refine (SegWS.liftS fs (Abort.Disp.seg_jabort4W (W := fun s c => W s c fs) (K := K) (exe := exe)
    (endPc := endPc) (p := p) (lbl := lbl) (Q := fun _ _ => False)
    (nC := printNAS (_root_.Executable.labels exe).label fr lbl it x e c1) rfl
    (fun σ c hJ => hJ.1.1) hF hR (by simp only [printNAS]; omega) (by simp only [printNAS]; omega)
    (by simp only [printNAS]; omega) hK (fun m0 σC c0 hJ => ?_)) fun _ _ h => h).mono_post
    fun _ _ _ h => h.1.elim
  refine (hstub m0 σC c0 hJ).stubWW hp hend hprog hK ?_
  exact fstable_enter (kb := -(fr.size : Int) - 56 - 8) hR hF (by omega) (by decide) (by omega) (by omega)
    (by omega) (by decide) (by decide)

/-! ## The write path inside `W2` -/

section W2

open A9NoSpawn
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Kraken.Promising.Lower.X64 (op64)
open Spike.Lib.X64.StubW (stubWW_sfactsA abortPhWriteOk phOne RefCtl sfactsA_sysW memSys syscallCall_write)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop}
  {lsize : Lsize} {fs : List TermRun.Frame} {K : State → State → Prop}

/-- **`W2` from `SFactsA` in the same abort phase** (at owned words with no
frame dependence) and no output `write(1, …)` (`hw1`). -/
theorem w2_of_sfactsA_ab {s : State} {c : Ctl}
    (h : SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab) (hw1 : NoW1 s) :
    W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs where
  st := ⟨h.noSite, h.mapped, h.svc, h.ownInstr c fs (.refl _), h.ownSys c fs (.refl _), h.ownTake, h.site,
    h.tkTake, h.tkInstr, h.tkSys, h.owned, h.wrTail⟩
  ab := ⟨h.abInstr, h.abSys, h.abTake⟩
  noRet := h.noRet
  run := ⟨h.cell, h.zero⟩
  place := h.place
  wr := h.wr
  abort := h.abortOk
  svc1 hs b n hd := (hw1 hs b n hd).elim

omit [Kraken.Executable.ValidLayout exe] in
/-- **A block's states inside `W2`** from `SFactsA` in the same abort phase
and no output `write(1, …)`. -/
theorem BlkW.w2_sfactsAb {n : ND} {blk : List (Directive × Nat)}
    (hS : BlkW (fun s c => SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab)
      K exe endPc R F n blk)
    (hP : BlkW (fun s _ => NoW1 s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n blk :=
  Spike.Lib.X64.AllocG.BlkW.imp hS hP fun _ _ h1 h2 => w2_of_sfactsA_ab h1 h2

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node's states inside `W2`** from `SFactsA` in the same abort phase
(as `BlkW.w2_sfactsAb`). -/
theorem NodeW.w2_sfactsAb {n : ND}
    (hS : NodeW (fun s c => SFactsA Λ μ p rd G (fun s _ => own s) rS Tk ar J lbl lsize s c fs Dt Ab)
      K exe endPc R F n)
    (hP : NodeW (fun s _ => NoW1 s) (fun _ _ => False) exe endPc R F n) :
    NodeW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n :=
  Spike.Lib.X64.AllocG.NodeW.imp hS hP fun _ _ h1 h2 => w2_of_sfactsA_ab h1 h2

omit [Kraken.Executable.ValidLayout exe] in
/-- **No output `write(1, …)` at a covered block** (off a system call,
`blkW_noSys'`). -/
theorem blkW_noW1 {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => NoW1 s) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.X64.AllocG.BlkW.imp (W1 := fun s _ => abi.atSys s = false) (blkW_noSys' hcode hok)
    (blkW_noSys' hcode hok) fun _ _ h _ hs => absurd hs (by rw [h]; decide)

omit [Kraken.Executable.ValidLayout exe] in
/-- **No output `write(1, …)` at a single instruction without an event**
(`SI`). -/
theorem nodeW_noW1_si {n : ND} {si : SI} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(si.toDir, z)]) :
    NodeW (fun s _ => NoW1 s) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -⟩ := id hA
  have hc := (hcode s hs hn).cell0 rfl rfl hpc
  refine ⟨fun hs' => ?_, fun _ h => h⟩
  rw [show abi.atSys s = false from atSyscall_false_of_cellAt hc (by cases si <;> intro _ _ h <;> cases h)]
    at hs'
  cases hs'

variable {lab : Label → Int64} {okPc : Nat → Bool} {ph : Nat → Nat}

/-- **The write stub's `write` call's states in `SFactsA … (WriteAb.Ab
lab)`** (as in `stubWW_sfactsA`, whose `StubWW` gives that call as a
segment). -/
theorem stubWW_sfactsA_sys {kp : Nat} {own : OwnS} {frs : List TermRun.Frame}
    (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhWriteOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.write c0 .sys) s c → Dt s) :
    NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (WriteAb.Ab lab)) K exe
      endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .sys) := by
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, hsysIn, -⟩ := hst
  simp only [abortPhWriteOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, o5, q5, -, -⟩ := hphs
  have he34 : (_root_.Executable.labels exe).label Abort.write.entry + Int64.ofNat 34 =
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .sys).pc := rfl
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
  have hc0 : c = c0 := hJ
  subst hc0
  have hAb : WriteAb.Ab (_root_.Executable.labels exe).label s := WriteAb.ab_stub (by rw [hpc]; exact memSys)
  rw [← he34] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o5)
  have hown : Tk s → Owned Λ rS s := fun _ =>
    Spike.Lib.X64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  exact ⟨sfactsA_sysW hc (hc.place s hD) hP.1.noSite hP.1.noTake
    (Spike.Lib.X64.Rt.cellOf hI hsysIn rfl hs hn hpc) (Spike.Lib.X64.Rt.next_same hI hpc q5) hown
    (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAb, hP.2⟩

/-- **`printAbSeg2`'s `hstub`: `StubWN` inside `W2 … (WriteAb.Ab lab)`** at
the frames `fs`, from `stubWW_sfactsA`'s premises at the owned words
`fun s _ => own s` (the path's states in `SFactsA` in the write abort's
phase): the path's blocks and single instructions are off a system call,
the `write` is to the error output (`%rdi = 2`), the exit call
`exit_group`. -/
theorem stubWN_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hphs : abortPhWriteOk okPc ph lab = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p (fun s _ => own s) lbl F c0 fs)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.write.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.write.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.write.exit).toBitVec.toNat = a → k = .writeErr)
    (hKex : ∀ s s', pcOf s = (lab Abort.write.exit).toBitVec.toNat → ¬ K s s')
    {ms : MemSide isa} (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.write.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.write c0 .sys) s c → Dt s) :
    StubWN (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (WriteAb.Ab lab) lbl lsize s c fs) K ms exe endPc R F
      c0 := by
  have hS := stubWW_sfactsA (p := p) (al := lbl) (own := fun s _ => own s) (frs := fs) (rd := rd) (G := G)
    (ar := ar) (J := J) (lsize := lsize) hI hprog hphs hR hR8 hlo hhi hl hh hF hsub hfit hFO hc hrel htk hk
    hKex hms hK hwr
  have hSys := stubWW_sfactsA_sys (own := fun s _ => own s) (frs := fs) (rd := rd) (G := G) (ar := ar) (J := J)
    (lsize := lsize) hI hprog hphs hR hR8 hl hh hsub hFO hc hwr
  have hlab := hI.labOk
  subst hlab
  have hsd := hprog
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hsc := Scc.Cert.Rt.X64.Abort.code_stub (c0 := c0) hI.lays hI.endOk hsd.1.1.2
  have hdc := Scc.Cert.Rt.X64.Abort.code_disp (c0 := c0) hI.lays hI.endOk hsd.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hS.ab⟩
  · exact BlkW.w2_sfactsAb hS.de (blkW_noW1 hdc.e Abort.Disp.d0_ok)
  · exact BlkW.w2_sfactsAb hS.dt1 (blkW_noW1 hdc.t1 Abort.Disp.t1_ok)
  · exact BlkW.w2_sfactsAb hS.dj1 (blkW_noW1 hdc.j1 Abort.Disp.j1_ok)
  · exact BlkW.w2_sfactsAb hS.dt2 (blkW_noW1 hdc.t2 Abort.Disp.t2_ok)
  · exact BlkW.w2_sfactsAb hS.dj2 (blkW_noW1 hdc.j2 Abort.Disp.j2_ok)
  · exact BlkW.w2_sfactsAb hS.dt3 (blkW_noW1 hdc.t3 Abort.Disp.t3_ok)
  · exact BlkW.w2_sfactsAb hS.dj3 (blkW_noW1 hdc.j3 Abort.Disp.j3_ok)
  · exact BlkW.w2_sfactsAb hS.dt4 (blkW_noW1 hdc.t4 Abort.Disp.t4_ok)
  · exact BlkW.w2_sfactsAb hS.dg4 (blkW_noW1 hdc.g4 Abort.Disp.g4_ok)
  · exact BlkW.w2_sfactsAb hS.se (blkW_noW1 hsc.e Abort.x0_ok)
  · exact NodeW.w2_sfactsAb hS.sn1 (nodeW_noW1_si hsc.n1)
  · exact BlkW.w2_sfactsAb hS.sn2 (blkW_noW1 hsc.n2 Abort.x1Write_ok)
  · refine NodeW.w2_sfactsAb hSys fun s c hA => ⟨fun _ b k hw => ?_, fun _ h => h⟩
    obtain ⟨-, -, -, -, σ, hA', -, -, hdi, hax⟩ := hA
    obtain ⟨b', k', hw'⟩ := syscallCall_write (r := s.st.1.regs) (by rw [hA'.regs]; exact hax)
      (by rw [hA'.regs]; exact hdi)
    have hw'' : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 2 b' k') := hw'
    rw [hw''] at hw
    cases hw
  · exact BlkW.w2_sfactsAb hS.sn5 (blkW_noW1 hsc.n5 Abort.x2_ok)
  · refine NodeW.w2_sfactsAb hS.sex fun s c hA => ⟨fun _ b k hw => ?_, fun _ h => h⟩
    obtain ⟨-, -, -, -, σ, hA', -, -, hax, -⟩ := hA
    have hx : s.st.1.regs.rax.toNat = 231 := by
      rw [hA'.regs]
      simp only [Reg64s.get64] at hax
      rw [← UInt64.toNat_toBitVec, hax]; rfl
    have hd : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) :=
      Spike.Lib.X64.syscallCall_exitGroup hx
    rw [hd] at hw
    cases hw

end W2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.printAbSeg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printAbSeg2

/-- info: 'Spike.Lib.LowerX64.printAbSeg2P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printAbSeg2P

/-- info: 'Spike.Lib.LowerX64.w2_of_sfactsA_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w2_of_sfactsA_ab

/-- info: 'Spike.Lib.LowerX64.stubWN_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubWN_w2

end PrintAbW2

end Spike.Lib.LowerX64
