/-
**Allocation and lane stores at any call depth**: `newBuf_callW`,
`newBuf_blkW` (`Spike/Lib/A64NewBuf.lean`) and `lane_storeW`
(`Spike/Lib/A64LaneStore.lean`) as segments with the source thread's frames
(`SegWS`, `Spike/Lib/SegS.lean`), at any fixed frames `frs`: the same
premises, under the memory side at `frs` (`msS frs = ms`; any, for the lane
store), inside any `W'` that contains `W` at `frs`. Each is `SegWS.liftS` of the one-frame rule.
-/
import Spike.Lib.A64NewBuf
import Spike.Lib.A64LaneStore
import Spike.Lib.SegS

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib

namespace NewBuf

open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull mOf)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`newBuf_callW` at any call depth.** -/
theorem newBuf_callWS {W : Frag isaLSE2} {W' : FragS isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} (hfs : fs % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hkc : -fs < R.hi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0) (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m))
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) :
    SegWS W' K p lbl msS
      (Frag.at (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs, []⟩, Jc⟩) frs)
      (Frag.at (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc x) s c)
        frs) := by
  have h := newBuf_callW (p := p) hp hend hprog hF hR hal hfs hlo hkc hq hra hmem hxa
    fun q _ h => hW q h
  subst hms
  exact SegWS.liftS frs h hWS'

/-- **`newBuf_blkW` at any call depth.** -/
theorem newBuf_blkWS {W : Frag isaLSE2} {W' : FragS isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} (hfs : fs % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fs) (hkc : -fs < R.hi)
    {B : List Directive} {pc pcR : Int64} {lo hi : Int} {J J1 : AS → Ctl → Prop}
    (hne : B ≠ []) (hok : okBlk lo hi ⟨-fs, []⟩ B = true) (hlo0 : R.lo ≤ lo) (hhi0 : hi ≤ R.hi)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B)
    (ha : ∀ σ, (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).pc =
        (_root_.Executable.labels exe).label "scc_rt_alloc" ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).so = ⟨-fs, []⟩)
    (hloc : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ J1 σ c')
    (hq : ∀ σ c, J1 σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X0.toBitVec = q.h ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X1.toBitVec = q.k ∧
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, J1 σ c →
      (arun (_root_.Executable.labels exe).label B ⟨pc, ⟨-fs, []⟩, σ⟩).σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1 σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hWB : BlkW W K exe endPc R F ⟨pc, ⟨-fs, []⟩, J⟩ B)
    (hW : ∀ q : Call, q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0) (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m))
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame) (hms : msS frs = ms)
    (hWS' : ∀ s c, W s c → W' s c frs) :
    SegWS W' K p lbl msS (Frag.at (At exe endPc R F ⟨pc, ⟨-fs, []⟩, J⟩) frs)
      (Frag.at (fun s c => ∃ x, At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR
        (nbJc (_root_.Executable.labels exe).label B pc ⟨-fs, []⟩ J1) x) s c) frs) := by
  have h := newBuf_blkW (p := p) hp hend hprog hF hR hal hfs hlo hkc hne hok hlo0 hhi0 hc ha hloc hq hra
    hmem hxa hWB fun q _ h => allocW_mono (hW q h) fun _ h => ⟨h.1, h.2.1⟩
  subst hms
  exact SegWS.liftS frs h hWS'

end NewBuf

namespace LaneStore

open TermRun
open Scc.Sem (ValRep)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`lane_storeW` at any call depth** (under any memory side: the rule
does not depend on it). -/
theorem lane_storeWS {W : Frag isaLSE2} {W' : FragS isaLSE2} {Kw : State → State → Prop} {B1 B2 : List Directive}
    {pc pcL pcS : Int64} {o oL oS : SO} {lo hi : Int} {t b t' : XReg} {i : Int64}
    {w ov bn : String} {sg : Bool} {wd : Wd} {K i' : Nat} {e : Expr} {J J' : AS → Ctl → Prop}
    (h1ne : B1 ≠ []) (h2ne : B2 ≠ []) (hok1 : okBlk lo hi o B1 = true) (hok2 : okBlk lo hi (oL.kill t) B2 = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc B1)
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcL [ldrDir t b i])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pcL + Int64.ofNat 4) B2)
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pcS [strDir t' b i])
    (ha1 : ∀ σ, (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).pc = pcL ∧
      (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).so = oL)
    (ha2 : ∀ σ, (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, σ⟩).pc = pcS ∧
      (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, σ⟩).so = oS)
    (hle : SO.le oL oL = true ∧ SO.le (oL.kill t) (oL.kill t) = true ∧ SO.le oS oS = true)
    (hbw : bn ≠ w) (hK : K < 2 ^ 64)
    (ht : ∀ σ c, J σ c → c.term = .let_ w (.asLanes sg wd (.lit K)) (.let_ ov (.xchgAt (.var bn) (.lit i') (.var w)) e))
    (hsrc : ∀ σ c, J σ c → ∃ (ty : Ty) (pw : Word) (μ : Mode) (l : WeakMem.AllocLabel) (A : Nat),
      evalAt c.env (.var bn) = some (ty, [pw]) ∧ pw.val = .loc ⟨l, 0⟩ 0 ∧ bufElem ty = some (μ, .lanes sg wd) ∧
      lbl l = some A ∧
      (rAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i).toNat = A + 8 * i' ∧
      (∀ m, F m → Mem.loadInt m.dmem (rAddr (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ.regs b i) 8
        = none) ∧
      ∀ r : BitVec 64,
        let σ1 := (arun (_root_.Executable.labels exe).label B1 ⟨pc, o, σ⟩).σ
        let σ2 := (arun (_root_.Executable.labels exe).label B2 ⟨pcL + Int64.ofNat 4, oL.kill t, ldStep t r σ1⟩).σ
        rAddr σ2.regs b i = rAddr σ1.regs b i ∧
        ((σ2.regs.getRegOrZr (.low (.reg t') .W64)).setWidth 128).toNat = K ∧
        ∀ wold : Word, J' σ2 ⟨e, (ov, .lanes sg wd, [wold]) :: (lsC1 w ov bn sg wd K i' e c).env, none⟩)
    (hW1 : BlkW W Kw exe endPc R F ⟨pc, o, J⟩ B1)
    (hWL : NodeW W Kw exe endPc R F (lsNL (_root_.Executable.labels exe).label B1 pc pcL o oL w ov bn sg wd K i' e J))
    (hW2 : BlkW W Kw exe endPc R F
      (lsNH (_root_.Executable.labels exe).label B1 pc pcL o oL t b i w ov bn sg wd K i' e J) B2)
    (hWS : NodeW W Kw exe endPc R F
      (lsNS (_root_.Executable.labels exe).label B1 B2 pc pcL pcS o oL oS t b i w ov bn sg wd K i' e J))
    (msS : List TermRun.Frame → MemSide isaLSE2) (frs : List TermRun.Frame)
    (hWS' : ∀ s c, W s c → W' s c frs) :
    SegWS W' Kw p lbl msS (Frag.at (At exe endPc R F ⟨pc, o, J⟩) frs)
      (Frag.at (At exe endPc R F ⟨pcS + Int64.ofNat 4, oS, J'⟩) frs) := by
  have h := lane_storeW (p := p) (lbl := lbl) (ms := msS frs) h1ne h2ne hok1 hok2 hF hR hal hlo hhi
    hc1 hc2 hc3 hc4 ha1 ha2 hle hbw hK ht hsrc hW1 hWL hW2 hWS
  exact SegWS.liftS frs h hWS'

end LaneStore

end Spike.Lib.A64.Flow
