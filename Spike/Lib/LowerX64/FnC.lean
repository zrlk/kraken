/-
**A lowered `Accepted1` function with calls is one segment at fixed frames**
(x86-64, H7a calls): the prologue (`prologue_body_seg`) lifted at the frames
`fs`, then the body (`bodyC_segS`), the calls a premise
(`CallC`). The twin of `Spike/Lib/LowerX64/Fn1.lean`'s `fn1_seg` with
calls; the per-function step of the induction over the program's
declarations (every callee's specification from its own `fnC_segS`).

- `prologue_body_segT`: `prologue_body_seg` at a node with the thread
  pointer: the prologue keeps the `%fs` base (`xFrRegs`), so the body's
  entry node has it (`ND.withTp`).
- `fnC_segS`: from the function's label at `fs` (`%rsp` at 0, the entry
  invariant `J` pinning the `%fs` base to `tp`) to the body's exits
  `ExitC` in the rebased region `rbR R`.
-/
import Spike.Lib.LowerX64.ProIn
import Spike.Lib.LowerX64.BodyC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (prologueIn prologue_seg_ofW XProW xStSlots xS1 xFrRegs hdRegs)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.Form (SEnv)
open Spike.Lib.LowerNode
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (lowerC Res1)

section Pro

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}

/-- **The prologue at a node with the thread pointer** (`prologue_body_seg_of`
with every entry state's `%fs` base `tp`, `htp`): the prologue writes no
`%fs` base, so the body's entry node is one with the thread pointer. -/
theorem prologue_body_segT {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31)
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn entry : String} {zl zf z1 z2 zs : Nat}
    (hin : proInC cells fr fn entry zl zf z1 z2 zs = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv} {tp : UInt64}
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [] J)
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ (∀ sl, NJ p lbl (rsOf fr) t s sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc (rbR R) F
        ((bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).withTp tp)) := by
  have hZ : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  refine (prologue_seg_ofW (nb := ⟨(_root_.Executable.labels exe).label entry,
      Spike.Lib.X64.Flow.oF (Int64.ofInt fr.size), fun σ c =>
        (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).J
          { σ with slot := shSl σ.slot } c ∧ σ.regs.fsBase = tp⟩)
    hp hend hin (by rw [hZ]; omega) hF hR (by rw [hZ]; exact hlo) (by omega) (by simp) rfl
    (by simp [SO.le, lk]) hW fun σ c hJ => ?_).mono_post fun _ _ h =>
      at_rbR (J' := fun σ c => (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).J σ c ∧
          σ.regs.fsBase = tp)
        (by show -8 - _ = _; rw [hZ]) (by simp [SO.get, lk]) (fun _ _ h => h) h
  obtain ⟨⟨hrt, hmp, hld, hG⟩, hfp, hra, hN, hc0⟩ := hedge σ c hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' hr hsl => ⟨⟨hN _, ?_, hc0⟩, ?_⟩⟩⟩
  · simp only [xStSlots] at hsl
    constructor <;> simp [shSl, hsl, xS1, upd_apply, hfp, hra]
  · rw [hr]
    simp [xFrRegs, hdRegs, Reg64s.set64, htp σ c hJ]

/-- **The emitted prologue with one parameter's spill**: `proInC` with the
store of `%rdi` at `o` (cell size `zp`). -/
def proInCP (cells : List (Directive × Nat)) (fr : Scc.Emit.X64.Frame) (fn entry : String)
    (zl zf z1 z2 zs : Nat) (o : Int64) (zp : Nat) : Bool :=
  prologueIn cells fn (Scc.Emit.X64.labelOf fr.fn "chk") entry (Int64.ofInt fr.size)
    (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [(.rdi, o, zp)]

/-- **The prologue with a parameter's spill at a node with the thread
pointer** (`prologue_body_segT` with `proInCP`): the parameter register
`pr`'s cell (`rsOf fr pr`, at `o`, `hpr`) holds the entry's `%rdi`, so the
source relation `NJ` is needed only at cells with it (`hedge`). -/
theorem prologue_body_segTP {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31)
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn entry : String} {zl zf z1 z2 zs : Nat}
    {o : Int64} {zp : Nat} (hin : proInCP cells fr fn entry zl zf z1 z2 zs o zp = true)
    {pr : Scc.IR.Reg} (hpr : ∀ k, rsOf fr pr = some k → k = o.toInt) (ho : o.toInt ≤ -8)
    (hoff : offOk (-8 - (fr.size : Int)) 0 (-8 + o.toInt) = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl} {t : Expr} {s : SEnv} {tp : UInt64}
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [(.rdi, o, zp)] J)
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧
      (∀ sl, (∀ k, rsOf fr pr = some k → sl k = σ.regs.rdi.toBitVec) → NJ p lbl (rsOf fr) t s sl c) ∧
      LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc (rbR R) F
        ((bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).withTp tp)) := by
  have hZ : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  refine (prologue_seg_ofW (nb := ⟨(_root_.Executable.labels exe).label entry,
      Spike.Lib.X64.Flow.oF (Int64.ofInt fr.size), fun σ c =>
        (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).J
          { σ with slot := shSl σ.slot } c ∧ σ.regs.fsBase = tp⟩)
    hp hend hin (by rw [hZ]; omega) hF hR (by rw [hZ]; exact hlo) (by omega)
    (by simpa [hZ] using hoff) rfl
    (by simp [SO.le, lk]) hW fun σ c hJ => ?_).mono_post fun _ _ h =>
      at_rbR (J' := fun σ c => (bodyN p lbl fr fp ra c0 ((_root_.Executable.labels exe).label entry) t s).J σ c ∧
          σ.regs.fsBase = tp)
        (by show -8 - _ = _; rw [hZ]) (by simp [SO.get, lk]) (fun _ _ h => h) h
  obtain ⟨⟨hrt, hmp, hld, hG⟩, hfp, hra, hN, hc0⟩ := hedge σ c hJ
  refine ⟨hrt, hmp, hld, fun v hv => ⟨hG v hv, fun σ' hr hsl => ⟨⟨hN _ fun k hk => ?_, ?_, hc0⟩, ?_⟩⟩⟩
  · rw [hpr k hk]
    simp only [xStSlots] at hsl
    simp [shSl, hsl, upd_apply, hr, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64]
  · simp only [xStSlots] at hsl
    have h0 : (-8 : Int) ≠ -8 + o.toInt := by omega
    have h8 : (0 : Int) ≠ -8 + o.toInt := by omega
    constructor <;> simp [shSl, hsl, xS1, upd_apply, hfp, hra, h0, h8]
  · rw [hr]
    simp [xFrRegs, hdRegs, Reg64s.set64, htp σ c hJ]

end Pro

section FnC

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : FragS isa} {K : State → State → Prop}

/-- **A lowered `Accepted1` function with calls is one segment at the
frames `fs`**: from the function's label (`%rsp` at 0, the entry invariant
`J` with the `%fs` base `tp`, `htp`) through the prologue (`hpro`, its
states inside `W₀`, `hWpro`, its limit facts and the entry's ghosts,
`hedge`) and the body (`bodyC_segS` in the rebased region `rbR R`, the
code `hcode`/`hbl` at the code predicate `Cd`, the calls `hcall`) to
the body's exits (`ExitC`): the return's exit at `fs` after the source's
frame run from the ghost `c0`, or an abort `Ab`. -/
theorem fnC_segS {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn entry : String}
    {zl zf z1 z2 zs : Nat} (hpro : proInC cells fr fn entry zl zf z1 z2 zs = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {fp ra : BitVec 64} {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hWb : ∀ c0, G0 c0 → ∀ pc t s blk, SubCd Cd pc blk → Kind1 fr blk →
      BlkW W₀ K exe endPc (rbR R) F (bodyN p lbl fr fp ra c0 pc t s) blk)
    (hWs : ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd Cd pc blk → Kind1 fr blk →
      BlkW W₀ K exe endPc (rbR R) F (pendN p lbl fr fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc (rbR R) F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    (hcall : CallC p lbl lcx fr Cd Bl exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab)
    {e : Expr} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res1} {kk : Nat}
    (hr : lowerC lcx env n l k e = some r) (hfr : Fresh env n)
    (hcode : CodeC fr Cd Bl kk ((_root_.Executable.labels exe).label entry) r.insts r.term)
    (hbl : BlocksCodeC fr Cd Bl (_root_.Executable.labels exe).label r.blocks)
    (hImm : ∀ q ∈ lowerEnvsC lcx.frames env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1)
    (hOne : ∀ q ∈ lowerEnvsC lcx.frames env n e, RetOne q)
    {J : AS → Ctl → Prop} {c0 : Ctl} (hg0 : G0 c0)
    (hWpro : XProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [] J)
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hedge : ∀ σ c, J σ c →
      ((ms fs).rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        (ms fs).mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, (ms fs).G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ (∀ sl, NJ p lbl (rsOf fr) e (ofEnv env) sl c) ∧ LocalRun p c0 c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc (rbR R) F fp ra tp c0 fs Ab) :=
  (SegWS.liftS fs (prologue_body_segT h1 hp hend hpro hF hR hlo hhi hWpro htp hedge) hW₀).seq
    (bodyC_segS hf h1 (rbR_fstable hR (by omega) (by omega) hF) (rbR_ok hR (by omega) (by omega))
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      hCd hW₀ hG0 hWb hWs hab hfrm hcall e env n l k r kk _ hr hfr hcode hbl hImm hOne c0 hg0)

/-- **A lowered `Accepted1` function with a parameter is one segment at
the frames `fs`** (`fnC_segS` with `prologue_body_segTP`): the parameter
register `pr`'s cell holds the entry's `%rdi`. -/
theorem fnC_segSP {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn entry : String}
    {zl zf z1 z2 zs : Nat} {o : Int64} {zp : Nat} (hpro : proInCP cells fr fn entry zl zf z1 z2 zs o zp = true)
    {pr : Scc.IR.Reg} (hpr : ∀ k, rsOf fr pr = some k → k = o.toInt) (ho : o.toInt ≤ -8)
    (hoff : offOk (-8 - (fr.size : Int)) 0 (-8 + o.toInt) = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 8 ≤ R.hi)
    {fp ra : BitVec 64} {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hWb : ∀ c0, G0 c0 → ∀ pc t s blk, SubCd Cd pc blk → Kind1 fr blk →
      BlkW W₀ K exe endPc (rbR R) F (bodyN p lbl fr fp ra c0 pc t s) blk)
    (hWs : ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd Cd pc blk → Kind1 fr blk →
      BlkW W₀ K exe endPc (rbR R) F (pendN p lbl fr fp ra c0 pc t s k) blk)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc (rbR R) F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    (hcall : CallC p lbl lcx fr Cd Bl exe endPc (rbR R) F W K ms fp ra tp fs G0 i T Ab)
    {e : Expr} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res1} {kk : Nat}
    (hr : lowerC lcx env n l k e = some r) (hfr : Fresh env n)
    (hcode : CodeC fr Cd Bl kk ((_root_.Executable.labels exe).label entry) r.insts r.term)
    (hbl : BlocksCodeC fr Cd Bl (_root_.Executable.labels exe).label r.blocks)
    (hImm : ∀ q ∈ lowerEnvsC lcx.frames env n e, ImmIn i (ofEnv q.2.1) q.1 ∧ T q.1)
    (hOne : ∀ q ∈ lowerEnvsC lcx.frames env n e, RetOne q)
    {J : AS → Ctl → Prop} {c0 : Ctl} (hg0 : G0 c0)
    (hWpro : XProW W₀ K exe endPc R F (ms fs) ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [(.rdi, o, zp)] J)
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hedge : ∀ σ c, J σ c →
      ((ms fs).rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        (ms fs).mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, (ms fs).G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧ (∀ sl, (∀ k, rsOf fr pr = some k → sl k = σ.regs.rdi.toBitVec) → NJ p lbl (rsOf fr) e (ofEnv env) sl c) ∧ LocalRun p c0 c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩).at fs)
      (ExitC p lbl exe endPc (rbR R) F fp ra tp c0 fs Ab) :=
  (SegWS.liftS fs (prologue_body_segTP h1 hp hend hpro hpr ho hoff hF hR hlo hhi hWpro htp hedge) hW₀).seq
    (bodyC_segS hf h1 (rbR_fstable hR (by omega) (by omega) hF) (rbR_ok hR (by omega) (by omega))
      (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
      hCd hW₀ hG0 hWb hWs hab hfrm hcall e env n l k r kk _ hr hfr hcode hbl hImm hOne c0 hg0)

end FnC

end Spike.Lib.LowerX64
