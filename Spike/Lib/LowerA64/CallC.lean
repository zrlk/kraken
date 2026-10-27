/-
**The plain call** (AArch64, the lowering without the depth counter):
`CallC` (`Spike/Lib/LowerA64/BodyC.lean`) from the callees' segments
(`CalleeSegs`, `Spike/Lib/LowerA64/ProgCB.lean`) and the call's blocks inside
`W` (`callC_of`), so the call premise `CallPre` (`callPreC_of`). The twin of
`Spike/Lib/LowerX64/CallC.lean`.

The call's walk, all at the caller's frames `fs` but the callee's segment
(at `fr :: fs`):

- `argC_seg`: `w`'s load into `x0` from the body's node, the source's local
  run taken to the call exactly (`csN`);
- `blC_seg`: `bl g` (`blD_run`), to the call node at `g`'s label, the return
  address in `x30`, at the caller's frame offsets (`bl` pushes nothing);
- `calleeC_seg`: the callee (`call_ndSF`, its region
  `R.callee (-frame) (-D) 0`, its entry `calleeN`, its exits `exN`: `ExitC`'s
  return with the callee's frame run), back at the return address (`retCN`)
  with the source returned into `x` (`FrameStep.ret`, the result's word a
  number represented by `x0`), the caller's frames re-anchored from the
  call's ghost `c0` by a frame run, the caller's cells outside the callee's
  region kept (the environment, the saved pair);
- `resC_seg`: `x0`'s store into `r%n`, to the body's node at `e`.

Where AArch64 differs from x86-64: `bl` writes `x30`, no memory, so the call
node is at the caller's offsets `oF cx` and the callee's region starts at the
frame's bottom (`R.callee (-frame) (-D) 0`, no return-address cell); `x29`
is not part of the caller's nodes (the frame's cells are `sp`-relative).
-/
import Spike.Lib.LowerA64.ProgCB
import Spike.Lib.LowerA64.CallSite
import Spike.Lib.LowerA64.CallBlkW

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl SRep opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (CallerCells setXReg_TPIDR)
open Scc.Lower.Inv (regName labName atomV)
open Spike.Lib.LowerCall (Callee)

set_option linter.unusedSimpArgs false

/-! ## The call's nodes -/

/-- **A node of a call** at `pc`: the source exactly at `t` (the
environment `s` placed in the frame's cells), its words numbers, the saved
pair, the source control in `Rn` (reached from the caller's ghost), the
thread pointer `tp`, and the call's own facts `P`. -/
def csN (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (tp : UInt64)
    (Rn : Ctl → Prop) (pc : Int64) (t : Expr) (s : SEnv) (P : AS → Prop) : ND :=
  ⟨pc, oF cx, fun σ c => NodeJ lbl (rsOf cx) t s σ.slot c ∧ EnvNum c.env ∧ FrJ fp ra σ.slot ∧ Rn c ∧
    σ.regs.TPIDR_EL0 = tp ∧ P σ⟩

/-- **A call's straight blocks**: `w`'s load into `x0`, or `x0`'s store
into a register's slot. -/
def CallBlk (cx : FnCtx) (blk : List Directive) : Prop :=
  (∃ w lw, cx.getOp .X0 w = .ok lw ∧ blk = directives lw) ∨
    ∃ d ls, cx.setReg d .X0 = .ok ls ∧ blk = directives ls

/-- The call node's facts for the callee: `x0` the argument `w`'s value,
the return address `pcR` in `x30`. -/
def callP (cx : FnCtx) (w : Scc.IR.Operand) (pcR : Int64) (σ : AS) : Prop :=
  opdVal (rsOf cx) σ.slot w = some σ.regs.X0.toBitVec.toNat ∧ σ.regs.X30.toBitVec = pcR.toBitVec

/-- **Back from the callee** at the return address `pc`: the source
returned at `e` whose environment `s` the frame's cells place with `x0`
stored to the result's cell `off`, its words numbers, the saved pair, the
source reached from the call's ghost `c0` by a frame run at the frames `fs`,
the thread pointer `tp`. -/
def retCN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (tp : UInt64)
    (c0 : Ctl) (fs : List TermRun.Frame) (pc : Int64) (e : Expr) (s : SEnv) (off : Int) : ND :=
  ⟨pc, oF cx, fun σ c => NodeJ lbl (rsOf cx) e s (upd σ.slot off σ.regs.X0.toBitVec) c ∧ EnvNum c.env ∧
    FrJ fp ra σ.slot ∧ FrameRun p (c0, fs) (c, fs) ∧ σ.regs.TPIDR_EL0 = tp⟩

/-- **The callee's exit** (`ExitC`'s return in the callee's region): the
callee's entry control `q.cE` runs at the pushed frames to `c0'`, from which
the return's exit holds. -/
def exN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (tp : UInt64) (fs : List TermRun.Frame) (q : CallG)
    (frm : TermRun.Frame) (c0' : Ctl) : ND :=
  ⟨Int64.ofBitVec q.ra, ⟨0, []⟩, fun σ c => FrameRun p (q.cE, frm :: fs) (c0', frm :: fs) ∧
    ((retN p lbl q.fp q.ra c0').withTp tp).J σ c⟩

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The argument's load and `bl g` -/

/-- **The argument's load into `x0`** from the body's node: the source's
local run taken to the call exactly (`csN`), `x0` holding `w`'s value. -/
theorem argC_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW W₀ K exe endPc R F n blk)
    {w : Scc.IR.Operand} {lw : List Item} (hw : cx.getOp .X0 w = .ok lw) {pc : Int64}
    (hc : Cd pc (directives lw)) {t : Expr} {s : SEnv} :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN p lbl cx fp ra c0 pc t s).withTp tp))
      (At exe endPc R F (csN lbl cx fp ra tp (LocalRun p c0) (pc + Int64.ofNat (4 * (directives lw).length)) t s
        fun σ => opdVal (rsOf cx) σ.slot w = some σ.regs.X0.toBitVec.toNat)) := by
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hCd _ _ hc)
    (hWB _ _ (SubCd.whole hc) rfl (fun σ c h => ⟨hG c h.1.2.2, h.1.2.1⟩) (.inl ⟨w, lw, hw, rfl⟩))
    (getOp_ne_nil hf h1 hw) (okBlk_argLoad hf h1 h16 hw) ?_
  rintro σ c ⟨⟨⟨c', hr, hj, hn⟩, hfj, hc0⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨v, hv, hrr⟩ := arun_getOp hf h1 hw (_root_.Executable.labels exe).label pc σ
  show Hit _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  rw [hrr]
  refine ⟨rfl, so_le_refl _ rfl, hj, hn, hfj, hc0.trans hr, ?_, ?_⟩
  · show (σ.regs.setXReg .X0 v).TPIDR_EL0 = tp
    rw [setXReg_TPIDR]; exact htp
  · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X0 v).X0.toBitVec.toNat
    simpa [Reg64s.setXReg] using hv

/-- **`bl g` is one segment**: from a call node at the `bl` (`Bl`) to the
call node at `g`'s label, at the same offsets, the return address `pc + 4`
in `x30`; the call's facts from `P` to `P'` (`hP`). -/
theorem blC_seg {cx : FnCtx} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2}
    {fp ra : BitVec 64} {tp : UInt64} {Bl : Int64 → Label → Nat → Prop}
    (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c)
    (hWBl : ∀ (n : ND) g k, Bl n.pc g k → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [blD g])
    {pc : Int64} {g : Label} {k : Nat} (hb : Bl pc g k) {t : Expr} {s : SEnv} {P P' : AS → Prop}
    (hP : ∀ σ, P σ → P' { σ with regs := σ.regs.setXReg .X30 (pc + 4).toBitVec }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (csN lbl cx fp ra tp Rn pc t s P))
      (At exe endPc R F (csN lbl cx fp ra tp Rn ((_root_.Executable.labels exe).label g) t s P')) := by
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hBl _ _ _ hb)
    (hWBl _ _ _ hb rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (by simp) (okBlk_blD _ _ _ g)
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit (csN lbl cx fp ra tp Rn ((_root_.Executable.labels exe).label g) t s P')
    (arun (_root_.Executable.labels exe).label [blD g] ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c
  erw [blD_run]
  obtain ⟨hj, hn, hfj, hr, htp, hp⟩ := hJ
  refine ⟨rfl, so_le_refl _ rfl, hj, hn, hfj, hr, ?_, hP σ hp⟩
  show (σ.regs.setXReg .X30 _).TPIDR_EL0 = tp
  rw [setXReg_TPIDR]; exact htp

/-! ## The callee -/

/-- **A frame cell is outside the callee's region**: a cell of the frame
(`[-frame, 0)`) is a cell of the caller's region, not of the callee's below
the frame. -/
theorem frame_outC {R : Region} {fr : Nat} {D : Int} (hD0 : 0 ≤ D) (hlo : R.lo ≤ -(fr : Int) - D) (hhi : 0 ≤ R.hi)
    {k : Int} (hk8 : k % 8 = 0) (hk1 : -(fr : Int) ≤ k) (hk2 : k + 8 ≤ 0) :
    R.Off k ∧ ¬ (R.callee (-(fr : Int)) (-D) 0).Off (k - -(fr : Int)) := by
  simp only [Region.Off, Region.callee]
  omega

/-- **The callee inside a plain call is one segment** at the caller's
frames `fs`: from the call node at `g`'s label (`csN`, the source exactly at
`let x = call g a in e`, reached locally from the ghost `c0`, `x30` the
return address `pcB + 4`) to the return address (`retCN`), or an abort
(`Ab`, inside the callee). The callee's label is inside `W` at a function
`dg` of the program (`hWC`); the callees' segments (`hcal`); the
continuation's free variables are bound (`hIt`) and its immediates the
table `i`'s (`hIc`), for `CalleeF`. -/
theorem calleeC_seg {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isaLSE2}
    {W : FragS isaLSE2} {Bl : Int64 → Label → Nat → Prop} {G0 : Ctl → Prop} {c0 : Ctl}
    (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    (hcal : CalleeSegs p lbl exe endPc R F W K ms cx Bl fp ra tp fs G0 i T D Ab)
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) {n : Nat}
    (hfresh : Fresh env n) {off : Int} (hoff : rsOf cx (regName "r" n) = some off)
    {pcB : Int64} {k : Nat} (hb : Bl pcB (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) e) :
    SegWS W K p lbl ms ((At exe endPc R F (csN lbl cx fp ra tp (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv env) (callP cx w (pcB + 4)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCN p lbl cx fp ra tp c0 fs (pcB + 4) e
          (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨ Ab s c fs') := by
  have h16' := frame_ge16 hf
  obtain ⟨-, dd, hfd, hretTy⟩ := hcl
  rw [hprog] at hfd
  -- the frame's cells are kept by the callee
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf cx r = some k' →
      R.Off k' ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (k' - -(cx.frame : Int)) := by
    intro r k' hk'
    unfold rsOf at hk'
    split at hk'
    · rename_i o ho
      cases hk'
      obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
      exact frame_outC hD0 hlo hhi (by omega) (by omega) (by omega)
    · cases hk'
  have houtA : R.Off (-16) ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (-16 - -(cx.frame : Int)) :=
    frame_outC hD0 hlo hhi (by decide) (by omega) (by omega)
  have houtB : R.Off (-8) ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (-8 - -(cx.frame : Int)) :=
    frame_outC hD0 hlo hhi (by decide) (by omega) (by omega)
  refine (call_ndSF (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := csN lbl cx fp ra tp (LocalRun p c0) ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv env) (callP cx w (pcB + 4)))
    (γ := CallG) (κ' := Ctl) (lo' := -D) (hi' := 0)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN p lbl tp fs q frm c0')
    (N := fun _ : Unit => retCN p lbl cx fp ra tp c0 fs (pcB + 4) e
      (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) off) (E := fun e : Empty => e.elim)
    (fs := fs) (Ab := Ab) hR hal hF
    (by show R.lo ≤ -(cx.frame : Int) + -D; omega) (by omega)
    (by show -(cx.frame : Int) < R.hi; omega) (Int.le_refl 0)
    (by show (-(cx.frame : Int)) % 16 = 0; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC g dd hfd _ rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    subst hR'eq
    refine (hcal g q frm F' hFS ?_ ?_ ?_ ?_).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, hcells m hm, mC, σC, c, _, _, hA, hkept, hct, hT, hj, hen, hfj, ?_⟩
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
      rw [hj.1] at ht1
      cases ht1
      subst hfr1
      have hne : ∀ y, y ≠ x →
          ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
        intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
      refine ⟨fun y hy hyx => ?_, fun y kk v hy hl => ?_⟩
      · have := hIt y hy
        rw [ofEnv_cons] at this
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
      · apply hIc y kk v
        rw [ofEnv_cons]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hy] using hl
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨c, x, a, e, hG c hJ.2.2.2.1, hT, hJ.1.1, hct⟩
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      obtain ⟨hj, hen, -, -, -, hP1, -⟩ := hJ
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, hev1, hcE1, -⟩ := hct
      rw [hj.1] at ht1
      cases ht1
      obtain ⟨ws', hev', hwr⟩ := hj.2.2.evalAt (fun _ => rfl) (sevalAt_ofEnv ha)
      rw [hev1] at hev'
      cases hev'
      match ws1, hwr, hev1, hcE1 with
      | [w'], ⟨⟨v, hv, hvr⟩, _⟩, hev1, hcE1 =>
        have hv' : v = q.v.toNat := by
          rw [hP1] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := EnvNum.evalAt hen (sevalAt_ofEnv ha) hev1 w' (by simp)
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      refine ⟨pcB, k, hb, ?_⟩
      rw [← hNe.2.2.1]
      exact hJ.2.2.2.2.2.2
    · rintro s c fs' (⟨rfl, c0', hrun, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩⟩ | hab)
      · exact .inl ⟨⟨c0', ⟨he, hn, hdc, hpc, σ, hA, hD, hrun, hJ⟩, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) (sevalAt_ofEnv ha)
    exact ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.X0.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, t, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP2⟩ := hJ
    obtain ⟨hrun, ⟨⟨a', t', w', hta, -, hev', ⟨nn, hnn⟩, hvr, -, -⟩, hlr⟩, htpx⟩ := hEx
    have hcE : cE = q.cE := hNe.1
    subst hcE
    have hct' := hct
    obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
    rw [hj.1] at ht1
    cases ht1
    rw [hfd] at hfd1
    cases hfd1
    subst hfr1
    have hstep : FrameStep p (c', ⟨x, e, c.env, [], dd.retTy⟩ :: fs)
        (⟨e, (x, dd.retTy, [w']) :: c.env, none⟩, fs) := .ret hta rfl hev'
    have hvr' : ValRep lbl w'.val σR.regs.X0.toBitVec.toNat := by rw [hregs]; exact hvr
    refine ⟨⟨e, (x, dd.retTy, [w']) :: c.env, none⟩, .single hstep, .inl ⟨(), ?_, ?_, ?_⟩⟩
    · show pcB + 4 = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [hP2, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(cx.frame : Int), []⟩ ⟨-(cx.frame : Int) + 0, []⟩ = true
      simp [SO.le]
    · refine ⟨⟨rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_⟩
      · show SRep lbl _ ((x, .int, [.one (.reg (regName "r" n))]) :: ofEnv env) ((x, dd.retTy, [w']) :: c.env)
        rw [hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x .int
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hk' hoff) hne
        exact hsl k' (hout r k' hk').1 (hout r k' hk').2
      · refine hen.cons fun w hw => ?_
        simp only [List.mem_singleton] at hw
        subst hw
        rw [hnn] at hvr'
        exact ⟨nn, hnn, hvr'.1⟩
      · exact ⟨(hsl _ houtA.1 houtA.2).trans hfj.1, (hsl _ houtB.1 houtB.2).trans hfj.2⟩
      · exact (FrameRun.ofLocal hr fs).trans (.step (hct.step fs)
          (hrun.trans ((FrameRun.ofLocal hlr _).trans (.single hstep))))
      · rw [hregs]; exact htpx
  · rintro s c fs' (⟨h, rfl⟩ | hab)
    · exact .inl (h.elim (fun ⟨_, h⟩ => ⟨h, rfl⟩) fun ⟨e, _⟩ => e.elim)
    · exact .inr hab

/-! ## The result's store -/

/-- **The result's store into `r%n`** from the return address (`retCN`):
`str x0, [sp, #o]` (`setReg_eq`), to a call node at `e` past it whose ghost
is a frame run from the call's `c0`. -/
theorem resC_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRun p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW W₀ K exe endPc R F n blk)
    {d : Scc.IR.Reg} {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) {off : Int}
    (hoff : rsOf cx d = some off) {pcR : Int64} (hc : Cd pcR (directives ls)) {e : Expr} {s : SEnv} :
    SegW W₀ K p lbl ms0 (At exe endPc R F (retCN p lbl cx fp ra tp c0 fs pcR e s off))
      (At exe endPc R F (csN lbl cx fp ra tp (fun c => FrameRun p (c0, fs) (c, fs))
        (pcR + Int64.ofNat (4 * (directives ls).length)) e s fun _ => True)) := by
  have hok := okBlk_resStore hf h1 h16 hs
  have hW := hWB ⟨pcR, oF cx, (retCN p lbl cx fp ra tp c0 fs pcR e s off).J⟩ _ (SubCd.whole hc) rfl
    (fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (.inr ⟨d, ls, hs, rfl⟩)
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  rw [setReg_eq hf (by omega) ho] at hs
  cases ok_inj hs
  have hoo : off = o - cx.frame := by
    simp only [rsOf, ho, Option.some.injEq] at hoff; exact hoff.symm
  subst hoo
  have hds : directives [ins (.STR (rz .W64 .X0) ⟨spW64, .imm ⟨i64 o, none⟩⟩)] =
      [spStr .X0 (Int64.ofInt o)] := rfl
  rw [hds] at hc hok hW ⊢
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hCd _ _ hc) hW (by simp) hok
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit _ (arun _ _ ⟨pcR, ⟨-(cx.frame : Int), []⟩, σ⟩) c
  rw [arun_spStr1, ofs_eq hf h1 ho]
  obtain ⟨hj, hn, hfj, hr, htp⟩ := hJ
  exact ⟨rfl, so_le_refl _ rfl, hj, hn, frJ_upd hfj (ofs_le hf ho) _, hr, htp, trivial⟩

/-! ## The plain call -/

/-- **The plain call** (`CallC`) at the frames `fs`, in the region `R` with
room `D` below the frame for the callee (`hlo`): the code predicates give
code (`hCd`, `hBl`); the call's straight blocks (`CallBlk`, `hWB`) and its
`bl` (`hWBl`) inside `W` at `fs` at every node of the frame's offsets whose
source controls are in `G0` (closed under the frame runs at `fs`, `hG0`)
with the saved pair, and so is the callee's label at the caller's offsets
for every function of the program (`hWC`); the terms in `T` call with no type
or index arguments (`hTc`); the callees' segments (`hcal`). -/
theorem callC_of {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) g k, Bl n.pc g k → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW (fun s c => W s c fs) K exe endPc R F n [blD g])
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isaLSE2}
    (hcal : CalleeSegs p lbl exe endPc R F W K ms cx Bl fp ra tp fs G0 i T D Ab) :
    CallC p lbl lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc kk env n x g is a ts e t w lw ls hc0 hT _ hcl ha hfresh hw hs hcw hb hcs hIt hIc
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRun.ofLocal h fs)
  have hGR : ∀ c, FrameRun p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(cx.frame : Int) := by omega
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf cx (regName "r" n) = some (o - cx.frame) := by simp [rsOf, ho]
  have sA := argC_seg (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv env) hf h1 h16 hF hR hal hlo0 hhi hCd hG hWB hw hcw
  have sB := blC_seg (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (tp := tp) (cx := cx)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv env) (Rn := LocalRun p c0)
    (P' := callP cx w (pc + Int64.ofNat (4 * (directives lw).length) + 4))
    hF hR hal hlo0 hhi hBl hG hWBl hb fun σ hp => by
      refine ⟨?_, ?_⟩
      · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X30 _).X0.toBitVec.toNat
        simpa [Reg64s.setXReg] using hp
      · simp [Reg64s.setXReg]
  have sW := SegWS.liftS (W := W) fs (sA.seq sB) (fun _ _ h => h)
  have sCal := calleeC_seg (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab)
    hf h16 hprog hF hR hal hD0 hD8 hlo hhi hG hWC hcal hT hcl ha hfresh hoff hb hIt hIc
  have sR := SegWS.liftS (W := W) fs (resC_seg (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (fp := fp)
    (ra := ra) (tp := tp) (e := e) (s := ofEnv ((x, .int, [.reg (regName "r" n)]) :: env))
    hf h1 h16 hF hR hal hlo0 hhi hCd hGR hWB hs hoff hcs) (fun _ _ h => h)
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, hen, hfj, hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨rfl, c, hr, he, hn, hdc, hpc, σ, hA, hD, ⟨⟨c, .refl c, hj, hen⟩, hfj, .refl c⟩, htp⟩
  · exact .inr hab

end Call

/-! ## The call premise -/

section Pre

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64} {W : FragS isaLSE2}
  {K : State → State → Prop}

/-- **A code block's call premise from its plain calls** (`CallPre` at a
context, `bodyC_segS` with `callC_of`): lowered without the depth counter
(`hfrm`) for the program `p` (`hprog`), at a return address with `RaOk`
(`hra`), the callee room `D` below the frame (`hlo`), the `bl`s' code
(`hBl`), the call's blocks and the callees' labels inside `W` at the frames
`fs` (`hWB`, `hWBl`, `hWC`, `callC_of`'s), the terms in `T` calling with no
type or index arguments (`hTc`). -/
theorem callPreC_of {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    (c : FnCode exe prog endPc RaOk Cd i T d) (hfrm : c.lcx.frames = none) (hprog : c.lcx.prog = p)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab : FragS isaLSE2} {D : Int} (hra : RaOk ra) (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(c.cx.frame : Int) - D)
    (hBl : ∀ pc g k, c.Bl ra pc g k → CdOf exe endPc pc [blD g])
    (hWB : ∀ (n : ND) blk, SubCd (Cd ra) n.pc blk → n.o = oF c.cx →
      (∀ σ c', n.J σ c' → G0 c' ∧ FrJ fp ra σ.slot) → CallBlk c.cx blk →
      BlkW (fun s c' => W s c' fs) K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) g k, c.Bl ra n.pc g k → n.o = oF c.cx →
      (∀ σ c', n.J σ c' → G0 c' ∧ FrJ fp ra σ.slot) → BlkW (fun s c' => W s c' fs) K exe endPc R F n [blD g])
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF c.cx →
      (∀ σ c', n.J σ c' → G0 c' ∧ FrJ fp ra σ.slot) → ∀ s c', At exe endPc R F n s c' → W s c' fs)
    (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = []) :
    CallPre W K p lbl ms c R F fs fp ra tp G0 Ab D := by
  intro hcal W₀ c0 hF hR hal hlo' hhi hW₀ hG0 hWb hWs hab hg0
  exact bodyC_segS c.hf c.h1 c.h16 hF hR hal hlo' hhi (c.hCd ra hra) hW₀ hG0 hWb hWs hab hfrm
    (callC_of c.hf c.h1 c.h16 hprog hF hR hal hD0 hD8 hlo hhi (c.hCd ra hra) hBl hG0 hWB hWBl hWC hTc hcal)
    _ _ _ _ _ _ _ _ c.hr c.hfr (c.hcode ra hra) (c.hbl ra hra) c.hImm c.hOne c0 hg0

end Pre

end Spike.Lib.LowerA64
