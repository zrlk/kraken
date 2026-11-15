/-
**The plain call of an `Accepted2` body with its blocks asked at placed
nodes** (AArch64): `callC2_ofFW : CallC2FW`
(`Spike/Lib/LowerA64/G1CallWStmt.lean`), `callC2_ofF`
(`Spike/Lib/LowerA64/CallC2.lean`) with the frame's fragment asked of the
call's blocks only at nodes whose controls the slot file places
(`SlotRepAt`) and, at no frames, are off a `ret`.

The call's nodes place their controls: the argument's load starts at
`bodyN2`, which carries `SlotRepAt`; the call site's node `csN2` (at `bl g`
and at the callee's entry) is at the call's `let` itself, placed by its
`NodeJE` and the walk's facts at the `let` (`SlotRepAt.of_nodeJE`: the
free variables bound, `htot_call`, the immediates and register bases from
the resumption facts' walk, `PtC2`); the landing node `retCN2` places the
continuation in the slot file with the result's slot at `x0`'s word (its
`NodeJE` and the continuation's facts).

- `htot_call`: the free variables at a plain call bound;
- `argC_seg2W`, `blC_seg2W`, `calleeC_seg2GW`, `resC_seg2W`: `argC_seg2`,
  `blC_seg2`, `calleeC_seg2G`, `resC_seg2` with the frame's fragment asked
  at their placed nodes;
- `callC2_ofFW`: the statement.
-/
import Spike.Lib.LowerA64.G1CallWStmt
import Spike.Lib.Src.LowerMarks2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv sevalAt lookupS WordPl SRep opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (CallerCells setXReg_TPIDR)
open Scc.Lower.Inv (regName labName atomV)
open Spike.Lib.LowerCall (Callee)

set_option linter.unusedSimpArgs false

/-- **The free variables at a plain call are bound** (`htot` at its
`let`): the argument's variable by `atomV`, the continuation's others than
`x` by its own (`hIt`). -/
theorem htot_call {env : Scc.Lower.Env} {x g : String} {a : At} {e : Expr} {n : Nat} {t : Ty}
    {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w]))
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome) :
    ∀ y ∈ Scc.Sem.exprFv (.let_ x (.call g [] a []) e), (lookupS (ofEnv2 env) y).isSome := by
  intro y hy
  simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.mem_append, List.mem_filter,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
  rcases hy with hy | ⟨hy, hne⟩
  · cases a with
    | var z =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      simp only [Scc.Lower.Inv.atomV, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      rw [lookupS_ofEnv2, hb]; rfl
    | lit _ => simp [Scc.Sem.atVars] at hy
    | unit => simp [Scc.Sem.atVars] at hy
  · have h := hIt y hy
    rw [lookupS_ofEnv2] at h ⊢
    have hne' : x ≠ y := fun h => by subst h; simp at hne
    simpa [List.find?_cons, hne'] using h

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The argument's load and `bl g` -/

/-- **The argument's load into `x0`** (`argC_seg2`) with the frame's
fragment asked at the load's node only as placed (`bodyN2`'s `SlotRepAt`)
and off a `ret` at no frames (the source runs locally to the call's term
`t`, `ht`). -/
theorem argC_seg2W {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {fs : List TermRun.Frame} {i : Expr → String → Nat → Option Nat}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk cx blk → BlkW W₀ K exe endPc R F n blk)
    {w : Scc.IR.Operand} {lw : List Item} (hw : cx.getOp .X0 w = .ok lw) {pc : Int64}
    (hc : Cd pc (directives lw)) {t : Expr} (ht : ∀ a, t ≠ .ret a) {s : SEnv}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp))
      (At exe endPc R F (csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        (pc + Int64.ofNat (4 * (directives lw).length)) t s
        fun σ => opdVal (rsOf cx) σ.slot w = some σ.regs.X0.toBitVec.toNat)) := by
  have hJ : ∀ σ c, ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp).J σ c →
      G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧ (fs = [] → ∀ a, c.term ≠ .ret a) := by
    rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, -⟩, hfj, hc0, hsr⟩, -⟩
    exact ⟨hG c hc0, hfj, hsr, fun _ => Spike.Lib.A64ConsumerS.noRet_of_run hr fun a h => by
      rw [hj.1] at h; exact ht a h⟩
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hCd _ _ hc)
    (hWB _ _ (SubCd.whole hc) rfl hJ (.inl ⟨w, lw, hw, rfl⟩))
    (getOp_ne_nil hf h1 hw) (okBlk_argLoad hf h1 h16 hw) ?_
  rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, hn, hb, hm, hS⟩, hfj, hc0, -⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨v, hv, hrr⟩ := arun_getOp hf h1 hw (_root_.Executable.labels exe).label pc σ
  show Hit _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  rw [hrr]
  refine ⟨rfl, so_le_refl _ rfl, hj, ⟨hn, hS, L, sm, B, hb, hm⟩, hfj, hc0.trans hr, ?_, ?_⟩
  · show (σ.regs.setXReg .X0 v).TPIDR_EL0 = tp
    rw [setXReg_TPIDR]; exact htp
  · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X0 v).X0.toBitVec.toNat
    simpa [Reg64s.setXReg] using hv

/-- **`bl g` is one segment** (`blC_seg2`) with the frame's fragment asked
at this `bl` (`hWBl`, at `g`, `k`) only at nodes placing their controls: its control at the call's term `t`
(`NodeJE`), placed by the walk's facts there (`htot`, `hlb`, `hic`), off a
`ret` (`ht`). -/
theorem blC_seg2W {cx : FnCtx} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2}
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {i : Expr → String → Nat → Option Nat}
    {Bl : Int64 → Label → Nat → Prop}
    (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 Q Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c) {g : Label} {k : Nat}
    (hWBl : ∀ (n : ND), Bl n.pc g k → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW W₀ K exe endPc R F n [blD g])
    {pc : Int64} (hb : Bl pc g k) {t : Expr} {s : SEnv}
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS s y).isSome) (hlb : LocBaseRegAt s t) (hic : ImmIn i s t)
    (ht : ∀ a, t ≠ .ret a) {P P' : AS → Prop}
    (hP : ∀ σ, P σ → P' { σ with regs := σ.regs.setXReg .X30 (pc + 4).toBitVec }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (csN2 lbl cx fp ra tp Q Rn pc t s P))
      (At exe endPc R F (csN2 lbl cx fp ra tp Q Rn ((_root_.Executable.labels exe).label g) t s P')) := by
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hBl _ _ _ hb)
    (hWBl _ hb rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1, SlotRepAt.of_nodeJE h.1 htot hlb hic,
      fun _ a ha => ht a (h.1.1 ▸ ha)⟩) (by simp) (okBlk_blD _ _ _ g)
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit (csN2 lbl cx fp ra tp Q Rn ((_root_.Executable.labels exe).label g) t s P')
    (arun (_root_.Executable.labels exe).label [blD g] ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c
  erw [blD_run]
  obtain ⟨hj, hq, hfj, hr, htp, hp⟩ := hJ
  refine ⟨rfl, so_le_refl _ rfl, hj, hq, hfj, hr, ?_, hP σ hp⟩
  show (σ.regs.setXReg .X30 _).TPIDR_EL0 = tp
  rw [setXReg_TPIDR]; exact htp

/-! ## The callee -/

/-- **The callee inside a plain call of an `Accepted2` body is one
segment** (`calleeC_seg2G`) with the frame's fragment asked at the
callee's entry only as placed: the call site's control at the call's `let`
(`NodeJE`), placed by the walk's facts there (`htot0`, `hlb0`, `hic0`). -/
theorem calleeC_seg2GW {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isaLSE2}
    {W : FragS isaLSE2} {Bl : Int64 → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c) {i : Expr → String → Nat → Option Nat}
    {T : Expr → Prop}
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf cx) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {Ab : FragS isaLSE2}
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf cx (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {k : Nat} (hb : Bl pcB (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (htot0 : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.call g [] a []) e), (lookupS (ofEnv2 env) y).isSome)
    (hlb0 : LocBaseRegAt (ofEnv2 env) (.let_ x (.call g [] a []) e))
    (hic0 : ImmIn i (ofEnv2 env) (.let_ x (.call g [] a []) e))
    (hcal : ∀ (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      q.ra = (pcB + 4).toBitVec →
      CallerAt2 p lbl lsize cx R D fp ra q frm F' c0 (.let_ x (.call g [] a []) e) env lits cs bufs →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab)) :
    SegWS W K p lbl ms ((At exe endPc R F (csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callP cx w (pcB + 4)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨
        Ab s c fs') := by
  have h16' := frame_ge16 hf
  have hcl0 := hcl
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] a []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
  have hsa := sevalAt_ofEnv2_one hg ha
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
    (nC := csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
      ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv2 env) (callP cx w (pcB + 4)))
    (γ := CallG) (κ' := Ctl) (lo' := -D) (hi' := 0)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN2 p lbl tp fs q frm c0')
    (N := fun _ : Unit => retCN2 p lbl cx fp ra tp c0 fs
      (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
        (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
      (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)
    (E := fun e : Empty => e.elim)
    (fs := fs) (Ab := Ab) hR hal hF
    (by show R.lo ≤ -(cx.frame : Int) + -D; omega) (by omega)
    (by show -(cx.frame : Int) < R.hi; omega) (Int.le_refl 0)
    (by show (-(cx.frame : Int)) % 16 = 0; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC g dd hfd hcl0 ⟨x, a, e, hT⟩ _ rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1, SlotRepAt.of_nodeJE h.1 htot0 hlb0 hic0,
      fun _ b hb => by rw [h.1.1] at hb; cases hb⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    subst hR'eq
    have hra : q.ra = (pcB + 4).toBitVec := by
      obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      rw [← hNe.2.2.1]
      exact hJ.2.2.2.2.2.2
    refine (hcal q frm F' hFS ?_ ?_ ?_ ?_ hra ?_).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, hcells m hm, mC, σC, c, _, _, hA, hkept, hct, hT, hj, ⟨lits, cs, bufs, hen⟩, hfj, ?_⟩
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
      rw [hj.1] at ht1
      cases ht1
      subst hfr1
      have hne : ∀ y, y ≠ x →
          ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
        intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
      refine ⟨fun y hy hyx => ?_, fun y hy hyx ty pls hl => ?_, fun y kk v hy hl => ?_⟩
      · have := hIt y hy
        rw [ofEnv2_cons hgr] at this
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
      · apply hlb y hy ty pls
        rw [ofEnv2_cons hgr]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using hl
      · apply hIc y kk v
        rw [ofEnv2_cons hgr]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hy] using hl
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨c, x, a, e, hG c hJ.2.2.2.1, hT, hJ.1.1, hct⟩
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      obtain ⟨hj, hen, -, -, -, hP1, -⟩ := hJ
      obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
      have hm1 := NJB.litMask_one (NJB.of_nodeJE (p := p) (B := B) hj hl hbB hmB hS) hsa hsc
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, hev1, hcE1, -⟩ := hct
      rw [hj.1] at ht1
      cases ht1
      obtain ⟨_, ws', hev', -, hwr⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
      rw [hev1] at hev'
      cases hev'
      match ws1, hwr, hev1, hcE1 with
      | [w'], ⟨⟨v, hv, hvr⟩, _⟩, hev1, hcE1 =>
        have hv' : v = q.v.toNat := by
          rw [hP1] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := NumL.one (hl.evalAt' hsc hlit hev1).2 hm1
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · exact ⟨pcB, k, hb, hra⟩
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, hr, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨mC, σC, c, hA, hkept, hct, hj, hen, hfj, hr⟩
    · rintro s c fs' (⟨rfl, c0', hrun, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩⟩ | hab)
      · exact .inl ⟨⟨c0', ⟨he, hn, hdc, hpc, σ, hA, hD, hrun, hJ⟩, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ta, ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
    exact ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.X0.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, ta, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP2⟩ := hJ
    obtain ⟨hrun, ⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, -, -⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
    have hcE : cE = q.cE := hNe.1
    subst hcE
    have hct' := hct
    obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
    rw [hj.1] at ht1
    cases ht1
    rw [hfd] at hfd1
    cases hfd1
    subst hfr1
    have hRL' : RetL .int c' := by rw [← hretTy]; exact hRL
    obtain ⟨a2, t2, w2, ht2, he2, hnum⟩ := RetL.int hRL'
    rw [hta] at ht2
    cases ht2
    rw [hev'] at he2
    simp only [Option.some.injEq, Prod.mk.injEq] at he2
    obtain ⟨rfl, rfl⟩ := he2
    have hstep : FrameStep p (c', ⟨x, e, c.env, [], dd.retTy⟩ :: fs)
        (⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, fs) := .ret hta rfl hev'
    have hvr' : ValRep lbl w2.val σR.regs.X0.toBitVec.toNat := by
      rw [hregs]; exact hvr 0 (by simp) (by decide)
    refine ⟨⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, .single hstep, .inl ⟨(), ?_, ?_, ?_⟩⟩
    · show pcB + 4 = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [hP2, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(cx.frame : Int), []⟩ ⟨-(cx.frame : Int) + 0, []⟩ = true
      simp [SO.le]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨rfl, rfl, ?_⟩
        show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
          ((x, dd.retTy, [w2]) :: c.env)
        rw [ofEnv2_cons hgr, hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv2 hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hk' hoff) hne
        exact hsl k' (hout r k' hk').1 (hout r k' hk').2
      · obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
        refine ⟨?_, EnvSmall.cons hS (WordsSmall.isNum hnum), L, sm, B, ?_, hmB⟩
        · show EnvLit _ ((x, dd.retTy, [w2]) :: c.env)
          rw [hop, hretTy]
          refine hl.cons rfl (NumL.of_all fun w hw => ?_)
          simp only [List.mem_singleton] at hw
          subst hw; exact hnum
        · show EnvB _ _ _ L sm lsize ((x, dd.retTy, [w2]) :: c.env)
          rw [hop]
          exact hbB.cons (SliceL.leaf none [w2]) (fun a h => by rcases h with h | h <;> cases h)
            (fun n τ h => by cases h)
      · exact ⟨(hsl _ houtA.1 houtA.2).trans hfj.1, (hsl _ houtB.1 houtB.2).trans hfj.2⟩
      · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
          (hrun.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
      · rw [hregs]; exact htpx
  · rintro s c fs' (⟨h, rfl⟩ | hab)
    · exact .inl (h.elim (fun ⟨_, h⟩ => ⟨h, rfl⟩) fun ⟨e, _⟩ => e.elim)
    · exact .inr hab

/-! ## The result's store -/

/-- **The result's store into `r%n`** (`resC_seg2`) with the frame's
fragment asked at the landing node only as placed: its control at the
continuation `e` (`NodeJE` in the slot file with the result's slot `off`
at `x0`'s word), placed by the continuation's facts (`htot`, `hlb`,
`hic`), off a `ret` at no frames (`hte`). -/
theorem resC_seg2W {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWR : ∀ (n : ND) blk (k0 : Int), SubCd Cd n.pc blk → n.o = oF cx → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt i lbl (rsOf cx) (Spike.Lib.upd σ.slot k0 σ.regs.X0.toBitVec) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk cx blk → BlkW W₀ K exe endPc R F n blk)
    {d : Scc.IR.Reg} {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) {off : Int}
    (hoff : rsOf cx d = some off) {pcR : Int64} (hc : Cd pcR (directives ls)) {e : Expr} {s : SEnv}
    (htot : ∀ y ∈ Scc.Sem.exprFv e, (lookupS s y).isSome) (hlb : LocBaseRegAt s e) (hic : ImmIn i s e)
    (hte : fs = [] → ∀ a, e ≠ .ret a) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off))
      (At exe endPc R F (csN2 lbl cx fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs))
        (pcR + Int64.ofNat (4 * (directives ls).length)) e s fun _ => True)) := by
  have hok := okBlk_resStore hf h1 h16 hs
  have hlen : (directives ls).length ≤ 1 := by
    obtain ⟨o, ho, -⟩ := bind_eq_ok hs
    rw [setReg_eq hf (by omega) ho] at hs
    cases ok_inj hs
    simp [directives, Scc.Emit.A64.ins]
  have hW := hWR ⟨pcR, oF cx, (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off).J⟩ _ off (SubCd.whole hc) rfl hlen
    (fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1, SlotRepAt.of_nodeJE h.1 htot hlb hic,
      fun hfs a ha => hte hfs a (h.1.1 ▸ ha)⟩) (.inr ⟨d, ls, hs, rfl⟩)
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
  obtain ⟨hj, hq, hfj, hr, htp⟩ := hJ
  exact ⟨rfl, so_le_refl _ rfl, hj, hq, frJ_upd hfj (ofs_le hf ho) _, hr, htp, trivial⟩

/-! ## The plain call -/

/-- **A plain call of an `Accepted2` body with its blocks asked at placed
nodes** (`CallC2FW`; `callC2_ofF` at `argC_seg2W`, `blC_seg2W`,
`calleeC_seg2GW`, `resC_seg2W`): the call's `let` placed by its walk's
facts (`htot_call`, the resumption facts' walk at its head, `PtC2`), the
continuation by `CallC2R`'s facts at it, off a `ret` at no frames by
the call's side condition. -/
theorem callC2_ofFW : CallC2FW := by
  intro p lbl lsize exe endPc R F K ms W cx hf h1 h16 lcx hprog hF hR hal D hD0 hD8 hlo hhi fp ra tp fs Cd Bl
    hCd hBl G0 hG0 i T hWB hWR hWBl hWC hTc Ab Lk hcal
  intro c0 pc pc' kk env n x g is a ts e t w lits cs bufs hte hc0 hT hfresh hlp hty hg hcnt hcl ha hcode hIt hIc hlb
    hpt
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT hcl
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRunM.ofLocal h fs)
  have hGR : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(cx.frame : Int) := by omega
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  -- the walk's facts at the call's `let`
  have htot0 := htot_call (g := g) ha hIt
  have hwk0 : ImmIn i (ofEnv2 env) (.let_ x (.call g [] a []) e) ∧
      LocBaseRegAt (ofEnv2 env) (.let_ x (.call g [] a []) e) := by
    obtain ⟨_, _, _, -, -, -, hwk, -⟩ := id hpt
    have := hwk _ (mem_lowerEnvs2_head lcx env n (.let_ x (.call g [] a []) e))
    exact ⟨this.1, this.2.2.2.2⟩
  obtain ⟨hic0, hlb0⟩ := hwk0
  have hnr : ∀ b, (.let_ x (.call g [] a []) e : Expr) ≠ .ret b := fun _ h => by cases h
  obtain ⟨lw, ls, hw, hs, hcw, hb, hcs, hp⟩ := instsC2_call hcode
  subst hp
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf cx (regName "r" n) = some (o - cx.frame) := by simp [rsOf, ho]
  -- `w`'s load into `x0`
  have sA := argC_seg2W (p := p) (lbl := lbl) (lsize := lsize) (K := K) (ms0 := ms fs) (tp := tp) (i := i)
    (fs := fs) (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs)
    hf h1 h16 hF hR hal hlo0 hhi hCd hG hWB hw hcw hnr
  -- `bl g`
  have sB := blC_seg2W (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (tp := tp) (cx := cx) (fs := fs)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (Q := fun c => EnvQ lits cs bufs lsize c.env)
    (Rn := LocalRun p c0)
    (P' := callP cx w (pc + Int64.ofNat (4 * (directives lw).length) + 4))
    hF hR hal hlo0 hhi hBl hG (fun n hb' hno hJ => hWBl n g _ hb' hcl ⟨x, a, e, hT⟩ hno hJ) hb htot0 hlb0
    hic0 hnr fun σ hp => by
      refine ⟨?_, ?_⟩
      · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X30 _).X0.toBitVec.toNat
        simpa [Reg64s.setXReg] using hp
      · simp [Reg64s.setXReg]
  have sW := SegWS.liftS (W := W) fs (sA.seq sB) (fun _ _ h => h)
  -- the callee
  have sCal := calleeC_seg2GW (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab) (lits := lits) (cs := cs) (bufs := bufs)
    hf h16 hprog hF hR hal hD0 hD8 hlo hhi hG hWC hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hlb
    htot0 hlb0 hic0
    fun q frm F' hFS hCF hex hav hbl hq hpin => hcal g q frm F' hFS hCF hex hav hbl
      ⟨c0, pc, _, kk, env, n, x, a, e, t, w, lits, cs, bufs, lw, hc0, hT, hfresh, hlp, hty, hg,
        hcnt, hcl, ha, hcode, hw, hq, hpt, hpin⟩
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (resC_seg2W (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (fp := fp)
    (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
    hf h1 h16 hF hR hal hlo0 hhi hCd hGR hWR hs hoff hcs hIt hlb hIc hte)
    (fun _ _ h => h)
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj, hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨rfl, c, hr, he, hn, hdc, hpc, σ, hA, hD,
      ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl c, SlotRepAt.of_nodeJE hj hIt hlb hIc⟩, htp⟩
  · exact .inr hab

end Call

/-- info: 'Spike.Lib.LowerA64.htot_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.htot_call

/-- info: 'Spike.Lib.LowerA64.argC_seg2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.argC_seg2W

/-- info: 'Spike.Lib.LowerA64.blC_seg2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blC_seg2W

/-- info: 'Spike.Lib.LowerA64.calleeC_seg2GW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.calleeC_seg2GW

/-- info: 'Spike.Lib.LowerA64.resC_seg2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resC_seg2W

/-- info: 'Spike.Lib.LowerA64.callC2_ofFW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2_ofFW

end Spike.Lib.LowerA64
