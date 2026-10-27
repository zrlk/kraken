/-
**A suspended caller resumed after its callee's return** (AArch64; h1's
resume walk): a callee's segment ending at its exits (`ExitC2B` at the
frames `f :: fs`) continues, through the source's return into the caller's
frame, as one segment to the caller's exits (`ExitC2SL` at `fs`). The
caller's state comes back from the callee's frame condition pinned at the
call site (`CallerAt2`); the machine leaves the callee's region (`at_leave`)
at the return address, where the source returns into the call's result
(`retCN2`); then the result's store (`resC_seg2`) and the caller's body from
the continuation (`BodyPtW.call`, `bodyAtPt2W`).

- `retCN2_of_exit`: the return taken at the callee's exit, the machine left
  in the caller's region at the return address (`retCN2`);
- `callC2_resume`: the caller resumed after the callee's segment.
-/
import Spike.Lib.LowerA64.Stk2
import Spike.Lib.LowerA64.Body2SegX

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal SEnv lookupS opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName atomV)
open Spike.Lib.LowerCall (Callee)
open Spike.Lib.LowerShape (lowerC2_fv)

section Resume2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The return at the callee's exit** (`calleeC_seg2`'s return, from the
pinned caller `CallerAt2`): at the callee's exit (`retNB` at the frame's
type, `sp` at the callee's region's base, at the return address `pcR`), the
source returns from the callee's `ret` into the caller's continuation `e`
with the result bound to `x`, and the machine, left in the caller's region
(`at_leave`), is at `retCN2` at `pcR`: the continuation placed by
`(x, int, [r%n]) :: env` with `x0` stored to `r%n`'s cell `off`, its facts
against the walk (`EnvQ`) at the call's, reached from the ghost `c0` by a
frame run at `fs`. -/
theorem retCN2_of_exit {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) {R : Region} {F : MachineData → Prop} {D : Int} (hD0 : 0 ≤ D)
    (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64}
    {fs : List TermRun.Frame} {c0 : Ctl} {x g : String} {b : At} {e : Expr} (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {n : Nat} (hfresh : Fresh env n) {off : Int}
    (hoff : rsOf cx (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {q : CallG} {pcR : Int64}
    (hq : q.ra = pcR.toBitVec) {f : TermRun.Frame} {F' : MachineData → Prop} (hFF : ∀ m, F' m → F m)
    (hpin : CallerAt2 p lbl lsize cx R D fp ra q f F' c0 (.let_ x (.call g [] b []) e) env lits cs bufs)
    {c0E : Ctl} (hrunE : FrameRunM p (q.cE, f :: fs) (c0E, f :: fs)) {s : State} {c : Ctl}
    (h : At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' ((retNB p lbl q.fp q.ra c0E f.ty).withTp tp) s c) :
    ∃ c', FrameRun p (c, f :: fs) (c', fs) ∧
      At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs
        (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] b [])) :: lits)
          (Scc.Lower.csAfter x cs (.call g [] b [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] b [])) lsize c.env)
        pcR e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off) s c' := by
  have h16' := frame_ge16 hf
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] b []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
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
  -- the machine left in the caller's region
  have hL := at_leave (kc := -(cx.frame : Int)) (lo' := -D) (hi' := 0)
    (P := fun σC => ∃ cC, CallTo p cC q.cE f ∧
      Spike.Lib.Form.NodeJE lbl (rsOf cx) (.let_ x (.call g [] b []) e) (ofEnv2 env) σC.slot cC ∧
      EnvQ lits cs bufs lsize cC.env ∧ FrJ fp ra σC.slot ∧ LocalRun p c0 cC) rfl
    (fun m hm => by
      obtain ⟨mC, σC, cC, hA, hK, hct, hj, hen, hfj, hr⟩ := hpin m hm
      exact ⟨hFF m hm, mC, σC, oF cx, hK, hA, cC, hct, hj, hen, hfj, hr⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC, hEx, ⟨cC, hct, hj, hen, hfj, hr⟩, rfl⟩ := hL
  obtain ⟨⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, -, -⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
  have hct' := hct
  obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
  rw [hj.1] at ht1
  cases ht1
  rw [hfd] at hfd1
  cases hfd1
  subst hfr1
  have hRL' : RetL .int c := by rw [← hretTy]; exact hRL
  obtain ⟨a2, t2, w2, ht2, he2, hnum⟩ := RetL.int hRL'
  rw [hta] at ht2
  cases ht2
  rw [hev'] at he2
  simp only [Option.some.injEq, Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl⟩ := he2
  have hstep : FrameStep p (c, ⟨x, e, cC.env, [], dd.retTy⟩ :: fs)
      (⟨e, (x, dd.retTy, [w2]) :: cC.env, none⟩, fs) := .ret hta rfl hev'
  have hvr' : ValRep lbl w2.val
      (leave (R.callee (-(cx.frame : Int)) (-D) 0) (-(cx.frame : Int)) σC σx).regs.X0.toBitVec.toNat :=
    hvr 0 (by simp) (by decide)
  have hsl : ∀ k, R.Off k → ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (k - -(cx.frame : Int)) →
      (leave (R.callee (-(cx.frame : Int)) (-D) 0) (-(cx.frame : Int)) σC σx).slot k = σC.slot k :=
    fun k _ hn => by simp only [leave]; exact ite_eq_right hn
  refine ⟨⟨e, (x, dd.retTy, [w2]) :: cC.env, none⟩, .single hstep, he, hn, hdc, ?_, _, hA, hD, ?_⟩
  · rw [hpc]
    show Int64.ofBitVec q.ra = pcR
    rw [hq, Int64.ofBitVec_toBitVec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, ?_⟩
    show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
      ((x, dd.retTy, [w2]) :: cC.env)
    rw [ofEnv2_cons hgr, hretTy]
    refine (hj.2.2.congr fun b' hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
      ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
    have hne := Fresh.ofEnv2 hfresh "r" b' hb pl hpl o ho r hr'
    rw [upd_apply]
    split
    · next hk => subst hk; exact absurd (rsOf_inj hk' hoff) hne
    exact hsl k' (hout r k' hk').1 (hout r k' hk').2
  · obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
    refine ⟨?_, EnvSmall.cons hS (WordsSmall.isNum hnum), L, sm, B, ?_, hmB⟩
    · show EnvLit _ ((x, dd.retTy, [w2]) :: cC.env)
      rw [hop, hretTy]
      refine hl.cons rfl (NumL.of_all fun w hw => ?_)
      simp only [List.mem_singleton] at hw
      subst hw; exact hnum
    · show EnvB _ _ _ L sm lsize ((x, dd.retTy, [w2]) :: cC.env)
      rw [hop]
      exact hbB.cons (SliceL.leaf none [w2]) (fun a h => by rcases h with h | h <;> cases h)
        (fun n τ h => by cases h)
  · exact ⟨(hsl _ houtA.1 houtA.2).trans hfj.1, (hsl _ houtB.1 houtB.2).trans hfj.2⟩
  · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
      (hrunE.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
  · exact htpx

/-- **A suspended caller resumed after its callee's segment**: a segment
from `P` to the callee's exits (`ExitC2B` at the frames `f :: fs`, the
callee's region below the caller's frame at room `D`, its frame condition
`F'` inside the caller's `F`, pinned at the call site: `CallerAt2`) goes on
to the caller's exits by placements (`ExitC2SL` at `fs`, the caller's
ghost `c0`), or ends in the callee's aborts `Ab'`. The call is `let x =
g(b)` at the resumption point `pc` of compiled block `c` (`BodyPtW`), `g` a
callee (`Callee`), `b`'s word `w` loaded into `x0` by `lw`, the return
address `q.ra` after the call's `bl`. The return (`retCN2_of_exit`), the
result's store (`resC_seg2`, its block by `hWB`), the caller's body from
the continuation (`BodyPtW.call`, `bodyAtPt2W` with its premises at the
caller's context). -/
theorem callC2_resume {prog : List Directive} {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List Directive → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    {d : Decl} (c : FnCode2 exe prog endPc RaOk Cd i T d) (hprog : c.lcx.prog = p) {R : Region}
    {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {Ab : FragS isaLSE2} {W₀ : Frag isaLSE2} (hra : RaOk ra) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) {D : Int} (hD0 : 0 ≤ D) (hlo : R.lo ≤ -(c.cx.frame : Int) - D)
    (hhi : 0 ≤ R.hi) (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd (Cd ra) n.pc blk → n.o = oF c.cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → CallBlk c.cx blk → BlkW W₀ K exe endPc R F n blk)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (hab : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 i T p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs)
    (hcon : CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    {c0 : Ctl} (hg0 : G0 c0) {pc : Int64} {x g : String} {b : At} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hpt : BodyPtW c ra pc (.let_ x (.call g [] b []) e) env n lits cs bufs) (hcl : Callee c.lcx g)
    {t : Ty} {w : Scc.IR.Operand} {lw : List Item} (ha : atomV env b = some (t, [w]))
    (hw : c.cx.getOp .X0 w = .ok lw) {q : CallG}
    (hq : q.ra = (pc + Int64.ofNat (4 * (directives lw).length) + 4).toBitVec)
    {f : TermRun.Frame} {F' : MachineData → Prop} (hFF : ∀ m, F' m → F m)
    (hpin : CallerAt2 p lbl lsize c.cx R D fp ra q f F' c0 (.let_ x (.call g [] b []) e) env lits cs bufs)
    {P Ab' : FragS isaLSE2}
    (hseg : SegWS W K p lbl ms P (ExitC2B p lbl exe endPc (R.callee (-(c.cx.frame : Int)) (-D) 0) F' q.fp q.ra tp
      q.cE (f :: fs) f.ty Ab')) :
    SegWS W K p lbl ms P (fun s c' fs' => ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab s c' fs' ∨
      Ab' s c' fs') := by
  have hf := c.hf
  have h1 := c.h1
  have h16 := c.h16
  have hCd := c.hCd ra hra
  have hlo0 : R.lo ≤ -(c.cx.frame : Int) := by omega
  -- the call's code and the continuation's resumption point
  have hpt0 := hpt
  obtain ⟨-, -, r, -, hr, hfresh, -, -, hWs, -, -, -⟩ := hpt0
  have hgrp := (walk2_head hWs).2.2.2.1
  obtain ⟨dg, t', w', kk, pc', -, -, ha', hi, hpt'⟩ := hpt.call hcl.1
  rw [ha] at ha'
  cases ha'
  obtain ⟨lw', ls, hw', hs, -, -, hcs, hp⟩ := instsC2_call hi
  rw [hw] at hw'
  cases hw'
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf c.cx (regName "r" n) = some (o - c.cx.frame) := by simp [rsOf, ho]
  have hpt'0 := hpt'
  obtain ⟨l', k', r', kk', hr', -, -, -, hWs', -, -, -⟩ := hpt'0
  have hh' := walk2_head hWs'
  -- the callee's exit to the return node
  have sE : SegWS W K p lbl ms P (fun s c' fs' =>
      (At exe endPc R F (retCN2 p lbl c.cx fp ra tp c0 fs
        (fun c1 => EnvQ ((x, Scc.Lower.opLit c.lcx.prog lits (.call g [] b [])) :: lits)
          (Scc.Lower.csAfter x cs (.call g [] b [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] b [])) lsize c1.env)
        (pc + Int64.ofNat (4 * (directives lw).length) + 4) e
        (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) (o - c.cx.frame))).at fs s c' fs' ∨
      Ab' s c' fs') := by
    refine SegWS.post_run (hseg.mono_post ?_)
    rintro s c' fs' (⟨rfl, c0E, hrunE, hA⟩ | hab')
    · obtain ⟨c'', hrun, hA'⟩ := retCN2_of_exit hf h16 hprog hD0 hlo hhi hcl hfresh hoff hq hFF hpin hrunE hA
      exact ⟨c'', fs, hrun, .inl ⟨hA', rfl⟩⟩
    · exact Pend.of (.inr hab')
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (resC_seg2 (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (fp := fp)
    (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c1 => EnvQ ((x, Scc.Lower.opLit c.lcx.prog lits (.call g [] b [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] b [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] b [])) lsize c1.env)
    hf h1 h16 hF hR hal hlo0 hhi hCd (fun c h => hG0 c0 c hg0 h) hWB hs hoff hcs) hW₀
  -- to the continuation's node
  have sC : SegWS W K p lbl ms P (ContC p lbl lsize i c.cx exe endPc R F fp ra tp c0 fs Ab' pc' e
      ((x, .int, [.reg (regName "r" n)]) :: env)
      ((x, Scc.Lower.opLit c.lcx.prog lits (.call g [] b [])) :: lits) (Scc.Lower.csAfter x cs (.call g [] b []))
      (Scc.Lower.bufsAfter x cs bufs (.call g [] b []))) := by
    refine (SegWS.seq_left sE sR).mono_post ?_
    subst hp
    rintro s c' fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj, hrr, htp, -⟩, rfl⟩ | hab')
    · exact .inl ⟨rfl, c', hrr, he, hn, hdc, hpc, σ, hA, hD,
        ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl c',
          SlotRepAt.of_nodeJE hj (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv c.lcx _ _ _ _ _ _ hr' y hy))
            hh'.2.2.2.2 hh'.1⟩, htp⟩
    · exact .inr hab'
  -- the caller's body from the continuation
  exact seg_contX (X := fun c0 s c' fs' => ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab s c' fs' ∨
      Ab' s c' fs') hG0
    (fun c0 c0' hr0 s c' fs' (h : _ ∨ _) => h.imp_left (ExitC2SL.trans hr0 s c' fs'))
    (fun _ _ _ _ h => Or.inr h) hg0 sC fun c0' hg0' =>
      (bodyAtPt2W c hra hF hR hal hlo0 hhi hW₀ hG0 hW hWp hab hcon hpt' hg0').mono_post fun _ _ _ h => Or.inl h

end Resume2

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.retCN2_of_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retCN2_of_exit
/-- info: 'Spike.Lib.LowerA64.callC2_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2_resume
