/-
**A lowered `Accepted2` body is one segment, at any exit** (x86-64):
`Spike/Lib/LowerX64/Body2Seg.lean`'s induction (`body2_segS_of`) with the
body's exits a parameter `X` of the ghost and the walk's fact at a `ret` a
parameter `Rk`, and its instance at the exit by placements (`retNS`,
`Spike/Lib/LowerX64/RetS.lean`): a `ret` of any words the result type
places (a locative two operands), as the setup block returns.

- `emits_retN`: the items of a `ret` of up to six words;
- `RetCX`: a `ret` to the exits `X` (`RetC2` at `X`, `Rk`);
- `seg_contX`, `body2_segS_ofX`: `seg_cont` and `body2_segS_of` at `X`;
- `ExitC2S`, `ExitC2S.trans`: the body's exits at `retNS`;
- `retC2S_of`: a `ret`'s premise at `ExitC2S` from its edge (`ret_edgeS`),
  `a`'s words placed by its type (`GrpL`), any `Rk`;
- `body2_segS_ofS`: the body's segment to `ExitC2S`.
-/
import Spike.Lib.LowerX64.Body2Seg
import Spike.Lib.LowerX64.RetS
import Spike.Lib.Src.GroupPl

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item emitTerm loadArgs epilogue labelOf)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2 isPure pureOp markR lowerC2_add_inv lowerC2_sub_inv lowerC2_call_inv
  lowerC2_newBuf_inv lowerC2_xchg_inv lowerC2_pure_inv lowerC2_split_inv lowerC2_unpack_inv lowerC2_ifeq_inv
  lowerC2_ret_inv walk2_tail_add walk2_tail_sub walk2_tail_call walk2_tail_print walk2_tail_newBuf
  walk2_tail_xchg walk2_tail_pure walk2_tail_split walk2_tail_unpack walk2_tail_yes walk2_tail_no lowerC2_fv
  lowerC2_term_ne)
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (atomV regName labName)
open Spike.Lib.Form (SEnv lookupS)

/-- The epilogue and `ret`'s items. -/
theorem emits_retTail : Emits (do epilogue; Scc.Emit.X64.ins (Scc.Emit.X64.i64 .ret)) epiItems :=
  (emits_ins _).seq ((emits_ins _).seq (emits_ins _))

/-- **The items of a `ret` of up to six words**: the words' loads into the
result registers (`getOps` into `retRegs`), the epilogue, `ret`. -/
theorem emits_retN {fr : Scc.Emit.X64.Frame} {ws : List Scc.IR.Operand} {l : List Item}
    (h : Emits (emitTerm fr (.ret ws)) l) :
    ws.length ≤ Scc.Emit.X64.retRegs.length ∧
      ∃ lw, getOps fr (ws.zip Scc.Emit.X64.retRegs) = .ok lw ∧ dirs l = retDirs lw := by
  have h0 := h {}
  by_cases hgt : ws.length > Scc.Emit.X64.retRegs.length
  · simp only [emitTerm, loadArgs, hgt, ite_true] at h0
    cases h0
  have hle : ws.length ≤ Scc.Emit.X64.retRegs.length := by omega
  have hl : loadArgs fr Scc.Emit.X64.retRegs ws "ret" =
      (ldsLoop fr (ws.zip Scc.Emit.X64.retRegs) >>= fun _ => pure ()) := by
    simp only [loadArgs, hgt, ite_false]
  have he : emitTerm fr (.ret ws) =
      ((ldsLoop fr (ws.zip Scc.Emit.X64.retRegs) >>= fun _ => pure ()) >>= fun _ =>
        (do epilogue; Scc.Emit.X64.ins (Scc.Emit.X64.i64 .ret))) := by
    simp only [emitTerm, hl]
  rw [he] at h0
  obtain ⟨u, s1, h1, -⟩ := bind_inv h0
  obtain ⟨lw, hlw⟩ := ldsLoop_ok h1
  refine ⟨hle, lw, hlw, ?_⟩
  have h2 := ((ldsLoop_emits hlw).seq emits_retTail) {}
  rw [h0] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h2
  have ho := congrArg S.out h2
  simp only [List.append_cancel_right_eq, List.reverse_inj] at ho
  rw [ho, retDirs]

section Body2SegX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

/-! ## The induction at any exit -/

/-- **A `ret` to the exits `X`** (`RetC2` at any exit `X` of the ghost and any walk fact `Rk`
at the `ret`). -/
def RetCX (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (lcx : Scc.Lower.Ctx)
    (fr : Scc.Emit.X64.Frame)
    (Cd : Int64 → List (Directive × Nat) → Prop) (Bl : Int64 → Nat → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isa)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isa) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Rk : Expr × Scc.Lower.Env × Nat → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop)
    (X : Ctl → FragS isa) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (a : At) (t : Ty)
    (ws : List Scc.IR.Operand) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
    PtF lcx G0 i T c0 (.ret a) env n lits cs bufs → Rk (.ret a, env, n) →
    Lk (.ret a, lits) →
    atomV env a = some (t, ws) → CodeC2 fr Cd Bl kk pc [] (.ret ws) →
    SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc (.ret a) env lits cs bufs)
      (X c0)

/-- **A construct's segment, then its continuation's, at the exits `X`** (`seg_cont` at
any exit of the ghost closed under the frame runs at `fs`, `hXr`, and taking the aborts, `hAbX`). -/
theorem seg_contX {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {i : Expr → String → Nat → Option Nat} {G0 : Ctl → Prop}
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') {Ab : FragS isa} {X : Ctl → FragS isa}
    (hXr : ∀ c0 c0', FrameRunM p (c0, fs) (c0', fs) → ∀ s c fs', X c0' s c fs' → X c0 s c fs')
    (hAbX : ∀ c0 s c fs', Ab s c fs' → X c0 s c fs') {c0 : Ctl}
    (hG : G0 c0) {P : FragS isa} {pc' : Int64} {e : Expr} {env' : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hseg : SegWS W K p lbl ms P (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e env' lits cs bufs))
    (ih : ∀ c0', G0 c0' → SegWS W K p lbl ms
      (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0' fs pc' e env' lits cs bufs)
      (X c0')) :
    SegWS W K p lbl ms P (X c0) := by
  have ih' : ∀ g : {c0' // FrameRunM p (c0, fs) (c0', fs)},
      SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp g.1 fs pc' e env' lits cs bufs)
        (X c0) := fun g =>
    (ih g.1 (hG0 _ _ hG g.2)).mono_post (hXr _ _ g.2)
  refine (SegWS.seq_left (Q := fun s c fs' => fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0' pc' e (ofEnv2 env') lits cs bufs).withTp tp) s c) (E := Ab)
    hseg ((SegWS.exists_pre ih').mono_pre
      fun s c fs' ⟨he, c0', hrun, h⟩ => ⟨⟨c0', hrun⟩, h, he⟩)).mono_post fun s c fs' h => ?_
  rcases h with h | h
  · exact h
  · exact hAbX _ _ _ _ h

/-- **A lowered `Accepted2` body is one segment to the exits `X`** (`body2_segS_of` at any
exit `X` of the ghost, closed under the frame runs at `fs` (`hXr`) and taking the aborts
(`hAbX`); a `ret`'s premise `RetCX` at the walk's fact `Rk` there). -/
theorem body2_segS_ofX {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    {Rk : Expr × Scc.Lower.Env × Nat → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    {X : Ctl → FragS isa}
    (hXr : ∀ c0 c0', FrameRunM p (c0, fs) (c0', fs) → ∀ s c fs', X c0' s c fs' → X c0 s c fs')
    (hAbX : ∀ c0 s c fs', Ab s c fs' → X c0 s c fs')
    (hcall : CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk)
    (hlane : LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk)
    (hprint : PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hadd : AddC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hsub : SubC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hpure : PureMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T)
    (hsplit : SplitMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T)
    (hunpack : UnpackMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T)
    (hif : IfC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T)
    (hret : RetCX p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Rk Lk X) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2) (kk : Nat) (pc : Int64)
      (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 fr Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 fr Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ Rk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits e, LitPt q ∧ CallLk lcx.prog q ∧ Lk q) →
      Scc.Lower.countsB lcx.prog cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (X c0) := by
  -- the walk's facts at the head, and at a continuation from the walk's tail
  have hpt : ∀ {c0 : Ctl} {t : Expr} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res2}
      {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)},
      G0 c0 → lowerC2 lcx env n l k t = some r → Fresh env n →
      (∀ q ∈ lowerEnvs2 lcx env n t, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ Rk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits t, LitPt q ∧ CallLk lcx.prog q ∧ Lk q) →
      Scc.Lower.countsB lcx.prog cs bufs lits t = true → PtF lcx G0 i T c0 t env n lits cs bufs := by
    intro c0 t env n l k r lits cs bufs hG hr hfr hW hL hC
    have hh := walk2_head hW
    refine ⟨hG, hh.2.1, hfr, (hL _ ?_).1, hh.2.2.2.1, hh.2.2.2.2.1, hC, hh.1,
      fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx t env n l k r hr y hy)⟩
    cases t <;> simp [Scc.Lower.litWalk2]
  have hcf : ∀ {e : Expr} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res2},
      lowerC2 lcx env n l k e = some r →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ Rk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      ContF i e env n := by
    intro e env n l k r hr hW
    have hh := walk2_head hW
    exact ⟨fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx e env n l k r hr y hy), hh.1, hh.2.2.2.2.1,
      hh.2.2.2.1, hh.2.2.2.2.2⟩
  -- the literal walk and `countsB` past a `let`
  have hlitL : ∀ {lits : List (String × Scc.Lower.LitV)} {x : String} {op : Op} {e : Expr},
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits (.let_ x op e), LitPt q ∧ CallLk lcx.prog q ∧ Lk q) →
      ∀ q ∈ Scc.Lower.litWalk2 lcx.prog ((x, Scc.Lower.opLit lcx.prog lits op) :: lits) e,
        LitPt q ∧ CallLk lcx.prog q ∧ Lk q :=
    fun hL q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq)
  have hcntL : ∀ {cs bufs : List (String × Nat)} {lits : List (String × Scc.Lower.LitV)} {x : String} {op : Op}
      {e : Expr}, Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x op e) = true →
      Scc.Lower.countsB lcx.prog (Scc.Lower.csAfter x cs op) (Scc.Lower.bufsAfter x cs bufs op)
        ((x, Scc.Lower.opLit lcx.prog lits op) :: lits) e = true := by
    intro cs bufs lits x op e h
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at h
    exact h.2
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    by_cases hp : isPure op = true
    · obtain ⟨t, ws, sc, hq, r', hpo, hm, hr', rfl⟩ := lowerC2_pure_inv hp hr
      have hW' := walk2_tail_pure hp hpo hm hW
      exact (ih _ n l k r' kk pc _ _ _ hr' (hfr.pure hpo x) hcode hbl hW' (hlitL hL) (hcntL hC)
        (xchgsB_tail hX) c0 hG).mono_pre
        (hpure c0 pc env n x op e t ws sc hq lits cs bufs hp hP (pairSmall_head hX) hpo hm (hcf hr' hW'))
    cases op with
    | add a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC2_add_inv hr
      obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_add ha hb hW
      exact seg_contX hG0 hXr hAbX hG
        (hadd c0 pc pc' kk kk' env n x a b e ta tb pa pb lits cs bufs hP ha hb hi (hcf hr' hW'))
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' kk' pc' _ _ _ hr' (hfr.add x) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | sub a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC2_sub_inv hr
      obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_sub ha hb hW
      exact seg_contX hG0 hXr hAbX hG
        (hsub c0 pc pc' kk kk' env n x a b e ta tb pa pb lits cs bufs hP ha hb hi (hcf hr' hW'))
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' kk' pc' _ _ _ hr' (hfr.add x) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
          | ⟨xe, dg, t, b, o, m, cw, r', hx, hdg, hrt, ha, hr', rfl⟩
      · obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append r'.insts [_] kk pc).1 hcode
        have hW' := walk2_tail_call hfrm hx hdg hrt ha hW
        have hF := hcf hr' hW'
        exact seg_contX hG0 hXr hAbX hG
          (hcall c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs hG hP.2.1 hfr hP.2.2.2.1
            hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC ⟨hx, dg, hdg, hrt⟩ ha hi hF.1 hF.2.1 hF.2.2.2.2
            ⟨l, k, _, hr, hcode, hbl,
            fun q hq =>
              ⟨(hW q hq).1, (hW q hq).2.1, (hW q hq).2.2.2.1, (hW q hq).2.2.2.2.1, (hW q hq).2.2.2.2.2⟩, hL, hC, hX⟩)
          fun c0' hG' => ih _ (n + 1) l (k + 1) r' kk' pc' _ _ _ hr' (fresh_callC1 hfr x) hrest hbl hW' (hlitL hL)
            (hcntL hC) (xchgsB_tail hX) c0' hG'
      · obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append r'.insts _ kk pc).1 hcode
        have hW' := walk2_tail_print hx hdg hrt ha hW
        have hF := hcf hr' hW'
        exact seg_contX hG0 hXr hAbX hG
          (hprint c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs hG hP.2.1
            hfr hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC
            (by
              rw [← argShape_of_find hdg]
              exact (hL (.let_ x (.call g is a ts) e, lits) (by simp [Scc.Lower.litWalk2])).2.1 x g is a ts e rfl)
            hx hdg hrt ha hi hF.1 hF.2.1 hF.2.2.2.2)
          fun c0' hG' => ih _ (n + 4) l (k + 5) r' kk' pc' _ _ _ hr' (hfr.print x) hrest hbl hW' (hlitL hL)
            (hcntL hC) (xchgsB_tail hX) c0' hG'
    | newBuf cn τ =>
      obtain ⟨tk, kv, en, em, h, sc, hq, r', ha, hc, hh, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
      obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_newBuf ha hc hh hw hm hW
      have hF := hcf hr' hW'
      exact seg_contX hG0 hXr hAbX hG (hbuf c0 pc pc' kk kk' env n x cn τ e tk kv en em h lits cs bufs hG hP.2.1 hfr
          hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC ha hc hh hw hi hF.1 hF.2.1 hF.2.2.2.2
          ⟨l, k, _, hr, hcode, hbl,
            fun q hq =>
              ⟨(hW q hq).1, (hW q hq).2.1, (hW q hq).2.2.2.1, (hW q hq).2.2.2.2.1, (hW q hq).2.2.2.2.2⟩, hL, hC, hX⟩)
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' kk' pc' _ _ _ hr' (hfr.newBuf x τ) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | xchgAt b j v =>
      obtain ⟨t, bw, rb, o, tj, iv, μ, u, nu, mu, tv, w, s1, sc, hq, r', hb, hrf, hj, he, hg, hv, hs, hm, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append r'.insts [_, _] kk pc).1 hcode
      have hW' := walk2_tail_xchg hb hrf hj he hg hv hs hm hW
      have hF := hcf hr' hW'
      exact seg_contX hG0 hXr hAbX hG
        (hlane c0 pc pc' kk kk' env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs
          hG hP.2.1 hfr hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC (xchgB_of_ok hX) hb hrf hj he hg hv hs hi
          hF.1 hF.2.1 hF.2.2.2.2
          hP.2.2.2.2.2.2.2.2 hP.2.2.2.2.2.2.2.1 (walk2_head hW).2.2.2.2.2)
        fun c0' hG' => ih _ (n + 1) l (k + 2) r' kk' pc' _ _ _ hr' (hfr.xchg x u) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) c0' hG'
    | _ => first | exact absurd rfl hp | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨t, ws, u, w, nu, ha, hpr, hv, hr'⟩ := lowerC2_split_inv hr
    have hW' := walk2_tail_split ha hpr hv hW
    have hL' : ∀ q ∈ Scc.Lower.litWalk2 lcx.prog (match Scc.Lower.litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits) e, LitPt q ∧ CallLk lcx.prog q ∧ Lk q :=
      fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq)
    have hC' : Scc.Lower.countsB lcx.prog (Scc.Lower.unbuf y (Scc.Lower.unbuf x cs))
        (Scc.Lower.unbuf y (Scc.Lower.unbuf x bufs)) (match Scc.Lower.litAt lits a with
          | .node l r => (y, r) :: (x, l) :: lits
          | _ => (y, .leaf none) :: (x, .leaf none) :: lits) e = true := by
      simp only [Scc.Lower.countsB] at hC; exact hC
    exact (ih _ n l k r kk pc _ _ _ hr' (hfr.split ha x y u w nu) hcode hbl hW' hL' hC'
      (by simpa only [xchgsB] using hX) c0 hG).mono_pre
      (hsplit c0 pc env n a x y e t ws u w nu lits cs bufs hP ha hpr hv (hcf hr' hW'))
  | unpack a i' x e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨b, ws, ha, hr'⟩ := lowerC2_unpack_inv hr
    have hW' := walk2_tail_unpack ha hW
    have hL' : ∀ q ∈ Scc.Lower.litWalk2 lcx.prog ((x, Scc.Lower.litAt lits a) :: lits) e,
        LitPt q ∧ CallLk lcx.prog q ∧ Lk q :=
      fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq)
    have hC' : Scc.Lower.countsB lcx.prog (Scc.Lower.unbuf x (Scc.Lower.unbuf i' cs))
        (Scc.Lower.unbuf x (Scc.Lower.unbuf i' bufs)) ((x, Scc.Lower.litAt lits a) :: lits) e = true := by
      simp only [Scc.Lower.countsB] at hC; exact hC
    exact (ih _ n l k r kk pc _ _ _ hr' (hfr.unpack ha x) hcode hbl hW' hL' hC'
      (by simpa only [xchgsB] using hX) c0 hG).mono_pre
      (hunpack c0 pc env n a i' x e b ws lits cs bufs hP ha (hcf hr' hW'))
  | ifeq a b yes no ihy ihn =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨ta, pa, tb, pb, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have hmy : (⟨labName "then" n, ry.insts, ry.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    have hmn : (⟨labName "else" (n + 1), rn.insts, rn.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    obtain ⟨ky, hcy⟩ := hbl _ hmy (lowerC2_term_ne lcx _ _ _ _ _ _ hy)
    obtain ⟨kn, hcn⟩ := hbl _ hmn (lowerC2_term_ne lcx _ _ _ _ _ _ hn)
    have hnext := lowerC2_next_ge lcx yes env (n + 2) _ 0 ry hy
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
    simp only [xchgsB, Bool.and_eq_true] at hX
    have segy := ihy env (n + 2) _ 0 ry ky _ lits cs bufs hy (hfr.mono (by omega)) hcy
      (fun b hb => hbl b (by simp [hb])) (walk2_tail_yes ha hb hW)
      (fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)))
      hC.1 hX.1 c0 hG
    have segn := ihn env ry.next _ 0 rn kn _ lits cs bufs hn (hfr.mono (by omega)) hcn
      (fun b hb => hbl b (by simp [hb])) (walk2_tail_no hfrm ha hb hy hW)
      (fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq)))
      hC.2 hX.2 c0 hG
    exact (hif c0 pc kk env n a b yes no ta tb pa pb lits cs bufs hP ha hb hcode).seq (SegWS.or_pre segy segn)
  | ret a =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨t, ws, ha, rfl⟩ := lowerC2_ret_inv hr
    exact hret c0 pc kk env n a t ws lits cs bufs hP (walk2_head hW).2.2.1
      (hL _ (by simp [Scc.Lower.litWalk2])).2.2 ha hcode
  | _ => intro env n l k r kk pc lits cs bufs hr; simp [lowerC2] at hr

/-! ## The exits by placements -/

/-- **The body's exits at frames `fs`** for `ret`s by placements: `ExitC2`
at `retNS`. -/
def ExitC2S (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (Ab : FragS isa) : FragS isa := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧ At exe endPc R F ((retNS p lbl fp ra c0').withTp tp) s c) ∨
    Ab s c fs'

theorem ExitC2S.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame} {Ab : FragS isa}
    (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2S p lbl exe endPc R F fp ra tp c0' fs Ab s c fs' →
      ExitC2S p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

/-- **A `ret`'s premise at `ExitC2S`** from its edge (`ret_edgeS`): `a`'s
words placed by its type (the walk's `GrpL`), loaded into the result
registers; any walk fact `Rk`. -/
theorem retC2S_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isa} {Rk : Expr × Scc.Lower.Env × Nat → Prop}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    RetCX p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Rk Lk
      (fun c0 => ExitC2S p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  intro c0 pc kk env n a t ws lits cs bufs hP _ _ ha hcode
  obtain ⟨hG, -, -, -, -, hg, -, -, -⟩ := hP
  rcases hcode with hu | ⟨l1, zs, hE, hz, hc⟩
  · cases hu
  obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
  rw [hl] at hz hc
  obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hg ha
  have hk : Kind2 fr ((retDirs lw).zip zs) := by
    unfold Kind2
    rw [List.map_fst_zip (by omega)]
    exact .inr ⟨ws, lw, hn, hlw, rfl⟩
  have hret := SegW.of_next1E (((ret_edgeS (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (lits := lits)
    (cs := cs) (bufs := bufs) (i := i) hf h1 hlw hn hz (_root_.Executable.labels exe).label hsa hpl).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd _ _ hc)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ (SubCd.whole hc) hk) tp))
  exact (SegWS.liftS fs hret hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- **A lowered `Accepted2` body is one segment to its exits by
placements** (`body2_segS_ofX` at `ExitC2S`, the `ret`'s premise
`retC2S_of`): a `ret` of the words its type places, at most six. The
premises and the walk's facts as `body2_segS_of`'s (with `CallLk`), but no
`RetOk`. -/
theorem body2_segS_ofS {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isa}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    (hcall : CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hlane : LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hprint : PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hadd : AddC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hsub : SubC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hpure : PureMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T)
    (hsplit : SplitMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T)
    (hunpack : UnpackMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T)
    (hif : IfC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2) (kk : Nat) (pc : Int64)
      (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 fr Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 fr Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits e, LitPt q ∧ CallLk lcx.prog q) →
      Scc.Lower.countsB lcx.prog cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2S p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  intro e env n l k r kk pc lits cs bufs hr hfr hcode hbl hWk hL
  exact body2_segS_ofX (Rk := fun _ => True) (Lk := fun _ => True) hG0 hfrm (fun _ _ hr => ExitC2S.trans hr)
    (fun _ _ _ _ h => .inr h) hcall hlane hbuf hprint hadd hsub hpure hsplit hunpack hif
    (retC2S_of hf h1 hF hR hlo hhi hCd hW₀ hW lcx tp) e env n l k r kk pc lits cs bufs hr hfr hcode hbl
    (fun q hq => have h := hWk q hq; ⟨h.1, h.2.1, trivial, h.2.2⟩) (fun q hq => ⟨(hL q hq).1, (hL q hq).2, trivial⟩)

end Body2SegX

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.emits_retN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms emits_retN

/-- info: 'Spike.Lib.LowerX64.body2_segS_ofX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segS_ofX

/-- info: 'Spike.Lib.LowerX64.retC2S_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retC2S_of

/-- info: 'Spike.Lib.LowerX64.body2_segS_ofS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segS_ofS

end Spike.Lib.LowerX64
