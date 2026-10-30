/-
**The resumption restricted to a walk** (AArch64; plan b1): a context's
resumption premises with the constructs' facts asked only at the points of
the walk `T` that also satisfy `Tr` (`ResumeCx2T`), for the landing's
allocating frame, whose body resumes after the allocation at the points of
the allocation's continuation only. The suspended records keep the full
`ResumeCx2`, asked only of contexts whose walk has a plain call (the record
of a suspended caller is at a call).

- `ResumeCx2T`: `ResumeCx2` without the call blocks (`hWB`, unused at the
  landing) and with the aborts and constructs at `T ∧ Tr`;
- `bodyAtPt2WT`: `bodyAtPt2W` at `T ∧ Tr`, the point's walk inside `Tr`
  (`hTr`);
- `resume_stkT`: `resume_stk` with each record's `ResumeCx2` asked of a
  context with a plain call in its walk (`StkFrOk.pin`'s call term at the
  resumption point, `walk2_head`);
- `landStk_segT`: `landStk_seg` with the allocating frame's `ResumeCx2T`
  at `Tr j` (`hresL`; the continuation's walk inside `Tr j`, `hTr`,
  `lowerEnvs2_tail`) and the records' guarded `ResumeCx2` (`hresS`);
- `resumeCx2T_ofCxLB`: `ResumeCx2T` inside `W2` from `CxLB` at `T ∧ Tr`
  (`resumeCx2_ofCxLB`'s route); `resumeCx2T_ofCxLB_noCall` for a block
  without calls.
-/
import Spike.Lib.LowerA64.H1Of2
import Spike.Lib.LowerA64.ResumeCxLB

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (Lbl Lsize)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (newBufTy)
open Scc.Lower.Inv (regName)
open Spike.Lib.A64.Flow.NewBuf (allocAbortDepth)

section ResumeT

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat}

/-- **`ResumeCx2` at the walk's points in `Tr`**: the code's program, the
region's facts, the ghosts closed under frame runs, and some fragment `W₀`
inside `W` at `fs` with the body's blocks (`hW`, `hWp`), the aborts and
the constructs' segments at `fun t => Ti t ∧ Tr t`. No call blocks: the
landing resumes no call through this context. -/
def ResumeCx2T (W : FragS isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isaLSE2)
    {Ti : Expr → Prop} {d : Decl} (c : FnCode2 exe prog endPc RaOk Cd i Ti d) (R : Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop) (Ab : FragS isaLSE2)
    (Tr : Expr → Prop) : Prop :=
  c.lcx.prog = p ∧ FStable R F ∧ R.OK ∧ R.base.toNat % 16 = 0 ∧ 0 ≤ R.hi ∧
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') ∧
    ∃ W₀ : Frag isaLSE2, (∀ s c, W₀ s c → W s c fs) ∧
      (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
        BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk) ∧
      (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
        BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk) ∧
      (∀ c0, G0 c0 → ∀ s c',
        At exe endPc R F (abortN2 i (fun t => Ti t ∧ Tr t) p lbl c.cx (_root_.Executable.labels exe).label fp ra c0)
          s c' → Ab s c' fs) ∧
      (CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i (fun t => Ti t ∧ Tr t)
          Ab (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i (fun t => Ti t ∧ Tr t)
          Ab ∧
        NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i
          (fun t => Ti t ∧ Tr t) Ab (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i
          (fun t => Ti t ∧ Tr t) Ab)

variable {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {K : State → State → Prop}
  {T : Expr → Prop} {d : Decl}

/-- **The body's segment from a `BodyPtW` at the walk's points in `Tr`**
(`bodyAtPt2W` with the aborts and constructs at `fun t => T t ∧ Tr t`): the
point's lowering walk inside `Tr` (`hTr`). -/
theorem bodyAtPt2WT (c : FnCode2 exe prog endPc RaOk Cd i T d) {Tr : Expr → Prop} {R : Region}
    {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {Ab : FragS isaLSE2} {W₀ : Frag isaLSE2} {c0 : Ctl} (hra : RaOk ra)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(c.cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (hab : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F (abortN2 i (fun t => T t ∧ Tr t) p lbl c.cx (_root_.Executable.labels exe).label fp ra c0)
        s c' → Ab s c' fs)
    (hcon : CallC2 p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i (fun t => T t ∧ Tr t) Ab ∧
      NewBufC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.cx (Cd ra) (c.Bl ra) exe endPc R F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab)
    {pc : Int64} {t : Expr} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} (hpt : BodyPtW c ra pc t env n lits cs bufs) (hg0 : G0 c0)
    (hTr : ∀ q ∈ lowerEnvs2 c.lcx env n t, Tr q.1) :
    SegWS W K p lbl ms (LetAt p lbl lsize i c.cx exe endPc R F fp ra tp c0 fs pc t env lits cs bufs)
      (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs d.retTy Ab) := by
  obtain ⟨hcall, hlane, hbuf, hprint⟩ := hcon
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := hpt
  have hCd := c.hCd ra hra
  exact body2_segS_ofSL c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hG0 hW c.hfrm d.retTy hcall hlane hbuf hprint
    (addC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp hab c.lcx tp)
    (subC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW hWp c.lcx tp)
    (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
    (ifC2_of c.hf c.h1 c.h16 hF hR hal hlo hhi hCd hW₀ hW c.lcx tp)
    t env n l k r kk pc lits cs bufs hr hfr hcode hbl
    (fun q hq => have h := hWs q hq; ⟨h.1, ⟨h.2.1, hTr q hq⟩, h.2.2⟩)
    (fun q hq => ⟨(hLs q hq).1, (hLs q hq).2.1⟩) (fun a lits' hq => (hLs _ hq).2.2 a rfl)
    hC hX c0 hg0

end ResumeT

section StkT

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isaLSE2}

/-- **`resume_stk` with each record's `ResumeCx2` asked of a context
whose walk has a plain call** (`hres`'s last premise): a record's
resumption point is at its call term (`StkFrOk.pin`), a point of its
block's walk (`walk2_head`). -/
theorem resume_stkT {Ab₀ : FragS isaLSE2}
    (hres : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (∃ x g b e, T j (.let_ x (.call g [] b []) e)) →
      ResumeCx2 W K p lbl lsize ms (hcode j d hd) R F fs fp ra tp G0 Ab)
    (hAb : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → Ab₀ s c fs') :
    ∀ {st : List StkFr} {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {ty : Ty} {Pre : FragS isaLSE2},
      StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot k st fs → k.G0 c0 →
      (∃ d, P[k.j]? = some d ∧ d.retTy = ty) →
      SegWS W K p lbl ms Pre (ExitC2SL p lbl exe endPc k.R k.F k.fp k.ra k.tp c0 fs ty Ab₀) →
      SegWS W K p lbl ms Pre (ExitStk p P lbl exe endPc (StkFr.botKey k st) (fs.drop st.length) Ab₀)
  | [], k, fs, c0, ty, Pre, _, hc0, hty, hseg =>
    hseg.mono_post fun _ _ _ h => ⟨c0, ty, hc0, hty, h⟩
  | _ :: _, _, [], _, _, _, h, _, _, _ => absurd h stkOkB_cons_nil
  | a :: st, k, f :: fs, c0, ty, Pre, h, hc0, hty, hseg => by
    obtain ⟨ha, hst⟩ := StkOk.uncons h
    obtain ⟨hcx, hra⟩ := StkFrOk.cx ha
    have hg0 : a.G0 a.c0 := by obtain ⟨_, _, _, _, hg, -⟩ := ha; exact hg
    obtain ⟨d, hd, x, g, b, e, t, w, lw, ht, hb, hD0, hlo, hk, hcl, hat, hw, hq, hFF, hpin⟩ := StkFrOk.pin ha
    obtain ⟨hfp, hra', htp, hG0l, ⟨dg, hdg, hint⟩, hfty⟩ := StkFrOk.link ha
    obtain ⟨d', hd', hty'⟩ := hty
    rw [hdg] at hd'
    cases hd'
    subst hty'
    -- the callee's exits at the call's pair, thread pointer and entry control
    have hseg' : SegWS W K p lbl ms Pre (ExitC2B p lbl exe endPc
        (a.R.callee (-((hcode a.j d hd).cx.frame : Int)) (-a.D) 0) k.F a.q.fp a.q.ra a.tp a.q.cE (f :: fs) f.ty
        Ab₀) := by
      refine hseg.mono_post fun s c fs' h1 => ?_
      rw [hint] at h1
      have h2 := ExitC2B.trans (hG0l c0 hc0) s c fs' (ExitC2SL.toB_int h1)
      rw [← hk, ← hfp, ← hra', ← htp, hfty]
      exact h2
    rw [ht] at hb hpin
    -- the record's call term is a point of its block's walk
    have hTc : ∃ x g b e, T a.j (.let_ x (.call g [] b []) e) := by
      obtain ⟨-, -, -, -, -, -, -, -, hWs, -⟩ := hb
      exact ⟨x, g, b, e, (walk2_head hWs).2.1⟩
    obtain ⟨hprog, hF, hR, hal, hhi, hG0, W₀, hW₀, hWB, hW, hWp, hab, hcon⟩ :=
      hres a.j d hd _ _ _ _ _ _ _ _ hcx hra hTc
    have hres1 := callC2_resume (hcode a.j d hd) hprog hra hF hR hal hD0 hlo hhi hW₀ hG0 hWB hW hWp hab hcon hg0
      hb hcl hat hw hq hFF hpin hseg'
    -- the caller's exits, its aborts inside `Ab₀`
    have hres2 : SegWS W K p lbl ms Pre
        (ExitC2SL p lbl exe endPc a.key.R a.key.F a.key.fp a.key.ra a.key.tp a.c0 fs d.retTy Ab₀) :=
      hres1.mono_post fun s c fs' h1 => by
        rcases h1 with (⟨he, c1, hr1, hA⟩ | h1) | h1
        · exact .inl ⟨he, c1, hr1, hA⟩
        · exact .inr (hAb _ _ _ _ _ _ _ _ _ hcx s c fs' h1)
        · exact .inr h1
    exact resume_stkT hres hAb (st := st) (k := a.key) (fs := fs) hst hg0 ⟨d, hd, rfl⟩ hres2

end StkT

section LandT

variable {p : Prog} {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
    (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **A landing's segment with the allocating frame resumed at `Tr`**
(`landStk_seg` with `hres` split): the allocating frame's `ResumeCx2T` at
`Tr j` (`hresL`), the continuation's walk inside `Tr j` (`hTr`, by
`lowerEnvs2_tail`), its body by `bodyAtPt2WT`; the records' `ResumeCx2`
asked of contexts with a plain call (`hresS`, `resume_stkT`). -/
theorem landStk_segT {W : Lbl → Lsize → FragS isaLSE2} {K : State → State → Prop}
    {ms : Lbl → Lsize → List TermRun.Frame → MemSide isaLSE2} {Ab₀ Q : FragS isaLSE2}
    {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b w : Nat} (hl : L l = none) (hz : ls l = 0)
    {Tr : Nat → Expr → Prop}
    (hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hAW : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      R.lo ≤ -allocAbortDepth ((hcode j d hd).cx.frame : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).cx (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => W L ls s c fs) K exe endPc R F (ms L ls fs) fp ra tp G0 i (T j) (RetLk d.retTy))
    (hTr : ∀ j d, P[j]? = some d → ∀ x cn τ e t, T j (.let_ x (.newBuf cn τ) e) → TailOf t e → Tr j t)
    (hresL : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ResumeCx2T (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
        (AllocReach.updN ls l w) (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
        (hcode j d hd) R F fs fp ra tp G0 Ab (Tr j))
    (hresS : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (∃ x g b e, T j (.let_ x (.call g [] b []) e)) →
      ResumeCx2 (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
        (AllocReach.updN ls l w) (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
        (hcode j d hd) R F fs fp ra tp G0 Ab)
    (hAb : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → Ab₀ s c fs')
    (hbot : ∀ k fs, Bot k fs → SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
      (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
      (ExitStk p P (AllocReach.upd L l b) exe endPc k fs Ab₀) Q)
    (hAbQ : SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
      (ms (AllocReach.upd L l b) (AllocReach.updN ls l w)) Ab₀ Q) :
    SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
      (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
      (LandStk (p := p) hcode CxOk Bot ms L ls l b w) Q := by
  have hv := Spike.Lib.LowerNode.lvlLe_upd hl hz b w
  refine segWS_of_points fun s c fs hE => ?_
  obtain ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, pcB, x, cn, τ, e, env, n, lits, cs, bufs, h, kv, u, la, q,
    hcx, hra, hc0, hpt, hnb, hla, rfl, -, hF', hctx, hAt, htp⟩ := hE
  obtain ⟨hlo, hAWi⟩ := hAW j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  obtain ⟨-, hFs, hR, hal, hhi, hG0, W₀, hW₀, hW, hWp, hab, hcon⟩ :=
    hresL j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  obtain ⟨hfr, hT, tk', kv', en, em, hh, kk, pc', hat', hco', hhd', hptc, hi, hIt, hIc, hlb, hpt'⟩ :=
    BodyPtW.newBufP hpt
  obtain ⟨tk, en0, em0, hat, hco, hhd, rfl⟩ := hnb
  rw [hat] at hat'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Scc.IR.Operand.imm.injEq, and_true] at hat'
  obtain ⟨rfl, rfl⟩ := hat'
  rw [hco] at hco'
  cases hco'
  rw [hhd] at hhd'
  cases hhd'
  have he2 := hTn j d hd x cn τ e hT
  -- the count held: the call's element type is the allocation's
  have hkz : q.1.n ≤ AllocReach.updN ls l w l := by
    obtain ⟨-, -, -, -, σ, -, hFm, hJ⟩ := id hAt
    obtain ⟨-, -, -, -, -, -, -, -, -, us, hus, hw⟩ := hJ
    obtain ⟨mC, σC, c1, -, ⟨σ0, hJ1, -⟩, hN, -⟩ := hctx _ hFm
    obtain ⟨-, -, -, -, -, -, Lx, sm, B, hNJ, -⟩ := hJ1
    have ht : q.1.c0.term = .let_ x (.newBuf cn τ) e := hN.1 ▸ hNJ.1
    rw [q.2.term] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨-, ⟨-, hτ⟩, -⟩ := ht
    rw [hτ] at hus
    have := nWords_of_elem2 he2 hus
    simp only [AllocReach.updN, ite_true]
    rw [hw]
    exact Nat.le_mul_of_pos_right _ this
  have hl' : AllocReach.upd L l b l = some b := by simp [AllocReach.upd]
  have s1 := newBufC_tail (W := W (AllocReach.upd L l b) (AllocReach.updN ls l w)) (K := K)
    (ms := ms L ls) (w := w) (Ab := Ab) (hcode j d hd).hf (hcode j d hd).h1 (hcode j d hd).h16 hFs hR hal hlo hhi
    ((hcode j d hd).hCd ra hra)
    (W₀ := fun L ls s c => W L ls s c fs) (hTn j d hd) (hcode j d hd).lcx hAWi hc0 hT hfr hat hco hhd hptc hi hIt hIc
    hlb hla q.2 hF' hctx hv.1 hl' hv.2 hkz (fun _ _ h => h)
    (ms' := ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
  refine (s1.mono_pre fun s' c' fs' ⟨h1, h2, h3⟩ => ⟨h1 ▸ h2 ▸ ⟨hAt, htp⟩, h3⟩).seq (SegWS.or_pre ?_ ?_)
  · -- the body at the extended placement at `Tr j`, its frames resumed, the bottom's exits
    obtain ⟨-, st, hst⟩ := CxOkS.mono_lbl hv (fun _ _ _ _ _ _ _ _ _ h => h) hcx
    have hlo1 : R.lo ≤ -((hcode j d hd).cx.frame : Int) := by
      simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame] at hlo; omega
    refine (SegWS.exists_pre (P := fun c0' s' c' fs' => FrameRunM p (c0, fs) (c0', fs) ∧
      LetAt p (AllocReach.upd L l b) (AllocReach.updN ls l w) i (hcode j d hd).cx exe endPc R F fp ra tp c0' fs pc' e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit (hcode j d hd).lcx.prog lits (.newBuf cn τ)) :: lits)
        (Scc.Lower.csAfter x cs (.newBuf cn τ)) (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) s' c' fs')
      fun c0' => ?_).mono_pre fun s' c' fs' ⟨hfs, c0', hr, hA⟩ => ⟨c0', hr, hA, hfs⟩
    by_cases hr : FrameRunM p (c0, fs) (c0', fs)
    · have hg0 := hG0 _ _ hc0 hr
      have s2 := bodyAtPt2WT (hcode j d hd) hra hFs hR hal hlo1 hhi hW₀ hG0 hW hWp hab hcon hpt' hg0
        fun q hq => hTr j d hd x cn τ e q.1 hT (lowerEnvs2_tail e _ _ q hq)
      have s3 := resume_stkT (hcode := hcode) (Bot := Bot) hresS hAb (k := ⟨j, R, F, fp, ra, tp, G0⟩) hst hg0
        ⟨d, hd, rfl⟩ (s2.mono_post fun s c fs h => h.imp_right (hAb _ _ _ _ _ _ _ _ _ hcx.1 s c fs))
      exact (s3.seq (hbot _ _ (StkOk.bot_drop hst))).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hr h.1
  · exact hAbQ.mono_pre fun s c fs h => hAb _ _ _ _ _ _ _ _ _ hcx.1 s c fs h

end LandT

section FnT

open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.WriteAb (Ab)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {Jv : InvS} {Dt : State → Prop}
  {lbl : Lbl} {lsize : Lsize} {ms : List TermRun.Frame → MemSide isaLSE2}

/-- **A context's `ResumeCx2T` inside `W2` from `CxLB` at `T ∧ Tr`**
(`resumeCx2_ofCxLB`'s route at the walk `fun t => T t ∧ Tr t`): the region
facts and the ghosts' closure from `H`, the lane stores by `laneC_w2E`, the
buffers by `newBufC_of` (`H.hAW`, `H.hAb` at `T ∧ Tr`); the code's
program, the blocks, the aborts, the plain calls and prints given. -/
theorem resumeCx2T_ofCxLB (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk (fun ra => CdCLE prog okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    {Tr : Expr → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hra : RaOk ra)
    (hBl : ∀ pc g k, c.Bl ra pc g k → CdOf exe endPc pc [blD g])
    (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.cx
      (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms (fun t => T t ∧ Tr t) (RetLk d.retTy)
      R F fs fp ra tp G0 Ab')
    (hprog : c.lcx.prog = p)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk →
      Kind2 c.cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (bodyN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (pendN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F
        (abortN2 Λ.imms (fun t => T t ∧ Tr t) p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab' s c' fs)
    (hcall : CallC2 p lbl lsize c.lcx c.cx (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) exe endPc R F
      (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K ms fp ra tp fs G0 Λ.imms
      (fun t => T t ∧ Tr t) Ab' (RetLk d.retTy))
    (hpc : PrintCallC p lbl lsize c.lcx c.cx (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) exe endPc R F
      (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K ms fp ra tp fs G0 Λ.imms
      (fun t => T t ∧ Tr t) Ab') :
    ResumeCx2T (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms c
      R F fs fp ra tp G0 Ab' Tr := by
  refine ⟨hprog, H.hFS, H.hR, H.hal, H.hhi, H.hG0,
    fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs, fun _ _ h => h, hW, hWp, habN,
    hcall, ?_, ?_, hpc⟩
  · exact laneC_w2E hI hpr hab c.hf c.h1 c.h16 H.hR H.hal H.hloF H.hhi H.hl H.hh hsub hfit H.hFO H.hFS hp H.hrs
      H.hfp c.lcx tp (fun _ _ h => h) H.hrd H.hroom H.hrg H.hwn H.hHW H.hG0F
  · exact newBufC_of c.hf c.h1 c.h16 c.hp c.hend hA H.hFS H.hR H.hal H.hloA H.hhi (c.hCd ra hra) hBl
      (W₀ := fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (fun _ _ h => h) H.hK
      H.hG0 (fun x cn τ e h => hTn x cn τ e h.1) c.lcx H.hAW H.hAb

/-- **`resumeCx2T_ofCxLB` for a block without calls**: the walk `T` only
at points of the body (`hT`), none of them a call (`hnc`); the plain calls
by `callC2_of_noCallee`, the prints by `printCallC_of_noCall`, both at
`T ∧ Tr`. -/
theorem resumeCx2T_ofCxLB_noCall (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe prog endPc RaOk (fun ra => CdCLE prog okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    {Tr : Expr → Prop}
    (hT : ∀ t, T t → TailOf t d.body)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isaLSE2} (hra : RaOk ra)
    (hBl : ∀ pc g k, c.Bl ra pc g k → CdOf exe endPc pc [blD g])
    (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.cx
      (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms (fun t => T t ∧ Tr t) (RetLk d.retTy)
      R F fs fp ra tp G0 Ab')
    (hprog : c.lcx.prog = p)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk →
      Kind2 c.cx blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (bodyN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE prog okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind2 c.cx blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc R F
        (pendN2 p lbl lsize Λ.imms c.cx fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc R F
        (abortN2 Λ.imms (fun t => T t ∧ Tr t) p lbl c.cx (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab' s c' fs) :
    ResumeCx2T (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms c
      R F fs fp ra tp G0 Ab' Tr := by
  have hno : ∀ x g is a ts e, ¬ (T (.let_ x (.call g is a ts) e) ∧ Tr (.let_ x (.call g is a ts) e)) :=
    fun x g is a ts e hT' => noCall_of_tailsL hnc x g is a ts e (hT _ hT'.1)
  exact resumeCx2T_ofCxLB hI hpr hab hA hsub hfit hp c hTn hra hBl H hprog hW hWp habN
    (callC2_of_noCallee fun x g is a ts e hT' _ => hno x g is a ts e hT') (printCallC_of_noCall hno)

end FnT

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.bodyAtPt2WT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.bodyAtPt2WT

/-- info: 'Spike.Lib.LowerA64.resume_stkT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resume_stkT

/-- info: 'Spike.Lib.LowerA64.landStk_segT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.landStk_segT

/-- info: 'Spike.Lib.LowerA64.resumeCx2T_ofCxLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resumeCx2T_ofCxLB

/--
info: 'Spike.Lib.LowerA64.resumeCx2T_ofCxLB_noCall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resumeCx2T_ofCxLB_noCall
