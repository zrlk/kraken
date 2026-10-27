/-
**The landing's resumption on the walk past the landed allocation**
(x86-64): `ResumeCx2`, `resume_stk`, `landStk_seg` and `resumeCx2_ofCxLB`
(`Spike/Lib/LowerX64/ResumeStk2.lean`, `Spike/Lib/LowerX64/H1Of2.lean`,
`Spike/Lib/LowerX64/ResumeCxLB.lean`) with the allocating context's
constructs asked only at the points of the walk satisfying a restriction
`Tr` (the walk predicate `T` re-indexed to `T ∧ Tr`), and the suspended
records' contexts asked only at a call.

At a landing, the allocating frame's body resumes at the landed
allocation's continuation `e`; every point the body then reaches is a
`TailOf e` (`lowerEnvs2_tail`), so the constructs (`CallC2`, `LaneC`,
`NewBufC`, `PrintCallC`) and the abort node are needed only at `T ∧ Tr`
for any `Tr` holding at the tails of the landed continuations (`hTr`).
`ResumeCx2.hWB` (the calls' result blocks) is read only at a record's call
(`callC2_resume`); records are at a call's `let` (`StkFrOk.pin`), so the
records' contexts are asked `ResumeCx2` only under that guard.

- `ResumeCx2T`: `ResumeCx2` with the constructs and abort node at `T ∧ Tr`
  and without the call blocks' `hWB`;
- `bodyAtPt2WT`: `bodyAtPt2W` with its walk at `T ∧ Tr` (`hTr` along the
  walk from the resumption point);
- `resume_stkT`: `resume_stk` with the records' contexts' `ResumeCx2`
  asked only at a call of their block;
- `landStk_segT`: `landStk_seg` with the landing's context at
  `ResumeCx2T` (`hresL`), the records' at the guarded `ResumeCx2`
  (`hresS`), `Tr` closed under the landed continuations' tails (`hTr`);
- `resumeCx2T_ofCxLB`, `resumeCx2T_ofCxLB_noCall`: `ResumeCx2T` inside
  `W2` from `CxLB` at `T ∧ Tr`.
-/
import Spike.Lib.LowerX64.H1Of2
import Spike.Lib.LowerX64.ResumeCxLB
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.X64Consumer (noRetBlk)
open Spike.Lib.Form (lookupS)
open Scc.Lower.Inv (atomV regName)
open Spike.Lib.LowerShape (newBufCall newBufTy unitsOf countsO lowerC2)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.Flow.NewBuf (nbJc AllocCtx allocAbortDepth)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64 A9NoSpawn
open Spike.Lib.X64.WriteAb (Ab)

section ResumeT

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat}

/-- **`ResumeCx2` on the walk restricted by `Tr`** (code facts `c`, entry
region `R`, frame condition `F`, frames `fs`, saved pair `fp`/`ra`, thread
pointer `tp`, ghosts `G0`, aborts `Ab`): `ResumeCx2`'s facts, with the
abort node and the constructs' segments (`CallC2`, `LaneC`, `NewBufC`,
`PrintCallC`) at the walk predicate `Ti ∧ Tr`, and without the calls'
result blocks (`ResumeCx2`'s `hWB`, read only at a record's call). -/
def ResumeCx2T (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isa)
    {Ti : Expr → Prop} {d : Decl} (c : FnCode2 exe cells endPc RaOk Cd i Ti d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isa) (Tr : Expr → Prop) : Prop :=
  c.lcx.prog = p ∧ FStable R F ∧ R.OK ∧ R.lo ≤ -8 - (c.fr.size : Int) ∧ 8 ≤ R.hi ∧
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') ∧
    (∀ pc zc g k, c.Bl ra pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)]) ∧
    ∃ W₀ : Frag isa, (∀ s c, W₀ s c → W s c fs) ∧
      (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
        BlkW W₀ K exe endPc (rbR R) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk) ∧
      (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
        BlkW W₀ K exe endPc (rbR R) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk) ∧
      (∀ c0, G0 c0 → ∀ s c',
        At exe endPc (rbR R) F
          (abortN2 i (fun t => Ti t ∧ Tr t) p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
          Ab s c' fs) ∧
      (CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
          (fun t => Ti t ∧ Tr t) Ab (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
          (fun t => Ti t ∧ Tr t) Ab ∧
        NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
          (fun t => Ti t ∧ Tr t) Ab (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
          (fun t => Ti t ∧ Tr t) Ab)

variable [Kraken.Executable.ValidLayout exe] {W : FragS isa} {K : State → State → Prop}
  {ms : List TermRun.Frame → MemSide isa}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A compiled block's body segment on the walk restricted by `Tr`**
(`bodyAtPt2W` with the walk predicate `T ∧ Tr`): from a resumption point
`hpt` whose lowering walk's points all satisfy `Tr` (`hTr`), the
constructs and the abort node are needed at `T ∧ Tr` only. -/
theorem bodyAtPt2WT {T : Expr → Prop} {d : Decl} (c : FnCode2 exe cells endPc RaOk Cd i T d)
    {Tr : Expr → Prop} {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    {W₀ : Frag isa} {c0 : Ctl} (hra : RaOk ra)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 8 ≤ R.hi)
    (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
      BlkW W₀ K exe endPc (rbR R) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc (rbR R) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk)
    (hab : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F
        (abortN2 i (fun t => T t ∧ Tr t) p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs)
    (hcon : CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab ∧
      NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i
        (fun t => T t ∧ Tr t) Ab)
    {pc : Int64} {t : Expr} {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} (hpt : BodyPtW c ra pc t env n lits cs bufs) (hg0 : G0 c0)
    (hTr : ∀ q ∈ lowerEnvs2 c.lcx env n t, Tr q.1) :
    SegWS W K p lbl ms (LetAt p lbl lsize i c.fr exe endPc (rbR R) F fp ra tp c0 fs pc t env lits cs bufs)
      (ExitC2SL p lbl exe endPc (rbR R) F fp ra tp c0 fs d.retTy Ab) := by
  obtain ⟨hcall, hlane, hbuf, hprint⟩ := hcon
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := hpt
  obtain ⟨hF', hR', hlo', hhi'⟩ := rbR_facts hF hR hlo hhi
  have hCd := c.hCd ra hra
  exact body2_segS_ofSL c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hG0 hW c.hfrm d.retTy hcall hlane hbuf hprint
    (addC2_of c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hW hWp hab c.lcx tp)
    (subC2_of c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hW hWp c.lcx tp)
    (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
    (ifC2_of c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀ hW c.lcx tp)
    t env n l k r kk pc lits cs bufs hr hfr hcode hbl
    (fun q hq => ⟨(hWs q hq).1, ⟨(hWs q hq).2.1, hTr q hq⟩, (hWs q hq).2.2⟩)
    (fun q hq => ⟨(hLs q hq).1, (hLs q hq).2.1⟩) (fun a lits' hq => (hLs _ hq).2.2 a rfl)
    hC hX c0 hg0

section Stk

variable {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **`resume_stk` with the records' contexts asked at a call**: as
`resume_stk`, each record's context's `ResumeCx2` asked only when its
block's walk predicate holds at a call's `let` (`hres`'s last premise; the
record's own term, `StkFrOk.pin`, `walk2_head`). -/
theorem resume_stkT {Ab₀ : FragS isa}
    (hres : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (∃ x g b e, T j (.let_ x (.call g [] b []) e)) →
      ResumeCx2 W K p lbl lsize ms (hcode j d hd) R F fs fp ra tp G0 Ab)
    (hAb : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → Ab₀ s c fs') :
    ∀ {st : List StkFr} {k : StkKey} {fs : List TermRun.Frame} {c0 : Ctl} {ty : Ty} {Pre : FragS isa},
      StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot k st fs → k.G0 c0 →
      (∃ d, P[k.j]? = some d ∧ d.retTy = ty) →
      SegWS W K p lbl ms Pre (ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty Ab₀) →
      SegWS W K p lbl ms Pre (ExitStk p P lbl exe endPc (StkFr.botKey k st) (fs.drop st.length) Ab₀)
  | [], k, fs, c0, ty, Pre, _, hc0, hty, hseg =>
    hseg.mono_post fun _ _ _ h => ⟨c0, ty, hc0, hty, h⟩
  | _ :: _, _, [], _, _, _, h, _, _, _ => absurd h stkOkB_cons_nil
  | a :: st, k, f :: fs, c0, ty, Pre, h, hc0, hty, hseg => by
    obtain ⟨ha, hst⟩ := StkOk.uncons h
    obtain ⟨hcx, hra⟩ := StkFrOk.cx ha
    have hg0 : a.G0 a.c0 := by obtain ⟨_, _, _, _, hg, -⟩ := ha; exact hg
    obtain ⟨d, hd, x, g, b, e, t, w, lw, zs, zc, kk, ht, hb, hD0, hlo, hk, hcl, hat, hw, hz, hc1, hbl, hq, hFF,
      hpin⟩ := StkFrOk.pin ha
    obtain ⟨hfp, hra', htp, hG0l, ⟨dg, hdg, hint⟩, hfty⟩ := StkFrOk.link ha
    obtain ⟨d', hd', hty'⟩ := hty
    rw [hdg] at hd'
    cases hd'
    subst hty'
    -- the record's block's walk predicate at its call
    have hTc : ∃ x g b e, T a.j (.let_ x (.call g [] b []) e) := by
      obtain ⟨-, -, -, -, -, -, -, -, hWs, -, -, -⟩ := hb
      exact ⟨x, g, b, e, ht ▸ (walk2_head hWs).2.1⟩
    -- the callee's exits at the call's pair, thread pointer and entry control
    have hseg' : SegWS W K p lbl ms Pre (ExitC2B p lbl exe endPc
        (rbR (calleeR (rbR a.R) (hcode a.j d hd).fr.size a.D)) k.F a.q.fp a.q.ra a.tp a.q.cE (f :: fs) f.ty
        Ab₀) := by
      refine hseg.mono_post fun s c fs' h1 => ?_
      rw [hint] at h1
      have h2 := ExitC2B.trans (hG0l c0 hc0) s c fs' (ExitC2SL.toB_int h1)
      rw [← hk, ← hfp, ← hra', ← htp, hfty]
      exact h2
    obtain ⟨hprog, hF, hR, hlob, hhib, hG0, hBl, W₀, hW₀, hWB, hW, hWp, hab, hcon⟩ :=
      hres a.j d hd _ _ _ _ _ _ _ _ hcx hra hTc
    rw [ht] at hb hpin
    have hres1 := callC2_resume (hcode a.j d hd) hprog hra hF hR hlob hhib hD0 hlo hW₀ hG0 hBl hWB hW hWp hab
      hcon hg0 hb hcl hat hw hz hc1 hbl hq hFF hpin hseg'
    -- the caller's exits, its aborts inside `Ab₀`
    have hres2 : SegWS W K p lbl ms Pre
        (ExitC2SL p lbl exe endPc (rbR a.key.R) a.key.F a.key.fp a.key.ra a.key.tp a.c0 fs d.retTy Ab₀) :=
      hres1.mono_post fun s c fs' h1 => by
        rcases h1 with (⟨he, c1, hr1, hA⟩ | h1) | h1
        · exact .inl ⟨he, c1, hr1, hA⟩
        · exact .inr (hAb _ _ _ _ _ _ _ _ _ hcx s c fs' h1)
        · exact .inr h1
    exact resume_stkT hres hAb (st := st) (k := a.key) (fs := fs) hst hg0 ⟨d, hd, rfl⟩ hres2

end Stk

end ResumeT

section LandT

variable {p : Prog} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
    (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **A landing's segment on the walk past the landed allocation**
(`landStk_seg` at `ResumeCx2T`): as `landStk_seg`, the allocating frame's
body from the landed continuation `e` by `bodyAtPt2WT`, its walk's points
tails of `e` (`lowerEnvs2_tail`) so in `Tr j` (`hTr`), its context's
constructs at `T j ∧ Tr j` (`hresL`); the suspended frames by
`resume_stkT`, the records' contexts' `ResumeCx2` at a call (`hresS`). -/
theorem landStk_segT {Tr : Nat → Expr → Prop} {W : Lbl → Lsize → FragS isa} {K : State → State → Prop}
    {ms : Lbl → Lsize → List TermRun.Frame → MemSide isa} {Ab₀ Q : FragS isa}
    {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b w : Nat} (hl : L l = none) (hz : ls l = 0)
    (hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hAW : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (rbR R).lo ≤ -allocAbortDepth ((hcode j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).fr (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => W L ls s c fs) K exe endPc (rbR R) F (ms L ls fs) fp ra tp G0 i (T j) (RetLk d.retTy))
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
  obtain ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, pcB, x, cn, τ, e, env, n, lits, cs, bufs, h, kv, u, la,
    zs, zc, kk, q, hcx, hra, hc0, hpt, hnb, hla, hzs, hcla, hbl, hpcB, -, hF', hctx, hAt, htp⟩ := hE
  subst hpcB
  obtain ⟨hlo, hAWi⟩ := hAW j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  obtain ⟨-, hFs, hR, hlo8, hhi8, hG0, hBl, W₀, hW₀, hW, hWp, hab, hcon⟩ :=
    hresL j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  obtain ⟨hFr, hRr, -, hhir⟩ := rbR_facts hFs hR hlo8 hhi8
  obtain ⟨hfr, hT, tk', kv', en, em, hh, kk1, kk1', pc', hat', hco', hhd', hptc, hi, hIt, hIc, hlb, hpt'⟩ :=
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
  -- the landing's call is the allocation's: its loads, cell sizes and `callq`
  obtain ⟨lw, off, zs', zc', z, hlw, hoff, hz', hcla', hbl', hcls, -, hpc'⟩ := instsC2_newBuf hi
  rw [hla] at hlw
  cases hlw
  have hCd := (hcode j d hd).hCd ra hra
  have hzs' : zs = zs' := cdOf_zip_sizes s hAt.1 hAt.2.1 hzs hz' (hCd _ _ hcla) (hCd _ _ hcla')
  subst hzs'
  have hzc : [zc] = [zc'] :=
    cdOf_zip_sizes (ds := [_]) s hAt.1 hAt.2.1 rfl rfl (hBl _ _ _ _ hbl) (hBl _ _ _ _ hbl')
  cases hzc
  subst hpc'
  have hWls := (hAWi c0 pc kk1 x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hptc la off zs zc
    z kk hla hoff hzs hcla hbl hcls)
  -- the count held: the call's element type is the allocation's
  have hkz : q.1.n ≤ AllocReach.updN ls l w l := by
    obtain ⟨-, -, -, -, σ, -, hFm, hJ⟩ := id hAt
    obtain ⟨-, -, -, -, -, -, -, us, hus, hw⟩ := hJ
    obtain ⟨mC, σC, c1, -, ⟨σ0, hJ1, -⟩, hN, -⟩ := hctx _ hFm
    obtain ⟨-, -, -, -, -, -, -, Lx, sm, B, hNJ, -⟩ := hJ1
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
    (W₀ := fun s c => W (AllocReach.upd L l b) (AllocReach.updN ls l w) s c fs) (Ab := Ab) (w := w)
    (hcode j d hd).hf (hcode j d hd).h1 hFr hRr hlo hhir (fun _ _ h => h) (hcode j d hd).lcx.prog he2 hfr hoff
    (hCd _ _ hcls) (hWls _ _ hv.1 hv.2) hIt hIc hlb q.2 hF' hctx hv.1 hl' hv.2 hkz
    (ms' := ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
  refine (s1.mono_pre fun s' c' fs' ⟨h1, h2, h3⟩ => ⟨h1 ▸ h2 ▸ ⟨hAt, htp⟩, h3⟩).seq (SegWS.or_pre ?_ ?_)
  · -- the body at the extended placement, its frames resumed, the bottom's exits
    obtain ⟨-, st, hst⟩ := CxOkS.mono_lbl hv (fun _ _ _ _ _ _ _ _ _ h => h) hcx
    refine (SegWS.exists_pre (P := fun c0' s' c' fs' => FrameRunM p (c0, fs) (c0', fs) ∧
      LetAt p (AllocReach.upd L l b) (AllocReach.updN ls l w) i (hcode j d hd).fr exe endPc (rbR R) F fp ra tp
        c0' fs (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit (hcode j d hd).lcx.prog lits (.newBuf cn τ)) :: lits)
        (Scc.Lower.csAfter x cs (.newBuf cn τ)) (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) s' c' fs')
      fun c0' => ?_).mono_pre fun s' c' fs' ⟨hfs, c0', hr, hA⟩ => ⟨c0', hr, hA, hfs⟩
    by_cases hr : FrameRunM p (c0, fs) (c0', fs)
    · have hg0 := hG0 _ _ hc0 hr
      have s2 := bodyAtPt2WT (hcode j d hd) hra hFs hR hlo8 hhi8 hW₀ hG0 hW hWp hab hcon hpt' hg0
        fun q hq => hTr j d hd x cn τ e q.1 hT (lowerEnvs2_tail e _ _ q hq)
      have s3 := resume_stkT (hcode := hcode) (Bot := Bot) hresS hAb (k := ⟨j, R, F, fp, ra, tp, G0⟩) hst hg0
        ⟨d, hd, rfl⟩ (s2.mono_post fun s c fs h => h.imp_right (hAb _ _ _ _ _ _ _ _ _ hcx.1 s c fs))
      exact (s3.seq (hbot _ _ (StkOk.bot_drop hst))).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hr h.1
  · exact hAbQ.mono_pre fun s c fs h => hAb _ _ _ _ _ _ _ _ _ hcx.1 s c fs h

end LandT

section FnT

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Scc.Sem.Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {Jv : InvS} {Dt : State → Prop}
  {lbl : Lbl} {lsize : Lsize} {ms : List TermRun.Frame → MemSide isa}

/-- **A context's `ResumeCx2T` inside `W2` from `CxLB` at `T ∧ Tr`**
(`resumeCx2_ofCxLB` at the walk predicate `T ∧ Tr`): the lane stores by
`laneC_w2E`, the buffers by `newBufC_of` from `CxLB`'s `hAW`, `hAb` at
`T ∧ Tr`; the code's program (`hprog`), its calls in the code (`hBl`), the
blocks' `BlkW` at `W2` at the frames `fs` (`hW`, `hWp`), the aborts
(`habN`), the plain calls (`hcall`) and prints (`hpc`) at `T ∧ Tr` given. -/
theorem resumeCx2T_ofCxLB (hI : Spike.Lib.X64.Rt.InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk (fun ra => CdCLE cells okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    {Tr : Expr → Prop}
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hra : RaOk ra)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 8 ≤ R.hi)
    (hBl : ∀ pc zc g k, c.Bl ra pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.fr
      (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms (fun t => T t ∧ Tr t) (RetLk d.retTy) (rbR R)
      F fs fp ra tp G0 Ab')
    (hprog : c.lcx.prog = p)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) pc blk →
      Kind2 c.fr blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc (rbR R) F
        (bodyN2 p lbl lsize Λ.imms c.fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc (rbR R) F
        (pendN2 p lbl lsize Λ.imms c.fr fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F
        (abortN2 Λ.imms (fun t => T t ∧ Tr t) p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab' s c' fs)
    (hcall : CallC2 p lbl lsize c.lcx c.fr (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) exe endPc
      (rbR R) F (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K ms fp ra tp fs G0
      Λ.imms (fun t => T t ∧ Tr t) Ab' (RetLk d.retTy))
    (hpc : PrintCallC p lbl lsize c.lcx c.fr (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) exe endPc
      (rbR R) F (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K ms fp ra tp fs G0
      Λ.imms (fun t => T t ∧ Tr t) Ab') :
    ResumeCx2T (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms c
      R F fs fp ra tp G0 Ab' Tr := by
  refine ⟨hprog, hF, hR, hlo, hhi, H.hG0, hBl,
    fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs, fun _ _ h => h, hW, hWp, habN,
    hcall, ?_, ?_, hpc⟩
  · exact laneC_w2E hI hpr hab c.hf c.h1 H.hR H.hR8 H.hloF H.hhi H.hl H.hh hsub hfit H.hFO H.hFS hp H.hrs
      H.hfp (lcx := c.lcx) (tp := tp) (fun _ _ h => h) H.hrd H.hroom H.hrg H.hwn H.hHW H.hG0F
  · exact newBufC_of c.hf c.h1 c.hp c.hend hA H.hFS H.hR H.hloA H.hhi (c.hCd ra hra) hBl
      (W₀ := fun lbl lsize s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) (fun _ _ h => h) H.hK
      H.hG0 (fun x cn τ e hT => hTn x cn τ e hT.1) c.lcx H.hAW H.hAb

/-- **`resumeCx2T_ofCxLB` for a block without calls**: the walk predicate
`T` only at points of the body (`hT`), none of them a call (`hnc`); the
plain calls by `callC2_of_noCallee`, the prints by `printCallC_of_noCall`
(at `T ∧ Tr`). -/
theorem resumeCx2T_ofCxLB_noCall (hI : Spike.Lib.X64.Rt.InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hp : ProgNoS ZBad p)
    {RaOk : BitVec 64 → Prop} {T : Expr → Prop} {d : Decl}
    (c : FnCode2 exe cells endPc RaOk (fun ra => CdCLE cells okPc ph lab (Int64.ofBitVec ra)) Λ.imms T d)
    {Tr : Expr → Prop}
    (hT : ∀ t, T t → TailOf t d.body)
    (hnc : (tailsL d.body).all (fun t => !isCallLet t) = true)
    (hTn : ∀ x cn τ e, T (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hra : RaOk ra)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8 - (c.fr.size : Int)) (hhi : 8 ≤ R.hi)
    (hBl : ∀ pc zc g k, c.Bl ra pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    (H : CxLB Λ μ p rd G own rS Tk ar Jv Dt lab K exe endPc ms lbl lsize c.lcx c.fr
      (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) (c.Bl ra) Λ.imms (fun t => T t ∧ Tr t) (RetLk d.retTy) (rbR R)
      F fs fp ra tp G0 Ab')
    (hprog : c.lcx.prog = p)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) pc blk →
      Kind2 c.fr blk →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc (rbR R) F
        (bodyN2 p lbl lsize Λ.imms c.fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk,
      SubCd (CdCLE cells okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
      BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K exe endPc (rbR R) F
        (pendN2 p lbl lsize Λ.imms c.fr fp ra c0 pc t s lits cs bufs k) blk)
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR R) F
        (abortN2 Λ.imms (fun t => T t ∧ Tr t) p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab' s c' fs) :
    ResumeCx2T (fun s c fs => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs) K p lbl lsize ms c
      R F fs fp ra tp G0 Ab' Tr := by
  have hno : ∀ x g is a ts e, ¬ (T (.let_ x (.call g is a ts) e) ∧ Tr (.let_ x (.call g is a ts) e)) :=
    fun x g is a ts e hT' => noCall_of_tailsL hnc x g is a ts e (hT _ hT'.1)
  exact resumeCx2T_ofCxLB hI hpr hab hA hsub hfit hp c hTn hra hF hR hlo hhi hBl H hprog hW hWp habN
    (callC2_of_noCallee fun x g is a ts e hT' _ => hno x g is a ts e hT') (printCallC_of_noCall hno)

end FnT

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.bodyAtPt2WT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.bodyAtPt2WT

/-- info: 'Spike.Lib.LowerX64.resume_stkT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.resume_stkT

/-- info: 'Spike.Lib.LowerX64.landStk_segT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.landStk_segT

/-- info: 'Spike.Lib.LowerX64.resumeCx2T_ofCxLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.resumeCx2T_ofCxLB

/--
info: 'Spike.Lib.LowerX64.resumeCx2T_ofCxLB_noCall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.resumeCx2T_ofCxLB_noCall
