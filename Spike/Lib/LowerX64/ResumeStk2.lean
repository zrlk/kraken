/-
**The suspended frames resumed in turn** (x86-64; the twin of
`Spike/Lib/LowerA64/ResumeStk2.lean`, h1's resume walk at depth): a segment
to the running frame's exits at its key `k` continues, through each record
of its suspended frames (`StkOk … k st fs`), as one segment to the exits of
the frame right above the bottom frames (`Bot`): each record's caller
resumed after its callee's segment (`callC2_resume`, its premises from the
record: `StkFrOk.pin`, `StkFrOk.link`), its caller's context facts from its
`CxOk` (`ResumeCx2`).

- `StkFr.botKey`: the key of the frame right above the bottom frames (the
  last record's, or `k` with no records);
- `StkOk.bot_drop`: the bottom frames `fs.drop st.length` at that key
  (`Bot`);
- `ExitStk`: a frame's exits at a key, its ghost in the key's ghosts, at its
  block's return type (`ExitC2SL` in the key's rebased region `rbR k.R`);
- `ResumeCx2`: `callC2_resume`'s premises at a caller's context;
- `resume_stk`: the running frame's segment resumed through the records.

Where x86-64 differs from AArch64: a key's region `k.R` is its context's
entry region, the body's exits in the rebased `rbR k.R` (`callC2_resume`'s);
the context's region facts are the entry region's (`Rb.lo ≤ -8 - size`,
`8 ≤ Rb.hi`), and the `callq`s of the block are code (`hBl`).
-/
import Spike.Lib.LowerX64.Resume2
import Spike.Lib.LowerX64.RetSL

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.X64Consumer (noRetBlk)

/-- **The key right above the bottom frames**: the last record's key, or
the running frame's `k` with no records. -/
def StkFr.botKey (k : StkKey) : List StkFr → StkKey
  | [] => k
  | a :: st => StkFr.botKey a.key st

section ResumeStk

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {cells : List (Directive × Nat)} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **The bottom frames below the records**: `fs` past the records, at the
key right above them. -/
theorem StkOk.bot_drop : ∀ {k : StkKey} {st : List StkFr} {fs : List TermRun.Frame},
    StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot k st fs →
      Bot (StkFr.botKey k st) (fs.drop st.length)
  | _, [], _, h => stkOkB_nil.mp h
  | _, _ :: _, [], h => absurd h stkOkB_cons_nil
  | _, a :: st, _ :: fs, h => StkOk.bot_drop (k := a.key) (st := st) (fs := fs) (StkOk.uncons h).2

/-- **A frame's exits at a key** (`ExitC2SL` at the key's rebased region
`rbR k.R`, frame condition, saved pair and thread pointer, at the frames
`fs`): some ghost `c0` in the key's ghosts, at the return type `ty` of the
key's block in `P`, the aborts `Ab`. -/
def ExitStk (p P : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (k : StkKey) (fs : List TermRun.Frame) (Ab : FragS isa) : FragS isa := fun s c fs' =>
  ∃ c0 ty, k.G0 c0 ∧ (∃ d, P[k.j]? = some d ∧ d.retTy = ty) ∧
    ExitC2SL p lbl exe endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty Ab s c fs'

/-- **`callC2_resume`'s premises at a caller's context** (code facts `c`,
entry region `R`, frame condition `F`, frames `fs`, saved pair `fp`/`ra`,
thread pointer `tp`, ghosts `G0`, aborts `Ab`): the code's program, the
region's facts, the ghosts closed under frame runs, the block's `callq`s
code (`hBl`), and some fragment `W₀` inside `W` at `fs` with the body's
blocks in the rebased region `rbR R` (`hWB`, `hW`, `hWp`), the aborts and
the constructs' segments (`CallC2`, `LaneC`, `NewBufC`, `PrintCallC`). -/
def ResumeCx2 (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ms : List TermRun.Frame → MemSide isa)
    {Ti : Expr → Prop} {d : Decl} (c : FnCode2 exe cells endPc RaOk Cd i Ti d) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (fp ra : BitVec 64) (tp : UInt64) (G0 : Ctl → Prop)
    (Ab : FragS isa) : Prop :=
  c.lcx.prog = p ∧ FStable R F ∧ R.OK ∧ R.lo ≤ -8 - (c.fr.size : Int) ∧ 8 ≤ R.hi ∧
    (∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c') ∧
    (∀ pc zc g k, c.Bl ra pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)]) ∧
    ∃ W₀ : Frag isa, (∀ s c, W₀ s c → W s c fs) ∧
      (∀ (n : ND) blk, SubCd (Cd ra) n.pc blk → n.o = oB c.fr →
        okBlk (-(c.fr.size : Int)) 16 (oB c.fr) blk = true → noRetBlk blk = true →
        (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc (rbR R) F n blk) ∧
      (∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
        BlkW W₀ K exe endPc (rbR R) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk) ∧
      (∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
        BlkW W₀ K exe endPc (rbR R) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk) ∧
      (∀ c0, G0 c0 → ∀ s c',
        At exe endPc (rbR R) F (abortN2 i Ti p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
          Ab s c' fs) ∧
      (CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i Ti Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i Ti Ab ∧
        NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i Ti Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp fs G0 i Ti Ab)

variable [Kraken.Executable.ValidLayout exe] {W : FragS isa} {K : State → State → Prop}
  {ms : List TermRun.Frame → MemSide isa}

/-- **The running frame's segment resumed through its suspended frames**:
at records `st` of the frames `fs` at the running frame's key `k`
(`StkOk`), a segment from `Pre` to the running frame's exits (`ExitC2SL`
at `rbR k.R`, its ghost `c0` in `k.G0`, at its block's return type `ty`)
goes on to the exits of the frame right above the bottom frames (`ExitStk`
at `StkFr.botKey k st`, the frames `fs.drop st.length`). Each record's
caller resumes after its callee (`callC2_resume`): its premises from the
record (`StkFrOk.pin`; the callee's exits at the call's pair, thread
pointer and entry control by `StkFrOk.link`, at `int`), its context's from
its `CxOk` (`hres`). The aborts of every context are inside `Ab₀`
(`hAb`). -/
theorem resume_stk {Ab₀ : FragS isa}
    (hres : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
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
      hres a.j d hd _ _ _ _ _ _ _ _ hcx hra
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
    exact resume_stk hres hAb (st := st) (k := a.key) (fs := fs) hst hg0 ⟨d, hd, rfl⟩ hres2

end ResumeStk

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.StkOk.bot_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.StkOk.bot_drop

/-- info: 'Spike.Lib.LowerX64.resume_stk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.resume_stk
