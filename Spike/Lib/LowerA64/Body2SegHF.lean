/-
**`main`'s return tail with the source held at a callee's `ret`**
(AArch64; the twin of `Spike/Lib/LowerX64/Body2SegHF.lean`, the noRet
walk's option A, the `HeldTail` shape): `main`'s last construct is a call
(or an output call) continuing with `ret b`, `b` a literal or the call's
result. The call's segment ends with the source held at the callee's `ret`
(`CallC2H`, `PrintCallCH`); `main`'s `ret b` block, its loads, the epilogue
and `ret`, then runs with the source still held, to the return's exit
`retNSL` at a held pair, which is `ExitC2SLF`'s
(`Spike/Lib/LowerA64/MainExitF.lean`).

- `heldRN`: a node at a held pair: the pair `HeldTail`, a frame run from it
  back to depth 0 reaching a control at the node `n`;
- `BlkEdge.heldRN`: a block's edge between nodes lifted to the held nodes
  (the held source takes no step);
- `seg_heldRN`: a one-exit block's edge at the held nodes is one segment at
  the held frames;
- `exitC2SLF_of_heldRN`: the return's exit at a held pair is `ExitC2SLF`;
- `blkW_heldS`: `HeldS` on a block from its four parts;
- `retHeld_seg`: `main`'s `ret b` block at the held node of its `bodyN2` is
  one segment at the held frames to `ExitC2SLF` (`ret_edgeSL` lifted);
- `heldRetOk_let`, …: `heldRetOk` past each construct;
- `HeldTailCX`, `body2_segS_ofXH`: a body whose paths all end in a held
  return tail is one segment to the exits `X` (`body2_segS_ofX` under
  `heldRetOk`, the tail by `HeldTailCX`);
- `held_segX`: from the held pairs (`HeldC`) to `ExitC2SLF`, from a segment
  at each held node.
-/
import Spike.Lib.LowerA64.MainExitF
import Spike.Lib.LowerA64.HeldTail
import Spike.Lib.LowerA64.HeldC
import Spike.Lib.LowerA64.Body2SegX

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode

/-- **A node at a held pair** of `main`'s return tail: the pair `HeldTail`
at the frames `fs`, a frame run from it back to depth 0 reaching a control
at `n`'s invariant. -/
def heldRN (p : Prog) (fs : List TermRun.Frame) (n : ND) : ND :=
  ⟨n.pc, n.o, fun σ c => HeldTail c fs ∧ ∃ cR, FrameRun p (c, fs) (cR, []) ∧ n.J σ cR⟩

section HeldRN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A block's edge lifted to the held nodes**: the held source takes no
step; the run the edge takes at depth 0 extends the held pair's run. -/
theorem BlkEdge.heldRN {lab : Label → Int64} {lo hi : Int} {n : ND} {blk : List Directive}
    {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (h : BlkEdge p lab lo hi n blk N E) (fs : List TermRun.Frame) :
    BlkEdge p lab lo hi (heldRN p fs n) blk (fun j => heldRN p fs (N j)) (fun x => heldRN p fs (E x)) := by
  refine ⟨h.1, h.2.1, fun σ c ⟨hH, cR, hr, hJ⟩ => ?_⟩
  obtain ⟨c', hr', hL⟩ := h.2.2 σ cR hJ
  have hrr : FrameRun p (c, fs) (c', []) := hr.trans (FrameRun.ofLocal hr' [])
  refine ⟨c, .refl c, ?_⟩
  rcases hL with ⟨j, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩
  · exact .inl ⟨j, h1, h2, hH, c', hrr, h3⟩
  · exact .inr ⟨x, h1, h2, hH, c', hrr, h3⟩

/-- **A one-exit block's edge at the held nodes is one segment** at the
held frames `fs` (`BlkEdge.seg` at `heldRN`, lifted by `SegWS.liftS`). -/
theorem seg_heldRN {lo hi : Int} {n m : ND} {blk : List Directive} {E : Empty → ND}
    (h : BlkEdge p (_root_.Executable.labels exe).label lo hi n blk (fun _ : Unit => m) E)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (fs : List TermRun.Frame) {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hW : BlkW W₀ K exe endPc R F (heldRN p fs n) blk) :
    SegWS W K p lbl ms ((At exe endPc R F (heldRN p fs n)).at fs) ((At exe endPc R F (heldRN p fs m)).at fs) :=
  SegWS.liftS fs (((h.heldRN fs).seg hF hR hal hlo hhi hcode hW).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) hW₀

/-- **The return's exit at a held pair is `ExitC2SLF`**: the frame run in
`heldRN`'s invariant reaches the return's control at depth 0. -/
theorem exitC2SLF_of_heldRN {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {ty : Ty} {Ab : FragS isaLSE2}
    {fs : List TermRun.Frame} (hr : FrameRunM p (c0, []) (c0', [])) {s : State} {c : Ctl}
    (h : At exe endPc R F (heldRN p fs ((retNSL p lbl fp ra c0' ty).withTp tp)) s c) :
    ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab s c fs := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hF, -, cR, hrR, hJ⟩ := h
  exact .inl ⟨cR, hrR, c0', hr, he, hn, hdc, hpc, σ, hA, hF, hJ⟩

/-- **`HeldS` on a block from its parts**: the abort phase's facts, `Ret0`,
no write, and no system call (so no output `write`). -/
theorem blkW_heldS {μ : Scc.Sem.Marks} {Ab : State → Prop} {lbl : Spike.Lib.A64Consumer.Lbl} {n : ND}
    {blk : List Directive}
    (hab : BlkW (fun s _ => Spike.Lib.A64ConsumerA.AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk)
    (hr : BlkW (Ret0 lbl) (fun _ _ => False) exe endPc R F n blk)
    (hw : BlkW (fun s _ => ∀ L, ¬ Spike.Lib.A64ConsumerA.WrAt s L) (fun _ _ => False) exe endPc R F n blk)
    (hs : BlkW (fun s _ => Scc.Sem.A64.abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (HeldS μ Ab lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hF hJ k hk m hA' hD
  have hs' := (hs s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1
  exact ⟨⟨(hab s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1, (hr s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1,
    (hw s σ c he hn hd hpc hA hF hJ k hk m hA' hD).1, fun h => absurd (hs'.symm.trans h) (by decide)⟩,
    fun _ h => h⟩

variable {lsize : WeakMem.AllocLabel → Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`main`'s `ret b` block at a held pair is one segment to `ExitC2SLF`**:
`ret_edgeSL`'s edge with the thread pointer, lifted to the held nodes
(`BlkEdge.heldRN`), one segment at the held frames (`seg_heldRN`), its
exit `ExitC2SLF` past the ghost's run `hr` (`exitC2SLF_of_heldRN`); the
block's states inside `W` at the held node (`hW`). -/
theorem retHeld_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} {fp ra : BitVec 64} {a : At} {s : Spike.Lib.Form.SEnv}
    {t : Ty} {pls : List WordPl} (hsa : Spike.Lib.Form.sevalAt s a = some (t, pls)) (hg : group t vs = some pls)
    {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a) (hlit : ∀ n, a = .lit n → n < 2 ^ 64)
    (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    (hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st pc (directives (ls ++ cx.leave ++ [ret])))
    {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', [])) (fs : List TermRun.Frame)
    {W₀ : Frag isaLSE2} (hW₀ : ∀ st c, W₀ st c → W st c fs)
    (hW : BlkW W₀ K exe endPc R F
      (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0' pc (.ret a) s lits cs bufs).withTp tp))
      (directives (ls ++ cx.leave ++ [ret]))) {Ab : FragS isaLSE2} :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0' pc (.ret a) s lits cs bufs).withTp tp))).at
        fs)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have he := (ret_edgeSL (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0') (pc := pc)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 h16 hl hn (_root_.Executable.labels exe).label
    hsa hg hsc hlit hera).tp tp
  exact (seg_heldRN he hF hR hal hlo hhi hcode fs hW₀ hW).mono_post
    fun _ _ _ ⟨h, hfs⟩ => hfs ▸ exitC2SLF_of_heldRN hr h

end HeldRN

/-! ## The walk to a held return tail -/

open Spike.Lib.LowerShape (lowerC2 Res2 isPure pureOp lowerC2_add_inv lowerC2_sub_inv lowerC2_call_inv
  lowerC2_newBuf_inv lowerC2_xchg_inv lowerC2_pure_inv lowerC2_split_inv lowerC2_unpack_inv lowerC2_ifeq_inv
  lowerC2_ret_inv walk2_tail_add walk2_tail_sub walk2_tail_call walk2_tail_print walk2_tail_newBuf
  walk2_tail_xchg walk2_tail_pure walk2_tail_split walk2_tail_unpack walk2_tail_yes walk2_tail_no lowerC2_fv
  lowerC2_term_ne)
open Spike.Lib.LowerCall (Callee)
open Scc.Lower.Inv (atomV regName labName)
open Spike.Lib.Form (SEnv lookupS)

section HeldWalk

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **`heldRetOk` past a `let`**: the continuation's, or the `let` is the
held tail, a call continuing with `ret b`, `b` a literal or its result. -/
theorem heldRetOk_let {x : String} {op : Op} {e : Expr} (h : Scc.Lower.heldRetOk (.let_ x op e) = true) :
    Scc.Lower.heldRetOk e = true ∨
      ∃ g is a ts b, op = .call g is a ts ∧ e = .ret b ∧ ((∃ k, b = .lit k) ∨ b = .var x) := by
  rw [Scc.Lower.heldRetOk.eq_def] at h
  split at h
  · rename_i x' g is a ts b heq
    obtain ⟨rfl, rfl, rfl⟩ := Expr.let_.inj heq
    refine .inr ⟨g, is, a, ts, b, rfl, rfl, ?_⟩
    split at h
    · exact .inl ⟨_, rfl⟩
    · exact .inr (by simpa using h)
    · cases h
  · obtain ⟨rfl, rfl, rfl⟩ := Expr.let_.inj ‹_›
    exact .inl h
  all_goals first | (exfalso; simp_all) | cases h

/-- `heldRetOk` rejects a bare `ret`. -/
theorem heldRetOk_ret {a : At} : Scc.Lower.heldRetOk (.ret a) = false := by
  simp [Scc.Lower.heldRetOk]

/-- `heldRetOk` of an `ifeq`: both branches'. -/
theorem heldRetOk_ifeq {a b : At} {y n : Expr} (h : Scc.Lower.heldRetOk (.ifeq a b y n) = true) :
    Scc.Lower.heldRetOk y = true ∧ Scc.Lower.heldRetOk n = true := by
  simpa [Scc.Lower.heldRetOk] using h

/-- `heldRetOk` of a `split`: its body's. -/
theorem heldRetOk_split {a : At} {x y : String} {e : Expr} (h : Scc.Lower.heldRetOk (.split a x y e) = true) :
    Scc.Lower.heldRetOk e = true := by
  simpa [Scc.Lower.heldRetOk] using h

/-- `heldRetOk` of an `unpack`: its body's. -/
theorem heldRetOk_unpack {a : At} {x y : String} {e : Expr} (h : Scc.Lower.heldRetOk (.unpack a x y e) = true) :
    Scc.Lower.heldRetOk e = true := by
  simpa [Scc.Lower.heldRetOk] using h

/-- **The held return tail to the exits `X`**: from the node at
`let x = call g … in ret b` (`b` a literal or `x`) with the walk's facts
there, a segment to `X` at the ghost `c0`. -/
def HeldTailCX (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (lcx : Scc.Lower.Ctx) (cx : FnCtx)
    (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (W : FragS isaLSE2)
    (K : State → State → Prop) (ms : List TermRun.Frame → MemSide isaLSE2) (fp ra : BitVec 64) (tp : UInt64)
    (fs : List TermRun.Frame) (G0 : Ctl → Prop) (i : Expr → String → Nat → Option Nat) (T : Expr → Prop)
    (Rk : Expr × Scc.Lower.Env × Nat → Prop) (Lk : Expr × List (String × Scc.Lower.LitV) → Prop)
    (X : Ctl → FragS isaLSE2) : Prop :=
  ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (env : Scc.Lower.Env) (n : Nat) (x g : String) (is : List String) (a : At)
    (ts : List Ty) (b : At) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
    (l : Scc.IR.Label) (k : Nat) (r : Res2),
    G0 c0 → lowerC2 lcx env n l k (.let_ x (.call g is a ts) (.ret b)) = some r → Fresh env n →
    CodeC2 cx Cd Bl kk pc r.insts r.term →
    BlocksCodeC2 cx Cd Bl (_root_.Executable.labels exe).label r.blocks →
    (∀ q ∈ lowerEnvs2 lcx env n (.let_ x (.call g is a ts) (.ret b)), ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ Rk q ∧
      EnvTy2 q ∧ GrpL q.2.1 ∧ LocBaseRegAt (ofEnv2 q.2.1) q.1) →
    (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits (.let_ x (.call g is a ts) (.ret b)),
      LitPt q ∧ CallLk lcx.prog q ∧ Lk q) →
    Scc.Lower.countsB lcx.prog cs bufs lits (.let_ x (.call g is a ts) (.ret b)) = true →
    xchgsB cs bufs (.let_ x (.call g is a ts) (.ret b)) = true →
    ((∃ k, b = .lit k) ∨ b = .var x) →
    SegWS W K p lbl ms
      (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc (.let_ x (.call g is a ts) (.ret b)) env lits cs bufs)
      (X c0)

/-- **A lowered body whose paths all end in a held return tail is one
segment to the exits `X`** (`body2_segS_ofX` under `heldRetOk`): each
`let x = call … in ret b` by `HeldTailCX`; no bare `ret` is reached. -/
theorem body2_segS_ofXH {cx : FnCtx} {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64}
    {Rk : Expr × Scc.Lower.Env × Nat → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    {X : Ctl → FragS isaLSE2}
    (hXr : ∀ c0 c0', FrameRunM p (c0, fs) (c0', fs) → ∀ s c fs', X c0' s c fs' → X c0 s c fs')
    (hAbX : ∀ c0 s c fs', Ab s c fs' → X c0 s c fs')
    (hcall : CallC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk)
    (hlane : LaneC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk)
    (hprint : PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hadd : AddC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hsub : SubC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hpure : PureMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hsplit : SplitMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hunpack : UnpackMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hif : IfC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T)
    (hheld : HeldTailCX p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Rk Lk X) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2) (kk : Nat) (pc : Int64)
      (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 cx Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 cx Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ Rk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits e, LitPt q ∧ CallLk lcx.prog q ∧ Lk q) →
      Scc.Lower.countsB lcx.prog cs bufs lits e = true → xchgsB cs bufs e = true →
      Scc.Lower.heldRetOk e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
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
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX hH c0 hG
    rcases heldRetOk_let hH with hH' | ⟨g, is, a, ts, b, rfl, rfl, hb⟩
    case inr => exact hheld c0 pc kk env n x g is a ts b lits cs bufs l k r hG hr hfr hcode hbl hW hL hC hX hb
    have hP := hpt hG hr hfr hW hL hC
    by_cases hp : isPure op = true
    · obtain ⟨t, ws, sc, hq, r', hpo, hm, hr', rfl⟩ := lowerC2_pure_inv hp hr
      have hW' := walk2_tail_pure hp hpo hm hW
      exact (ih _ n l k r' kk pc _ _ _ hr' (hfr.pure hpo x) hcode hbl hW' (hlitL hL) (hcntL hC)
        (xchgsB_tail hX) hH' c0 hG).mono_pre
        (hpure c0 pc env n x op e t ws sc hq lits cs bufs hp hP (pairSmall_head hX) hpo hm (hcf hr' hW'))
    cases op with
    | add a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC2_add_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_add ha hb hW
      exact seg_contX hG0 hXr hAbX hG
        (hadd c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hP ha hb hi (hcf hr' hW'))
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (hfr.add x) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) hH' c0' hG'
    | sub a b =>
      obtain ⟨ta, pa, tb, pb, r', ha, hb, hr', rfl⟩ := lowerC2_sub_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_sub ha hb hW
      exact seg_contX hG0 hXr hAbX hG
        (hsub c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hP ha hb hi (hcf hr' hW'))
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (hfr.add x) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) hH' c0' hG'
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
          | ⟨xe, dg, t, b, o, m, cw, r', hx, hdg, hrt, ha, hr', rfl⟩
      · obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
        have hW' := walk2_tail_call hfrm hx hdg hrt ha hW
        have hF := hcf hr' hW'
        exact seg_contX hG0 hXr hAbX hG
          (hcall c0 pc pc' kk env n x g is a ts e t w lits cs bufs hG hP.2.1 hfr hP.2.2.2.1
            hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC ⟨hx, dg, hdg, hrt⟩ ha hi hF.1 hF.2.1 hF.2.2.2.2
            ⟨l, k, _, hr, hcode, hbl,
            fun q hq =>
              ⟨(hW q hq).1, (hW q hq).2.1, (hW q hq).2.2.2.1, (hW q hq).2.2.2.2.1, (hW q hq).2.2.2.2.2⟩, hL, hC, hX⟩)
          fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (Fresh.callC1 hfr x) hrest hbl hW' (hlitL hL)
            (hcntL hC) (xchgsB_tail hX) hH' c0' hG'
      · obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts _ kk pc).1 hcode
        have hW' := walk2_tail_print hx hdg hrt ha hW
        have hF := hcf hr' hW'
        exact seg_contX hG0 hXr hAbX hG (hprint c0 pc pc' kk env n x g is a ts e xe dg t b o m cw lits cs bufs hG hP.2.1
            hfr hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC
            (by
              rw [← argShape_of_find hdg]
              exact (hL (.let_ x (.call g is a ts) e, lits) (by simp [Scc.Lower.litWalk2])).2.1 x g is a ts e rfl) hx
            hdg hrt ha hi hF.1 hF.2.1 hF.2.2.2.2)
          fun c0' hG' => ih _ (n + 4) l (k + 5) r' _ pc' _ _ _ hr' (hfr.print x) hrest hbl hW' (hlitL hL)
            (hcntL hC) (xchgsB_tail hX) hH' c0' hG'
    | newBuf cn τ =>
      obtain ⟨tk, kv, en, em, h, sc, hq, r', ha, hc, hh, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
      have hW' := walk2_tail_newBuf ha hc hh hw hm hW
      have hF := hcf hr' hW'
      exact seg_contX hG0 hXr hAbX hG (hbuf c0 pc pc' kk env n x cn τ e tk kv en em h lits cs bufs hG hP.2.1 hfr
          hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC ha hc hh hw hi hF.1 hF.2.1 hF.2.2.2.2
          ⟨l, k, _, hr, hcode, hbl,
            fun q hq =>
              ⟨(hW q hq).1, (hW q hq).2.1, (hW q hq).2.2.2.1, (hW q hq).2.2.2.2.1, (hW q hq).2.2.2.2.2⟩, hL, hC, hX⟩)
        fun c0' hG' => ih _ (n + 1) l (k + 1) r' _ pc' _ _ _ hr' (hfr.newBuf x τ) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) hH' c0' hG'
    | xchgAt b j v =>
      obtain ⟨t, bw, rb, o, tj, iv, μ, u, nu, mu, tv, w, s1, sc, hq, r', hb, hrf, hj, he, hg, hv, hs, hm, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_, _] kk pc).1 hcode
      have hW' := walk2_tail_xchg hb hrf hj he hg hv hs hm hW
      have hF := hcf hr' hW'
      exact seg_contX hG0 hXr hAbX hG (hlane c0 pc pc' kk env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs
          hG hP.2.1 hfr hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hC (xchgB_of_ok hX) hb hrf hj he hg hv hs hi
          hF.1 hF.2.1 hF.2.2.2.2
          hP.2.2.2.2.2.2.2.2 hP.2.2.2.2.2.2.2.1 (walk2_head hW).2.2.2.2.2)
        fun c0' hG' => ih _ (n + 1) l (k + 2) r' _ pc' _ _ _ hr' (hfr.xchg x u) hrest hbl hW' (hlitL hL)
          (hcntL hC) (xchgsB_tail hX) hH' c0' hG'
    | _ => first | exact absurd rfl hp | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX hH c0 hG
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
      (by simpa only [xchgsB] using hX) (heldRetOk_split hH) c0 hG).mono_pre
      (hsplit c0 pc env n a x y e t ws u w nu lits cs bufs hP ha hpr hv (hcf hr' hW'))
  | unpack a i' x e ih =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX hH c0 hG
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
      (by simpa only [xchgsB] using hX) (heldRetOk_unpack hH) c0 hG).mono_pre
      (hunpack c0 pc env n a i' x e b ws lits cs bufs hP ha (hcf hr' hW'))
  | ifeq a b yes no ihy ihn =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX hH c0 hG
    have hP := hpt hG hr hfr hW hL hC
    obtain ⟨ta, pa, tb, pb, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have hmy : (⟨labName "then" n, ry.insts, ry.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    have hmn : (⟨labName "else" (n + 1), rn.insts, rn.term⟩ : Scc.IR.Block) ∈
        ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
          ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks := by simp
    obtain ⟨Ly, ky, hLy, hcy⟩ := hbl _ hmy (lowerC2_term_ne lcx _ _ _ _ _ _ hy)
    obtain ⟨Ln, kn, hLn, hcn⟩ := hbl _ hmn (lowerC2_term_ne lcx _ _ _ _ _ _ hn)
    have hnext := lowerC2_next_ge lcx yes env (n + 2) _ 0 ry hy
    simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
    simp only [xchgsB, Bool.and_eq_true] at hX
    have segy := ihy env (n + 2) _ 0 ry ky _ lits cs bufs hy (hfr.mono (by omega)) hcy
      (fun b hb => hbl b (by simp [hb])) (walk2_tail_yes ha hb hW)
      (fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hq)))
      hC.1 hX.1 (heldRetOk_ifeq hH).1 c0 hG
    have segn := ihn env ry.next _ 0 rn kn _ lits cs bufs hn (hfr.mono (by omega)) hcn
      (fun b hb => hbl b (by simp [hb])) (walk2_tail_no hfrm ha hb hy hW)
      (fun q hq => hL q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hq)))
      hC.2 hX.2 (heldRetOk_ifeq hH).2 c0 hG
    exact (hif c0 pc kk env n a b yes no ta tb pa pb lits cs bufs hP ha hb hcode Ly Ln hLy hLn).seq
      (SegWS.or_pre segy segn)
  | ret a =>
    intro env n l k r kk pc lits cs bufs hr hfr hcode hbl hW hL hC hX hH
    simp [Scc.Lower.heldRetOk] at hH
  | _ => intro env n l k r kk pc lits cs bufs hr; simp [lowerC2] at hr


/-- **From a held pair to the exits**: the source held at a callee's `ret`
one frame above `main` (`HeldC` of `ContC` at `ret b`, `b` a literal or the
call's result `x`) is at `heldRN` of the node at `ret b` at the frame (its
`HeldTail` from the frame, `heldTail_of_frame`; the return step its run);
a segment from each such held node to `ExitC2SLF` gives one from `HeldC`. -/
theorem held_segX {cx : FnCtx} {fp ra : BitVec 64} {tp : UInt64} {i : Expr → String → Nat → Option Nat}
    {ty : Ty} {Ab : FragS isaLSE2} {x : String} {b : At} {c0 : Ctl} {pc' : Int64}
    {env' : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hbx : (∃ k, b = .lit k) ∨ b = .var x)
    (hseg : ∀ (f : TermRun.Frame) (c0' : Ctl), FrameRunM p (c0, []) (c0', []) → f.x = x → f.body = .ret b →
      SegWS W K p lbl ms
        ((At exe endPc R F (heldRN p [f] ((bodyN2 p lbl lsize i cx fp ra c0' pc' (.ret b) (ofEnv2 env') lits cs
          bufs).withTp tp))).at [f])
        (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab)) :
    SegWS W K p lbl ms
      (fun s c fs' => HeldC p (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 [] (fun _ _ _ => False) pc' (.ret b)
        env' lits cs bufs) [] x (.ret b) s c fs')
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  refine (SegWS.exists_pre (P := fun g : {q : TermRun.Frame × Ctl //
      FrameRunM p (c0, []) (q.2, []) ∧ q.1.x = x ∧ q.1.body = .ret b} =>
      (At exe endPc R F (heldRN p [g.1.1] ((bodyN2 p lbl lsize i cx fp ra g.1.2 pc' (.ret b) (ofEnv2 env') lits cs
        bufs).withTp tp))).at [g.1.1])
    fun g => hseg g.1.1 g.1.2 g.2.1 g.2.2.1 g.2.2.2).mono_pre ?_
  rintro s c fs' ⟨a, f, cR, hc, rfl, hfx, hfb, hst, hQ⟩
  rcases hQ with ⟨-, c0', hrun, he, hn, hd, hpc, σ, hA, hFm, hJ⟩ | hQ
  · have hσ : f.σs = [] := by
      cases hst with
      | ret _ hσ _ => exact hσ
    exact ⟨⟨(f, c0'), hrun, hfx, hfb⟩, ⟨he, hn, hd, hpc, σ, hA, hFm, heldTail_of_frame hc hσ hfx hfb hbx, cR,
      .single hst, hJ⟩, rfl⟩
  · exact hQ.elim

end HeldWalk

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.seg_heldRN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.seg_heldRN

/-- info: 'Spike.Lib.LowerA64.exitC2SLF_of_heldRN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.exitC2SLF_of_heldRN

/-- info: 'Spike.Lib.LowerA64.retHeld_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retHeld_seg

/-- info: 'Spike.Lib.LowerA64.body2_segS_ofXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.body2_segS_ofXH

/-- info: 'Spike.Lib.LowerA64.held_segX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.held_segX
