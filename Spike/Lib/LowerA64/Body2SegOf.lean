/-
**The constructs' premises of the `Accepted2` body's induction, from the
edges** (AArch64): `Spike/Lib/LowerA64/Body2Seg.lean`'s premises at the
code-carrying constructs from `Spike/Lib/LowerA64/Node2Edges.lean`'s block
edges, the code-free moves from the source moves at `ofEnv2`
(`Spike/Lib/Src/NJLBEnv2.lean`); the twin of the x86-64
`Spike/Lib/LowerX64/Body2SegOf.lean`.

- `addC2_of`, `subC2_of`: a checked `+` and a saturating `-` (`add_edge2`,
  `sub_edge2`, then `store_edge2`);
- `ifC2_of`: an `if` (`br_edge2`, then `jmp_edge2`);
- `addC2_ofQ`, `subC2_ofQ`, `ifC2_ofQ`: the same with the blocks inside `W₀`
  only at the nodes meeting a guard `Q` (e.g. `fs = [] → no bare ret`,
  `CalleePre2`'s), `Q` at the construct and its continuation from the
  walk (`hQ`, e.g. `ContNR.qAdd`); `addC2_of`, `subC2_of`, `ifC2_of` at no
  guard;
- `retC2_of`: a `ret` of any number of words (`ret_edgeN2`);
- `pureMv2_of`, `splitMv2_of`, `unpackMv2_of`: the moves (`NJB.pure_move2`,
  `NJB.split_move2`, `NJB.unpack_move2`);
- `body2_segS`: the body's segment (`body2_segS_of` from the above), the
  calls (`CallC2`, `LaneC`, `NewBufC`, `PrintCallC`) premises.
-/
import Spike.Lib.LowerA64.Body2Seg
import Spike.Lib.Src.ContNR
import Spike.Lib.LowerA64.Node2Edges
import Spike.Lib.Src.NJLBEnv2
import Spike.Lib.Src.GroupPl

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (newBufCall)
open Scc.Lower.Inv (atomV regName labName)
open Spike.Lib.Form (SEnv sevalAt lookupS)

section Body2SegOf

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

theorem ofEnv2_int (env : Scc.Lower.Env) (x : String) (d : Scc.IR.Reg) :
    ofEnv2 ((x, .int, [.reg d]) :: env) = (x, .int, [.one (.reg d)]) :: ofEnv2 env := rfl

/-- **A checked `+`'s premise** (`AddC2`) from its edges: the add's block
to the pending store or the overflow abort label (`add_edge2`), the
store's to the node at the continuation (`store_edge2`). -/
theorem addC2_ofQ {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    {Q : Expr → Prop}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk → Q t →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 cx blk → blk.length ≤ 1 →
      Q t → BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop}
    (hQ : ∀ x a b e, T (.let_ x (.add a b) e) → Q (.let_ x (.add a b) e) ∧ Q e) {Ab : FragS isaLSE2}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    AddC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hP ha hb hi hcf
  obtain ⟨hG, hTt, hfr, hL, -, hg, -, hImm, hfv⟩ := hP
  rcases hi with ⟨-, l, hl, hc, hpc'⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [newBufCall] at he
  · cases he
  obtain ⟨la, lb, off, hla, hlb, hd, hds⟩ := inst_addChk_inv hf h1 hl
  rw [hds] at hc hpc'
  simp only [InstsC2] at hpc'
  rw [List.length_append, show (strDirs off).length = 1 from rfl, add_ofNat_four_succ] at hpc'
  subst hpc'
  have hc1 := SubCd.left hc
  have hc2 := SubCd.right hc
  have hCd' : ∀ {pc blk}, SubCd Cd pc blk → CdOf exe endPc pc blk := fun h => SubCd.cdOf hCd h
  have hia : InLits lits a := hL.1 a (by simp [headAtoms])
  have hib : InLits lits b := hL.1 b (by simp [headAtoms])
  have hadd := ((add_edge2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
    (cs := cs) (bufs := bufs) hf h1 h16 hla hlb hd (_root_.Executable.labels exe).label
    (sevalAt_ofEnv2_one hg ha) (sevalAt_ofEnv2_one hg hb) hia hib (fresh_ofEnv2 hfr x) hfv hImm hTt
    hcf.1 hcf.2.2.2.2 hcf.2.1).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc1)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc1 (Kind2.of1 (.inl ⟨pa, pb, la, lb, hla, hlb, .inl rfl⟩))
      (hQ x a b e hTt).1) tp)
  have hst := ((store_edge2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := e)
    (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv2 env)
    (lits := (x, .leaf none) :: lits) (cs := Scc.Lower.csAfter x cs (.add a b))
    (bufs := Scc.Lower.bufsAfter x cs bufs (.add a b)) hf h1 h16 hd
    (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
    hF hR hal hlo hhi (hCd' hc2) (BlkW.withTp (hWp c0 hG _ _ _ _ _ _ _ _ hc2
      (Kind2.of1 (.inr (.inl ⟨_, off, hd, rfl⟩))) (Nat.le_refl 1) (hQ x a b e hTt).2) tp)
  have h0 := SegW.seq_left (hadd.mono_post fun s c h => h.elim (fun ⟨_, h⟩ => .inl h)
    fun ⟨_, h⟩ => .inr h) (hst.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim)
  refine (SegWS.liftS fs h0 hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => ?_
  rcases h with h | ⟨he, hn, hdd, hpc, σ, hA, hFm, hJ, _⟩
  · exact .inl ⟨hfs, c0, .refl _, h⟩
  · exact .inr (hfs ▸ hab c0 hG s c ⟨he, hn, hdd, hpc, σ, hA, hFm, hJ⟩)

/-- **A saturating `-`'s premise** (`SubC2`) from its edges (`sub_edge2`,
`store_edge2`). -/
theorem subC2_ofQ {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    {Q : Expr → Prop}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk → Q t →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 cx blk → blk.length ≤ 1 →
      Q t → BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop}
    (hQ : ∀ x a b e, T (.let_ x (.sub a b) e) → Q (.let_ x (.sub a b) e) ∧ Q e) {Ab : FragS isaLSE2}
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    SubC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk env n x a b e ta tb pa pb lits cs bufs hP ha hb hi hcf
  obtain ⟨hG, hTt, hfr, hL, -, hg, -, -, -⟩ := hP
  rcases hi with ⟨-, l, hl, hc, hpc'⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ | ⟨_, _, _, he, -⟩
  rotate_left
  · cases he
  · simp [newBufCall] at he
  · cases he
  obtain ⟨la, lb, off, hla, hlb, hd, hds⟩ := inst_subSat_inv hf h1 hl
  rw [hds] at hc hpc'
  simp only [InstsC2] at hpc'
  rw [List.length_append, show (strDirs off).length = 1 from rfl, add_ofNat_four_succ] at hpc'
  subst hpc'
  have hc1 := SubCd.left hc
  have hc2 := SubCd.right hc
  have hCd' : ∀ {pc blk}, SubCd Cd pc blk → CdOf exe endPc pc blk := fun h => SubCd.cdOf hCd h
  have hsub := (((sub_edge2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
    (cs := cs) (bufs := bufs) hf h1 h16 hla hlb hd (_root_.Executable.labels exe).label
    (sevalAt_ofEnv2_one hg ha) (sevalAt_ofEnv2_one hg hb) (hL.1 a (by simp [headAtoms]))
    (hL.1 b (by simp [headAtoms])) (fresh_ofEnv2 hfr x) hcf.1 hcf.2.2.2.2 hcf.2.1).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc1)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc1 (Kind2.of1 (.inl ⟨pa, pb, la, lb, hla, hlb, .inr (.inl rfl)⟩))
      (hQ x a b e hTt).1)
      tp)).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  have hst := (((store_edge2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := e)
    (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv2 env)
    (lits := (x, .leaf none) :: lits) (cs := Scc.Lower.csAfter x cs (.sub a b))
    (bufs := Scc.Lower.bufsAfter x cs bufs (.sub a b)) hf h1 h16 hd
    (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
    hF hR hal hlo hhi (hCd' hc2) (BlkW.withTp (hWp c0 hG _ _ _ _ _ _ _ _ hc2
      (Kind2.of1 (.inr (.inl ⟨_, off, hd, rfl⟩))) (Nat.le_refl 1) (hQ x a b e hTt).2) tp)).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  exact (SegWS.liftS fs (hsub.seq hst) hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- **An `if`'s premise** (`IfC2`) from its edges: the compare-and-branch
(`br_edge2`), then on the fall-through the `b` to the `else` label
(`jmp_edge2`). -/
theorem ifC2_ofQ {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    {Q : Expr → Prop}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk → Q t →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} (hQ : ∀ a b y n, T (.ifeq a b y n) → Q (.ifeq a b y n) ∧ Q n)
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    IfC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T := by
  intro c0 pc kk env n a b yes no ta tb pa pb lits cs bufs hP ha hb hcode Ly Ln hLy hLn
  obtain ⟨hG, hTt, -, hL, -, hg, -, -, -⟩ := hP
  obtain ⟨la, lb, Tl, Fl, hla, hlb, hT, hFl, hc1, hc2⟩ := codeC2_br hcode
  rw [hLy, Except.ok.injEq] at hT
  rw [hLn, Except.ok.injEq] at hFl
  subst hT hFl
  have hCd' : ∀ {pc blk}, SubCd Cd pc blk → CdOf exe endPc pc blk := fun h => SubCd.cdOf hCd h
  have hbr := (((br_edge2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (yes := yes) (no := no)
    (cs := cs) (bufs := bufs) hf h1 h16 hla hlb Ly (_root_.Executable.labels exe).label
    (sevalAt_ofEnv2_one hg ha) (sevalAt_ofEnv2_one hg hb) (hL.1 a (by simp [headAtoms]))
    (hL.1 b (by simp [headAtoms]))).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc1)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc1 (Kind2.of1 (.inl ⟨pa, pb, la, lb, hla, hlb, .inr (.inr ⟨Ly, rfl⟩)⟩))
      (hQ a b yes no hTt).1) tp)).mono_post
    fun st c h => show At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0
        (pc + Int64.ofNat (4 * (brDirs la lb Ly).length)) no (ofEnv2 env) lits cs bufs).withTp tp) st c ∨
      At exe endPc R F ((bodyN2 p lbl lsize i cx fp ra c0 ((_root_.Executable.labels exe).label Ly) yes (ofEnv2 env)
        lits cs bufs).withTp tp) st c from by
      rcases h with ⟨bb, h⟩ | ⟨e, _⟩
      · cases bb
        · exact .inl h
        · exact .inr h
      · exact e.elim
  have hj := (((jmp_edge2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (t := no) (s := ofEnv2 env)
    (lits := lits) (cs := cs) (bufs := bufs) (cx := cx) Ln (_root_.Executable.labels exe).label).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc2)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc2 (Kind2.of1 (.inr (.inr (.inl ⟨Ln, rfl⟩))))
      (hQ a b yes no hTt).2) tp)).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  have h2 := SegWS.seq_left ((SegWS.liftS fs hbr hW₀).mono_post fun s c fs' ⟨h, hfs⟩ =>
    h.imp (fun h => (⟨h, hfs⟩ : Frag.at _ fs s c fs')) (fun h => (⟨h, hfs⟩ : Frag.at _ fs s c fs')))
    (SegWS.liftS fs hj hW₀)
  exact h2.mono_post fun s c fs' h => h.symm

/-- **A checked `+`'s premise** (`AddC2`) from its edges, the blocks
inside `W₀` at every node (`addC2_ofQ` at no guard). -/
theorem addC2_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isaLSE2}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    AddC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  addC2_ofQ (Q := fun _ => True) hf h1 h16 hF hR hal hlo hhi hCd hW₀
    (fun c0 h pc t s l cs b blk hc hk _ => hW c0 h pc t s l cs b blk hc hk)
    (fun c0 h pc t s l cs b k blk hc hk h1 _ => hWp c0 h pc t s l cs b k blk hc hk h1)
    (fun _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩) hab lcx tp

/-- **A saturating `-`'s premise** (`SubC2`) from its edges (`subC2_ofQ` at
no guard). -/
theorem subC2_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isaLSE2}
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    SubC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  subC2_ofQ (Q := fun _ => True) hf h1 h16 hF hR hal hlo hhi hCd hW₀
    (fun c0 h pc t s l cs b blk hc hk _ => hW c0 h pc t s l cs b blk hc hk)
    (fun c0 h pc t s l cs b k blk hc hk h1 _ => hWp c0 h pc t s l cs b k blk hc hk h1)
    (fun _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩) lcx tp

/-- **An `if`'s premise** (`IfC2`) from its edges (`ifC2_ofQ` at no
guard). -/
theorem ifC2_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    IfC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T :=
  ifC2_ofQ (Q := fun _ => True) hf h1 h16 hF hR hal hlo hhi hCd hW₀
    (fun c0 h pc t s l cs b blk hc hk _ => hW c0 h pc t s l cs b blk hc hk)
    (fun _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩) lcx tp

/-- **A `ret`'s premise** (`RetC2`) from its edge (`ret_edgeN2`): `a`'s
words placed one by one (`RetOk`). -/
theorem retC2_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isaLSE2}
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    RetC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc kk env n a t ws lits cs bufs hP hok ha hcode
  obtain ⟨hG, -, -, -, -, hg, -, -, -⟩ := hP
  obtain ⟨-, ls, hl, hc⟩ := codeC2_retN hcode
  obtain ⟨t', ws', ha', hn, hgr⟩ := hok a rfl
  rw [ha] at ha'
  cases ha'
  obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2L hg ha
  rw [hgr, Option.some.injEq] at hpl
  subst hpl
  have hCd' : ∀ {pc blk}, SubCd Cd pc blk → CdOf exe endPc pc blk := fun h => SubCd.cdOf hCd h
  have hret := (((ret_edgeN2 (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (lits := lits) (cs := cs)
    (bufs := bufs) hf h1 h16 hl hn (_root_.Executable.labels exe).label hsa).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc (Or.inr ⟨ws, ls, hn, hl, rfl⟩)) tp)).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  exact (SegWS.liftS fs hret hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- A `let` without code's literal words do not read the program. -/
theorem opLit_pure {op : Op} (hp : Spike.Lib.LowerShape.isPure op = true) (p q : Prog)
    (lits : List (String × Scc.Lower.LitV)) : Scc.Lower.opLit p lits op = Scc.Lower.opLit q lits op := by
  cases op <;> simp_all [Spike.Lib.LowerShape.isPure, Scc.Lower.opLit]

/-- **A `let` without code's move** (`PureMv2`) from the source move at
`ofEnv2` (`NJB.pure_move2`). -/
theorem pureMv2_of {cx : FnCtx} {fp ra : BitVec 64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    PureMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T := by
  intro c0 pc env n x op e t ws sc hq lits cs bufs hp hP hbn hpo _ _ s c fs'
    ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  obtain ⟨-, -, -, hL, -, hg, hC, -, -⟩ := hP
  simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
  refine ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, ?_⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  rw [opLit_pure hp lcx.prog p]
  exact hJ.pure_move2 hpo hg hL hC.1 hbn

/-- **A `split`'s move** (`SplitMv2`) from the source move at `ofEnv2`
(`NJB.split_move2`). -/
theorem splitMv2_of {cx : FnCtx} {fp ra : BitVec 64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    SplitMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T := by
  intro c0 pc env n a x y e t ws u w nu lits cs bufs hP ha hpr hv _ s c fs'
    ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  obtain ⟨-, -, -, hL, hT, hg, -, -, -⟩ := hP
  exact ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ.split_move2 ha hpr hv hg hT hL⟩, hfj, hc0, hsr⟩, htp⟩,
    hfs⟩

/-- **An index unpack's move** (`UnpackMv2`) from the source move at
`ofEnv2` (`NJB.unpack_move2`). -/
theorem unpackMv2_of {cx : FnCtx} {fp ra : BitVec 64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    UnpackMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T := by
  intro c0 pc env n a i' x e b ws lits cs bufs hP ha _ s c fs'
    ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  obtain ⟨-, -, -, hL, -, hg, -, -, -⟩ := hP
  exact ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ.unpack_move2 ha hg hL⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩

/-- **A lowered `Accepted2` body is one segment at the frames `fs`**: from
the node at the body (`LetAt`: the lowering's environment `env` grouped,
`ofEnv2`; the walk's layouts `lits`, known values `cs`, buffers `bufs`; the
ghost `c0` in `G0`, closed under the frame runs at `fs`, `hG0`; the thread
pointer `tp`) to the body's exits (`ExitC2`). The code predicate `Cd` gives
the code (`hCd`): the open block's at `pc` (`CodeC2`), the later blocks' at
their labels (`BlocksCodeC2`); the blocks' states are inside `W₀` (inside
`W` at `fs`, `hW₀`) at the body's nodes (`hW`) and pending stores (`hWp`)
over every part of a code block (`SubCd`) that is a construct's block
(`Kind2`), for every ghost in `G0`; the body's own overflow abort label is
an abort (`hab`); the calls (`CallC2`, `LaneC`'s lane stores, `NewBufC`,
`PrintCallC`) are premises, the lowering's calls plain (`hfrm`) and its
program `p` (`hprog`); at each point of the lowering's walk (`lowerEnvs2`)
its immediates `i`'s, the point in `T`, a `ret` of at most eight words
placed one by one (`RetOk`), the types (`EnvTy2`) and grouping (`GrpL`); at
each point of the literal walk (`litWalk2`) `LitPt` and the calls'
layouts (`CallLk`); the pairs paired
(`countsB`); the lane stores in range (`xchgsB`). -/
theorem body2_segS {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 cx blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isaLSE2}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) (hprog : lcx.prog = p) {tp : UInt64}
    (hcall : CallC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hlane : LaneC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hprint : PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Spike.Lib.LowerShape.Res2)
      (kk : Nat) (pc : Int64) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      Spike.Lib.LowerShape.lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 cx Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 cx Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ RetOk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 p lits e, LitPt q ∧ CallLk p q) →
      Scc.Lower.countsB p cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  subst hprog
  exact body2_segS_of hG0 hfrm hcall hlane hbuf hprint
    (addC2_of hf h1 h16 hF hR hal hlo hhi hCd hW₀ hW hWp hab lcx tp)
    (subC2_of hf h1 h16 hF hR hal hlo hhi hCd hW₀ hW hWp lcx tp)
    (pureMv2_of lcx tp) (splitMv2_of lcx tp) (unpackMv2_of lcx tp)
    (ifC2_of hf h1 h16 hF hR hal hlo hhi hCd hW₀ hW lcx tp)
    (retC2_of hf h1 h16 hF hR hal hlo hhi hCd hW₀ hW lcx tp)

end Body2SegOf

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.addC2_ofQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addC2_ofQ

/-- info: 'Spike.Lib.LowerA64.subC2_ofQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subC2_ofQ

/-- info: 'Spike.Lib.LowerA64.ifC2_ofQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifC2_ofQ

end Spike.Lib.LowerA64
