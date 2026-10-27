/-
**The constructs' premises of the `Accepted2` body's induction, from the
edges** (x86-64): `Spike/Lib/LowerX64/Body2Seg.lean`'s premises at the
code-carrying constructs from `Spike/Lib/LowerX64/Node2Edges.lean`'s block
edges, the code-free moves from the source moves at `ofEnv2`
(`Spike/Lib/Src/NJLBEnv2.lean`); the twin of the AArch64
`Spike/Lib/LowerA64/Body2SegOf.lean`.

- `add_edge2E`, `sub_edge2E`, `br_edge2E`: the edges at a lowering
  environment (`ofEnv2`), the operands' leaf facts from the node's own
  source invariant (`NJB.litMask_one`);
- `addC2_of`, `subC2_of`: a checked `+` and a saturating `-` (`add_edge2E`,
  `sub_edge2E`, then `store_edge2`);
- `ifC2_of`: an `if` (`br_edge2E`, then `jmp_edge2`);
- `addC2_ofQ`, `subC2_ofQ`, `ifC2_ofQ`: the same with the blocks inside `W₀`
  only at the nodes meeting a guard `Q` (e.g. `fs = [] → no bare ret`,
  `CalleePre2`'s), `Q` at the construct and its continuation from the
  walk (`hQ`, e.g. `ContNR.qAdd`); `addC2_of`, `subC2_of`, `ifC2_of` at no
  guard;
- `retC2_of`: a `ret` of up to six words (`ret_edgeN2`);
- `pureMv2_of`, `splitMv2_of`, `unpackMv2_of`: the moves (`NJB.pure_move2`,
  `NJB.split_move2`, `NJB.unpack_move2`);
- `body2_segS`: the body's segment (`body2_segS_of` from the above), the
  calls (`CallC2`, `LaneC`, `NewBufC`, `PrintCallC`) premises;
- `body2_segSS`: the same to the exits by placements (`body2_segS_ofS`).
-/
import Spike.Lib.LowerX64.Body2SegX
import Spike.Lib.LowerX64.Node2Edges
import Spike.Lib.Src.NJLBEnv2
import Spike.Lib.Src.GroupPl

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item labelOf)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2 isPure pureOp markR)
open Scc.Lower.Inv (atomV regName labName)
open Spike.Lib.Form (SEnv sevalAt lookupS)
open Scc.Lower (LitV litAt)

section Edges

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {c0 : Ctl}
  {lits : List (String × LitV)} {cs bufs : List (String × Nat)}

/-- **The checked `+`'s edge at a lowering environment** (`add_edge2` at
`ofEnv2 env`, the operands' leaf facts from the node's `NJB`). -/
theorem add_edge2E {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ addChecked (ovfL fr))).length) (lab : String → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {env : Scc.Lower.Env} {ta tb : Ty}
    (hsa : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsb : sevalAt (ofEnv2 env) b = some (tb, [.one pb]))
    (hla : InLits lits a) (hlb : InLits lits b)
    (hfr : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS (ofEnv2 env) y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i (ofEnv2 env) (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e))
    (htot' : ∀ y ∈ Scc.Sem.exprFv e, (lookupS ((x, .int, [.one (.reg d)]) :: ofEnv2 env) y).isSome)
    (hlb' : LocBaseRegAt ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e)
    (himm' : ImmIn i ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e) :
    BlkEdge p lab (-(fr.size : Int)) 16
      (bodyN2 p lbl lsize i fr fp ra c0 pc (.let_ x (.add a b) e) (ofEnv2 env) lits cs bufs)
      ((dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs)
      (fun _ : Unit => pendN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat zs.sum)
        e ((x, .int, [.one (.reg d)]) :: ofEnv2 env) ((x, .leaf none) :: lits) (Scc.Lower.csAfter x cs (.add a b))
        (Scc.Lower.bufsAfter x cs bufs (.add a b)) off)
      (fun _ : Unit => abortN2 i T p lbl fr lab fp ra c0) := by
  obtain ⟨hne, hok, -⟩ := add_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (x := x) (e := e) (pc := pc)
    hf h1 ha hb hd hz lab hsa hsb hfr htot himm hT
  refine ⟨hne, hok, fun σ c hJ => ?_⟩
  obtain ⟨L, sm, B, hN⟩ := hJ.1
  exact (add_edge2 (p := p) (lbl := lbl) (lsize := lsize)
      (c0 := c0) (lits := lits) (cs := cs) (bufs := bufs) (pc := pc) hf h1
    ha hb hd hz lab hsa hsb hla hlb (hN.litMask_one hsa hla) (hN.litMask_one hsb hlb) hfr htot himm hT htot' hlb'
    himm').2.2 σ c hJ

/-- **The saturating `-`'s edge at a lowering environment** (`sub_edge2` at
`ofEnv2 env`). -/
theorem sub_edge2E {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ subSatItems)).length) (lab : String → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {env : Scc.Lower.Env} {ta tb : Ty}
    (hsa : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsb : sevalAt (ofEnv2 env) b = some (tb, [.one pb]))
    (hla : InLits lits a) (hlb : InLits lits b)
    (hfr : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    {i : Expr → String → Nat → Option Nat}
    (htot' : ∀ y ∈ Scc.Sem.exprFv e, (lookupS ((x, .int, [.one (.reg d)]) :: ofEnv2 env) y).isSome)
    (hlb' : LocBaseRegAt ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e)
    (himm' : ImmIn i ((x, .int, [.one (.reg d)]) :: ofEnv2 env) e) :
    BlkEdge p lab (-(fr.size : Int)) 16
      (bodyN2 p lbl lsize i fr fp ra c0 pc (.let_ x (.sub a b) e) (ofEnv2 env) lits cs bufs)
      ((dirs (la ++ lb ++ subSatItems)).zip zs)
      (fun _ : Unit => pendN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat zs.sum)
        e ((x, .int, [.one (.reg d)]) :: ofEnv2 env) ((x, .leaf none) :: lits) (Scc.Lower.csAfter x cs (.sub a b))
        (Scc.Lower.bufsAfter x cs bufs (.sub a b)) off) (fun e : Empty => e.elim) := by
  obtain ⟨hne, hok, -⟩ := sub_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (x := x) (e := e) (pc := pc)
    hf h1 ha hb hd hz lab hsa hsb hfr
  refine ⟨hne, hok, fun σ c hJ => ?_⟩
  obtain ⟨L, sm, B, hN⟩ := hJ.1
  exact (sub_edge2 (p := p) (lbl := lbl) (lsize := lsize)
      (c0 := c0) (lits := lits) (cs := cs) (bufs := bufs) (pc := pc) hf h1
    ha hb hd hz lab hsa hsb hla hlb (hN.litMask_one hsa hla) (hN.litMask_one hsb hlb) hfr htot' hlb'
    himm').2.2 σ c hJ

/-- **An `if`'s compare-and-branch's edge at a lowering environment**
(`br_edge2` at `ofEnv2 env`). -/
theorem br_edge2E {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    (T : String) {pc : Int64} {zs : List Nat} (hz : zs.length = (brDirs la lb T).length) (lab : String → Int64)
    {fp ra : BitVec 64} {a b : At} {yes no : Expr} {env : Scc.Lower.Env} {ta tb : Ty}
    (hsa : sevalAt (ofEnv2 env) a = some (ta, [.one pa])) (hsb : sevalAt (ofEnv2 env) b = some (tb, [.one pb]))
    (hla : InLits lits a) (hlb : InLits lits b) {i : Expr → String → Nat → Option Nat} :
    BlkEdge p lab (-(fr.size : Int)) 16
      (bodyN2 p lbl lsize i fr fp ra c0 pc (.ifeq a b yes no) (ofEnv2 env) lits cs bufs)
      ((brDirs la lb T).zip zs)
      (fun bb : Bool =>
        if bb then bodyN2 p lbl lsize i fr fp ra c0 (lab T) yes (ofEnv2 env) lits cs bufs
        else bodyN2 p lbl lsize i fr fp ra c0 (pc + Int64.ofNat zs.sum) no (ofEnv2 env) lits cs bufs)
      (fun e : Empty => e.elim) := by
  obtain ⟨hne, hok, -⟩ := br_edge (p := p) (lbl := lbl) (c0 := c0) (fp := fp) (ra := ra) (yes := yes)
    (no := no) (pc := pc) hf h1 ha hb T hz lab hsa hsb
  refine ⟨hne, hok, fun σ c hJ => ?_⟩
  obtain ⟨L, sm, B, hN⟩ := hJ.1
  exact (br_edge2 (p := p) (lbl := lbl) (lsize := lsize) (c0 := c0) (lits := lits) (cs := cs) (bufs := bufs) (pc := pc)
    (yes := yes) (no := no) (i := i) hf h1 ha hb T hz lab hsa hsb hla hlb (hN.litMask_one hsa hla)
    (hN.litMask_one hsb hlb)).2.2 σ c hJ

end Edges

section Body2SegOf

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

theorem ofEnv2_int (env : Scc.Lower.Env) (x : String) (d : Scc.IR.Reg) :
    ofEnv2 ((x, .int, [.reg d]) :: env) = (x, .int, [.one (.reg d)]) :: ofEnv2 env := rfl

theorem pc_append1 (pc : Int64) (zs : List Nat) (z : Nat) :
    pc + Int64.ofNat (zs ++ [z]).sum = pc + Int64.ofNat zs.sum + Int64.ofNat z := by
  rw [List.sum_append, Int64.ofNat_add, Int64.add_assoc]; simp

/-- **A checked `+`'s premise** (`AddC2`) from its edges: the add's block
to the pending store or the overflow abort label (`add_edge2E`), the
store's to the node at the continuation (`store_edge2`). -/
theorem addC2_ofQ {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    {Q : Expr → Prop}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk → Q t →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      Q t → BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop}
    (hQ : ∀ x a b e, T (.let_ x (.add a b) e) → Q (.let_ x (.add a b) e) ∧ Q e) {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    AddC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk kk' env n x a b e ta tb pa pb lits cs bufs hP ha hb hi hcf
  obtain ⟨hG, hTt, hfr, hL, -, hg, -, hImm, hfv⟩ := hP
  rcases hi with ⟨-, l, zs, hE, hz, hc, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, _, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩
  rotate_left
  · cases he
  · cases he
  · cases he
  obtain ⟨la, lb, off, hla, hlb, hd, hl⟩ := emits_add hE
  rw [hl] at hz hc
  obtain ⟨zs1, zs2, rfl, hz1, hz2, hc1, hc2⟩ := subCd_split hz (SubCd.whole hc)
  match zs2, hz2 with
  | [z], _ =>
  have hCd' := cdOf_subCd hCd
  have hadd := ((add_edge2E (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0) (x := x) (e := e)
    (lits := lits) (cs := cs) (bufs := bufs) hf h1 hla hlb hd hz1 (_root_.Executable.labels exe).label
    (sevalAt_ofEnv2_one hg ha) (sevalAt_ofEnv2_one hg hb) (hL.1 a (by simp [headAtoms]))
    (hL.1 b (by simp [headAtoms])) (fresh_ofEnv2 hfr x) hfv hImm hTt hcf.1 hcf.2.2.2.2 hcf.2.1).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc1)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc1
      (Kind2.of1 (kind1_zip (.inl ⟨_, _, la, lb, hla, hlb, .inl rfl⟩) hz1)) (hQ x a b e hTt).1) tp)
  have hst := SegW.of_next1E (((store_edge2 (p := p) (lbl := lbl) (lsize := lsize)
      (fp := fp) (ra := ra) (c0 := c0) (t := e)
    (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv2 env)
    (lits := (x, .leaf none) :: lits) (cs := Scc.Lower.csAfter x cs (.add a b))
    (bufs := Scc.Lower.bufsAfter x cs bufs (.add a b)) (i := i) (z := z) hf h1 hd
    (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
    hF hR hlo hhi (hCd' _ _ hc2)
    (BlkW.withTp (hWp c0 hG _ _ _ _ _ _ _ _ hc2 (Kind2.of1 (kind1_zip (.inr (.inl ⟨_, off, hd, rfl⟩)) rfl))
      (by simp) (hQ x a b e hTt).2) tp))
  have h0 := SegW.seq_left (hadd.mono_post fun s c h => h.elim (fun ⟨_, h⟩ => .inl h)
    fun ⟨_, h⟩ => .inr h) hst
  rw [pc_append1]
  refine (SegWS.liftS fs h0 hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => ?_
  rcases h with h | h
  · exact .inl ⟨hfs, c0, .refl _, h⟩
  · exact .inr (hfs ▸ hab c0 hG s c (At.of_withTp h))

/-- **A saturating `-`'s premise** (`SubC2`) from its edges (`sub_edge2E`,
`store_edge2`). -/
theorem subC2_ofQ {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    {Q : Expr → Prop}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk → Q t →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      Q t → BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} (hQ : ∀ x a b e, T (.let_ x (.sub a b) e) → Q (.let_ x (.sub a b) e) ∧ Q e)
    {Ab : FragS isa} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    SubC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk kk' env n x a b e ta tb pa pb lits cs bufs hP ha hb hi hcf
  obtain ⟨hG, hTt, hfr, hL, -, hg, -, -, -⟩ := hP
  rcases hi with ⟨-, l, zs, hE, hz, hc, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, _, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩
  rotate_left
  · cases he
  · cases he
  · cases he
  obtain ⟨la, lb, off, hla, hlb, hd, hl⟩ := emits_sub hE
  rw [hl] at hz hc
  obtain ⟨zs1, zs2, rfl, hz1, hz2, hc1, hc2⟩ := subCd_split hz (SubCd.whole hc)
  match zs2, hz2 with
  | [z], _ =>
  have hCd' := cdOf_subCd hCd
  have hsub := SegW.of_next1E (((sub_edge2E (p := p) (lbl := lbl) (lsize := lsize)
      (fp := fp) (ra := ra) (c0 := c0) (x := x)
    (e := e) (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hla hlb hd hz1
    (_root_.Executable.labels exe).label
    (sevalAt_ofEnv2_one hg ha) (sevalAt_ofEnv2_one hg hb) (hL.1 a (by simp [headAtoms]))
    (hL.1 b (by simp [headAtoms])) (fresh_ofEnv2 hfr x) hcf.1 hcf.2.2.2.2 hcf.2.1).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc1)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc1
      (Kind2.of1 (kind1_zip (.inl ⟨_, _, la, lb, hla, hlb, .inr (.inl rfl)⟩) hz1)) (hQ x a b e hTt).1) tp))
  have hst := SegW.of_next1E (((store_edge2 (p := p) (lbl := lbl) (lsize := lsize)
      (fp := fp) (ra := ra) (c0 := c0) (t := e)
    (s := (x, .int, [.one (.reg (regName x n))]) :: ofEnv2 env)
    (lits := (x, .leaf none) :: lits) (cs := Scc.Lower.csAfter x cs (.sub a b))
    (bufs := Scc.Lower.bufsAfter x cs bufs (.sub a b)) (i := i) (z := z) hf h1 hd
    (_root_.Executable.labels exe).label).tp tp).seg (W := W₀) (K := K) (lbl := lbl) (ms := ms fs)
    hF hR hlo hhi (hCd' _ _ hc2)
    (BlkW.withTp (hWp c0 hG _ _ _ _ _ _ _ _ hc2 (Kind2.of1 (kind1_zip (.inr (.inl ⟨_, off, hd, rfl⟩)) rfl))
      (by simp) (hQ x a b e hTt).2) tp))
  rw [pc_append1]
  exact (SegWS.liftS fs (hsub.seq hst) hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- **An `if`'s premise** (`IfC2`) from its edges: the compare-and-branch
(`br_edge2E`), then on the fall-through the `jmp` to the `else` label
(`jmp_edge2`). -/
theorem ifC2_ofQ {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    {Q : Expr → Prop}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk → Q t →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} (hQ : ∀ a b y n, T (.ifeq a b y n) → Q (.ifeq a b y n) ∧ Q n)
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    IfC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T := by
  intro c0 pc kk env n a b yes no ta tb pa pb lits cs bufs hP ha hb hcode
  obtain ⟨hG, hTt, -, hL, -, hg, -, -, -⟩ := hP
  rcases hcode with hu | ⟨l1, zs, hE, hz, hc⟩
  · cases hu
  obtain ⟨la, lb, hla, hlb, hl⟩ := emits_br hE
  rw [hl] at hz hc
  obtain ⟨zs1, zs2, rfl, hz1, hz2, hc1, hc2⟩ := subCd_split hz (SubCd.whole hc)
  match zs2, hz2 with
  | [z], _ =>
  have hCd' := cdOf_subCd hCd
  have hbr := SegW.of_nextBTp (((br_edge2E (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0)
    (yes := yes) (no := no) (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hla hlb _ hz1
    (_root_.Executable.labels exe).label (sevalAt_ofEnv2_one hg ha) (sevalAt_ofEnv2_one hg hb)
    (hL.1 a (by simp [headAtoms])) (hL.1 b (by simp [headAtoms]))).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc1)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc1
      (Kind2.of1 (kind1_zip (.inl ⟨_, _, la, lb, hla, hlb, .inr (.inr ⟨_, rfl⟩)⟩) hz1))
      (hQ a b yes no hTt).1) tp))
  have hj := SegW.of_next1E (((jmp_edge2 (p := p) (lbl := lbl) (lsize := lsize)
      (fp := fp) (ra := ra) (c0 := c0) (t := no)
    (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs) (i := i) (fr := fr) _ (z := z)
    (_root_.Executable.labels exe).label).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd' _ _ hc2)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc2 (Kind2.of1 (kind1_zip (.inr (.inr (.inl ⟨_, rfl⟩))) rfl))
      (hQ a b yes no hTt).2) tp))
  have h2 := SegWS.seq_left ((SegWS.liftS_or fs hbr hW₀).mono_post fun s c fs' h => h.symm)
    (SegWS.liftS fs hj hW₀)
  exact h2.mono_post fun s c fs' h => h.symm

/-- **A checked `+`'s premise** (`AddC2`) from its edges, the blocks
inside `W₀` at every node (`addC2_ofQ` at no guard). -/
theorem addC2_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    AddC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  addC2_ofQ (Q := fun _ => True) hf h1 hF hR hlo hhi hCd hW₀
    (fun c0 h pc t s l cs b blk hc hk _ => hW c0 h pc t s l cs b blk hc hk)
    (fun c0 h pc t s l cs b k blk hc hk h1 _ => hWp c0 h pc t s l cs b k blk hc hk h1)
    (fun _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩) hab lcx tp

/-- **A saturating `-`'s premise** (`SubC2`) from its edges (`subC2_ofQ` at
no guard). -/
theorem subC2_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isa} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    SubC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab :=
  subC2_ofQ (Q := fun _ => True) hf h1 hF hR hlo hhi hCd hW₀
    (fun c0 h pc t s l cs b blk hc hk _ => hW c0 h pc t s l cs b blk hc hk)
    (fun c0 h pc t s l cs b k blk hc hk h1 _ => hWp c0 h pc t s l cs b k blk hc hk h1)
    (fun _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩) lcx tp

/-- **An `if`'s premise** (`IfC2`) from its edges (`ifC2_ofQ` at no
guard). -/
theorem ifC2_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    IfC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T :=
  ifC2_ofQ (Q := fun _ => True) hf h1 hF hR hlo hhi hCd hW₀
    (fun c0 h pc t s l cs b blk hc hk _ => hW c0 h pc t s l cs b blk hc hk)
    (fun _ _ _ _ _ => ⟨⟨⟩, ⟨⟩⟩) lcx tp

/-- **A `ret`'s premise** (`RetC2`) from its edge (`ret_edgeN2`): `a`'s
words placed one by one (`RetOk`), loaded into the result registers. -/
theorem retC2_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isa} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    RetC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc kk env n a t ws lits cs bufs hP hok ha hcode
  obtain ⟨hG, -, -, -, -, hg, -, -, -⟩ := hP
  rcases hcode with hu | ⟨l1, zs, hE, hz, hc⟩
  · cases hu
  obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
  rw [hl] at hz hc
  obtain ⟨t', ws', ha', -, hgr⟩ := hok a rfl
  rw [ha] at ha'
  cases ha'
  obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hg ha
  rw [hgr, Option.some.injEq] at hpl
  subst hpl
  have hk : Kind2 fr ((retDirs lw).zip zs) := by
    unfold Kind2
    rw [List.map_fst_zip (by omega)]
    exact .inr ⟨ws, lw, hn, hlw, rfl⟩
  have hret := SegW.of_next1E (((ret_edgeN2 (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hlw hn hz (_root_.Executable.labels exe).label
    hsa).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd _ _ hc)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ (SubCd.whole hc) hk) tp))
  exact (SegWS.liftS fs hret hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- A `let` without code's literal words do not read the program. -/
theorem opLit_pure {op : Op} (hp : isPure op = true) (p q : Prog)
    (lits : List (String × Scc.Lower.LitV)) : Scc.Lower.opLit p lits op = Scc.Lower.opLit q lits op := by
  cases op <;> simp_all [isPure, Scc.Lower.opLit]

/-- **A `let` without code's move** (`PureMv2`) from the source move at
`ofEnv2` (`NJB.pure_move2`). -/
theorem pureMv2_of {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    PureMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T := by
  intro c0 pc env n x op e t ws sc hq lits cs bufs hp hP hbn hpo _ _ s c fs'
    ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  obtain ⟨-, -, -, hL, -, hg, hC, -, -⟩ := hP
  simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC
  refine ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, ?_⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  rw [opLit_pure hp lcx.prog p]
  exact hJ.pure_move2 hpo hg hL hC.1 hbn

/-- **A `split`'s move** (`SplitMv2`) from the source move at `ofEnv2`
(`NJB.split_move2`). -/
theorem splitMv2_of {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    SplitMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T := by
  intro c0 pc env n a x y e t ws u w nu lits cs bufs hP ha hpr hv _ s c fs'
    ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ⟩, hfj, hc0, hsr⟩, htp⟩, hfs⟩
  obtain ⟨-, -, -, hL, hT, hg, -, -, -⟩ := hP
  exact ⟨⟨he, hn, hd, hpc, σ, hA, hFm, ⟨⟨L, sm, B, hJ.split_move2 ha hpr hv hg hT hL⟩, hfj, hc0, hsr⟩, htp⟩,
    hfs⟩

/-- **An index unpack's move** (`UnpackMv2`) from the source move at
`ofEnv2` (`NJB.unpack_move2`). -/
theorem unpackMv2_of {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {fs : List TermRun.Frame} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (lcx : Scc.Lower.Ctx) (tp : UInt64) :
    UnpackMv2 p lbl lsize lcx fr exe endPc R F fp ra tp fs G0 i T := by
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
its immediates `i`'s, the point in `T`, a `ret` of at most six words
placed one by one (`RetOk`), the types (`EnvTy2`) and grouping (`GrpL`); at
each point of the literal walk (`litWalk2`) `LitPt` and the calls'
layouts (`CallLk`); the pairs paired
(`countsB`); the lane stores in range (`xchgsB`). -/
theorem body2_segS {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) (hprog : lcx.prog = p) {tp : UInt64}
    (hcall : CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hlane : LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hprint : PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2)
      (kk : Nat) (pc : Int64) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 fr Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 fr Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ RetOk q ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 p lits e, LitPt q ∧ CallLk p q) →
      Scc.Lower.countsB p cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2 p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  subst hprog
  exact body2_segS_of hG0 hfrm hcall hlane hbuf hprint
    (addC2_of hf h1 hF hR hlo hhi hCd hW₀ hW hWp hab lcx tp)
    (subC2_of hf h1 hF hR hlo hhi hCd hW₀ hW hWp lcx tp)
    (pureMv2_of lcx tp) (splitMv2_of lcx tp) (unpackMv2_of lcx tp)
    (ifC2_of hf h1 hF hR hlo hhi hCd hW₀ hW lcx tp)
    (retC2_of hf h1 hF hR hlo hhi hCd hW₀ hW lcx tp)

/-- **A lowered `Accepted2` body is one segment to its exits by
placements** (`body2_segS_ofS` with the constructs' premises from their
edges): `body2_segS`'s premises, but no `RetOk`. -/
theorem body2_segSS {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd Cd pc blk → Kind2 fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc R F (pendN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs k) blk)
    {T : Expr → Prop} {Ab : FragS isa}
    (hab : ∀ c0, G0 c0 → ∀ s c,
      At exe endPc R F (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) s c → Ab s c fs)
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) (hprog : lcx.prog = p) {tp : UInt64}
    (hcall : CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hlane : LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (fun _ => True))
    (hprint : PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2)
      (kk : Nat) (pc : Int64) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 fr Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 fr Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 p lits e, LitPt q ∧ CallLk p q) →
      Scc.Lower.countsB p cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2S p lbl exe endPc R F fp ra tp c0 fs Ab) := by
  subst hprog
  exact body2_segS_ofS hf h1 hF hR hlo hhi hCd hW₀ hG0 hW hfrm hcall hlane hbuf hprint
    (addC2_of hf h1 hF hR hlo hhi hCd hW₀ hW hWp hab lcx tp)
    (subC2_of hf h1 hF hR hlo hhi hCd hW₀ hW hWp lcx tp)
    (pureMv2_of lcx tp) (splitMv2_of lcx tp) (unpackMv2_of lcx tp)
    (ifC2_of hf h1 hF hR hlo hhi hCd hW₀ hW lcx tp)

end Body2SegOf

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.addC2_ofQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addC2_ofQ

/-- info: 'Spike.Lib.LowerX64.subC2_ofQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subC2_ofQ

/-- info: 'Spike.Lib.LowerX64.ifC2_ofQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifC2_ofQ

/-- info: 'Spike.Lib.LowerX64.addC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms addC2_of

/-- info: 'Spike.Lib.LowerX64.subC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subC2_of

/-- info: 'Spike.Lib.LowerX64.ifC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ifC2_of

/-- info: 'Spike.Lib.LowerX64.retC2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms retC2_of

/-- info: 'Spike.Lib.LowerX64.body2_segS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segS

/-- info: 'Spike.Lib.LowerX64.body2_segSS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body2_segSS

end Spike.Lib.LowerX64
