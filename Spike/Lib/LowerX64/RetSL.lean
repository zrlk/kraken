/-
**The exits by placements with the source facts for the caller**
(x86-64): `retNS` with `RetL` (the returned atom at the block's return
type), the exit a block's segment ends in for its callers; the twin of
`Spike/Lib/LowerA64/RetSL.lean`.

- `retNSL`, `ExitC2SL`: `retNS`'s invariant and `RetL ty`, the body's exits
  there; `ExitC2SL.trans`, `ExitC2SL.toS` (forgetting `RetL`);
- `RetJS.toJ2_int`, `ExitC2SL.toB_int`: at `int`, the placements one word
  in `%rax` (`RetJ2`), so the exit is `ExitC2B`'s;
- `ret_edgeSL`: `ret a`'s edge at `bodyN2` to `retNSL` (`ret_edgeS` with the
  layout's facts at `a`: bound, a literal below `2^64`, the erasure `ty`'s);
- `retC2SL_of`: a `ret`'s premise at `ExitC2SL` (the walk's literal fact
  `RetLk ty` at the `ret`);
- `body2_segS_ofSL`: the body's segment to `ExitC2SL`, the literal walk's
  `ret`s at `ty`'s layout (`hretL`).
-/
import Spike.Lib.LowerX64.Body2SegX
import Spike.Lib.LowerX64.RetNB
import Spike.Lib.Src.NJLBEnv2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal SEnv sevalAt WordPl WordsRep group)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2)
open Scc.Lower.Inv (atomV)

/-- **The return's exit by placements with `RetL`**: `retNS`'s node, its
invariant with the returned atom's facts at the return type `ty`. -/
def retNSL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) (ty : Ty) : ND :=
  ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => (RetJS lbl fp σ c ∧ LocalRun p c0 c) ∧ RetL ty c⟩

/-- **The literal walk's fact at a `ret`**: the returned atom's layout,
literals dropped, `ty`'s (`ret_layout`). -/
def RetLk (ty : Ty) (q : Expr × List (String × Scc.Lower.LitV)) : Prop :=
  ∀ a, q.1 = .ret a → (Scc.Lower.litAt q.2 a).erase = Scc.Lower.shapeOf ty

/-- **At `int`, the placements are one word in `%rax`** (`RetL.int`: one
number, which no locative placement represents). -/
theorem RetJS.toJ2_int {lbl : WeakMem.AllocLabel → Option Nat} {fp : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJS lbl fp σ c) (hL : RetL .int c) : RetJ2 lbl fp σ c := by
  obtain ⟨a, t, ws, ops, pls, val, ht, hh, he, hg, hn, hv, hw, hbp⟩ := h
  obtain ⟨a', t', w, ht', he', hnum⟩ := RetL.int hL
  rw [ht] at ht'
  cases ht'
  rw [he] at he'
  cases he'
  obtain ⟨n, hnv, -⟩ := hnum
  rcases pls with _ | ⟨pl, _ | ⟨pl', pls⟩⟩
  · exact absurd hw (by simp [WordsRep])
  · have hop := group_opds hg
    cases pl with
    | one o =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, WordPl.opds] at hop
      subst hop
      obtain ⟨⟨v, hvo, hrep⟩, -⟩ := hw
      have h0 := hv 0 (by simp) (by decide)
      simp only [List.getElem_cons_zero] at h0
      rw [hvo] at h0
      cases h0
      refine ⟨a, t, [w], ht, hh, he, by simp only [List.length_singleton]; decide, fun j hj _ => ?_, hbp⟩
      simp only [List.length_singleton] at hj
      obtain rfl : j = 0 := by omega
      exact hrep
    | loc b off =>
      obtain ⟨⟨vb, vo, -, -, hloc⟩, -⟩ := hw
      rw [hnv] at hloc
      exact hloc.elim
  · exact absurd hw (by simp [WordsRep])

section RetSL

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

/-- **The body's exits at the frames `fs` by placements with `RetL`**:
`ExitC2S` at `retNSL`. -/
def ExitC2SL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (ty : Ty) (Ab : FragS isa) : FragS isa := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    At exe endPc R F ((retNSL p lbl fp ra c0' ty).withTp tp) s c) ∨ Ab s c fs'

/-- **`ExitC2SL` re-anchored by a frame run** of the ghost. -/
theorem ExitC2SL.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame}
    {ty : Ty} {Ab : FragS isa} (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2SL p lbl exe endPc R F fp ra tp c0' fs ty Ab s c fs' →
      ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

/-- **`ExitC2SL` is an `ExitC2S`** (`RetL` dropped). -/
theorem ExitC2SL.toS {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame}
    {ty : Ty} {Ab : FragS isa} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame} (h : ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs') :
    ExitC2S p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' := by
  rcases h with ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, -⟩, htp⟩ | h
  · exact .inl ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, hJ, htp⟩
  · exact .inr h

/-- **At `int`, `ExitC2SL` is an `ExitC2B`** (`RetJS.toJ2_int`). -/
theorem ExitC2SL.toB_int {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame}
    {Ab : FragS isa} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame} (h : ExitC2SL p lbl exe endPc R F fp ra tp c0 fs .int Ab s c fs') :
    ExitC2B p lbl exe endPc R F fp ra tp c0 fs .int Ab s c fs' := by
  rcases h with ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨⟨hJ, hl⟩, hL⟩, htp⟩ | h
  · exact .inl ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨⟨hJ.toJ2_int hL, hl⟩, hL⟩, htp⟩
  · exact .inr h

end RetSL

section Edge

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {c0 : Ctl}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`ret a`'s edge by placements at `bodyN2` with `RetL`** (`ret_edgeS`):
`a` bound in the layouts `lits` or a literal below `2^64` (`hsc`, `hlit`),
its layout, literals dropped, `ty`'s (`hera`); the returned words as many
as the layout's (`compat_plLen`, `group_grp`). -/
theorem ret_edgeSL {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (retDirs lw).length) (lab : String → Int64) {fp ra : BitVec 64} {a : At} {s : SEnv}
    {t : Ty} {pls : List WordPl} (hsa : sevalAt s a = some (t, pls)) (hg : group t vs = some pls)
    {i : Expr → String → Nat → Option Nat}
    {ty : Ty} (hsc : InLits lits a) (hlit : ∀ n, a = .lit n → n < 2 ^ 64)
    (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN2 p lbl lsize i fr fp ra c0 pc (.ret a) s lits cs bufs)
      ((retDirs lw).zip zs) (fun _ : Unit => retNSL p lbl fp ra c0 ty) (fun e : Empty => e.elim) := by
  have hrr : Scc.Emit.X64.retRegs = Spike.Lib.X64.retRegs := rfl
  rw [hrr] at hl hn
  obtain ⟨rws, hlen, hd, hoks, hvs⟩ := getOps_rw hf h1 hl hn
  have hblk : retDirs lw = retBlk rws := by
    rw [retDirs, dirs_append, dirs_epiItems, hd]; rfl
  rw [hblk] at hz ⊢
  have hne : (retBlk rws).zip zs ≠ [] := by
    intro h
    have h' := congrArg List.length h
    simp only [List.length_zip, List.length_nil, ← hz, Nat.min_self] at h'
    rw [h'] at hz
    simp [retBlk, epi] at hz
  refine ⟨hne, retBlk_ok (by omega) hoks hz, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
  obtain ⟨c1, hr, hj, hEL, hEB, -, -⟩ := hJ
  obtain ⟨t', ws, he, hE, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  have hg' := (Spike.Lib.Form.group_of_eraseLen hE vs).trans hg
  -- the returned atom's facts for the caller
  have hRL : RetL ty c1 := by
    obtain ⟨hca, -⟩ := hEL.evalAt hsc hsa he
    have hlen : ws.length = (Scc.Lower.litAt lits a).words.length := by
      have := compat_plLen _ _ hca
      rw [plLen_of_eraseLen hE, (group_grp hg).2.1] at this
      rw [hw.length]; exact Option.some.inj this
    exact ⟨a, lits, hj.1, hEL, hsc, hlit, hera, ⟨L, sm, hEB.1⟩, t', ws, he, hlen⟩
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨c1, hr, .inl ⟨(), retBlk_hit lab pc (-(fr.size : Int)) σ rws hz (by simp [retNSL, hra]) rfl ?_⟩⟩
  intro σ' hsl _ hbp _ hreg
  refine ⟨⟨⟨a, t', ws, vs, pls, opdVal (rsOf fr) σ.slot, hj.1, hj.2.1, he, hg', hrr ▸ hn, fun k hk hk2 => ?_, hw,
    ?_⟩, hc0.trans hr⟩, hRL⟩
  · have hkr : k < rws.length := hlen ▸ hk
    rw [hvs k hk hkr σ.slot]
    have hm : (Spike.Lib.X64.retRegs[k]'(hrr ▸ hk2), rws[k]) ∈ Spike.Lib.X64.retRegs.zip rws := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩
    have := hreg _ _ hm
    simp only [hrr]
    rw [this]
  · rw [hbp, hfp]

end Edge

section Body

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isa} {K : State → State → Prop}

/-- **A `ret`'s premise at `ExitC2SL`** from its edge (`ret_edgeSL`): as
`retC2S_of`, the returned atom bound or a literal below `2^64` (`LitPt`)
and at `ty`'s layout (the walk's literal fact `RetLk ty`); any walk fact
`Rk`. -/
theorem retC2SL_of {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isa} {Rk : Expr × Scc.Lower.Env × Nat → Prop}
    (lcx : Scc.Lower.Ctx) (tp : UInt64) (ty : Ty) :
    RetCX p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Rk (RetLk ty)
      (fun c0 => ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab) := by
  intro c0 pc kk env n a t ws lits cs bufs hP _ hLk ha hcode
  obtain ⟨hG, -, -, hlp, -, hg, -, -, -⟩ := hP
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  rcases hcode with hu | ⟨l1, zs, hE, hz, hc⟩
  · cases hu
  obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
  rw [hl] at hz hc
  obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hg ha
  have hk : Kind2 fr ((retDirs lw).zip zs) := by
    unfold Kind2
    rw [List.map_fst_zip (by omega)]
    exact .inr ⟨ws, lw, hn, hlw, rfl⟩
  have hret := SegW.of_next1E (((ret_edgeSL (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0) (lits := lits)
    (cs := cs) (bufs := bufs) (i := i) hf h1 hlw hn hz (_root_.Executable.labels exe).label hsa hpl hsc hlit
    (hLk a rfl)).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hlo hhi (hCd _ _ hc)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ (SubCd.whole hc) hk) tp))
  exact (SegWS.liftS fs hret hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- **A lowered `Accepted2` body is one segment to its exits by placements
with `RetL`** (`body2_segS_ofX` at `ExitC2SL`, the `ret`'s premise
`retC2SL_of`): `body2_segS_ofS`'s premises, and every `ret` of the literal
walk at `ty`'s layout (`hretL`, `ret_layout` at a block of return type
`ty`). -/
theorem body2_segS_ofSL {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 fr blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isa}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64} (ty : Ty)
    (hcall : CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (RetLk ty))
    (hlane : LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (RetLk ty))
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
      (∀ a lits', (.ret a, lits') ∈ Scc.Lower.litWalk2 lcx.prog lits e →
        (Scc.Lower.litAt lits' a).erase = Scc.Lower.shapeOf ty) →
      Scc.Lower.countsB lcx.prog cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i fr exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab) := by
  intro e env n l k r kk pc lits cs bufs hr hfr hcode hbl hWk hL hretL
  exact body2_segS_ofX (Rk := fun _ => True) (Lk := RetLk ty) hG0 hfrm (fun _ _ hr => ExitC2SL.trans hr)
    (fun _ _ _ _ h => .inr h) hcall hlane hbuf hprint hadd hsub hpure hsplit hunpack hif
    (retC2SL_of hf h1 hF hR hlo hhi hCd hW₀ hW lcx tp ty) e env n l k r kk pc lits cs bufs hr hfr hcode
    hbl (fun q hq => have h := hWk q hq; ⟨h.1, h.2.1, trivial, h.2.2⟩)
    (fun q hq => ⟨(hL q hq).1, (hL q hq).2, fun a ha => hretL a q.2 (by rw [← ha]; exact hq)⟩)

end Body

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.RetJS.toJ2_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.RetJS.toJ2_int

/-- info: 'Spike.Lib.LowerX64.ExitC2SL.toB_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ExitC2SL.toB_int

/-- info: 'Spike.Lib.LowerX64.ret_edgeSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ret_edgeSL

/-- info: 'Spike.Lib.LowerX64.retC2SL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retC2SL_of

/-- info: 'Spike.Lib.LowerX64.body2_segS_ofSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.body2_segS_ofSL
