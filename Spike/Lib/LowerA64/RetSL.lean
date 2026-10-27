/-
**The exits by placements with the source facts for the caller**
(AArch64): `retNS` with `RetL` (the returned atom at the block's return
type), the exit a block's segment ends in for its callers; the twin of
`Spike/Lib/LowerX64/RetSL.lean`.

- `retNSL`, `ExitC2SL`: `retNS`'s invariant and `RetL ty`, the body's exits
  there; `ExitC2SL.trans`, `ExitC2SL.toS` (forgetting `RetL`);
- `RetJS.toJ2_int`, `ExitC2SL.toB_int`: at `int`, the placements one word
  in `x0` (`RetJ2`), so the exit is `ExitC2B`'s;
- `ret_edgeSL`: `ret a`'s edge at `bodyN2` to `retNSL` (`ret_edgeS` with the
  layout's facts at `a`: bound, a literal below `2^64`, the erasure `ty`'s);
- `retC2SL_of`: a `ret`'s premise at `ExitC2SL` (the walk's literal fact
  `RetLk ty` at the `ret`);
- `body2_segS_ofSL`: the body's segment to `ExitC2SL`, the literal walk's
  `ret`s at `ty`'s layout (`hretL`).
-/
import Spike.Lib.LowerA64.Body2SegX
import Spike.Lib.LowerA64.RetNB
import Spike.Lib.Src.NJLBEnv2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal SEnv sevalAt WordPl WordsRep group)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (lowerC2 Res2 lowerC2_ret_inv)
open Scc.Lower.Inv (atomV)

/-- **The return's exit by placements with `RetL`**: `retNS`'s node, its
invariant with the returned atom's facts at the return type `ty`. -/
def retNSL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) (ty : Ty) : ND :=
  ⟨Int64.ofBitVec ra, ⟨0, []⟩, fun σ c => (RetJS lbl fp ra σ c ∧ LocalRun p c0 c) ∧ RetL ty c⟩

/-- **The literal walk's fact at a `ret`**: the returned atom's layout,
literals dropped, `ty`'s (`ret_layout`). -/
def RetLk (ty : Ty) (q : Expr × List (String × Scc.Lower.LitV)) : Prop :=
  ∀ a, q.1 = .ret a → (Scc.Lower.litAt q.2 a).erase = Scc.Lower.shapeOf ty

/-- **At `int`, the placements are one word in `x0`** (`RetL.int`: one
number, which no locative placement represents). -/
theorem RetJS.toJ2_int {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJS lbl fp ra σ c) (hL : RetL .int c) : RetJ2 lbl fp ra σ c := by
  obtain ⟨a, t, ws, ops, pls, val, ht, hh, he, hg, hn, hv, hw, h29, h30⟩ := h
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
      refine ⟨a, t, [w], ht, hh, he, by simp only [List.length_singleton]; decide, fun j hj _ => ?_, h29, h30⟩
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
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The body's exits at the frames `fs` by placements with `RetL`**:
`ExitC2S` at `retNSL`. -/
def ExitC2SL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (ty : Ty) (Ab : FragS isaLSE2) : FragS isaLSE2 := fun s c fs' =>
  (fs' = fs ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    At exe endPc R F ((retNSL p lbl fp ra c0' ty).withTp tp) s c) ∨ Ab s c fs'

/-- **`ExitC2SL` re-anchored by a frame run** of the ghost. -/
theorem ExitC2SL.trans {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {fs : List TermRun.Frame}
    {ty : Ty} {Ab : FragS isaLSE2} (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2SL p lbl exe endPc R F fp ra tp c0' fs ty Ab s c fs' →
      ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨e, c1, hr', h⟩ => ⟨e, c1, hr.trans hr', h⟩

/-- **`ExitC2SL` is an `ExitC2S`** (`RetL` dropped). -/
theorem ExitC2SL.toS {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame}
    {ty : Ty} {Ab : FragS isaLSE2} {s : State} {c : Ctl}
    {fs' : List TermRun.Frame} (h : ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs') :
    ExitC2S p lbl exe endPc R F fp ra tp c0 fs Ab s c fs' := by
  rcases h with ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, ⟨hJ, -⟩, htp⟩ | h
  · exact .inl ⟨e, c0', hr, he, hn, hd, hpc, σ, hA, hFm, hJ, htp⟩
  · exact .inr h

/-- **At `int`, `ExitC2SL` is an `ExitC2B`** (`RetJS.toJ2_int`). -/
theorem ExitC2SL.toB_int {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl} {fs : List TermRun.Frame}
    {Ab : FragS isaLSE2} {s : State} {c : Ctl}
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
theorem ret_edgeSL {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty} {pls : List WordPl}
    (hsa : sevalAt s a = some (t, pls)) (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat}
    {ty : Ty} (hsc : InLits lits a) (hlit : ∀ n, a = .lit n → n < 2 ^ 64)
    (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty) :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN2 p lbl lsize i cx fp ra c0 pc (.ret a) s lits cs bufs)
      (directives (ls ++ cx.leave ++ [ret])) (fun _ : Unit => retNSL p lbl fp ra c0 ty)
      (fun e : Empty => e.elim) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have hds := directives_leave hf h1 ls
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (ls ++ cx.leave ++ [ret])) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [hds, okBlk_retLoads hf h1 h16 _ _ hl]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this
  refine ⟨by rw [hds]; simp [epi], hok, fun σ c ⟨⟨L, sm, B, hJ⟩, hfj, hc0, _⟩ => ?_⟩
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
  obtain ⟨R, hrun, -, hval⟩ := arun_retLoads hf h1 lab _ hl pc σ
  have hsnd : ((vs.zip argRegs).map Prod.snd).Nodup := by
    exact argRegs_nodup.sublist (map_snd_zip_sublist _ _)
  refine ⟨c1, hr, .inl ⟨(), ?_⟩⟩
  show Hit (retNSL p lbl fp ra c0 ty)
    (arun _ (directives (ls ++ cx.leave ++ [ret])) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c1
  rw [hds, arun_append, hrun]
  obtain ⟨hpc, hso, hsl, -, h29, h30, hr0⟩ := arun_epi lab
    (pc + Int64.ofNat (4 * (directives ls).length)) (-(cx.frame : Int)) { σ with regs := R }
    (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  have h16' : (Int64.ofInt cx.frame - 16).toInt = cx.frame - 16 := by
    rw [Int64.toInt_sub, show (16 : Int64).toInt = 16 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc h30
  rw [h16', show -(cx.frame : Int) + (cx.frame - 16) = -16 by omega] at h29
  rw [hF64, show -(cx.frame : Int) + cx.frame = 0 by omega] at hso
  obtain ⟨hfp, hra⟩ := hfj
  refine ⟨?_, ?_, ⟨⟨a, t', ws, vs, pls, opdVal (rsOf cx) σ.slot, hj.1, hj.2.1, he, hg', hn, fun k hk hr' => ?_, hw,
    ?_, ?_⟩, hc0.trans hr⟩, hRL⟩
  · rw [hpc]; simp [retNSL, hra]
  · rw [hso]; rfl
  · have hmem : (vs[k], argRegs[k]) ∈ vs.zip argRegs := by
      have hz : (vs.zip argRegs)[k]'(by simp; omega) = (vs[k], argRegs[k]) := List.getElem_zip
      rw [← hz]
      exact List.getElem_mem _
    obtain ⟨v, hv, hR⟩ := hval hsnd _ hmem
    have hne := argRegs_ne (List.getElem_mem hr')
    rw [hr0 _ hne.1 hne.2]
    simp only at hR hv
    rw [hR, hv]
  · rw [h29]; exact hfp
  · rw [h30]; exact hra

end Edge

section Body

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A `ret`'s premise at `ExitC2SL`** from its edge (`ret_edgeSL`): as
`retC2S_of`, the returned atom bound or a literal below `2^64` (`LitPt`)
and at `ty`'s layout (the walk's literal fact `RetLk ty`); any walk fact
`Rk`. -/
theorem retC2SL_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isaLSE2} {Rk : Expr × Scc.Lower.Env × Nat → Prop}
    (lcx : Scc.Lower.Ctx) (tp : UInt64) (ty : Ty) :
    RetCX p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Rk (RetLk ty)
      (fun c0 => ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab) := by
  intro c0 pc kk env n a t ws lits cs bufs hP _ hLk ha hcode
  obtain ⟨hG, -, -, hlp, -, hg, -, -, -⟩ := hP
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  obtain ⟨hm, ls, hl, hc⟩ := codeC2_retN hcode
  have hn : ws.length ≤ argRegs.length := by
    have : argRegs.length = 8 := rfl
    have : Scc.IR.maxRets = 6 := rfl
    omega
  obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hg ha
  have hCd' : ∀ {pc blk}, SubCd Cd pc blk → CdOf exe endPc pc blk := fun h => SubCd.cdOf hCd h
  have hret := (((ret_edgeSL (p := p) (lbl := lbl) (fp := fp) (ra := ra) (c0 := c0)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 h16 hl hn (_root_.Executable.labels exe).label
    hsa hpl hsc hlit (hLk a rfl)).tp tp).seg
    (W := W₀) (K := K) (lbl := lbl) (ms := ms fs) hF hR hal hlo hhi (hCd' hc)
    (BlkW.withTp (hW c0 hG _ _ _ _ _ _ _ hc (Or.inr ⟨ws, ls, hn, hl, rfl⟩)) tp)).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  exact (SegWS.liftS fs hret hW₀).mono_post fun s c fs' ⟨h, hfs⟩ => .inl ⟨hfs, c0, .refl _, h⟩

/-- **A lowered `Accepted2` body is one segment to its exits by placements
with `RetL`** (`body2_segS_ofX` at `ExitC2SL`, the `ret`'s premise
`retC2SL_of`): `body2_segS_ofS`'s premises, and every `ret` of the literal
walk at `ty`'s layout (`hretL`, `ret_layout` at a block of return type
`ty`). -/
theorem body2_segS_ofSL {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {Cd : Int64 → List Directive → Prop}
    {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {fs : List TermRun.Frame} {W₀ : Frag isaLSE2} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    {i : Expr → String → Nat → Option Nat}
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd Cd pc blk → Kind2 cx blk →
      BlkW W₀ K exe endPc R F (bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs) blk)
    {T : Expr → Prop} {Ab : FragS isaLSE2}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64} (ty : Ty)
    (hcall : CallC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (RetLk ty))
    (hlane : LaneC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hbuf : NewBufC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab (RetLk ty))
    (hprint : PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hadd : AddC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hsub : SubC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hpure : PureMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hsplit : SplitMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hunpack : UnpackMv2 p lbl lsize lcx cx exe endPc R F fp ra tp fs G0 i T)
    (hif : IfC2 p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T) :
    ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (l : Scc.IR.Label) (k : Nat) (r : Res2) (kk : Nat) (pc : Int64)
      (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)),
      lowerC2 lcx env n l k e = some r → Fresh env n →
      CodeC2 cx Cd Bl kk pc r.insts r.term →
      BlocksCodeC2 cx Cd Bl (_root_.Executable.labels exe).label r.blocks →
      (∀ q ∈ lowerEnvs2 lcx env n e, ImmIn i (ofEnv2 q.2.1) q.1 ∧ T q.1 ∧ EnvTy2 q ∧ GrpL q.2.1 ∧
        LocBaseRegAt (ofEnv2 q.2.1) q.1) →
      (∀ q ∈ Scc.Lower.litWalk2 lcx.prog lits e, LitPt q ∧ CallLk lcx.prog q) →
      (∀ a lits', (.ret a, lits') ∈ Scc.Lower.litWalk2 lcx.prog lits e →
        (Scc.Lower.litAt lits' a).erase = Scc.Lower.shapeOf ty) →
      Scc.Lower.countsB lcx.prog cs bufs lits e = true → xchgsB cs bufs e = true →
      ∀ c0, G0 c0 → SegWS W K p lbl ms (LetAt p lbl lsize i cx exe endPc R F fp ra tp c0 fs pc e env lits cs bufs)
        (ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab) := by
  intro e env n l k r kk pc lits cs bufs hr hfr hcode hbl hWk hL hretL
  exact body2_segS_ofX (Rk := fun _ => True) (Lk := RetLk ty) hG0 hfrm (fun _ _ hr => ExitC2SL.trans hr)
    (fun _ _ _ _ h => .inr h) hcall hlane hbuf hprint hadd hsub hpure hsplit hunpack hif
    (retC2SL_of hf h1 h16 hF hR hal hlo hhi hCd hW₀ hW lcx tp ty) e env n l k r kk pc lits cs bufs hr hfr hcode
    hbl (fun q hq => have h := hWk q hq; ⟨h.1, h.2.1, trivial, h.2.2⟩)
    (fun q hq => ⟨(hL q hq).1, (hL q hq).2, fun a ha => hretL a q.2 (by rw [← ha]; exact hq)⟩)

end Body

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.RetJS.toJ2_int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.RetJS.toJ2_int

/-- info: 'Spike.Lib.LowerA64.ExitC2SL.toB_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ExitC2SL.toB_int

/-- info: 'Spike.Lib.LowerA64.ret_edgeSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.ret_edgeSL

/-- info: 'Spike.Lib.LowerA64.retC2SL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retC2SL_of

/-- info: 'Spike.Lib.LowerA64.body2_segS_ofSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.body2_segS_ofSL
