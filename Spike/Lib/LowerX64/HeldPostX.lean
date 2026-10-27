/-
**`main`'s held exits with the held pair's facts** (x86-64): the producer
of `main`'s call at a post `UPostRF ∧ Q` for any `Q` a held pair and its
`UPostRF` give (e.g. the post control's value facts `MainCtlV`).

At `main`'s held exits the source is held one frame above depth 0 at a
callee's `ret a` (`HeldTail`), the frame continuing with `ret b`. The pair
reads its value back (`HeldRd`) when the callee's `ret` reads nothing (the
output extern's `ret ()`) or the frame returns its result (`b` the call's
result). The exit `ExitC2SLFV` is `ExitC2SLF` with both facts, `main`'s
own `ret` at depth 0 excluded.

- `HeldRd`, `heldCtlV`: at a held pair that reads its value back, a frame
  run to the return of `v` (`UPostRF`) gives the post control's facts:
  free of `ZBad`, not `main`'s `ret` at no frame, every word it reads
  representing `v`, the frame placed at no place;
- `ExitC2SLFV`, `ExitC2SLFV.trans`, `exitC2SLFV_of_heldRN`,
  `exitC2SLFV_of_heldRNU`;
- `held_segXQ`, `held_segXUQ`: `held_segX`, `held_segXU` at any exits;
- `mainTailX_segCV`, `mainTailX_segPV`: `mainTailX_segC`, `mainTailX_segP`
  to `ExitC2SLFV`;
- `heldTailCX_mainV`: `heldTailCX_main` to `ExitC2SLFV`, a literal returned
  only after the output extern (`hlitE`: no plain call at a literal tail);
- `CalleePre2.segHV`, `mainCallWSF_of_exitC2SLFV`, `mainCallWSF_ofHeldV`:
  `main`'s call at `UPostRF ∧ Q`;
- `heldLit_print`, `mainCallWSF_ofPlaceOKHV`: from the placement check, the
  literal tails `print` with its one index (`hlitP`) not a plain call;
  `mainCallWSF_ofPlaceOKHVC` the same at any code facts with
  `fnCode2OfP`'s return-address phase and code predicate (e.g.
  `fnCode2OfPMe`), its prologue facts and lowering context given.
-/
import Spike.Lib.LowerX64.MainHeldX
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff WcG CallerCells)
open Scc.Lower.Inv (atomV regName)
open Spike.Lib.LowerShape (lowerC2 Res2 lowerC2_call_inv walk2_tail_call walk2_tail_print lowerC2_ret_inv
  lowerC2_fv)

/-! ## The held pair's facts -/

/-- **A held pair reads its value back**: the held control reads nothing,
or every frame returns its result. -/
def HeldRd (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  exprFv c.term = [] ∨ ∀ f ∈ fs, f.body = .ret (.var f.x)

/-- **The post control's facts at a held pair**: from `HeldTail`, `HeldRd`
and a frame run to the return of `v` (`UPostRF`): free of `ZBad`, not
`main`'s `ret` at no frame, every word a variable of its term holds
representing `v` (the callee's `ret` read back through the frame's
`ret x`), the frame placed at no place (it reads nothing but its result). -/
theorem heldCtlV {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {c : Ctl} {fs : List TermRun.Frame}
    {v : BitVec 64} (hH : HeldTail c fs) (hrd : HeldRd c fs) (hU : UPostRF p lbl c fs v) :
    FrOk2 c fs ∧ (fs = [] → ∀ a, c.term ≠ .ret a) ∧
      (∀ y ∈ exprFv c.term, ∀ t ws, TermRun.lookupE c.env y = some (t, ws) → ∀ w ∈ ws,
        ValRep lbl w.val v.toNat) ∧
      ∀ s, FramesPlaced Λ lbl s fs := by
  obtain ⟨a, f, b, hc, rfl, hσ, hb, hfil⟩ := hH
  refine ⟨⟨by rw [hc]; trivial, fun f' hf' => by
      rw [List.mem_singleton] at hf'; subst hf'; rw [hb]; trivial⟩,
    fun h => absurd h (List.cons_ne_nil _ _), ?_, fun s => ?_⟩
  · intro y hy t ws hl w hw
    rw [hc] at hy
    obtain rfl : a = .var y := by
      cases a <;> simp [exprFv, atVars] at hy
      exact hy ▸ rfl
    rcases hrd with h0 | hx
    · rw [hc] at h0; simp [exprFv, atVars] at h0
    have hfb := hx f (List.mem_singleton_self f)
    obtain ⟨c', hr, a', t', w', hc', -, hev, -, hv⟩ := hU
    cases hr with
    | step h1 h2 =>
      cases h1 with
      | loc hl' => exact absurd hc (hl'.not_ret _)
      | call hc'' => rw [hc] at hc''; cases hc''
      | ret hc1 _ hev1 =>
        rw [hc] at hc1
        cases hc1
        cases h2 with
        | refl =>
          simp only [hfb] at hc'
          cases hc'
          simp only [TermRun.evalAt, TermRun.lookupE, List.find?_cons, beq_self_eq_true,
            Option.map_some] at hev
          cases hev
          simp only [TermRun.evalAt] at hev1
          rw [hl] at hev1
          cases hev1
          rw [List.mem_singleton] at hw
          exact hw ▸ hv
        | step h3 _ =>
          cases h3 with
          | loc hl' => exact absurd hfb (hl'.not_ret _)
          | call hc'' => rw [hfb] at hc''; cases hc''
  · refine ⟨fun _ _ _ => none, fun _ _ _ _ _ _ _ _ _ _ _ h => absurd h (by simp), fun d f' hf' x hx => ?_,
      fun _ _ _ _ _ _ h => absurd h (by simp)⟩
    cases d with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hf'
      subst hf'
      rw [hb] at hx
      simp only [exprFv] at hx
      rw [hfil] at hx
      cases hx
    | succ d => simp at hf'

/-! ## The held exits -/

/-- **The body's exits held at a pair that reads its value back**:
`ExitC2SLF`'s held exit at a pair `HeldTail` and `HeldRd` (`main`'s own
`ret` at depth 0 excluded), or an abort `Ab`. -/
def ExitC2SLFV (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (ty : Ty) (Ab : FragS isa) : FragS isa := fun s c fs' =>
  (ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs ty (fun _ _ _ => False) s c fs' ∧ HeldTail c fs' ∧
    HeldRd c fs') ∨ Ab s c fs'

section HeldExit

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {ty : Ty} {Ab : FragS isa}

/-- **`ExitC2SLFV` re-anchored by a frame run** of the ghost. -/
theorem ExitC2SLFV.trans {c0 c0' : Ctl} {fs : List TermRun.Frame} (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2SLFV p lbl exe endPc R F fp ra tp c0' fs ty Ab s c fs' →
      ExitC2SLFV p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun s c fs' h => h.imp_left fun ⟨h, hH, hd⟩ => ⟨ExitC2SLF.trans hr s c fs' h, hH, hd⟩

/-- **The return's exit at a held pair reading its value back is
`ExitC2SLFV`** (`exitC2SLF_of_heldRN` with `heldRN`'s `HeldTail`). -/
theorem exitC2SLFV_of_heldRN {c0 c0' : Ctl} {fs : List TermRun.Frame} (hr : FrameRunM p (c0, []) (c0', []))
    {s : State} {c : Ctl} (h : At exe endPc R F (heldRN p fs ((retNSL p lbl fp ra c0' ty).withTp tp)) s c)
    (hrd : HeldRd c fs) : ExitC2SLFV p lbl exe endPc R F fp ra tp c0 [] ty Ab s c fs := by
  obtain ⟨_, _, _, _, _, _, _, hH, _⟩ := id h
  exact .inl ⟨exitC2SLF_of_heldRN hr h, hH, hrd⟩

/-- **The return's exit at a held pair reading nothing is `ExitC2SLFV`**
(`exitC2SLF_of_heldRNU`; the pair reads its value back). -/
theorem exitC2SLFV_of_heldRNU {c0 c0' : Ctl} {fs : List TermRun.Frame} (hr : FrameRunM p (c0, []) (c0', []))
    {s : State} {c : Ctl} (h : At exe endPc R F (heldRNU p fs ((retNSL p lbl fp ra c0' ty).withTp tp)) s c) :
    ExitC2SLFV p lbl exe endPc R F fp ra tp c0 [] ty Ab s c fs := by
  obtain ⟨_, _, _, _, _, _, _, hv, hH, _⟩ := id h
  exact .inl ⟨exitC2SLF_of_heldRNU hr h, hH, .inl hv⟩

end HeldExit

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {exe : _root_.Executable} {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : List TermRun.Frame → MemSide isa} {W : FragS isa}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **From a held pair to any exits** (`held_segX` at the exits `Q`). -/
theorem held_segXQ {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat} {x : String} {b : At} {c0 : Ctl} {pc' : Int64}
    {env' : Scc.Lower.Env} {Q : FragS isa}
    (hbx : (∃ k, b = .lit k) ∨ b = .var x)
    (hseg : ∀ (f : TermRun.Frame) (c0' : Ctl), FrameRunM p (c0, []) (c0', []) → f.x = x → f.body = .ret b →
      SegWS W K p lbl ms
        ((At exe endPc R F (heldRN p [f] ((bodyN2 p lbl lsize i fr fp ra c0' pc' (.ret b) (ofEnv2 env') lits cs
          bufs).withTp tp))).at [f]) Q) :
    SegWS W K p lbl ms
      (fun s c fs' => HeldC p (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 [] (fun _ _ _ => False) pc' (.ret b)
        env' lits cs bufs) [] x (.ret b) s c fs') Q := by
  refine (SegWS.exists_pre (P := fun g : {q : TermRun.Frame × Ctl //
      FrameRunM p (c0, []) (q.2, []) ∧ q.1.x = x ∧ q.1.body = .ret b} =>
      (At exe endPc R F (heldRN p [g.1.1] ((bodyN2 p lbl lsize i fr fp ra g.1.2 pc' (.ret b) (ofEnv2 env') lits cs
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

/-- **From a held pair at `ret ()` to any exits** (`held_segXU` at the
exits `Q`). -/
theorem held_segXUQ {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat} {x : String} {b : At} {c0 : Ctl}
    {pc' : Int64} {env' : Scc.Lower.Env} {Q : FragS isa}
    (hbx : (∃ k, b = .lit k) ∨ b = .var x)
    (hseg : ∀ (f : TermRun.Frame) (c0' : Ctl), FrameRunM p (c0, []) (c0', []) → f.x = x → f.body = .ret b →
      SegWS W K p lbl ms
        ((At exe endPc R F (heldRNU p [f] ((bodyN2 p lbl lsize i fr fp ra c0' pc' (.ret b) (ofEnv2 env') lits cs
          bufs).withTp tp))).at [f]) Q) :
    SegWS W K p lbl ms
      (fun s c fs' => HeldC p (ContC p lbl lsize i fr exe endPc R F fp ra tp c0 [] (fun _ _ _ => False) pc' (.ret b)
        env' lits cs bufs) [] x (.ret b) s c fs' ∧ c.term = .ret .unit) Q := by
  refine (SegWS.exists_pre (P := fun g : {q : TermRun.Frame × Ctl //
      FrameRunM p (c0, []) (q.2, []) ∧ q.1.x = x ∧ q.1.body = .ret b} =>
      (At exe endPc R F (heldRNU p [g.1.1] ((bodyN2 p lbl lsize i fr fp ra g.1.2 pc' (.ret b) (ofEnv2 env') lits cs
        bufs).withTp tp))).at [g.1.1])
    fun g => hseg g.1.1 g.1.2 g.2.1 g.2.2.1 g.2.2.2).mono_pre ?_
  rintro s c fs' ⟨⟨a, f, cR, hc, rfl, hfx, hfb, hst, hQ⟩, hu⟩
  rcases hQ with ⟨-, c0', hrun, he, hn, hd, hpc, σ, hA, hFm, hJ⟩ | hQ
  · have hσ : f.σs = [] := by
      cases hst with
      | ret _ hσ _ => exact hσ
    exact ⟨⟨(f, c0'), hrun, hfx, hfb⟩, ⟨he, hn, hd, hpc, σ, hA, hFm, by rw [hu]; rfl,
      heldTail_of_frame hc hσ hfx hfb hbx, cR, .single hst, hJ⟩, rfl⟩
  · exact hQ.elim

variable [Kraken.Executable.ValidLayout exe]

/-- **`main`'s return tail after a plain call to `ExitC2SLFV`**
(`mainTailX_segC`; the held pair reads its value back at every control,
`hrd`, e.g. the frame returning its result). -/
theorem mainTailX_segCV (hp : ProgNoS ZBad p)
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL cells okPc ph lab (Int64.ofBitVec ra)) pc ((retDirs lw).zip zs))
    (hpos : PosOff cells lab (Int64.ofBitVec ra))
    {s : Spike.Lib.Form.SEnv} {a : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt s a = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    {fs : List TermRun.Frame} {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', []))
    (hx : ∀ f, fs = [f] → ∃ t r, Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]) ∧
      ∃ k, rsOf fr r = some k ∧ R.Off k)
    (hW₀ : ∀ st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize st c fs → W st c fs)
    {Ab : FragS isa} (hrd : ∀ c, HeldRd c fs) :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRN p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp
        tp))).at fs)
      (ExitC2SLFV p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have he := (ret_edgeSL (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0') (pc := pc)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hl hn hz (_root_.Executable.labels exe).label
    hsa hg hsc hlit hera).tp tp
  have hok := he.2.1
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st pc ((retDirs lw).zip zs) :=
    SubCd.cdOf (fun pc' blk h => by
      have h' := CdCL.toCdC h
      rw [← hI.labOk] at h'
      exact cdOf_cdC hI.lays hI.endOk pc' blk h') hcd
  let n := heldRN p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp tp)
  have hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot := fun _ _ ⟨_, _, _, ⟨⟨_, hfj, _⟩, _⟩⟩ => hfj
  have hS := blkW_sfacts_ret2 (lbl := lbl) (n := n) hI hf h1 hR hR8 hlo hhi hl8 hh8 hsub hfit hFO rfl hfj hl hn
    hz (hcd.mono fun _ _ h => CdCL.toCdC h)
  have hab := retHeld_hab (F := F) (n := n) hI hpr habt hl hz hcd hok hR hlo hhi
    (fun _ _ ⟨_, _, _, ⟨hJ, _⟩⟩ => retDirs_pc_bodyN2 hf h1 hl hn hz lab hJ) hpos
  have hW := retHeld_hW (Λ := Λ) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize)
    (n := n) (fs := fs) hp hl
    hcode hok hR hlo hhi hS (fun _ _ h => h.1) (fun _ _ ⟨hH, _, hr', hJ, _⟩ => retSlot_bodyN2 hx hH hr' hJ) hab
  exact (SegWS.liftS fs (((he.heldRN fs).seg hF hR hlo hhi hcode hW).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) hW₀).mono_post
    fun _ c _ ⟨h, hfs⟩ => hfs ▸ exitC2SLFV_of_heldRN hr h (hrd c)

/-- **`main`'s return tail after an output call to `ExitC2SLFV`**
(`mainTailX_segP`; the held control reads nothing). -/
theorem mainTailX_segPV (hp : ProgNoS ZBad p) {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL cells okPc ph lab (Int64.ofBitVec ra)) pc ((retDirs lw).zip zs))
    (hpos : PosOff cells lab (Int64.ofBitVec ra))
    {s : Spike.Lib.Form.SEnv} {a : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt s a = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    {fs : List TermRun.Frame} {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', []))
    (hW₀ : ∀ st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize st c fs → W st c fs)
    {Ab : FragS isa} :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRNU p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp
        tp))).at fs)
      (ExitC2SLFV p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have he := (ret_edgeSL (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0') (pc := pc)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 hl hn hz (_root_.Executable.labels exe).label
    hsa hg hsc hlit hera).tp tp
  have hok := he.2.1
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st pc ((retDirs lw).zip zs) :=
    SubCd.cdOf (fun pc' blk h => by
      have h' := CdCL.toCdC h
      rw [← hI.labOk] at h'
      exact cdOf_cdC hI.lays hI.endOk pc' blk h') hcd
  let n := heldRNU p fs ((bodyN2 p lbl lsize i fr fp ra c0' pc (.ret a) s lits cs bufs).withTp tp)
  have hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot := fun _ _ ⟨_, _, _, _, ⟨⟨_, hfj, _⟩, _⟩⟩ => hfj
  have hS := blkW_sfacts_ret2 (lbl := lbl) (n := n) hI hf h1 hR hR8 hlo hhi hl8 hh8 hsub hfit hFO rfl hfj hl hn
    hz (hcd.mono fun _ _ h => CdCL.toCdC h)
  have hab := retHeld_hab (F := F) (n := n) hI hpr habt hl hz hcd hok hR hlo hhi
    (fun _ _ ⟨_, _, _, _, ⟨hJ, _⟩⟩ => retDirs_pc_bodyN2 hf h1 hl hn hz lab hJ) hpos
  have hW := blkW_heldTail (Λ := Λ) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) hp hS
    (fun _ _ h => h.2.1)
    (blkW_heldS hab (blkW_ret0_nil (lbl := lbl) fun _ _ h => h.1) (blkW_noWr' hcode hok hR hlo hhi)
      (blkW_noSys' hcode hok))
  exact (SegWS.liftS fs (((he.heldRNU fs).seg hF hR hlo hhi hcode hW).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) hW₀).mono_post
    fun _ _ _ ⟨h, hfs⟩ => hfs ▸ exitC2SLFV_of_heldRNU hr h

/-- **`main`'s held return tail to `ExitC2SLFV` at `main`'s code**
(`heldTailCX_main`): after a plain call the tail returns the call's result
(a literal there excluded by `hlitE`: at a literal tail the call is to an
extern), the pair reading it back; after an output call the held control
reads nothing (`print`'s `ret ()`). -/
theorem heldTailCX_mainV (hp : ProgNoS ZBad p)
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCdL : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hpos : PosOff cells lab (Int64.ofBitVec ra))
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64} {ty : Ty}
    (hcallH : CallC2H p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T Ab (RetLk ty))
    (hprintH : PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T Ab)
    (hW₀ : ∀ st c fs, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.X64.WriteAb.Ab lab) lbl lsize st c fs →
      W st c fs)
    (hlitE : ∀ x g is a ts k, T (.let_ x (.call g is a ts) (.ret (.lit k))) →
      lcx.externs.find? (·.1 == g) = none → False) :
    HeldTailCX p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T (fun _ => True) (RetLk ty)
      (fun c0 => ExitC2SLFV p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  intro c0 pc kk env n x g is a ts b lits cs bufs l k r hG hr hfr hcode hbl hWk hL hC hX hbx
  have hh0 := walk2_head hWk
  have hL0 := (hL (.let_ x (.call g is a ts) (.ret b), lits) (by simp [Scc.Lower.litWalk2])).1
  have hhi0 : (0 : Int) ≤ R.hi := by omega
  rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
      | ⟨xe, dg, t, bo, o, m, cw, r', hx, hdg, hrt, ha, hr', rfl⟩
  · have hbv : b = .var x := by
      rcases hbx with ⟨k', rfl⟩ | h
      · exact (hlitE x g is a ts k' (hWk _ (by rw [lowerEnvs2]; exact List.Mem.head _)).2.1 hx).elim
      · exact h
    obtain ⟨tb, ws, hab, rfl⟩ := lowerC2_ret_inv hr'
    obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append _ [_] kk pc).1 hcode
    have hW' := walk2_tail_call hfrm hx hdg hrt ha hWk
    have hh := walk2_head hW'
    have hlb := hL (.ret b, (x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits)
      (by simp [Scc.Lower.litWalk2])
    rcases hrest with hu | ⟨l1, zs, hE, hz, hc⟩
    · cases hu
    obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
    rw [hl] at hz hc
    obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hh.2.2.2.2.1 hab
    refine (SegWS.seq_left (hcallH c0 pc pc' kk kk' env n x g is a ts (.ret b) t w lits cs bufs hG hh0.2.1 hfr hL0
        hh0.2.2.2.1 hh0.2.2.2.2.1 hC ⟨hx, dg, hdg, hrt⟩ ha hi
        (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx _ _ _ _ _ _ hr' y hy)) hh.1 hh.2.2.2.2.2
        ⟨l, k, _, hr, hcode, hbl, fun q hq =>
          ⟨(hWk q hq).1, (hWk q hq).2.1, (hWk q hq).2.2.2.1, (hWk q hq).2.2.2.2.1, (hWk q hq).2.2.2.2.2⟩, hL, hC,
          hX⟩)
      (held_segXQ hbx fun f c0' hrun hfx hfb => ?_)).mono_post fun s c fs' h => h.elim id .inr
    exact mainTailX_segCV hp hI hpr habt hf h1 hF hR hR8 hlo hhi hl8 hh8 hsub hfit hFO hlw hn hz
      (SubCd.whole (hCdL _ _ hc)) hpos hsa hpl (hlb.1.1 b (by simp [headAtoms]))
      (fun k hk => hlb.1.2.2.2 k (by subst hk; simp [headAtoms])) (hlb.2.2 b rfl) hrun
      (hx_held hf hi hlo hhi0 fun f' h => by cases h; exact hfx) (fun st c => hW₀ st c _)
      fun _ => .inr fun f' hf' => by rw [List.mem_singleton] at hf'; subst hf'; rw [hfb, hfx, hbv]
  · obtain ⟨tb, ws, hab, rfl⟩ := lowerC2_ret_inv hr'
    obtain ⟨kk', pc', hi, hrest⟩ := (codeC2_append _ _ kk pc).1 hcode
    have hW' := walk2_tail_print hx hdg hrt ha hWk
    have hh := walk2_head hW'
    have hlb := hL (.ret b, (x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits)
      (by simp [Scc.Lower.litWalk2])
    rcases hrest with hu | ⟨l1, zs, hE, hz, hc⟩
    · cases hu
    obtain ⟨hn, lw, hlw, hl⟩ := emits_retN hE
    rw [hl] at hz hc
    obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hh.2.2.2.2.1 hab
    refine (SegWS.seq_left (hprintH c0 pc pc' kk kk' env n x g is a ts (.ret b) xe dg t bo o m cw lits cs bufs hG
        hh0.2.1 hfr hL0 hh0.2.2.2.1 hh0.2.2.2.2.1 hC
        (by
          rw [← argShape_of_find hdg]
          exact (hL (.let_ x (.call g is a ts) (.ret b), lits) (by simp [Scc.Lower.litWalk2])).2.1 x g is a ts _ rfl)
        hx hdg hrt ha hi (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx _ _ _ _ _ _ hr' y hy)) hh.1
        hh.2.2.2.2.2)
      (held_segXUQ hbx fun f c0' hrun hfx hfb => ?_)).mono_post fun s c fs' h => h.elim id .inr
    exact mainTailX_segPV hp hI hpr habt hf h1 hF hR hR8 hlo hhi hl8 hh8 hsub hfit hFO hlw hn hz
      (SubCd.whole (hCdL _ _ hc)) hpos hsa hpl (hlb.1.1 b (by simp [headAtoms]))
      (fun k hk => hlb.1.2.2.2 k (by subst hk; simp [headAtoms])) (hlb.2.2 b rfl) hrun fun st c => hW₀ st c _

/-! ## `main`'s call at `UPostRF ∧ Q` -/

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)}
  {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **A held function's segment at a context to `ExitC2SLFV`**
(`CalleePre2.segH` at the held tails' exits `ExitC2SLFV`, e.g.
`heldTailCX_mainV`). -/
theorem CalleePre2.segHV {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    {c : FnCode2 exe cells endPc RaOk Cd i T d} {R : Region} {F : MachineData → Prop}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa} {J : AS → Ctl → Prop} {c0 : Ctl}
    (h : CalleePre2 W K p lbl lsize ms CxOk c R F [] fp ra tp G0 Ab J c0)
    (hcall : CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp [] G0 i T Ab
      (RetLk d.retTy))
    (hlane : LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp [] G0 i T Ab)
    (hbuf : NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp [] G0 i T Ab
      (RetLk d.retTy))
    (hprint : PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp [] G0 i T Ab)
    (hheld : HeldTailCX p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR R) F W K ms fp ra tp [] G0 i T
      (fun _ => True) (RetLk d.retTy) (fun c0 => ExitC2SLFV p lbl exe endPc (rbR R) F fp ra tp c0 [] d.retTy Ab))
    (hok : Scc.Lower.heldRetOk d.body = true) (hT : ∀ t, T t → ContNR t) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label c.fn, ⟨0, []⟩, J⟩).at [])
      (ExitC2SLFV p lbl exe endPc (rbR R) F fp ra tp c0 [] d.retTy Ab) := by
  obtain ⟨hF', hR', hlo', hhi'⟩ := rbR_facts h.hF h.hR h.hlo h.hhi
  have hCd := c.hCd ra h.hra
  have hW₀ : ∀ s c', (fun s c => W s c []) s c' → W s c' [] := fun _ _ h => h
  exact (SegWS.liftS [] (proSeg2 c h.hF h.hR h.hlo (by have := h.hhi; omega) h.hpro h.hedge) hW₀).seq
    (body2_segS_ofXH h.hG0 c.hfrm (fun _ _ hr => ExitC2SLFV.trans hr) (fun _ _ _ _ h => .inr h) hcall hlane hbuf
      hprint (addC2_ofQ (Q := fun t => ([] : List TermRun.Frame) = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀
        h.hW h.hWp (ContNR.qAdd hT) h.hab c.lcx tp)
      (subC2_ofQ (Q := fun t => ([] : List TermRun.Frame) = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀
        h.hW h.hWp (ContNR.qSub hT) c.lcx tp)
      (pureMv2_of c.lcx tp) (splitMv2_of c.lcx tp) (unpackMv2_of c.lcx tp)
      (ifC2_ofQ (Q := fun t => ([] : List TermRun.Frame) = [] → ∀ a, t ≠ .ret a)
        c.hf c.h1 hF' hR' hlo' hhi' hCd hW₀
        h.hW (ContNR.qIf hT) c.lcx tp) hheld
      d.body c.env 0 "entry" 0 c.r c.kk _ c.lits [] [] c.hr c.hfr (c.hcode ra h.hra) (c.hbl ra h.hra)
      (fun q hq => have h := c.hWk q hq; ⟨h.1, h.2.1, trivial, h.2.2⟩)
      (fun q hq => ⟨c.hlit q hq, c.hcallL q hq, fun a ha => c.hretL a q.2 (by rw [← ha]; exact hq)⟩)
      c.hcnt c.hxchg hok c0 h.hg0)

omit [Kraken.Executable.ValidLayout exe] in
/-- **The user `main` after a setup block at depth, from its exits held at
pairs reading their value back** (`mainCallWSF_of_exitC2SLF` at
`ExitC2SLFV`): `MainCallWSF` at `UPostRF ∧ Q`, `Q` from the held pair's
facts and its `UPostRF` (`hQ`, e.g. `heldCtlV`). -/
theorem mainCallWSF_of_exitC2SLFV {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64}
    {Q : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hQ : ∀ c fs v, HeldTail c fs → HeldRd c fs → UPostRF p lbl c fs v → Q c fs v)
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ra → g.tp = tp → (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (Ab : FragS isa) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F fn ZU Pre g)).at [])
          (ExitC2SLFV p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' g.fp g.ra tp c0' []
            .int Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre
      (fun c fs v => UPostRF p lbl c fs v ∧ Q c fs v) ra tp := by
  intro F' hR0 hF' hFF g hra htp
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uNM])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hF' hFF g hra htp hbase
  refine (SegWS.seq_left (Q := Ab)
      (E := Spike.Lib.X64.Rt.NxF exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
        (fun c fs v => UPostRF p lbl c fs v ∧ Q c fs v) g)
      (h1.mono_post fun s c fs h => ?_) hAb).mono_post fun s c fs h => ?_
  · rcases h with ⟨⟨c1, hr, c2, -, hA⟩ | hF, hH, hrd⟩ | h
    · obtain ⟨he, hn, hdc, hpc, σ, hA', hD, hU, hJ⟩ := uPostRF_ret hbase hr hA
      exact .inr ⟨he, hn, hdc, hpc, σ, hA', hD, ⟨hU, hQ _ _ _ hH hrd hU⟩, hJ⟩
    · exact hF.elim
    · exact .inl h
  · exact h.elim False.elim id

/-- **The user `main` after the setup block, its paths held, at
`UPostRF ∧ Q`** (`mainCallWSF_ofHeld` at the held tails' exits
`ExitC2SLFV`, e.g. `heldTailCX_mainV`; `Q` from the held pair's facts,
`hQ`). -/
theorem mainCallWSF_ofHeldV {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (c : FnCode2 exe cells endPc RaOk Cd i T d) (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hT : ∀ t, T t → ContNR t)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64}
    {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64} (hfn : fn = c.fn)
    {Q : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hQ : ∀ c fs v, HeldTail c fs → HeldRd c fs → UPostRF p lbl c fs v → Q c fs v)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ra → g.tp = tp → (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp → ∀ cP : Ctl,
      (∃ rs, Pre cP rs) →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa) (c0' : Ctl),
        CalleePre2 W K p lbl lsize ms CxOk c (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F fn ZU
            (fun c rs => Pre c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8))
          F' W K ms g.fp g.ra tp [] G0 i T Ab (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8))
          F' W K ms g.fp g.ra tp [] G0 i T Ab ∧
        NewBufC p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc
          (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' W K ms g.fp g.ra tp [] G0 i T Ab (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc
          (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' W K ms g.fp g.ra tp [] G0 i T Ab ∧
        HeldTailCX p lbl lsize c.lcx c.fr (Cd g.ra) (c.Bl g.ra) exe endPc
          (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' W K ms g.fp g.ra tp [] G0 i T (fun _ => True)
          (RetLk d.retTy) (fun c0 => ExitC2SLFV p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
            g.fp g.ra tp c0 [] d.retTy Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre
      (fun c fs v => UPostRF p lbl c fs v ∧ Q c fs v) ra tp :=
  MainCallWSF.ofCtl fun cP hcP => mainCallWSF_of_exitC2SLFV hQ fun F' hR0 hF' hFF g hra htp hbase => by
    obtain ⟨G0, Ab, c0', hP, hcall, hlane, hbuf, hprint, hheld, hAb⟩ := hpre F' hR0 hF' hFF g hra htp hbase cP hcP
    have H := hP.segHV hcall hlane hbuf hprint hheld hok hT
    rw [hint] at H
    subst hfn
    exact ⟨Ab, c0', H, hAb⟩

end Call

/-- **No output call with one index without the extern**: at a call of
`print` at a `TailOf` a compiled block's body of an `Accepted2` program,
`print` not among the frontend's externs, the call has no indices
(`body2`'s check of an ordinary callee). -/
theorem heldLit_print {p : Prog} (hacc : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {x : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call "print" is a ts) e') d.body)
    (hn : (Scc.Frontend.externs p).find? (·.1 == "print") = none) : is = [] := by
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 (List.mem_of_getElem? hd)
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hp⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, hext, -⟩ := body2_of_compiled hacc hp hdc'
  have hpr : Scc.Lower.hasPrint p = false := by
    cases hh : Scc.Lower.hasPrint p
    · rfl
    · have := externs_print hh
      rw [hn] at this; cases this
  obtain ⟨_, _, _, hb'⟩ := body2_tail ht hb
  simp only [Scc.Lower.body2, Bool.and_eq_true] at hb'
  have hc := hb'.1.1
  rw [hext, hpr] at hc
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, Bool.and_eq_true] at hc
  simpa using hc.1.2

section Place

open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

include hp in
/-- **`main`'s call after the setup block from the placement check, its
paths held, at `UPostRF ∧ Q`, at any code facts of the check's output**
(the body of `mainCallWSF_ofPlaceOKHV` at `c` with the return address's
phase and `main`'s code as `fnCode2OfP`'s, any immediates `im`, e.g.
`fnCode2OfPMe`'s `imms2Me`): its prologue's facts `hcPro` and lowering
context `hlcx`; the rest as `mainCallWSF_ofPlaceOKHV`. -/
theorem mainCallWSF_ofPlaceOKHVC {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {im : Expr → String → Nat → Option Nat}
    (c : FnCode2 (LY).exe (LY).prog (LY).endPc
      (fun ra => Spike.Lib.X64.PhRec.ph LY (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY ((LY).lab raL).toBitVec.toNat)
      (fun ra => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra))
      im (TailAt2 p j) d)
    (hcPro : ProOK LY d c)
    (hlcx : c.lcx = lcx2 p cfg.layout.obj d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body →
      g = "print" ∧ is.length = 1)
    {Q : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hQ : ∀ c fs v, HeldTail c fs → HeldRd c fs → UPostRF p lbl c fs v → Q c fs v) {sw : Nat}
    (hc : rtCodeOkS OP (setupMC sw) = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = c.fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL c.fr)))
    {ty : Ty} {c0 : Ctl} {x0 : BitVec 64}
    (hsT : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 5)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (hE : ∀ x f a e, c0.term = .let_ x (.call f [] a []) e → ∀ b, e ≠ .ret b)
    (hfo : ∀ c regs, SetupArgs (SPostC p lbl ty c0) sw x0 c regs → FrOk2 c [])
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ((LY).lab (setupMC sw).sp1).toBitVec → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa) (c0' : Ctl),
        CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk c rS
          (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU
            (fun c rs => SetupArgs (SPostC p lbl ty c0) sw x0 c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize c.lcx c.fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          (c.Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 im (TailAt2 p j) Ab ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF
      (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (SetupArgs (SPostC p lbl ty c0) sw x0) (fun c fs v => UPostRF p lbl c fs v ∧ Q c fs v)
      ((LY).lab (setupMC sw).sp1).toBitVec tp := by
  refine mainCallWSF_ofHeldV (lsize := lsize) (CxOk := CxOk) c hint hok
    (fun _ ht => contNR_tailAt2 hd hok ht) hfn hQ
    fun F' hR0 hF' hFF g hra htp hbase cP hcP => ?_
  obtain ⟨G0, Ab, c0', hP, hcall, hlane, hbuf, hprint, hcallH, hprintH, hAb⟩ :=
    hpre F' hR0 hF' hFF g hra htp hbase cP (hfo _ _ hcP.choose_spec)
  have hP2 := hP.toPre (by rw [hra]; exact RaMain.raOk_main h _ hc)
    (hpro_main_ofPlaceOK h c hcPro hL (fun _ _ h => h)
      hP.hR hP.hR8 hP.hlo (by have := hP.hhi; omega) hP.hl hP.hh (htp ▸ hmr)
      (fun m hm => htp ▸ hun m (hFF m hm).1) hsub hfit hP.hFO hpN
      (fun c regs hc' => hPl_setupArgs hsT hw hsw hme Λw c regs hc'.1)
      (fun c regs hc' => hnr_setupArgs hE c regs hc'.1) (fun c regs hc' => hfo c regs hc'.1))
  refine ⟨G0, Ab, c0', hP2, hcall, hlane, hbuf, hprint, ?_, hAb⟩
  have hlo := hP.hlo
  have hhi := hP.hhi
  obtain ⟨hF2, hR2, hlo2, hhi2⟩ := rbR_facts hP.hF hP.hR hlo hhi
  have hb := rbR_base hP.hR (by omega) (by omega)
  have hR8 := hP.hR8
  have hl := hP.hl
  have hh := hP.hh
  have hR8' : (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)).base.toNat % 8 = 0 := by omega
  exact heldTailCX_mainV hpN (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h _) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) c.hf c.h1 hF2 hR2 hR8' hlo2
    hhi2 (by have e : (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)).lo
          = (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).lo + 8 := rfl; omega)
    (by have e : (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)).hi
          = (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).hi + 8 := rfl; omega) hsub hfit
    (fun m hm => stackOff_rbR hP.hR (by omega) (by omega) (hP.hFO m hm)) (fun _ _ h => CdCLE.toCdCL h)
    (by rw [hra]; exact posOff_mainRetS (Spike.Lib.X64.Rt.mainSIn_of_okS hc))
    c.hfrm hcallH hprintH (fun _ _ _ h => h) fun x g is a ts k hT hn => by
      obtain ⟨rfl, his⟩ := hlitP x g is a ts k (hT d hd)
      rw [hlcx] at hn
      rw [heldLit_print hp hd (hT d hd) hn] at his
      cases his

/-- **`main`'s call after the setup block from the placement check, its
paths held, at `UPostRF ∧ Q`** (`mainCallWSF_ofPlaceOKH` through
`mainCallWSF_ofHeldV` and `heldTailCX_mainV`): a literal tail only after
`print` with its one index (`hlitP`), so not after a plain call (with the
extern absent `print` takes no index, `heldLit_print`); `Q` from the held
pair's facts (`hQ`, e.g. `heldCtlV`). -/
theorem mainCallWSF_ofPlaceOKHV {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Λw : Scc.Sem.Layout} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {rS : Range} {ar : Arena} {J : InvS}
    {Dt : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {CxOk : Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isa → Prop}
    (hint : d.retTy = .int) (hok : Scc.Lower.heldRetOk d.body = true)
    (hlitP : ∀ x g is a ts k, TailOf (.let_ x (.call g is a ts) (.ret (.lit k))) d.body →
      g = "print" ∧ is.length = 1)
    {Q : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hQ : ∀ c fs v, HeldTail c fs → HeldRd c fs → UPostRF p lbl c fs v → Q c fs v) {sw : Nat}
    (hc : rtCodeOkS OP (setupMC sw) = true)
    {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {tp : UInt64}
    (hfn : fn = (fnCode2OfP hp h j d hd).fn)
    (hL : PosOff OP (LY).lab ((LY).lab (proL (fnCode2OfP hp h j d hd).fr)))
    {ty : Ty} {c0 : Ctl} {x0 : BitVec 64}
    (hsT : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 5)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (hE : ∀ x f a e, c0.term = .let_ x (.call f [] a []) e → ∀ b, e ≠ .ret b)
    (hfo : ∀ c regs, SetupArgs (SPostC p lbl ty c0) sw x0 c regs → FrOk2 c [])
    (hmr : Scc.Sem.Kernel.mapped (K0 Λw) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λw.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hpN : ProgNoS ZBad p)
    (hpre : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : WcG, g.ra = ((LY).lab (setupMC sw).sp1).toBitVec → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp → ∀ cP : Ctl,
      FrOk2 cP [] →
      ∃ (G0 : Ctl → Prop) (Ab : FragS isa) (c0' : Ctl),
        CalleePre2R (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl lsize ms CxOk (fnCode2OfP hp h j d hd) rS
          (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra tp G0 Ab
          (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (LY).exe).label (ms []) F fn ZU
            (fun c rs => SetupArgs (SPostC p lbl ty c0) sw x0 c rs ∧ c = cP) g).J c0' ∧
        CallC2 p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        LaneC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        NewBufC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallC p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        CallC2H p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab
          (RetLk d.retTy) ∧
        PrintCallCH p lbl lsize (fnCode2OfP hp h j d hd).lcx (fnCode2OfP hp h j d hd).fr
          (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab (Int64.ofBitVec g.ra))
          ((fnCode2OfP hp h j d hd).Bl g.ra) (LY).exe (LY).endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F'
          (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) ms g.fp g.ra tp [] G0 (Scc.Lower.imms2Of p) (TailAt2 p j) Ab ∧
        SegWS (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
            (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
          (Spike.Lib.X64.PhRec.K LY rS) p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF
      (fun s c fs => W2 Λw (Spike.Lib.X64.PhRec.μ LY) p rd G (Spike.Lib.X64.PhRec.own LY) rS
        (Spike.Lib.X64.PhRec.Tk LY) ar J Dt (Spike.Lib.X64.WriteAb.Ab (LY).lab) lbl lsize s c fs)
      (Spike.Lib.X64.PhRec.K LY rS) p lbl ms (LY).exe (LY).endPc R F fn Z D ZU
      (SetupArgs (SPostC p lbl ty c0) sw x0) (fun c fs v => UPostRF p lbl c fs v ∧ Q c fs v)
      ((LY).lab (setupMC sw).sp1).toBitVec tp :=
  mainCallWSF_ofPlaceOKHVC hp h hd (fnCode2OfP hp h j d hd) (fnCode2OfP_spec hp h j d hd).2.2
    (fnCode2OfP_spec hp h j d hd).1 hint hok hlitP hQ hc hfn hL hsT hw hsw hme hE hfo hmr hun hsub hfit hpN hpre

end Place

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.heldCtlV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.heldCtlV

/-- info: 'Spike.Lib.LowerX64.mainTailX_segCV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainTailX_segCV

/-- info: 'Spike.Lib.LowerX64.mainTailX_segPV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainTailX_segPV

/-- info: 'Spike.Lib.LowerX64.heldTailCX_mainV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.heldTailCX_mainV

/-- info: 'Spike.Lib.LowerX64.CalleePre2.segHV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CalleePre2.segHV

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_of_exitC2SLFV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_of_exitC2SLFV

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofHeldV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofHeldV

/-- info: 'Spike.Lib.LowerX64.heldLit_print' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.heldLit_print

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHV

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHVC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofPlaceOKHVC
