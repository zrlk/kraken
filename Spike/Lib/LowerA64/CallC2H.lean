/-
**A plain call of an `Accepted2` body held at the callee's return**
(AArch64; the twin of `Spike/Lib/LowerX64/CallC2H.lean`): `callC2_of`
(`CallC2.lean`) with the source's `ret` not taken. The machine's return
and the result's store `str x0, [sp, #o]` run with the source at the
callee's exit control at `f :: fs`; the segment ends at `ContC` behind
that `ret` (`HeldC`).

- `heldND`: a node held one frame above `fs`, its invariant at the
  control the held `ret` steps to;
- `calleeC_seg2H`: `calleeC_seg2` held (`call_ndSFH`), ending at the held
  return node;
- `resC_seg2H`, `resC_segS2H`: the result's store between held nodes, `W`
  at the held pairs from `hWH` (the store's node only);
- `callC2H_of`: `CallC2H` from `callC2_of`'s premises and `hWH`.
-/
import Spike.Lib.LowerA64.HeldC
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.A64CallSAH

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv sevalAt lookupS WordPl SRep opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (CallerCells setXReg_TPIDR)
open Scc.Lower.Inv (regName labName atomV)
open Spike.Lib.LowerCall (Callee)

set_option linter.unusedSimpArgs false

/-- **A node held one frame above `fs`**: `n` at the control the held
source's `ret` (at frames `f :: fs`, `f` the call's frame: its result
variable `x`, its continuation `e`) steps to. -/
def heldND (p : Prog) (f : TermRun.Frame) (fs : List TermRun.Frame) (x : String) (e : Expr) (n : ND) : ND :=
  ⟨n.pc, n.o, fun σ c => f.x = x ∧ f.body = e ∧ ∃ a cR, c.term = .ret a ∧ FrameStep p (c, f :: fs) (cR, fs) ∧
    n.J σ cR⟩

section Call


variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The result's store, held -/

/-- **The result's store into `r%n` with the source held** (`resC_seg2`
between `heldND`s): the store takes no source step, so the held `ret` and
its landing are carried; `W₀` at the held pairs of the store's node from
`hWH`, no outside move there from `hWB`. -/
theorem resC_seg2H {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms0 : MemSide isaLSE2} {W₀ W₁ : Frag isaLSE2} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW W₁ K exe endPc R F n blk)
    {d : Scc.IR.Reg} {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) {off : Int}
    (hoff : rsOf cx d = some off) {pcR : Int64} (hc : Cd pcR (directives ls)) {x : String} {e : Expr}
    {s : SEnv}
    {f : TermRun.Frame}
    (hWH : ∀ st c a cR, c.term = .ret a → FrameStep p (c, f :: fs) (cR, fs) →
      At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off) st cR → W₀ st c) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (heldND p f fs x e (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off)))
      (At exe endPc R F (heldND p f fs x e (csN2 lbl cx fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs))
        (pcR + Int64.ofNat (4 * (directives ls).length)) e s fun _ => True))) := by
  have hok := okBlk_resStore hf h1 h16 hs
  have hW := hWB ⟨pcR, oF cx, (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off).J⟩ _ (SubCd.whole hc) rfl
    (fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (.inr ⟨d, ls, hs, rfl⟩)
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  rw [setReg_eq hf (by omega) ho] at hs
  cases ok_inj hs
  have hoo : off = o - cx.frame := by
    simp only [rsOf, ho, Option.some.injEq] at hoff; exact hoff.symm
  subst hoo
  have hds : directives [ins (.STR (rz .W64 .X0) ⟨spW64, .imm ⟨i64 o, none⟩⟩)] =
      [spStr .X0 (Int64.ofInt o)] := rfl
  rw [hds] at hc hok hW ⊢
  refine seg_blk1 (lo := -(cx.frame : Int)) hF hR hal hlo hhi (hCd _ _ hc) ?_ (by simp) hok
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  · intro st σ c he hn hdc hpc hA hF0 hJ k hk m hAm hD
    obtain ⟨-, -, a, cR, ht, hst, hJR⟩ := hJ
    have hk0 : k = 0 := by simpa using hk
    subst hk0
    refine ⟨hWH _ c a cR ht hst ?_, (hW st σ cR he hn hdc hpc hA hF0 hJR 0 hk m hAm hD).2⟩
    exact ⟨he, hn, hdc, by simp [heldND, retCN2], σ, by simpa [arun, heldND] using hAm, hF _ _ hF0 hD, hJR⟩
  · show Hit _ (arun _ _ ⟨pcR, ⟨-(cx.frame : Int), []⟩, σ⟩) c
    rw [arun_spStr1, ofs_eq hf h1 ho]
    obtain ⟨hfx, hfb, a, cR, ht, hst, hj, hq, hfj, hr, htp⟩ := hJ
    exact ⟨rfl, so_le_refl _ rfl, hfx, hfb, a, cR, ht, hst, hj, hq, frJ_upd hfj (ofs_le hf ho) _, hr, htp, trivial⟩

/-- **The result's store with the source held, at any callee frame**
(`resC_seg2H` lifted to frames `f :: fs`, `W` at the store's held pairs
from `hWH`). -/
theorem resC_segS2H {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {W₁ : Frag isaLSE2}
    {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List Directive → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW W₁ K exe endPc R F n blk)
    {d : Scc.IR.Reg} {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) {off : Int}
    (hoff : rsOf cx d = some off) {pcR : Int64} (hc : Cd pcR (directives ls)) {x : String} {e : Expr}
    {s : SEnv}
    (hWH : ∀ f st c a cR, c.term = .ret a → FrameStep p (c, f :: fs) (cR, fs) →
      At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off) st cR → W st c (f :: fs)) :
    SegWS W K p lbl ms
      (fun st c fs' => ∃ f, (At exe endPc R F (heldND p f fs x e (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off))).at
        (f :: fs) st c fs')
      (fun st c fs' => ∃ f, (At exe endPc R F (heldND p f fs x e (csN2 lbl cx fp ra tp Q
        (fun c => FrameRunM p (c0, fs) (c, fs)) (pcR + Int64.ofNat (4 * (directives ls).length)) e s
        fun _ => True))).at (f :: fs) st c fs') :=
  SegWS.exists_pre fun f =>
    (SegWS.liftS (W := W) (f :: fs) (resC_seg2H (p := p) (lbl := lbl) (K := K) (ms0 := ms (f :: fs))
      (W₀ := fun st c => W st c (f :: fs)) (fp := fp) (ra := ra) (tp := tp) (Q := Q) (f := f)
      hf h1 h16 hF hR hal hlo hhi hCd hG hWB hs hoff hc (hWH f)) fun _ _ h => h).mono_post
      fun _ _ _ h => ⟨f, h⟩

/-! ## The callee, held -/

/-- **The callee inside a plain call held at its return** (`calleeC_seg2`
by `call_ndSFH`): the segment ends at the return node held one frame above
`fs` (`heldND`), the source at the callee's exit control. -/
theorem calleeC_seg2H {cx : FnCtx} (hf : FrameOk cx) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isaLSE2}
    {W : FragS isaLSE2} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2 lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab))
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf cx (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {k : Nat} (hb : Bl pcB (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hlb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hsite : ∀ q : CallG, q.ra = (pcB + 4).toBitVec →
      CallSite2 lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q) :
    SegWS W K p lbl ms ((At exe endPc R F (csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callP cx w (pcB + 4)))).at fs)
      (fun s c fs' => (∃ f, (At exe endPc R F (heldND p f fs x e (retCN2 p lbl cx fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off))).at (f :: fs) s c
          fs') ∨ Ab s c fs') := by
  have h16' := frame_ge16 hf
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] a []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
  have hsa := sevalAt_ofEnv2_one hg ha
  -- the frame's cells are kept by the callee
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf cx r = some k' →
      R.Off k' ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (k' - -(cx.frame : Int)) := by
    intro r k' hk'
    unfold rsOf at hk'
    split at hk'
    · rename_i o ho
      cases hk'
      obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
      exact frame_outC hD0 hlo hhi (by omega) (by omega) (by omega)
    · cases hk'
  have houtA : R.Off (-16) ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (-16 - -(cx.frame : Int)) :=
    frame_outC hD0 hlo hhi (by decide) (by omega) (by omega)
  have houtB : R.Off (-8) ∧ ¬ (R.callee (-(cx.frame : Int)) (-D) 0).Off (-8 - -(cx.frame : Int)) :=
    frame_outC hD0 hlo hhi (by decide) (by omega) (by omega)
  refine (call_ndSFH (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := csN2 lbl cx fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
      ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv2 env) (callP cx w (pcB + 4)))
    (γ := CallG) (κ' := Ctl) (lo' := -D) (hi' := 0)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN2 p lbl tp fs q frm c0')
    (N := fun f (_ : Unit) => heldND p f fs x e (retCN2 p lbl cx fp ra tp c0 fs
      (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
        (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
      (pcB + 4) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off))
    (E := fun _ (e : Empty) => e.elim)
    (fs := fs) (Ab := Ab) hR hal hF
    (by show R.lo ≤ -(cx.frame : Int) + -D; omega) (by omega)
    (by show -(cx.frame : Int) < R.hi; omega) (Int.le_refl 0)
    (by show (-(cx.frame : Int)) % 16 = 0; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC g dd hfd _ rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    subst hR'eq
    have hra : q.ra = (pcB + 4).toBitVec := by
      obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      rw [← hNe.2.2.1]
      exact hJ.2.2.2.2.2.2
    refine (hcal g q frm F' hFS ?_ ?_ ?_ ?_ (hsite q hra)).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, hcells m hm, mC, σC, c, _, _, hA, hkept, hct, hT, hj, ⟨lits, cs, bufs, hen⟩, hfj, ?_⟩
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
      rw [hj.1] at ht1
      cases ht1
      subst hfr1
      have hne : ∀ y, y ≠ x →
          ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
        intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
      refine ⟨fun y hy hyx => ?_, fun y hy hyx ty pls hl => ?_, fun y kk v hy hl => ?_⟩
      · have := hIt y hy
        rw [ofEnv2_cons hgr] at this
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
      · apply hlb y hy ty pls
        rw [ofEnv2_cons hgr]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using hl
      · apply hIc y kk v
        rw [ofEnv2_cons hgr]
        simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hy] using hl
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨c, x, a, e, hG c hJ.2.2.2.1, hT, hJ.1.1, hct⟩
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      obtain ⟨hj, hen, -, -, -, hP1, -⟩ := hJ
      obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
      have hm1 := NJB.litMask_one (NJB.of_nodeJE (p := p) (B := B) hj hl hbB hmB hS) hsa hsc
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, hev1, hcE1, -⟩ := hct
      rw [hj.1] at ht1
      cases ht1
      obtain ⟨_, ws', hev', -, hwr⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
      rw [hev1] at hev'
      cases hev'
      match ws1, hwr, hev1, hcE1 with
      | [w'], ⟨⟨v, hv, hvr⟩, _⟩, hev1, hcE1 =>
        have hv' : v = q.v.toNat := by
          rw [hP1] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := NumL.one (hl.evalAt' hsc hlit hev1).2 hm1
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · exact ⟨pcB, k, hb, hra⟩
    · rintro s c fs' (⟨rfl, c0', hrun, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩⟩ | hab)
      · exact .inl ⟨⟨c0', ⟨he, hn, hdc, hpc, σ, hA, hD, hrun, hJ⟩, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ta, ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
    exact ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.X0.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, ta, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP2⟩ := hJ
    obtain ⟨hrun, ⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, -, -⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
    have hcE : cE = q.cE := hNe.1
    subst hcE
    have hct' := hct
    obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
    rw [hj.1] at ht1
    cases ht1
    rw [hfd] at hfd1
    cases hfd1
    subst hfr1
    have hRL' : RetL .int c' := by rw [← hretTy]; exact hRL
    obtain ⟨a2, t2, w2, ht2, he2, hnum⟩ := RetL.int hRL'
    rw [hta] at ht2
    cases ht2
    rw [hev'] at he2
    simp only [Option.some.injEq, Prod.mk.injEq] at he2
    obtain ⟨rfl, rfl⟩ := he2
    have hstep : FrameStep p (c', ⟨x, e, c.env, [], dd.retTy⟩ :: fs)
        (⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, fs) := .ret hta rfl hev'
    have hvr' : ValRep lbl w2.val σR.regs.X0.toBitVec.toNat := by
      rw [hregs]; exact hvr 0 (by simp) (by decide)
    refine .inl ⟨(), ?_, ?_, rfl, rfl, _, _, hta, hstep, ?_⟩
    · show pcB + 4 = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec σC.regs.X30.toBitVec
      rw [hP2, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(cx.frame : Int), []⟩ ⟨-(cx.frame : Int) + 0, []⟩ = true
      simp [SO.le]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨rfl, rfl, ?_⟩
        show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
          ((x, dd.retTy, [w2]) :: c.env)
        rw [ofEnv2_cons hgr, hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv2 hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hk' hoff) hne
        exact hsl k' (hout r k' hk').1 (hout r k' hk').2
      · obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
        refine ⟨?_, EnvSmall.cons hS (WordsSmall.isNum hnum), L, sm, B, ?_, hmB⟩
        · show EnvLit _ ((x, dd.retTy, [w2]) :: c.env)
          rw [hop, hretTy]
          refine hl.cons rfl (NumL.of_all fun w hw => ?_)
          simp only [List.mem_singleton] at hw
          subst hw; exact hnum
        · show EnvB _ _ _ L sm lsize ((x, dd.retTy, [w2]) :: c.env)
          rw [hop]
          exact hbB.cons (SliceL.leaf none [w2]) (fun a h => by rcases h with h | h <;> cases h)
            (fun n τ h => by cases h)
      · exact ⟨(hsl _ houtA.1 houtA.2).trans hfj.1, (hsl _ houtB.1 houtB.2).trans hfj.2⟩
      · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
          (hrun.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
      · rw [hregs]; exact htpx
  · rintro s c fs' (⟨fr', h, rfl⟩ | hab)
    · exact .inl ⟨fr', h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩
    · exact .inr hab

/-! ## The call, held -/

/-- **A plain call of an `Accepted2` body held at the callee's return**
(`CallC2H`; `callC2_of` with the source's `ret` not taken): `callC2_of`'s
premises and `hWH`, `W` at the held pairs of the result's store's node
(`retCN2`), the only machine states between the return and `ContC`. -/
theorem callC2H_of {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2} {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {lcx : Scc.Lower.Ctx}
    (hprog : lcx.prog = p) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {D : Int}
    (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - D) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk) (hBl : ∀ pc g k, Bl pc g k → CdOf exe endPc pc [blD g])
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      CallBlk cx blk → BlkW (fun s c => W s c fs) K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) g k, Bl n.pc g k → n.o = oF cx → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW (fun s c => W s c fs) K exe endPc R F n [blD g])
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) → n.o = oF cx →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isaLSE2} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (R.callee (-(cx.frame : Int)) (-D) 0) F' → CalleeF2 p lbl lsize cx R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB k, Bl pcB (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + 4).toBitVec) →
      CallSite2 lcx cx Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (R.callee (-(cx.frame : Int)) (-D) 0) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty
          Ab))
    (hWH : ∀ (c0 : Ctl) (Q : Ctl → Prop) (pcR : Int64) (e : Expr) (s : SEnv) (off : Int) (st : State)
      (c : Ctl) (a : CoreTerm.At) (f : TermRun.Frame) (cR : Ctl), G0 c0 → c.term = .ret a →
      FrameStep p (c, f :: fs) (cR, fs) → At exe endPc R F (retCN2 p lbl cx fp ra tp c0 fs Q pcR e s off) st cR →
      W st c (f :: fs)) :
    CallC2H p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk env n x g is a ts e t w lits cs bufs hc0 hT hfresh hlp hty hg hcnt hcl ha hcode hIt hIc hlb
    hpt
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRunM.ofLocal h fs)
  have hGR : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(cx.frame : Int) := by omega
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  obtain ⟨lw, ls, hw, hs, hcw, hb, hcs, hp⟩ := instsC2_call hcode
  subst hp
  obtain ⟨o, ho, -⟩ := bind_eq_ok hs
  have hoff : rsOf cx (regName "r" n) = some (o - cx.frame) := by simp [rsOf, ho]
  -- `w`'s load into `x0`
  have sA := argC_seg2 (p := p) (lbl := lbl) (lsize := lsize) (K := K) (ms0 := ms fs) (tp := tp) (i := i)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs)
    hf h1 h16 hF hR hal hlo0 hhi hCd hG hWB hw hcw
  -- `bl g`
  have sB := blC_seg2 (p := p) (lbl := lbl) (K := K) (ms0 := ms fs) (tp := tp) (cx := cx)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (Q := fun c => EnvQ lits cs bufs lsize c.env)
    (Rn := LocalRun p c0)
    (P' := callP cx w (pc + Int64.ofNat (4 * (directives lw).length) + 4))
    hF hR hal hlo0 hhi hBl hG hWBl hb fun σ hp => by
      refine ⟨?_, ?_⟩
      · show opdVal (rsOf cx) σ.slot w = some (σ.regs.setXReg .X30 _).X0.toBitVec.toNat
        simpa [Reg64s.setXReg] using hp
      · simp [Reg64s.setXReg]
  have sW := SegWS.liftS (W := W) fs (sA.seq sB) (fun _ _ h => h)
  -- the callee
  have sCal := calleeC_seg2H (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab) (lits := lits) (cs := cs) (bufs := bufs)
    hf h16 hprog hF hR hal hD0 hD8 hlo hhi hG hWC hcal hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hlb
    fun q hq => ⟨c0, pc, _, kk, env, n, x, a, e, t, w, lits, cs, bufs, lw, hc0, hT, hfresh, hlp, hty, hg,
      hcnt, hcl, ha, hcode, hw, hq, hpt⟩
  -- the result's store
  have sR := resC_segS2H (p := p) (lbl := lbl) (x := x) (K := K) (W := W) (ms := ms) (fp := fp)
    (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
    hf h1 h16 hF hR hal hlo0 hhi hCd hGR hWB hs hoff hcs
    fun f st c a' cR ht hst hA => hWH c0 _ _ _ _ _ st c a' f cR hc0 ht hst hA
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨f, ⟨he, hn, hdc, hpc, σ, hA, hD, hfx, hfb, a', cR, ht, hst, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj,
    hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨a', f, cR, ht, rfl, hfx, hfb, hst, .inl ⟨rfl, cR, hr, he, hn, hdc, hpc, σ, hA, hD,
      ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl cR, SlotRepAt.of_nodeJE hj hIt hlb hIc⟩, htp⟩⟩
  · exact .inr hab

end Call

/-- info: 'Spike.Lib.LowerA64.resC_segS2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.resC_segS2H

/-- info: 'Spike.Lib.LowerA64.calleeC_seg2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.calleeC_seg2H

/-- info: 'Spike.Lib.LowerA64.callC2H_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callC2H_of

end Spike.Lib.LowerA64
