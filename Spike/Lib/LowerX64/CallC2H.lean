/-
**A plain call of an `Accepted2` body held at the callee's return**
(x86-64): `callC2_of` (`CallC2.lean`) with the source's `ret` not taken.
The machine's return and the result's store `mov %rax, off(%rbp)` run with
the source at the callee's exit control at `f :: fs`; the segment ends at
`ContC` behind that `ret` (`HeldC`).

- `heldND`: a node held one frame above `fs`, its invariant at the
  control the held `ret` steps to;
- `calleeP_seg2H`: `calleeP_seg2` held (`call_ndSFH`), ending at the held
  return node;
- `retP_seg2H`, `retP_segS2H`: the result's store between held nodes, `W`
  at the held pairs from `hWH` (the store's node only);
- `callC2H_of`: `CallC2H` from `callC2_of`'s premises and `hWH`.
-/
import Spike.Lib.LowerX64.HeldC
import Spike.Lib.LowerX64.CallC2
import Spike.Lib.X64CallSAH

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (labelOf i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv opdVal_upd WordsRep SRep sevalAt lookupS)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName labName atomV)
open Scc.Sem (ValRep)
open Spike.Lib.LowerCall (Callee)
open Spike.Lib.X64Consumer (noRetBlk)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)

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

/-- **The result's store into `r%n` with the source held** (`retP_seg2`
between `heldND`s): the store takes no source step, so the held `ret` and
its landing are carried; `W₀` at the held pairs of the store's node from
`hWH`, no outside move there from `hWB`. -/
theorem retP_seg2H {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ W₁ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₁ K exe endPc R F n blk)
    {x : String} {e : Expr} {s : SEnv} {off : Int} {r : Scc.IR.Reg} (hoff : rsOf fr r = some off)
    {pcR : Int64} {z : Nat} (hc : Cd pcR [(stDir off, z)]) {f : TermRun.Frame}
    (hWH : ∀ st c a cR, c.term = .ret a → FrameStep p (c, f :: fs) (cR, fs) →
      At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off) st cR → W₀ st c) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (heldND p f fs x e (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off)))
      (At exe endPc R F (heldND p f fs x e (brN2 lbl fr fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs))
        (pcR + Int64.ofNat z) e s fun _ => True))) := by
  let n1 : ND := ⟨pcR, oB fr, (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off).J⟩
  let n0 : ND := ⟨pcR, oB fr, (heldND p f fs x e (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off)).J⟩
  have hB := hWB n1 _ (SubCd.whole hc) rfl (okBlk_stDir hf h1 hoff z) rfl
    fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩
  have s0 : SegW W₀ K p lbl ms0 (At exe endPc R F n0)
      (At exe endPc R F (heldND p f fs x e (brN2 lbl fr fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs))
        (pcR + Int64.ofNat z) e s fun _ => True))) := by
    refine seg_blk1 hF hR hlo hhi (hCd _ _ hc) ?_ (by simp) (okBlk_stDir hf h1 hoff z)
      fun σ c hJ => ⟨c, .refl c, ?_⟩
    · intro st σ c he hn hdc hpc hA hF0 hJ k hk m hAm hD
      obtain ⟨-, -, a, cR, ht, hst, hJR⟩ := hJ
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      refine ⟨hWH _ c a cR ht hst ?_, (hB st σ cR he hn hdc hpc hA hF0 hJR 0 hk m hAm hD).2⟩
      refine ⟨he, hn, hdc, by simp [cellOff, n0, retCP2, heldND], σ, ?_, hF _ _ hF0 hD, hJR⟩
      exact Abs.weaken (o := oB fr) (by simp [SO.le, oB, retCP2]) (by simpa [arun] using hAm)
    · show Hit _ (arun _ _ ⟨pcR, oB fr, σ⟩) c
      rw [arun_stDir hf h1 hoff]
      obtain ⟨hfx, hfb, a, cR, ht, hst, hj, hen, hfj, hr, htp, -⟩ := hJ
      exact ⟨rfl, so_le_oB fr, hfx, hfb, a, cR, ht, hst, hj, hen, frJ_upd hf hfj hoff _, hr, htp, trivial⟩
  exact s0.mono_pre fun st c h => at_rbp_addr (k := 0) h fun σ c hJ => by
    obtain ⟨_, _, _, _, _, _, hJ'⟩ := hJ
    exact hJ'.2.2.2.2.2

/-- **The result's store with the source held, at any callee frame**
(`retP_seg2H` lifted to frames `f :: fs`, `W` at the store's held pairs
from `hWH`). -/
theorem retP_segS2H {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms : List TermRun.Frame → MemSide isa} {W : FragS isa} {W₁ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₁ K exe endPc R F n blk)
    {x : String} {e : Expr} {s : SEnv} {off : Int} {r : Scc.IR.Reg} (hoff : rsOf fr r = some off)
    {pcR : Int64} {z : Nat} (hc : Cd pcR [(stDir off, z)])
    (hWH : ∀ f st c a cR, c.term = .ret a → FrameStep p (c, f :: fs) (cR, fs) →
      At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off) st cR → W st c (f :: fs)) :
    SegWS W K p lbl ms
      (fun st c fs' => ∃ f, (At exe endPc R F (heldND p f fs x e (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off))).at
        (f :: fs) st c fs')
      (fun st c fs' => ∃ f, (At exe endPc R F (heldND p f fs x e (brN2 lbl fr fp ra tp Q
        (fun c => FrameRunM p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s fun _ => True))).at (f :: fs) st c fs') :=
  SegWS.exists_pre fun f =>
    (SegWS.liftS (W := W) (f :: fs) (retP_seg2H (p := p) (lbl := lbl) (K := K) (ms0 := ms (f :: fs))
      (W₀ := fun st c => W st c (f :: fs)) (fp := fp) (ra := ra) (tp := tp) (Q := Q) (f := f)
      hf h1 hF hR hlo hhi hCd hG hWB hoff hc (hWH f)) fun _ _ h => h).mono_post fun _ _ _ h => ⟨f, h⟩

/-! ## The callee, held -/

/-- **The callee inside a plain call held at its return** (`calleeP_seg2`
by `call_ndSFH`): the segment ends at the return node held one frame above
`fs` (`heldND`), the source at the callee's exit control. -/
theorem calleeP_seg2H {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2 lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab))
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) (hg : GrpL env)
    {n : Nat} (hfresh : Fresh env n) {off : Int} (hoff : rsOf fr (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} (hsc : InLits lits a)
    (hlit : ∀ k, a = .lit k → k < 2 ^ 64)
    {pcB : Int64} {zc k : Nat} (hb : Bl pcB zc (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e,
      (Spike.Lib.Form.lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hLb : LocBaseRegAt (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) e)
    (hsite : ∀ q : CallG, q.ra = (pcB + Int64.ofNat zc).toBitVec →
      CallSite2 lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q) :
    SegWS W K p lbl ms
      ((At exe endPc R F (callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))).at fs)
      (fun s c fs' => (∃ f, (At exe endPc R F (heldND p f fs x e (retCP2 p lbl R fr fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off))).at (f :: fs) s c
          fs') ∨ Ab s c fs') := by
  have h8 := frame_mod8B hf
  have hsp : ((oB fr).sp - 8) - 0 = -(fr.size : Int) - 8 := by simp [oB]
  have hRc : R.callee (((oB fr).sp - 8) - 0) (-D) 8 = calleeR R fr.size D := by rw [hsp]; rfl
  have hsp0 : ((oB fr).sp - 8) - 0 + 0 = -(fr.size : Int) - 8 := by simp [oB]
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] a []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
  have hsa := sevalAt_ofEnv2_one hg ha
  -- the frame's cells are kept by the callee
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf fr r = some k' →
      R.Off k' ∧ ¬ (R.callee (((oB fr).sp - 8) - 0) (-D) 8).Off (k' - (((oB fr).sp - 8) - 0)) := by
    intro r k' hk'
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk'
    rw [hsp]
    exact frame_out hlo hhi hD0 hk2 (by omega) (by omega)
  have hout0 : R.Off 0 ∧ ¬ (R.callee (((oB fr).sp - 8) - 0) (-D) 8).Off (0 - (((oB fr).sp - 8) - 0)) := by
    rw [hsp]; exact frame_out hlo hhi hD0 (by decide) (by omega) (by omega)
  have hout8 : R.Off 8 ∧ ¬ (R.callee (((oB fr).sp - 8) - 0) (-D) 8).Off (8 - (((oB fr).sp - 8) - 0)) := by
    rw [hsp]; exact frame_out hlo hhi hD0 (by decide) (by omega) (by omega)
  refine (call_ndSFH (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
      ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))
    (γ := CallG) (κ' := Ctl) (e0 := 0) (lo' := -D) (hi' := 8)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN2 p lbl tp fs q frm c0')
    (N := fun f (_ : Unit) => heldND p f fs x e (retCP2 p lbl R fr fp ra tp c0 fs
      (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
        (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
      (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off))
    (E := fun _ (e : Empty) => e.elim)
    (fs := fs) (Ab := Ab) hR hF
    (by show R.lo ≤ ((oB fr).sp - 8) - 0 + -D; rw [hsp]; omega) (by omega)
    (by show ((oB fr).sp - 8) - 0 < R.hi; rw [hsp]; omega)
    (by show ((oB fr).sp - 8) - 0 + 8 ≤ R.hi; rw [hsp]; omega)
    (by show (((oB fr).sp - 8) - 0) % 8 = 0; rw [hsp]; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC _ g dd hfd rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    have hR' : R' = calleeR R fr.size D := hR'eq.trans hRc
    subst hR'
    have hra : q.ra = (pcB + Int64.ofNat zc).toBitVec := by
      obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      rw [← hNe.2.2.1]
      show σC.slot ((oB fr).sp - 8 - 0 + 0) = _
      rw [hsp0]; exact hJ.2.2.2.2.2.2.2
    refine (hcal g q frm F' hFS ?_ ?_ ?_ ?_ (hsite q hra)).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, fun k hk hn => hcells m hm k hk ?_, mC, σC, c, _, _, hA, fun k hk hn => hkept k hk ?_,
        hct, hT, hj, ⟨lits, cs, bufs, hen⟩, hfj, ?_⟩
      · show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
      · show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
      · obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
        rw [hj.1] at ht1
        cases ht1
        subst hfr1
        have hne : ∀ y, y ≠ x →
            ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
          intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
        refine ⟨fun y hy hyx => ?_, fun y hy hyx ty pls hl b o hb => ?_, fun y kk v hy hl => ?_⟩
        · have := hIt y hy
          rw [ofEnv2_cons hgr] at this
          simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
        · refine hLb y hy ty pls ?_ b o hb
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
      obtain ⟨hj, hen, -, -, -, hP2, -, -⟩ := hJ
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
          rw [hP2] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := NumL.one (hl.evalAt' hsc hlit hev1).2 hm1
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · exact ⟨pcB, zc, k, hb, hra⟩
    · rintro s c fs' (⟨rfl, c0', hrun, hat⟩ | hab)
      · exact .inl ⟨⟨c0', at_of_rbR (fun σ c h => ⟨hrun, h⟩) hat, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ta, ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) hsa
    exact ⟨⟨σC.regs.rbp.toBitVec, σC.slot ((oB fr).sp - 8 - 0 + 0), σC.regs.rdi.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, ta, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP3, hP4⟩ := hJ
    obtain ⟨hrun, ⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, hrbp⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
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
    have hvr' : ValRep lbl w2.val (σR.regs.get64 .rax).toNat := by
      rw [hregs]; exact hvr 0 (by simp) (by simp [Scc.Emit.X64.retRegs])
    refine .inl ⟨(), ?_, ?_, rfl, rfl, _, _, hta, hstep, ?_⟩
    · show pcB + Int64.ofNat zc = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec (σC.slot ((oB fr).sp - 8 - 0 + 0))
      rw [hsp0, hP4, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(fr.size : Int), []⟩ ⟨(oB fr).sp - 8 - 0 + 8, []⟩ = true
      simp [SO.le, oB]
    · refine ⟨⟨rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
          ((x, dd.retTy, [w2]) :: c.env)
        rw [ofEnv2_cons hgr, hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv2 hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hf hk' hoff) hne
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
      · exact ⟨(hsl 0 hout0.1 hout0.2).trans hfj.1, (hsl 8 hout8.1 hout8.2).trans hfj.2⟩
      · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
          (hrun.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
      · rw [hregs]; exact htpx
      · rw [hregs]; exact hrbp.trans (hNe.2.1.symm.trans hP3)
  · rintro s c fs' (⟨fr', h, rfl⟩ | hab)
    · exact .inl ⟨fr', h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim, rfl⟩
    · exact .inr hab

/-! ## The call, held -/

/-- **A plain call of an `Accepted2` body held at the callee's return**
(`CallC2H`; `callC2_of` with the source's `ret` not taken): `callC2_of`'s
premises and `hWH`, `W` at the held pairs of the result's store's node
(`retCP2`), the only machine states between the return and `ContC`. -/
theorem callC2H_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel g)), zc)])
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isa} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      CallSite2 lcx fr Cd Bl G0 T (_root_.Executable.labels exe).label i Lk g q →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab))
    (hWH : ∀ (c0 : Ctl) (Q : Ctl → Prop) (pcR : Int64) (e : Expr) (s : SEnv) (off : Int) (st : State)
      (c : Ctl) (a : CoreTerm.At) (f : TermRun.Frame) (cR : Ctl), G0 c0 → c.term = .ret a →
      FrameStep p (c, f :: fs) (cR, fs) → At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off) st cR →
      W st c (f :: fs)) :
    CallC2H p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk := by
  intro c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs hc0 hT hfresh hlp hty hg hcnt hcl ha hcode hIt hIc
    hLb hpt
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRunM.ofLocal h fs)
  have hGR : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(fr.size : Int) := by omega
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  obtain ⟨lw, off, zs, zc, z, hlw, hoff, hz, hc1, hb, hc3, -, hp⟩ := instsC2_call hcode
  subst hp
  -- `w`'s load into `%rdi`
  have sA := argP_seg2 (p := p) (lbl := lbl) (lsize := lsize) (K := K) (W₀ := W₀) (ms0 := ms fs) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs) (i := i)
    hf h1 hF hR hlo0 hhi hCd hG hWB hlw hz hc1
  -- `callq g`
  have sQ := callq_seg2 (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs) (fp := fp) (ra := ra) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (Q := fun c => EnvQ lits cs bufs lsize c.env)
    (Rn := LocalRun p c0)
    (P := fun σ => opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat ∧ σ.regs.get64 .rbp = R.addr 0)
    (P' := callPP fr R w (pc + Int64.ofNat zs.sum + Int64.ofNat zc))
    hf hF hR (by omega) hhi hBl hG hWBl hb fun σ ⟨hp2, hp3⟩ => by
      refine ⟨?_, ?_, ?_⟩
      · show opdVal (rsOf fr) (upd _ _ _) w = some ((σ.regs.set64 .rsp _).get64 .rdi).toNat
        rw [opdVal_upd_out hf (by omega), Reg64s.get64_set64_ne _ (by decide)]; exact hp2
      · show (σ.regs.set64 .rsp _).get64 .rbp = _
        rw [Reg64s.get64_set64_ne _ (by decide)]; exact hp3
      · show upd _ _ _ _ = _
        rw [upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have sW := SegWS.liftS (W := W) fs ((sA.mono_post fun _ _ h => at_brN2_rbp h).seq sQ) hW₀
  -- the callee
  have sCal := calleeP_seg2H (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab) (lits := lits) (cs := cs) (bufs := bufs)
    hf hprog hF hR hD0 hD8 hlo hhi hG hWC hcal hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hLb
    fun q hq => ⟨c0, pc, _, kk, kk', env, n, x, a, e, t, w, lits, cs, bufs, lw, zs, zc, hc0, hT, hfresh, hlp,
      hty, hg, hcnt, hcl, ha, hcode, hlw, hz, hc1, hb, hq, hpt⟩
  -- the result's store
  have sR := retP_segS2H (p := p) (lbl := lbl) (x := x) (K := K) (W := W) (ms := ms)
    (fp := fp) (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
    hf h1 hF hR hlo0 hhi hCd hGR hWB hoff hc3
    fun f st c a' cR ht hst hA => hWH c0 _ _ _ _ _ st c a' f cR hc0 ht hst hA
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨f, ⟨he, hn, hdc, hpc, σ, hA, hD, hfx, hfb, a', cR, ht, hst, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj,
    hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨a', f, cR, ht, rfl, hfx, hfb, hst, .inl ⟨rfl, cR, hr, he, hn, hdc, hpc, σ, hA, hD,
      ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl cR, SlotRepAt.of_nodeJE hj hIt hLb hIc⟩, htp⟩⟩
  · exact .inr hab

end Call

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.retP_segS2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retP_segS2H

/-- info: 'Spike.Lib.LowerX64.calleeP_seg2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleeP_seg2H

/-- info: 'Spike.Lib.LowerX64.callC2H_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2H_of
