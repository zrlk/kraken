/-
**A plain call** (x86-64, no depth counter): `CallC`, the call's
obligation at the body's node at `let x = call g a in e`, and its proof
`callC_of` from the call's code, its blocks inside the frame's fragment and
the callee's segment.

A plain call's code (`CodeC`'s call arm, `codeC_call`) is `w`'s load into
`%rdi`, `callq g` (`Bl`) and the result's store `movq %rax, off(%rbp)` into
`r%n`. The walk, at the caller's frames `fs` but the callee's segment (at
`frm :: fs`):

- `w`'s load (`argP_seg`): from the body's node, taking the source's local
  run to the call exactly (`brN`);
- `callq g` (`callq_seg`, `Spike/Lib/LowerX64/CallNodes.lean`): the return
  address pushed into the cell `-(size) - 8`;
- the callee (`calleeP_seg`): `call_ndSF` (`Spike/Lib/X64CallSA.lean`) with
  the callee's segment `hcal`, back at the return address (`retCP`) with the
  source returned, or an abort;
- the result's store (`retP_seg`), the ghost re-anchored at the source's
  control there.

The callee's label is `W`'s only at a function of the program (`hWC`'s
`p.find?`), as the callee entry's own coverage gives it.
-/
import Spike.Lib.LowerX64.CallNodes

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (labelOf i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ SEnv opdVal_upd WordsRep SRep)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName labName atomV)
open Scc.Sem (ValRep)
open Spike.Lib.LowerCall (Callee)
open Spike.Lib.X64Consumer (noRetBlk)

set_option linter.unusedSimpArgs false

/-! ## The call's nodes -/

/-- **Back from the callee** at the return address `pc`: `%rsp` at the
frame's bottom (`%rbp` not yet a static offset but at the region's base),
the source returned at `e` whose environment `s` the frame's cells place
with `%rax` stored to the result's cell `off`, its words numbers, the saved
pair, the source reached from the call's ghost `c0` by a frame run at the
frames `fs`, the `%fs` base `tp`. -/
def retCP (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (R : Region) (fr : Scc.Emit.X64.Frame)
    (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame) (pc : Int64) (e : Expr) (s : SEnv)
    (off : Int) : ND :=
  ⟨pc, ⟨-(fr.size : Int), []⟩, fun σ c => NodeJ lbl (rsOf fr) e s (upd σ.slot off (σ.regs.get64 .rax)) c ∧
    EnvNum c.env ∧ FrJ fp ra σ.slot ∧ FrameRun p (c0, fs) (c, fs) ∧ σ.regs.fsBase = tp ∧
    σ.regs.get64 .rbp = R.addr 0⟩

/-- The call node's facts for the callee: `%rdi` the argument `w`'s value,
`%rbp` the region's base, the return address `pcR` in the cell below the
frame. -/
def callPP (fr : Scc.Emit.X64.Frame) (R : Region) (w : Scc.IR.Operand) (pcR : Int64) (σ : AS) : Prop :=
  opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat ∧
    σ.regs.get64 .rbp = R.addr 0 ∧ σ.slot (-(fr.size : Int) - 8) = pcR.toBitVec

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The argument's load -/

/-- A call's argument load into `%rdi` has no `ret`. -/
theorem noRet_argLoadC {fr : Scc.Emit.X64.Frame} {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item}
    (hw : getOp fr .rdi w = .ok lw) {zs : List Nat} (hz : zs.length = (dirs lw).length) :
    noRetBlk ((dirs lw).zip zs) = true := by
  rcases getOp_cases hw with ⟨r, off, rfl, -, hl⟩ | ⟨v, rfl, hl⟩
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    rfl
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    rfl

/-- **The argument's load into `%rdi`** from the body's node: the source's
local run taken to the call exactly (`brN`), `%rdi` holding `w`'s value. -/
theorem argP_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item} (hlw : getOp fr .rdi w = .ok lw)
    {zs : List Nat} (hz : zs.length = (dirs lw).length) {pc : Int64} (hc : Cd pc ((dirs lw).zip zs))
    {t : Expr} {s : SEnv} :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN p lbl fr fp ra c0 pc t s).withTp tp))
      (At exe endPc R F (brN lbl fr fp ra tp (LocalRun p c0) (pc + Int64.ofNat zs.sum) t s
        fun σ => opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat)) := by
  obtain ⟨dl, hdl⟩ := dirs_getOp hlw
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs lw).zip zs) = true := by
    have := okBlk_getOp hf h1 (by decide) (by decide) hlw hz []
    rw [List.append_nil] at this
    rw [this]; rfl
  refine seg_blk1 hF hR hlo hhi (hCd _ _ hc)
    (hWB _ _ (SubCd.whole hc) rfl hok (noRet_argLoadC hlw hz) fun σ c h => ⟨hG c h.1.2.2, h.1.2.1⟩)
    (zip_ne_nil hz (by rw [hdl]; simp)) hok ?_
  rintro σ c ⟨⟨⟨c', hr, hj, hn⟩, hfj, hc0⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨v, hv, hrr⟩ := arun_getOp hf h1 (by decide) hlw (_root_.Executable.labels exe).label pc σ hz
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  rw [hrr]
  refine ⟨rfl, so_le_oB fr, hj, hn, hfj, hc0.trans hr, ?_, ?_⟩
  · show (σ.regs.set64 .rdi v).fsBase = tp
    rw [Reg64s.set64_fsBase]; exact htp
  · show opdVal (rsOf fr) σ.slot w = some ((σ.regs.set64 .rdi v).get64 .rdi).toNat
    rw [Reg64s.get64_set64_self]; exact hv

/-! ## The callee -/

/-- **The callee inside a plain call is one segment** at the caller's
frames `fs`: from the call node at `g`'s label (`callN`, the source exactly
at `let x = call g a in e`, reached locally from the ghost `c0`) to the
return address `pcB + zc` (`retCP`), or an abort (`Ab`, inside the callee).
The callee's label is inside `W` at a function `dg` of the program
(`hWC`); the continuation's free variables are bound (`hIt`) and its
immediates the table `i`'s (`hIc`), for `CalleeF`. -/
theorem calleeP_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {Bl : Int64 → Nat → Label → Nat → Prop} {G0 : Ctl → Prop} {c0 : Ctl}
    (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF p lbl fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) Ab))
    {x g : String} {a : At} {e : Expr} (hT : T (.let_ x (.call g [] a []) e)) (hcl : Callee lcx g)
    {env : Scc.Lower.Env} {t : Ty} {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w])) {n : Nat}
    (hfresh : Fresh env n) {off : Int} (hoff : rsOf fr (regName "r" n) = some off)
    {pcB : Int64} {zc k : Nat} (hb : Bl pcB zc (Scc.Lower.Names.user g) k)
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (Spike.Lib.Form.lookupS (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome)
    (hIc : ImmIn i (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) e) :
    SegWS W K p lbl ms ((At exe endPc R F (callN lbl fr fp ra tp (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv env) (callPP fr R w (pcB + Int64.ofNat zc)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCP p lbl R fr fp ra tp c0 fs (pcB + Int64.ofNat zc) e
          (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨ Ab s c fs') := by
  have h8 := frame_mod8B hf
  have hsp : ((oB fr).sp - 8) - 0 = -(fr.size : Int) - 8 := by simp [oB]
  have hRc : R.callee (((oB fr).sp - 8) - 0) (-D) 8 = calleeR R fr.size D := by rw [hsp]; rfl
  have hsp0 : ((oB fr).sp - 8) - 0 + 0 = -(fr.size : Int) - 8 := by simp [oB]
  obtain ⟨-, dd, hfd, hretTy⟩ := hcl
  rw [hprog] at hfd
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
  refine (call_ndSF (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := callN lbl fr fp ra tp (LocalRun p c0) ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv env) (callPP fr R w (pcB + Int64.ofNat zc)))
    (γ := CallG) (κ' := Ctl) (e0 := 0) (lo' := -D) (hi' := 8)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN p lbl tp fs q frm c0')
    (N := fun _ : Unit => retCP p lbl R fr fp ra tp c0 fs (pcB + Int64.ofNat zc) e
      (ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) off) (E := fun e : Empty => e.elim)
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
    refine (hcal g q frm F' hFS ?_ ?_ ?_ ?_).mono_post ?_
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, -, -, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨hF'F m hm, fun k hk hn => hcells m hm k hk ?_, mC, σC, c, _, _, hA, fun k hk hn => hkept k hk ?_,
        hct, hT, hj, hen, hfj, ?_⟩
      · show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
      · show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
      · obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, -, -, hfr1⟩ := id hct
        rw [hj.1] at ht1
        cases ht1
        subst hfr1
        have hne : ∀ y, y ≠ x →
            ((x, Ty.int, [Spike.Lib.Form.WordPl.one (.reg (regName "r" n))]).1 == y) = false := by
          intro y hy; simp only [beq_eq_false_iff_ne]; exact fun h => hy h.symm
        refine ⟨fun y hy hyx => ?_, fun y kk v hy hl => ?_⟩
        · have := hIt y hy
          rw [ofEnv_cons] at this
          simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hyx] using this
        · apply hIc y kk v
          rw [ofEnv_cons]
          simpa only [Spike.Lib.Form.lookupS, List.find?_cons, hne y hy] using hl
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      have hcE : cE = q.cE := hNe.1
      subst hcE
      exact ⟨c, x, a, e, hG c hJ.2.2.2.1, hT, hJ.1.1, hct⟩
    · obtain ⟨σC, c, cE, hJ, hct, hNe⟩ := hex
      obtain ⟨hj, hen, -, -, -, hP2, -, -⟩ := hJ
      obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, -, hev1, hcE1, -⟩ := hct
      rw [hj.1] at ht1
      cases ht1
      obtain ⟨ws', hev', hwr⟩ := hj.2.2.evalAt (fun _ => rfl) (sevalAt_ofEnv ha)
      rw [hev1] at hev'
      cases hev'
      match ws1, hwr, hev1, hcE1 with
      | [w'], ⟨⟨v, hv, hvr⟩, _⟩, hev1, hcE1 =>
        have hv' : v = q.v.toNat := by
          rw [hP2] at hv
          cases hv
          rw [← hNe.2.2.2.1]; rfl
        obtain ⟨kk, hkk, hlt⟩ := EnvNum.evalAt hen (sevalAt_ofEnv ha) hev1 w' (by simp)
        exact ⟨d1.arg, d1.argTy, w', by rw [← hNe.1, hcE1], hv' ▸ hvr, kk, hkk, hlt⟩
    · obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      refine ⟨pcB, zc, k, hb, ?_⟩
      rw [← hNe.2.2.1]
      show σC.slot ((oB fr).sp - 8 - 0 + 0) = _
      rw [hsp0]; exact hJ.2.2.2.2.2.2.2
    · rintro s c fs' (⟨rfl, c0', hrun, hat⟩ | hab)
      · exact .inl ⟨⟨c0', at_of_rbR (fun σ c h => ⟨hrun, h⟩) hat, trivial⟩, rfl⟩
      · exact .inr hab
  · -- the source's call and the callee's entry
    intro σC c hJ
    obtain ⟨hj, -, -, -, htp, -⟩ := hJ
    obtain ⟨ws', hev, -⟩ := hj.2.2.evalAt (fun _ => rfl) (sevalAt_ofEnv ha)
    exact ⟨⟨σC.regs.rbp.toBitVec, σC.slot ((oB fr).sp - 8 - 0 + 0), σC.regs.rdi.toBitVec,
      ⟨dd.body, [(dd.arg, dd.argTy, ws')], none⟩⟩, _, ⟨x, e, c.env, [], dd.retTy⟩,
      ⟨x, g, a, e, dd, t, ws', hj.1, hfd, hev, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, htp⟩
  · -- the return: the source returns into `x`, the caller's cells kept
    intro q c0' σC c cE frm σx c' σR hJ hct hNe hEx hregs _ _ hsl
    obtain ⟨hj, hen, hfj, hr, -, -, hP3, hP4⟩ := hJ
    obtain ⟨hrun, ⟨⟨a', t', w', hta, -, hev', ⟨nn, hnn⟩, hvr, hrbp⟩, hlr⟩, htpx⟩ := hEx
    have hcE : cE = q.cE := hNe.1
    subst hcE
    have hct' := hct
    obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
    rw [hj.1] at ht1
    cases ht1
    rw [hfd] at hfd1
    cases hfd1
    subst hfr1
    have hstep : FrameStep p (c', ⟨x, e, c.env, [], dd.retTy⟩ :: fs)
        (⟨e, (x, dd.retTy, [w']) :: c.env, none⟩, fs) := .ret hta rfl hev'
    have hvr' : ValRep lbl w'.val (σR.regs.get64 .rax).toNat := by rw [hregs]; exact hvr
    refine ⟨⟨e, (x, dd.retTy, [w']) :: c.env, none⟩, .single hstep, .inl ⟨(), ?_, ?_, ?_⟩⟩
    · show pcB + Int64.ofNat zc = Int64.ofBitVec q.ra
      rw [← hNe.2.2.1]
      show _ = Int64.ofBitVec (σC.slot ((oB fr).sp - 8 - 0 + 0))
      rw [hsp0, hP4, Int64.ofBitVec_toBitVec]
    · show SO.le ⟨-(fr.size : Int), []⟩ ⟨(oB fr).sp - 8 - 0 + 8, []⟩ = true
      simp [SO.le, oB]
    · refine ⟨⟨rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · show SRep lbl _ ((x, .int, [.one (.reg (regName "r" n))]) :: ofEnv env) ((x, dd.retTy, [w']) :: c.env)
        rw [hretTy]
        refine (hj.2.2.congr fun b hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x .int
          ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
        have hne := Fresh.ofEnv hfresh "r" b hb pl hpl o ho r hr'
        rw [upd_apply]
        split
        · next hk => subst hk; exact absurd (rsOf_inj hf hk' hoff) hne
        exact hsl k' (hout r k' hk').1 (hout r k' hk').2
      · refine hen.cons fun w hw => ?_
        simp only [List.mem_singleton] at hw
        subst hw
        rw [hnn] at hvr'
        exact ⟨nn, hnn, hvr'.1⟩
      · exact ⟨(hsl 0 hout0.1 hout0.2).trans hfj.1, (hsl 8 hout8.1 hout8.2).trans hfj.2⟩
      · exact (FrameRun.ofLocal hr fs).trans (.step (hct.step fs)
          (hrun.trans ((FrameRun.ofLocal hlr _).trans (.single hstep))))
      · rw [hregs]; exact htpx
      · rw [hregs]; exact hrbp.trans (hNe.2.1.symm.trans hP3)
  · rintro s c fs' (⟨h, rfl⟩ | hab)
    · exact .inl (h.elim (fun ⟨_, h⟩ => ⟨h, rfl⟩) fun ⟨e, _⟩ => e.elim)
    · exact .inr hab

/-! ## The result's store -/

/-- **The result's store into `r%n`** after the return: from the return
address (`retCP`) to a node whose ghost is a frame run from the call's `c0`
(`brN` with `Rn := FrameRun p (c0, fs) (·, fs)`). -/
theorem retP_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRun p (c0, fs) (c, fs) → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    {e : Expr} {s : SEnv} {off : Int} {r : Scc.IR.Reg} (hoff : rsOf fr r = some off)
    {pcR : Int64} {z : Nat} (hc : Cd pcR [(stDir off, z)]) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (retCP p lbl R fr fp ra tp c0 fs pcR e s off))
      (At exe endPc R F (brN lbl fr fp ra tp (fun c => FrameRun p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s
        fun _ => True)) := by
  let n0 : ND := ⟨pcR, oB fr, (retCP p lbl R fr fp ra tp c0 fs pcR e s off).J⟩
  have s0 : SegW W₀ K p lbl ms0 (At exe endPc R F n0)
      (At exe endPc R F (brN lbl fr fp ra tp (fun c => FrameRun p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s
        fun _ => True)) := by
    refine seg_blk1 hF hR hlo hhi (hCd _ _ hc)
      (hWB n0 _ (SubCd.whole hc) rfl (okBlk_stDir hf h1 hoff z) rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩)
      (by simp) (okBlk_stDir hf h1 hoff z) fun σ c hJ => ⟨c, .refl c, ?_⟩
    show Hit _ (arun _ _ ⟨pcR, oB fr, σ⟩) c
    rw [arun_stDir hf h1 hoff]
    obtain ⟨hj, hen, hfj, hr, htp, -⟩ := hJ
    exact ⟨rfl, so_le_oB fr, hj, hen, frJ_upd hf hfj hoff _, hr, htp, trivial⟩
  exact s0.mono_pre fun st c h => at_rbp_addr (k := 0) h fun σ c hJ => hJ.2.2.2.2.2

/-! ## The call -/

/-- **A plain call** (`CallC`) at the frames `fs`, in the region `R` with
room `D` below the frame and its return address for the callee (`hlo`):
the code predicates give code (`hCd`, `hBl`); the call's blocks inside `W₀`
(inside `W` at `fs`, `hW₀`) at every node of the frame's offsets whose
source controls are in `G0` (closed under the frame runs at `fs`, `hG0`)
with the saved pair (`hWB` at its covered `ret`-free blocks of `Cd`,
`okBlk`, `noRetBlk`; `hWBl`; `hWC` at a program function's label after the
push); the terms in `T` call with no type or index arguments
(`hTc`); and the callee's segment at the pushed frame `frm :: fs` in the
callee's region (`calleeR`) from its entry to its exits in the rebased
region (`hcal`, e.g. its `FnSpecC`), for every frame condition `F'` with
`CalleeF` (at the table `i`), from a call in `G0` at a term in `T` (`q.cE`
the callee's entry control) with the argument `ArgV` and the return address
after a `callq g` (`Bl`). -/
theorem callC_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → okBlk (-(fr.size : Int)) 16 (oB fr) blk = true →
      noRetBlk blk = true → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc R F n blk)
    (hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel g)), zc)])
    (hWC : ∀ (n : ND) g dg, p.find? (·.name == g) = some dg →
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {T : Expr → Prop} (hTc : ∀ x g is a ts e, T (.let_ x (.call g is a ts) e) → is = [] ∧ ts = [])
    {i : Expr → String → Nat → Option Nat} {Ab : FragS isa}
    (hcal : ∀ (g : String) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF p lbl fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) Ab)) :
    CallC p lbl lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc kk env n x g is a ts e t w is' tm hc0 hT hcl ha hfresh hcode hIt hIc
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRun.ofLocal h fs)
  have hGR : ∀ c, FrameRun p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(fr.size : Int) := by omega
  obtain ⟨lw, off, zs, zc, z, hlw, hoff, hz, hc1, hb, hc3, hrest⟩ := codeC_call hcode
  refine ⟨_, hrest, ?_⟩
  -- `w`'s load into `%rdi`
  have sA := argP_seg (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv env) hf h1 hF hR hlo0 hhi hCd hG hWB hlw hz hc1
  -- `callq g`
  have sQ := callq_seg (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs) (fp := fp) (ra := ra) (tp := tp)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv env) (Rn := LocalRun p c0)
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
  have sW := SegWS.liftS (W := W) fs ((sA.mono_post fun _ _ h => at_brN_rbp h).seq sQ) hW₀
  -- the callee
  have sCal := calleeP_seg (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab)
    hf hprog hF hR hD0 hD8 hlo hhi hG hWC hcal hT hcl ha hfresh hoff hb hIt hIc
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (retP_seg (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs)
    (fp := fp) (ra := ra) (tp := tp) (e := e) (s := ofEnv ((x, .int, [.reg (regName "r" n)]) :: env)) hf h1 hF hR hlo0 hhi hCd hGR hWB hoff
    hc3) hW₀
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, hen, hfj, hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨rfl, c, hr, he, hn, hdc, hpc, σ, hA, hD, ⟨⟨c, .refl c, hj, hen⟩, hfj, .refl c⟩, htp⟩
  · exact .inr hab

end Call

end Spike.Lib.LowerX64
