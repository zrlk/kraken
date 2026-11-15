/-
**The plain call of an `Accepted2` body with its blocks asked at placed
nodes** (x86-64; the twin of `Spike/Lib/LowerA64/G1CallW.lean`):
`callC2_ofFW : CallC2FW` (`Spike/Lib/LowerX64/G1CallWStmt.lean`),
`callC2_ofF` (`Spike/Lib/LowerX64/CallC2.lean`) with the frame's fragment
asked of the call's blocks only at nodes whose controls the slot file
places (`SlotRepAt`) and, at no frames, are off a `ret`.

The call's nodes place their controls: the argument's load starts at
`bodyN2`, which carries `SlotRepAt`; the bracket's nodes `brN2` (at
`callq g`) and `callN2` (at the callee's entry) are at the call's `let`
itself, placed by their `NodeJE` and the walk's facts at the `let`
(`SlotRepAt.of_nodeJE`: the free variables bound, `htot_call`, the
immediates and register bases from the resumption facts' walk, `PtC2`);
the landing node `retCP2` places the continuation in the slot file with the
result's slot at `%rax`'s word (its `NodeJE` and the continuation's facts).

- `htot_call`: the free variables at a plain call bound;
- `argP_seg2W`, `callq_seg2W`, `calleeP_seg2GW`, `retP_seg2W`: `argP_seg2`,
  `callq_seg2`, `calleeP_seg2G`, `retP_seg2` with the frame's fragment
  asked at their placed nodes;
- `callC2_ofFW`: the statement.
-/
import Spike.Lib.LowerX64.G1CallWStmt
import Spike.Lib.Src.LowerMarks2

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

/-- **The free variables at a plain call are bound** (`htot` at its
`let`): the argument's variable by `atomV`, the continuation's others than
`x` by its own (`hIt`). -/
theorem htot_call {env : Scc.Lower.Env} {x g : String} {a : At} {e : Expr} {n : Nat} {t : Ty}
    {w : Scc.IR.Operand} (ha : atomV env a = some (t, [w]))
    (hIt : ∀ y ∈ Scc.Sem.exprFv e, (lookupS (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) y).isSome) :
    ∀ y ∈ Scc.Sem.exprFv (.let_ x (.call g [] a []) e), (lookupS (ofEnv2 env) y).isSome := by
  intro y hy
  simp only [Scc.Sem.exprFv, Scc.Sem.opVars, Scc.Sem.opAts, List.mem_append, List.mem_filter,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy
  rcases hy with hy | ⟨hy, hne⟩
  · cases a with
    | var z =>
      simp only [Scc.Sem.atVars, List.mem_singleton] at hy
      subst hy
      simp only [Scc.Lower.Inv.atomV, Option.map_eq_some_iff] at ha
      obtain ⟨b, hb, -⟩ := ha
      rw [lookupS_ofEnv2, hb]; rfl
    | lit _ => simp [Scc.Sem.atVars] at hy
    | unit => simp [Scc.Sem.atVars] at hy
  · have h := hIt y hy
    rw [lookupS_ofEnv2] at h ⊢
    have hne' : x ≠ y := fun h => by subst h; simp at hne
    simpa [List.find?_cons, hne'] using h

section Call

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-! ## The argument's load and `callq g` -/

/-- **The argument's load into `%rdi`** (`argP_seg2`) with the frame's
fragment asked at the load's node only as placed (`bodyN2`'s `SlotRepAt`)
and off a `ret` at no frames (the source runs locally to the call's term
`t`, `ht`). -/
theorem argP_seg2W {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {i : Expr → String → Nat → Option Nat}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk fr blk → BlkW W₀ K exe endPc R F n blk)
    {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item} (hlw : getOp fr .rdi w = .ok lw)
    {zs : List Nat} (hz : zs.length = (dirs lw).length) {pc : Int64} (hc : Cd pc ((dirs lw).zip zs))
    {t : Expr} (ht : ∀ a, t ≠ .ret a) {s : SEnv} {lits : List (String × Scc.Lower.LitV)}
    {cs bufs : List (String × Nat)} :
    SegW W₀ K p lbl ms0 (At exe endPc R F ((bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).withTp tp))
      (At exe endPc R F (brN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        (pc + Int64.ofNat zs.sum) t s fun σ => opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat)) := by
  have hJ : ∀ σ c, ((bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).withTp tp).J σ c →
      G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧ (fs = [] → ∀ a, c.term ≠ .ret a) := by
    rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, -⟩, hfj, hc0, hsr⟩, -⟩
    exact ⟨hG c hc0, hfj, hsr, fun _ => Spike.Lib.X64ConsumerS.noRet_of_run hr fun a h => by
      rw [hj.1] at h; exact ht a h⟩
  obtain ⟨dl, hdl⟩ := dirs_getOp hlw
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs lw).zip zs) = true := by
    have := okBlk_getOp hf h1 (by decide) (by decide) hlw hz []
    rw [List.append_nil] at this
    rw [this]; rfl
  refine seg_blk1 hF hR hlo hhi (hCd _ _ hc)
    (hWB _ _ (SubCd.whole hc) rfl hJ (.inl ⟨w, lw, zs, hlw, hz, rfl⟩))
    (zip_ne_nil hz (by rw [hdl]; simp)) hok ?_
  rintro σ c ⟨⟨⟨L, sm, B, c', hr, hj, hn, hb, hm, hS⟩, hfj, hc0, -⟩, htp⟩
  refine ⟨c', hr, ?_⟩
  obtain ⟨v, hv, hrr⟩ := arun_getOp hf h1 (by decide) hlw (_root_.Executable.labels exe).label pc σ hz
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  rw [hrr]
  refine ⟨rfl, so_le_oB fr, hj, ⟨hn, hS, L, sm, B, hb, hm⟩, hfj, hc0.trans hr, ?_, ?_⟩
  · show (σ.regs.set64 .rdi v).fsBase = tp
    rw [Reg64s.set64_fsBase]; exact htp
  · show opdVal (rsOf fr) σ.slot w = some ((σ.regs.set64 .rdi v).get64 .rdi).toNat
    rw [Reg64s.get64_set64_self]; exact hv

/-- **`callq g` is one segment** (`callq_seg2`) with the frame's fragment
asked at the bracket's node only as placed: its control at the call's term
`t` (`NodeJE`), placed by the walk's facts there (`htot`, `hlb`, `hic`), off
a `ret` (`ht`), `g` a callee of the lowering context called at a term of
`T` (`hcl`, `hT`). -/
theorem callq_seg2W {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {i : Expr → String → Nat → Option Nat} {lcx : Scc.Lower.Ctx} {T : Expr → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {G0 Q Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c)
    (hWBl : ∀ (n : ND) zc (g : String) k, Bl n.pc zc (Scc.Lower.Names.user g) k → Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → n.o = oB fr →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel (Scc.Lower.Names.user g))), zc)])
    {pc : Int64} {zc : Nat} {g : String} {k : Nat} (hb : Bl pc zc (Scc.Lower.Names.user g) k)
    (hcl : Callee lcx g) (hT : ∃ x a e, T (.let_ x (.call g [] a []) e)) {t : Expr} {s : SEnv}
    (htot : ∀ y ∈ Scc.Sem.exprFv t, (lookupS s y).isSome) (hlb : LocBaseRegAt s t) (hic : ImmIn i s t)
    (ht : ∀ a, t ≠ .ret a) {P P' : AS → Prop}
    (hP : ∀ σ, P σ → P'
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64),
               slot := upd σ.slot (-(fr.size : Int) - 8) (pc + Int64.ofNat zc).toBitVec }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (brN2 lbl fr fp ra tp Q Rn pc t s P))
      (At exe endPc R F (callN2 lbl fr fp ra tp Q Rn
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) t s P')) := by
  have h8 := frame_mod8B hf
  refine seg_blk1 (lo := -(fr.size : Int) - 8) (hi := 16) hF hR hlo hhi (hBl _ _ _ _ hb)
    (hWBl _ _ _ _ hb hcl hT rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1, SlotRepAt.of_nodeJE h.1 htot hlb hic,
      fun _ a ha => ht a (h.1.1 ▸ ha)⟩) (by simp)
    (okBlk_callq _ _ (by simp [offOk, brN2, oB]; omega)) fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c
  rw [arun_callq]
  obtain ⟨hj, hn, hfj, hr, htp, hp⟩ := hJ
  have hk : (oB fr).sp - 8 = -(fr.size : Int) - 8 := rfl
  refine ⟨rfl, so_le_oB8 fr, ?_, hn, ?_, hr, ?_, ?_⟩
  · show NodeJE _ _ _ _ (upd _ ((oB fr).sp - 8) _) c
    rw [hk]
    exact ⟨hj.1, hj.2.1, hj.2.2.congr fun _ _ _ _ o _ => opdVal_upd_out hf (by omega) _ _ o⟩
  · show FrJ _ _ (upd _ ((oB fr).sp - 8) _)
    rw [hk]; exact frJ_upd_out hfj (by omega) _
  · show (σ.regs.set64 .rsp _).fsBase = tp
    rw [Reg64s.set64_fsBase]; exact htp
  · show P' { σ with regs := _, slot := upd _ ((oB fr).sp - 8) _ }
    rw [hk]; exact hP σ hp

/-! ## The callee -/

/-- **The callee inside a plain call of an `Accepted2` body is one
segment** (`calleeP_seg2G`) with the frame's fragment asked at the
callee's entry only as placed: the bracket's control at the call's `let`
(`NodeJE`), placed by the walk's facts there (`htot0`, `hlb0`, `hic0`). -/
theorem calleeP_seg2GW {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    (hF : FStable R F) (hR : R.OK) {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {ms : List TermRun.Frame → MemSide isa}
    {W : FragS isa} {Bl : Int64 → Nat → Label → Nat → Prop}
    {G0 : Ctl → Prop} {c0 : Ctl} (hG : ∀ c, LocalRun p c0 c → G0 c)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
    (hWC : ∀ (g : String) (dg : Decl), p.find? (·.name == g) = some dg → Callee lcx g →
      (∃ x a e, T (.let_ x (.call g [] a []) e)) → ∀ (n : ND),
      n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g) →
      n.o = { oB fr with sp := (oB fr).sp - 8 } →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧ SlotRepAt i lbl (rsOf fr) σ.slot c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      ∀ s c, At exe endPc R F n s c → W s c fs)
    {Ab : FragS isa}
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
    (htot0 : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.call g [] a []) e), (lookupS (ofEnv2 env) y).isSome)
    (hlb0 : LocBaseRegAt (ofEnv2 env) (.let_ x (.call g [] a []) e))
    (hic0 : ImmIn i (ofEnv2 env) (.let_ x (.call g [] a []) e))
    (hcal : ∀ (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop),
      FStable (calleeR R fr.size D) F' → CalleeF2 p lbl lsize fr R F D fp ra i T q frm F' →
      (∃ c x a e, G0 c ∧ T (.let_ x (.call g [] a []) e) ∧ c.term = .let_ x (.call g [] a []) e ∧
        CallTo p c q.cE frm) → ArgV lbl q →
      (∃ pcB zc k, Bl pcB zc (Scc.Lower.Names.user g) k ∧ q.ra = (pcB + Int64.ofNat zc).toBitVec) →
      q.ra = (pcB + Int64.ofNat zc).toBitVec →
      CallerAt2 p lbl lsize fr R D fp ra q frm F' c0 (.let_ x (.call g [] a []) e) env lits cs bufs →
      SegWS W K p lbl ms ((At exe endPc (calleeR R fr.size D) F'
          (calleeN (_root_.Executable.labels exe).label g tp q)).at (frm :: fs))
        (ExitC2B p lbl exe endPc (rbR (calleeR R fr.size D)) F' q.fp q.ra tp q.cE (frm :: fs) frm.ty Ab)) :
    SegWS W K p lbl ms
      ((At exe endPc R F (callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
        ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (.let_ x (.call g [] a []) e)
        (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))).at fs)
      (fun s c fs' => (At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs
          (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
            (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
          (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c fs' ∨
        Ab s c fs') := by
  have h8 := frame_mod8B hf
  have hsp : ((oB fr).sp - 8) - 0 = -(fr.size : Int) - 8 := by simp [oB]
  have hRc : R.callee (((oB fr).sp - 8) - 0) (-D) 8 = calleeR R fr.size D := by rw [hsp]; rfl
  have hsp0 : ((oB fr).sp - 8) - 0 + 0 = -(fr.size : Int) - 8 := by simp [oB]
  have hcl0 := hcl
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
  refine (call_ndSF (KC := False) (W := W) (K := K) (M := fun _ => True) (F₂ := F)
    (nC := callN2 lbl fr fp ra tp (fun c => EnvQ lits cs bufs lsize c.env) (LocalRun p c0)
      ((_root_.Executable.labels exe).label (Scc.Lower.Names.user g))
      (.let_ x (.call g [] a []) e) (ofEnv2 env) (callPP fr R w (pcB + Int64.ofNat zc)))
    (γ := CallG) (κ' := Ctl) (e0 := 0) (lo' := -D) (hi' := 8)
    (Ne := fun q _ => calleeN (_root_.Executable.labels exe).label g tp q)
    (Ex := fun q frm c0' => exN2 p lbl tp fs q frm c0')
    (N := fun _ : Unit => retCP2 p lbl R fr fp ra tp c0 fs
      (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
        (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
      (pcB + Int64.ofNat zc) e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)
    (E := fun e : Empty => e.elim)
    (fs := fs) (Ab := Ab) hR hF
    (by show R.lo ≤ ((oB fr).sp - 8) - 0 + -D; rw [hsp]; omega) (by omega)
    (by show ((oB fr).sp - 8) - 0 < R.hi; rw [hsp]; omega)
    (by show ((oB fr).sp - 8) - 0 + 8 ≤ R.hi; rw [hsp]; omega)
    (by show (((oB fr).sp - 8) - 0) % 8 = 0; rw [hsp]; omega) (by omega) (by decide)
    (fun h => h.elim) (fun h => h.elim) (fun _ hm _ => hm)
    (hWC g dd hfd hcl0 ⟨x, a, e, hT⟩ _ rfl rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1,
      SlotRepAt.of_nodeJE h.1 htot0 hlb0 hic0, fun _ b hb => by rw [h.1.1] at hb; cases hb⟩) ?_ (fun _ _ => rfl) ?_ ?_).mono_post ?_
  · -- the callee's segment, from `hcal`
    intro R' F' _ _ _ hFS _ hF'F hR'eq hcells q frm hex hall
    have hR' : R' = calleeR R fr.size D := hR'eq.trans hRc
    subst hR'
    have hra : q.ra = (pcB + Int64.ofNat zc).toBitVec := by
      obtain ⟨σC, c, cE, hJ, -, hNe⟩ := hex
      rw [← hNe.2.2.1]
      show σC.slot ((oB fr).sp - 8 - 0 + 0) = _
      rw [hsp0]; exact hJ.2.2.2.2.2.2.2
    refine (hcal q frm F' hFS ?_ ?_ ?_ ?_ hra ?_).mono_post ?_
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
    · intro m hm
      obtain ⟨mC, σC, c, cE, hA, hJ, hct, hNe, hkept⟩ := hall m hm
      obtain ⟨hj, hen, hfj, hr, -, -, hP3, -⟩ := hJ
      have hcE : cE = q.cE := hNe.1
      subst hcE
      refine ⟨mC, σC, c, hA, fun k hk hn => hkept k hk ?_, hct, hj, hen, hfj, hr, hNe.2.1.symm.trans hP3⟩
      show ¬ (calleeR R fr.size D).Off (k - ((oB fr).sp - 8 - 0)); rw [hsp]; exact hn
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
    refine ⟨⟨e, (x, dd.retTy, [w2]) :: c.env, none⟩, .single hstep, .inl ⟨(), ?_, ?_, ?_⟩⟩
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
  · rintro s c fs' (⟨h, rfl⟩ | hab)
    · exact .inl (h.elim (fun ⟨_, h⟩ => ⟨h, rfl⟩) fun ⟨e, _⟩ => e.elim)
    · exact .inr hab

/-! ## The result's store -/

/-- **The result's store into `r%n`** after the return (`retP_seg2`) with
the frame's fragment asked at the landing node only as placed: its control
at the continuation `e` (`NodeJE` in the slot file with the result's slot
`off` at `%rax`'s word), placed by the continuation's facts (`htot`, `hlb`,
`hic`), off a `ret` at no frames (`hte`). -/
theorem retP_seg2W {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {i : Expr → String → Nat → Option Nat}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Q : Ctl → Prop} {c0 : Ctl} {fs : List TermRun.Frame} (hG : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c)
    (hWR : ∀ (n : ND) blk (k0 : Int), SubCd Cd n.pc blk → n.o = oB fr → blk.length ≤ 1 →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot ∧
        SlotRepAt i lbl (rsOf fr) (Spike.Lib.upd σ.slot k0 (σ.regs.get64 .rax)) c ∧
        (fs = [] → ∀ a, c.term ≠ .ret a)) →
      CallBlk fr blk → BlkW W₀ K exe endPc R F n blk)
    {e : Expr} {s : SEnv} {off : Int} {r : Scc.IR.Reg} (hoff : rsOf fr r = some off)
    {pcR : Int64} {z : Nat} (hc : Cd pcR [(stDir off, z)])
    (htot : ∀ y ∈ Scc.Sem.exprFv e, (lookupS s y).isSome) (hlb : LocBaseRegAt s e) (hic : ImmIn i s e)
    (hte : fs = [] → ∀ a, e ≠ .ret a) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off))
      (At exe endPc R F (brN2 lbl fr fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s
        fun _ => True)) := by
  let n0 : ND := ⟨pcR, oB fr, (retCP2 p lbl R fr fp ra tp c0 fs Q pcR e s off).J⟩
  have s0 : SegW W₀ K p lbl ms0 (At exe endPc R F n0)
      (At exe endPc R F (brN2 lbl fr fp ra tp Q (fun c => FrameRunM p (c0, fs) (c, fs)) (pcR + Int64.ofNat z) e s
        fun _ => True)) := by
    refine seg_blk1 hF hR hlo hhi (hCd _ _ hc)
      (hWR n0 _ off (SubCd.whole hc) rfl (by simp) (fun σ c h =>
        ⟨hG c h.2.2.2.1, h.2.2.1, SlotRepAt.of_nodeJE h.1 htot hlb hic, fun hfs a ha => hte hfs a (h.1.1 ▸ ha)⟩)
        (.inr ⟨r, off, z, hoff, rfl⟩))
      (by simp) (okBlk_stDir hf h1 hoff z) fun σ c hJ => ⟨c, .refl c, ?_⟩
    show Hit _ (arun _ _ ⟨pcR, oB fr, σ⟩) c
    rw [arun_stDir hf h1 hoff]
    obtain ⟨hj, hen, hfj, hr, htp, -⟩ := hJ
    exact ⟨rfl, so_le_oB fr, hj, hen, frJ_upd hf hfj hoff _, hr, htp, trivial⟩
  exact s0.mono_pre fun st c h => at_rbp_addr (k := 0) h fun σ c hJ => hJ.2.2.2.2.2

/-! ## The plain call -/

/-- **A plain call of an `Accepted2` body with its blocks asked at placed
nodes** (`CallC2FW`; `callC2_ofF` at `argP_seg2W`, `callq_seg2W`,
`calleeP_seg2GW`, `retP_seg2W`): the call's `let` placed by its walk's
facts (`htot_call`, the resumption facts' walk at its head, `PtC2`), the
continuation by `CallC2R`'s facts at it, off a `ret` at no frames by
`CallC2R`'s side condition (`hte`). -/
theorem callC2_ofFW : CallC2FW := by
  intro p lbl lsize exe endPc R F K ms W fr hf h1 _h16 lcx hprog hF hR _hal D hD0 hD8 hlo hhi fp ra tp fs Cd Bl
    hCd hBl G0 hG0 i T hWB hWR hWBl hWC hTc Ab Lk hcal
  intro c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs hte hc0 hT hfresh hlp hty hg hcnt hcl ha hcode hIt hIc
    hLb hpt
  obtain ⟨rfl, rfl⟩ := hTc _ _ _ _ _ _ hT hcl
  have hG : ∀ c, LocalRun p c0 c → G0 c := fun c h => hG0 c0 c hc0 (FrameRunM.ofLocal h fs)
  have hGR : ∀ c, FrameRunM p (c0, fs) (c, fs) → G0 c := fun c h => hG0 c0 c hc0 h
  have hlo0 : R.lo ≤ -(fr.size : Int) := by omega
  have hsc : InLits lits a := hlp.1 a (by simp [headAtoms])
  have hlit : ∀ k, a = .lit k → k < 2 ^ 64 := fun k hk => hlp.2.2.2 k (by subst hk; simp [headAtoms])
  -- the walk's facts at the call's `let`
  have htot0 := htot_call (g := g) ha hIt
  have hwk0 : ImmIn i (ofEnv2 env) (.let_ x (.call g [] a []) e) ∧
      LocBaseRegAt (ofEnv2 env) (.let_ x (.call g [] a []) e) := by
    obtain ⟨_, _, _, -, -, -, hwk, -⟩ := id hpt
    have := hwk _ (mem_lowerEnvs2_head lcx env n (.let_ x (.call g [] a []) e))
    exact ⟨this.1, this.2.2.2.2⟩
  obtain ⟨hic0, hlb0⟩ := hwk0
  have hnr : ∀ b, (.let_ x (.call g [] a []) e : Expr) ≠ .ret b := fun _ h => by cases h
  obtain ⟨lw, off, zs, zc, z, hlw, hoff, hz, hc1, hb, hc3, -, hp⟩ := instsC2_call hcode
  subst hp
  -- `w`'s load into `%rdi`
  have sA := argP_seg2W (p := p) (lbl := lbl) (lsize := lsize) (K := K) (W₀ := fun s c => W s c fs)
    (ms0 := ms fs) (tp := tp) (fs := fs) (i := i)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (lits := lits) (cs := cs) (bufs := bufs)
    hf h1 hF hR hlo0 hhi hCd hG hWB hlw hz hc1 hnr
  -- `callq g`
  have sQ := callq_seg2W (p := p) (lbl := lbl) (K := K) (W₀ := fun s c => W s c fs) (ms0 := ms fs) (fp := fp)
    (ra := ra) (tp := tp) (fs := fs) (i := i) (lcx := lcx) (T := T)
    (t := .let_ x (.call g [] a []) e) (s := ofEnv2 env) (Q := fun c => EnvQ lits cs bufs lsize c.env)
    (Rn := LocalRun p c0)
    (P := fun σ => opdVal (rsOf fr) σ.slot w = some (σ.regs.get64 .rdi).toNat ∧ σ.regs.get64 .rbp = R.addr 0)
    (P' := callPP fr R w (pc + Int64.ofNat zs.sum + Int64.ofNat zc))
    hf hF hR (by omega) hhi hBl hG hWBl hb hcl ⟨x, a, e, hT⟩ htot0 hlb0 hic0 hnr fun σ ⟨hp2, hp3⟩ => by
      refine ⟨?_, ?_, ?_⟩
      · show opdVal (rsOf fr) (upd _ _ _) w = some ((σ.regs.set64 .rsp _).get64 .rdi).toNat
        rw [opdVal_upd_out hf (by omega), Reg64s.get64_set64_ne _ (by decide)]; exact hp2
      · show (σ.regs.set64 .rsp _).get64 .rbp = _
        rw [Reg64s.get64_set64_ne _ (by decide)]; exact hp3
      · show upd _ _ _ _ = _
        rw [upd_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  have sW := SegWS.liftS (W := W) fs ((sA.mono_post fun _ _ h => at_brN2_rbp h).seq sQ) (fun _ _ h => h)
  -- the callee
  have sCal := calleeP_seg2GW (p := p) (lbl := lbl) (exe := exe) (endPc := endPc) (K := K) (ms := ms) (W := W)
    (fp := fp) (ra := ra) (tp := tp) (fs := fs) (c0 := c0) (Ab := Ab) (lits := lits) (cs := cs) (bufs := bufs)
    hf hprog hF hR hD0 hD8 hlo hhi hG hWC hT hcl ha hg hfresh hoff hsc hlit hb hIt hIc hLb htot0 hlb0 hic0
    fun q frm F' hFS hCF hex hav hbl hq hpin => hcal g q frm F' hFS hCF hex hav hbl
      ⟨c0, pc, _, kk, kk', env, n, x, a, e, t, w, lits, cs, bufs, lw, zs, zc, hc0, hT, hfresh, hlp,
        hty, hg, hcnt, hcl, ha, hcode, hlw, hz, hc1, hb, hq, hpt, hpin⟩
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (retP_seg2W (p := p) (lbl := lbl) (K := K) (W₀ := fun s c => W s c fs)
    (ms0 := ms fs) (fp := fp) (ra := ra) (tp := tp) (i := i) (e := e)
    (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] a [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] a [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] a [])) lsize c.env)
    hf h1 hF hR hlo0 hhi hCd hGR hWR hoff hc3 hIt hLb hIc hte) (fun _ _ h => h)
  refine (sW.seq (SegWS.seq_left sCal sR)).mono_post ?_
  rintro s c fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj, hr, htp, -⟩, rfl⟩ | hab)
  · exact .inl ⟨rfl, c, hr, he, hn, hdc, hpc, σ, hA, hD,
      ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl c, SlotRepAt.of_nodeJE hj hIt hLb hIc⟩, htp⟩
  · exact .inr hab


end Call

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.htot_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.htot_call

/-- info: 'Spike.Lib.LowerX64.argP_seg2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.argP_seg2W

/-- info: 'Spike.Lib.LowerX64.callq_seg2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callq_seg2W

/-- info: 'Spike.Lib.LowerX64.calleeP_seg2GW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleeP_seg2GW

/-- info: 'Spike.Lib.LowerX64.retP_seg2W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retP_seg2W

/-- info: 'Spike.Lib.LowerX64.callC2_ofFW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2_ofFW
