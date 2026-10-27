/-
**A suspended caller resumed after its callee's return** (x86-64; h1's
resume walk; the twin of `Spike/Lib/LowerA64/Resume2.lean`): a callee's
segment ending at its exits (`ExitC2B` at the frames `f :: fs`) continues,
through the source's return into the caller's frame, as one segment to the
caller's exits (`ExitC2SL` at `fs`). The caller's state comes back from the
callee's frame condition pinned at the call site (`CallerAt2`); the machine,
back in the callee's entry offsets (`at_of_rbR`), leaves the callee's region
(`at_leave`) at the return address, where the source returns into the
call's result (`retCP2`); then the result's store (`retP_seg2`) and the
caller's body from the continuation (`BodyPtW.call`, `bodyAtPt2W`).

The call's sizes are the code's: the argument's load and the `callq` laid
out at a pc have one size list (`cdOf_zip_sizes`, from `CellAt`'s `codeAt`),
so the return address the call site records is the one after the
continuation's decomposition's `callq`.

- `cdOf_zip_sizes`: one size list per directive list at a pc;
- `retCP2_of_exit`: the return taken at the callee's exit, the machine left
  in the caller's region at the return address (`retCP2`);
- `callC2_resume`: the caller resumed after the callee's segment.
-/
import Spike.Lib.LowerX64.Stk2
import Spike.Lib.LowerX64.Body2SegX

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
open Spike.Lib.LowerShape (lowerC2_fv)

/-- **One size list per directive list at a pc**: two size lists of the
directives `ds` both laid out at `pc` (`CdOf`) are one, each cell's size the
one `codeAt` finds at its address (`CellAt`), given any state of the
executable. -/
theorem cdOf_zip_sizes {exe : _root_.Executable} {endPc : Int64} (s : State) (he : s.exe = exe)
    (hn : s.endPc = endPc) :
    ∀ {ds : List Directive} {pc : Int64} {zs zs' : List Nat}, zs.length = ds.length → zs'.length = ds.length →
      CdOf exe endPc pc (ds.zip zs) → CdOf exe endPc pc (ds.zip zs') → zs = zs'
  | [], _, [], [], _, _, _, _ => rfl
  | _ :: _, _, [], _, h1, _, _, _ => by simp at h1
  | _ :: _, _, _ :: _, [], _, h2, _, _ => by simp at h2
  | d :: ds, pc, z :: zr, z' :: zr', h1, h2, h, h' => by
    have c1 : ∃ rest, Kraken.Executable.codeAt s.exe (pc + Int64.ofNat 0) = (d, z) :: rest :=
      (h s he hn 0 d z rfl).code
    have c2 : ∃ rest, Kraken.Executable.codeAt s.exe (pc + Int64.ofNat 0) = (d, z') :: rest :=
      (h' s he hn 0 d z' rfl).code
    obtain ⟨r1, e1⟩ := c1
    obtain ⟨r2, e2⟩ := c2
    rw [e1] at e2
    simp only [List.cons.injEq, Prod.mk.injEq, true_and] at e2
    obtain ⟨rfl, -⟩ := e2
    have t1 := cdOf_sub (pre := [(d, z)]) (blk := ds.zip zr) (post := []) (by simpa using h)
    have t2 := cdOf_sub (pre := [(d, z)]) (blk := ds.zip zr') (post := []) (by simpa using h')
    rw [cdOf_zip_sizes s he hn (by simpa using h1) (by simpa using h2) t1 t2]

section Resume2

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **The return at the callee's exit** (`calleeP_seg2`'s return, from the
pinned caller `CallerAt2`): at the callee's exit (`retNB` at the frame's
type in the callee's rebased region, at the return address `pcR`), the
source returns from the callee's `ret` into the caller's continuation `e`
with the result bound to `x`, and the machine, back at the callee's entry
offsets (`at_of_rbR`) and left in the caller's region (`at_leave`), is at
`retCP2` at `pcR`: the continuation placed by `(x, int, [r%n]) :: env`
with `%rax` stored to `r%n`'s cell `off`, its facts against the walk
(`EnvQ`) at the call's, reached from the ghost `c0` by a frame run at
`fs`, `%rbp` the region's frame record. -/
theorem retCP2_of_exit {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {lcx : Scc.Lower.Ctx} (hprog : lcx.prog = p)
    {R : Region} {F : MachineData → Prop} {D : Int} (hD0 : 0 ≤ D) (hlo : R.lo ≤ -(fr.size : Int) - 8 - D)
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame} {c0 : Ctl} {x g : String}
    {b : At} {e : Expr} (hcl : Callee lcx g) {env : Scc.Lower.Env} {n : Nat} (hfresh : Fresh env n) {off : Int}
    (hoff : rsOf fr (regName "r" n) = some off)
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {q : CallG} {pcR : Int64}
    (hq : q.ra = pcR.toBitVec) {f : TermRun.Frame} {F' : MachineData → Prop} (hFF : ∀ m, F' m → F m)
    (hpin : CallerAt2 p lbl lsize fr R D fp ra q f F' c0 (.let_ x (.call g [] b []) e) env lits cs bufs)
    {c0E : Ctl} (hrunE : FrameRunM p (q.cE, f :: fs) (c0E, f :: fs)) {s : State} {c : Ctl}
    (h : At exe endPc (rbR (calleeR R fr.size D)) F' ((retNB p lbl q.fp q.ra c0E f.ty).withTp tp) s c) :
    ∃ c', FrameRun p (c, f :: fs) (c', fs) ∧
      At exe endPc R F (retCP2 p lbl R fr fp ra tp c0 fs
        (fun c => EnvQ ((x, Scc.Lower.opLit lcx.prog lits (.call g [] b [])) :: lits)
          (Scc.Lower.csAfter x cs (.call g [] b [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] b [])) lsize c.env)
        pcR e (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off) s c' := by
  obtain ⟨-, dd, hfd0, hretTy⟩ := hcl
  have hfd := hfd0
  rw [hprog] at hfd
  have hop : Scc.Lower.opLit lcx.prog lits (.call g [] b []) = .leaf none := by
    simp only [Scc.Lower.opLit, retShape_of_find hfd0, hretTy]; rfl
  have hgr : Spike.Lib.Form.group .int [.reg (regName "r" n)] = some [.one (.reg (regName "r" n))] := rfl
  -- the frame's cells are kept by the callee
  have hout : ∀ (r : Scc.IR.Reg) (k' : Int), rsOf fr r = some k' →
      R.Off k' ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-D) 8).Off (k' - (-(fr.size : Int) - 8)) := by
    intro r k' hk'
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk'
    exact frame_out hlo hhi hD0 hk2 (by omega) (by omega)
  have hout0 := frame_out (k := 0) hlo hhi hD0 (by decide) (by omega) (by omega)
  have hout8 := frame_out (k := 8) hlo hhi hD0 (by decide) (by omega) (by omega)
  -- back at the callee's entry offsets
  have hat : At exe endPc (calleeR R fr.size D) F' (exN2 p lbl tp fs q f c0E) s c :=
    at_of_rbR (fun σ c h => ⟨hrunE, h⟩) h
  -- the machine left in the caller's region
  have hL := at_leave (R := R) (kb := -(fr.size : Int) - 8) (lo' := -D) (hi' := 8) (e := 8)
    (P := fun σC => ∃ cC, CallTo p cC q.cE f ∧
      Spike.Lib.Form.NodeJE lbl (rsOf fr) (.let_ x (.call g [] b []) e) (ofEnv2 env) σC.slot cC ∧
      EnvQ lits cs bufs lsize cC.env ∧ FrJ fp ra σC.slot ∧ LocalRun p c0 cC ∧ q.fp = R.addr 0) rfl
    (fun m hm => by
      obtain ⟨mC, σC, cC, hA, hK, hct, hj, hen, hfj, hr, hfp⟩ := hpin m hm
      exact ⟨hFF m hm, mC, σC, _, hK, hA, cC, hct, hj, hen, hfj, hr, hfp⟩) hat
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC, hEx, ⟨cC, hct, hj, hen, hfj, hr, hfp⟩, rfl⟩ := hL
  obtain ⟨-, ⟨⟨⟨a', t', ws', hta, -, hev', -, hvr, hrbp⟩, hlr⟩, hRL⟩, htpx⟩ := hEx
  have hct' := hct
  obtain ⟨x1, f1, a1, e1, d1, t1, ws1, ht1, hfd1, -, -, hfr1⟩ := hct'
  rw [hj.1] at ht1
  cases ht1
  rw [hfd] at hfd1
  cases hfd1
  subst hfr1
  have hRL' : RetL .int c := by rw [← hretTy]; exact hRL
  obtain ⟨a2, t2, w2, ht2, he2, hnum⟩ := RetL.int hRL'
  rw [hta] at ht2
  cases ht2
  rw [hev'] at he2
  simp only [Option.some.injEq, Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl⟩ := he2
  have hstep : FrameStep p (c, ⟨x, e, cC.env, [], dd.retTy⟩ :: fs)
      (⟨e, (x, dd.retTy, [w2]) :: cC.env, none⟩, fs) := .ret hta rfl hev'
  have hvr' : ValRep lbl w2.val
      ((leave (R.callee (-(fr.size : Int) - 8) (-D) 8) (-(fr.size : Int) - 8) σC σx).regs.get64 .rax).toNat :=
    hvr 0 (by simp) (by simp [Scc.Emit.X64.retRegs])
  have hsl : ∀ k, R.Off k → ¬ (R.callee (-(fr.size : Int) - 8) (-D) 8).Off (k - (-(fr.size : Int) - 8)) →
      (leave (R.callee (-(fr.size : Int) - 8) (-D) 8) (-(fr.size : Int) - 8) σC σx).slot k = σC.slot k :=
    fun k _ hn => by simp only [leave]; exact ite_eq_right hn
  have ho : -(fr.size : Int) - 8 + 8 = -(fr.size : Int) := by omega
  rw [ho] at hA
  refine ⟨⟨e, (x, dd.retTy, [w2]) :: cC.env, none⟩, .single hstep, he, hn, hdc, ?_, _, hA, hD, ?_⟩
  · rw [hpc]
    show Int64.ofBitVec q.ra = pcR
    rw [hq, Int64.ofBitVec_toBitVec]
  refine ⟨⟨rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show Spike.Lib.Form.SRepE lbl _ (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
      ((x, dd.retTy, [w2]) :: cC.env)
    rw [ofEnv2_cons hgr, hretTy]
    refine (hj.2.2.congr fun b' hb pl hpl o ho => opdVal_upd fun r k' hr' hk' => ?_).bind x rfl
      ⟨⟨_, by simp [opdVal, hoff, upd_apply], hvr'⟩, trivial⟩
    have hne := Fresh.ofEnv2 hfresh "r" b' hb pl hpl o ho r hr'
    rw [upd_apply]
    split
    · next hk => subst hk; exact absurd (rsOf_inj hf hk' hoff) hne
    exact hsl k' (hout r k' hk').1 (hout r k' hk').2
  · obtain ⟨hl, hS, L, sm, B, hbB, hmB⟩ := hen
    refine ⟨?_, EnvSmall.cons hS (WordsSmall.isNum hnum), L, sm, B, ?_, hmB⟩
    · show EnvLit _ ((x, dd.retTy, [w2]) :: cC.env)
      rw [hop, hretTy]
      refine hl.cons rfl (NumL.of_all fun w hw => ?_)
      simp only [List.mem_singleton] at hw
      subst hw; exact hnum
    · show EnvB _ _ _ L sm lsize ((x, dd.retTy, [w2]) :: cC.env)
      rw [hop]
      exact hbB.cons (SliceL.leaf none [w2]) (fun a h => by rcases h with h | h <;> cases h)
        (fun n τ h => by cases h)
  · exact ⟨(hsl 0 hout0.1 hout0.2).trans hfj.1, (hsl 8 hout8.1 hout8.2).trans hfj.2⟩
  · exact (FrameRunM.ofLocal hr fs).trans (.step (.frame (hct.step fs))
      (hrunE.trans ((FrameRunM.ofLocal hlr _).trans (.single (.frame hstep)))))
  · exact htpx
  · exact hrbp.trans hfp

/-- **A suspended caller resumed after its callee's segment**: a segment
from `P` to the callee's exits (`ExitC2B` at the frames `f :: fs`, the
callee's rebased region below the caller's frame at room `D`, its frame
condition `F'` inside the caller's `F`, pinned at the call site:
`CallerAt2`) goes on to the caller's exits by placements (`ExitC2SL` at
`fs` in the body's region `rbR Rb`, the caller's ghost `c0`), or ends in
the callee's aborts `Ab'`. The call is `let x = g(b)` at the resumption
point `pc` of compiled block `c` (`BodyPtW`), `g` a callee (`Callee`),
`b`'s word `w` loaded into `%rdi` by `lw` of sizes `zs`, the `callq` of
size `zc` (`Bl`, its code by `hBl`), the return address `q.ra` after it.
The return (`retCP2_of_exit`), the result's store (`retP_seg2`, its block
by `hWB`), the caller's body from the continuation (`BodyPtW.call`,
`bodyAtPt2W` with its premises at the caller's context). -/
theorem callC2_resume [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {RaOk : BitVec 64 → Prop}
    {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop} {i : Expr → String → Nat → Option Nat}
    {T : Expr → Prop} {d : Decl} (c : FnCode2 exe cells endPc RaOk Cd i T d) (hprog : c.lcx.prog = p)
    {Rb : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab : FragS isa} {W₀ : Frag isa} (hra : RaOk ra) (hF : FStable Rb F) (hR : Rb.OK)
    (hlob : Rb.lo ≤ -8 - (c.fr.size : Int)) (hhib : 8 ≤ Rb.hi) {D : Int} (hD0 : 0 ≤ D)
    (hlo : (rbR Rb).lo ≤ -(c.fr.size : Int) - 8 - D) (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hG0 : ∀ c c', G0 c → FrameRunM p (c, fs) (c', fs) → G0 c')
    (hBl : ∀ pc zc g k, c.Bl ra pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    (hWB : ∀ (n : ND) blk, SubCd (Cd ra) n.pc blk → n.o = oB c.fr →
      okBlk (-(c.fr.size : Int)) 16 (oB c.fr) blk = true → noRetBlk blk = true →
      (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) → BlkW W₀ K exe endPc (rbR Rb) F n blk)
    (hW : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk →
      BlkW W₀ K exe endPc (rbR Rb) F (bodyN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs) blk)
    (hWp : ∀ c0, G0 c0 → ∀ pc t s lits cs bufs k blk, SubCd (Cd ra) pc blk → Kind2 c.fr blk → blk.length ≤ 1 →
      BlkW W₀ K exe endPc (rbR Rb) F (pendN2 p lbl lsize i c.fr fp ra c0 pc t s lits cs bufs k) blk)
    (hab : ∀ c0, G0 c0 → ∀ s c',
      At exe endPc (rbR Rb) F (abortN2 i T p lbl c.fr (_root_.Executable.labels exe).label fp ra c0) s c' →
        Ab s c' fs)
    (hcon : CallC2 p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR Rb) F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      LaneC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR Rb) F W K ms fp ra tp fs G0 i T Ab ∧
      NewBufC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR Rb) F W K ms fp ra tp fs G0 i T Ab
        (RetLk d.retTy) ∧
      PrintCallC p lbl lsize c.lcx c.fr (Cd ra) (c.Bl ra) exe endPc (rbR Rb) F W K ms fp ra tp fs G0 i T Ab)
    {c0 : Ctl} (hg0 : G0 c0) {pc : Int64} {x g : String} {b : At} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hpt : BodyPtW c ra pc (.let_ x (.call g [] b []) e) env n lits cs bufs) (hcl : Callee c.lcx g)
    {t : Ty} {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item} {zs : List Nat} {zc kk : Nat}
    (ha : atomV env b = some (t, [w])) (hw : getOp c.fr .rdi w = .ok lw) (hz : zs.length = (dirs lw).length)
    (hc1 : Cd ra pc ((dirs lw).zip zs)) (hb : c.Bl ra (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) kk)
    {q : CallG} (hq : q.ra = (pc + Int64.ofNat zs.sum + Int64.ofNat zc).toBitVec)
    {f : TermRun.Frame} {F' : MachineData → Prop} (hFF : ∀ m, F' m → F m)
    (hpin : CallerAt2 p lbl lsize c.fr (rbR Rb) D fp ra q f F' c0 (.let_ x (.call g [] b []) e) env lits cs bufs)
    {P Ab' : FragS isa}
    (hseg : SegWS W K p lbl ms P (ExitC2B p lbl exe endPc (rbR (calleeR (rbR Rb) c.fr.size D)) F' q.fp q.ra tp
      q.cE (f :: fs) f.ty Ab')) :
    SegWS W K p lbl ms P (fun s c' fs' => ExitC2SL p lbl exe endPc (rbR Rb) F fp ra tp c0 fs d.retTy Ab s c' fs' ∨
      Ab' s c' fs') := by
  have hf := c.hf
  have h1 := c.h1
  have hCd := c.hCd ra hra
  obtain ⟨hF', hR', hlo', hhi'⟩ := rbR_facts (size := c.fr.size) hF hR hlob hhib
  -- the call's code and the continuation's resumption point
  have hpt0 := hpt
  obtain ⟨-, -, -, -, -, hfresh, -, -, -, -, -, -⟩ := hpt0
  obtain ⟨dg, t', w', kk1, kk1', pc', -, -, ha', hi, hpt'⟩ := hpt.call hcl.1
  rw [ha] at ha'
  cases ha'
  obtain ⟨lw', off, zs', zc', z, hlw', hoff, hz', hc1', hb', hc3, -, hp⟩ := instsC2_call hi
  rw [hw] at hlw'
  cases hlw'
  have hpt'0 := hpt'
  obtain ⟨l', k', r', kk', hr', -, -, -, hWs', -, -, -⟩ := hpt'0
  have hh' := walk2_head hWs'
  -- the callee's exit to the return node
  have sE : SegWS W K p lbl ms P (fun s c' fs' =>
      (At exe endPc (rbR Rb) F (retCP2 p lbl (rbR Rb) c.fr fp ra tp c0 fs
        (fun c1 => EnvQ ((x, Scc.Lower.opLit c.lcx.prog lits (.call g [] b [])) :: lits)
          (Scc.Lower.csAfter x cs (.call g [] b [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] b [])) lsize c1.env)
        (pc + Int64.ofNat zs'.sum + Int64.ofNat zc') e
        (ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env)) off)).at fs s c' fs' ∨
      Ab' s c' fs') := by
    refine SegWS.post_run (hseg.mono_post ?_)
    rintro s c' fs' (⟨rfl, c0E, hrunE, hA⟩ | hab')
    · have hzs : zs = zs' := cdOf_zip_sizes s hA.1 hA.2.1 hz hz' (hCd _ _ hc1) (hCd _ _ hc1')
      subst hzs
      have hzc : [zc] = [zc'] := cdOf_zip_sizes (ds := [_]) s hA.1 hA.2.1 rfl rfl (hBl _ _ _ _ hb) (hBl _ _ _ _ hb')
      cases hzc
      obtain ⟨c'', hrun, hA'⟩ := retCP2_of_exit hf hprog hD0 hlo hhi' hcl hfresh hoff hq hFF hpin hrunE hA
      exact ⟨c'', fs, hrun, .inl ⟨hA', rfl⟩⟩
    · exact Pend.of (.inr hab')
  -- the result's store
  have sR := SegWS.liftS (W := W) fs (retP_seg2 (p := p) (lbl := lbl) (K := K) (W₀ := W₀) (ms0 := ms fs)
    (fp := fp) (ra := ra) (tp := tp) (e := e) (s := ofEnv2 ((x, .int, [.reg (regName "r" n)]) :: env))
    (Q := fun c1 => EnvQ ((x, Scc.Lower.opLit c.lcx.prog lits (.call g [] b [])) :: lits)
      (Scc.Lower.csAfter x cs (.call g [] b [])) (Scc.Lower.bufsAfter x cs bufs (.call g [] b [])) lsize c1.env)
    hf h1 hF' hR' hlo' hhi' hCd (fun c h => hG0 c0 c hg0 h) hWB hoff hc3) hW₀
  -- to the continuation's node
  have sC : SegWS W K p lbl ms P (ContC p lbl lsize i c.fr exe endPc (rbR Rb) F fp ra tp c0 fs Ab' pc' e
      ((x, .int, [.reg (regName "r" n)]) :: env)
      ((x, Scc.Lower.opLit c.lcx.prog lits (.call g [] b [])) :: lits) (Scc.Lower.csAfter x cs (.call g [] b []))
      (Scc.Lower.bufsAfter x cs bufs (.call g [] b []))) := by
    refine (SegWS.seq_left sE sR).mono_post ?_
    subst hp
    rintro s c' fs' (⟨⟨he, hn, hdc, hpc, σ, hA, hD, hj, ⟨hl, hS, L, sm, B, hbB, hmB⟩, hfj, hrr, htp, -⟩, rfl⟩ | hab')
    · exact .inl ⟨rfl, c', hrr, he, hn, hdc, hpc, σ, hA, hD,
        ⟨⟨L, sm, B, NJB.of_nodeJE hj hl hbB hmB hS⟩, hfj, .refl c',
          SlotRepAt.of_nodeJE hj (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv c.lcx _ _ _ _ _ _ hr' y hy))
            hh'.2.2.2.2 hh'.1⟩, htp⟩
    · exact .inr hab'
  -- the caller's body from the continuation
  exact seg_contX (X := fun c0 s c' fs' => ExitC2SL p lbl exe endPc (rbR Rb) F fp ra tp c0 fs d.retTy Ab s c' fs' ∨
      Ab' s c' fs') hG0
    (fun c0 c0' hr0 s c' fs' (h : _ ∨ _) => h.imp_left (ExitC2SL.trans hr0 s c' fs'))
    (fun _ _ _ _ h => Or.inr h) hg0 sC fun c0' hg0' =>
      (bodyAtPt2W c hra hF hR hlob hhib hW₀ hG0 hW hWp hab hcon hpt' hg0').mono_post fun _ _ _ h => Or.inl h

end Resume2

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.cdOf_zip_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cdOf_zip_sizes

/-- info: 'Spike.Lib.LowerX64.retCP2_of_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retCP2_of_exit

/-- info: 'Spike.Lib.LowerX64.callC2_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callC2_resume
