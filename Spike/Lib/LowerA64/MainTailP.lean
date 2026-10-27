/-
**`main`'s return tail after an output call, end to end** (AArch64): the
print arm of `mainTailA_seg` (`Spike/Lib/LowerA64/MainTailA.lean`), `main`
ending `let x = print … in ret a` (hello1's `print …; ret 0`). The source
is held at `print`'s `ret ()` (`PrintCallCH`), which reads nothing: its
`Ret0` is the literal disjunct (`exprFv c.term = []`), no result cell.

The held node `heldRNU` is `heldRN`'s with the held control reading
nothing; the block of `main`'s `ret a` is one segment from it to
`ExitC2SLF`, its states inside `W2` at the held frames (`blkW_heldTail`):
`SFacts` by `blkW_sfacts_ret2`, `HeldS` by `blkW_heldS` from the write
abort's phase (`blkW_abSt_ret2`), `Ret0` from the held control
(`blkW_ret0_nil`), no write and no system call.

- `heldRNU`, `BlkEdge.heldRNU`, `exitC2SLF_of_heldRNU`: the held node with
  a control reading nothing, a block's edge lifted to it, the return's exit
  there;
- `blkW_ret0_nil`: `Ret0` along a block at such a node;
- `blkW_abSt_ret2`: `main`'s `ret` block keeps the write abort's phase at
  any node with the frame's offsets and saved pair (`FrJ`);
- `mainTailA_segP`: the tail as one segment;
- `heldP_segA`: from `PrintCallCH`'s held pairs to the exits;
- `heldTailCX_of`: `HeldTailCX`'s instance, the call arm by `mainTailA_seg`,
  the print arm by `heldP_segA`.
-/
import Spike.Lib.LowerA64.MainTailA
import Spike.Lib.LowerA64.HeldC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (WordPl group)
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)

/-- **A node at a held pair whose control reads nothing** (`heldRN` with
`exprFv c.term = []`, e.g. `print`'s `ret ()`). -/
def heldRNU (p : Prog) (fs : List TermRun.Frame) (n : ND) : ND :=
  ⟨n.pc, n.o, fun σ c => Scc.Sem.exprFv c.term = [] ∧ (heldRN p fs n).J σ c⟩

section HeldRNU

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : FragS isaLSE2} {K : State → State → Prop}

/-- **A block's edge lifted to the held nodes reading nothing**
(`BlkEdge.heldRN`): the held source takes no step. -/
theorem BlkEdge.heldRNU {lab : Label → Int64} {lo hi : Int} {n : ND} {blk : List Directive}
    {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (h : BlkEdge p lab lo hi n blk N E) (fs : List TermRun.Frame) :
    BlkEdge p lab lo hi (heldRNU p fs n) blk (fun j => heldRNU p fs (N j)) (fun x => heldRNU p fs (E x)) := by
  refine ⟨h.1, h.2.1, fun σ c ⟨hv, hH, cR, hr, hJ⟩ => ?_⟩
  obtain ⟨c', hr', hL⟩ := h.2.2 σ cR hJ
  have hrr : FrameRun p (c, fs) (c', []) := hr.trans (FrameRun.ofLocal hr' [])
  refine ⟨c, .refl c, ?_⟩
  rcases hL with ⟨j, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩
  · exact .inl ⟨j, h1, h2, hv, hH, c', hrr, h3⟩
  · exact .inr ⟨x, h1, h2, hv, hH, c', hrr, h3⟩

/-- **The return's exit at a held pair reading nothing is `ExitC2SLF`**
(`exitC2SLF_of_heldRN`). -/
theorem exitC2SLF_of_heldRNU {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl} {ty : Ty} {Ab : FragS isaLSE2}
    {fs : List TermRun.Frame} (hr : FrameRunM p (c0, []) (c0', [])) {s : State} {c : Ctl}
    (h : At exe endPc R F (heldRNU p fs ((retNSL p lbl fp ra c0' ty).withTp tp)) s c) :
    ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab s c fs := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hF, -, -, cR, hrR, hJ⟩ := h
  exact .inl ⟨cR, hrR, c0', hr, he, hn, hdc, hpc, σ, hA, hF, hJ⟩

/-- **`Ret0` along a block at a node whose controls read nothing** (the
literal disjunct). -/
theorem blkW_ret0_nil {lbl : Lbl} {n : ND} {blk : List Directive}
    (hJ : ∀ σ c, n.J σ c → Scc.Sem.exprFv c.term = []) :
    BlkW (Ret0 lbl) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJn k hk m hA' _
  exact ⟨.inl (hJ σ c hJn), fun _ h => h⟩

end HeldRNU

/-- **`main`'s `ret` block keeps the write abort's phase**
(`blkW_abSt_subCdLR`, `retHeld_hab` at any node): at a node with the
frame's offsets (`hno`) whose controls have the saved pair in their cells
(`hfj`), the block a part of the code off the write abort's labels at the
saved `ra` (`hcd`), `ra` a position off the write abort (`hpos`). -/
theorem blkW_abSt_ret2 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    {R : Region} {F : MachineData → Prop} {n : ND} {fp ra : BitVec 64} (hno : n.o = oF cx)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot)
    (hcd : SubCd (CdCL prog okPc ph lab (Int64.ofBitVec ra)) n.pc (directives (ls ++ cx.leave ++ [ret])))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hpos : PosOff prog lab (Int64.ofBitVec ra)) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s) (fun _ _ => False) exe endPc R F n
      (directives (ls ++ cx.leave ++ [ret])) := by
  refine blkW_abSt_subCdLR hI hpr habt hcd (hno ▸ okBlk_ret2 hf h1 h16 hl) hR hal hlo hhi
    (hret_ret2 hf h1 h16 hno hfj hl) (.inl (retBlk_last hf h1 ls)) ?_
  intro σ c _ k hk a ha t ht hc
  rcases retBlk_fallR hf h1 hl _ (List.getElem_mem hk) a ha with hfa | ⟨r, rfl⟩
  · rcases hc with hc | ⟨r, rfl⟩
    · cases a <;> simp only [fallI, Bool.false_eq_true] at hfa <;>
        simp only [aiTgts, List.mem_singleton] at ht <;> exact absurd ht hc
    · simp [fallI] at hfa
  · simp only [aiTgts, List.mem_singleton] at ht
    exact .inl (ht ▸ hpos)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : List TermRun.Frame → MemSide isaLSE2} {W : FragS isaLSE2}
  {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}

/-- **`main`'s return tail after an output call is one segment to
`ExitC2SLF`** (`mainTailA_seg`'s print arm): from the held node reading
nothing (`heldRNU`, the source at `print`'s `ret ()`) of the `ret a`
block's `bodyN2`, `ret_edgeSL` lifted, the block's states inside `W2` at
the held frames (`blkW_heldTail`; `SFacts` by `blkW_sfacts_ret2`, `HeldS`
by `blkW_heldS` from `blkW_abSt_ret2` and `blkW_ret0_nil`). The premises
are `mainTailA_seg`'s but the held call's: the frame and the region, the
runtime's facts, the block of the code at `main`'s return address `ra`
(`hcd`), `ra` off the write abort (`hpos`), the returned atom's placements
and layout at any symbolic environment `s`, the frame run to the ghost
`c0'` (`hr`), `W` from `W2` (`hW₀`). -/
theorem mainTailA_segP (hp : ProgNoS ZBad p) {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL prog okPc ph lab (Int64.ofBitVec ra)) pc (directives (ls ++ cx.leave ++ [ret])))
    (hpos : PosOff prog lab (Int64.ofBitVec ra))
    {s : Spike.Lib.Form.SEnv} {a : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt s a = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits a)
    (hlit : ∀ n, a = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits a).erase = Scc.Lower.shapeOf ty)
    {fs : List TermRun.Frame} {tp : UInt64} {c0 c0' : Ctl} (hr : FrameRunM p (c0, []) (c0', []))
    (hW₀ : ∀ st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize st c fs → W st c fs)
    {Ab : FragS isaLSE2} :
    SegWS W K p lbl ms
      ((At exe endPc R F (heldRNU p fs ((bodyN2 p lbl lsize i cx fp ra c0' pc (.ret a) s lits cs bufs).withTp
        tp))).at fs)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  have hok := okBlk_ret2 hf h1 h16 hl
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc →
      CodeAt st pc (directives (ls ++ cx.leave ++ [ret])) :=
    SubCd.cdOf (fun _ _ h => by
      obtain ⟨-, L, j, hpc, hb, -⟩ := CdCL.toCdC h
      exact Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (by rw [hI.labOk]; exact hpc)) hcd
  have hfj : ∀ σ c, (heldRNU p fs ((bodyN2 p lbl lsize i cx fp ra c0' pc (.ret a) s lits cs bufs).withTp
      tp)).J σ c → FrJ fp ra σ.slot := fun _ _ ⟨_, _, _, _, ⟨⟨_, hfj, _⟩, _⟩⟩ => hfj
  have hS := blkW_sfacts_ret2 (lbl := lbl) hI hf h1 h16 hR hal hlo hhi hl8 hh8 hsub hfit hFO rfl hfj hl
    (hcd.mono fun _ _ h => CdCL.toCdC h)
  have hab := blkW_abSt_ret2 (F := F) hI hpr habt hf h1 h16 hl rfl hfj hcd hR hal hlo hhi hpos
  have hW := blkW_heldTail (Λ := Λ) (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) hp hS
    (fun _ _ h => h.2.1)
    (blkW_heldS hab (blkW_ret0_nil (lbl := lbl) fun _ _ h => h.1) (blkW_noWr' hcode hok hR hal hlo (by omega))
      (blkW_noSys' hcode hok))
  have he := (ret_edgeSL (p := p) (lbl := lbl) (lsize := lsize) (fp := fp) (ra := ra) (c0 := c0') (pc := pc)
    (lits := lits) (cs := cs) (bufs := bufs) (i := i) hf h1 h16 hl hn (_root_.Executable.labels exe).label
    hsa hg hsc hlit hera).tp tp
  exact (SegWS.liftS fs (((he.heldRNU fs).seg hF hR hal hlo hhi hcode hW).mono_post
    fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim) hW₀).mono_post
    fun _ _ _ ⟨h, hfs⟩ => hfs ▸ exitC2SLF_of_heldRNU hr h

/-- **From an output call held at `print`'s `ret ()` to the exits**
(`held_segX`'s print arm, at `heldRNU`): the source held at a `ret ()` one
frame above `main` (`HeldC` of `ContC` at `ret b` with the held control's
term `ret ()`, `PrintCallCH`'s post; `b` a literal or the call's result
`x`) is at `heldRNU` of the node at `ret b` at the frame (`HeldTail` by
`heldTail_of_frame`, the return step its run, the control reading
nothing); `mainTailA_segP` from each such node. The premises are
`mainTailA_segP`'s at the continuation's symbolic environment
`ofEnv2 env'`, `W` from `W2` at each held frame (`hW₀`). -/
theorem heldP_segA (hp : ProgNoS ZBad p) {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls)
    (hn : vs.length ≤ argRegs.length) {pc : Int64} {fp ra : BitVec 64}
    (hcd : SubCd (CdCL prog okPc ph lab (Int64.ofBitVec ra)) pc (directives (ls ++ cx.leave ++ [ret])))
    (hpos : PosOff prog lab (Int64.ofBitVec ra))
    {env' : Scc.Lower.Env} {b : At} {t : Ty} {pls : List WordPl}
    (hsa : Spike.Lib.Form.sevalAt (ofEnv2 env') b = some (t, pls))
    (hg : group t vs = some pls) {i : Expr → String → Nat → Option Nat} {ty : Ty} (hsc : InLits lits b)
    (hlit : ∀ n, b = .lit n → n < 2 ^ 64) (hera : (Scc.Lower.litAt lits b).erase = Scc.Lower.shapeOf ty)
    {x : String} (hbx : (∃ k, b = .lit k) ∨ b = .var x) {tp : UInt64} {c0 : Ctl}
    (hW₀ : ∀ f st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize st c [f] → W st c [f])
    {Ab : FragS isaLSE2} :
    SegWS W K p lbl ms
      (fun s c fs' => HeldC p (ContC p lbl lsize i cx exe endPc R F fp ra tp c0 [] (fun _ _ _ => False) pc (.ret b)
        env' lits cs bufs) [] x (.ret b) s c fs' ∧ c.term = .ret .unit)
      (ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  refine (SegWS.exists_pre (P := fun g : {q : TermRun.Frame × Ctl // FrameRunM p (c0, []) (q.2, [])} =>
      (At exe endPc R F (heldRNU p [g.1.1] ((bodyN2 p lbl lsize i cx fp ra g.1.2 pc (.ret b) (ofEnv2 env') lits cs
        bufs).withTp tp))).at [g.1.1])
    fun g => mainTailA_segP hp hI hpr habt hf h1 h16 hF hR hal hlo hhi hl8 hh8 hsub hfit hFO hl hn hcd hpos hsa hg
      hsc hlit hera g.2 (hW₀ g.1.1)).mono_pre ?_
  rintro s c fs' ⟨⟨a, f, cR, hc, rfl, hfx, hfb, hst, hQ⟩, ht⟩
  rcases hQ with ⟨-, c0', hrun, he, hn, hd, hpc, σ, hA, hFm, hJ⟩ | hQ
  · have hσ : f.σs = [] := by
      cases hst with
      | ret _ hσ _ => exact hσ
    exact ⟨⟨(f, c0'), hrun⟩, ⟨he, hn, hd, hpc, σ, hA, hFm, by rw [ht]; rfl,
      heldTail_of_frame hc hσ hfx hfb hbx, cR, .single hst, hJ⟩, rfl⟩
  · exact hQ.elim

open Spike.Lib.LowerShape (lowerC2_call_inv lowerC2_ret_inv walk2_tail_call walk2_tail_print lowerC2_fv) in
/-- **`main`'s held return tail to `ExitC2SLF`** (`HeldTailCX`'s instance;
the twin of the x86-64 `heldTailCX_of`): the call's segment held at the
callee's `ret` (`CallC2H`, `PrintCallCH`), then `main`'s `ret b` block at
the held pair to the return's exit there: a plain call's by `held_segX` and
`mainTailA_seg` (the held frame's result cell), an output call's by
`heldP_segA` (the held control `print`'s `ret ()`). The frame, the region
and the runtime's facts as `mainTailA_seg`'s; the code at `main`'s return
address `ra` (`hCd`), `ra` off the write abort (`hpos`); `W` from `W2` at
each held frame (`hW₀`). -/
theorem heldTailCX_of (hp : ProgNoS ZBad p) {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) (hl8 : R.lo % 8 = 0) (hh8 : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab (Int64.ofBitVec ra) pc blk)
    (hpos : PosOff prog lab (Int64.ofBitVec ra))
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isaLSE2}
    {lcx : Scc.Lower.Ctx} (hfrm : lcx.frames = none) {tp : UInt64} {ty : Ty}
    (hcallH : CallC2H p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T Ab (RetLk ty))
    (hprintH : PrintCallCH p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T Ab)
    (hW₀ : ∀ f st c, W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize st c [f] →
      W st c [f]) :
    HeldTailCX p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp [] G0 i T (fun _ => True) (RetLk ty)
      (fun c0 => ExitC2SLF p lbl exe endPc R F fp ra tp c0 [] ty Ab) := by
  intro c0 pc kk env n x g is a ts b lits cs bufs l k r hG hr hfr hcode hbl hWk hL hC hX hbx
  have hh0 := walk2_head hWk
  have hL0 := (hL (.let_ x (.call g is a ts) (.ret b), lits) (by simp [Scc.Lower.litWalk2])).1
  have hnr : ∀ ws : List Scc.IR.Operand, ws.length ≤ Scc.IR.maxRets → ws.length ≤ argRegs.length := by
    intro ws hm
    have : argRegs.length = 8 := rfl
    have : Scc.IR.maxRets = 6 := rfl
    omega
  rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hdg, hrt, ha, hr', rfl⟩
      | ⟨xe, dg, t, bo, o, m, cw, r', hx, hdg, hrt, ha, hr', rfl⟩
  · obtain ⟨tb, ws, hab, rfl⟩ := lowerC2_ret_inv hr'
    obtain ⟨pc', hi, hrest⟩ := (CodeC2_append _ [_] kk pc).1 hcode
    have hW' := walk2_tail_call hfrm hx hdg hrt ha hWk
    have hh := walk2_head hW'
    have hlb := hL (.ret b, (x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits)
      (by simp [Scc.Lower.litWalk2])
    obtain ⟨hm, ls, hl, hc⟩ := codeC2_retN hrest
    obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hh.2.2.2.2.1 hab
    refine (SegWS.seq_left (hcallH c0 pc pc' kk env n x g is a ts (.ret b) t w lits cs bufs hG hh0.2.1 hfr hL0
        hh0.2.2.2.1 hh0.2.2.2.2.1 hC ⟨hx, dg, hdg, hrt⟩ ha hi
        (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx _ _ _ _ _ _ hr' y hy)) hh.1 hh.2.2.2.2.2
        ⟨l, k, _, hr, hcode, hbl, fun q hq =>
          ⟨(hWk q hq).1, (hWk q hq).2.1, (hWk q hq).2.2.2.1, (hWk q hq).2.2.2.2.1, (hWk q hq).2.2.2.2.2⟩, hL, hC,
          hX⟩)
      (held_segX hbx fun f c0' hrun hfx _ => ?_)).mono_post fun s c fs' h => h.elim id .inr
    exact mainTailA_seg hp hI hpr habt hf h1 h16 hF hR hal hlo hhi hl8 hh8 hsub hfit hFO hl (hnr ws hm)
      (hc.mono hCd) hpos hsa hpl (hlb.1.1 b (by simp [headAtoms]))
      (fun k hk => hlb.1.2.2.2 k (by subst hk; simp [headAtoms])) (hlb.2.2 b rfl) hi
      (fun _ h => by cases h; exact hfx) hrun (hW₀ f)
  · obtain ⟨tb, ws, hab, rfl⟩ := lowerC2_ret_inv hr'
    obtain ⟨pc', hi, hrest⟩ := (CodeC2_append _ _ kk pc).1 hcode
    have hW' := walk2_tail_print hx hdg hrt ha hWk
    have hh := walk2_head hW'
    have hlb := hL (.ret b, (x, Scc.Lower.opLit lcx.prog lits (.call g is a ts)) :: lits)
      (by simp [Scc.Lower.litWalk2])
    obtain ⟨hm, ls, hl, hc⟩ := codeC2_retN hrest
    obtain ⟨pls, hpl, hsa⟩ := sevalAt_ofEnv2G hh.2.2.2.2.1 hab
    exact (SegWS.seq_left (hprintH c0 pc pc' kk env n x g is a ts (.ret b) xe dg t bo o m cw lits cs bufs hG
        hh0.2.1 hfr hL0 hh0.2.2.2.1 hh0.2.2.2.2.1 hC
        (by
          rw [← argShape_of_find hdg]
          exact (hL (.let_ x (.call g is a ts) (.ret b), lits) (by simp [Scc.Lower.litWalk2])).2.1 x g is a ts _ rfl)
        hx hdg hrt ha hi (fun y hy => isSome_lookupS_ofEnv2 (lowerC2_fv lcx _ _ _ _ _ _ hr' y hy)) hh.1
        hh.2.2.2.2.2)
      (heldP_segA hp hI hpr habt hf h1 h16 hF hR hal hlo hhi hl8 hh8 hsub hfit hFO hl (hnr ws hm) (hc.mono hCd)
        hpos hsa hpl (hlb.1.1 b (by simp [headAtoms])) (fun k hk => hlb.1.2.2.2 k (by subst hk; simp [headAtoms]))
        (hlb.2.2 b rfl) hbx hW₀)).mono_post fun s c fs' h => h.elim id .inr

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_ret2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_abSt_ret2

/-- info: 'Spike.Lib.LowerA64.mainTailA_segP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainTailA_segP

/-- info: 'Spike.Lib.LowerA64.heldP_segA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.heldP_segA

/-- info: 'Spike.Lib.LowerA64.heldTailCX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.heldTailCX_of
