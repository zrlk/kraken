/-
**A call's blocks inside the body's fragment at depth** (AArch64, H7a
calls): the twin of `Spike/Lib/LowerX64/CallBlkW.lean`. The obligations of
`CallPre` (`Spike/Lib/LowerA64/ProgCB.lean`) that a plain call needs, inside
`BodyWS0` at the frames `fs`, from the code's placement and phase facts.

- `blkW_bodySC`: any block of the code predicate `CdC` (`SubCd`) covered
  at its node's offsets (`okBlk`) and without a `ret` is inside `BodyWS0`
  at `fs`; a construct's block (`Kind1`) is covered (`okBlk_kind1`), and so
  are a call's argument load into `x0` (`okBlk_argLoad`, `noRet_argLoad`)
  and its result's store from `x0` (`okBlk_resStore`, `noRet_resStore`),
  which are no construct's: `Kind1` alone does not cover the call's blocks;
- `blkW_bl`: a call's `bl g` at `BlC`;
- `okBlk_chkHead_at`, `nodeW_calleeEntry`: the callee's entry at the
  caller's frame offsets (`bl` pushes nothing), at the callee's prologue
  head (`chkHead`, after `labelGap fn sc 0`, with its phase facts
  `ProPh.hd`), inside `BodyWS0` at `fs` (`call_ndSF`'s `hWC`, for a callee
  that is a code block);
- `nodeW_calleeEntry_ofCode`: the same for a callee `g` of the program
  (`p.find? (·.name == g) = some dg`), from its code facts `FnCode` (the
  prologue's placement `hpro`) and its prologue's phase facts.

Where AArch64 differs from x86-64: the callee's head `sub x9, sp, #Z; mrs
x10, tpidr_el0` writes no memory (the `stp`-like saves of `x29`/`x30` are
in the frame's set-up after the stack check, in the callee's own region),
so the callee's entry needs no room below the caller's frame
(`R.lo ≤ -frame`, not `-frame - 16`); the entry's offsets are the
caller's `oF cx` (no return address pushed); regions are 16-aligned.
-/
import Spike.Lib.LowerA64.BodyWSC
import Spike.Lib.LowerA64.NodeTp
import Spike.Lib.LowerA64.UserW
import Spike.Lib.LowerA64.ProgC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt labelGap label_labelGap)
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl blkPh noRetBlk noRet_false)
open Spike.Lib.A64ConsumerS (SFactsS)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)

/-! ## The blocks' coverage -/

section Ok

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
include hf h1 h16

/-- A construct's block is covered at the body's offsets (`kind1_ok`). -/
theorem okBlk_kind1 {blk : List Directive} (hk : Kind1 cx blk) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) blk = true :=
  kind1_ok hf h1 h16 hk

/-- **A call's argument load into `x0` is covered** at the body's offsets
(`okBlk_getOp`). -/
theorem okBlk_argLoad {w : Scc.IR.Operand} {lw : List Item} (hw : cx.getOp .X0 w = .ok lw) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) (directives lw) = true := by
  have := okBlk_getOp hf h1 h16 hw []
  rw [List.append_nil] at this
  show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
  rw [this]; rfl

/-- **A call's result store from `x0` is covered** at the body's offsets:
one `str x0, [sp, #off]` into the result's slot (`setReg_eq`). -/
theorem okBlk_resStore {d : Scc.IR.Reg} {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) (directives ls) = true := by
  obtain ⟨off, hoff, -⟩ := bind_eq_ok hs
  rw [setReg_eq hf (by omega) hoff] at hs
  cases ok_inj hs
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hoff
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hds : directives [ins (.STR (rz .W64 .X0) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] =
      [(.X0, Int64.ofInt off)].map fun q => spStr q.1 q.2 := rfl
  rw [hds]
  refine okBlk_spStrs (by simp [oF]; omega) fun q hq => ?_
  simp only [List.mem_singleton] at hq
  subst hq
  simp only [oF, ho, offOk, decide_eq_true_eq]
  omega

end Ok

/-- `movz` is no `ret`. -/
theorem noRet_movzD (d : XReg) (q : Nat × Nat) : noRetBlk [movzD d q] = true := by
  unfold movzD noRetBlk A64.Flow.classify; rfl

/-- `movk` is no `ret`. -/
theorem noRet_movkD (d : XReg) (q : Nat × Nat) : noRetBlk [movkD d q] = true := by
  unfold movkD noRetBlk A64.Flow.classify; rfl

/-- A block without `ret`, one directive at a time. -/
theorem noRetBlk_cons (a : Directive) (l : List Directive) :
    noRetBlk (a :: l) = (noRetBlk [a] && noRetBlk l) := by
  simp [noRetBlk]

/-- `movz` then `movk`s is no `ret`. -/
theorem noRet_movDs (d : XReg) : ∀ hs, noRetBlk (movDs d hs) = true
  | [] => noRet_movzD d (0, 0)
  | q :: rest => by
    show noRetBlk (movzD d q :: rest.map (movkD d)) = true
    rw [noRetBlk_cons, noRet_movzD, Bool.true_and]
    induction rest with
    | nil => rfl
    | cons x xs ih => rw [List.map_cons, noRetBlk_cons, noRet_movkD, Bool.true_and]; exact ih

/-- A call's argument load into `x0` has no `ret`. -/
theorem noRet_argLoad {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {w : Scc.IR.Operand}
    {lw : List Item} (hw : cx.getOp .X0 w = .ok lw) : noRetBlk (directives lw) = true := by
  rcases getOp_cases hf h1 hw with ⟨r, off, rfl, -, hl⟩ | ⟨v, rfl, rfl⟩
  · rw [hl]; cases off <;> rfl
  · rw [directives_movImm]
    exact noRet_movDs _ _

/-- A call's result store from `x0` has no `ret`. -/
theorem noRet_resStore {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {d : Scc.IR.Reg}
    {ls : List Item} (hs : cx.setReg d .X0 = .ok ls) : noRetBlk (directives ls) = true := by
  obtain ⟨off, hoff, -⟩ := bind_eq_ok hs
  rw [setReg_eq hf (by omega) hoff] at hs
  cases ok_inj hs
  rfl

/-- `bl g` has no `ret`. -/
theorem noRet_bl (g : Label) : noRetBlk [blD g] = true := rfl

/-- **The callee's prologue head is covered** at any `sp` offset with no
register offsets: it writes `x9` and `x10` only. -/
theorem okBlk_chkHead_at (lo hi sp : Int) (Z : Int64) : okBlk lo hi ⟨sp, []⟩ (chkHead Z) = true := by
  simp [chkHead, okBlk, A64.Flow.classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write,
    SO.kill, rm, SO.set, SO.get]

/-! ## The blocks inside `BodyWS0` -/

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl}

omit [Kraken.Executable.ValidLayout exe] in
/-- **SFacts at the held-back control lifted into `BodyWS0`**: a block
inside `SFacts` from the control `c0` (`Good1` with no frame) is inside
`BodyWS0` at the frames `fs` at a node whose pairs at `fs` are `Good1` with
no hold. -/
theorem BlkW.bodyS {n : ND} {blk : List Directive} (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame}
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none)
    (H : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
      blk) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hF hJn k hk m hA' hD
  obtain ⟨hW, hK⟩ := H s σ c0 he hn hd hpc hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨(hJ σ c hJn).1, (hJ σ c hJn).2, SFactsS.ofSFacts0 hW hp hg0⟩, hK⟩

/-- **A covered block of the code without a `ret` is inside `BodyWS0`**
at the frames `fs`: a block of the code predicate `CdC` at a return address
`ra` (`SubCd`, its phase from the run's check, `blkPh_of_runPhB`), covered
at its node's offsets (`hok`), with no `ret` (`hnr`), at a node whose pairs
at `fs` are `Good1` with no hold (`hJ`): `blkW_postO` at the held-back
control `c0` (`Good1` with no frame, its facts `hC0`), lifted to `BodyWS0`
(`BlkW.bodyS`). -/
theorem blkW_bodySC {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame} {n : ND}
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) {ra : Int64} {blk : List Directive}
    (hcd : SubCd (CdC prog okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  have he : lab L + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
  rw [hpc, ← he] at hph
  refine BlkW.bodyS hp hg0 hJ ?_
  exact Spike.Lib.A64.Rt.blkW_postO (n := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩)
    (dead := fun _ => false) (ra := ra) hI (blockAt_sub hb) he hok hR hal hlo hhi (fun _ _ h => h.1 ▸ hC0) hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO

/-- **A call's `bl g` is inside `BodyWS0`** at the frames `fs`: at `BlC`
(its placement and phase facts), at a node whose pairs at `fs` are `Good1`
with no hold, in any region holding the frame (`bl` writes `x30` only). -/
theorem blkW_bl {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : FnCtx}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame} {n : ND}
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) {ra : Int64} {g : Label} {k : Nat}
    (hbl : BlC prog okPc ph lab cx ra n.pc g k) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n [blD g] := by
  obtain ⟨L, j, hpc, hb, -, hph, -⟩ := hbl
  rw [← hpc] at hph
  refine BlkW.bodyS hp hg0 hJ ?_
  exact Spike.Lib.A64.Rt.blkW_postO (n := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩)
    (dead := fun _ => false) (ra := ra) (lo := -(cx.frame : Int)) (hi := 0) hI hb hpc
    (Spike.Lib.A64.Flow.okBlk_blD _ _ _ g) hR hal hlo hhi (fun _ _ h => h.1 ▸ hC0) hph
    (fun _ _ _ k hk r hr => (noRet_false (noRet_bl g) k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO

/-- **The callee's entry is inside `BodyWS0`** at the frames `fs`
(`call_ndSF`'s `hWC`, for a callee `fn` with a prologue): at the callee's
label, at the caller's frame offsets (`bl` pushes nothing), with the
callee's stack check label `sc` right after it (`hgap`), its head there
(`hb`) and its phase facts (`hph`, `ProPh.hd`), at a node whose pairs at
`fs` are `Good1` with no hold, in any region holding the caller's frame
(the head writes registers only): the head's block (`blkW_postO` at
`okBlk_chkHead_at`, lifted, `BlkW.bodyS`) at its first instruction
(`BlkW.nodeW`). -/
theorem nodeW_calleeEntry {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {cx : FnCtx}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame} {fn sc : Label} {Z : Int64}
    (hgap : labelGap prog fn sc 0 = true) (hb : blockAt prog sc 0 (chkHead Z) = true)
    (hph : blkPh okPc ph (fun _ => false) lab (lab sc + Int64.ofNat (4 * 0)) 0 (chkHead Z) = true)
    {n : ND} (hpc : n.pc = (_root_.Executable.labels exe).label fn) (hno : n.o = oF cx)
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) :
    ∀ s c, At exe endPc R F n s c → BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs := by
  have he : lab sc + Int64.ofNat (4 * 0) = n.pc := by
    rw [hpc, ← hI.labOk, label_labelGap hI.lays hgap, ofNat4_zero, ofNat4_zero]
  have hok : okBlk (-(cx.frame : Int)) 0 n.o (chkHead Z) = true := by
    rw [hno]; exact okBlk_chkHead_at _ _ _ Z
  have H := Spike.Lib.A64.Rt.blkW_postO (n := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩)
    (dead := fun _ => false) (ra := 0) hI hb he hok hR hal hlo hhi (fun _ _ h => h.1 ▸ hC0) hph
    (fun _ _ _ k hk r hr => (noRet_false (Spike.Lib.A64.Rt.MainU.chkHead_noRet Z) k hk r hr).elim)
    (fun _ _ _ => rfl) hl hh hsub hfit hFO
  intro s c hA
  exact (BlkW.nodeW (BlkW.bodyS (cl := cl) (ctr := ctr) hp hg0 hJ H) (by simp [chkHead]) s c hA).1

/-- **A program callee's entry is inside `BodyWS0`** (`call_ndSF`'s `hWC`
with the callee restriction): for a callee `g` of `p`
(`p.find? (·.name == g) = some dg`, the restriction's binder first) whose
code facts `c'` (at `dg`) place its prologue (`c'.hpro`) and whose
prologue's phase facts hold (`hph`, `CodeFactsS`' `ProPh`), the entry at
`g`'s user label at the caller's frame offsets: `nodeW_calleeEntry`. -/
theorem nodeW_calleeEntry_ofCode {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {cx : FnCtx} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame}
    {g : String} {dg : Decl} (hfd : p.find? (·.name == g) = some dg)
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (c' : FnCode exe prog endPc RaOk Cd i T dg)
    (hph : ProPh okPc ph lab (c'.cx.local "stack_check") (Int64.ofInt c'.cx.frame) (proL c'.cx) c'.ps)
    {n : ND} (hpc : n.pc = (_root_.Executable.labels exe).label (Scc.Lower.Names.user g)) (hno : n.o = oF cx)
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) :
    ∀ s c, At exe endPc R F n s c → BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs := by
  have hnm : dg.name = g := by simpa using List.find?_some hfd
  have hin := c'.hpro
  simp only [prologueIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hgap, hb⟩, -⟩, -⟩, -⟩, -⟩ := hin
  refine nodeW_calleeEntry hI hR hal hlo hhi hl hh hsub hfit hFO hC0 hp hg0 hgap hb hph.hd ?_ hno hJ
  rw [hpc, c'.hfn, hnm]

end W

end Spike.Lib.LowerA64
