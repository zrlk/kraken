/-
**A call's blocks inside the body's fragment at depth** (x86-64, H7a
calls): the obligations of `CallPre` (`Spike/Lib/LowerX64/ProgCB.lean`)
that a plain call needs, inside `BodyWS0` at the frames `fs`, from the
code's placement and phase facts.

- `blkW_bodySC`: any block of the code predicate `CdC` (`SubCd`) covered
  at its node's offsets (`okBlk`) and without a `ret` is inside `BodyWS0`
  at `fs` (`CallPre`'s `hWB`); a
  construct's block (`Kind1`) is covered (`okBlk_kind1`; all but a `ret`'s
  are `ret`-free), and so is a call's argument load into `%rdi`
  (`okBlk_argLoad`, `noRet_argLoad`), which is no construct's: `Kind1`
  alone does not cover the call's blocks;
- `blkW_callq`: a call's `callq g` at `BlC` (`CallPre`'s `hWBl`);
- `okBlk_xHead_call`, `nodeW_calleeEntry`: the callee's entry `8` below
  the caller's frame, at the callee's prologue head (`blockAtB … xHead`
  with its phase facts, `ProPh.hd`), inside `BodyWS0` at `fs`
  (`CallPre`'s `hWC`, for a callee that is a code block,
  the region holding the head's push below the return address).
-/
import Spike.Lib.LowerX64.BodyWSC
import Spike.Lib.LowerX64.NodeTp
import Spike.Lib.LowerX64.UserW

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (xHead)
open Scc.Lower.InvX64
open Scc.Emit.X64 (i64 rel)
open Scc.Cert.Rt.X64 (blockAt blockAtB)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl blkPh noRetBlk noRet_false)
open Spike.Lib.X64ConsumerS (SFactsS)
open Spike.Lib.X64.Rt (InstOk blkW_postO)
open Spike.Lib.X64.Flow.Ret0 (StackOff)

/-! ## The blocks' coverage -/

section Ok

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
include hf h1

/-- A construct's block is covered at the body's offsets (`kind1_ok`). -/
theorem okBlk_kind1 {blk : List (Directive × Nat)} (hk : Kind1 fr blk) :
    okBlk (-(fr.size : Int)) 16 (oB fr) blk = true :=
  kind1_ok hf h1 hk

/-- **A call's argument load into `%rdi` is covered** at the body's
offsets (`okBlk_getOp`). -/
theorem okBlk_argLoad {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item} (hw : getOp fr .rdi w = .ok lw)
    {zs : List Nat} (hz : zs.length = (dirs lw).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs lw).zip zs) = true := by
  have := okBlk_getOp hf h1 (by decide) (by decide) hw hz []
  rw [List.append_nil] at this
  rw [this]; rfl

end Ok

/-- A call's argument load into `%rdi` has no `ret`. -/
theorem noRet_argLoad {fr : Scc.Emit.X64.Frame} {w : Scc.IR.Operand} {lw : List Scc.Emit.X64.Item}
    (hw : getOp fr .rdi w = .ok lw) {zs : List Nat} (hz : zs.length = (dirs lw).length) :
    noRetBlk ((dirs lw).zip zs) = true := by
  rcases getOp_cases hw with ⟨r, off, rfl, -, hl⟩ | ⟨v, rfl, hl⟩
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    rfl
  · rw [hl] at hz ⊢
    obtain ⟨z, rfl⟩ := length_one hz
    rfl

/-- `callq g` is covered when the return address's cell is. -/
theorem okBlk_callqC {lo hi : Int} {o : SO} (g : String) (z : Nat) (h : offOk lo hi (o.sp - 8) = true) :
    okBlk lo hi o [(i64 (.call (rel g)), z)] = true := by
  simp [okBlk, i64, Scc.Emit.X64.op, rel, X64.classify, AI.ok, AI.isTerm, h]

/-- `callq g` has no `ret`. -/
theorem noRet_callq (g : String) (z : Nat) : noRetBlk [(i64 (.call (rel g)), z)] = true := rfl

/-- **The callee's prologue head is covered at the callee's entry** `8`
below the caller's frame (the return address pushed), when the region
holds the saved `%rbp`'s cell `16` below the frame. -/
theorem okBlk_xHead_call (fr : Scc.Emit.X64.Frame) {lo hi : Int} (hlo : lo ≤ -(fr.size : Int) - 16)
    (h8 : (fr.size : Int) % 8 = 0) (hhi : -(fr.size : Int) - 8 ≤ hi) :
    okBlk lo hi { oB fr with sp := (oB fr).sp - 8 } xHead = true := by
  simp [xHead, okBlk, X64.classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, SO.get, SO.set, SO.kill, rm,
    offOk, oB]
  omega

/-! ## The blocks inside `BodyWS0` -/

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl}

omit [Kraken.Executable.ValidLayout exe] in
/-- **SFacts at the held-back control lifted into `BodyWS0`**: a block
inside `SFacts` from the control `c0` (`Good1` with no frame) is inside
`BodyWS0` at the frames `fs` at a node whose pairs at `fs` are `Good1` with
no hold. -/
theorem BlkW.bodyS {n : ND} {blk : List (Directive × Nat)} (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame}
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none)
    (H : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
      blk) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n blk := by
  intro s σ c he hn hd hpc hA hF hJn k hk m hA' hD
  obtain ⟨hW, hK⟩ := H s σ c0 he hn hd hpc hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨(hJ σ c hJn).1, (hJ σ c hJn).2, SFactsS.ofSFacts0 hW hp hg0⟩, hK⟩

/-- **A covered block of the code without a `ret` is inside `BodyWS0`**
at the frames `fs` (`CallPre`'s `hWB`): a block of the
code predicate `CdC` at a return address `ra` (`SubCd`, its phase from the
run's check, `blkPh_of_runPhB`), covered at its node's offsets (`hok`), with
no `ret` (`hnr`), at a node whose pairs at `fs` are `Good1` with no hold
(`hJ`): `blkW_postO'` at the held-back control `c0` (`Good1` with no frame,
its facts `hC0`), lifted to `BodyWS0` (`BlkW.bodyS`). -/
theorem blkW_bodySC {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame} {n : ND}
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) {ra : Int64} {blk : List (Directive × Nat)}
    (hcd : SubCd (CdC cells okPc ph lab ra) n.pc blk) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, off, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
    simp [cellOff]
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  rw [hc, ← hpc] at hph
  have hb' := blockAt_sub hb
  have hpc' : lab L + Int64.ofNat (off + (pre.map (·.2)).sum) = n.pc := by
    rw [hpc, ← hpc0, Int64.ofNat_add, Int64.add_assoc]
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb'
    rwa [hI.labOk, hpc'] at this
  refine BlkW.bodyS hp hg0 hJ ?_
  exact blkW_postO' (n := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩) (dead := fun _ => false) (ra := ra)
    hI hcode hok hR hlo hhi hR8 hl hh (fun _ _ h => h.1 ▸ hC0) hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO

/-- **A call's `callq g` is inside `BodyWS0`** at the frames `fs`
(`CallPre`'s `hWBl`): at `BlC` (its placement and phase facts), at a
node with the body's offsets whose pairs at `fs` are `Good1` with no hold,
in a region holding the return address's cell `8` below the frame. -/
theorem blkW_callq {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (h8 : (fr.size : Int) % 8 = 0)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame} {n : ND} (hno : n.o = oB fr)
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) {ra : Int64} {zc : Nat} {g : Label} {k : Nat}
    (hbl : BlC cells okPc ph lab fr ra n.pc zc g k) :
    BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F n
      [(i64 (.call (rel g)), zc)] := by
  obtain ⟨L, j, off, hpc, hb, -, hph, -⟩ := hbl
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(i64 (.call (rel g)), zc)] := by
    intro s hs hn
    have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
    rwa [hI.labOk, hpc] at this
  have hok : okBlk (-(fr.size : Int) - 8) 16 n.o [(i64 (.call (rel g)), zc)] = true :=
    okBlk_callqC g zc (by rw [hno]; simp [offOk, oB]; omega)
  refine BlkW.bodyS hp hg0 hJ ?_
  exact blkW_postO' (n := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩) (dead := fun _ => false) (ra := ra)
    hI hcode hok hR hlo hhi hR8 hl hh (fun _ _ h => h.1 ▸ hC0) hph
    (fun _ _ _ k hk hr => (noRet_false (noRet_callq g zc) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO

/-- **The callee's entry is inside `BodyWS0`** at the frames `fs`
(`CallPre`'s `hWC`, for a callee `fn` with a prologue): at the callee's
label, `8` below the caller's frame (the return address pushed), with the
callee's prologue head there (`hb`) and its phase facts (`hph`, `ProPh.hd`),
at a node whose pairs at `fs` are `Good1` with no hold, in a region holding
the head's push of `%rbp` `16` below the frame: the head's block
(`blkW_postO` at `okBlk_xHead_call`, lifted, `BlkW.bodyS`) at its first
instruction (`BlkW.nodeW`). -/
theorem nodeW_calleeEntry {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (h8 : (fr.size : Int) % 8 = 0)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 16) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true)
    (hg0 : Good1 p (c0, [])) {cl ctr : Nat} {fs : List TermRun.Frame} {fn : Label}
    (hb : blockAtB cells fn 0 xHead = true)
    (hph : blkPh okPc ph (fun _ => false) lab (lab fn + Int64.ofNat 0) 0 xHead = true)
    {n : ND} (hpc : n.pc = (_root_.Executable.labels exe).label fn) (hno : n.o = { oB fr with sp := (oB fr).sp - 8 })
    (hJ : ∀ σ c, n.J σ c → Good1 p (c, fs) ∧ c.hold = none) :
    ∀ s c, At exe endPc R F n s c → BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs := by
  have hok : okBlk (-(fr.size : Int) - 16) 16 n.o xHead = true := by
    rw [hno]; exact okBlk_xHead_call fr (Int.le_refl _) h8 (by omega)
  have H := blkW_postO (n := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩) (dead := fun _ => false) (ra := 0)
    hI hb (by rw [hpc, hI.labOk]; simp) hok hR hlo hhi hR8 hl hh (fun _ _ h => h.1 ▸ hC0) hph
    (fun _ _ _ k hk hr => (noRet_false Spike.Lib.X64.Rt.MainU.xHead_noRet k hk hr).elim) (fun _ _ _ => rfl)
    hsub hfit hFO
  intro s c hA
  exact (BlkW.nodeW (BlkW.bodyS (cl := cl) (ctr := ctr) hp hg0 hJ H) (by simp [xHead]) s c hA).1

end W

end Spike.Lib.LowerX64
