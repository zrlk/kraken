/-
**An `Accepted1` body's construct blocks with calls inside the consumer's
facts at depth** (AArch64, H7a calls): the twin of
`Spike/Lib/LowerX64/BodyWSC.lean`. `fnC_segS`' premises `hWb`/`hWs`
(`CalleePre`'s) at the code predicate with calls `CdC`, from the call-free
`blkW_bodyS1`: a construct's block (`Kind1`) inside a block of `CdC` is a
block at `Cd1`.

- `blockAt_sub`: a block inside a placed block is placed, `pre.length`
  instructions further.
- `cd1_of_subCdC`: a construct's block inside a block of `CdC` (`SubCd`)
  is at `Cd1` (`kind1_ok`, `runPhB`'s `blkPh_of_runPhB`).
- `hWbS_of`, `hWsS_of`: the body's construct blocks at its nodes and
  pending stores, from every ghost of `G0` (its pairs at the frames `fs`
  `Good1` with no hold, closed under the frame runs at `fs`), inside
  `BodyWS0` at `fs`.

Where AArch64 differs from x86-64: `blockAt` counts instructions (no byte
offsets), and the region's base is 16-aligned with `0 ≤ R.hi` (the
context's own region, no rebasing).
-/
import Spike.Lib.LowerA64.BodyWS1
import Spike.Lib.LowerA64.BodyC

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (CFacts Own Lbl)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)

/-- **A block inside a placed block is placed**, `pre.length`
instructions further. -/
theorem blockAt_sub {prog : List Directive} {l : Label} {k : Nat} {pre blk post : List Directive}
    (h : blockAt prog l k (pre ++ blk ++ post) = true) : blockAt prog l (k + pre.length) blk = true := by
  unfold blockAt at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨hl, hb⟩ := h
  generalize Scc.Cert.Rt.A64.run prog l = r at hb ⊢
  have hd : r.drop k = pre ++ blk ++ post ++ (r.drop k).drop (pre ++ blk ++ post).length := by
    have := List.take_append_drop (pre ++ blk ++ post).length (r.drop k)
    rw [hb] at this
    exact this.symm
  refine ⟨hl, ?_⟩
  rw [← List.drop_drop, hd]
  simp

variable {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
include hf h1 h16

/-- **A construct's block inside a block of `CdC` is at `Cd1`**: placed
(`blockAt_sub`), passing the phase check (`blkPh_of_runPhB`, its
directives covered by `kind1_ok`). -/
theorem cd1_of_subCdC {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {ra pc : Int64} {blk : List Directive}
    (h : SubCd (CdC prog okPc ph lab ra) pc blk) (hk : Kind1 cx blk) :
    Cd1 prog okPc ph lab cx ra pc blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, hpc0, hb, hrun⟩, rfl⟩ := h
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk (kind1_ok hf h1 h16 hk))
  refine ⟨hk, L, j + pre.length, ?_, blockAt_sub hb, hph⟩
  rw [← hpc0, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {cS : Ctl} {fp ra : BitVec 64}

/-- **`fnC_segS`' `hWb` at depth**: every construct block inside a block of
`CdC` at the body's nodes from a ghost of `G0` is inside `BodyWS0` (the
consumer's start `cS` held back) at the frames `fs`: the ghosts' pairs at
`fs` `Good1` with no hold (`hGd`), closed under the frame runs at `fs`
(`hG0`), so every control a local run reaches from them. -/
theorem hWbS_of {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl cS) (hp : Scc.Lower.Accepted1 p = true)
    (hgS : Good1 p (cS, [])) (hhS : cS.hold = none) {cl ctr : Nat} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hGd : ∀ c, G0 c → Good1 p (c, fs) ∧ c.hold = none) {al : WeakMem.AllocLabel → Option Nat} :
    ∀ c0, G0 c0 → ∀ pc t s blk, SubCd (CdC prog okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind1 cx blk →
      BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr cS s c fs) K exe endPc R F
        (bodyN p al cx fp ra c0 pc t s) blk :=
  fun c0 hg pc t s _ hcd hk => blkW_bodyS1 (n := bodyN p al cx fp ra c0 pc t s) hI hf h1 h16 hR hal hlo hhi hl
    hh hsub hfit hFO hC0 hp hgS hhS rfl
    (fun _ c ⟨_, hfj, hr⟩ => ⟨hGd c (hG0 _ _ hg (FrameRun.ofLocal hr fs)), hfj⟩)
    (cd1_of_subCdC hf h1 h16 hcd hk)

/-- **`fnC_segS`' `hWs` at depth**: `hWbS_of` at the pending stores. -/
theorem hWsS_of {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl cS) (hp : Scc.Lower.Accepted1 p = true)
    (hgS : Good1 p (cS, [])) (hhS : cS.hold = none) {cl ctr : Nat} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hGd : ∀ c, G0 c → Good1 p (c, fs) ∧ c.hold = none) {al : WeakMem.AllocLabel → Option Nat} :
    ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (CdC prog okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind1 cx blk →
      BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr cS s c fs) K exe endPc R F
        (pendN p al cx fp ra c0 pc t s k) blk :=
  fun c0 hg pc t s k _ hcd hk => blkW_bodyS1 (n := pendN p al cx fp ra c0 pc t s k) hI hf h1 h16 hR hal hlo hhi
    hl hh hsub hfit hFO hC0 hp hgS hhS rfl
    (fun _ c ⟨_, hfj, hr⟩ => ⟨hGd c (hG0 _ _ hg (FrameRun.ofLocal hr fs)), hfj⟩)
    (cd1_of_subCdC hf h1 h16 hcd hk)

end Spike.Lib.LowerA64
