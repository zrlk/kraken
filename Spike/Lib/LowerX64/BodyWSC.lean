/-
**An `Accepted1` body's construct blocks with calls inside the consumer's
facts at depth** (x86-64, H7a calls): `fnC_segS`' premises `hWb`/`hWs`
(`FnSpecC`'s) at the code predicate with calls `CdC`, from the call-free
`blkW_bodyS1`: a construct's block (`Kind1`) inside a block of `CdC` is a
block at `Cd1`.

- `blockAt_sub`: a block inside a placed block is placed, past the cells
  before it.
- `cd1_of_subCdC`: a construct's block inside a block of `CdC` (`SubCd`)
  is at `Cd1` (`kind1_ok`, `runPhB_sub`'s `blkPh_of_runPhB`).
- `hWbS_of`, `hWsS_of`: the body's construct blocks at its nodes and
  pending stores, from every ghost of `G0` (its pairs at the frames `fs`
  `Good1` with no hold, closed under the frame runs at `fs`), inside
  `BodyWS0` at `fs`.
-/
import Spike.Lib.LowerX64.BodyWS1
import Spike.Lib.LowerX64.BodyC

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAt)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts Own Lbl)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (NJ)

/-- **A block inside a placed block is placed**, `pre.length` cells and
`pre`'s bytes further. -/
theorem blockAt_sub {cells : List (Directive × Nat)} {l : Label} {k off : Nat}
    {pre blk post : List (Directive × Nat)} (h : blockAt cells l k off (pre ++ blk ++ post) = true) :
    blockAt cells l (k + pre.length) (off + (pre.map (·.2)).sum) blk = true := by
  unfold blockAt at h ⊢
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hl, hoff⟩, hb⟩ := h
  generalize Scc.Cert.Rt.X64.run cells l = r at hoff hb ⊢
  have hlen : (pre ++ blk ++ post).length ≤ (r.drop k).length := by
    have := congrArg List.length hb
    simp only [List.length_take] at this
    omega
  have hd : r.drop k = pre ++ blk ++ post ++ (r.drop k).drop (pre ++ blk ++ post).length := by
    have := List.take_append_drop (pre ++ blk ++ post).length (r.drop k)
    rw [hb] at this
    exact this.symm
  refine ⟨⟨hl, ?_⟩, ?_⟩
  · rw [List.take_add, List.map_append, List.sum_append, hoff, hd]
    simp
  · rw [← List.drop_drop, hd]
    simp

variable {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
include hf h1

/-- **A construct's block inside a block of `CdC` is at `Cd1`**: placed
(`blockAt_sub`), passing the phase check (`runPhB_sub`'s
`blkPh_of_runPhB`, its directives covered by `kind1_ok`). -/
theorem cd1_of_subCdC {cells : List (Directive × Nat)} {okPc : Nat → Bool} {ph : Nat → Nat}
    {lab : Label → Int64} {ra pc : Int64} {blk : List (Directive × Nat)}
    (h : SubCd (CdC cells okPc ph lab ra) pc blk) (hk : Kind1 fr blk) :
    Cd1 cells okPc ph lab fr ra pc blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, off, hpc0, hb, hrun⟩, rfl⟩ := h
  have hc : cellOff (pre ++ blk ++ post) pre.length = (pre.map (·.2)).sum := by
    simp [cellOff]
  have hph := Scc.Cert.Ph1X64.blkPh_of_runPhB hrun (classify_of_okBlk (kind1_ok hf h1 hk))
  rw [hc] at hph
  refine ⟨hk, L, j + pre.length, off + (pre.map (·.2)).sum, ?_, blockAt_sub hb, hph⟩
  rw [← hpc0, Int64.ofNat_add, Int64.add_assoc]

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {cS : Ctl} {fp ra : BitVec 64}

/-- **`fnC_segS`' `hWb` at depth**: every construct block inside a block of
`CdC` at the body's nodes from a ghost of `G0` is inside `BodyWS0` (the
consumer's start `cS` held back) at the frames `fs`: the ghosts' pairs at
`fs` `Good1` with no hold (`hGd`), closed under the frame runs at `fs`
(`hG0`), so every control a local run reaches from them. -/
theorem hWbS_of {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl cS) (hp : Scc.Lower.Accepted1 p = true)
    (hgS : Good1 p (cS, [])) (hhS : cS.hold = none) {cl ctr : Nat} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hGd : ∀ c, G0 c → Good1 p (c, fs) ∧ c.hold = none) {al : WeakMem.AllocLabel → Option Nat} :
    ∀ c0, G0 c0 → ∀ pc t s blk, SubCd (CdC cells okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind1 fr blk →
      BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr cS s c fs) K exe endPc R F
        (bodyN p al fr fp ra c0 pc t s) blk :=
  fun c0 hg pc t s _ hcd hk => blkW_bodyS1 (n := bodyN p al fr fp ra c0 pc t s) hI hf h1 hR hR8 hlo hhi hl hh
    hsub hfit hFO hC0 hp hgS hhS rfl
    (fun _ c ⟨_, hfj, hr⟩ => ⟨hGd c (hG0 _ _ hg (FrameRun.ofLocal hr fs)), hfj⟩) (cd1_of_subCdC hf h1 hcd hk)

/-- **`fnC_segS`' `hWs` at depth**: `hWbS_of` at the pending stores. -/
theorem hWsS_of {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl cS) (hp : Scc.Lower.Accepted1 p = true)
    (hgS : Good1 p (cS, [])) (hhS : cS.hold = none) {cl ctr : Nat} {fs : List TermRun.Frame}
    {G0 : Ctl → Prop} (hG0 : ∀ c c', G0 c → FrameRun p (c, fs) (c', fs) → G0 c')
    (hGd : ∀ c, G0 c → Good1 p (c, fs) ∧ c.hold = none) {al : WeakMem.AllocLabel → Option Nat} :
    ∀ c0, G0 c0 → ∀ pc t s k blk, SubCd (CdC cells okPc ph lab (Int64.ofBitVec ra)) pc blk → Kind1 fr blk →
      BlkW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr cS s c fs) K exe endPc R F
        (pendN p al fr fp ra c0 pc t s k) blk :=
  fun c0 hg pc t s k _ hcd hk => blkW_bodyS1 (n := pendN p al fr fp ra c0 pc t s k) hI hf h1 hR hR8 hlo hhi hl
    hh hsub hfit hFO hC0 hp hgS hhS rfl
    (fun _ c ⟨_, hfj, hr⟩ => ⟨hGd c (hG0 _ _ hg (FrameRun.ofLocal hr fs)), hfj⟩) (cd1_of_subCdC hf h1 hcd hk)

end Spike.Lib.LowerX64
