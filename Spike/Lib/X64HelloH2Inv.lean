/-
**`h2`'s invariant at hello, on x86-64** (`inv2H`; the twin of `Spike/Lib/A64HelloH2Inv.lean`, the hello twin of
`Spike/Lib/X64WakeH1Inv.lean`'s `inv1W`, one level up): the statement of the segment after the box's allocation
(`X64HelloPreA.H2StmtH`) with its invariant fixed, generic in the level's fragment `W2`, outside move `K` and
memory side `ms2`, so that the machine side (the post-box nodes up to the `clone`) and the clone's consumers
(`X64HelloHClW.hClH_of`'s `hown2`, `hx1`) agree on one object.

`inv2H … l b n l' b' n'` is the greatest closed invariant (`X64GfpS.GfpS`) inside `W2 … ∧ X2H …` under `K` at
`ms2 …` and the twice extended placement. `X2H` carries the per-state facts `W2` does not: at the clone's pc
`CloneInvH`, `c`'s label of positive size, the child's stack owned, `%rsi` at its top (`kOf`), main's segment-end
facts (`CloneSegD`), `%r8` the second TCB (`tH`) and the parent's saved frame pointer at the clone frame's slot
`80`; at the take pc the site's range the child's stack, main's
stack owned, the child's not private (wake's `X1W`, plus `%rsi`).

- `X2H`, `x2H_off`: the per-state facts; off both pcs they hold outright.
- `inv2H`, `segInvS_inv2H`: the invariant, a segment inside `W2`.
- `x2H_of`, `cloneInv2_of`, `own2_of`, `x1_2_of`, `seg2_of`, `x3_2_of`, `fp2_of`, `take2_of`: `X2H`'s clauses at
  `inv2H`'s pairs (`H2StmtH`'s clone clause; `hClH_of`'s `hown2`, `hx1`; the segment end's `hseg`, `hfp`).
- `inv2H_of_segWS`: the start of a segment inside `W2 ∧ X2H` with no exit is in `inv2H` (how the landing gets in).
- `h2Stmt_of`: `H2StmtH` at `inv2H`, given the landing `Box` in it.

## Differences from the AArch64 version

- The clone's registers are x86-64's: the child's stack top in `%rsi` (AArch64: `x1`), the second TCB in `%r8`
  (`clone`'s `tls` argument; AArch64: `x3`). The names `x1_2_of`, `x3_2_of` are kept.
- Over x86-64's `X64ConsumerA`, `X64GfpS`, `X64HelloPreA`, `X64HelloCloneSegD.CloneSegD`,
  `X64.Flow.HelloWc.tH`, `X64.Flow.WakeWc.kOf`, `X64.Rt.PreChild.r1Of`, `X64.Rt.Ti2.r0Of`,
  `X64.Flow.Ret0.StackM`.
- The clone clause also carries the parent's saved frame pointer (`fp2_of`, the segment end's `hfp` in its `fp`
  form; AArch64 reads `x29` from `CloneSegD`).
- A64's `lsize2_of` is dead and not twinned (`X2H` keeps its clause).
-/
import Spike.Lib.X64HelloHClW
import Spike.Lib.X64GfpS
import Spike.Lib.X64HelloCloneSegD
import Spike.Lib.X64HelloWcSp3
import Spike.Lib.X64HelloParent

namespace Spike.Lib.X64HelloH2Inv

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Arena FragS SegWS MemSide)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloPreA (clonePcH CloneInvH H2StmtH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64GfpS (GfpS)

/-- **`h2`'s per-state facts**: at the clone's pc, `CloneInvH` at the placement `lbl`, `c`'s label of positive
size under `lsize`, the child's stack owned, `%rsi` its top (`kOf`), main's segment-end facts
(`X64HelloCloneSegD.CloneSegD`) and `%r8` the second TCB (`tH`); at the take pc `a`, the
site's range the child's stack, main's stack owned and the child's not private. -/
def X2H (L : RuntimeLayout) (a endPc : Int64) (lbl : Lbl) (lsize : Lsize) : FragS isa := fun s c fs =>
  (pcOf s = clonePcH L → CloneInvH L endPc lbl s c fs ∧
    -- `c`'s label has cells: the landing binds `o` to the box with `n' = 1`, `c` is `publish o`
    (∀ l', TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l', 0⟩ 0)]) →
      0 < lsize l') ∧
    -- the child's stack is owned at the clone (`hClH_of`'s `hown2`): `scc_rt_thread_init` took it
    Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s ∧
    -- `%rsi` the child's stack top (`hClH_of`'s `hx1`; `ClonePostH` leaves it existential)
    s.st.1.regs.get64 .rsi = Spike.Lib.X64.Flow.WakeWc.kOf L.lab ∧
    -- main's segment end (the segment end's `hseg`): `At` in the widened region, base, alignment, `ra`, `%r15`
    Spike.Lib.X64HelloCloneSegD.CloneSegD L endPc s c ∧
    -- `%r8` the second TCB (the clone's `tls`; the root's `hx3`)
    s.st.1.regs.get64 .r8 = Spike.Lib.X64.Flow.HelloWc.tH L.lab ∧
    -- the parent's saved frame pointer at the clone: `%rbp`'s slot of the clone frame (the segment end's `hfp`)
    ∀ (Rm : Spike.Lib.Region) (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64),
      Spike.Lib.X64.At L.exe endPc ⟨Rm.base, -128, 40⟩ F₂
        ⟨Spike.Lib.X64HelloPreA.cloneAtH L.exe, Spike.Lib.X64.Flow.Worker.Hello.Parent.oP,
          Spike.Lib.X64.Flow.Worker.Hello.Parent.JS c cA fp ra tp⟩ s c →
        fp = (⟨Rm.base, -128, 40⟩ : Spike.Lib.Region).addr 80) ∧
    (pcOf s = a.toBitVec.toNat →
      Kernel.siteRange abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s.st.1)

/-- **`X2H` off the clone's and the take's pcs**: both clauses are guarded by the pc. -/
theorem x2H_off {L : RuntimeLayout} {a endPc : Int64} {lbl : Lbl} {lsize : Lsize} {s : State}
    {c : Spike.Lib.Ctl} {fs : List TermRun.Frame} (hc : pcOf s ≠ clonePcH L) (ha : pcOf s ≠ a.toBitVec.toNat) :
    X2H L a endPc lbl lsize s c fs :=
  ⟨fun h => absurd h hc, fun h => absurd h ha⟩

section Inv

variable (W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (K : State → State → Prop)
  (ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa)
  (L : RuntimeLayout) (a endPc : Int64) (L0 : Lbl) (ls0 : Lsize)

set_option hygiene false in
/-- The level's placement. -/
local notation "L2" => fun (l : WeakMem.AllocLabel) (b : Nat) (l' : WeakMem.AllocLabel) (b' : Nat) =>
  Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd L0 l b) l' b'

set_option hygiene false in
/-- The level's sizes. -/
local notation "S2" => fun (l : WeakMem.AllocLabel) (n : Nat) (l' : WeakMem.AllocLabel) (n' : Nat) =>
  Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN ls0 l n) l' n'

/-- **`h2`'s invariant**: the greatest closed invariant inside `W2 ∧ X2H` under `K` at `ms2`. -/
def inv2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) : FragS isa :=
  GfpS (fun s c fs => W2 l b n l' b' n' s c fs ∧ X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs)
    K helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')

/-- **`inv2H` is a segment inside `W2`.** -/
theorem segInvS_inv2H (l : WeakMem.AllocLabel) (b n : Nat) (l' : WeakMem.AllocLabel) (b' n' : Nat) :
    SegInvS (W2 l b n l' b' n') K helloSrc ((L2) l b l' b') (ms2 l b n l' b' n')
      (inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n') :=
  fun s c fs hi => let h' := Spike.Lib.X64GfpS.segInvS_gfpS s c fs hi; ⟨h'.1.1, h'.2⟩

variable {W2 K ms2 L a endPc L0 ls0} {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
  {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}

/-- **`X2H` at `inv2H`'s pairs.** -/
theorem x2H_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) :
    X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs :=
  (Spike.Lib.X64GfpS.segInvS_gfpS s c fs h).1.2

/-- **`H2StmtH`'s clone clause** at `inv2H`. -/
theorem cloneInv2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    CloneInvH L endPc ((L2) l b l' b') s c fs :=
  ((x2H_of h).1 hpc).1

/-- **The child's stack owned** at `inv2H`'s clone states (`X64HelloHClW.hClH_of`'s `hown2`). -/
theorem own2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s :=
  ((x2H_of h).1 hpc).2.2.1

/-- **`%rsi` the child's stack top** at `inv2H`'s clone states (`X64HelloHClW.hClH_of`'s `hx1`). -/
theorem x1_2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    s.st.1.regs.get64 .rsi = Spike.Lib.X64.Flow.WakeWc.kOf L.lab :=
  ((x2H_of h).1 hpc).2.2.2.1

/-- **main's segment-end facts** at `inv2H`'s clone states (the segment end's `hseg`). -/
theorem seg2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    Spike.Lib.X64HelloCloneSegD.CloneSegD L endPc s c :=
  ((x2H_of h).1 hpc).2.2.2.2.1

/-- **`%r8` the second TCB** at `inv2H`'s clone states (the root's `hx3`): the clone's `tls` argument, `wcNSH`'s
TCB word in `%r8` (`X64HelloWcSp6.JLH`), at `X64.Flow.HelloWc.tH`. -/
theorem x3_2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    s.st.1.regs.get64 .r8 = Spike.Lib.X64.Flow.HelloWc.tH L.lab :=
  ((x2H_of h).1 hpc).2.2.2.2.2.1

/-- **The parent's saved frame pointer** at `inv2H`'s clone states (the segment end's `hfp`): at an `At` node of
the clone frame `⟨Rm.base, -128, 40⟩`, `JS`'s `fp` is its slot `80`. -/
theorem fp2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = clonePcH L) :
    ∀ (Rm : Spike.Lib.Region) (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64),
      Spike.Lib.X64.At L.exe endPc ⟨Rm.base, -128, 40⟩ F₂
        ⟨Spike.Lib.X64HelloPreA.cloneAtH L.exe, Spike.Lib.X64.Flow.Worker.Hello.Parent.oP,
          Spike.Lib.X64.Flow.Worker.Hello.Parent.JS c cA fp ra tp⟩ s c →
        fp = (⟨Rm.base, -128, 40⟩ : Spike.Lib.Region).addr 80 :=
  ((x2H_of h).1 hpc).2.2.2.2.2.2

/-- **The take's facts** at `inv2H`'s take states: the site's range the child's stack, main's stack owned, the
child's not private. -/
theorem take2_of (h : inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs) (hpc : pcOf s = a.toBitVec.toNat) :
    Kernel.siteRange abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s.st.1 :=
  (x2H_of h).2 hpc

/-- **The start of a segment inside `W2 ∧ X2H` with no exit is in `inv2H`** (`gfpS_of_segWS`). -/
theorem inv2H_of_segWS {P : FragS isa}
    (h : SegWS (fun s c fs => W2 l b n l' b' n' s c fs ∧ X2H L a endPc ((L2) l b l' b') ((S2) l n l' n') s c fs)
      K helloSrc ((L2) l b l' b') (ms2 l b n l' b' n') P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c fs :=
  Spike.Lib.X64GfpS.gfpS_of_segWS h

variable (W2 K ms2 L a endPc L0 ls0)

/-- **`H2StmtH` at `inv2H`**, given the landing `Box` in it (`hB`). -/
theorem h2Stmt_of (ar : Arena)
    (Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop)
    (hB : ∀ l b n l' b' n', L0 l = none → AllocLand ar.heap ar.cells b n →
      Spike.Lib.X64ConsumerA.upd L0 l b l' = none → AllocLand ar.heap ar.cells b' n' →
      ∀ s c, Box l b n l' b' n' s c → inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n' s c []) :
    H2StmtH W2 K ar L0 ms2 L endPc Box (inv2H W2 K ms2 L a endPc L0 ls0) :=
  fun l b n l' b' n' hl hb hl' hb' =>
    ⟨segInvS_inv2H W2 K ms2 L a endPc L0 ls0 l b n l' b' n', hB l b n l' b' n' hl hb hl' hb',
      fun _ _ _ h hpc => cloneInv2_of h hpc⟩

end Inv

end Spike.Lib.X64HelloH2Inv

/-- info: 'Spike.Lib.X64HelloH2Inv.segInvS_inv2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Inv.segInvS_inv2H

/-- info: 'Spike.Lib.X64HelloH2Inv.own2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Inv.own2_of

/-- info: 'Spike.Lib.X64HelloH2Inv.x1_2_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Inv.x1_2_of

/-- info: 'Spike.Lib.X64HelloH2Inv.inv2H_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Inv.inv2H_of_segWS

/-- info: 'Spike.Lib.X64HelloH2Inv.h2Stmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2Inv.h2Stmt_of
