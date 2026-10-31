/-
**`h1`'s invariant at wake** (`inv1W`, x86-64): the statement of the
segment after the box's allocation (`OpenW.h1`, `WakeOPremW.oPrem_W`'s `h1`)
with its invariant fixed, so that the machine side (the post-allocation
nodes up to the `clone`) and the source side (the landing, the clone's
facts) agree on one object.

`inv1W … l b n` is the greatest closed invariant (`X64GfpS.GfpS`) inside
`W1W … l b n` together with the per-state facts `X1W` (the analogue of
`W0`'s `X0W`, `Spike/Lib/X64WakeX0.lean`, kept outside `W1` so that `W1`'s
signature stays as it is), under `OpenW.h1`'s outside move
(`TakeCKS (aW) (ClW)`) and memory side (`ms1W`: `msOfA` at `upd L0T l b`,
`updN (ls0T ls0) l n`, with no allocation).

- `X1W L a endPc l lbl lsize`: at the clone's pc `CloneInv`, `c`'s label
  of positive size and `c` bound to the box `l`; at the take pc `a` the
  site's range the child's stack `r1Of`, main's stack `r0Of` owned, `r1Of`
  not in private memory (`¬ StackM`).
- `x1W_off`: `X1W` at a state off both pcs.
- `ms1W`, `K1W`, `inv1W`: the memory side, outside move and invariant.
- `segInvS_weakW`: a segment inside a smaller fragment is one inside a larger.
- `segInvS_inv1W`, `h1_of`: `inv1W` is a segment inside `W1W` (`OpenW.h1`).
- `x1W_of`, `lsize_of`, `own1_of`, `cl_of`, `cloneInv_of`, `h1Take_of`,
  `h1TakeOwn_of`: `H1Stmt`'s clone clause, `H1Take`, `H1TakeOwn` (`OpenW.h1t`, `h1o`).
- `inv1W_of_segWS`: the start of a segment inside `W1W ∧ X1W` with no exit
  is in `inv1W` (how the landing `Box` gets in).
- `h1Stmt_of`: `H1Stmt` at `inv1W`, given the landing in it.

x86-64 twin of `Spike/Lib/A64WakeH1Inv.lean` (same names, namespace
`Spike.Lib.X64.WakeH1Inv`).

**Unlike AArch64**: the assembly is a parameter `asm` (A64:
`SccCertificate.asm`; `X64WakeOPremW`'s), first argument of `ms1W`, `inv1W`
and the lemmas about them (not `K1W`, which does not read it); `endR` (A64
`WakeSpawnR.endR`, not yet twinned) is defined here, as `endOf` at wake's
cells and the layout's prefix. `X1W` takes the box's label `l` and its clone
clause binds `c` to it (`cl_of`): x86-64's `PreR.hcm` needs `c`'s cell in
the heap (`X64WakeHPreC.hcm_of`), A64's `PreR` does not.
-/
import Spike.Lib.X64WakeOPremW
import Spike.Lib.X64GfpS

namespace Spike.Lib.X64.WakeH1Inv

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Arena FragS SegWS MemSide PlaceWX)
open Spike.Lib.X64WakeT1 (wakeSrc)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS msOfA)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.WakeWc (clonePc CloneInv H1Stmt H1Take H1TakeOwn)
open Spike.Lib.X64GfpS (GfpS)
open Spike.Lib.X64.WakeOPremW (W1W)

/-- **`h1`'s per-state facts**: at the clone's pc, `CloneInv` at the
placement `lbl`, `c`'s label of positive size under `lsize`, the child's stack owned and `c` bound to
the box `l`'s locative; at the take pc `a`, the
site's range the child's stack, main's stack owned and the child's not. -/
def X1W (L : RuntimeLayout) (a endPc : Int64) (l : WeakMem.AllocLabel) (lbl : Lbl) (lsize : Lsize) : FragS isa :=
    fun s c fs =>
  (pcOf s = clonePc L → CloneInv L endPc lbl s c fs ∧
    -- `c`'s label has cells: the landing binds `o` to the box `l` with `n = 1` (`NewSt`), `c` is
    -- `publish o`, and the path keeps the binding (discharged with `Box ⊆ inv1W`)
    (∀ l', TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l', 0⟩ 0)]) →
      0 < lsize l') ∧
    -- the child's stack is owned at the clone (`OpenW.hCl`'s `hown1`): `scc_rt_thread_init` took it
    -- (`CloneP`'s `StackM`, through `owned_of_stackM`)
    Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s ∧
    -- `c` is the box `l` (`X64WakeHPreC.hcm_of`'s `hcl_c`): the landing binds `o` to `l`
    -- (`X64.Flow.WakeWc.box_env`), `c` is `publish o` (`X64WakeBoxDefs.boxPubSy`), the path keeps it
    TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)])) ∧
    (pcOf s = a.toBitVec.toNat →
      Kernel.siteRange abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s.st.1)

/-- **`X1W` off the clone's and the take's pcs**: both clauses are guarded
by the pc, so a state at neither holds it outright. -/
theorem x1W_off {L : RuntimeLayout} {a endPc : Int64} {l : WeakMem.AllocLabel} {lbl : Lbl} {lsize : Lsize}
    {s : State}
    {c : Spike.Lib.Ctl} {fs : List TermRun.Frame} (hc : pcOf s ≠ clonePc L) (ha : pcOf s ≠ a.toBitVec.toNat) :
    X1W L a endPc l lbl lsize s c fs :=
  ⟨fun h => absurd h hc, fun h => absurd h ha⟩

/-- **A segment inside a smaller fragment** is one inside a larger. -/
theorem segInvS_weakW {W W' : FragS isa} {K : State → State → Prop} {p : Prog} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isa} {inv : FragS isa} (h : SegInvS W' K p lbl ms inv)
    (hW : ∀ s c fs, W' s c fs → W s c fs) : SegInvS W K p lbl ms inv :=
  fun s c fs hi => let h' := h s c fs hi; ⟨hW s c fs h'.1, h'.2⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The layout's end of text** at wake's cells (A64 `WakeSpawnR.endR`). -/
abbrev endR : Int64 := Scc.Cert.Rt.X64.endOf (Ly).exe SccCode.wakeCells (Ly).pfx

/-- **`h1`'s memory side** at `l` placed at `b`, `n` bytes (`OpenW.h1`'s:
`msOfA` at `wakeD`'s `rd`, `G`, `own`, `ar`, no allocation). -/
def ms1W (l : WeakMem.AllocLabel) (b n : Nat) : List TermRun.Frame → MemSide isa :=
  msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True) (X64WakeOG.gW hp i cT)
    (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
    (WakeOD.arW hp i) (fun _ _ _ _ _ => False)
    (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
    (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n)

/-- **`h1`'s outside move** (`OpenW.h1`'s: the take or the clone's error). -/
def K1W : State → State → Prop := TakeCKS (X64WakeOSide.aW hp i E) (WakeOD.ClW hp i)

/-- **`h1`'s invariant**: the greatest closed invariant inside `W1W ∧ X1W`. -/
def inv1W (l : WeakMem.AllocLabel) (b n : Nat) : FragS isa :=
  GfpS (fun s c fs => W1W asm hp i E Dt Ctx ls0 l b n s c fs ∧
      X1W (Ly) (X64WakeOSide.aW hp i E) (endR hp i) l
        (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
          (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) s c fs)
    (K1W hp i E) wakeSrc (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
    (ms1W asm hp i E cT ls0 l b n)

/-- **`inv1W` is a segment inside `W1W`.** -/
theorem segInvS_inv1W (l : WeakMem.AllocLabel) (b n : Nat) :
    SegInvS (W1W asm hp i E Dt Ctx ls0 l b n) (K1W hp i E) wakeSrc
      (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b) (ms1W asm hp i E cT ls0 l b n)
      (inv1W asm hp i E cT Dt Ctx ls0 l b n) :=
  segInvS_weakW Spike.Lib.X64GfpS.segInvS_gfpS fun _ _ _ h => h.1

/-- **`X1W` at `inv1W`'s pairs.** -/
theorem x1W_of {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : inv1W asm hp i E cT Dt Ctx ls0 l b n s c fs) :
    X1W (Ly) (X64WakeOSide.aW hp i E) (endR hp i) l
      (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
        (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) s c fs :=
  (Spike.Lib.X64GfpS.segInvS_gfpS s c fs h).1.2

/-- **`c`'s label has cells** at `inv1W`'s clone states. -/
theorem lsize_of (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s c fs, inv1W asm hp i E cT Dt Ctx ls0 l b n s c fs → pcOf s = clonePc (Ly) → ∀ l',
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l', 0⟩ 0)]) →
      0 < Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n l' :=
  fun _ _ _ h hpc => ((x1W_of asm hp i E cT Dt Ctx ls0 h).1 hpc).2.1

/-- **The child's stack owned** at `inv1W`'s clone states (`OpenW.hCl`'s
`hown1`). -/
theorem own1_of (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s c fs, inv1W asm hp i E cT Dt Ctx ls0 l b n s c fs → pcOf s = clonePc (Ly) →
      Spike.Lib.X64Consumer.Owned (Ly).Λ (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) s :=
  fun _ _ _ h hpc => ((x1W_of asm hp i E cT Dt Ctx ls0 h).1 hpc).2.2.1

/-- **`c` is the box `l`** at `inv1W`'s clone states (`X64WakeHPreC`'s
`hcl_c` at `wakeD`). -/
theorem cl_of (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s (c : Spike.Lib.Ctl) fs, inv1W asm hp i E cT Dt Ctx ls0 l b n s c fs → pcOf s = clonePc (Ly) →
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :=
  fun _ _ _ h hpc => ((x1W_of asm hp i E cT Dt Ctx ls0 h).1 hpc).2.2.2

/-- **`H1Stmt`'s clone clause** at `inv1W`. -/
theorem cloneInv_of (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s c fs, inv1W asm hp i E cT Dt Ctx ls0 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (endR hp i) (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b) s c fs :=
  fun _ _ _ h hpc => ((x1W_of asm hp i E cT Dt Ctx ls0 h).1 hpc).1

/-- **`H1Take`** at `inv1W` (`OpenW.h1t`). -/
theorem h1Take_of : H1Take (Ly) (X64WakeOSide.aW hp i E) (inv1W asm hp i E cT Dt Ctx ls0) :=
  fun _ _ _ _ _ _ h hpc => ((x1W_of asm hp i E cT Dt Ctx ls0 h).2 hpc).1

/-- **`H1TakeOwn`** at `inv1W` (`OpenW.h1o`). -/
theorem h1TakeOwn_of : H1TakeOwn (Ly) (X64WakeOSide.aW hp i E) (inv1W asm hp i E cT Dt Ctx ls0) :=
  fun _ _ _ _ _ _ h hpc => ((x1W_of asm hp i E cT Dt Ctx ls0 h).2 hpc).2

/-- **The start of a segment inside `W1W ∧ X1W` with no exit is in
`inv1W`** (`gfpS_of_segWS`). -/
theorem inv1W_of_segWS {l : WeakMem.AllocLabel} {b n : Nat} {P : FragS isa}
    (h : SegWS (fun s c fs => W1W asm hp i E Dt Ctx ls0 l b n s c fs ∧
        X1W (Ly) (X64WakeOSide.aW hp i E) (endR hp i) l
          (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
            (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls0) l n) s c fs)
      (K1W hp i E) wakeSrc (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) l b)
      (ms1W asm hp i E cT ls0 l b n) P (fun _ _ _ => False)) :
    ∀ s c fs, P s c fs → inv1W asm hp i E cT Dt Ctx ls0 l b n s c fs :=
  Spike.Lib.X64GfpS.gfpS_of_segWS h

/-- **`H1Stmt` at `inv1W`**, given the landing `Box` in it. -/
theorem h1Stmt_of (Box : WeakMem.AllocLabel → Nat → Nat → State → Spike.Lib.Ctl → Prop)
    (hB : ∀ l b n, Spike.Lib.X64WakeLoadT.L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ s c, Box l b n s c → inv1W asm hp i E cT Dt Ctx ls0 l b n s c []) :
    H1Stmt (W1W asm hp i E Dt Ctx ls0) (K1W hp i E) (WakeOD.arW hp i)
      (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (ms1W asm hp i E cT ls0) (Ly) (endR hp i) Box
      (inv1W asm hp i E cT Dt Ctx ls0) :=
  fun l b n hl hb => ⟨segInvS_inv1W asm hp i E cT Dt Ctx ls0 l b n, hB l b n hl hb,
    cloneInv_of asm hp i E cT Dt Ctx ls0 l b n⟩

/-- **`OpenW.h1` / `oPrem_W`'s `h1` at `inv1W`**: the field's statement at
`wakeD hp i E cT Dt ls0 W0 inv0 (W1W …) (inv1W …)`, for any `W0`, `inv0`. -/
theorem h1_of (W0 inv0 : FragS isa) :
    ∀ l b n, (WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 (W1W asm hp i E Dt Ctx ls0)
        (inv1W asm hp i E cT Dt Ctx ls0)).L0 l = none →
      AllocLand (WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 (W1W asm hp i E Dt Ctx ls0)
        (inv1W asm hp i E cT Dt Ctx ls0)).ar.heap
        (WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 (W1W asm hp i E Dt Ctx ls0)
          (inv1W asm hp i E cT Dt Ctx ls0)).ar.cells b n →
      let D := WakeOD.wakeD hp i E cT Dt ls0 W0 inv0 (W1W asm hp i E Dt Ctx ls0)
        (inv1W asm hp i E cT Dt Ctx ls0)
      SegInvS (D.W1 l b n) (TakeCKS D.a D.Cl) wakeSrc (Spike.Lib.X64ConsumerA.upd D.L0 l b)
        (msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) D.rd D.G D.own D.ar
          (fun _ _ _ _ _ => False) (Spike.Lib.X64ConsumerA.upd D.L0 l b)
          (Spike.Lib.X64ConsumerA.updN D.ls0 l n)) (D.inv1 l b n) :=
  fun l b n _ _ => segInvS_inv1W asm hp i E cT Dt Ctx ls0 l b n

end Inst

end Spike.Lib.X64.WakeH1Inv

/-- info: 'Spike.Lib.X64.WakeH1Inv.x1W_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.x1W_off

/-- info: 'Spike.Lib.X64.WakeH1Inv.segInvS_weakW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.segInvS_weakW

/-- info: 'Spike.Lib.X64.WakeH1Inv.segInvS_inv1W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.segInvS_inv1W

/-- info: 'Spike.Lib.X64.WakeH1Inv.x1W_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.x1W_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.lsize_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.lsize_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.own1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.own1_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.cl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.cl_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.cloneInv_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.cloneInv_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.h1Take_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.h1Take_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.h1TakeOwn_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.h1TakeOwn_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.inv1W_of_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.inv1W_of_segWS

/-- info: 'Spike.Lib.X64.WakeH1Inv.h1Stmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.h1Stmt_of

/-- info: 'Spike.Lib.X64.WakeH1Inv.h1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeH1Inv.h1_of
