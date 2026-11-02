/-
**hello.w's pre-spawn `O` per entry**: the twin of
`Spike.Lib.X64WakeO` at `helloSrc` over the two-allocation invariant `I3`
(`Spike.Lib.X64SegInstA3`), main allocating rodata's buffer and then the
`ThreadId` box before its `clone`.

The relation is `R1OH … X = RSAH … ∧ X`, with `X` a named slot for the
pure source conjuncts at `helloSrc`: the `VBufR` / `VPre` / `VPreC` /
`VFlag` conjuncts and their lifters, and the `NoObs` / `X64SpawnCohSteps` /
`X64SpawnFlag` / `SpawnLt` twins. Their `Pre1T`
lifters plug in through `hello_O_at`'s `lift`, as `X64WakeO.wake_O_at`
applies `X64WakeO`'s in order.

- `ODataH`: the instance data of one entry (`X64WakeO.OData` plus the third
  level's fragments `W2`, `inv2`).
- `IH`: the invariant `I3 ar L0 ls0 inv0 inv1 inv2` of the data.
- `R1H`, `R1OH`: the base relation `RSAH` at `IH D` and `HeldOk2 Λ r0 r1`,
  and it with the slot `X`.
- `OPremH`: `X64HelloPreAsm.pre1T_of_seg3`'s premises at an entry and its
  data (owners as in `X64WakeO.OPrem`; `h2`/`hW2` the box-to-clone segment
  and its per-state facts).
- `hello_O_base`: `Pre1T` at `R1H` from `OPremH`; `hello_hw`: no
  `write(1, …)` at a system call under `R1H` (`X64WakeNoObs.rsah_hw`), the
  premise of the `NoObs` lifter.
- `hello_O_at`: `Pre1T` at `R1OH … X` from `OPremH` and a lifter `lift`.
- `hello_O`: per admissible entry.

x86-64 twin of `Spike/Lib/HelloO.lean` (same names, namespaces with the `X64` prefix).

**Where this differs from AArch64**: the base relation's obligations come from `X64HelloPreAsm.pre1T_of_seg3`
at x86-64's `NodesA`/`HeldPathS` and `X64SegInstA3`'s `I3`; the statements are otherwise the A64 file's.
-/
import Spike.Lib.X64HelloPreAsm
import Spike.Lib.X64WakeNoObs
import Spike.Lib.X64WakePreInv

namespace Spike.Lib.X64HelloO

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64
open Spike.Lib.X64WakePreTi (Pre1T)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc)

/-- **The instance data of one entry** (see the module doc). -/
structure ODataH where
  rd : TermRun.Word → Prop
  G : Loc → Val → Prop
  own : OwnS
  ar : Arena
  Cl : State → Prop
  Dt : State → Prop
  L0 : Lbl
  ls0 : Lsize
  a : Int64
  W0 : FragS isa
  inv0 : FragS isa
  W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa
  inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa
  W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa
  inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa
  r0 : Range
  r1 : Range

/-- The data's invariant: `I3` at its levels and fragments. -/
abbrev IH (D : ODataH) : InvS := I3 D.ar D.L0 D.ls0 D.inv0 D.inv1 D.inv2

/-- **The base relation**: `RSAH` at `IH D` and `HeldOk2 Λ r0 r1`. -/
abbrev R1H (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (μ : Marks) (D : ODataH) (d : Cfg) (s : TermRun.Cfg) :
    Prop :=
  RSAH Λ (srcPo 2 arch helloSrc) helloSrc D.G D.own (IH D) (HeldOk2 Λ D.r0 D.r1) μ D.ar d s

/-- **The pre-spawn relation** at data `D`, marks `μ` and slot `X`: `R1H`
with the named conjuncts `X` on the right (see the module doc). -/
def R1OH (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (μ : Marks) (D : ODataH) (X : Cfg → TermRun.Cfg → Prop)
    (d : Cfg) (s : TermRun.Cfg) : Prop :=
  R1H arch Λ μ D d s ∧ X d s

/-- **`pre1T_of_seg3`'s premises at one entry** (owners as in
`X64WakeO.OPrem`); `μ` is the entry's marks. -/
structure OPremH (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : Asm) (E : Entry)
    (Ab Ac : State → Prop) (D : ODataH) : Prop where
  /- the segments -/
  h2 : ∀ l b n l' b' n', D.L0 l = none → AllocLand D.ar.heap D.ar.cells b n →
    X64ConsumerA.upd D.L0 l b l' = none → AllocLand D.ar.heap D.ar.cells b' n' →
    SegInvS (D.W2 l b n l' b' n') (TakeCKS D.a D.Cl) helloSrc (X64ConsumerA.upd (X64ConsumerA.upd D.L0 l b) l' b')
      (msOfA Λ ((target (kernel 2) E).marks asm Λ) D.rd D.G D.own D.ar (fun _ _ _ _ _ => False)
        (X64ConsumerA.upd (X64ConsumerA.upd D.L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN D.ls0 l n) l' n'))
      (D.inv2 l b n l' b' n')
  h1 : ∀ l b n, D.L0 l = none → AllocLand D.ar.heap D.ar.cells b n →
    Spike.Lib.X64SegWPub.SegInvSP (D.W1 l b n) (TakeCKS D.a D.Cl) helloSrc (X64ConsumerA.upd D.L0 l b)
      (msOfA Λ ((target (kernel 2) E).marks asm Λ) D.rd D.G D.own D.ar (IH D) (X64ConsumerA.upd D.L0 l b)
        (X64ConsumerA.updN D.ls0 l n)) (D.inv1 l b n)
  h0 : SegInvS D.W0 (TakeCKS D.a D.Cl) helloSrc D.L0
    (msOfA Λ ((target (kernel 2) E).marks asm Λ) D.rd D.G D.own D.ar (IH D) D.L0 D.ls0) D.inv0
  /- the per-state facts -/
  hW0 : ∀ s c fs, D.inv0 s c fs → D.W0 s c fs →
    SFactsACH Λ ((target (kernel 2) E).marks asm Λ) helloSrc D.rd D.G D.own D.ar (IH D)
      D.L0 D.ls0 s c fs D.Dt Ab D.Cl Ac
  hW1 : ∀ l b n s c fs, D.L0 l = none → AllocLand D.ar.heap D.ar.cells b n → D.W1 l b n s c fs →
    SFactsACH Λ ((target (kernel 2) E).marks asm Λ) helloSrc D.rd D.G D.own D.ar (IH D)
      (X64ConsumerA.upd D.L0 l b) (X64ConsumerA.updN D.ls0 l n) s c fs D.Dt Ab D.Cl Ac
  hW2 : ∀ l b n l' b' n' s c fs, D.L0 l = none → AllocLand D.ar.heap D.ar.cells b n →
    X64ConsumerA.upd D.L0 l b l' = none → AllocLand D.ar.heap D.ar.cells b' n' → D.W2 l b n l' b' n' s c fs →
    SFactsACH Λ ((target (kernel 2) E).marks asm Λ) helloSrc D.rd D.G D.own D.ar (IH D)
      (X64ConsumerA.upd (X64ConsumerA.upd D.L0 l b) l' b')
      (X64ConsumerA.updN (X64ConsumerA.updN D.ls0 l n) l' n') s c fs D.Dt Ab D.Cl Ac
  /- the take, the ranges, the side facts, the load -/
  ha : ((target (kernel 2) E).marks asm Λ).site .take = some D.a.toBitVec.toNat
  hsplit : ∀ lbl lsize s c fs hl, IH D lbl lsize s c fs → HeldOk2 Λ D.r0 D.r1 s hl →
    ∀ a, ((target (kernel 2) E).marks asm Λ).site .take = some a → pcOf s = a →
      (hl = [] ∧ Kernel.siteRange abi s = D.r0) ∨ (hl = [(0, D.r0)] ∧ Kernel.siteRange abi s = D.r1)
  hs0 : D.r0.Sub Λ.stackPool
  hs1 : D.r1.Sub Λ.stackPool
  hz0 : 0 < D.r0.size
  hz1 : 0 < D.r1.size
  hro : Λ.rodata.Disjoint Λ.stackPool
  hd : D.r1.Disjoint D.r0
  hw0 : D.r0.lo + D.r0.size ≤ 2 ^ 64
  hw1 : D.r1.lo + D.r1.size ≤ 2 ^ 64
  hP : HookOK (srcPo 2 arch helloSrc) helloSrc
  hClc : ∀ s, D.Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)
  hsafe : SrcSafeS (srcPo 2 arch helloSrc) helloSrc (IH D)
  hrd : SrcRd (srcPo 2 arch helloSrc) helloSrc D.rd
  hwf : Λ.WF
  hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → D.G (wordLoc a) v
  hok : D.ar.OK
  hB : B.cells = D.ar.cells
  hdt : ∀ s buf n, D.Dt s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)
  hinit : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
    ∃ s0, (srcS helloSrc arch).init s0 ∧ R1H arch Λ ((target (kernel 2) E).marks asm Λ) D d s0
  hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {E : Entry}
  {Ab Ac : State → Prop} {D : ODataH}

/-- **`Pre1T` at the base relation** (`X64HelloPreAsm.pre1T_of_seg3`). -/
theorem hello_O_base (h : OPremH arch Λ B asm E Ab Ac D) :
    Pre1T arch Λ B asm E (R1H arch Λ ((target (kernel 2) E).marks asm Λ) D) Ab Ac helloSrc :=
  X64HelloPreAsm.pre1T_of_seg3 rfl h.h2 h.h1 h.h0 h.ha h.hW0 h.hW1 h.hW2 h.hsplit h.hs0 h.hs1 h.hz0 h.hz1 h.hro
    h.hd h.hw0 h.hw1 h.hP h.hClc h.hsafe h.hrd h.hwf h.hGpl h.hok h.hB h.hdt h.hinit h.hti0

/-- **No `write(1, …)` at a system call under `R1H`** (`X64WakeNoObs.rsah_hw`
from the write tail, `inst_of_segWA3CH2`'s `WrInS`): the `NoObs`
lifter's premise. -/
theorem hello_hw (h : OPremH arch Λ B asm E Ab Ac D) :
    ∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isa),
      R1H arch Λ ((target (kernel 2) E).marks asm Λ) D d s → d.2.exited = none → d.1.threads[tid]? = some t →
      abi.atSys t.st = true → ∀ buf n, Kernel.callOf abi t ≠ some (.write 1 buf n) := by
  obtain ⟨-, -, -, hWr, -⟩ := inst_of_segWA3CH2 (fun l b n l' b' n' hl hb hl' hb' => (h.h2 l b n l' b' n' hl hb hl' hb').toP)
      (fun l b n hl hb => h.h1 l b n hl hb) h.h0.toP h.ha h.hW0 h.hW1 h.hW2 h.hsplit h.hs0 h.hs1
    h.hz0 h.hz1 h.hro h.hd h.hw0 h.hw1
  exact X64WakeNoObs.rsah_hw fun _ _ _ _ _ hI hsys buf n hc => h.hdt _ buf n (hWr _ _ _ _ _ hI hsys 1 buf n hc) hc

/-- **`Pre1T` at one entry** at `R1OH … X`: the base (`hello_O_base`)
through the lifters `lift` adding the slot's conjuncts (given `hello_hw`
for `NoObs`).

Non-vacuity of `I3`: `X64HelloWcInv3`'s example checks the two landings
at trivial `inv0`/`inv1`/`inv2`; the real check is where the entry's data
`D` instantiates `I3` with hello's
`H0StmtH`/`H1StmtH`/`H2StmtH` invariants. -/
theorem hello_O_at {X : Cfg → TermRun.Cfg → Prop} (h : OPremH arch Λ B asm E Ab Ac D)
    (lift : Pre1T arch Λ B asm E (R1H arch Λ ((target (kernel 2) E).marks asm Λ) D) Ab Ac helloSrc →
      (∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isa),
        R1H arch Λ ((target (kernel 2) E).marks asm Λ) D d s → d.2.exited = none → d.1.threads[tid]? = some t →
        abi.atSys t.st = true → ∀ buf n, Kernel.callOf abi t ≠ some (.write 1 buf n)) →
      Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) D X) Ab Ac helloSrc) :
    Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) D X) Ab Ac helloSrc :=
  lift (hello_O_base h) (hello_hw h)

/-- **`O` at every admissible entry**, data, premises and lifter per entry. -/
theorem hello_O {D : Entry → ODataH} {X : Entry → Cfg → TermRun.Cfg → Prop}
    (h : ∀ E : Entry, E.Ok Λ → OPremH arch Λ B asm E Ab Ac (D E))
    (lift : ∀ E : Entry, E.Ok Λ →
      Pre1T arch Λ B asm E (R1H arch Λ ((target (kernel 2) E).marks asm Λ) (D E)) Ab Ac helloSrc →
      (∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isa),
        R1H arch Λ ((target (kernel 2) E).marks asm Λ) (D E) d s → d.2.exited = none →
        d.1.threads[tid]? = some t → abi.atSys t.st = true → ∀ buf n, Kernel.callOf abi t ≠ some (.write 1 buf n)) →
      Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) (D E) (X E)) Ab Ac helloSrc) :
    ∀ E : Entry, E.Ok Λ →
      Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) (D E) (X E)) Ab Ac helloSrc :=
  fun E hE => hello_O_at (h E hE) (lift E hE)

/-- With the empty slot, the lifter is the identity up to `∧ True`
(`R1OH … (fun _ _ => True)`), so `hello_O_at` needs no lifter yet. -/
theorem hello_O_true (h : OPremH arch Λ B asm E Ab Ac D) :
    Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) D fun _ _ => True) Ab Ac helloSrc :=
  hello_O_at h fun O _ => Spike.Lib.X64WakePreInv.Pre1T.inv O (fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial)

end Spike.Lib.X64HelloO

/-- info: 'Spike.Lib.X64HelloO.hello_O_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloO.hello_O_at

/-- info: 'Spike.Lib.X64HelloO.hello_O_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloO.hello_O_true
