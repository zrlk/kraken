/-
**wake.w's pre-spawn obligations `O` at every admissible entry** (AArch64):
`WakePreAsm.pre1T_of_seg` at the entry's marks, with `NoObs`
(`WakeNoObs.Pre1T.noObs`, `hw` by `rsah_hw` from the write tail `Dt`) and
`VPre` (`WakeSpawnLt.pre1T_vpre`), `VPreC`
(`SpawnCohSteps.pre1T_vpreC`) and `VFlag` (`SpawnFlag.pre1T_vflag`): the
relation `R1O … = (((RSAH … ∧ NoObs) ∧ VPre) ∧ VPreC) ∧ VFlag`, which
carries what `WakeSpawnLt.hlt0_of` reads (`RSAH`, `VPre`, and `hex` from
`NoObs`), the spawn's coherence (`VPreC`) and the source flag cell
(`VFlag`). Each conjunct is added on the right by its
`Pre1T` lifter, applied in order in `wake_O_at`; a new conjunct is one more
`∧` in `R1O` and one more lifter there.

- `R1O`: the relation, from the instance data `OData` at the marks `μ`.
- `OData`: the instance data of one entry (the consumer's levels `L0`,
  `ls0`, fragments `W0`, `inv0`, `W1`, `inv1`, the take site `a`, the clone
  path `Cl`, the write tail `Dt`, the read side `rd`, the guarantee `G`, the
  ownership `own`, the arena `ar`, the two stack ranges `r0`, `r1`).
- `OPrem`: `pre1T_of_seg`'s premises at an entry and its data:
  - the wc chain compositions: `h0` (from the entry to the heap
    box: `scc_rt_start`, `scc_rt_main`, `wc_main` up to the allocation) and
    `h1` (from the box's landing `AllocLand` to the `clone`, per fresh
    label `l`, base `b`, size `n`);
  - per-state facts (the analogue of hello1's `A64Hello1I` /
    `A64Hello1SFactsN`): `hW0` (`SFactsACH` at every state of `W0` under
    `inv0`, at the levels `L0`/`ls0`) and `hW1` (at every state of `W1 l b n`,
    at the updated levels `A64ConsumerA.upd L0 l b`/`updN ls0 l n`), both over the
    fragment's invariant `I2 ar L0 ls0 inv0 inv1` and the tails `Dt Ab Cl Ac`;
  - the take site `ha`, the split `hsplit` and the ranges, the side
    facts, the load's relation `hinit` (`WakePreAsm.wake_init`) and `TIC`
    there `hti0`.
- `wake_O_at`: `Pre1T` at one entry from `OPrem`.
- `wake_O`: `O` at every admissible entry, data and premises per entry.
-/
import Spike.Lib.WakeNoObs
import Spike.Lib.WakeSpawnLt
import Spike.Lib.SpawnCohSteps
import Spike.Lib.SpawnFlag

namespace Spike.Lib.WakeO

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64
open Spike.Lib.WakePreTi (Pre1T)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.SpawnViewLtSteps (VPre)
open Spike.Lib.SpawnCohSteps (VPreC)
open Spike.Lib.SpawnFlag (VFlag)
open Spike.Lib.WakeNoObs (NoObs)

/-- **The instance data of one entry** (see the module doc). -/
structure OData where
  rd : TermRun.Word → Prop
  G : Loc → Val → Prop
  own : OwnS
  ar : Arena
  Cl : State → Prop
  Dt : State → Prop
  L0 : Lbl
  ls0 : Lsize
  a : Int64
  W0 : FragS isaLSE2
  inv0 : FragS isaLSE2
  W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2
  inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2
  r0 : Range
  r1 : Range

/-- **The pre-spawn relation** at data `D` and marks `μ`:
`RSAH` at `I2 …` and `HeldOk2 Λ r0 r1`, with `NoObs`, `VPre`, `VPreC` and `VFlag`,
conjoined on the right in the order `wake_O_at` adds them. -/
def R1O (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (μ : Marks) (D : OData) (d : Cfg) (s : TermRun.Cfg) : Prop :=
  (((RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc D.G D.own (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) (HeldOk2 Λ D.r0 D.r1) μ D.ar
    d s ∧ NoObs d s) ∧ VPre s) ∧ VPreC s) ∧ VFlag s

/-- **`pre1T_of_seg`'s premises at one entry** (see the module doc for the
owners); `μ` is the entry's marks. -/
structure OPrem (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (E : Entry)
    (Ab Ac : State → Prop) (D : OData) : Prop where
  /- the segments -/
  h1 : ∀ l b n, D.L0 l = none → AllocLand D.ar.heap D.ar.cells b n →
    SegInvS (D.W1 l b n) (TakeCKS D.a D.Cl) wakeSrc (A64ConsumerA.upd D.L0 l b)
      (msOfA Λ ((target (kernel 2) E).marks asm Λ) D.rd D.G D.own D.ar (fun _ _ _ _ _ => False) (A64ConsumerA.upd D.L0 l b)
        (A64ConsumerA.updN D.ls0 l n)) (D.inv1 l b n)
  h0 : SegInvS D.W0 (TakeCKS D.a D.Cl) wakeSrc D.L0
    (msOfA Λ ((target (kernel 2) E).marks asm Λ) D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) D.L0 D.ls0)
    D.inv0
  /- the per-state facts -/
  hW0 : ∀ s c fs, D.inv0 s c fs → D.W0 s c fs →
    SFactsACH Λ ((target (kernel 2) E).marks asm Λ) wakeSrc D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1)
      D.L0 D.ls0 s c fs D.Dt Ab D.Cl Ac
  hW1 : ∀ l b n s c fs, D.L0 l = none → AllocLand D.ar.heap D.ar.cells b n → D.W1 l b n s c fs →
    SFactsACH Λ ((target (kernel 2) E).marks asm Λ) wakeSrc D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1)
      (A64ConsumerA.upd D.L0 l b) (A64ConsumerA.updN D.ls0 l n) s c fs D.Dt Ab D.Cl Ac
  /- the take, the ranges, the side facts, the load -/
  ha : ((target (kernel 2) E).marks asm Λ).site .take = some D.a.toBitVec.toNat
  hsplit : ∀ lbl lsize s c fs hl, I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize s c fs → HeldOk2 Λ D.r0 D.r1 s hl →
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
  hP : HookOK (srcPo 2 arch wakeSrc) wakeSrc
  hClc : ∀ s, D.Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)
  hsafe : SrcSafeS (srcPo 2 arch wakeSrc) wakeSrc (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1)
  hrd : SrcRd (srcPo 2 arch wakeSrc) wakeSrc D.rd
  hwf : Λ.WF
  hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → D.G (wordLoc a) v
  hok : D.ar.OK
  hB : B.cells = D.ar.cells
  hdt : ∀ s buf n, D.Dt s → Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)
  hinit : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d →
    ∃ s0, (wakeS arch).init s0 ∧
      RSAH Λ (srcPo 2 arch wakeSrc) wakeSrc D.G D.own (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) (HeldOk2 Λ D.r0 D.r1)
        ((target (kernel 2) E).marks asm Λ) D.ar d s0
  hti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d

/-- **`Pre1T` at one entry** (see the module doc). -/
theorem wake_O_at {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
    {Ab Ac : State → Prop} {D : OData} (h : OPrem arch Λ B asm E Ab Ac D) :
    Pre1T arch Λ B asm E (R1O arch Λ ((target (kernel 2) E).marks asm Λ) D) Ab Ac := by
  have hO := WakePreAsm.pre1T_of_seg rfl h.h1 h.h0 h.ha h.hW0 h.hW1 h.hsplit h.hs0 h.hs1 h.hz0 h.hz1 h.hro h.hd
    h.hw0 h.hw1 h.hP h.hClc h.hsafe h.hrd h.hwf h.hGpl h.hok h.hB h.hdt h.hinit h.hti0
  obtain ⟨-, -, -, hWr, -⟩ := inst_of_segWA2CH2 h.h1 h.h0 h.ha h.hW0 h.hW1 h.hsplit h.hs0 h.hs1 h.hz0 h.hz1 h.hro
    h.hd h.hw0 h.hw1
  refine Spike.Lib.SpawnFlag.pre1T_vflag ?_ (fun _ _ h => h.1.2)
  exact Spike.Lib.SpawnCohSteps.pre1T_vpreC <| Spike.Lib.WakeSpawnLt.pre1T_vpre <|
    WakeNoObs.Pre1T.noObs hO (WakeNoObs.rsah_hw
      (fun _ _ _ _ _ hI hsys buf n hc => h.hdt _ buf n (hWr _ _ _ _ _ hI hsys 1 buf n hc) hc))

/-- **`O` at every admissible entry** (see the module doc): the final
statement's `O` at `R1 E := R1O arch Λ (marks E) (D E)`. -/
theorem wake_O {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Ab Ac : State → Prop}
    {D : Entry → OData} (h : ∀ E : Entry, E.Ok Λ → OPrem arch Λ B asm E Ab Ac (D E)) :
    ∀ E : Entry, E.Ok Λ → Pre1T arch Λ B asm E (R1O arch Λ ((target (kernel 2) E).marks asm Λ) (D E)) Ab Ac :=
  fun E hE => wake_O_at (h E hE)

end Spike.Lib.WakeO

/-- info: 'Spike.Lib.WakeO.wake_O_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeO.wake_O_at

/-- info: 'Spike.Lib.WakeO.wake_O' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeO.wake_O
