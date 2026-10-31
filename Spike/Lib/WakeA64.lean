/-
**wake.w on AArch64, whole program: the skeleton.**

The statement `Scc.Sem.A64.CorrectE 2` for the wake program (`main` spawns
`worker` on `(c, me)`, then `waitLoop c`; `worker` does `store rel c 1` and
`unpark j`), proved top-down from a step-wise simulation
(`Scc.Sem.correct_of_stepSim`). The relation has two phases:

* **before the spawn** (`Pre`): the two-slot load lifted from the one-slot
  one (`Spike.Lib.A64TwoSlot.load_two`), the extra thread inert, and a
  one-thread relation `R1` on the one-slot configuration;
* **after the spawn** (`Post`): `Inv2` with hello's protocol
  (`Spike.Lib.HelloProt.HelloProt`) and a thread-0 relation that carries
  main's pre-spawn facts about the flag (`Spike.Lib.Inv2Read.PreC`, the
  "PreC addition to thread-0 PT", `PTw`), plus a kernel-side relation `KR`.

Every piece not proved here is a named field of `WakeObligations`. Proved here: the init, step (the pre/post case
split, the `clone` hand-over via `Spike.Lib.Handover.step_up_cases`, the
threads `≥ 2` case), abort/witness plumbing, the
thread-0-`PT` start (`ptw_start`, `post_start`), the 0/1 split of main's
acquire load of the flag together with the source load reading the
worker's `1` (`wake_ldSt`), and `wake_correctE`.

The source program and its start (`progInitT`, `srcPo`) are `Scc/Sem/SrcOut.lean`'s
with the main thread's own `ThreadId` (namespace `Spike.Lib.WakeT1`);
`SrcOut.lean` itself is untouched.
-/
import Spike.Lib.Inv2Start
import Spike.Lib.A64TwoSlot
import Spike.Lib.WakeRunInv
import Scc.Sem.CorrectEA64
import Scc.Sem.SrcOut
import Spike.Lib.CertReplay

/-! ## The start with the main thread's own `ThreadId` -/

namespace Spike.Lib.WakeT1

open CoreLang CoreTerm TermRun Scc.Sem Scc.Sem.SrcSem

/-- **The main thread's own `ThreadId`** in a start of label stripe `cap`: its box label
`freshLabel 0 (max cap 1) 0 0` (thread 0's first allocation, as `current` would allocate
it, `TermRun.curCfg`), and the word `cst (.loc ⟨l, 0⟩ 0)` naming it (`thrOfTid`). -/
def mainTidLbl (cap : Nat) : WeakMem.AllocLabel := freshLabel 0 (max cap 1) 0 0

/-- **The start of `main(a : ThreadId)`**: one thread entering `main` on its own
`ThreadId` (`tidLbl` set, one allocation made: the box); empty memory; stripe `cap`. -/
def tidStartT (cap : Nat) : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := .tail "main" [] (.var "me"), env := [("me", .tid, [cst (.loc ⟨mainTidLbl cap, 0⟩ 0)])],
             tidLbl := some (mainTidLbl cap), nalloc := 1 }]
  cap := cap

/-- **The start before the setup block of `main(a : S * ThreadId)`**: as `setupStart`,
with `me` the main thread's own `ThreadId` (as `tidStartT`). -/
def setupStartT (cap : Nat) : TermRun.Cfg where
  mem := #[]
  ths := #[{ term := setupTerm, env := [("me", .tid, [cst (.loc ⟨mainTidLbl cap, 0⟩ 0)]), ("u", .unit, [])],
             tidLbl := some (mainTidLbl cap), nalloc := 1 }]
  cap := cap

/-- **The start of program `p`**, by `main`'s argument type (the classes of
`Scc.Frontend.entryOf`): `Unit` starts at `main` (`mainInit`), `Ptr pub Void` at `main`
on the thread's word (`tidInit`), `S * Ptr pub Void` before the setup block
(`setupInit`), `ThreadId` at `main` on the thread's own `ThreadId` (`tidStartT`),
`S * ThreadId` before the setup block with it (`setupStartT`). Any other program has no
start. -/
def progInitT (p : Prog) (cap : Nat) : TermRun.Cfg → Prop :=
  match p.find? (·.name == "main") with
  | some d =>
    match d.argTy with
    | .unit => mainInit cap
    | .ptr .pub .void => tidInit cap
    | .prod _ (.ptr .pub .void) => setupInit cap
    | .tid => (· = tidStartT cap)
    | .prod _ .tid => (· = setupStartT cap)
    | _ => fun _ => False
  | none => fun _ => False

/-- **The source parameters of program `p` with output and `n` threads** (`n ≥ 1`; the
statement takes `n` at least the target's thread slots and above `B.threads`): as
`srcP1o`, with capacity and label stripe `n`. -/
def srcPo (n : Nat) (arch : WeakMem.Arch) (p : Prog) : SrcParams where
  arch := arch
  cap := n
  init := progInitT p n
  hooks := wcHooks p .all arch

/-- **wake.w**, elaborated. -/
def wakeSrc : CoreTerm.Prog :=
  [{
    name := "worker",
    tparams := [],
    idx := [],
    arg := "a",
    argTy := CoreLang.Ty.prod (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int)) (CoreLang.Ty.tid),
    retTy := CoreLang.Ty.unit,
    body := CoreTerm.Expr.split
        (CoreTerm.At.var "a")
        "c"
        "j"
        (CoreTerm.Expr.let_
          "d"
          (CoreTerm.Op.store true (CoreTerm.At.var "c") (CoreTerm.At.lit 1) none)
          (CoreTerm.Expr.let_
            "w"
            (CoreTerm.Op.ext (CoreTerm.ExtName.unpark) (CoreTerm.At.var "j"))
            (CoreTerm.Expr.ret (CoreTerm.At.unit)))) },
  {
    name := "waitLoop",
    tparams := [],
    idx := [],
    arg := "c",
    argTy := CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int),
    retTy := CoreLang.Ty.int,
    body := CoreTerm.Expr.let_
        "d"
        (CoreTerm.Op.load true (CoreTerm.At.var "c"))
        (CoreTerm.Expr.ifeq
          (CoreTerm.At.var "d")
          (CoreTerm.At.lit 1)
          (CoreTerm.Expr.ret (CoreTerm.At.lit 0))
          (CoreTerm.Expr.let_
            "p"
            (CoreTerm.Op.ext (CoreTerm.ExtName.park) (CoreTerm.At.unit))
            (CoreTerm.Expr.tail "waitLoop" [] (CoreTerm.At.var "c") []))) },
  {
    name := "main",
    tparams := [],
    idx := [],
    arg := "me",
    argTy := CoreLang.Ty.tid,
    retTy := CoreLang.Ty.int,
    body := CoreTerm.Expr.let_
        "z"
        (CoreTerm.Op.zero (CoreLang.Ty.int))
        (CoreTerm.Expr.let_
          "o"
          (CoreTerm.Op.new (CoreTerm.At.var "z") (some (CoreLang.Ty.int)))
          (CoreTerm.Expr.let_
            "c"
            (CoreTerm.Op.publish (CoreTerm.At.var "o"))
            (CoreTerm.Expr.let_
              "p"
              (CoreTerm.Op.pair (CoreTerm.At.var "c") (CoreTerm.At.var "me"))
              (CoreTerm.Expr.let_
                "t"
                (CoreTerm.Op.spawn
                  "worker"
                  (CoreTerm.At.var "p")
                  (CoreLang.Ty.prod
                    (CoreLang.Ty.ptr (CoreLang.Mode.pub) (CoreLang.Ty.int))
                    (CoreLang.Ty.tid))
                  [])
                (CoreTerm.Expr.tail "waitLoop" [] (CoreTerm.At.var "c") []))))) }]

theorem wake_start : progInitT wakeSrc 2 = (· = tidStartT 2) := by unfold progInitT; rfl

theorem wake_me : thrOfTid (tidStartT 2) (cst (.loc ⟨mainTidLbl 2, 0⟩ 0)) = some 0 := by decide

end Spike.Lib.WakeT1

/-! ## The skeleton -/

namespace Spike.Lib.WakeA64

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.Handover Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.Inv2Read
open Spike.Lib.Inv2Start Spike.Lib.A64TwoSlot Spike.Lib.WakeT1

/-- The machine configurations (both slot counts). -/
abbrev Cfg : Type := Config isaLSE2 × KState

/-- **The source semantics of wake.w** at `n = 2`. -/
abbrev wakeS (arch : WeakMem.Arch) : SrcSem := SrcSem.source (srcPo 2 arch wakeSrc) wakeSrc

/-- **The data of the relation** (no proof content): the one-thread relation
before the spawn, and, indexed by a ghost record `ι`, the parameters of
`Inv2` after it. -/
structure WakeRel where
  /-- The one-thread relation on the one-slot configuration, before the spawn. -/
  R1 : Cfg → TermRun.Cfg → Prop
  /-- The ghost record of the two-thread phase (spawn record, flag, permit word, ...). -/
  ι : Type
  SR : ι → SpawnRec
  /-- The flag's record. **Review guard**: when instantiated, `(C w).mviewS`
  and `(C w).obS` must be the real `Promises.storeMview` and
  `Promises.storeOb` of the source worker's `store rel c 1`
  (`WeakCore/Promises.lean`, as `HelloProt.CRec` documents them); the
  consumer must not choose its own versions. -/
  C : ι → CRec isaLSE2
  pT : ι → Loc
  P : ι → Inv2Params isaLSE2
  G : ι → Loc → Val → Prop
  own : ι → Nat → isaLSE2.State → List TermRun.Frame → List (Loc × Val)
  /-- main's per-thread relation (without `PreC`, which `PTw` adds). -/
  PT0 : ι → Memory → WeakMem.Memory → Thread isaLSE2 → TermRun.TTh → Prop
  /-- the worker's per-thread relation. -/
  PT1 : ι → Memory → WeakMem.Memory → Thread isaLSE2 → TermRun.TTh → Prop
  /-- the kernel-side relation (slots, held ranges, futex, exit). -/
  KR : ι → Cfg → TermRun.Cfg → Prop
  /-- The worker at its unpark row (`OutT.unpk`, `Spike/Lib/SegThr.lean`): its
  `swpal` of `1` on main's permit word, the source worker at
  `let x = ext unpark a in e` with `a` main's thread id. -/
  atUnpk : Cfg → TermRun.Cfg → Prop
  /-- The worker at its exit row (`OutT.texit`): `thr_worker`'s exit `svc`
  (`x8 = 93`), the source worker at `ret a`. -/
  atTexit : Cfg → TermRun.Cfg → Prop

namespace WakeRel

variable (Q : WakeRel)

/-- **The thread relations of `Inv2`, with the PreC addition**: thread 0's is
main's pre-spawn facts about the flag (`PreC`) and `PT0`; thread 1's is `PT1`. -/
def PTw (w : Q.ι) : Nat → Memory → WeakMem.Memory → Thread isaLSE2 → TermRun.TTh → Prop :=
  fun i tm sm t s => if i = 0 then PreC (Q.SR w) (Q.C w).cT tm t.views ∧ Q.PT0 w tm sm t s else Q.PT1 w tm sm t s

/-- **The relation after the spawn**: `Inv2` with hello's protocol, and `KR`. -/
def Post (Λ : Scc.Sem.Layout) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ w, Inv2 Λ (Q.SR w) (Q.P w) (Q.G w) (Q.own w) (Q.PTw w) (HelloProt (Q.SR w) (Q.C w) (Q.pT w)) t.1 s ∧
    Q.KR w t s

/-- **The relation before the spawn**: a lifted one-slot configuration, the
extra thread inert with no private memory, related by `R1`. -/
def Pre (t : Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ d u, t = up d u ∧ Inert u ∧ (∀ a, privLoad u.st a = none) ∧ d.1.threads.size = d.2.slots.size ∧ Q.R1 d s

/-- **The simulation relation.** -/
def Rw (Λ : Scc.Sem.Layout) (t : Cfg) (s : TermRun.Cfg) : Prop := Q.Pre t s ∨ Q.Post Λ t s

end WakeRel

/-- **Every running thread with promises is certified by an append-free
run** at the current kernel state (`CertReplay.CertOkCNA` under `certSem`,
which gives `CertOkC`) while the process runs (`exited = none`, all
`post_progress` needs; after an `exit_group` there is nothing to certify):
the simulation's certification invariant after the
spawn (the premise of `post_progress`), kept by
`WakeObligations.cert_step`. Append-free, so that the other thread's
appends do not break it (the transports). -/
def CertAll (μ : Marks) (t : Cfg) : Prop :=
  t.2.exited = none → ∀ i th, t.1.threads[i]? = some th → t.2.runs i = true → th.prom ≠ [] →
    CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem

/-- **The conversion of a running thread's certification** at a state:
`CertOkC` (what the semantics' steps carry) to `CertOkCNA` (`CertAll`). -/
def CertConv (μ : Marks) (t : Cfg) : Prop :=
  t.2.exited = none → ∀ i th, t.1.threads[i]? = some th → t.2.runs i = true → th.prom ≠ [] →
    CertOkC Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem →
    CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem

/-- **The obligations of 1.6** at entry state `E`; each field names its owner.
`μ` is the loaded program's marks (`(target (kernel 2) E).marks asm Λ`, the
same at one slot, `marks_two`). -/
structure WakeObligations (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (Q : WakeRel)
    (E : Entry) (Ti : Cfg → List Ev → Prop) : Prop where
  /-- The layout is well formed. -/
  hwf : Λ.WF
  /-- (hello1's one-thread consumer) The program loads at one slot. -/
  hstart : ∃ d, (target (kernel 1) E).load asm Λ = some d
  /-- (hello1's one-thread consumer) The one-slot load is related by `R1`
  to the source start (`wake_start`: `tidStartT 2`). -/
  pre_init : ∀ d, (target (kernel 1) E).load asm Λ = some d → ∃ s0, (wakeS arch).init s0 ∧ Q.R1 d s0
  /-- (main's rows before the spawn) A step of the one-slot
  configuration keeps `R1` and the slot count, with a matching source run. -/
  pre_step : ∀ tid d es d' s, Q.R1 d s → d.1.threads.size = d.2.slots.size →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.R1 d' s' ∧ d'.1.threads.size = d'.2.slots.size
  /-- (`post_start` assembles `Inv2` from the parts) The `clone` into slot 1 is the source
  `spawn`: a source run with no observable event to `Post` after `afterClone`. -/
  spawn : ∀ tid d s th stack tls r, Q.R1 d s → d.1.threads.size = d.2.slots.size →
    d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
    callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
    CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
    ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s'
  /-- (main's target/source rows after the spawn, using `wake_ldSt`;
  park as a stutter; the rely of thread 0 under the worker's writes) A step of
  main keeps `Post`. -/
  post_step0 : ∀ t es t' s, Q.Post Λ t s → (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 0 t es t' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (the worker's target rows and source steps; the rely of
  thread 1) A step of the worker other than its unpark and exit rows keeps
  `Post`. -/
  post_step1 : ∀ t es t' s, Q.Post Λ t s → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- **The source unpark**: the worker's `swpal(1)` on
  main's permit word `⟨B + 16, 8⟩` commits the source worker's
  `ext unpark` (and it is committed nowhere else: main's park is never a
  commit point), keeping `Post`. -/
  unpark_src : ∀ t es t' s, Q.Post Λ t s → Q.atUnpk t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- **The worker's exit**: `thr_worker`'s exit `svc`
  (the `texit` row) leaves the source worker at `ret`, keeping `Post`. -/
  worker_done : ∀ t es t' s, Q.Post Λ t s → Q.atTexit t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- Progress and layout before the spawn, of the lifted
  configuration: at main's `clone` the one-slot configuration faults (no
  dormant slot, `faultAt`) while the lifted one steps, so this is not a
  one-slot statement (`Spike.Lib.WakePre.Pre1.pre_progress` reduces it to
  one slot off the `clone`, `progress_up`). -/
  pre_progress : ∀ d u s, Q.R1 d s → Inert u → (∀ a, privLoad u.st a = none) →
    d.1.threads.size = d.2.slots.size →
    (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) (up d u) ∧
      InLayout (M := machine (kernel 2)) Λ (up d u)
  /-- (`WakeProgress.post_progress_of`) Progress and layout after the
  spawn, under the run invariant (`WakeRunInv.RunInv`) and the certification
  invariant (`CertAll`). -/
  post_progress : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → CertAll ((target (kernel 2) E).marks asm Λ) t →
    (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) t ∧ InLayout (M := machine (kernel 2)) Λ t
  /-- The program's instructions are in the wide fragment
  (`WakeRunInv.runInv_load`: the run invariant at the load). -/
  hwide : ∀ prog, (textProgram asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true
  /-- (the transports for the thread that does not step) A step
  from `Post` to `Post` keeps `CertAll`. -/
  cert_step : ∀ tid t es t' s s', Q.Post Λ t s → CertAll ((target (kernel 2) E).marks asm Λ) t →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Q.Post Λ t' s' →
    CertAll ((target (kernel 2) E).marks asm Λ) t'
  /-- (main's wrapper, from `relW0`; the worker's fact) At `Post` a running
  thread's certification is append-free (`CertReplay.certOkCNA_of_certOkC`):
  the parent's after the `clone`. -/
  hconv : ∀ t s, Q.Post Λ t s → CertConv ((target (kernel 2) E).marks asm Λ) t
  /-- `Ti` (the structure's parameter; before the spawn `TIC` on
  thread 0 of `up d u`) is a **trace invariant** of reachable
  two-slot configurations, handed to `pre_abort`/`post_abort` (whose
  `writeErr`/`threads` cases need the trace, not just the relation): it
  holds at the load with the empty trace. -/
  ti_load : ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → Ti t0 []
  /-- A step of a related configuration extends `Ti` by its events. -/
  ti_step : ∀ tid t es t' s pre, Q.Rw Λ t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ti t pre → Ti t' (pre ++ es)
  /-- An abort step of the one-slot configuration before the spawn is
  justified (a `clone` emits no event, so every abort is such a step). -/
  pre_abort : ∀ tr d u s tid es d' k, (wakeS arch).Reach (obs tr) s → Q.R1 d s → Inert u →
    (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size → Ti (up d u) tr →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → Ev.abort k ∈ es →
    ∃ w i, Components (machine (kernel 2)) Λ w (up d u) s ∧ w.thr i = some tid ∧ AbortJustified B (wakeS arch) tr s i k
  /-- (the stub rows) An abort step after the spawn is justified. -/
  post_abort : ∀ tr t s tid es t' k, (wakeS arch).Reach (obs tr) s → Q.Post Λ t s → Ti t tr →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ev.abort k ∈ es →
    ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧ AbortJustified B (wakeS arch) tr s i k
  /-- The explicit witness before the spawn. -/
  pre_wit : ∀ d u s, Q.R1 d s → Inert u → (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
    ∃ w, Components (machine (kernel 2)) Λ w (up d u) s
  /-- (`own`/`PhRec2`) The explicit witness after the spawn. -/
  post_wit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s

/-! ## Proved pieces -/

section Proved

variable {Λ : Scc.Sem.Layout} {Q : WakeRel}

/-- **The PreC addition at the clone**: main's thread-0 relation holds for
the parent after its return when `PT0` does and the latest write of the flag
has value `0` (`preC_parent`). -/
theorem ptw_start {w : Q.ι} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isaLSE2} {stack : Nat} {r : BitVec 64}
    {sm : WeakMem.Memory} {s0 : TermRun.TTh} (hSR : Q.SR w = ⟨d.1.mem.last, sm.size, lbl, lsize⟩)
    (hi : Inv1 Λ lbl lsize ts th d.1.mem sm) (hp : th.prom = []) {j : Nat}
    (hj : d.1.mem.read? (Q.C w).cT j = some 0) (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (h0 : Q.PT0 w d.1.mem sm (retThread abi (parentPre abi d.2 0 th stack) r) s0) :
    Q.PTw w 0 d.1.mem sm (retThread abi (parentPre abi d.2 0 th stack) r) s0 := by
  simp only [WakeRel.PTw, ↓reduceIte]
  refine ⟨?_, h0⟩
  rw [hSR]
  exact preC_parent (K := abi) hi hp hj hjl

/-- **`Post` at the clone**, from `inv2_start`'s parts with the PreC addition
(`ptw_start`) and the kernel relation: what the `spawn` obligation's owners
assemble. -/
theorem post_start {w : Q.ι} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isaLSE2} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    (hsub0 : ∀ L v, (L, v) ∈ Q.own w 0 (retThread abi (parentPre abi d.2 0 th stack) r).st s0.stack → (L, v) ∈ own₀)
    (hsub1 : ∀ L v, (L, v) ∈ Q.own w 1 (childAfter abi d.2 0 th stack tls).st s1.stack → (L, v) ∈ own₀)
    (hdisj : ∀ L v v', (L, v) ∈ Q.own w 0 (retThread abi (parentPre abi d.2 0 th stack) r).st s0.stack →
      (L, v') ∈ Q.own w 1 (childAfter abi d.2 0 th stack tls).st s1.stack → False)
    (hcov0 : ∀ L v, (L, v) ∈ Q.own w 0 (retThread abi (parentPre abi d.2 0 th stack) r).st s0.stack → (Q.P w).cov 0 L)
    (hcov1 : ∀ L v, (L, v) ∈ Q.own w 1 (childAfter abi d.2 0 th stack tls).st s1.stack → (Q.P w).cov 1 L)
    {j : Nat} (hj : d.1.mem.read? (Q.C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (hPT0 : Q.PT0 w d.1.mem s.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hPT1 : Q.PT1 w d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1)
    (hProt : HelloProt (Q.SR w) (Q.C w) (Q.pT w) d.1.mem (retThread abi (parentPre abi d.2 0 th stack) r)
      (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : Q.KR w (afterClone abi d 0 th stack tls r) s) :
    Q.Post Λ (afterClone abi d 0 th stack tls r) s := by
  refine ⟨w, ?_, hKR⟩
  have hPT1' : Q.PTw w 1 d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1 := by
    simp only [WakeRel.PTw]; exact hPT1
  have h := inv2_start (K := abi) (P := Q.P w) (G := Q.G w) (own := Q.own w) (PT := Q.PTw w)
    (Prot := HelloProt (Q.SR w) (Q.C w) (Q.pT w)) (lbl := lbl) (lsize := lsize) (tls := tls)
    h1 hs hi hp hmsgs hin hfits hG hb hown hsp0 hsp1 hs0 hs1 hfrz hfoot hsub0 hsub1 hdisj hcov0 hcov1
    (ptw_start hSR hi hp hj hjl hPT0) hPT1' hProt
  rw [hSR] at h ⊢; exact h

/-- **main's view of `Post`**: the two threads, main's `PreC` and `PT0`, and
hello's protocol. -/
theorem post_main {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) :
    ∃ w t0 t1 s0 s1 ts tp sp, t.1.threads = #[t0, t1] ∧ s.ths = #[s0, s1] ∧
      PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views ∧ Q.PT0 w t.1.mem s.mem t0 s0 ∧
      HelloProt (Q.SR w) (Q.C w) (Q.pT w) t.1.mem t0 t1 s.mem s0 s1 ts tp sp := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, h1, h2, -, h0, -, hp⟩, -⟩ := h
  simp only [WakeRel.PTw, ↓reduceIte] at h0
  exact ⟨w, t0, t1, s0, s1, ts, tp, sp, h1, h2, h0.1, h0.2, hp⟩

end Proved

/-- **main's acquire load of the flag: the 0/1 split and the source glue.**
A load of `cT` by main (`PreC` on its views, hello's protocol) leaves the
memory, keeps `PreC`, and reads `0` (the source stutters: `waitLoop` loops)
or `1`, and then the worker's source message `kc` holds `1` and every source
load of `cS` has an outcome reading it (`stepOne_load_c`, `stepLoad_kc`). -/
theorem wake_ldSt {I : ISA} (A : Arch) {R : SpawnRec} {C : CRec I} {pT : Loc} {tm : Memory}
    {t0 t1 : Thread I} {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    (hp : HelloProt R C pT tm t0 t1 sm s0 s1 ts tp sp) (hpre : PreC R C.cT tm t0.views)
    {kl : Kraken.LoadKind} {xcl : Bool} {g : Val → I.State}
    (hex : I.exec t0.st = some (.load kl xcl C.cT fun v => .done (g v))) {tid : Nat}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t0 tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) :
    o.mem = tm ∧ PreC R C.cT tm o.thread.views ∧ ∃ v, o.thread.st = g v ∧
      (v = 0 ∨ (v = 1 ∧ ∃ kc m, sm[kc]? = some m ∧ m.val = .num 1 ∧
        ∀ (arch : WeakMem.Arch) (pairs : List Nat) (th : Promises.Thread) (dst : WeakMem.Reg)
          (deps : List WeakMem.Reg) (acq : Bool),
          ∃ th' ∈ Promises.stepLoad arch sm pairs th dst C.cS deps acq, th'.regs dst = ⟨m.val, m.view, kc⟩)) := by
  obtain ⟨oc, hc⟩ := hp
  obtain ⟨hm, hpre', v, hst, h01⟩ := stepOne_load_c A hc hpre hex hstep ho
  refine ⟨hm, hpre', v, hst, ?_⟩
  rcases h01 with h0 | ⟨Tc, kc, rfl, h1⟩
  · exact .inl h0
  · obtain ⟨-, -, -, -, m, hm, -, hv⟩ := hc.some_msg Tc kc rfl
    refine .inr ⟨h1, kc, m, hm, hv, fun arch pairs th dst deps acq => ?_⟩
    obtain ⟨m', hm', -, hres⟩ := stepLoad_kc hc arch pairs th dst deps acq
    rw [hm] at hm'
    cases hm'
    exact hres

section Main

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel} {E : Entry}

/-- **The child after a `clone` has no promise.** -/
theorem wakeChildAfter_prom {x : KState} {tid : Nat} {th : Thread isaLSE2} {stack tls : Nat} :
    (childAfter abi x tid th stack tls).prom = [] := by
  unfold childAfter
  split <;> rfl

/-- **`CertAll` after the `clone`** of a one-thread configuration: the parent
by the `clone`'s `CertAfter` converted (`hcv`), the child with no promise. -/
theorem certAll_afterClone {μ : Marks} {d : Cfg} {tid : Nat} {th : Thread isaLSE2} {stack tls : Nat}
    {r : BitVec 64} (hsz : d.1.threads.size = 1) (h1 : d.1.threads[tid]? = some th)
    (hc : CertAfter abi Arch.armv8 μ tid (afterClone abi d tid th stack tls r))
    (hcv : CertConv μ (afterClone abi d tid th stack tls r)) :
    CertAll μ (afterClone abi d tid th stack tls r) := by
  intro hx i t' ht' hr hp
  have htid : tid = 0 := by
    have := (Array.getElem?_eq_some_iff.mp h1).1
    omega
  subst htid
  rcases i with _ | _ | i
  · exact hcv hx 0 t' ht' hr hp (hc t' ht')
  · exfalso
    apply hp
    have e : (afterClone abi d 0 th stack tls r).1.threads[1]? = some (childAfter abi d.2 0 th stack tls) := by
      simp only [afterClone]
      rw [Array.getElem?_push]
      simp [hsz]
    rw [e] at ht'
    cases ht'
    exact wakeChildAfter_prom
  · exfalso
    have : (afterClone abi d 0 th stack tls r).1.threads.size = 2 := by simp [afterClone, hsz]
    have := (Array.getElem?_eq_some_iff.mp ht').1
    omega

/-- **A step before the spawn**: a matching source run to `Pre`, or (the
`clone`) to `Post` with `CertAll` (`certAll_afterClone`). -/
theorem wake_stepPre {Ti : Cfg → List Ev → Prop} (O : WakeObligations arch Λ B asm Q E Ti) {tid : Nat}
    {t t' : Cfg} {es : List Ev} {s : TermRun.Cfg} (hR : Q.Pre t s)
    (hs : (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t') :
    ∃ s', (wakeS arch).Run s (obs es) s' ∧
      (Q.Pre t' s' ∨ (Q.Post Λ t' s' ∧ CertAll ((target (kernel 2) E).marks asm Λ) t')) := by
  obtain ⟨d, u, rfl, hu, hpl, hn, hR⟩ := hR
  obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨rfl, th, stack, tls, r, h1, h2, h3, h4, h5, h6, h7, rfl, hc⟩⟩ :=
    step_up_cases hn hs
  · obtain ⟨s', hr, hR', hn'⟩ := O.pre_step tid d es d' s hR hn hd'
    exact ⟨s', hr, .inl ⟨d', u, rfl, hu, hpl, hn', hR'⟩⟩
  · obtain ⟨s', hr, hP⟩ := O.spawn tid d s th stack tls r hR hn h1 h2 h3 h4 h5 h6 h7 hc
    have hsz : d.1.threads.size = 1 := by
      obtain ⟨-, ⟨t0, t1, -, -, -, -, -, hT, -⟩, -⟩ := hP
      have := congrArg Array.size hT
      simp [afterClone] at this
      omega
    exact ⟨s', hr, .inr ⟨hP, certAll_afterClone hsz h1 hc (O.hconv _ _ hP)⟩⟩

/-- **A step after the spawn** keeps `Post`, with a matching source run. -/
theorem wake_stepPost {Ti : Cfg → List Ev → Prop} (O : WakeObligations arch Λ B asm Q E Ti) {tid : Nat}
    {t t' : Cfg} {es : List Ev} {s : TermRun.Cfg} (hP : Q.Post Λ t s)
    (hs : (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t') :
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  rcases tid with _ | _ | tid
  · exact O.post_step0 t es t' s hP hs
  · by_cases hu : Q.atUnpk t s
    · exact O.unpark_src t es t' s hP hu hs
    by_cases hx : Q.atTexit t s
    · exact O.worker_done t es t' s hP hx hs
    exact O.post_step1 t es t' s hP hu hx hs
  · exfalso
    obtain ⟨⟨th, hth⟩, -, -⟩ := hs.runs
    obtain ⟨-, ⟨t0, t1, -, -, -, -, -, h1, -⟩, -⟩ := hP
    rw [h1] at hth
    simp at hth

/-- **The simulation relation with its invariants**: the run invariant
(`WakeRunInv.RunInv`, every reachable configuration), and before the spawn
`Pre`, after it `Post` with the certification invariant `CertAll`. -/
def Rx (Q : WakeRel) (Λ : Scc.Sem.Layout) (E : Entry) (μ : Marks) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  WakeRunInv.RunInv Λ E t ∧ (Q.Pre t s ∨ (Q.Post Λ t s ∧ CertAll μ t))

theorem Rx.rw {μ : Marks} {t : Cfg} {s : TermRun.Cfg} (h : Rx Q Λ E μ t s) : Q.Rw Λ t s :=
  h.2.imp id And.left

/-- **The step-wise simulation.** -/
theorem wake_stepSim {Ti : Cfg → List Ev → Prop} (O : WakeObligations arch Λ B asm Q E Ti) :
    StepSim (target (kernel 2) E) (wakeS arch) Λ asm (Rx Q Λ E ((target (kernel 2) E).marks asm Λ)) where
  init := by
    intro t0 h0
    have hri := WakeRunInv.runInv_load O.hwide h0
    obtain ⟨d, u, hd, rfl, hu, hpl, hn⟩ := load_two h0
    obtain ⟨s0, hi, hR⟩ := O.pre_init d hd
    exact ⟨s0, hi, hri, .inl ⟨d, u, rfl, hu, hpl, hn, hR⟩⟩
  step := by
    intro tid t es t' s hR hs
    change (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' at hs
    rcases hR with ⟨hri, hpre | ⟨hP, hca⟩⟩
    · obtain ⟨s', hr, h'⟩ := wake_stepPre O hpre hs
      exact ⟨s', hr, WakeRunInv.runInv_step hri hs, h'⟩
    · obtain ⟨s', hr, hP'⟩ := wake_stepPost O hP hs
      exact ⟨s', hr, WakeRunInv.runInv_step hri hs, .inr ⟨hP', O.cert_step tid t es t' s s' hP hca hs hP'⟩⟩

/-- **The trace invariant along a run**: from a related configuration
satisfying `Ti` with trace `pre`, a run keeps `Ti` with the run's events
appended (by `ti_step`, the relation carried by `wake_stepSim`). -/
theorem wake_tiRun {Ti : Cfg → List Ev → Prop} (O : WakeObligations arch Λ B asm Q E Ti) {t t' : Cfg} {tr : List Ev}
    (hr : (machine (kernel 2)).Run ((target (kernel 2) E).marks asm Λ) t tr t') {s : TermRun.Cfg}
    (hR : Rx Q Λ E ((target (kernel 2) E).marks asm Λ) t s) {pre : List Ev} (hT : Ti t pre) :
    Ti t' (pre ++ tr) := by
  induction hr generalizing s pre with
  | refl => simpa using hT
  | step hs _ ih =>
    obtain ⟨tid, hs⟩ := hs
    obtain ⟨s1, -, hR1⟩ := (wake_stepSim O).step _ _ _ _ _ hR hs
    simpa [List.append_assoc] using ih hR1 (O.ti_step tid _ _ _ s pre hR.rw hs hT)

/-- **wake.w is correct on AArch64 with two slots**, given the obligations
at every admissible entry state. -/
theorem wake_correctE (Ti : Entry → Cfg → List Ev → Prop)
    (O : ∀ E : Entry, E.Ok Λ → WakeObligations arch Λ B asm Q E (Ti E)) :
    CorrectE 2 (wakeS arch) Λ B asm := by
  intro E hE
  have O := O E hE
  have hsim := wake_stepSim O
  refine correct_of_stepSim hsim O.hwf ?_ ?_ ?_ ?_
  · obtain ⟨d, hd⟩ := O.hstart
    obtain ⟨u, hu, -⟩ := load_one hd
    exact ⟨_, hu⟩
  · intro t0 tr t h0 hr
    obtain ⟨s, -, hri, hR⟩ := hsim.reach h0 hr
    rcases hR with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, hca⟩
    · exact O.pre_progress d u s hR hu hpl hn
    · exact O.post_progress t s hP hri hca
  · intro t0 tr t tid es t' k s h0 hr hreach hR hs hk
    change (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' at hs
    have hTi : Ti E t tr := by
      obtain ⟨s0, -, hR0⟩ := hsim.init t0 h0
      simpa using wake_tiRun O hr hR0 (O.ti_load t0 h0)
    rcases hR.2 with ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩
    · obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨rfl, -⟩⟩ := step_up_cases hn hs
      · exact O.pre_abort tr d u s tid es d' k hreach hR hu hpl hn hTi hd' hk
      · cases hk
    · exact O.post_abort tr t s tid es t' k hreach hP hTi hs hk
  · intro t s hR
    rcases hR with ⟨hri, ⟨d, u, rfl, hu, hpl, hn, hR⟩ | ⟨hP, -⟩⟩
    · exact O.pre_wit d u s hR hu hpl hn
    · exact O.post_wit t s hP hri

end Main

/-- info: 'Spike.Lib.WakeA64.wake_correctE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_correctE

end Spike.Lib.WakeA64
