/-
**wake.w on AArch64: the spawn obligation at the instance**: `spawn_R`, the `spawn` hypothesis of
`WakeAssemblyR.wake_obligations_R`, at the relation `WakeWorkerR.QIR` of the
placed layout `L := RuntimeLayout.ofPlaceW hp i` over the records
satisfying `GhOK L.Λ` (any marks `μ`, main's side `M` with `wakeM`'s `Mi`
and `cw`), and `wake_obligations_RS`, `wake_obligations_R` with it.

`spawn_R` follows `WakeSpawn.spawn_of` (`WakeStart.post_startW`,
`HelloProt.helloProt_start`, `WakeKR.kr_start`), the record `w` the clone's
`WakeOkW.recW`:

- the child in `Wi` by `WakeSpawnWQ.spawn_workerPostQ` (its `StOk` facts
  by `WakeChildSt.childSt_I`/`childSt_al`; the handed range, the TCB and the
  thread from `ClonePre` against the premises of the `spawn` field);
- main's `PT0` by `A64WakeMainClosedWS.main_closed_ws` (`hK` by `rfl`);
- `¬ passT` at the child by `WCompat.pass` (`hpass`) at `wkTail`,
  `¬ passS` by `wkTail`.

**Open** (premises of `spawn_R`):

- `hpre : HPre` (the pre-spawn segment end): at the clone of thread `tid`,
  `tid = 0`, a source run to the spawned configuration and `PreR`, among
  its fields `hlt` and `hsp` (the run shape `s' = spawnCfg ...` from the source run,
  with the bound, both by `hlt0_of`); the private-memory invariant at
  `d` is not a field but `R1`'s (`WakePrivR.VPriv`, `WakeObligationsRP`);
- `hMainR : HMainR`: `main_closed_ws`'s hypotheses past the clone,
  `MainWS` (field by field: the segment end, the source side,
  the instance lemmas `WakeMainInst` / `WakeMainInstD`);
- (closed) `HView`, the worker's store view and ordering bound at the
  spawn below the source memory's size: `hView`, by `WakeSpawnLt.hview_R` at `PreR.hlt` (the run shape and the bound);
- instance facts: `hprog`, `hlo`, `hpin2`, `hinit2`, `hwide` (the
  executable wide), `hpass` (`WakeWorkerR.hC_IR`'s `pass`).

**Satisfiability.** `HPre` is existential (the witnesses are picked at the
concrete run); `HMainR` and `HView` are universal over every witness tuple
with `SpawnPrem`, the run and `PreR`, so they must follow from `PreR` alone.
`d`, `s` are the field's; `th` is pinned by `SpawnPre.threads`, `r1`,
`stack`, `tls` and `r0'` by `ClonePre`/`SpawnPre.held`/`top` and `x3`, `l`
by `c`'s value, `w` by `hw`, `s0`, `s1` by `SpawnPre.ths` as `s'`'s threads.
The placement `lbl`, `lsize` (`SpawnPre.SR`, the record's) is
not unique, so `MainWS` must follow at any placement with `SpawnPre.inv1`;
the rest (`A`, the frames, `tp`, ...) is under the conclusions'
existentials. The run's end `s'`
is pinned by `PreR.hlt` (`WakeSpawnLt.LtPre`: `s' = TermSpawnStep.spawnCfg
s 0 th0 ...`, with `SpawnVLt` bound), so `s0`, `s1` are functions of
`s`.
-/
import Spike.Lib.WakeAssemblyR
import Spike.Lib.WakeSpawn
import Spike.Lib.WakeSpawnWQ
import Spike.Lib.WakeChildSt
import Spike.Lib.A64WakeMainClosedWS
import Spike.Lib.WakeSpawnLt
import Spike.Lib.DmemPriv
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeSpawnR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeT1
open Spike.Lib.WakePreTi (Pre1T TiPre)
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.WakeInst (Gh wakeMs mainWR mainInv)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.WakeOkW (recW)
open Spike.Lib.WakeSpawn (SpawnPrem SpawnPre)
open Spike.Lib.WakeTcbArea (Q2)
open Spike.Lib.WakePreA (ClonePre cloneAt)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.WakeMainSrc (waitC)
open Spike.Lib.WakeM0 (mTail wlIf MTerm EnvC)
open Scc.Cert.Rt.A64 (endOf)

/-! ## main's facts past the clone -/

/-- **`main_closed_ws`'s hypotheses past the clone** (all but the listing's
`hp`/`hend`, the clone `h`, the child's id bounds `hr0`/`hrm` and `hK`),
at main's control `cP`, the clone's configuration `t`, the handed range `r1`
and the child's id `r`. -/
structure MainWS (exe : _root_.Executable) (endPc : Int64) (Λ' : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ms : MemSide isaLSE2)
    (t : Cfg) (r1 : Range) (r : BitVec 64) (cP : Ctl) (R : Spike.Lib.Region) (F0 : MachineData → Prop)
    (A x29 ra tp : BitVec 64) (w : TermRun.Word) (tyP : Ty) {γ : Type} (Rg : γ → Spike.Lib.Region)
    (Fg : γ → MachineData → Prop) (fp : γ → BitVec 64) (g0 : γ) : Prop where
  hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP
  hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80
  hRlo : R.lo = -96
  hRhi : R.hi = 16
  hR : R.OK
  htop : r1.lo + r1.size ≤ 2 ^ 64
  htP : cP.term = mTail
  hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])
  hval : ValRep lbl w.val A.toNat
  hloc : LocRep lbl w.val A.toNat 0
  hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label
  hRg : Rg g0 = R
  hfp : fp g0 = x29
  hFg : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
    DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → Fg g0 m
  hF : ∀ g, FStable (Rg g) (Fg g)
  hRo : ∀ g, (Rg g).OK
  hal : ∀ g, (Rg g).base.toNat % 16 = 0
  hlo : ∀ g, (Rg g).lo ≤ -96
  hhi : ∀ g, 16 ≤ (Rg g).hi
  hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none
  hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64
  htp4 : (tp + 16#64).toNat % 4 = 0
  htls : ∀ g,
    SegW (mainWR (_root_.Executable.labels exe).label exe Λ' lbl lsize) (fun _ _ => False)
      Spike.Lib.WakeT1.wakeSrc lbl ms
      (At exe endPc (Rg g) (Fg g)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx
          (waitC w) "d" wlIf (.ptr .pub .int) (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
      (At exe endPc (Rg g) (Fg g)
        (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx
          (waitC w) "d" wlIf (.ptr .pub .int) (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1))
  hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0
  hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
    (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
    At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
      fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit Spike.Lib.WakeT1.wakeSrc ms s c 0
  hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s
  hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ') wr ⟨A, 8⟩ = true
  hmP : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') cP
  hmE : ∀ c, Spike.Lib.A64.WaitLoop.Past (waitC w) "d" wlIf (.ptr .pub .int)
    (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
    Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') c

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The records. -/
abbrev ιR := {g : Gh // GhOK (RuntimeLayout.ofPlaceW hp i).Λ g}

/-- The layout's end of text. -/
abbrev endR : Int64 :=
  endOf (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx

/-- The worker's side at the layout. -/
noncomputable abbrev DR : WSide (ιR hp i) :=
  WakeWorkerR.wakeDR hp i (GhOK (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).exe
    (endR hp i) (RuntimeLayout.ofPlaceW hp i).pfx

/-- The relation at the layout (`WakeAssemblyR.QR` at `μ := μR`, `M := MR`). -/
noncomputable abbrev QG (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : WakeRel :=
  WakeWorkerR.QIR hp i (GhOK (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).exe (endR hp i)
    (RuntimeLayout.ofPlaceW hp i).pfx arch R1 μ M r0 r1

/-- **The pre side's facts at main's clone** (the segment end): the
clone `ClonePre` at `X` (the clone's `svc` with `x3` the TCB of a `Q2`
request `q`), `c`'s label `l`, the record `w` the clone's `recW` with
`SpawnPre` at it, the spawned worker's argument words `w1`, `w2`, main's
source thread `s0`'s `PT0` facts and main's id word `x10 = pinA + 8`. -/
structure PreR (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks) (M : WakeM0.MSide (ιR hp i))
    (r0 r1 : ιR hp i → Range) (d : Cfg) (th : Thread isaLSE2) (stack : Nat) (s s' : TermRun.Cfg)
    (w : ιR hp i) (s0 s1 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (j : Nat) (own₀ : List (Loc × Val))
    (T S : Nat) (l : WeakMem.AllocLabel) (pT : Loc) (w1 w2 : TermRun.Word) (Ty : Ty) (r0' : Range)
    (X : State → Prop) (q : TcbGG) : Prop where
  clone : ClonePre pfxM (RuntimeLayout.ofPlaceW hp i).Λ r0' (r1Of (RuntimeLayout.ofPlaceW hp i).lab) X lbl d s
  hX : ∀ st, X st → st.exe = (RuntimeLayout.ofPlaceW hp i).exe ∧ st.endPc = endR hp i ∧ st.decls = {}
  hXq : ∀ st, X st → st.st.2 = cloneAt pfxM (RuntimeLayout.ofPlaceW hp i).exe ∧
    (st.st.1.regs.getXReg .X3).toBitVec = tcbOf (RuntimeLayout.ofPlaceW hp i).lab q
  hq : Q2 q
  hc : ∃ th0, s.ths = #[th0] ∧
    TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)])
  hw : w.1 = recW T S lbl lsize l pT w1
  pre : SpawnPre (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ (DR hp i) r0 r1 w d th stack s'
    s0 s1 lbl lsize ts j own₀
  hin : 0 < lsize l
  hS : 0 < S
  env1 : s1.env = [("a", Ty, [w1, w2])]
  hw1 : w1.val = .loc ⟨l, 0⟩ 0
  hw2 : w2.val = mainTidW
  stack0 : s0.stack = []
  σ0 : s0.σs = []
  term0 : MTerm s0.term
  env0 : EnvC (TermRun.cst (.loc ⟨l, 0⟩ 0)) s0.env
  prom0 : s0.promises = []
  tid0 : s0.tidLbl = some (mainTidLbl 2)
  hme : BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64 = (RuntimeLayout.ofPlaceW hp i).pinA + 24#64
  hlt : WakeSpawnLt.LtPre s s' l Ty
  /-- The spawned configuration is main's `spawn` at `spawnTerm` (`WakeSpawnLt.hlt0_of`'s run, with `hlt`). -/
  hsp : ∃ th0 ws, s.ths = #[th0] ∧
    s' = TermSpawnStep.spawnCfg s 0 th0 "t" WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws

/-- **The open premise of the pre-spawn segment's end**: at the
clone of thread `tid`, `tid = 0`, a source run to the spawned configuration
and `PreR`. -/
def HPre (asm : String) (E : Entry) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : Prop :=
  ∀ tid d s th stack tls r,
    SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E tid d s th stack tls r →
    tid = 0 ∧ ∃ s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q, (wakeS arch).Run s [] s' ∧
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q

/-- **The open premise of main's facts past the clone**: `main_closed_ws`'s
hypotheses, `MainWS`, at main's source thread's control `cP`. -/
def HMainR (asm : String) (E : Entry) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : Prop :=
  ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
    SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0 d s th stack tls r →
    (wakeS arch).Run s [] s' →
    PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
    ∃ (cP : Ctl) (R : Spike.Lib.Region) (F0 : MachineData → Prop) (A x29 ra tp : BitVec 64) (cw : TermRun.Word)
      (tyP : Ty) (γ : Type) (Rg : γ → Spike.Lib.Region) (Fg : γ → MachineData → Prop) (fp : γ → BitVec 64)
      (g0 : γ), Ctl.of s0 = cP ∧
      MainWS (RuntimeLayout.ofPlaceW hp i).exe (endR hp i) (RuntimeLayout.ofPlaceW hp i).Λ lbl lsize
        (wakeMs hp i w.1) d (r1Of (RuntimeLayout.ofPlaceW hp i).lab) r cP R F0 A x29 ra tp cw tyP Rg Fg fp g0

/-- **The open premise of the worker's view at the spawn**:
its store view and ordering bound below the source memory's size. -/
def HView (asm : String) (E : Entry) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : Prop :=
  ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
    SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E 0 d s th stack tls r →
    (wakeS arch).Run s [] s' →
    PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
    ((QG hp i arch R1 μ M r0 r1).C w).mviewS s1 < ((QG hp i arch R1 μ M r0 r1).SR w).S ∧
      ((QG hp i arch R1 μ M r0 r1).C w).obS s1 < ((QG hp i arch R1 μ M r0 r1).SR w).S

/-- **`HView` by `WakeSpawnLt.hview_R`** at `PreR.hlt`. -/
theorem hView {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} : HView hp i asm E arch R1 μ M r0 r1 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR =>
    WakeSpawnLt.hview_R hp i _ _ _ _ hR.hw (by rw [hR.pre.SR]) hR.pre.ths hR.env1 hR.hlt

/-- **The `spawn` hypothesis of `wake_obligations_R`** at `QG` (see the
module doc). -/
theorem spawn_R {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hMi : ∀ w, M.Mi w = mainInv w.1.lbl (wakeMs hp i w.1)
      (mainWR (RuntimeLayout.ofPlaceW hp i).lab (RuntimeLayout.ofPlaceW hp i).exe (RuntimeLayout.ofPlaceW hp i).Λ
        w.1.lbl w.1.lsize))
    (hMcw : ∀ w, M.cw w = w.1.cwM)
    /- instance facts -/
    (hprog : o.prog = wakeProg) (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    (hpass : ∀ w s c, (DR hp i).Wi w s c →
      (((QG hp i arch R1 μ M r0 r1).C w).passT s ↔ (c.term = WorkerSrc.wkUnpark ∨ c.term = .ret .unit)))
    /- OPEN: the pre-spawn segment's end -/
    (hpre : HPre hp i asm E arch R1 μ M r0 r1)
    /- OPEN: main's facts past the clone -/
    (hMainR : HMainR hp i asm E arch R1 μ M r0 r1) :
    ∀ tid d s th stack tls (r : BitVec 64), (QG hp i arch R1 μ M r0 r1).R1 d s →
      d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th → abi.atSys th.st = true →
      d.2.runs tid = true → d.2.exited = none → callOf abi th = some (.clone stack tls) → 0 < r.toNat →
      r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (QG hp i arch R1 μ M r0 r1).Post (RuntimeLayout.ofPlaceW hp i).Λ (afterClone abi d tid th stack tls r) s' := by
  intro tid d s th stack tls r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hP : SpawnPrem (QG hp i arch R1 μ M r0 r1) (RuntimeLayout.ofPlaceW hp i).Λ asm E tid d s th stack tls r :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨rfl, s', w, s0, s1, lbl, lsize, ts, j, own₀, T, S, l, pT, w1, w2, Ty, r0', X, q, hrun, hR⟩ :=
    hpre _ _ _ _ _ _ _ hP
  obtain ⟨cP, R, F0, A, x29, ra, tp, cw, tyP, γ, Rg, Fg, fp, g0, hcP, hM⟩ :=
    hMainR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  have hlt := hView hp i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  have hS := hR.pre
  haveI := (RuntimeLayout.ofPlaceW hp i).valid
  have hl : Scc.Cert.Rt.A64.Lays (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← hprog]; exact (RuntimeLayout.ofPlaceW hp i).lays
  -- the clone's thread, handed range and TCB are the field's
  have hcl := hR.clone
  obtain ⟨thc, -, tlsc, -, -, -, hthc, -, -, -, -, hcall, -, h3c, -, -, hheld, -, -, hO1, hXc, -⟩ := hcl
  have ethc : thc = th := by
    rw [hS.threads] at hthc; exact (List.singleton_inj.mp (congrArg Array.toList hthc)).symm
  subst thc
  have er1 : r1 w = r1Of (RuntimeLayout.ofPlaceW hp i).lab := by
    have := hS.held.symm.trans hheld
    simp only [List.cons.injEq, Prod.mk.injEq, true_and] at this
    exact this.1
  have estack : stack = (r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo + (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size := by
    rw [← hS.top, er1]
  subst estack
  have etls : tls = (tcbOf (RuntimeLayout.ofPlaceW hp i).lab q).toNat := by
    rw [h7] at hcall
    simp only [Option.some.injEq, Scc.Sem.Kernel.Call.clone.injEq] at hcall
    rw [hcall.2, ← h3c, ← (hR.hXq _ hXc).2]; rfl
  subst etls
  -- the record
  obtain ⟨g, hg⟩ := w
  have hgw : g = recW T S lbl lsize l pT w1 := hR.hw
  subst hgw
  -- the worker
  obtain ⟨th0, l', hs0, hc0, hk⟩ :=
    WakeSpawnWQ.spawn_workerPostQ hp i hl rfl hwide hprog hlo hpin2 hinit2 hR.hq hR.clone hR.hX hR.hXq
  have el : l' = l := by
    obtain ⟨th0', hs0', hc0'⟩ := hR.hc
    rw [hs0] at hs0'
    have e0 : th0 = th0' := List.singleton_inj.mp (congrArg Array.toList hs0')
    subst e0
    rw [hc0] at hc0'
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true, true_and] at hc0'
    have := congrArg Promises.TVal.val hc0'
    simp only [TermRun.cst, Promises.TVal.mk0] at this
    cases this; rfl
  subst el
  have hm := hS.inv1.mem
  have hh : handed d.2 0 ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo + (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size) =
      some (0, r1Of (RuntimeLayout.ofPlaceW hp i).lab) := by
    simp [handed, hheld]
  have hsub := hO1.1
  have hst : ∀ {a : BitVec 64}, (a = (RuntimeLayout.ofPlaceW hp i).pinA + 24#64 ∨
      a = (RuntimeLayout.ofPlaceW hp i).pinA + 128#64) → Spike.Lib.A64.Flow.Ret0.StOk (wakeMs hp i (recW T S lbl lsize l' pT w1))
        (DFrame (Worker.Wake.Child.childR ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo +
            (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size) (-16384))
          (childAfter abi d.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo +
            (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size)
            (tcbOf (RuntimeLayout.ofPlaceW hp i).lab q).toNat).st.st.1) (RuntimeLayout.ofPlaceW hp i).exe
        (endR hp i) a 1#64 :=
    fun ha => WakeChildSt.childSt_I hp i (recW T S lbl lsize l' pT w1) hm hpin2 ha hh hsub rfl
  have e128 : BitVec.ofNat 64 (tcbOf (RuntimeLayout.ofPlaceW hp i).lab q).toNat + 24#64 =
      (RuntimeLayout.ofPlaceW hp i).pinA + 128#64 := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, WakeTcbArea.tcbOf_q2 hp i hR.hq, BitVec.add_assoc]; rfl
  obtain ⟨hg', hW⟩ := hk s1 Ty w1 w2 hm hR.hin hR.hS hS.term1 hR.env1 hR.hw1 hR.hw2 (fun th' hth' => by
    have e : th' = th := by
      rw [hS.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
    subst e
    exact ⟨hst (.inl hR.hme), by rw [hR.hme]; exact WakeChildSt.childSt_al hp i, hst (.inr e128)⟩)
  have hW1 := hW th hS.threads
  -- main
  obtain ⟨th', hth', hmi⟩ := A64WakeMainClosedWS.main_closed_ws hl rfl hR.clone hM.hat hM.hRb hM.hRlo hM.hRhi hM.hR
    hM.htop h8 h9 hM.htP hM.hlP hM.hval hM.hloc hM.hin g0 hM.hRg hM.hfp hM.hFg hM.hF hM.hRo hM.hal hM.hlo
    hM.hhi hM.hdm rfl hM.hS hM.htp4 hM.htls hM.hra hM.hexit hM.hwide hM.hmA hM.hmP hM.hmE
  have e' : th' = th := by
    rw [hS.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
  subst th'
  have hPT0 : (QG hp i arch R1 μ M r0 r1).PT0 ⟨recW T S lbl lsize l' pT w1, hg⟩ d.1.mem s'.mem
      (retThread abi (parentPre abi d.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo +
        (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size)) r) s0 := by
    refine ⟨.inl ?_, hR.stack0, hR.σ0, hR.term0, ?_, hR.prom0, hR.tid0⟩
    · show M.Mi _ _ _
      rw [hMi, hcP]; exact hmi
    · show EnvC (M.cw _) _
      rw [hMcw]; exact hR.env0
  -- the protocol at the start
  have hpT : ¬ ((QG hp i arch R1 μ M r0 r1).C ⟨recW T S lbl lsize l' pT w1, hg⟩).passT
      (childAfter abi d.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hp i).lab).lo +
        (r1Of (RuntimeLayout.ofPlaceW hp i).lab).size) (tcbOf (RuntimeLayout.ofPlaceW hp i).lab q).toNat).st := by
    rw [hpass _ _ _ hW1]
    simp [Ctl.of, hS.term1, wkTail, WorkerSrc.wkUnpark]
  have hpS : ¬ ((QG hp i arch R1 μ M r0 r1).C ⟨recW T S lbl lsize l' pT w1, hg⟩).passS s1 := by
    show ¬ WorkerSrc.WPass s1
    simp [WorkerSrc.WPass, hS.term1, wkTail, WorkerSrc.wkUnpark]
  obtain ⟨k, hsl⟩ := hS.slots
  have hK : (QG hp i arch R1 μ M r0 r1).KR ⟨recW T S lbl lsize l' pT w1, hg⟩
      (afterClone abi d 0 th _ (tcbOf (RuntimeLayout.ofPlaceW hp i).lab q).toNat r) s' :=
    WakeKR.kr_start hsl hS.held hS.top hS.live hS.trace
  have hT : d.1.mem.last ≤ ((QG hp i arch R1 μ M r0 r1).SR ⟨recW T S lbl lsize l' pT w1, hg⟩).T := by
    rw [hS.SR]; exact Nat.le_refl _
  have hSz : s'.mem.size ≤ ((QG hp i arch R1 μ M r0 r1).SR ⟨recW T S lbl lsize l' pT w1, hg⟩).S := by
    rw [hS.SR]; exact Nat.le_refl _
  exact ⟨s', hrun, WakeStart.post_startW rfl rfl hS.SR hS.threads hS.ths hS.inv1 hS.prom hS.msgs hS.memIn
    hS.fits hS.memInv hS.bnd hS.own hS.sp0 hS.sp1 hS.scov0 hS.scov1
    (WakeInstFields.hfrz_I hp i _) (WakeInstFields.hfoot_I hp i _) hS.flag hS.flagLast hPT0 hW1 hS.st1 hS.σ1
    hS.term1 hS.env1 (HelloProt.helloProt_start hT hSz hpT hpS hlt) hK⟩

/-- info: 'Spike.Lib.WakeSpawnR.spawn_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_R

/-- **`WakeAssemblyR.wake_obligations_R` at any entry state `E`** whose stack
is clear of the placed layout (`hE`; same proof, `hstart` by
`WakeHStart.hstart_of_loadOk`; the marks do not depend on `E`). -/
theorem wake_obligations_RE {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs) (hE : E.clear (RuntimeLayout.ofPlaceW hp i).Λ = true)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ)
        tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ (WakeAssemblyR.QR hp i hpa arch R1 r0 r1).Post
        (RuntimeLayout.ofPlaceW hp i).Λ (afterClone abi d tid th stack tls r) s') :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm
      (WakeAssemblyR.QR hp i hpa arch R1 r0 r1) E (TiPre Ab Ac) := by
  have ho : o.prog = wakeProg := Except.ok.inj (hpa.symm.trans hwp)
  have hl : Scc.Cert.Rt.A64.Lays (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← ho]; exact (RuntimeLayout.ofPlaceW hp i).lays
  have hlo : Scc.Cert.Link.A64.loadOk (RuntimeLayout.ofPlaceW hp i).Λ wakeProg o.secs = true := by
    rw [← ho]; exact PlaceW.loadOk_link_of_placeW i hp
  have hμ := WorkerSide.wake_hμ (H := kernel 2) (E := Entry.linux) hwp hlo
  rw [← ho] at hμ
  have hC := WakeWorkerR.hC_IR hp i (GhOK (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).exe
    (endOf (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx)
    (RuntimeLayout.ofPlaceW hp i).pfx (arch := arch) (R1 := R1) (μ := WakeAssemblyR.μR hp i)
    (M := WakeAssemblyR.MR hp i hpa) (r0 := r0)
    (r1 := r1) (fun _ h => h) hl rfl hμ
  have hC0 := WakeAssemblyR.hC0R hp i hpa (arch := arch) (R1 := R1) (r0 := r0) (r1 := r1)
  -- the marks at `E` are `μR` (`marks_target`), not definitionally cheaply: abstract them
  have hm : (target (kernel 2) E).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ = WakeAssemblyR.μR hp i :=
    (Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa).trans
      (Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa).symm
  unfold WakeAssemblyR.QR WakeAssemblyR.MR at *
  generalize WakeAssemblyR.hoffR hp i hpa = hoff at hC hC0 spawn ⊢
  generalize WakeAssemblyR.μR hp i = μ at hoff hC hC0 spawn hm ⊢
  subst hm
  exact WakeWorkerR.wake_obligations_IWR hp i hoff hC (WakeWorkerR.hx_IR hp i _ _ _ _) hC0
    (WakeHStart.hstart_of_loadOk hpa hd (PlaceW.loadOk_link_of_placeW i hp) hE) O spawn rfl
    (WakeWorkerR.hW_IR hp i _ _ _ _) (fun _ => rfl) (WakeWorkerR.hmp_IR hp i _ _ _ _) (pcfg' := pcfg) (PlaceW.link i hp) hpa

/-- **`wake_obligations_RE` with `spawn_R`** at `QR` (`μ := μR`, `M := MR`)
and an entry state `E` clear of the layout (`hE`): `hMi`, `hMcw` by `rfl`,
`hprog` from the loader's two parses, `hpass` by `WakeWorkerR.hC_IR`'s
`pass`. -/
theorem wake_obligations_RS {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range}
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs) (hE : E.clear (RuntimeLayout.ofPlaceW hp i).Λ = true)
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm E R1 Ab Ac)
    /- instance facts -/
    (hlo : (RuntimeLayout.ofPlaceW hp i).Λ.code.lo = Spike.Lib.A64.WakePh.lo)
    (hpin2 : (RuntimeLayout.ofPlaceW hp i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hp i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hp i).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (RuntimeLayout.ofPlaceW hp i).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (RuntimeLayout.ofPlaceW hp i), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (RuntimeLayout.ofPlaceW hp i).exe)
    /- OPEN -/
    (hpre : HPre hp i SccCertificate.asm E arch R1 (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1)
    (hMainR : HMainR hp i SccCertificate.asm E arch R1 (WakeAssemblyR.μR hp i) (WakeAssemblyR.MR hp i hpa) r0 r1) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm
      (WakeAssemblyR.QR hp i hpa arch R1 r0 r1) E (TiPre Ab Ac) := by
  have ho : o.prog = wakeProg := Except.ok.inj (hpa.symm.trans hwp)
  haveI := (RuntimeLayout.ofPlaceW hp i).valid
  have hl : Scc.Cert.Rt.A64.Lays (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← ho]; exact (RuntimeLayout.ofPlaceW hp i).lays
  have hlk : Scc.Cert.Link.A64.loadOk (RuntimeLayout.ofPlaceW hp i).Λ wakeProg o.secs = true := by
    rw [← ho]; exact PlaceW.loadOk_link_of_placeW i hp
  have hμ := WorkerSide.wake_hμ (H := kernel 2) (E := Entry.linux) hwp hlk
  rw [← ho] at hμ
  exact wake_obligations_RE hp i hpa hwp hd hE O
    (spawn_R hp i (fun _ => rfl) (fun _ => rfl) ho hlo hpin2 hinit2 hwide
      (WakeWorkerR.hC_IR hp i _ _ _ _ (fun _ h => h) hl rfl hμ).pass hpre hMainR)

/-- info: 'Spike.Lib.WakeSpawnR.wake_obligations_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_RE

/-- info: 'Spike.Lib.WakeSpawnR.wake_obligations_RS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_RS

end Inst

end Spike.Lib.WakeSpawnR
