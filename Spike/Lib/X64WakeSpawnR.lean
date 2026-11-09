/-
**wake.w on x86-64: the spawn obligation at the instance** (in the manner
of `Spike/Lib/WakeSpawnR.lean`): `spawn_R`, the `spawn` hypothesis of
`X64WakeAssemblyR.wake_obligations_R`, at the relation `X64WakeWorkerR.QIR`
of the placed layout `L := RuntimeLayout.ofPlaceWX hp i` over the records
satisfying `X64WakeAssemblyR.GhOKR L` (`GhOK L.Λ` and `SelfOK`; TCB words `tcbM L`, `tcb2 L`, store point
`wakePassT`, any marks `μ`, main's side `M` with `wakeM`'s `Mi` and `cw`),
and `wake_obligations_RE`, `wake_obligations_RS` with it.

`spawn_R` follows `X64WakeSpawn.spawn_of` (`X64WakeOwnX.post_startOXW`,
`HelloProt.helloProt_start`, `X64WakeKR.kr_start`), the record `w` the
clone's `X64WakeOkW.recW`:

- the child in `Wi` by `X64WakeSpawnWQ.spawn_workerPostQ` (its stores
  discharged there by `X64WakeChildSt`; the handed range, the TCB and the
  thread from `ClonePre` against the premises of the `spawn` field);
- the worker's store view bound by `hView` (`SpawnViewLt.hview_of_spawnCfg`
  at `PreR.hlt`);
- main's `PT0` by `X64WakeMainClosedWS.main_closed_ws` (`hK` by `rfl`, `hms`
  by `X64WakeInst.rtOff_msXW`) into `X64WakeInst.mainInv`;
- `¬ passT` at the child by `WCompat.pass` (`hpass`) at `wkTail`,
  `¬ passS` by `wkTail`;
- `post_startOXW`'s owned-word facts: `hQ` by `X64WakeQ.hown`, `hTW` by
  `WakePh.tcb2_ne_tcbM`, `hcovT`/`hcovW` by `WakeP.wakeP_own_cov`; `hT0`,
  `hW0` by `X64WakeInst.handover_clone` (X64-own-handover) at `PreR.hown₀`;
  `hfrz`, `hfoot` by `X64WakeInstFields`
  (`hfoot`'s `SelfOK` from the records' `GhOKR`).

`selfOK_placed`/`ghOKR_of` give a record's `SelfOK`/`GhOKR` from the
memory relation placing its labels (X64-SelfOK, via
`X64WakeInst.selfOK_tcb`): `HPre`'s producer builds the clone's record with
them from `SpawnPre.inv1.mem` and `X64WakeWorkerR.ghOK_of_clone`.

**Open** (premises of `spawn_R`):

- `hpre : HPre` (the pre-spawn segment's end): at the clone of thread
  `tid`, `tid = 0`, a source run to the spawned configuration and `PreR`;
  among its fields `hcm` (`c`'s cell in the heap, main's id word `tcbM L`:
  the spawn's memory relation) and `hown₀` (`SpawnPre`'s own list at the clone
  is the runtime's `own₀ = ownGXW L a th.st`, the pre-spawn ownership
  invariant, as `X64WakeSpawnWQ` uses at `a := ntA L.lab`);
- `hMainR : HMainR`: `main_closed_ws`'s hypotheses past the clone,
  `MainWS`;
- instance facts: `hprog`, `hlo`, `hA13`, `hpin2`, `hinit2`, `hwide`, `hpass`
  (`X64WakeWorkerR.hC_IRX`'s `pass`).

The trust-boundary parses `hwp`, `hd`, `hoffs` of `wake_obligations_RE`/`RS`
are discharged at the final/root tier at the concrete certificate
(X64-trust-params); only `hpa` stays a premise of the final theorem.

**Unlike AArch64** (forced by the x64 shape):
- The records are `GhOKR` (`GhOK` with `SelfOK`), so no `hself` premise;
  a record's `SelfOK` is shown where it is built (`selfOK_placed`).
- The worker's view bound `HView` is proved here (`hView`, at `PreR.hlt`)
  rather than by an `hview_R` in `X64WakeSpawnLt`, which provides only
  `LtPre`, `hlt0_of`.
- `PreR` has `hcm` (for the child's segment) and `hown₀` (for
  `post_startOXW`'s `hT0`/`hW0`) in place of A64's `hme`; its clone has no
  prefix, its TCB register is `%r8`.
- `MainWS` follows the x64 `main_closed_ws`: one region `R` with frame `F`
  (no `Rg`/`Fg`/`g0`, no `htls`, no `hal`), main's TCB word loaded and owned
  (`hT`, `hown`), the limit (`hlim`) and `scc_rt_park`'s code (`hpcode`,
  `hpentry`).
- The certificate is a parameter `asm` (`X64WakeAssemblyR`).
-/
import Spike.Lib.X64WakeAssemblyR
import Spike.Lib.X64WakeSpawn
import Spike.Lib.X64WakeSpawnWQ
import Spike.Lib.X64WakeChildSt
import Spike.Lib.X64WakeMainClosedWS
import Spike.Lib.X64WakeSpawnLt
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeSelfOK
import Spike.Lib.X64WakeHandover
import Spike.Lib.X64WakeWcSegM

namespace Spike.Lib.X64WakeSpawnR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64WakeA64 Spike.Lib.X64WakeW1 Spike.Lib.X64WakeT1
open Spike.Lib.X64WakePreTi (Pre1T TiPre)
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64WakeInst (Gh wakeMs msM mainWR mainInv)
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64WakeOkW (recW)
open Spike.Lib.X64WakeSpawn (SpawnPrem SpawnPre)
open Spike.Lib.X64WakeTcbArea (Q2)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64.WakePh (tcbM tcb2)
open Spike.Lib.X64.WakePh.WcClone (oW)
open Spike.Lib.X64.WakePh.Parent (JS)
open Spike.Lib.X64.WakePh.MainPost (mainX2)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64WakeMainSrc (waitC)
open Spike.Lib.X64WakeM0 (mTail wlIf MTerm EnvC)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (endOf)

/-! ## main's facts past the clone -/

/-- **`main_closed_ws`'s hypotheses past the clone** (all but the listing's
`hp`/`hend`, the clone `h`, the child's id bounds `hr0`/`hrm`, `hK` and
`hms`), at main's control `cP`, the clone's configuration `t`, the handed
range `r1` and the child's id `r`. -/
structure MainWS (exe : _root_.Executable) (endPc : Int64) (Λ' : Scc.Sem.Layout)
    (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (ms : MemSide isa)
    (t : Cfg) (r1 : Range) (r : BitVec 64) (cP : Ctl) (R : Region) (F0 F : MachineData → Prop)
    (A fp ra tp : BitVec 64) (w : TermRun.Word) (tyP : Ty) : Prop where
  hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP
  hRb : ∀ th : Thread isa, t.1.threads = #[th] →
    (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64
  hRlo : R.lo = -80
  hRhi : R.hi = 40
  hR : R.OK
  htop : r1.lo + r1.size ≤ 2 ^ 64
  htP : cP.term = mTail
  hlP : TermRun.lookupE cP.env "c" = some (tyP, [w])
  hval : ValRep lbl w.val A.toNat
  hloc : LocRep lbl w.val A.toNat 0
  hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label
  hFR : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
    DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m
  hF : FStable R F
  hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec)
  hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none
  hT : LdOk ms F tp
  hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp
  hS : StOk ms F (tp + 16#64) 0#64
  htp4 : (tp + 16#64).toNat % 4 = 0
  hpcode : ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64), Park.Code c0' rbp0' ra' tp' exe endPc
  hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
    (_root_.Executable.labels exe).label "scc_rt_park" + 8
  hfp : fp = R.addr 48
  hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2
  hexit : ∀ s c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
    At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
      fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s →
      MainExit Spike.Lib.X64WakeT1.wakeSrc ms s c 0
  hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s
  hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ') wr ⟨A, 8⟩ = true
  hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') cP
  hmE : ∀ c, Past (waitC w) "d" wlIf (.ptr .pub .int) (RdOne (ms := ms) lbl) c →
    Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') c

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`SelfOK` of a record placed by the memory relation** (X64-SelfOK,
via `X64WakeInst.selfOK_tcb`): the TCB words `tcbM L = pinA + 8`,
`tcb2 L = pinA + 136` lie in `pinned` (`hpin2`), off every label the memory
relation places (in `.data` or the heap, disjoint from `pinned`), and the
flag's word lies in its label (`X64WakeInst.inLabel_cT`).

**Unlike AArch64**: no counterpart (A64's records need no `SelfOK`). -/
theorem selfOK_placed (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {g : Gh}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hg : GhOK (Ly).Λ g) :
    Spike.Lib.X64WakeInst.SelfOK (tcbM (Ly)) (tcb2 (Ly)) g := by
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hp i
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  have hH := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.heap ∈ (Ly).Λ.regions)
  have hD := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.data ∈ (Ly).Λ.regions)
  have h0 := PlaceWX.pinA_toNat_ofPlaceWX hp i
  have hsm := X64WakeChildSt.pinA_small hp i
  have eT : (tcbM (Ly)).toNat = (Ly).pinA.toNat + 8 := X64WakeChildSt.pinA_add hp i (c := 8) (by decide)
  have eW : (tcb2 (Ly)).toNat = (Ly).pinA.toNat + 136 := X64WakeChildSt.pinA_add hp i (c := 136) (by decide)
  simp only [Range.Disjoint, Range.InSpace] at hdp hhp hH hD
  have hoff : ∀ a : BitVec 64, a.toNat = (Ly).pinA.toNat + 8 ∨ a.toNat = (Ly).pinA.toNat + 136 →
      (Spike.Lib.X64WakeInst.wakeMs hp i g).rt a.toNat := by
    rintro a ha ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
    simp only [Range.contains] at hs
    omega
  refine Spike.Lib.X64WakeInst.selfOK_tcb hp i (hoff _ (.inl eT)) (hoff _ (.inr eW))
    (Spike.Lib.X64WakeInst.inLabel_cT hm (fun x hx => ?_) hg)
  simp only [Range.contains] at hx
  omega

/-- **A record of the layout from the memory relation**: `GhOK` and
`selfOK_placed`. -/
theorem ghOKR_of (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) {g : Gh}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp) (hg : GhOK (Ly).Λ g) :
    X64WakeAssemblyR.GhOKR (Ly) g :=
  ⟨hg, selfOK_placed hp i hpin2 hm hg⟩

/-- The records. -/
abbrev ιR := {g : Gh // X64WakeAssemblyR.GhOKR (Ly) g}

/-- The worker's side at the layout. -/
noncomputable abbrev DR : WSide (ιR hp i) :=
  X64WakeWorkerR.wakeDR hp i (tcbM (Ly)) (tcb2 (Ly)) (X64WakeAssemblyR.GhOKR (Ly)) (Ly).exe (X64WakeAssemblyR.endR hp i)
    (Ly).pfx

/-- The relation at the layout (`X64WakeAssemblyR.QR` at `μ`, `M`). -/
noncomputable abbrev QG (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : X64WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : WakeRel :=
  X64WakeWorkerR.QIR hp i (tcbM (Ly)) (tcb2 (Ly)) (X64WakeAssemblyR.GhOKR (Ly)) (Ly).exe (X64WakeAssemblyR.endR hp i)
    (Ly).pfx arch R1 μ M r0 r1 Spike.Lib.X64.Flow.Worker.Wake.Pass.wakePassT

/-- **The pre side's facts at main's clone** (the segment's end): the
clone `ClonePre` at `X` (the clone's `syscall` with `%r8` the TCB of a `Q2`
request `q`), `c`'s label `l`, the record `w` the clone's `recW` with
`SpawnPre` at it, the spawned worker's argument words `w1`, `w2`, main's
source thread `s0`'s `PT0` facts, `c`'s cell in the heap and main's id word
`tcbM L` (`hcm`), and main's own list the runtime's `ownGXW` (`hown₀`). -/
structure PreR (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks) (M : X64WakeM0.MSide (ιR hp i))
    (r0 r1 : ιR hp i → Range) (d : Cfg) (th : Thread isa) (stack : Nat) (s s' : TermRun.Cfg)
    (w : ιR hp i) (s0 s1 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (j : Nat) (own₀ : List (Loc × Val))
    (T S : Nat) (l : WeakMem.AllocLabel) (pT : Loc) (w1 w2 : TermRun.Word) (Ty : Ty) (r0' : Range)
    (X : State → Prop) (q : TcbGG) : Prop where
  clone : ClonePre (Ly).Λ r0' (r1Of (Ly).lab) X lbl d s
  hX : ∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = X64WakeAssemblyR.endR hp i ∧ st.decls = {}
  hXq : ∀ st, X st → st.st.2 = cloneAt (Ly).exe ∧ st.st.1.regs.get64 .r8 = tcbOf (Ly).lab q
  hq : Q2 q
  hc : ∃ th0, s.ths = #[th0] ∧
    TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)])
  hw : w.1 = recW T S lbl lsize l pT w1
  pre : SpawnPre (QG hp i arch R1 μ M r0 r1) (Ly).Λ (DR hp i) r0 r1 w d th stack s' s0 s1 lbl lsize ts j own₀
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
  /-- `c`'s cell in the heap, main's id word main's TCB (the spawn's memory relation). -/
  hcm : (Ly).Λ.heap.contains (th.st.st.1.regs.get64 .r12).toNat ∧
    BitVec.ofNat 64 (th.st.st.1.regs.get64 .rbx).toNat = tcbM (Ly)
  /-- main's own list at the clone is the runtime's `ownGXW` (the spawn's
  ownership invariant; both TCB words by `X64WakeInst.handover_clone`). -/
  hown₀ : ∃ a, own₀ = Spike.Lib.X64.WakePh.ownGXW (Ly) a th.st
  hlt : X64WakeSpawnLt.LtPre s s' l Ty
  /-- The spawned configuration is main's `spawn` at `spawnTerm` (`X64WakeSpawnLt.hlt0_of`'s run). -/
  hsp : ∃ th0 ws, s.ths = #[th0] ∧
    s' = TermSpawnStep.spawnCfg s 0 th0 "t" X64WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws

/-- **The open premise of the pre-spawn segment's end**: at the clone of
thread `tid`, `tid = 0`, a source run to the spawned configuration and
`PreR`. -/
def HPre (asm : Asm) (E : Entry) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : X64WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : Prop :=
  ∀ tid d s th stack tls r,
    SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E tid d s th stack tls r →
    tid = 0 ∧ ∃ s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q, (wakeS arch).Run s [] s' ∧
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q

/-- **The open premise of main's facts past the clone**: `main_closed_ws`'s
hypotheses, `MainWS`, at main's source thread's control `cP`. -/
def HMainR (asm : Asm) (E : Entry) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : X64WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : Prop :=
  ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
    SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
    (wakeS arch).Run s [] s' →
    PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
    ∃ (cP : Ctl) (R : Region) (F0 F : MachineData → Prop) (A fp ra tp : BitVec 64) (cw : TermRun.Word)
      (tyP : Ty), Ctl.of s0 = cP ∧
      MainWS (Ly).exe (X64WakeAssemblyR.endR hp i) (Ly).Λ lbl lsize (msM hp i (tcbM (Ly)) (tcb2 (Ly)) w.1) d
        (r1Of (Ly).lab) r cP R F0 F A fp ra tp cw tyP

/-- **The open premise of the worker's view at the spawn**: its store view
and ordering bound below the source memory's size. -/
def HView (asm : Asm) (E : Entry) (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : X64WakeM0.MSide (ιR hp i)) (r0 r1 : ιR hp i → Range) : Prop :=
  ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
    SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
    (wakeS arch).Run s [] s' →
    PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
    ((QG hp i arch R1 μ M r0 r1).C w).mviewS s1 < ((QG hp i arch R1 μ M r0 r1).SR w).S ∧
      ((QG hp i arch R1 μ M r0 r1).C w).obS s1 < ((QG hp i arch R1 μ M r0 r1).SR w).S

/-- **`HView` at main's spawn** (A64's `WakeSpawnLt.hview_R` folded into
its use at `PreR.hlt`): `SpawnViewLt.hview_of_spawnCfg` at the spawned
configuration, the record's source size `s'.mem.size` (`SpawnPre.SR`),
`s'`'s threads (`SpawnPre.ths`) and the worker's environment (`PreR.env1`);
`QG`'s `mviewS s1`, `obS s1` are `helloC`'s at the worker's word `cwW = w1`
and `cS = ⟨l, 0⟩` (`PreR.hw`).

**Unlike AArch64**: stated and proved at `QG` here rather than as a
separate `hview_R` at `X64WakeWorkerR.QIR` in `X64WakeSpawnLt` (which does
not import the worker's relation). -/
theorem hView {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} : HView hp i asm E arch R1 μ M r0 r1 := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q _ _ hR
  obtain ⟨th0, x, e, f, tys, ws, hs0, rfl, hv, hws⟩ := hR.hlt
  rw [hR.pre.SR]
  have hs1 : (TermSpawnStep.spawnCfg s 0 th0 x e f tys ty1 ws).ths[s.ths.size]? = some s1 := by
    rw [hR.pre.ths, hs0]; rfl
  have h := SpawnViewLt.hview_of_spawnCfg hv hws hs1 hR.env1 Promises.Knobs.all arch
  have hcw : w.1.cwW = w1 := by rw [hR.hw]; rfl
  have hcS : w.1.cS = ⟨l, 0⟩ := by rw [hR.hw]; rfl
  have hcw' : (DR hp i).cw w = w1 := hcw
  simp only [QG, X64WakeWorkerR.QIR, X64WakeInst.wakeQI, X64WakeQ.wakeQ, WorkerSrc.helloC, hcw', hcS]
  exact h

/-- **The `spawn` hypothesis of `wake_obligations_R`** at `QG` (see the
module doc). -/
theorem spawn_R {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hMi : ∀ w, M.Mi w = mainInv w.1.lbl (msM hp i (tcbM (Ly)) (tcb2 (Ly)) w.1)
      (mainWR (Ly).lab (Ly).exe (Ly).Λ w.1.lbl w.1.lsize))
    (hMcw : ∀ w, M.cw w = w.1.cwM)
    /- instance facts -/
    (hprog : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideX64.ExeWide (Ly).exe)
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
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm (Ly).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (QG hp i arch R1 μ M r0 r1).Post (Ly).Λ (afterClone abi d tid th stack tls r) s' := by
  intro tid d s th stack tls r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hP : SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E tid d s th stack tls r :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨rfl, s', w, s0, s1, lbl, lsize, ts, j, own₀, T, S, l, pT, w1, w2, Ty, r0', X, q, hrun, hR⟩ :=
    hpre _ _ _ _ _ _ _ hP
  obtain ⟨cP, R, F0, F, A, fp, ra, tp, cw, tyP, hcP, hM⟩ :=
    hMainR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  have hlt := hView hp i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  have hS := hR.pre
  haveI := (Ly).valid
  have hl : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := by
    rw [← hprog]; exact (Ly).lays
  -- the clone's thread, handed range and TCB are the field's
  have hcl := hR.clone
  obtain ⟨thc, -, tlsc, -, -, -, hthc, -, -, -, -, hcall, -, h8c, -, -, hheld, -, -, hO1, hXc, -⟩ := hcl
  have ethc : thc = th := by
    rw [hS.threads] at hthc; exact (List.singleton_inj.mp (congrArg Array.toList hthc)).symm
  subst thc
  have er1 : r1 w = r1Of (Ly).lab := by
    have := hS.held.symm.trans hheld
    simp only [List.cons.injEq, Prod.mk.injEq, true_and] at this
    exact this.1
  have estack : stack = (r1Of (Ly).lab).lo + (r1Of (Ly).lab).size := by
    rw [← hS.top, er1]
  subst estack
  have etls : tls = (tcbOf (Ly).lab q).toNat := by
    rw [h7] at hcall
    simp only [Option.some.injEq, Scc.Sem.Kernel.Call.clone.injEq] at hcall
    rw [hcall.2, ← h8c, (hR.hXq _ hXc).2]
  subst etls
  -- the record
  obtain ⟨g, hg⟩ := w
  have hgw : g = recW T S lbl lsize l pT w1 := hR.hw
  subst hgw
  -- the worker
  obtain ⟨th0, l', hs0, hc0, hk⟩ :=
    X64WakeSpawnWQ.spawn_workerPostQ hp i hA13 hl rfl hwide hprog hlo hpin2 hinit2 hR.hq hR.clone hR.hX hR.hXq
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
  obtain ⟨hg', hW⟩ := hk s1 Ty w1 w2 hm hR.hin hR.hS hS.term1 hR.env1 hR.hw1 hR.hw2 (fun th' hth' => by
    have e : th' = th := by
      rw [hS.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
    subst e
    exact hR.hcm)
  -- `wakeDR`'s `Wi` reads the record only (`GhOK` / `GhOKR` alike)
  have hW1 : (DR hp i).Wi ⟨recW T S lbl lsize l' pT w1, hg⟩
      (childAfter abi d.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat).st
      (Ctl.of s1) := hW th hS.threads
  -- main
  obtain ⟨c0', rbp0', ra', tp', hpc⟩ := hM.hpcode
  obtain ⟨th', hth', inv, hcl, hiW, hinv⟩ := X64WakeMainClosedWS.main_closed_ws hl rfl hR.clone hM.hat hM.hRb
    hM.hRlo hM.hRhi hM.hR hM.htop h8 h9 hM.htP hM.hlP hM.hval hM.hloc hM.hin hM.hFR hM.hF hM.hlim hM.hdm rfl
    hM.hT hM.hown hM.hS hM.htp4 hpc hM.hpentry hM.hfp hM.hra hM.hexit hM.hwide hM.hmA hM.hmP hM.hmE
    (X64WakeInst.rtOff_msXW hp i (tcbM (Ly)) (tcb2 (Ly)) (recW T S lbl lsize l' pT w1) (tcbM (Ly)))
  have e' : th' = th := by
    rw [hS.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
  subst th'
  have hPT0 : (QG hp i arch R1 μ M r0 r1).PT0 ⟨recW T S lbl lsize l' pT w1, hg⟩ d.1.mem s'.mem
      (retThread abi (parentPre abi d.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)) r) s0 := by
    refine ⟨.inl ?_, hR.stack0, hR.σ0, hR.term0, ?_, hR.prom0, hR.tid0⟩
    · show M.Mi _ _ _
      rw [hMi, hcP]; exact X64WakeInst.mainInv_of hiW hcl hinv
    · show EnvC (M.cw _) _
      rw [hMcw]; exact hR.env0
  -- the protocol at the start
  have hpT : ¬ ((QG hp i arch R1 μ M r0 r1).C ⟨recW T S lbl lsize l' pT w1, hg⟩).passT
      (childAfter abi d.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat).st := by
    rw [hpass _ _ _ hW1]
    simp [Ctl.of, hS.term1, wkTail, WorkerSrc.wkUnpark]
  have hpS : ¬ ((QG hp i arch R1 μ M r0 r1).C ⟨recW T S lbl lsize l' pT w1, hg⟩).passS s1 := by
    show ¬ WorkerSrc.WPass s1
    simp [WorkerSrc.WPass, hS.term1, wkTail, WorkerSrc.wkUnpark]
  obtain ⟨k, hsl⟩ := hS.slots
  have hK : (QG hp i arch R1 μ M r0 r1).KR ⟨recW T S lbl lsize l' pT w1, hg⟩
      (afterClone abi d 0 th _ (tcbOf (Ly).lab q).toNat r) s' :=
    X64WakeKR.kr_start hsl hS.held hS.top hS.live hS.trace
  have hT : d.1.mem.last ≤ ((QG hp i arch R1 μ M r0 r1).SR ⟨recW T S lbl lsize l' pT w1, hg⟩).T := by
    rw [hS.SR]; exact Nat.le_refl _
  have hSz : s'.mem.size ≤ ((QG hp i arch R1 μ M r0 r1).SR ⟨recW T S lbl lsize l' pT w1, hg⟩).S := by
    rw [hS.SR]; exact Nat.le_refl _
  have hTW : (⟨tcbM (Ly), 8⟩ : Loc) ≠ ⟨tcb2 (Ly), 8⟩ := fun h =>
    Spike.Lib.X64.WakePh.tcb2_ne_tcbM (Ly) (congrArg Loc.addr h).symm
  -- main's own list at the clone holds both TCB words (X64-own-handover)
  have hho : ((⟨tcbM (Ly), 8⟩ : Loc), (tcbM (Ly)).setWidth 128) ∈ own₀ ∧
      ((⟨tcb2 (Ly), 8⟩ : Loc), (tcb2 (Ly)).setWidth 128) ∈ own₀ := by
    obtain ⟨a, rfl⟩ := hR.hown₀
    obtain ⟨th', hth', hh⟩ := X64WakeInst.handover_clone hp i hlo hprog hR.clone fun st h => (hR.hX st h).1
    have e : th' = th := by
      rw [hS.threads] at hth'; exact (List.singleton_inj.mp (congrArg Array.toList hth')).symm
    subst e
    exact hh a
  exact ⟨s', hrun, X64WakeOwnX.post_startOXW X64WakeQ.hown hTW hS.SR hS.threads hS.ths hS.inv1 hS.prom
    hS.msgs hS.memIn hS.fits hS.memInv hS.bnd hS.own hho.1 hho.2
    (WakeP.wakeP_own_cov (.inl ⟨rfl, rfl⟩)) (WakeP.wakeP_own_cov (.inr ⟨rfl, rfl⟩))
    hS.sp0 hS.sp1 hS.scov0 hS.scov1
    (X64WakeInstFields.hfrz_I hp i _ _ _) (X64WakeInstFields.hfoot_I hp i _ _ (fun w => w.2.2) _)
    hS.flag hS.flagLast hPT0
    (X64WakeStart.pt1_start _ _ d.1.mem s'.mem hW1 hS.st1 hS.σ1 hS.term1 hS.env1 hS.sp1 childAfter_prom)
    (HelloProt.helloProt_start hT hSz hpT hpS hlt) hK⟩

/-- info: 'Spike.Lib.X64WakeSpawnR.selfOK_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selfOK_placed

/-- info: 'Spike.Lib.X64WakeSpawnR.ghOKR_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ghOKR_of

/-- info: 'Spike.Lib.X64WakeSpawnR.hView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hView

/-- info: 'Spike.Lib.X64WakeSpawnR.spawn_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spawn_R

/-- **`X64WakeAssemblyR.wake_obligations_R` at any entry state `E`** whose
stack is clear of the placed layout (`hE`; same proof, `hstart` by
`X64WakeHStart.hstart_ofPlaceOKAt`; the marks do not depend on `E`). -/
theorem wake_obligations_RE {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range} {asm : Asm}
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    (hE : E.clear (Ly).Λ = true)
    (O : Pre1T arch (Ly).Λ B asm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm (Ly).Λ)
        tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ (X64WakeAssemblyR.QR hp i asm hpa arch R1 r0 r1).Post
        (Ly).Λ (afterClone abi d tid th stack tls r) s') :
    WakeObligations arch (Ly).Λ B asm (X64WakeAssemblyR.QR hp i asm hpa arch R1 r0 r1) E (TiPre Ab Ac) := by
  have ho : o.prog = wakeCells := Option.some.inj (hpa.symm.trans hwp)
  have hl : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := by
    rw [← ho]; exact (Ly).lays
  have hTW : (⟨tcbM (Ly), 8⟩ : Loc) ≠ ⟨tcb2 (Ly), 8⟩ := fun h =>
    Spike.Lib.X64.WakePh.tcb2_ne_tcbM (Ly) (congrArg Loc.addr h).symm
  have hC := X64WakeWorkerR.hC_IRX hp i (tcbM (Ly)) (tcb2 (Ly)) (X64WakeAssemblyR.GhOKR (Ly))
    (X64WakeAssemblyR.endR hp i) (Ly).pfx (arch := arch) (R1 := R1) (μ := X64WakeAssemblyR.μR hp i asm)
    (M := X64WakeAssemblyR.MR hp i asm hpa) (r0 := r0) (r1 := r1) (fun _ h => h.1) (fun w => w.2.2) hTW hl rfl
    (X64WakeAssemblyR.μR_eq hp i asm hpa)
  have hC0 := X64WakeAssemblyR.hC0R hp i asm hpa (arch := arch) (R1 := R1) (r0 := r0) (r1 := r1)
  -- the marks at `E` are `μR` (`marks_target`): abstract them
  have hm : (target (kernel 2) E).marks asm (Ly).Λ = X64WakeAssemblyR.μR hp i asm :=
    (Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa).trans
      (Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa).symm
  unfold X64WakeAssemblyR.QR X64WakeAssemblyR.MR at *
  generalize X64WakeAssemblyR.hoffR hp i asm hpa = hoff at hC hC0 spawn ⊢
  generalize X64WakeAssemblyR.μR hp i asm = μ at hoff hC hC0 spawn hm ⊢
  subst hm
  exact X64WakeWorkerR.wake_obligations_IWR hp i hoff hC (X64WakeWorkerR.hx_IR hp i _ _ _ _ _ _) hC0
    (X64WakeHStart.hstart_ofPlaceOKAt (PlaceWX.link i hp) hpa hd hoffs hE) O spawn rfl
    (X64WakeWorkerR.hW_IR hp i _ _ _ _ _ _) (fun _ => rfl) (X64WakeWorkerR.hmp_IR hp i _ _ _ _ _ _)
    (pcfg' := pcfg) (PlaceWX.link i hp) hpa

/-- **`wake_obligations_RE` with `spawn_R`** at `QR` (`μ := μR`, `M := MR`)
and an entry state `E` clear of the layout (`hE`): `hMi`, `hMcw` by `rfl`,
`hprog` from the loader's two parses, `hpass` by `X64WakeWorkerR.hC_IRX`'s
`pass`. -/
theorem wake_obligations_RS {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : ιR hp i → Range} {asm : Asm}
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    (hE : E.clear (Ly).Λ = true)
    (O : Pre1T arch (Ly).Λ B asm E R1 Ab Ac)
    /- instance facts -/
    (hlo : (Ly).Λ.code.lo = Spike.Lib.X64.WakePh.lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideX64.ExeWide (Ly).exe)
    /- OPEN -/
    (hpre : HPre hp i asm E arch R1 (X64WakeAssemblyR.μR hp i asm) (X64WakeAssemblyR.MR hp i asm hpa) r0 r1)
    (hMainR : HMainR hp i asm E arch R1 (X64WakeAssemblyR.μR hp i asm) (X64WakeAssemblyR.MR hp i asm hpa) r0 r1) :
    WakeObligations arch (Ly).Λ B asm (X64WakeAssemblyR.QR hp i asm hpa arch R1 r0 r1) E (TiPre Ab Ac) := by
  have ho : o.prog = wakeCells := Option.some.inj (hpa.symm.trans hwp)
  have hl : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := by
    rw [← ho]; exact (Ly).lays
  have hTW : (⟨tcbM (Ly), 8⟩ : Loc) ≠ ⟨tcb2 (Ly), 8⟩ := fun h =>
    Spike.Lib.X64.WakePh.tcb2_ne_tcbM (Ly) (congrArg Loc.addr h).symm
  exact wake_obligations_RE hp i hpa hwp hd hoffs hE O
    (spawn_R hp i (fun _ => rfl) (fun _ => rfl) ho hlo hA13 hpin2 hinit2 hwide
      (X64WakeWorkerR.hC_IRX hp i _ _ _ _ _ (fun _ h => h.1) (fun w => w.2.2) hTW hl rfl
        (X64WakeAssemblyR.μR_eq hp i asm hpa)).pass hpre hMainR)

/-- info: 'Spike.Lib.X64WakeSpawnR.wake_obligations_RE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_RE

/-- info: 'Spike.Lib.X64WakeSpawnR.wake_obligations_RS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_RS

/-- **main's segment end at every `PreR`** (A64's
`A64WakeWcSeg.hpc_of`): `X64.Flow.WakeWc.mainSeg_of` at `PreR`'s `clone`,
`hc` and `pre.threads`, given main's `ClonePost` at the clone (`hpost`).

**Unlike AArch64**: stated here, beside `PreR` (A64 in `A64WakeWcSeg`); the
frame is `⟨Rm.base, -64, 16⟩` and the guard bound holds at every offset. -/
theorem hpc_of {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range}
    (hpost : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c J t, Spike.Lib.X64.Flow.WakeWc.ClonePost (Ly) (X64WakeAssemblyR.endR hp i) J t th.st c) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c Rm F₂ cA fp ra tp, X64WakeMainHRD.MainSeg (Ly) (X64WakeAssemblyR.endR hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧
        ∀ k, -64 ≤ k → k < 16 → (Ly).stacksA.toNat + 4096 ≤ ((⟨Rm.base, -64, 16⟩ : Region).addr k).toNat := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q hP hrun hR
  obtain ⟨c, J, t, h⟩ := hpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP hrun hR
  obtain ⟨th0, hs, hc⟩ := hR.hc
  exact ⟨c, Spike.Lib.X64.Flow.WakeWc.mainSeg_of h hR.clone hs hc hR.pre.threads⟩

/-- info: 'Spike.Lib.X64WakeSpawnR.hpc_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpc_of

end Inst

end Spike.Lib.X64WakeSpawnR
