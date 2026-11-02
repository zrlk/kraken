/-
**wake.w's worker side per record on x86-64** (in the manner of
`Spike/Lib/WakeWorkerR.lean`): the worker's side with each record's states
inside `wakeZX` at that record's own spawn placement `w.1.lbl` and flag
`w.1.cS` (not one `lbl'`/`cSf` for the family), so the assembly needs
neither `hlbl` nor `hcS`.

- `ZR`, `wkPR`, `wkPR_of`, `wkPR_seg`: the record's `wakeZX` (with the
  worker's TCB word `W`), the union of the preconditions of the segments
  keeping it (the child's entry by `X64WakeChildXI.childSeg_XI` at
  `lbl' := w.1.lbl`, `cSf := w.1.cS`), its segment.
- `wakeDR`: the worker's side (`WorkerSide.wi_exists` per record, memory
  side `msW hp i T W w.1`); `wakeDR_entry`, `wakeDR_inv`; `hW_IR`,
  `hmp_IR`.
- `QIR`: `X64WakeInst.wakeQI` at `D := wakeDR`.
- `hx_IR`, `hC_IR_of`/`hC_IR`/`hC_IRX`: `WCompatX`, `WCompat` at `ok`
  records satisfying `X64WakeInstFields.GhOK` (`hok`); `noSite` a premise
  of `hC_IR_of`, from the marks' sites `hμ` in `hC_IR` (open), from the
  runtime's marks `PhRec.μ L` at `L.exe` in `hC_IRX` (closed).
- `ghOK_of_clone`: `X64WakeOkW.recW` satisfies `GhOK` (open: `hin`, `hS`).
- `wake_obligations_IWR`: `X64WakeAssemblyI.wake_obligations_I` with the
  worker's facts from a per-record `hW` (`wakeZX` at `(SR w).lbl`, `cS w`)
  and `post_wit` by `X64WakePostWit.post_wit_of`.

**Unlike AArch64** (forced by the x64 shape):
- The worker's memory side is `msW hp i T W g` (owning its TCB self word,
  its runtime writes off both self words), not `wakeMs hp i g`, and
  `wakeZX` carries `W`; `QIR` takes the store point `passT` and `T W`.
- `hC_IR` is at the store point `wakePassT` (`QIR` takes it) and carries
  `hself` (`SelfOK`, for `footLab`) and `hTW` (the two self words differ;
  at the instance `tcbM L ≠ tcb2 L`); A64 has no self words.
- `ownInstr` is `OwnInstrW.ownInstr_of` from `wakeZX`'s `OwnW W` per
  record (the worker never writes its self word), `hcovW` is
  `WakeP.wakeP_own_cov`; A64's owned words are none.
-/
import Spike.Lib.X64WakeAssemblyI
import Spike.Lib.X64WakeWorkerX
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeInstFields
import Spike.Lib.X64WakeOkW
import Spike.Lib.X64WakeAssembly

namespace Spike.Lib.X64WakeWorkerR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakeW1 Spike.Lib.WakeP Spike.Lib.X64WakePreTi
open Spike.Lib.Handover Spike.Lib.Inv2Core
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeInst (Gh msW wakeSR wakeG' wakeLocs wakeM wakeQI placed_I)
open Spike.Lib.X64.Flow.Worker (NNZ)
open Spike.Lib.X64.Flow.Worker.Wake.ZX (wakeZX)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.WideKeep (WideX)

/-! ## The worker's side per record -/

section Side

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)
  (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat)

/-- **The record's `wakeZX`**: at the instance's layout, the record's spawn
placement and flag, the worker's TCB word `W`. -/
abbrev ZR (w : {g : Gh // ok g}) : Frag isa :=
  wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ w.1.lbl w.1.cS W exe kp

/-- **The worker's pairs**: those of the precondition of some segment
keeping the record's `wakeZX`. -/
def wkPR (w : {g : Gh // ok g}) : Frag isa := fun s c =>
  ∃ Pj : Frag isa, SegTC (NNZ exe endPc (ZR hp i W ok exe kp w)) wakeSrc w.1.lbl (msW hp i T W w.1) Pj
    (fun _ _ => False) ∧ Pj s c

/-- **A segment's precondition's pairs are the worker's.** -/
theorem wkPR_of {w : {g : Gh // ok g}} {Pj : Frag isa}
    (h : SegTC (NNZ exe endPc (ZR hp i W ok exe kp w)) wakeSrc w.1.lbl (msW hp i T W w.1) Pj
      (fun _ _ => False))
    {s : State} {c : Ctl} (hP : Pj s c) : wkPR hp i T W ok exe endPc kp w s c :=
  ⟨Pj, h, hP⟩

/-- `wkPR`'s segment. -/
theorem wkPR_seg (w : {g : Gh // ok g}) :
    SegTC (NNZ exe endPc (ZR hp i W ok exe kp w)) wakeSrc w.1.lbl (msW hp i T W w.1)
      (wkPR hp i T W ok exe endPc kp w) (fun _ _ => False) :=
  (X64WakeWorkerX.segTC_iUnion (κ := {Pj : Frag isa // SegTC (NNZ exe endPc (ZR hp i W ok exe kp w)) wakeSrc
      w.1.lbl (msW hp i T W w.1) Pj (fun _ _ => False)}) fun j => j.2).mono_pre
    fun _ _ ⟨Pj, h, hP⟩ => ⟨⟨Pj, h⟩, hP⟩

/-- **The worker's side per record**: `WorkerSide.side`'s construction with
each record's own `wakeZX`. -/
noncomputable def wakeDR : WSide {g : Gh // ok g} where
  lbl w := w.1.lbl
  ms w := msW hp i T W w.1
  Wi w := Classical.choose
    (WorkerSide.wi_exists (X64WakeWorkerX.msW_K hp i T W w.1) (wkPR_seg hp i T W ok exe endPc kp w))
  closed w := (Classical.choose_spec
    (WorkerSide.wi_exists (X64WakeWorkerX.msW_K hp i T W w.1) (wkPR_seg hp i T W ok exe endPc kp w))).2.2
  cw w := w.1.cwW
  S w := w.1.S

/-- `wakeDR`'s invariant holds the segments' entries in `WideX exe`. -/
theorem wakeDR_entry (w : {g : Gh // ok g}) (s : State) (c : Ctl) (hP : wkPR hp i T W ok exe endPc kp w s c)
    (hW : WideX exe s) : (wakeDR hp i T W ok exe endPc kp).Wi w s c :=
  (Classical.choose_spec
    (WorkerSide.wi_exists (X64WakeWorkerX.msW_K hp i T W w.1) (wkPR_seg hp i T W ok exe endPc kp w))).1 s c hP hW

/-- `wakeDR`'s invariant lies inside `NN ∧ ZR w ∧ WideX`. -/
theorem wakeDR_inv : ∀ w s c, (wakeDR hp i T W ok exe endPc kp).Wi w s c →
    NNZ exe endPc (ZR hp i W ok exe kp w) s c ∧ WideX exe s :=
  fun w => (Classical.choose_spec
    (WorkerSide.wi_exists (X64WakeWorkerX.msW_K hp i T W w.1) (wkPR_seg hp i T W ok exe endPc kp w))).2.1

/-- **`wake_obligations_IWR`'s `hW`** at `wakeDR`. -/
theorem hW_IR : ∀ w s c, (wakeDR hp i T W ok exe endPc kp).Wi w s c →
    NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ w.1.lbl w.1.cS W exe kp) s c :=
  fun w s c h => (wakeDR_inv hp i T W ok exe endPc kp w s c h).1

/-- **`wake_obligations_IWR`'s `hmp`** at `wakeDR`. -/
theorem hmp_IR : ∀ w L wr, ((wakeDR hp i T W ok exe endPc kp).ms w).mp L wr →
    Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (RuntimeLayout.ofPlaceWX hp i).Λ) wr L = true :=
  fun _ _ _ h => h.1.1

/-- **The instance's relation at `wakeDR`** (`wakeQI`'s data, main side
`M`, marks `μ`, store point `passT`). -/
noncomputable abbrev QIR (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : X64WakeM0.MSide {g : Gh // ok g}) (r0 r1 : {g : Gh // ok g} → Range) (passT : State → Prop) :
    WakeRel :=
  wakeQI hp i T W ok arch R1 μ M (wakeDR hp i T W ok exe endPc kp) r0 r1 passT

/-! ## The compatibility facts -/

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks} {M : X64WakeM0.MSide {g : Gh // ok g}}
  {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop}

/-- **`WCompatX`** at `wakeDR`: closed (`hms` by `rfl` at `msW := msXW
(wakeMs …) W T W`, `Gc` by `X64WakeInstFields.Gc_I`). -/
theorem hx_IR :
    WCompatX (QIR hp i T W ok exe endPc kp arch R1 μ M r0 r1 passT) (wakeDR hp i T W ok exe endPc kp) :=
  X64WakeAssembly.wCompatX_of X64WakeQ.hPT0 X64WakeQ.hKR X64WakeQ.hown
    (msW := fun w => Spike.Lib.X64WakeInst.wakeMs hp i w.1) (fun _ => rfl)
    (X64WakeInstFields.Gc_I hp i T W (R1 := R1) (M := M) (r0 := r0) (r1 := r1))

/-- **`WCompat`** at `wakeDR`, at the store point `wakePassT`, the records'
facts `GhOK` (`hok`), their self words' separation `SelfOK` (`hself`, for
`footLab`) and the two self words distinct (`hTW`); open: the marks' sites
(`hμ`). The worker never writes the self words: `ownInstr` by
`OwnInstrW.ownInstr_of` from `wakeZX`'s `OwnW W` (`hW_IR`), the runtime's
writes off both by `msW`'s `mp` (`msXW`), `ownMp1` by
`X64WakeOwnX.ownMp1XW` (inside `wCompat_of`). -/
theorem hC_IR_of [Kraken.Executable.ValidLayout exe]
    (hok : ∀ g, ok g → X64WakeInstFields.GhOK (RuntimeLayout.ofPlaceWX hp i).Λ g)
    (hself : ∀ w : {g : Gh // ok g}, Spike.Lib.X64WakeInst.SelfOK T W w.1)
    (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩)
    (hns : ∀ w s c, (wakeDR hp i T W ok exe endPc kp).Wi w s c → siteAt abi μ s = none) :
    WCompat (QIR hp i T W ok exe endPc kp arch R1 μ M r0 r1 Spike.Lib.X64.Flow.Worker.Wake.Pass.wakePassT)
      (wakeDR hp i T W ok exe endPc kp) μ (RuntimeLayout.ofPlaceWX hp i).Λ arch := by
  have hD : ∀ w s c, (wakeDR hp i T W ok exe endPc kp).Wi w s c →
      Spike.Lib.X64.Flow.Worker.NN exe endPc s ∧ WideX exe s :=
    fun w s c h => ⟨(wakeDR_inv hp i T W ok exe endPc kp w s c h).1.1,
      (wakeDR_inv hp i T W ok exe endPc kp w s c h).2⟩
  refine X64WakeAssembly.wCompat_of X64WakeQ.hPT0 X64WakeQ.hKR X64WakeQ.hown X64WakeQ.pt1 X64WakeQ.atUnpk
    X64WakeQ.atTexit (fun _ => rfl) (fun w => X64WakeWorkerX.msW_K hp i T W w.1)
    (WorkerSide.wide_of hD) hns (WorkerSide.sysExec_of hD)
    (WorkerSide.sysOk_of hD) (fun w => (hok w.1 w.2).2.1) (fun _ => rfl) (fun _ => rfl)
    (msW := fun w => Spike.Lib.X64WakeInst.wakeMs hp i w.1) (fun _ => rfl)
    (fun _ _ h => ⟨.inr (.inl h), (h.1.2 rfl).2, (h.1.2 rfl).1⟩) X64WakeQ.hC (fun w => ?_)
    (fun w => (hok w.1 w.2).2.2.2.2)
    (fun _ => WakeP.wakeP_foot_c) (fun _ => WakeP.wakeP_not_frzS_c)
    (fun w => (hok w.1 w.2).2.2.1) (fun w _ hf hL =>
      WakeP.wakeP_footLab (Spike.Lib.X64WakeInst.wakeLocs_ok hp i T W w.1 (hself w)) hf hL)
    (WorkerSide.pass_of (fun w s c h => (wakeDR_inv hp i T W ok exe endPc kp w s c h).1.2.1.1) X64WakeQ.hpT)
    (OwnInstrW.ownInstr_of X64WakeQ.hown fun w s c h =>
      Spike.Lib.X64.Flow.Worker.Wake.ZX.ownW (hW_IR hp i T W ok exe endPc kp w s c h).2)
    (fun _ => WakeP.wakeP_own_cov (.inr ⟨rfl, rfl⟩)) hTW
    (X64WakeInstFields.noProm_I hp i T W (R1 := R1) (M := M) (r0 := r0) (r1 := r1))
  obtain ⟨b, hb, ho, hT⟩ := (hok w.1 w.2).2.2.2.1
  exact ⟨_, hT, show wordAddr w.1.lbl w.1.cS = some _ by simp [wordAddr, hb], ho⟩

/-- **`WCompat`** at `wakeDR` (`hC_IR_of`), `noSite` by
`WorkerSide.noSite_of` from the marks' sites (`hμ`, open). -/
theorem hC_IR [Kraken.Executable.ValidLayout exe]
    (hok : ∀ g, ok g → X64WakeInstFields.GhOK (RuntimeLayout.ofPlaceWX hp i).Λ g)
    (hself : ∀ w : {g : Gh // ok g}, Spike.Lib.X64WakeInst.SelfOK T W w.1)
    (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩)
    (hl : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat) :
    WCompat (QIR hp i T W ok exe endPc kp arch R1 μ M r0 r1 Spike.Lib.X64.Flow.Worker.Wake.Pass.wakePassT)
      (wakeDR hp i T W ok exe endPc kp) μ (RuntimeLayout.ofPlaceWX hp i).Λ arch :=
  hC_IR_of hp i T W ok exe endPc kp hok hself hTW
    (WorkerSide.noSite_of (fun w s c h => ⟨(wakeDR_inv hp i T W ok exe endPc kp w s c h).1.1,
      (wakeDR_inv hp i T W ok exe endPc kp w s c h).2⟩) hl hend hμ)

/-- **`WCompat`** at `wakeDR` at the layout's executable and the runtime's
marks `PhRec.μ L` (`hμ`), closed but `hok`/`hself`/`hTW`: `noSite` by
`WorkerSide.noSite_ofPlaceWX`. -/
theorem hC_IRX (hok : ∀ g, ok g → X64WakeInstFields.GhOK (RuntimeLayout.ofPlaceWX hp i).Λ g)
    (hself : ∀ w : {g : Gh // ok g}, Spike.Lib.X64WakeInst.SelfOK T W w.1)
    (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩)
    (hl : Lays (RuntimeLayout.ofPlaceWX hp i).exe SccCode.wakeCells kp)
    (hend : endPc = endOf (RuntimeLayout.ofPlaceWX hp i).exe SccCode.wakeCells kp)
    (hμ : μ = Spike.Lib.X64.PhRec.μ (RuntimeLayout.ofPlaceWX hp i)) :
    WCompat (QIR hp i T W ok (RuntimeLayout.ofPlaceWX hp i).exe endPc kp arch R1 μ M r0 r1
        Spike.Lib.X64.Flow.Worker.Wake.Pass.wakePassT)
      (wakeDR hp i T W ok (RuntimeLayout.ofPlaceWX hp i).exe endPc kp) μ (RuntimeLayout.ofPlaceWX hp i).Λ arch := by
  have : Kraken.Executable.ValidLayout (RuntimeLayout.ofPlaceWX hp i).exe := (RuntimeLayout.ofPlaceWX hp i).valid
  subst hμ
  exact hC_IR_of hp i T W ok _ endPc kp hok hself hTW
    (WorkerSide.noSite_ofPlaceWX hp i (fun w s c h => ⟨(wakeDR_inv hp i T W ok _ endPc kp w s c h).1.1,
      (wakeDR_inv hp i T W ok _ endPc kp w s c h).2⟩) hl hend)

end Side

/-- **The record at the clone satisfies `GhOK`**: `X64WakeOkW.okW_of_clone`
at the record's own placement and flag; the worker's word `cw` (`hcw`);
open: `hin`, `hS`. -/
theorem ghOK_of_clone {Λ : Scc.Sem.Layout} {T S : Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel} {pT : Loc} {cw : TermRun.Word}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {cA : Nat} (hv : ValRep lbl (.loc ⟨l, 0⟩ 0) cA)
    /- (the spawn's argument word, bumped) -/ (hcw : cw.val = .loc ⟨l, 0⟩ 0)
    /- OPEN: `c`'s label holds a word -/ (hin : 0 < lsize l)
    /- OPEN: the source memory is nonempty at the spawn -/ (hS : 0 < S) :
    X64WakeInstFields.GhOK Λ (X64WakeOkW.recW T S lbl lsize l pT cw) :=
  (X64WakeOkW.okW_of_clone hm hwf hv hcw hin hS rfl rfl).1

/-! ## The assembly with a per-record `hW` -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  {arch : WeakMem.Arch} {B : Budget} {asm : Asm} {E : Entry}
  {ok : Gh → Prop} {lab : String → Int64} {T W : BitVec 64}
  {R1 : Cfg → TermRun.Cfg → Prop} {SR : {g : Gh // ok g} → SpawnRec}
  {cT : {g : Gh // ok g} → Loc} {cS : {g : Gh // ok g} → WeakMem.Address} {pT : {g : Gh // ok g} → Loc}
  {P : {g : Gh // ok g} → Inv2Params isa} {G : {g : Gh // ok g} → Loc → Val → Prop}
  {D : WSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop}

/-- **The assembly at main's instance, the worker's facts from a
per-record `hW`**: `wake_obligations_I` with `hhalt1`, `hW1` (`ZX.hhalt1_ofX`,
`ZX.hW1_ofX` per record), `hmapW` (`X64WakeMappedRow.hW_of` with
`X64WakeLabMapped.labMapped_flag` at the record's flag) and `post_wit`
(`X64WakePostWit.post_wit_of`) from the worker's states inside
`NNZ exe endPc (wakeZX Λ (SR w).lbl (cS w) W' exe kp)`. -/
theorem wake_obligations_IWR {Ab Ac : State → Prop}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    (hC : WCompat (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ arch)
    (hx : WCompatX (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D)
    /- OPEN: main's side -/
    (hC0 : X64WakeM0.WCompat0
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W)
      (wakeM hp i T W ok lab _ hoff)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ)
    /- OPEN -/
    (hstart : ∃ d, (target (kernel 1) E).load asm (RuntimeLayout.ofPlaceWX hp i).Λ = some d)
    /- OPEN: the pre-spawn half -/
    (O : Pre1T arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm E R1 Ab Ac)
    /- OPEN: the spawn -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W).Post
          (RuntimeLayout.ofPlaceWX hp i).Λ (afterClone abi d tid th stack tls r) s')
    /- (`hW_IR` at `D := wakeDR`) the worker's states keep the record's `wakeZX` -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} {W' : BitVec 64}
    (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hW : ∀ w s c, D.Wi w s c →
      NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ (SR w).lbl (cS w) W' exe kp) s c)
    /- (instance data; `rfl` at `X64WakeInst.wakeQI`) -/ (hSR : ∀ w, (SR w).lbl = (wakeSR w.1).lbl)
    /- (`hmp_IR`) -/
    (hmp : ∀ w L wr, (D.ms w).mp L wr →
      Kernel.mapped (X64Consumer.K0 (RuntimeLayout.ofPlaceWX hp i).Λ) wr L = true)
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg' (RuntimeLayout.ofPlaceWX hp i).Λ po)
    (hpa : cellsOf asm = some po.prog)
    /- (`rfl` at wake's worker sides) -/ (hDp : D.p = Spike.Lib.X64WakeT1.wakeSrc := by rfl) :
    WakeObligations arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) E
      (TiPre Ab Ac) :=
  X64WakeAssemblyI.wake_obligations_I hp i hoff hC hx hC0 hstart O spawn
    (fun w s c h => Spike.Lib.X64.Flow.Worker.Wake.ZX.hhalt1_ofX (ι := Unit) (Wi := fun _ => D.Wi w) hend
      (cOf := id) (fun _ s c h => hW w s c h) () s c h)
    (X64WakeMappedRow.hW_of hC.K hmp fun w s c hi => by
      obtain ⟨a, hTa, hAa, -⟩ := hC.cT w
      rw [hC.lbl w]
      exact X64WakeLabMapped.labMapped_flag
        (fun sa hpt => Spike.Lib.X64.Flow.Worker.Wake.ZX.labPtr (hW w s c hi).2 sa hpt)
        hAa hTa (hC.cTin w))
    (fun w s c e h => Spike.Lib.X64.Flow.Worker.Wake.ZX.hW1_ofX (ι := Unit) (Wi := fun _ => D.Wi w)
      (cOf := id) (fun _ s c h => hW w s c h) () s c e h)
    hpl hpa
    (X64WakePostWit.post_wit_of rfl rfl (X64WakeQ.hwf_ofPlaceOK hp i)
      (fun w s c h => (hSR w).symm ▸ placed_I hp i T W w s c h)
      (fun w s c h => Spike.Lib.X64.Flow.Worker.Wake.ZX.placed (hW w s c h).2)) hDp

/-- `hW_IR` is `wake_obligations_IWR`'s `hW` at `wakeQI`'s data
(`SR := (wakeSR ·.1)`, `cS := (·.1.cS)`, `D := wakeDR`). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)
    (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat) :
    ∀ w s c, (wakeDR hp i T W ok exe endPc kp).Wi w s c → NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ
      ((wakeSR ·.1) w).lbl ((·.1.cS) w) W exe kp) s c :=
  hW_IR hp i T W ok exe endPc kp

/-- info: 'Spike.Lib.X64WakeWorkerR.hx_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hx_IR

/-- info: 'Spike.Lib.X64WakeWorkerR.hC_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_IR

/-- info: 'Spike.Lib.X64WakeWorkerR.hC_IRX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_IRX

/-- info: 'Spike.Lib.X64WakeWorkerR.ghOK_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ghOK_of_clone

/-- info: 'Spike.Lib.X64WakeWorkerR.wake_obligations_IWR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_IWR

end Spike.Lib.X64WakeWorkerR
