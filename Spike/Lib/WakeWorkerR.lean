/-
**wake.w's worker side per record** (AArch64): the
worker's side with each record's states inside `wakeZX` at that record's
own spawn placement `w.1.lbl` and flag `w.1.cS` (not one `lbl'`/`cSf` for
the family), so the assembly needs neither `hlbl` nor `hcS`, and the
records' facts are `WakeInstFields.GhOK` alone. The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `ZR`, `wkPR`, `wkPR_seg`: the record's `wakeZX`, the union of the
  preconditions of the segments keeping it (the child's entry by
  `WakeChildXI.childSeg_XI` at `lbl' := w.1.lbl`, `cSf := w.1.cS`), its
  segment.
- `wakeDR`: the worker's side (`WorkerSide.wi_exists` per record);
  `wakeDR_entry`, `wakeDR_inv`; `hW_IR`, `hmp_IR`.
- `QIR`: `WakeInst.wakeQI`'s relation data at `D := wakeDR`.
- `hx_IR`, `hC_IR`: `WCompatX`, `WCompat` at `ok` records satisfying `GhOK`
  (`hok`); open in `hC_IR`: `hμ` (`WorkerSide.wake_hμ`).
- `ghOK_of_clone`: `WakeOkW.recW` satisfies `GhOK` (open: `hin`, `hS`).
- `wake_obligations_IWR`: `WakeAssemblyI.wake_obligations_I` with the
  worker's facts from a per-record `hW` (`wakeZX` at `(SR w).lbl`, `cS w`)
  and `post_wit` by `WakePostWit.post_wit_of`.
-/
import Spike.Lib.WakeAssemblyI
import Spike.Lib.WakeWorkerX
import Spike.Lib.WakeOkW
import Spike.Lib.WakeAssembly
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeWorkerR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.WakeP Spike.Lib.WakePreTi
open Spike.Lib.Handover Spike.Lib.Inv2Core
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh wakeMs wakeSR wakeG' wakeLocs wakeM placed_I)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.A64.Flow.Worker (NNZ)
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.WideKeep (WideX)

/-! ## The worker's side per record -/

section Side

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat)

/-- **The record's `wakeZX`**: at the instance's layout, the record's spawn
placement and flag. -/
abbrev ZR (w : {g : Gh // ok g}) : Frag isaLSE2 := wakeZX (RuntimeLayout.ofPlaceW hp i).Λ w.1.lbl w.1.cS exe kp

/-- **The worker's pairs**: those of the precondition of some segment
keeping the record's `wakeZX`. -/
def wkPR (w : {g : Gh // ok g}) : Frag isaLSE2 := fun s c =>
  ∃ Pj : Frag isaLSE2, SegTC (NNZ exe endPc (ZR hp i ok exe kp w)) wakeSrc w.1.lbl (wakeMs hp i w.1) Pj
    (fun _ _ => False) ∧ Pj s c

/-- **A segment's precondition's pairs are the worker's.** -/
theorem wkPR_of {w : {g : Gh // ok g}} {Pj : Frag isaLSE2}
    (h : SegTC (NNZ exe endPc (ZR hp i ok exe kp w)) wakeSrc w.1.lbl (wakeMs hp i w.1) Pj (fun _ _ => False))
    {s : State} {c : Ctl} (hP : Pj s c) : wkPR hp i ok exe endPc kp w s c :=
  ⟨Pj, h, hP⟩

/-- `wkPR`'s segment. -/
theorem wkPR_seg (w : {g : Gh // ok g}) :
    SegTC (NNZ exe endPc (ZR hp i ok exe kp w)) wakeSrc w.1.lbl (wakeMs hp i w.1) (wkPR hp i ok exe endPc kp w)
      (fun _ _ => False) :=
  (WakeWorkerX.segTC_iUnion (κ := {Pj : Frag isaLSE2 // SegTC (NNZ exe endPc (ZR hp i ok exe kp w)) wakeSrc
      w.1.lbl (wakeMs hp i w.1) Pj (fun _ _ => False)}) fun j => j.2).mono_pre
    fun _ _ ⟨Pj, h, hP⟩ => ⟨⟨Pj, h⟩, hP⟩

/-- **The worker's side per record**: `WorkerSide.side`'s construction with
each record's own `wakeZX`. -/
noncomputable def wakeDR : WSide {g : Gh // ok g} where
  lbl w := w.1.lbl
  ms w := wakeMs hp i w.1
  Wi w := Classical.choose (WorkerSide.wi_exists (WakeWorkerX.wakeMs_K hp i w.1) (wkPR_seg hp i ok exe endPc kp w))
  closed w := (Classical.choose_spec
    (WorkerSide.wi_exists (WakeWorkerX.wakeMs_K hp i w.1) (wkPR_seg hp i ok exe endPc kp w))).2.2
  cw w := w.1.cwW
  S w := w.1.S

/-- `wakeDR`'s invariant holds the segments' entries in `WideX exe`. -/
theorem wakeDR_entry (w : {g : Gh // ok g}) (s : State) (c : Ctl) (hP : wkPR hp i ok exe endPc kp w s c)
    (hW : WideX exe s) : (wakeDR hp i ok exe endPc kp).Wi w s c :=
  (Classical.choose_spec
    (WorkerSide.wi_exists (WakeWorkerX.wakeMs_K hp i w.1) (wkPR_seg hp i ok exe endPc kp w))).1 s c hP hW

/-- `wakeDR`'s invariant lies inside `NN ∧ ZR w ∧ WideX`. -/
theorem wakeDR_inv : ∀ w s c, (wakeDR hp i ok exe endPc kp).Wi w s c →
    NNZ exe endPc (ZR hp i ok exe kp w) s c ∧ WideX exe s :=
  fun w => (Classical.choose_spec
    (WorkerSide.wi_exists (WakeWorkerX.wakeMs_K hp i w.1) (wkPR_seg hp i ok exe endPc kp w))).2.1

/-- **`wake_obligations_IWR`'s `hW`** at `wakeDR`. -/
theorem hW_IR : ∀ w s c, (wakeDR hp i ok exe endPc kp).Wi w s c →
    NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ w.1.lbl w.1.cS exe kp) s c :=
  fun w s c h => (wakeDR_inv hp i ok exe endPc kp w s c h).1

/-- **`wake_obligations_IWR`'s `hmp`** at `wakeDR`. -/
theorem hmp_IR : ∀ w L wr, ((wakeDR hp i ok exe endPc kp).ms w).mp L wr →
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) wr L = true :=
  fun _ _ _ h => h.1

/-! ## The compatibility facts -/

variable {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks} {M : WakeM0.MSide {g : Gh // ok g}}
  {r0 r1 : {g : Gh // ok g} → Range}

/-- **The instance's relation at `wakeDR`** (`wakeQI`'s data, main side
`M`, marks `μ`). -/
noncomputable abbrev QIR (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (μ : Marks)
    (M : WakeM0.MSide {g : Gh // ok g}) (r0 r1 : {g : Gh // ok g} → Range) : WakeRel :=
  WakeQ.wakeQ arch R1 {g : Gh // ok g} (wakeSR ·.1) (·.1.cT) (·.1.cS) (·.1.pT)
    (fun g => wakeP abi μ (wakeLocs hp i g.1)) (fun g => wakeG' hp i g.1) M (wakeDR hp i ok exe endPc kp) r0 r1

/-- **`WCompatX`** at `wakeDR`: closed. -/
theorem hx_IR : WCompatX (QIR hp i ok exe endPc kp arch R1 μ M r0 r1) (wakeDR hp i ok exe endPc kp) :=
  WakeAssembly.wCompatX_of WakeQ.hPT0 WakeQ.hKR WakeQ.hown fun _ => WakeG.wakeG_cT (G0 := _) _

/-- **`WCompat`** at `wakeDR`, the records' facts `GhOK` (`hok`); open:
the marks' sites (`hμ`). -/
theorem hC_IR [Kraken.Executable.ValidLayout exe] (hok : ∀ g, ok g → GhOK (RuntimeLayout.ofPlaceW hp i).Λ g)
    (hl : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat) :
    WCompat (QIR hp i ok exe endPc kp arch R1 μ M r0 r1) (wakeDR hp i ok exe endPc kp)
      μ (RuntimeLayout.ofPlaceW hp i).Λ arch := by
  have hD : ∀ w s c, (wakeDR hp i ok exe endPc kp).Wi w s c → Spike.Lib.A64.Flow.Worker.NN exe endPc s ∧ WideX exe s :=
    fun w s c h => ⟨(wakeDR_inv hp i ok exe endPc kp w s c h).1.1, (wakeDR_inv hp i ok exe endPc kp w s c h).2⟩
  refine WakeAssembly.wCompat_of WakeQ.hPT0 WakeQ.hKR WakeQ.hown WakeQ.pt1 WakeQ.atUnpk WakeQ.atTexit
    { lbl := fun _ => rfl
      K := fun w => WakeWorkerX.wakeMs_K hp i w.1
      wide := WorkerSide.wide_of hD
      noSite := WorkerSide.noSite_of hD hl hend hμ
      sysExec := WorkerSide.sysExec_of hD
      sysOk := WorkerSide.sysOk_of hD
      cwv := fun w => (hok w.1 w.2).2.1
      S := fun _ => rfl
      hZ := fun w s c h => (wakeDR_inv hp i ok exe endPc kp w s c h).1.2.1.1 }
    (fun _ => rfl) (fun _ _ => rfl)
    (fun w L hm => ⟨Or.inr (Or.inl hm), (hm.2 rfl).2, (hm.2 rfl).1⟩)
    WakeQ.hC (fun w => ?_) (fun w => (hok w.1 w.2).2.2.2.2) (fun _ => Or.inr (Or.inr ⟨rfl, rfl⟩))
    (fun _ h => h.2 rfl) (fun w => (hok w.1 w.2).2.2.1)
    (fun w L hf hL => by
      rcases hf with hf | hf | ⟨-, hf⟩
      · exact hf.elim
      · exact ((WakeInst.wakeLocs_ok hp i w.1).priv_nlab 1 L (by omega) hf hL).elim
      · exact hf)
    WakeQ.hpT (fun _ _ _ _ hn hc => noProm_prom hn hc)
  obtain ⟨b, hb, ho, hT⟩ := (hok w.1 w.2).2.2.2.1
  exact ⟨_, hT, show wordAddr w.1.lbl w.1.cS = some _ by simp [wordAddr, hb], ho⟩

end Side

/-- **The record at the clone satisfies `GhOK`**: `WakeOkW.okW_of_clone` at
the record's own placement and flag; the worker's word `cw` (`hcw`); open: `hin`, `hS`. -/
theorem ghOK_of_clone {Λ : Scc.Sem.Layout} {T S : Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel} {pT : Loc} {cw : TermRun.Word}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {cA : Nat} (hv : ValRep lbl (.loc ⟨l, 0⟩ 0) cA)
    /- (the spawn's argument word, bumped) -/ (hcw : cw.val = .loc ⟨l, 0⟩ 0)
    /- (`newLoc_in`) OPEN -/ (hin : 0 < lsize l)
    /- (G3) OPEN -/ (hS : 0 < S) :
    GhOK Λ (WakeOkW.recW T S lbl lsize l pT cw) :=
  (WakeOkW.okW_of_clone hm hwf hv hcw hin hS rfl rfl).1

/-! ## The assembly with a per-record `hW` -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry}
  {ok : Gh → Prop} {lab : String → Int64}
  {R1 : Cfg → TermRun.Cfg → Prop} {SR : {g : Gh // ok g} → SpawnRec}
  {cT : {g : Gh // ok g} → Loc} {cS : {g : Gh // ok g} → WeakMem.Address} {pT : {g : Gh // ok g} → Loc}
  {P : {g : Gh // ok g} → Inv2Params isaLSE2} {G : {g : Gh // ok g} → Loc → Val → Prop}
  {D : WSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range}

/-- **The assembly at main's instance, the worker's facts from a
per-record `hW`**: `wake_obligations_I` with `hhalt1`, `hW1` (`ZX.hhalt1_ofX`,
`ZX.hW1_ofX` per record), `hmapW` (`WakeMappedRow.hW_of` with
`WakeLabMapped.labMapped_flag` at the record's flag) and `post_wit`
(`WakePostWit.post_wit_of`) from the worker's states inside
`NNZ exe endPc (wakeZX Λ (SR w).lbl (cS w) exe kp)`. -/
theorem wake_obligations_IWR {Ab Ac : State → Prop}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- (worker side; `hC_IR` / `hx_IR`) -/
    (hC : WCompat (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1) D
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).Λ arch)
    (hx : WCompatX (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1) D)
    /- (its `relW0` is `WakeInst.relW0_I`) OPEN -/
    (hC0 : WakeM0.WCompat0 (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1)
      (wakeM hp i ok lab _ hoff)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).Λ)
    /- OPEN -/
    (hstart : ∃ d, (target (kernel 1) E).load asm (RuntimeLayout.ofPlaceW hp i).Λ = some d)
    /- OPEN -/
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B asm E R1 Ab Ac)
    /- OPEN -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1).Post
          (RuntimeLayout.ofPlaceW hp i).Λ (afterClone abi d tid th stack tls r) s')
    /- (`hW_IR` at `D := wakeDR`) the worker's states keep the
    record's `wakeZX` -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe wakeProg kp)
    (hW : ∀ w s c, D.Wi w s c → NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ (SR w).lbl (cS w) exe kp) s c)
    /- (instance data; `rfl` at `WakeInst.wakeQI`) -/ (hSR : ∀ w, (SR w).lbl = (wakeSR w.1).lbl)
    /- (`hmp_IR`) -/
    (hmp : ∀ w L wr, (D.ms w).mp L wr →
      Kernel.mapped (A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) wr L = true)
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    (hpl : PlaceW pcfg' (RuntimeLayout.ofPlaceW hp i).Λ po)
    (hpa : textProgram asm = .ok po.prog) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B asm
      (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1) E (TiPre Ab Ac) :=
  WakeAssemblyI.wake_obligations_I hp i hoff hC hx hC0 hstart O spawn
    (fun w s c h => Spike.Lib.A64.Flow.Worker.Wake.ZX.hhalt1_ofX (ι := Unit) (Wi := fun _ => D.Wi w) hend
      (cOf := id) (fun _ s c h => hW w s c h) () s c h)
    (WakeMappedRow.hW_of hC.K hmp fun w s c hi => by
      obtain ⟨a, hTa, hAa, -⟩ := hC.cT w
      rw [hC.lbl w]
      exact WakeLabMapped.labMapped_flag
        (fun sa hpt => Spike.Lib.A64.Flow.Worker.Wake.ZX.labPtr (hW w s c hi).2 sa hpt)
        hAa hTa (hC.cTin w))
    (fun w s c e h => Spike.Lib.A64.Flow.Worker.Wake.ZX.hW1_ofX (ι := Unit) (Wi := fun _ => D.Wi w)
      (cOf := id) (fun _ s c h => hW w s c h) () s c e h)
    hpl hpa
    (WakePostWit.post_wit_of rfl rfl (WakeQ.hwf_ofPlaceOK hp i)
      (fun w s c h => (hSR w).symm ▸ placed_I hp i w s c h)
      (fun w s c h => Spike.Lib.A64.Flow.Worker.Wake.ZX.placed (hW w s c h).2))

/-- `hW_IR` is `wake_obligations_IWR`'s `hW` at `wakeQI`'s data
(`SR := (wakeSR ·.1)`, `cS := (·.1.cS)`, `D := wakeDR`). -/
example {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat) :
    ∀ w s c, (wakeDR hp i ok exe endPc kp).Wi w s c → NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ
      ((wakeSR ·.1) w).lbl ((·.1.cS) w) exe kp) s c :=
  hW_IR hp i ok exe endPc kp

/-- info: 'Spike.Lib.WakeWorkerR.hC_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC_IR

/-- info: 'Spike.Lib.WakeWorkerR.wake_obligations_IWR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_IWR

end Spike.Lib.WakeWorkerR
