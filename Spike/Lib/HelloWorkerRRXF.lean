/-
**hello.w's worker side at the spawned child's segment inside `XHF ∧ AbX`** (hello.w, rows 5j-wit-W,
5j-wit-E-call, 5i-hab1, SegTCSX-inhab; AArch64): `HelloWorkerRR.helloDR` at each record's segment (`seg_childXHF`'s
obligations with `AbObl.zObl_abX`/`zXObl_abX`): the entry fragment `P w := childPX … (cS w)`, the segment fact
`Z w := ZHR exe kp ∧ (XHF ∧ AbX μ lab)`, the landing fragment `X w := XHF ∧ AbX μ lab`, at labels `helloProg`'s
at `lo` (`hlab`) whose marks are off the labels (`hμ`).

Release note: this is the `DH` of the assembly's switch (`HelloAssemblyI.DH` at `P := childPX`, `Z := ZHR ∧ X`,
`X := XHF ∧ AbX`, `hseg := hsegF`). The entry fragment is inhabited only where `childPX` is produced at the clone
(row B8-hcS, `childPX_of_clone`); the final instance carries that witness.

- `hsegF`: each record's segment.
- `helloDRF`: the worker's side.
- `helloDRF_XHF`, `helloDRF_ab`: the invariant inside `XHF`, and its abort facts `AbFacts μ (WriteAb.Ab lab)`.
- `helloDRF_hplW`, `helloDRF_hcall`, `helloDRF_flag`: the rows `hplW`, `hcall` and the flag.
- `helloDRF_clone`: the invariant holds at the child after main's `clone` (`SegR.childPX_of_cloneX`), once
  `ChildPrem` holds there (the executable in the fragment): `helloDRF`'s entry fragment is produced at the clone
  (row B8-hcS).
- `helloDRF_zhr`: the invariant inside `NNH ∧ WideX ∧ Pend (ZHR exe kp)` (the consumers of `Z := ZHR`).
-/
import Spike.Lib.HelloWorkerRRX
import Spike.Lib.A64HelloXHFSeg
import Spike.Lib.A64HelloChildPX
import Spike.Lib.A64HelloAbLand

namespace Spike.Lib.HelloWorkerRRXF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.A64.Flow.Worker (NNH)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem ChildD)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZObl ZXObl childPX)
open Spike.Lib.A64.Flow.Worker.Hello.AbObl (AbX MarksL)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.A64.HelloPh.XH (XHF)
open Spike.Lib.HelloWorkerRR (helloDR)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

variable {ι : Type} {Λ : Scc.Sem.Layout} (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid Λ)
  (exe : _root_.Executable) [Kraken.Executable.ValidLayout exe] (endPc : Int64) (kp : Nat) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isaLSE2)
  (cS : ι → WeakMem.Address) (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  {μ : Marks} (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
  (hK : ∀ w fs, (ms w fs).K = some abi)
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)

include hI hp hend hlab hμ hK in
/-- **Each record's segment**: the spawned child's run inside `XHF ∧ AbX μ lab` (`seg_childXHF`'s obligations with
`AbObl.zObl_abX` and `AbObl.zXObl_abX`; `zObl_abX`'s region and slice facts from `d.ok` and `ChildPrem.hm`). -/
theorem hsegF (w : ι) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ (fun w s c fs => ZHR exe kp s c fs ∧
        (XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs)) w s c fs)
      ((fun w s c fs => XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs) w)
      helloSrc (lbl w) (ms w) ((fun w => childPX exe endPc kp (lbl w) (ms w) (cS w)) w) (fun _ _ _ => False) :=
  Spike.Lib.A64.Flow.Worker.Hello.SegRP.seg_childPPXc hp hend (hK w)
    (fun d ho hc hcS => ZObl.and
      (Spike.Lib.A64.HelloPh.XH.zObl_XHF
        (Spike.Lib.A64.HelloPh.XHNode.zObl_XH hcS
          (fun y k => hI.hkid _ _ _ _ _ _ y k) hI.hwc
          (Spike.Lib.A64.Flow.Worker.Hello.PlacedZ.zObl_placed_ok (d := d) ho hc.hv0 hc.hv1 hc.hv2 hc.hv hc.hvu))
        (Spike.Lib.A64.Flow.Worker.Hello.FlagObl.zObl_flag hcS))
      (let ⟨_, hR, hal, _, hhi⟩ := ho
       Spike.Lib.A64.Flow.Worker.Hello.AbObl.zObl_abX hp hend hlab hμ hR hal (by omega) hhi hc.hm))
    (fun d ho hc hcS => ZXObl.and
      (ZXObl.and (Spike.Lib.A64.HelloPh.XHLand.zXObl_XH hc.hv hc.hvu)
        (Spike.Lib.A64.Flow.Worker.Hello.FlagR.zXObl_flag hcS))
      (Spike.Lib.A64.Flow.Worker.Hello.AbObl.zXObl_abX hp hend hlab hμ))

/-- **The worker's side at the spawned child's segment inside `XHF ∧ AbX μ lab`.** -/
noncomputable abbrev helloDRF : WSideH ι :=
  helloDR exe endPc SR lbl ms (fun w => childPX exe endPc kp (lbl w) (ms w) (cS w))
    (fun w s c fs => ZHR exe kp s c fs ∧
      (XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs))
    (fun w s c fs => XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs) hK
    (hsegF hI exe endPc kp lbl ms cS hp hend hlab hμ hK) cw bufL nB mB

/-- **`helloDRF`'s invariant inside its landing fragment's `XHF`** (`helloDR_X`'s first conjunct). -/
theorem helloDRF_XHF : ∀ w s c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w s c fs →
    XHF Λ (lbl w) (cS w) s c fs := fun w s c fs h =>
  (HelloWorkerRR.helloDR_X exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h).1

/-- **`helloDRF`'s abort facts** (row 5i-hab1): every state of the invariant has `AbFacts μ (WriteAb.Ab lab)`
(`helloDR_X`'s second conjunct, `AbX`'s body). -/
theorem helloDRF_ab : ∀ w s c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w s c fs →
    HelloPostAb.AbFacts μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s := fun w s c fs h =>
  (HelloWorkerRR.helloDR_X exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h).2

/-- **The row `hplW` at `helloDRF`.** -/
theorem helloDRF_hplW : ∀ w st c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w st c fs →
    PlacedSE Λ (lbl w) st c fs := fun w st c fs h =>
  Spike.Lib.A64.HelloPh.XH.hplW_ofF (fun w s c fs h => helloDRF_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK
    cw bufL nB mB w s c fs h) w st c fs h

/-- **The row `hcall` at `helloDRF`.** -/
theorem helloDRF_hcall : ∀ w st c,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w st c [] →
    ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (lbl w) st [⟨"u", workerRestH, c'.env, [], .unit⟩] :=
  Spike.Lib.A64.HelloPh.XH.hcall_ofF (fun w s c fs h => helloDRF_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK
    cw bufL nB mB w s c fs h)

/-- **The flag at `helloDRF`.** -/
theorem helloDRF_flag : ∀ w st c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w st c fs →
    FlagF (cS w) st c fs :=
  Spike.Lib.A64.HelloPh.XH.hflag_ofF (fun w s c fs h => helloDRF_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK
    cw bufL nB mB w s c fs h)

/-- **`helloDRF`'s invariant inside `NNH ∧ WideX ∧ Pend (ZHR exe kp)`**: the consumers of the segment fact
`Z := ZHR exe kp` (`HelloHaltMapW`, `HelloPassH`) read it through this projection. -/
theorem helloDRF_zhr : ∀ w s c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc (ZHR exe kp) s c fs := fun w s c fs h =>
  have h' := HelloWorkerRR.helloDR_inv exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h
  ⟨h'.1, h'.2.1, h'.2.2.mono fun _ _ _ h => h.1⟩

/-- **`helloDRF`'s invariant at the child after main's `clone`** (row B8-hcS): `childPX_of_cloneX`'s entry,
given word 3 at the record's flag (`hw3`), `ChildPrem` at the child of main's thread and the clone's `tls`
(`hpr`), and a fragment executable (`hw`, as `HelloWiI`'s `HelloMainG.hw_IH`; `WideX` at the child by
`WorkerSide.wideX_childAfter`). The entry fragment `childPX` is produced at the clone, so the segment's
precondition is not empty there. -/
theorem helloDRF_clone (w : ι) {Λ' : Scc.Sem.Layout} {r0 r1 : Range} {Xc : State → Prop}
    {lbl0 : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.HelloPreA.ClonePreH Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM Λ' r0 r1 Xc lbl0 t s)
    (hX : ∀ st, Xc st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) (hal : (r1.lo + r1.size) % 16 = 0) (hsz : 272 ≤ r1.size)
    (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) (hw3 : w3.val = .loc (cS w) 0)
    (hpr : ∀ th tls, t.1.threads = #[th] → callOf abi th = some (.clone (r1.lo + r1.size) tls) →
      ChildPrem exe endPc kp (lbl w) (ms w)
      (Spike.Lib.A64.Flow.DFrame (Spike.Lib.A64.Flow.Worker.Wake.Child.childR (r1.lo + r1.size) (-272))
        (Spike.Lib.Handover.childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
      (Spike.Lib.A64.Flow.Worker.Hello.SegR.wordsX th) (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size))
      w0 w1 w2 w3 w4 n m)
    (hw : Scc.Cert.WideA64.ExeWide exe) :
    ∃ (th : Thread isaLSE2) (tls : Nat), t.1.threads = #[th] ∧
      (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w
        (Spike.Lib.Handover.childAfter abi t.2 0 th (r1.lo + r1.size) tls).st
        (Spike.Lib.A64.Flow.Worker.Hello.SegR.kidH T w0 w1 w2 w3 w4) [] := by
  obtain ⟨th, tls, hth, hcall, -, hP⟩ := Spike.Lib.A64.Flow.Worker.Hello.SegR.childPX_of_cloneX (lbl' := lbl w)
    (ms := ms w) (kp := kp) hp hend h hX htop hal hsz T w0 w1 w2 w3 w4 n m hw3
  obtain ⟨th', _, _, _, _, _, _, _, _, _, _, _, hth', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXs, -⟩ := h
  obtain rfl : th' = th := by
    have := hth'.symm.trans hth
    simpa using this
  obtain ⟨he, -, hd⟩ := hX _ hXs
  exact ⟨th', tls, hth, HelloWorkerRR.helloDR_entry exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w _ _ _
    (hP (hpr th' tls hth hcall)) (Spike.Lib.WakeW1.WorkerSide.wideX_childAfter
      (Spike.Lib.WakeW1.WorkerSide.wideX_of hw he hd))⟩

end Spike.Lib.HelloWorkerRRXF

/-- info: 'Spike.Lib.HelloWorkerRRXF.helloDRF_hplW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRXF.helloDRF_hplW

/-- info: 'Spike.Lib.HelloWorkerRRXF.helloDRF_hcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRXF.helloDRF_hcall

/-- info: 'Spike.Lib.HelloWorkerRRXF.helloDRF_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRXF.helloDRF_flag

/-- info: 'Spike.Lib.HelloWorkerRRXF.helloDRF_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRXF.helloDRF_ab

/-- info: 'Spike.Lib.HelloWorkerRRXF.helloDRF_zhr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRXF.helloDRF_zhr

/-- info: 'Spike.Lib.HelloWorkerRRXF.helloDRF_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloWorkerRRXF.helloDRF_clone
