/-
**hello.w's worker side at the spawned child's segment inside `XHF ∧ AbX` on x86-64** (the twin of
`Spike/Lib/HelloWorkerRRXF.lean`): `X64HelloWorkerRR.helloDR` at each record's segment (`seg_childPPXc`'s
obligations with `AbObl.zObl_abX`/`zXObl_abX`): the entry fragment `P w := childPX … (cS w)`, the segment fact
`Z w := ZHR exe kp ∧ (XHF ∧ AbX μ lab)`, the landing fragment `X w := XHF ∧ AbX μ lab`, at labels `helloCells`'
at `lo` (`hlab`) whose marks are off the labels (`hμ`).

This is the assembly's worker side (`X64HelloAssemblyI.DH` at `P := childPX`, `Z := ZHR ∧ X`,
`X := XHF ∧ AbX`, `hseg := hsegF`). The entry fragment `childPX` holds at the child where `ChildPrem` holds after
main's clone (`SegRP.childPX`'s producer at the clone's data).

- `hsegF`: each record's segment.
- `helloDRF`: the worker's side.
- `helloDRF_XHF`, `helloDRF_ab`: the invariant inside `XHF`, and its abort facts `AbFacts μ (WriteAb.Ab lab)`.
- `helloDRF_hplW`, `helloDRF_hcall`, `helloDRF_flag`: the rows `hplW`, `hcall` and the flag.
- `helloDRF_zhr`: the invariant inside `NNH ∧ WideX ∧ Pend (ZHR exe kp)` (the consumers of `Z := ZHR`).
- `hsegFY`, `helloDRFY`, `helloDRFY_*`: the same with a node-only fragment `Y w` in the segment fact
  (`ZHR ∧ Y w ∧ (XHF ∧ AbX)`, `seg_childPPXcY`).

## Differences from the AArch64 version

- The cells are `SccCode.helloCells` (AArch64 `helloProg`), the labels' check `Scc.Sem.X64.codeLabel` (AArch64
  `Link.A64.codeOf`), the abort model `Scc.Sem.X64.abi`.
- The segment is `X64HelloWorkerSegRPX.seg_childPPXc`; the child datum's region facts `ChildD.ok` carry no
  alignment, and `zObl_abX` takes the region `R.lo ≤ -128` (from `ChildD.ok`'s `-264`).
- `XHNode.zObl_XH` takes the immediate table's facts as `hik`, `hiw` (`ImmsKid.hkid`, `ImmsKid.hwc`).
- AArch64's `helloDRF_clone` is not twinned: it is dead in hello. So are `HelloWorkerRRX` and `A64HelloChildPX`,
  which AArch64 imports; this module imports neither twin.
-/
import Spike.Lib.X64HelloWorkerRR
import Spike.Lib.X64HelloXHFSeg
import Spike.Lib.X64HelloXHNode
import Spike.Lib.X64HelloPlacedZObl
import Spike.Lib.X64HelloFlagObl
import Spike.Lib.X64HelloXHLand
import Spike.Lib.X64HelloFlagR
import Spike.Lib.X64HelloAbOblZ
import Spike.Lib.X64HelloAbLand

namespace Spike.Lib.X64HelloWorkerRRXF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64.Flow.Worker (NNH)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64HelloSplit (workerCallH workerRestH)
open Spike.Lib.X64.Flow.Worker.Hello.Z (ZHR)
open Spike.Lib.X64.Flow.Worker.Hello.SegRP (ZObl ZXObl childPX)
open Spike.Lib.X64.Flow.Worker.Hello.AbObl (AbX MarksL)
open Spike.Lib.X64.Flow.Worker.Hello.FlagZ (FlagF)
open Spike.Lib.X64.HelloPh.XH (XHF)
open Spike.Lib.X64HelloWorkerRR (helloDR)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (helloCells)

variable {ι : Type} {Λ : Scc.Sem.Layout} (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid Λ)
  (exe : _root_.Executable) [Kraken.Executable.ValidLayout exe] (endPc : Int64) (kp : Nat) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isa)
  (cS : ι → WeakMem.Address) (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  {μ : Marks} (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
  (hK : ∀ w fs, (ms w fs).K = some abi)
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)

include hI hp hend hlab hμ hK in
/-- **Each record's segment**: the spawned child's run inside `XHF ∧ AbX μ lab` (`seg_childPPXc`'s obligations
with `AbObl.zObl_abX` and `AbObl.zXObl_abX`; `zObl_abX`'s region and slice facts from `d.ok` and
`ChildPrem.hm`). -/
theorem hsegF (w : ι) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ (fun w s c fs => ZHR exe kp s c fs ∧
        (XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs)) w s c fs)
      ((fun w s c fs => XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs) w)
      helloSrc (lbl w) (ms w) ((fun w => childPX exe endPc kp (lbl w) (ms w) (cS w)) w) (fun _ _ _ => False) :=
  Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childPPXc hp hend (hK w)
    (fun d ho hc hcS => ZObl.and
      (Spike.Lib.X64.HelloPh.XH.zObl_XHF
        (Spike.Lib.X64.HelloPh.XHNode.zObl_XH hcS
          (fun y k => hI.hkid _ _ _ _ _ _ y k) hI.hwc
          (Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zObl_placed_ok (d := d) ho hc.hv0 hc.hv1 hc.hv2 hc.hv hc.hvu))
        (Spike.Lib.X64.Flow.Worker.Hello.FlagObl.zObl_flag hcS))
      (let ⟨_, hR, hlo, hhi⟩ := ho
       Spike.Lib.X64.Flow.Worker.Hello.AbObl.zObl_abX hp hend hlab hμ hR (by omega) hhi hc.hm))
    (fun d _ hc hcS => ZXObl.and
      (ZXObl.and (Spike.Lib.X64.HelloPh.XHLand.zXObl_XH hc.hv hc.hvu)
        (Spike.Lib.X64.Flow.Worker.Hello.FlagR.zXObl_flag hcS))
      (Spike.Lib.X64.Flow.Worker.Hello.AbObl.zXObl_abX hp hend hlab hμ))

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
  (X64HelloWorkerRR.helloDR_X exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h).1

/-- **`helloDRF`'s abort facts**: every state of the invariant has `AbFacts μ (WriteAb.Ab lab)` (`helloDR_X`'s
second conjunct, `AbX`'s body). -/
theorem helloDRF_ab : ∀ w s c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w s c fs →
    X64HelloPostAb.AbFacts μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s :=
  fun w s c fs h => (X64HelloWorkerRR.helloDR_X exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h).2

/-- **The row `hplW` at `helloDRF`.** -/
theorem helloDRF_hplW : ∀ w st c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w st c fs →
    PlacedSE Λ (lbl w) st c fs :=
  Spike.Lib.X64.HelloPh.XH.hplW_ofF (fun w s c fs h => helloDRF_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ
    hK cw bufL nB mB w s c fs h)

/-- **The row `hcall` at `helloDRF`.** -/
theorem helloDRF_hcall : ∀ w st c,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w st c [] →
    ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (lbl w) st [⟨"u", workerRestH, c'.env, [], .unit⟩] :=
  Spike.Lib.X64.HelloPh.XH.hcall_ofF (fun w s c fs h => helloDRF_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ
    hK cw bufL nB mB w s c fs h)

/-- **The flag at `helloDRF`.** -/
theorem helloDRF_flag : ∀ w st c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w st c fs →
    FlagF (cS w) st c fs :=
  Spike.Lib.X64.HelloPh.XH.hflag_ofF (fun w s c fs h => helloDRF_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ
    hK cw bufL nB mB w s c fs h)

/-- **`helloDRF`'s invariant inside `NNH ∧ WideX ∧ Pend (ZHR exe kp)`**: the consumers of the segment fact
`Z := ZHR exe kp` read it through this projection. -/
theorem helloDRF_zhr : ∀ w s c fs,
    (helloDRF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc (ZHR exe kp) s c fs := fun w s c fs h =>
  have h' := X64HelloWorkerRR.helloDR_inv exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h
  ⟨h'.1, h'.2.1, h'.2.2.mono fun _ _ _ h => h.1⟩

/-! ## With a node-only fragment `Y`

The segment fact gains a fragment `Y w` kept at every node of the child's run (`seg_childPPXcY`), asked at no
landing; the landing fragment is unchanged. -/

section Y

variable (Y : ι → FragS isa)
  (hY : ∀ w (d : Spike.Lib.X64.Flow.Worker.Hello.SegR.ChildD), d.ok →
    Spike.Lib.X64.Flow.Worker.Hello.SegR.ChildPrem exe endPc kp (lbl w) (ms w) d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2
      d.w3 d.w4 d.n d.m → d.w3.val = .loc (cS w) 0 →
    ZObl (Y w) exe endPc (ms w) d.R d.F d.w d.tp d.sp0 d.T d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)

include hI hp hend hlab hμ hK hY in
/-- **Each record's segment with `Y`**: `hsegF`'s, the segment fact `ZHR ∧ Y w ∧ (XHF ∧ AbX μ lab)`
(`seg_childPPXcY`, `Y`'s obligations `hY`). -/
theorem hsegFY (w : ι) :
    SegTCSX (fun s c fs => NNH exe endPc s ∧ (fun w s c fs => ZHR exe kp s c fs ∧ Y w s c fs ∧
        (XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs)) w s c fs)
      ((fun w s c fs => XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs) w)
      helloSrc (lbl w) (ms w) ((fun w => childPX exe endPc kp (lbl w) (ms w) (cS w)) w) (fun _ _ _ => False) :=
  Spike.Lib.X64.Flow.Worker.Hello.SegRP.seg_childPPXcY hp hend (hK w) (hY w)
    (fun d ho hc hcS => ZObl.and
      (Spike.Lib.X64.HelloPh.XH.zObl_XHF
        (Spike.Lib.X64.HelloPh.XHNode.zObl_XH hcS
          (fun y k => hI.hkid _ _ _ _ _ _ y k) hI.hwc
          (Spike.Lib.X64.Flow.Worker.Hello.PlacedZ.zObl_placed_ok (d := d) ho hc.hv0 hc.hv1 hc.hv2 hc.hv hc.hvu))
        (Spike.Lib.X64.Flow.Worker.Hello.FlagObl.zObl_flag hcS))
      (let ⟨_, hR, hlo, hhi⟩ := ho
       Spike.Lib.X64.Flow.Worker.Hello.AbObl.zObl_abX hp hend hlab hμ hR (by omega) hhi hc.hm))
    (fun d _ hc hcS => ZXObl.and
      (ZXObl.and (Spike.Lib.X64.HelloPh.XHLand.zXObl_XH hc.hv hc.hvu)
        (Spike.Lib.X64.Flow.Worker.Hello.FlagR.zXObl_flag hcS))
      (Spike.Lib.X64.Flow.Worker.Hello.AbObl.zXObl_abX hp hend hlab hμ))

/-- **The worker's side with `Y`** (`helloDRF` at the segment fact `ZHR ∧ Y w ∧ (XHF ∧ AbX μ lab)`). -/
noncomputable abbrev helloDRFY : WSideH ι :=
  helloDR exe endPc SR lbl ms (fun w => childPX exe endPc kp (lbl w) (ms w) (cS w))
    (fun w s c fs => ZHR exe kp s c fs ∧ Y w s c fs ∧
      (XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs))
    (fun w s c fs => XHF Λ (lbl w) (cS w) s c fs ∧ AbX μ (_root_.Executable.labels exe).label s c fs) hK
    (hsegFY hI exe endPc kp lbl ms cS hp hend hlab hμ hK Y hY) cw bufL nB mB

set_option hygiene false in
local notation "DY" => helloDRFY hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB Y hY

/-- **`helloDRFY`'s invariant inside `XHF`.** -/
theorem helloDRFY_XHF : ∀ w s c fs, (DY).Wi w s c fs → XHF Λ (lbl w) (cS w) s c fs := fun w s c fs h =>
  (X64HelloWorkerRR.helloDR_X exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h).1

/-- **`helloDRFY`'s abort facts.** -/
theorem helloDRFY_ab : ∀ w s c fs, (DY).Wi w s c fs →
    X64HelloPostAb.AbFacts μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s :=
  fun w s c fs h => (X64HelloWorkerRR.helloDR_X exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h).2

/-- **The row `hplW` at `helloDRFY`.** -/
theorem helloDRFY_hplW : ∀ w st c fs, (DY).Wi w st c fs → PlacedSE Λ (lbl w) st c fs :=
  Spike.Lib.X64.HelloPh.XH.hplW_ofF (helloDRFY_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB Y hY)

/-- **The row `hcall` at `helloDRFY`.** -/
theorem helloDRFY_hcall : ∀ w st c, (DY).Wi w st c [] →
    ∀ c', LocalRunS helloSrc c c' → c'.term = workerCallH →
      FramesPlaced Λ (lbl w) st [⟨"u", workerRestH, c'.env, [], .unit⟩] :=
  Spike.Lib.X64.HelloPh.XH.hcall_ofF (helloDRFY_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB Y hY)

/-- **The flag at `helloDRFY`.** -/
theorem helloDRFY_flag : ∀ w st c fs, (DY).Wi w st c fs → FlagF (cS w) st c fs :=
  Spike.Lib.X64.HelloPh.XH.hflag_ofF (helloDRFY_XHF hI exe endPc kp SR lbl ms cS hp hend hlab hμ hK cw bufL nB mB Y hY)

/-- **`helloDRFY`'s invariant inside `NNH ∧ WideX ∧ Pend (ZHR exe kp)`.** -/
theorem helloDRFY_zhr : ∀ w s c fs, (DY).Wi w s c fs →
    NNH exe endPc s ∧ WideX exe s ∧ Pend helloSrc (ZHR exe kp) s c fs := fun w s c fs h =>
  have h' := X64HelloWorkerRR.helloDR_inv exe endPc SR lbl ms _ _ _ hK _ cw bufL nB mB w s c fs h
  ⟨h'.1, h'.2.1, h'.2.2.mono fun _ _ _ h => h.1⟩

end Y

end Spike.Lib.X64HelloWorkerRRXF

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.hsegF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.hsegF

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRF_hplW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRF_hplW

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRF_hcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRF_hcall

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRF_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRF_flag

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRF_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRF_ab

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRF_zhr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRF_zhr

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.hsegFY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.hsegFY

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRFY_hplW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRFY_hplW

/-- info: 'Spike.Lib.X64HelloWorkerRRXF.helloDRFY_zhr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRRXF.helloDRFY_zhr
