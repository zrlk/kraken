/-
**wake.w on x86-64: the assembly at the instance, per record** (in the
manner of `Spike/Lib/WakeAssemblyR.lean`): `X64WakeWorkerR.wake_obligations_IWR`
at a certificate `asm` whose text parses to the listing `wakeCells`
(`E := Entry.linux`), the placed output's runtime layout
`L := RuntimeLayout.ofPlaceWX hp i`, the records satisfying
`ok := GhOKR L` (`GhOK L.Λ` and `SelfOK`), main's labels `L.lab`, the TCB words
`T := tcbM L`, `W := tcb2 L` and the worker's side `D := X64WakeWorkerR.wakeDR`
at `L.exe`, its end and prefix. Discharged here:

- `hoff` (`hoffR`): `X64AbOffL.off_of_A_ofPlaceOK` at the target's marks
  (`AbOffW.marks_target`);
- `hC` by `X64WakeWorkerR.hC_IRX` (`hok`, `hself` from `GhOKR`; the marks
  `PhRec.μ L` by `marks_target`,
  `Lays` by `L.lays`, `hTW` by `WakePh.tcb2_ne_tcbM`), `hx` by `hx_IR`, `hW`
  by `hW_IR`, `hmp` by `hmp_IR`, `hSR` and `hend` by `rfl`;
- `hC0` (`hC0R`): every field of `X64WakeM0.WCompat0` by its `X64WakeInst` /
  `X64WakeInstFields` / `X64WakeInstFlag` theorem (`noSite0`, `abortAt0` at
  the target's marks by `marks_target`; `cw0` from `GhOK`);
- `hstart` by `X64WakeHStart.hstart_linux`; `hpl` by `hp` (the layout's
  link, `po := o`).

**Open**: `O` (the pre-spawn half) and `spawn` (which constructs the
clone's record, so its `SelfOK` too). **The trust boundary** (the loader's parses of
the certificate): `hpa` (its text is the output's program), `hwp` (and
`wakeCells`), `hd` (its data sections the output's), `hoffs` (its label
offsets the output's). Only `hpa` (with the budget) stays a premise of the
final theorem, as on AArch64: `hwp`, `hd` and `hoffs` are discharged at
the final/root tier at the concrete certificate (by `decide`/`rfl` on its
parse, or from `hpa`) (X64-trust-params).

**Unlike AArch64** (forced by the x64 shape):
- The certificate is a parameter `asm` with its parses (`hpa`, `hwp`, `hd`,
  `hoffs`), not a fixed `SccCertificate.asm`; x86-64's start also reads the
  label offsets (`hoffs`).
- The relation carries the TCB words `tcbM L`, `tcb2 L` and the store point
  `wakePassT`; the records are `GhOKR` (`SelfOK` with `GhOK`), so `hC`'s
  `hself` is closed here, as is `hTW`.
- `hC` is at the runtime's marks (`hC_IRX`), so needs no `wake_hμ`.
- `WCompat0` has the owned-word fields `ownConst0`, `ownMp0`, `ownCov0`
  (main owns its TCB word).
-/
import Spike.Lib.X64WakeWorkerR
import Spike.Lib.X64WakeHStart
import Spike.Lib.X64WakeInstFlag
import Spike.Lib.X64AbOffL
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeAssemblyR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeW1 Spike.Lib.X64WakePreTi Spike.Lib.Handover
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeInst (Gh wakeM)
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64.WakePh (tcbM tcb2)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (endOf)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (asm : Asm)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- The certificate's marks at the placed layout. -/
noncomputable abbrev μR : Marks :=
  (target (kernel 2) Entry.linux).marks asm (Ly).Λ

/-- **The certificate's marks are the runtime's** (`AbOffW.marks_target`). -/
theorem μR_eq (hpa : cellsOf asm = some o.prog) : μR hp i asm = Spike.Lib.X64.PhRec.μ (Ly) :=
  Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa

/-- **`hoff` at the instance**: a state off the abort exits of the layout's
labels is off every abort site of the certificate's marks. -/
theorem hoffR (hpa : cellsOf asm = some o.prog) :
    ∀ s c, Spike.Lib.X64WakeOff.AbOffA (Ly).lab s c →
      ∀ k a, (μR hp i asm).abortAt k = some a → pcOf s ≠ a := by
  intro s c h
  rw [μR_eq hp i asm hpa]
  exact Spike.Lib.X64AbOffL.off_of_A_ofPlaceOK hp i h

/-- **The records at the layout**: `GhOK L.Λ` together with the self
words' separation `SelfOK (tcbM L) (tcb2 L)` (X64-SelfOK: per record at its
construction, by `X64WakeSpawnR.selfOK_placed` from the spawn's memory
relation).

**Unlike AArch64**: A64's records are `GhOK` alone; the x64 relation's
owned TCB words need `SelfOK` for every record (`hC`'s `footLab`), which no
`GhOK` record satisfies in general (its labels are arbitrary). -/
def GhOKR (L : RuntimeLayout) (g : Gh) : Prop :=
  GhOK L.Λ g ∧ Spike.Lib.X64WakeInst.SelfOK (tcbM L) (tcb2 L) g

/-- **main's side at the instance**: at the layout's labels and the
certificate's marks, over the records satisfying `GhOKR`, the TCB words
`tcbM L`, `tcb2 L`. -/
noncomputable abbrev MR (hpa : cellsOf asm = some o.prog) :
    X64WakeM0.MSide {g : Gh // GhOKR (Ly) g} :=
  wakeM hp i (tcbM (Ly)) (tcb2 (Ly)) (GhOKR (Ly)) (Ly).lab (μR hp i asm) (hoffR hp i asm hpa)

/-- The layout's end of text. -/
abbrev endR : Int64 := endOf (Ly).exe wakeCells (Ly).pfx

/-- **The instance's relation**: `X64WakeWorkerR.QIR` at the layout's
executable, its end and prefix, the certificate's marks, `MR` and the store
point `wakePassT`. -/
noncomputable abbrev QR (hpa : cellsOf asm = some o.prog) (arch : WeakMem.Arch)
    (R1 : Cfg → TermRun.Cfg → Prop) (r0 r1 : {g : Gh // GhOKR (Ly) g} → Range) : WakeRel :=
  X64WakeWorkerR.QIR hp i (tcbM (Ly)) (tcb2 (Ly)) (GhOKR (Ly)) (Ly).exe (endR hp i) (Ly).pfx arch R1
    (μR hp i asm) (MR hp i asm hpa) r0 r1 Spike.Lib.X64.Flow.Worker.Wake.Pass.wakePassT

/-- **`hC0` at the instance**: `X64WakeM0.WCompat0` field by field. -/
theorem hC0R (hpa : cellsOf asm = some o.prog) {arch : WeakMem.Arch}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : {g : Gh // GhOKR (Ly) g} → Range} :
    X64WakeM0.WCompat0 (QR hp i asm hpa arch R1 r0 r1) (MR hp i asm hpa) (μR hp i asm) (Ly).Λ where
  lbl0 := X64WakeInst.lbl0_I hp i _ _
  K0 := X64WakeInst.K0_I hp i _ _
  G0 := X64WakeInst.G0_I hp i _ _
  own0 := X64WakeInst.own0_I hp i _ _
  ownConst0 := X64WakeInst.ownConst0_I hp i _ _
  ownMp0 := X64WakeInst.ownMp0_I hp i _ _
  ownCov0 := X64WakeInst.ownCov0_I hp i _ _
  mpW0 := X64WakeInst.mpW0_I hp i _ _
  wide0 := X64WakeInst.wide0_I hp i _ _
  noSite0 := by
    rw [μR_eq hp i asm hpa]
    exact X64WakeInst.noSite0_I hp i _ _ rfl
  sysExec0 := X64WakeInstFields.sysExec0_I hp i _ _
  noWrite0 := X64WakeInst.noWrite0_I hp i _ _
  cw0 := X64WakeInstFields.cw0_I hp i _ _ fun _ h => h.1
  live0 := X64WakeInst.live0_I hp i _ _
  flagLd := X64WakeInst.flagLd_I hp i _ _
  noProm0 := X64WakeInstFields.noProm0_I hp i _ _
  rd1 := X64WakeInstFields.rd1_I hp i _ _
  abortAt0 := X64WakeInstFields.abortAt0_I hp i _ _ hpa
  relW0 := X64WakeInst.relW0_I hp i _ _

/-- **The assembly at the instance, per record** (see the module doc):
`WakeObligations` at the certificate, the placed layout and `QR`; open the
pre-spawn half `O` and the spawn obligation `spawn`, over the loader's parses `hpa`, `hwp`, `hd`, `hoffs`. -/
theorem wake_obligations_R {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : {g : Gh // GhOKR (Ly) g} → Range}
    /- the loader's parses of the certificate (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- OPEN -/
    (O : Pre1T arch (Ly).Λ B asm Entry.linux R1 Ab Ac)
    /- OPEN -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso (μR hp i asm) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (QR hp i asm hpa arch R1 r0 r1).Post (Ly).Λ (afterClone abi d tid th stack tls r) s') :
    WakeObligations arch (Ly).Λ B asm (QR hp i asm hpa arch R1 r0 r1) Entry.linux (TiPre Ab Ac) := by
  have ho : o.prog = wakeCells := Option.some.inj (hpa.symm.trans hwp)
  have hl : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := by
    rw [← ho]; exact (Ly).lays
  have hTW : (⟨tcbM (Ly), 8⟩ : Loc) ≠ ⟨tcb2 (Ly), 8⟩ := fun h =>
    Spike.Lib.X64.WakePh.tcb2_ne_tcbM (Ly) (congrArg Loc.addr h).symm
  exact X64WakeWorkerR.wake_obligations_IWR hp i (hoffR hp i asm hpa)
    (X64WakeWorkerR.hC_IRX hp i _ _ _ _ _ (fun _ h => h.1) (fun w => w.2.2) hTW hl rfl (μR_eq hp i asm hpa))
    (X64WakeWorkerR.hx_IR hp i _ _ _ _ _ _)
    (hC0R hp i asm hpa)
    (X64WakeHStart.hstart_linux (Λ := (Ly).Λ) (PlaceWX.link i hp) hpa hd hoffs) O spawn rfl
    (X64WakeWorkerR.hW_IR hp i _ _ _ _ _ _) (fun _ => rfl) (X64WakeWorkerR.hmp_IR hp i _ _ _ _ _ _)
    (pcfg' := pcfg) (PlaceWX.link i hp) hpa

/-- info: 'Spike.Lib.X64WakeAssemblyR.hC0R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC0R

/-- info: 'Spike.Lib.X64WakeAssemblyR.wake_obligations_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_R

end Spike.Lib.X64WakeAssemblyR
