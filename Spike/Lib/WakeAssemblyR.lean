/-
**wake.w on AArch64: the assembly at the instance, per record**: `WakeWorkerR.wake_obligations_IWR` at wake's certificate
(`asm := SccCertificate.asm`, `E := Entry.linux`, the listing `wakeProg`),
the placed output's runtime layout `L := RuntimeLayout.ofPlaceW hp i`, the
records satisfying `ok := WakeInstFields.GhOK L.Λ`, main's labels `L.lab`
and the worker's side `D := WakeWorkerR.wakeDR` at `L.exe`, its end and
prefix. Discharged here:

- `hoff` (`hoffR`): `A64AbOffL.off_of_A_ofPlaceOK` at the target's marks
  (`AbOffW.marks_target`);
- `hC` by `WakeWorkerR.hC_IR` (`hμ` by `WorkerSide.wake_hμ`, `Lays` by
  `L.lays`), `hx` by `hx_IR`, `hW` by `hW_IR`, `hmp` by `hmp_IR`, `hSR` and
  `hend` by `rfl`;
- `hC0` (`hC0R`): every field of `WakeM0.WCompat0` by its `WakeInst` /
  `WakeInstFields` theorem (`noSite0`, `abortAt0` at the target's marks by
  `marks_target`; `cw0` from `GhOK`);
- `hstart` by `WakeHStart.hstart_linux`; `hpl` by `hp` (the layout's link is
  `placeOKAt`'s, `po := o`).

**Open**: `O` (the pre-spawn half) and `spawn`. **The trust boundary** (the loader's parses of the
certificate, as `hpa` before): `hpa` (its text is the output's program),
`hwp` (and `wakeProg`), `hd` (its data sections the output's).
-/
import Spike.Lib.WakeWorkerR
import Spike.Lib.WakeHStart
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeAssemblyR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakePreTi Spike.Lib.Handover
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeInst (Gh wakeM)
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (endOf)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The certificate's marks at the placed layout. -/
noncomputable abbrev μR : Marks :=
  (target (kernel 2) Entry.linux).marks SccCertificate.asm (RuntimeLayout.ofPlaceW hp i).Λ

/-- **`hoff` at the instance**: a state off the abort exits of the layout's
labels is off every abort site of the certificate's marks. -/
theorem hoffR (hpa : textProgram SccCertificate.asm = .ok o.prog) :
    ∀ s c, Spike.Lib.A64WakeOff.AbOffA (RuntimeLayout.ofPlaceW hp i).lab s c →
      ∀ k a, (μR hp i).abortAt k = some a → pcOf s ≠ a := by
  intro s c h
  rw [μR, Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
  exact Spike.Lib.A64AbOffL.off_of_A_ofPlaceOK hp i h

/-- **main's side at the instance**: at the layout's labels and the
certificate's marks, over the records satisfying `GhOK`. -/
noncomputable abbrev MR (hpa : textProgram SccCertificate.asm = .ok o.prog) :
    WakeM0.MSide {g : Gh // GhOK (RuntimeLayout.ofPlaceW hp i).Λ g} :=
  wakeM hp i (GhOK (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).lab (μR hp i) (hoffR hp i hpa)

/-- **The instance's relation**: `WakeWorkerR.QIR` at the layout's
executable, its end and prefix, the certificate's marks and `MR`. -/
noncomputable abbrev QR (hpa : textProgram SccCertificate.asm = .ok o.prog) (arch : WeakMem.Arch)
    (R1 : Cfg → TermRun.Cfg → Prop)
    (r0 r1 : {g : Gh // GhOK (RuntimeLayout.ofPlaceW hp i).Λ g} → Range) : WakeRel :=
  WakeWorkerR.QIR hp i (GhOK (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).exe
    (endOf (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx)
    (RuntimeLayout.ofPlaceW hp i).pfx arch R1 (μR hp i) (MR hp i hpa) r0 r1

/-- **`hC0` at the instance**: `WakeM0.WCompat0` field by field. -/
theorem hC0R (hpa : textProgram SccCertificate.asm = .ok o.prog) {arch : WeakMem.Arch}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : {g : Gh // GhOK (RuntimeLayout.ofPlaceW hp i).Λ g} → Range} :
    WakeM0.WCompat0 (QR hp i hpa arch R1 r0 r1) (MR hp i hpa) (μR hp i) (RuntimeLayout.ofPlaceW hp i).Λ where
  lbl0 := WakeInst.lbl0_I hp i
  K0 := WakeInst.K0_I hp i
  G0 := WakeInst.G0_I hp i
  own0 := WakeInst.own0_I hp i
  mpW0 := WakeInst.mpW0_I hp i
  wide0 := WakeInstFields.wide0_I hp i
  noSite0 := by
    rw [μR, Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa]
    exact WakeInst.noSite0_I hp i rfl
  sysExec0 := WakeInstFields.sysExec0_I hp i
  noWrite0 := WakeInst.noWrite0_I hp i
  cw0 := WakeInstFields.cw0_I hp i fun _ h => h
  live0 := WakeInst.live0_I hp i
  flagLd := WakeInst.flagLd_I hp i
  noProm0 := WakeInstFields.noProm0_I hp i
  rd1 := WakeInstFields.rd1_I hp i
  abortAt0 := WakeInstFields.abortAt0_I hp i hpa
  relW0 := WakeInst.relW0_I hp i

/-- **The assembly at the instance, per record** (see the module doc):
`WakeObligations` at the certificate, the placed layout and `QR`; open the
pre-spawn half `O` and the spawn obligation `spawn`, over the loader's parses
`hpa`, `hwp`, `hd`.

**Superseded** by `WakeSpawnR.wake_obligations_RE` (generic in the entry
`E`, the form `WakeFinalCA.wake_finalCA_gen` consumes); kept for its
existing users, new consumers should take the `RE` form. -/
theorem wake_obligations_R {Ab Ac : State → Prop} {arch : WeakMem.Arch} {B : Budget}
    {R1 : Cfg → TermRun.Cfg → Prop} {r0 r1 : {g : Gh // GhOK (RuntimeLayout.ofPlaceW hp i).Λ g} → Range}
    /- the loader's parses of the certificate (the trust boundary) -/
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs)
    /- OPEN -/
    (O : Pre1T arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm Entry.linux R1 Ab Ac)
    /- OPEN -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 (μR hp i) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (QR hp i hpa arch R1 r0 r1).Post (RuntimeLayout.ofPlaceW hp i).Λ (afterClone abi d tid th stack tls r) s') :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B SccCertificate.asm (QR hp i hpa arch R1 r0 r1)
      Entry.linux (TiPre Ab Ac) := by
  have ho : o.prog = wakeProg := Except.ok.inj (hpa.symm.trans hwp)
  have hl : Scc.Cert.Rt.A64.Lays (RuntimeLayout.ofPlaceW hp i).exe wakeProg (RuntimeLayout.ofPlaceW hp i).pfx := by
    rw [← ho]; exact (RuntimeLayout.ofPlaceW hp i).lays
  have hlo : Scc.Cert.Link.A64.loadOk (RuntimeLayout.ofPlaceW hp i).Λ wakeProg o.secs = true := by
    rw [← ho]; exact PlaceW.loadOk_link_of_placeW i hp
  have hμ := WorkerSide.wake_hμ (H := kernel 2) (E := Entry.linux) hwp hlo
  rw [← ho] at hμ
  exact WakeWorkerR.wake_obligations_IWR hp i (hoffR hp i hpa)
    (WakeWorkerR.hC_IR hp i _ _ _ _ (fun _ h => h) hl rfl hμ) (WakeWorkerR.hx_IR hp i _ _ _ _)
    (hC0R hp i hpa) (WakeHStart.hstart_linux (Λ := (RuntimeLayout.ofPlaceW hp i).Λ) (PlaceW.link i hp) hpa hd) O spawn rfl
    (WakeWorkerR.hW_IR hp i _ _ _ _) (fun _ => rfl) (WakeWorkerR.hmp_IR hp i _ _ _ _) (pcfg' := pcfg) (PlaceW.link i hp) hpa

/-- info: 'Spike.Lib.WakeAssemblyR.hC0R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC0R

/-- info: 'Spike.Lib.WakeAssemblyR.wake_obligations_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_obligations_R

end Spike.Lib.WakeAssemblyR
