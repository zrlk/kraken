/-
**hello.w on AArch64: the `WakeObligations` assembly at the placed
instance** (the instance of `Spike.Lib.HelloAssembly.hello_obligations`, as
wake's `WakeQ` / `WakeAssembly.wake_obligations_RPD` instantiate
`wake_obligations`). The layout is the placed output's
(`L := RuntimeLayout.ofPlaceW hp i`), the records hello's root records
(`ι := {g : Gh // HelloOkHR.okHR L.Λ HelloOkW.lBH g}`), with the field
choices `SR w := wakeSR w.1`, `cS w := w.1.cS`, `cT w := w.1.cT`,
`pT w := w.1.pT`, the worker's pointer word `w.1.cwW` and main's `w.1.cwM`,
the buffer `lBH` of `13` bytes and `2` words, the value invariant
`G w := wakeG (G0 w) w.1.cT`, the ranges `r0 w := Dd.r0`, `r1 w := r1c`.
The worker side is `HelloW1Store.helloDH` (segment `hseg`), main's
side `HelloMainInv.helloM` at the target's marks (`HelloCompatI.μP`), and
the relation `HelloW1Store.QIH`.

Closed here: `HelloCompat` (`HelloCompatI.hC_IP`,
`HelloW1Store.wcompat_relW_IR` with the spawn rows of `HelloRootRows`,
`HelloSpos.sposH` and `HelloLive.mainLiveH`, `HelloWorkerRR.hx_IR`,
`HelloMs.hC0Ms`); `hwf` (`WakeQ.hwf_ofPlaceOK`); `hstart`
(`WakeHStart.hstart_of_loadOk` from the loader's data parse and `E.clear`);
`spawn` (`HelloSpawnR.spawn_RH` with `HelloHPre.hpre_ofH` and
`HelloRec.hrec_okHRc`).

Open, each an explicit hypothesis carrying its row (`row:` tag):
the pre-spawn half `O` and its relation `hR1`, the clone's facts `hCl`,
the data's guarantee below the records' `hG`, the target store point
`pass`, the store phase's control facts `hZ`, main's invariant past the
clone `hMainR`, the child's entry `hWi`, the worker's halting and mapped
facts at its system calls and instructions `hhalt1`, `hmapW` (progress's
worker half), and `HelloRowsW` (`HelloRows` without main's step, row
the worker's unpark, progress, and the
steps' keeping `CertAll`, which `HelloM0Post.post_step0H`,
`HelloUnpk.unpark_srcH`, `HelloProgress.post_progressH` (main's halting and
mapped facts from `HelloMainInv.mainInvP_W`, `WakeMappedRow.hM_of`) and
`HelloCert.cert_stepH` (from `HelloRowsW.hconv`) prove).

main's side here is `helloM` at `μP` (as `HelloMs.hC0Ms` reads it), while
`HelloMainG.hMainRH_ofG` proves `HMainRH` at `HelloMainG.helloMI`
(`PhRec.μ L`, `Gm`); the two marks agree only propositionally
(`A64.Flow.Worker.Wake.AbOffW.marks_target`), so `hMainR` stays a premise.

- `LH`, `ιH`, `endH`, `SRH`, `GH`, `PaH`, `μH`, `DH`, `MH`, `QH`: the
  instance's data.
- `hello_obligations_I`: the assembly at the instance.
-/
import Spike.Lib.HelloAssembly
import Spike.Lib.HelloRec
import Spike.Lib.HelloRootRows
import Spike.Lib.HelloSpos
import Spike.Lib.HelloLive
import Spike.Lib.HelloMs
import Spike.Lib.WakeQ
import Spike.Lib.WakeHStart
import Spike.Lib.HelloM0Post
import Spike.Lib.HelloUnpk
import Spike.Lib.HelloCert
import Spike.Lib.HelloProgress

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Inv2Core Spike.Lib.WakeInst
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloW1Store (helloDH QIH ZStoreOk noWrite_IR)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.HelloInst (helloP)
open Spike.Lib.HelloMs (msH helloLocs)
open Spike.Lib.HelloMsW (msWH)
open Spike.Lib.HelloMainInv (helloM)
open Spike.Lib.HelloOkHR (okHR)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.HelloSpawnR (HMainRH HWiH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloAssembly (HelloCompat HelloRows HelloRowsW hello_obligations)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (endOf)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The placed runtime layout. -/
abbrev LH : RuntimeLayout := RuntimeLayout.ofPlaceW hp i

/-- hello's root records at the placed layout. -/
abbrev ιH : Type := {g : Gh // okHR (LH hp i).Λ lBH g}

/-- Where a thread running hello's text halts. -/
abbrev endH : Int64 := endOf (LH hp i).exe helloProg (LH hp i).pfx

/-- The record's spawn data. -/
abbrev SRH (w : ιH hp i) : SpawnRec := wakeSR w.1

/-- The record's value invariant: `G0 w`, the flag's target word `cT`
taking `1`. -/
abbrev GH (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) : Loc → Val → Prop := WakeG.wakeG (G0 w) w.1.cT

/-- The target's marks at the placed layout. -/
noncomputable abbrev μH (E : Entry) (asm : String) : Marks := HelloCompatI.μP hp i (kernel 2) E asm

/-- The record's location data. -/
noncomputable abbrev PaH (E : Entry) (asm : String) (w : ιH hp i) : Inv2Params isaLSE2 :=
  helloP abi (μH hp i E asm) (helloLocs (LH hp i) (SRH hp i w).lbl (SRH hp i w).lsize w.1.cT w.1.cS)

variable /- row: root (the records' value invariant below `wakeG`) -/ (G0 : ιH hp i → Loc → Val → Prop)
  (P Z X : ιH hp i → FragS isaLSE2)
  /- row: 5j-misc (`A64.Flow.Worker.Hello.Wk.seg_wcWorkerS` composed with
  the tail, at `HelloWorkerCallSrc`'s `Pr`/`Kc` and the concrete `Z`) -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False))

/-- The worker's side: `helloDH` at the record's pointer word and hello's
buffer (`lBH`, `13` bytes, `2` words). -/
noncomputable abbrev DH : WSideH (ιH hp i) :=
  helloDH (LH hp i).exe (endH hp i) (LH hp i) (GH hp i G0) (SRH hp i) P Z X hseg (fun w => w.1.cwW) (fun _ => lBH)
    (fun _ => 13) (fun _ => 2)

/-- main's side: `helloM` at the target's marks (`HelloMs.hC0Ms`'). -/
noncomputable abbrev MH (E : Entry) {asm : String} (hpa : textProgram asm = .ok o.prog) : WakeM0.MSide (ιH hp i) :=
  helloM (fun w => (SRH hp i w).lbl) (fun w => (SRH hp i w).lsize) (msH (LH hp i) (GH hp i G0) (SRH hp i))
    (fun w => w.1.cwM) (LH hp i).lab (LH hp i).exe (LH hp i).Λ (μH hp i E asm) (HelloCompatI.hoffP hp i hpa)

/-- **The relation at the instance** (`QIH`). -/
noncomputable abbrev QH (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (E : Entry) {asm : String}
    (hpa : textProgram asm = .ok o.prog) (passT : State → Prop) (Dd : ODataH) (r1c : Range) : WakeRel :=
  QIH (LH hp i).exe (endH hp i) (LH hp i) (GH hp i G0) (SRH hp i) P Z X hseg (fun w => w.1.cwW) (fun _ => lBH)
    (fun _ => 13) (fun _ => 2) (fun w => w.1.cT) (fun w => w.1.cS) (arch := arch) (R1 := R1)
    (μ := μH hp i E asm) (pT := fun w => w.1.pT) (passT := passT) (M := MH hp i G0 E hpa)
    (r0 := fun _ => Dd.r0) (r1 := fun _ => r1c)

/-- The worker's pointer word is a locative to `cS` (`HelloRootRows.cwv_okHR`). -/
theorem cwvH : ∀ w : ιH hp i, (w.1.cwW).val = .loc w.1.cS 0 :=
  HelloRootRows.cwv_okHR (cS := fun w => w.1.cS) (cw := fun w => w.1.cwW) (fun _ => rfl) (fun _ => rfl)

/-- `HelloCompat`'s `hcw` at the instance. -/
theorem hcwH : ∀ w, ∃ cS, ((DH hp i G0 P Z X hseg).cw w).val = .loc cS 0 := fun w => ⟨w.1.cS, cwvH hp i w⟩

/-- `HelloCompat`'s `hem` at the instance (`HelloW1Store.noWrite_IR`). -/
theorem hemH (hZ : ZStoreOk (LH hp i).exe Z) : HelloW1Store.NoWrite (DH hp i G0 P Z X hseg) :=
  noWrite_IR (LH hp i).exe (endH hp i) (SRH hp i) (fun w => (SRH hp i w).lbl)
    (fun w _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) P Z X (fun _ _ => rfl)
      hseg (fun w => w.1.cwW)
    (fun _ => lBH) (fun _ => 13) (fun _ => 2) (hcwH hp i G0 P Z X hseg) hZ

/-- **The assembly at the placed instance** (see the module doc). -/
theorem hello_obligations_I {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {passT : State → Prop} {Dd : ODataH} {r1c : Range}
    {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
    /- the loader's parses (the trust boundary): the listing's program is the
    placed output's and hello's, its data sections the output's -/
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hd : dataSections asm = some o.secs)
    /- row: 5j-start. The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- (row 1's `hbuf` in `R1`). The pre-spawn half. -/
    (O : Pre1T arch (LH hp i).Λ B asm E R1 Ab Ac helloSrc)
    /- `R1` is the pre-spawn relation with its source
    conjuncts (`HelloHPre.hpre_ofH`'s `hR1`). -/
    (hR1 : ∀ d s, R1 d s → R1OH arch (LH hp i).Λ (μH hp i E asm) Dd XH d s)
    /- row: 5j-hCl. The clone's facts at the pre-spawn segment's end
    (`hpre_ofH`'s `hCl`). -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      A64Consumer.HeldOk2 (LH hp i).Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH ".L22_wc_main" (LH hp i).Λ Dd.r0 r1c X lbl d s)
    /- row: root. The data's guarantee is below every record's. -/
    (hG : ∀ w m, MemInv Dd.G m → MemInv (GH hp i G0 w) m)
    /- (the record's park permit word at the clone; any) -/ (pT0 : Loc)
    /- row: 5j-k. The target store point (`WCompatH.pass`). -/
    (pass : HelloW1.PassH (DH hp i G0 P Z X hseg) passT)
    /- row: 5j-ZS. The store phase's pc facts on the segment's `Z`. -/
    (hZ : ZStoreOk (LH hp i).exe Z)
    /- row: 5j-segEnd (`HelloMainG.hMainRH_ofG` proves it at `helloMI`,
    `PhRec.μ L`, see the module doc). main's invariant past the clone. -/
    (hMainR : HMainRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg) (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E
      (HelloHPre.FrH Dd))
    /- row: 5j-misc. The child in the worker side's invariant. -/
    (hWi : HWiH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg) (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E
      (HelloHPre.FrH Dd))
    /- The worker's states run at a system call
    (`WakeAssembly`'s `hhalt1`). -/
    (hhalt1 : ∀ w s c fs, (DH hp i G0 P Z X hseg).Wi w s c fs → abi.atSys s = true → (isaLSE2.exec s).isSome)
    /- The worker's instructions touch only
    locations mapped in `K0` (`WakeAssembly`'s `hmapW`). -/
    (hmapW : ∀ w s c fs, (DH hp i G0 P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isaLSE2.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (A64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- 5i, 5j-wit; see
    `HelloRowsW`' fields. -/
    (R : HelloRowsW arch (LH hp i).Λ B asm (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) E
      (DH hp i G0 P Z X hseg) (MH hp i G0 E hpa) (AbW (LH hp i).exe) (hcwH hp i G0 P Z X hseg)
      (hemH hp i G0 P Z X hseg hZ) Ab Ac Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) E
      (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc :=
  haveI := (LH hp i).valid
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  have hwf := WakeQ.hwf_ofPlaceOK hp i
  have hC : HelloCompat (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (DH hp i G0 P Z X hseg) (MH hp i G0 E hpa)
      ((target (kernel 2) E).marks asm (LH hp i).Λ) (LH hp i).Λ arch (AbW (LH hp i).exe) (hcwH hp i G0 P Z X hseg)
      (hemH hp i G0 P Z X hseg hZ) :=
    ⟨HelloCompatI.hC_IP hp i (endH hp i) (SRH hp i) (fun w => (SRH hp i w).lbl)
        (fun w _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) P Z X (fun _ _ => rfl)
        hseg (fun w => w.1.cwW)
        (fun _ => lBH) (fun _ => 13) (fun _ => 2) ho hpa rfl (cwvH hp i) pass,
      HelloW1Store.wcompat_relW_IR (LH hp i).exe (endH hp i) (LH hp i) (GH hp i G0) (SRH hp i) P Z X hseg
        (fun w => w.1.cwW) (fun _ => lBH) (fun _ => 13) (fun _ => 2) (fun w => w.1.cT) (fun w => w.1.cS) hl rfl
        (HelloCompatI.hello_hμP hp i ho hpa) (cwvH hp i) pass hZ
        (HelloRootRows.cT_okHR (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
        (HelloRootRows.cTin_okHR (fun _ => rfl)) HelloRootRows.cTfoot_okHR HelloRootRows.cSfrz_okHR
        HelloSpos.sposH HelloRootRows.footLab_okHR HelloLive.mainLiveH,
      HelloWorkerRR.hx_IR (HelloRootRows.Gc_okHR (fun _ => rfl)),
      HelloMs.hC0Ms hp i hpa
        (HelloRootRows.hcw_okHR (cS := fun w => w.1.cS) (cw := fun w => w.1.cwM) (fun _ => rfl) (fun _ => rfl))⟩
  have hpre := HelloHPre.hpre_ofH (SR := SRH hp i) (cT := fun w => w.1.cT) (cS := fun w => w.1.cS)
    (pT := fun w => w.1.pT) (Pa := PaH hp i E asm) (G := GH hp i G0) (passT := passT) (M := MH hp i G0 E hpa)
    (D := DH hp i G0 P Z X hseg) (r0 := fun _ => Dd.r0) (r1 := fun _ => r1c) (asm := asm) (E := E)
    hR1 (fun _ => rfl) (fun _ => rfl) hwf hCl
    (HelloRec.hrec_okHRc pT0 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hG hwf) (fun _ => rfl)
  hello_obligations hwf rfl rfl hC
    (WakeHStart.hstart_of_loadOk hpa hd (PlaceW.loadOk_link_of_placeW i hp) hE) O
    (HelloSpawnR.spawn_RH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT)
      (PaH hp i E asm) (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg) (fun _ => Dd.r0)
      (fun _ => r1c) (LH hp i).Λ asm E (HelloHPre.FrH Dd) (fun _ => WakeP.wakeP_frz_cov)
      (fun w => WakeP.wakeP_foot_cov (HelloMs.helloLocs_ok (LH hp i) _ _ _ _)) pass hpre hMainR hWi)
    { R with post_step0 := HelloM0.post_step0H rfl rfl rfl hwf rfl, unpark_src := HelloUnpk.unpark_srcH hwf rfl
             post_progress := fun hC => HelloProgress.post_progressH rfl rfl hC (fun _ _ => rfl)
               (MH hp i G0 E hpa).off (fun _ s c h _ => (HelloMainInv.mainInvP_W s c h).2.1.1) hhalt1
               (WakeMappedRow.hM_of (fun _ => rfl) (fun _ _ _ h => h.1)
                 (fun _ s c h => (HelloMainInv.mainInvP_W s c h).2.2.1)) hmapW
             cert_step := fun hC => HelloCert.cert_stepH rfl rfl hC (R.hconv hC) }
    (PlaceW.link i hp) hpa

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.hello_obligations_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.hello_obligations_I
