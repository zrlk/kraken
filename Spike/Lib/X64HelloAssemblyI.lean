/-
**hello.w on x86-64: the `WakeObligations` assembly at the placed
instance** (the twin of `Spike/Lib/HelloAssemblyI.lean`; the instance of
`Spike.Lib.X64HelloAssembly.hello_obligations`). The layout is the placed
output's (`L := RuntimeLayout.ofPlaceWX hp i`), the records hello's root
records (`ι := {g : Gh // X64HelloOkHR.okHR L.Λ X64HelloOkW.lBH (tcbM L) (tcbWH L) g}`), with
the field choices `SR w := wakeSR w.1`, `cS w := w.1.cS`, `cT w := w.1.cT`,
`pT w := w.1.pT`, the worker's pointer word `w.1.cwW` and main's `w.1.cwM`,
the buffer `lBH` of `13` bytes and `2` words, the value invariant
`G w := wakeG (G0 w) w.1.cT`, the ranges `r0 w := Dd.r0`, `r1 w := r1c`.
The worker side is `X64HelloW1Store.helloDH` (the segment `hseg`) on the worker's
owning memory side `X64HelloOwnLift.msWHX`, main's side `X64HelloMainInv.helloM` at the target's marks
(`X64HelloCompatI.μP`) on main's owning memory side `X64HelloMs.msHX`, and the relation
`X64HelloW1Store.QIH`, whose owned words are wake's self words `wakeOwnXW (tcbM L) (tcbWH L)` (`own_QH`).

Closed here: `HelloCompat` (`X64HelloCompatI.hC_IP` with the worker's word covered by
`X64HelloMs.ownCov1_H` and disjoint from main's by `tcbM_ne_tcbWH`,
`X64HelloW1Store.wcompat_relW_IR` with the spawn rows of `X64HelloRootRows`,
`X64HelloSpos.sposH` and `X64HelloLive.mainLiveH`, `X64HelloWorkerRR.hx_IR` (the worker's word constant and
never a runtime write's, `X64WakeOwnX.ownMpXW`), `X64HelloMs.hC0Ms`); `hwf` (`X64WakeQ.hwf_ofPlaceOK`); `hstart`
(`X64WakeHStart.hstart_of_loadOk` from the loader's data parse, its label
offsets and `E.clear`); `spawn` (`X64HelloSpawnR.spawn_RH` at `own_QH`, each self word in its thread's cover
set, with `X64HelloHPre.hpre_ofH` and `X64HelloRec.hrec_okHRc`, the record's `SelfOK` by
`X64HelloSelfOK.selfOK_placedH` from the pinned region's reach `hpin2`; `hpre_ofH`'s `hself` by
`X64HelloHPre.wakeOwnXW_inj_at` at `own_QH`, the labels by `X64HelloOInit.hlab_H` at `hlo`, and `hDd`, `hexe`).

Open, each an explicit hypothesis: the pre-spawn half `O` and its relation
`hR1`, the clone's facts `hCl`, the data's guarantee below the records'
`hG`, the target store point `pass`, the store phase's control facts `hZ`,
main's invariant past the clone `hMainR`, the child's entry `hWi`, the
store phase's writes off the worker's self word `hZW` (discharged at `AssemblyRS` by the worker fragment's
`OwnW (tcbWH)` conjunct, in progress; it does not follow from `Z`), the data's own map `hDd` (`rfl` at the
root's data, discharged in the root's invariant), main's thread at the clone on the layout's executable `hexe`
(from the pre-spawn fragment, as `X64HelloXOk.hX_ofR`), the
worker's halting and mapped facts at its system calls and instructions
`hhalt1`, `hmapW` (progress's worker half), and `HelloRowsW` (`HelloRows`
without main's step, the worker's unpark, progress, and the steps' keeping
`CertAll`, which `X64HelloM0.post_step0H`, `X64HelloUnpk.unpark_srcH`,
`X64HelloProgress.post_progressH` (main's halting and mapped facts from
`X64HelloMainInv.mainInvP_W`, `X64WakeMappedRow.hM_of`) and
`X64HelloCert.cert_stepH` (from `HelloRowsW.hconv`) prove).

main's side here is `helloM` at `μP` on `msHX` (as `X64HelloMs.hC0Ms` reads it); the
marks main's invariant past the clone is proved at agree with `μP` only
propositionally, so `hMainR` stays a premise.

- `LH`, `ιH`, `endH`, `SRH`, `GH`, `PaH`, `μH`, `DH`, `MH`, `QH`: the
  instance's data.
- `own_QH`: the instance's owned words are `wakeOwnXW (tcbM L) (tcbWH L)`.
- `hello_obligations_I`: the assembly at the instance.

## Differences from the AArch64 version

- The placement check is `PlaceWX` at `Scc.Cert.PlaceOK.X64.Out`, the layout
  `RuntimeLayout.ofPlaceWX`, and the program the placed cells
  `SccCode.helloCells` (the loader's parse `cellsOf asm = some …`, not
  `textProgram`).
- The data sections are parsed from `asm.text`, and the load reads the
  listing's label offsets: `hoffs : asm.labelOffs = o.labelOffs` is a further
  loader premise (as in `X64HelloOHinit`), consumed by `hstart`.
- The clone's facts `hCl` are `X64HelloHPre.hpre_ofH`'s, whose `ClonePreH`
  carries no label prefix.
- `X64HelloAssembly.hello_obligations` reads the placement check at the
  linked layout (`PlaceWX.link i hp`) and the cells' parse, in place of
  AArch64's `PlaceW.link i hp` and `textProgram` parse.
- Unlike AArch64, each thread owns its TCB self word (main `tcbM`, the worker `tcbWH`; the memory sides `msHX`,
  `msWHX`), read through `%fs` where AArch64 reads `tpidr_el0`; so the spawn hands both words over
  (`SpawnPreH.self`, `hself`) and the store phase keeps the worker's (`hZW`).
-/
import Spike.Lib.X64HelloAssembly
import Spike.Lib.X64HelloRec
import Spike.Lib.X64HelloSelfOK
import Spike.Lib.X64HelloRootRows
import Spike.Lib.X64HelloSpos
import Spike.Lib.X64HelloLive
import Spike.Lib.X64HelloMs
import Spike.Lib.X64HelloOwnLift
import Spike.Lib.X64HelloOInit
import Spike.Lib.X64WakeQ
import Spike.Lib.X64WakeHStart
import Spike.Lib.X64HelloM0Post
import Spike.Lib.X64HelloUnpk
import Spike.Lib.X64HelloCert
import Spike.Lib.X64HelloProgress

namespace Spike.Lib.X64HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Inv2Core Spike.Lib.X64WakeInst
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloW1Store (helloDH QIH ZStoreOk noWrite_IR)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH AbW)
open Spike.Lib.X64HelloInst (helloP)
open Spike.Lib.X64HelloMs (msHX helloLocs)
open Spike.Lib.X64HelloOwnLift (msWHX)
open Spike.Lib.X64HelloMainInv (helloM)
open Spike.Lib.X64HelloOkHR (okHR)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.X64HelloSpawnR (HMainRH HWiH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloAssembly (HelloCompat HelloRows HelloRowsW hello_obligations)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Cert.Rt.X64 (endOf)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The placed runtime layout. -/
abbrev LH : RuntimeLayout := RuntimeLayout.ofPlaceWX hp i

/-- hello's root records at the placed layout. -/
abbrev ιH : Type :=
  {g : Gh // okHR (LH hp i).Λ lBH (Spike.Lib.X64.WakePh.tcbM (LH hp i)) (X64HelloOwnLift.tcbWH (LH hp i)) g}

/-- Where a thread running hello's text halts. -/
abbrev endH : Int64 := endOf (LH hp i).exe SccCode.helloCells (LH hp i).pfx

/-- The record's spawn data. -/
abbrev SRH (w : ιH hp i) : SpawnRec := wakeSR w.1

/-- The record's value invariant: `G0 w`, the flag's target word `cT`
taking `1`. -/
abbrev GH (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i) : Loc → Val → Prop := WakeG.wakeG (G0 w) w.1.cT

/-- The target's marks at the placed layout. -/
noncomputable abbrev μH (E : Entry) (asm : Asm) : Marks := X64HelloCompatI.μP hp i (kernel 2) E asm

/-- The record's location data. -/
noncomputable abbrev PaH (E : Entry) (asm : Asm) (w : ιH hp i) : Inv2Params isa :=
  helloP abi (μH hp i E asm) (helloLocs (LH hp i) (SRH hp i w).lbl (SRH hp i w).lsize w.1.cT w.1.cS)

variable /- the records' value invariant below `wakeG` -/ (G0 : ιH hp i → Loc → Val → Prop)
  (P Z X : ιH hp i → FragS isa)
  /- the worker's segment at hello's memory side -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False))

/-- The worker's side: `helloDH` at the record's pointer word and hello's
buffer (`lBH`, `13` bytes, `2` words). -/
noncomputable abbrev DH : WSideH (ιH hp i) :=
  helloDH (LH hp i).exe (endH hp i) (LH hp i) (GH hp i G0) (SRH hp i) P Z X hseg (fun w => w.1.cwW) (fun _ => lBH)
    (fun _ => 13) (fun _ => 2)

/-- main's side: `helloM` at the target's marks on `msHX` (`X64HelloMs.hC0Ms`'). -/
noncomputable abbrev MH (E : Entry) {asm : Asm} (hpa : cellsOf asm = some o.prog) : X64WakeM0.MSide (ιH hp i) :=
  helloM (fun w => (SRH hp i w).lbl) (fun w => (SRH hp i w).lsize) (msHX (LH hp i) (GH hp i G0) (SRH hp i))
    (fun w => w.1.cwM) (LH hp i).lab (LH hp i).exe (LH hp i).Λ (μH hp i E asm) (X64HelloCompatI.hoffP hp i hpa)

/-- **The relation at the instance** (`QIH`). -/
noncomputable abbrev QH (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (E : Entry) {asm : Asm}
    (hpa : cellsOf asm = some o.prog) (passT : State → Prop) (Dd : ODataH) (r1c : Range) : WakeRel :=
  QIH (LH hp i).exe (endH hp i) (LH hp i) (GH hp i G0) (SRH hp i) P Z X hseg (fun w => w.1.cwW) (fun _ => lBH)
    (fun _ => 13) (fun _ => 2) (fun w => w.1.cT) (fun w => w.1.cS) (arch := arch) (R1 := R1)
    (μ := μH hp i E asm) (pT := fun w => w.1.pT) (passT := passT) (M := MH hp i G0 E hpa)
    (r0 := fun _ => Dd.r0) (r1 := fun _ => r1c)

/-- The worker's pointer word is a locative to `cS` (`X64HelloRootRows.cwv_okHR`). -/
theorem cwvH : ∀ w : ιH hp i, (w.1.cwW).val = .loc w.1.cS 0 :=
  X64HelloRootRows.cwv_okHR (cS := fun w => w.1.cS) (cw := fun w => w.1.cwW) (fun _ => rfl) (fun _ => rfl)

/-- `HelloCompat`'s `hcw` at the instance. -/
theorem hcwH : ∀ w, ∃ cS, ((DH hp i G0 P Z X hseg).cw w).val = .loc cS 0 := fun w => ⟨w.1.cS, cwvH hp i w⟩

/-- `HelloCompat`'s `hem` at the instance (`X64HelloW1Store.noWrite_IR`). -/
theorem hemH (hZ : ZStoreOk (LH hp i).exe Z) : X64HelloW1Store.NoWrite (DH hp i G0 P Z X hseg) :=
  noWrite_IR (LH hp i).exe (endH hp i) (SRH hp i) (fun w => (SRH hp i w).lbl)
    (fun w _ => msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) P Z X (fun _ _ => rfl)
      hseg (fun w => w.1.cwW)
    (fun _ => lBH) (fun _ => 13) (fun _ => 2) (hcwH hp i G0 P Z X hseg) hZ

/-- **The instance's owned words are wake's self words** (`X64HelloQ.own_XW`): main's side `msHX` owns `tcbM`'s
word, the worker's `msWHX` `tcbWH`'s. -/
theorem own_QH (arch : WeakMem.Arch) (R1 : Cfg → TermRun.Cfg → Prop) (E : Entry) {asm : Asm}
    (hpa : cellsOf asm = some o.prog) (passT : State → Prop) (Dd : ODataH) (r1c : Range) :
    (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).own =
      X64WakeOwnX.wakeOwnXW (Spike.Lib.X64.WakePh.tcbM (LH hp i)) (X64HelloOwnLift.tcbWH (LH hp i)) :=
  X64HelloQ.own_XW (fun _ _ => rfl) (fun _ _ _ => rfl)

/-- `msHX` is wake's `msXW` at `msH`, owning `tcbM` (`own_QH`'s thread 0 side). -/
example (G : ιH hp i → Loc → Val → Prop) (w : ιH hp i) :
    msHX (LH hp i) G (SRH hp i) w = X64WakeOwnX.msXW (X64HelloMs.msH (LH hp i) G (SRH hp i) w)
      (Spike.Lib.X64.WakePh.tcbM (LH hp i)) (Spike.Lib.X64.WakePh.tcbM (LH hp i)) ((LH hp i).pinA + 112#64) := rfl

/-- **The assembly at the placed instance** (see the module doc). -/
theorem hello_obligations_I {arch : WeakMem.Arch} {B : Budget} {asm : Asm} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {passT : State → Prop} {Dd : ODataH} {r1c : Range}
    {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
    /- the loader's parses (the trust boundary): the listing's cells are the
    placed output's and hello's, its data sections and label offsets the
    output's -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- The pinned region reaches `pinA + 168` (the records' `SelfOK`, `X64HelloSelfOK.selfOK_placedH`). -/
    (hpin2 : (LH hp i).pinA.toNat + 168 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    /- The code is placed at hello's `lo` (`X64HelloOInit.hlab_H`, the labels for `hpre_ofH`'s `hself`). -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.HelloPh.lo)
    /- The pre-spawn half. -/
    (O : Pre1T arch (LH hp i).Λ B asm E R1 Ab Ac helloSrc)
    /- `R1` is the pre-spawn relation with its source conjuncts
    (`X64HelloHPre.hpre_ofH`'s `hR1`). -/
    (hR1 : ∀ d s, R1 d s → R1OH arch (LH hp i).Λ (μH hp i E asm) Dd XH d s)
    /- The clone's facts at the pre-spawn segment's end (`hpre_ofH`'s `hCl`). -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      X64Consumer.HeldOk2 (LH hp i).Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH (LH hp i).Λ Dd.r0 r1c X lbl d s)
    /- The data's guarantee is below every record's. -/
    (hG : ∀ w m, MemInv Dd.G m → MemInv (GH hp i G0 w) m)
    /- (the record's park permit word at the clone; any) -/ (pT0 : Loc)
    /- The target store point (`WCompatH.pass`). -/
    (pass : X64HelloW1.PassH (DH hp i G0 P Z X hseg) passT)
    /- The store phase's pc facts on the segment's `Z`. -/
    (hZ : ZStoreOk (LH hp i).exe Z)
    /- The store phase's instructions write off the worker's TCB self word (discharged at `AssemblyRS` by the
    worker fragment's `OwnW (tcbWH)` conjunct, in progress; it does not follow from `Z`). -/
    (hZW : ∀ w s c, Z w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c)
    /- The data's own map is `ownGHXW L a` (`hpre_ofH`'s `hself`; `rfl` at the root's data, discharged in the
    root's invariant). -/
    {a : BitVec 64} (hDd : ∀ s fs, Dd.own s fs = Spike.Lib.X64.HelloPh.ownGHXW (LH hp i) a s)
    /- main's thread at the clone runs the layout's executable (`hpre_ofH`'s `hself`; from the pre-spawn
    fragment, as `X64HelloXOk.hX_ofR`). -/
    (hexe : ∀ d s th stack tls r, SpawnPrem (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (LH hp i).Λ asm E 0
      d s th stack tls r → th.st.exe = (LH hp i).exe)
    /- main's invariant past the clone (see the module doc). -/
    (hMainR : HMainRH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg) (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E
      (X64HelloHPre.FrH Dd))
    /- The child in the worker side's invariant. -/
    (hWi : HWiH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg) (fun _ => Dd.r0) (fun _ => r1c) (LH hp i).Λ asm E
      (X64HelloHPre.FrH Dd))
    /- The worker's states run at a system call (`X64WakeAssembly`'s `hhalt1`). -/
    (hhalt1 : ∀ w s c fs, (DH hp i G0 P Z X hseg).Wi w s c fs → abi.atSys s = true → (isa.exec s).isSome)
    /- The worker's instructions touch only locations mapped in `K0`
    (`X64WakeAssembly`'s `hmapW`). -/
    (hmapW : ∀ w s c fs, (DH hp i G0 P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isa.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (X64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- See `HelloRowsW`' fields. -/
    (R : HelloRowsW arch (LH hp i).Λ B asm (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) E
      (DH hp i G0 P Z X hseg) (MH hp i G0 E hpa) (AbW (LH hp i).exe) (hcwH hp i G0 P Z X hseg)
      (hemH hp i G0 P Z X hseg hZ) Ab Ac Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) E
      (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc :=
  haveI := (LH hp i).valid
  have ho : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.X64.Lays (LH hp i).exe SccCode.helloCells (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  have hwf := X64WakeQ.hwf_ofPlaceOK hp i
  have hC : HelloCompat (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (DH hp i G0 P Z X hseg) (MH hp i G0 E hpa)
      ((target (kernel 2) E).marks asm (LH hp i).Λ) (LH hp i).Λ arch (AbW (LH hp i).exe) (hcwH hp i G0 P Z X hseg)
      (hemH hp i G0 P Z X hseg hZ) :=
    ⟨X64HelloCompatI.hC_IP hp i (endH hp i) (SRH hp i) (fun w => (SRH hp i w).lbl)
        (fun w _ => msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) P Z X (fun _ _ => rfl)
        hseg (fun w => w.1.cwW)
        (fun _ => lBH) (fun _ => 13) (fun _ => 2) ho hpa rfl (cwvH hp i) pass
        (fun w s _ Lc v h => X64HelloMs.ownCov1_H (L := LH hp i) (SR := SRH hp i) (μ := μH hp i E asm)
          (fun w => w.1.cT) (fun w => w.1.cS) w s Lc v h)
        (fun w s0 s _ Lc v v' h0 h1 => by
          have h0' : (Lc, v) ∈ (msHX (LH hp i) (GH hp i G0) (SRH hp i) w).own s0 := h0
          simp only [msWHX, msHX, X64WakeOwnX.msXW, List.mem_singleton, Prod.mk.injEq] at h0' h1
          have h0 := h0'
          exact X64HelloMs.tcbM_ne_tcbWH (LH hp i) (congrArg Loc.addr (h0.1.symm.trans h1.1))),
      X64HelloW1Store.wcompat_relW_IR (LH hp i).exe (endH hp i) (LH hp i) (GH hp i G0) (SRH hp i) P Z X hseg
        (fun w => w.1.cwW) (fun _ => lBH) (fun _ => 13) (fun _ => 2) (fun w => w.1.cT) (fun w => w.1.cS) hl rfl
        (X64HelloCompatI.hello_hμP hp i hpa) (cwvH hp i) pass hZ hZW (fun _ _ => rfl)
        (X64HelloRootRows.cT_okHR (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
        (X64HelloRootRows.cTin_okHR (fun _ => rfl)) X64HelloRootRows.cTfoot_okHR X64HelloRootRows.cSfrz_okHR
        X64HelloSpos.sposH
        (X64HelloRootRows.footLab_okHR (fun w => X64HelloMs.helloLocs_okG _ w.1 (X64HelloOkHR.okHR_self w)))
        X64HelloLive.mainLiveH,
      X64HelloWorkerRR.hx_IR (fun _ _ _ => rfl) (fun _ s Lc v h => X64WakeOwnX.ownMpXW (.inr rfl) s Lc v h)
        (X64HelloRootRows.Gc_okHR (fun _ => rfl)),
      X64HelloMs.hC0Ms hp i hpa
        (X64HelloRootRows.hcw_okHR (cS := fun w => w.1.cS) (cw := fun w => w.1.cwM) (fun _ => rfl) (fun _ => rfl))⟩
  have hpre := X64HelloHPre.hpre_ofH (SR := SRH hp i) (cT := fun w => w.1.cT) (cS := fun w => w.1.cS)
    (pT := fun w => w.1.pT) (Pa := PaH hp i E asm) (G := GH hp i G0) (passT := passT) (M := MH hp i G0 E hpa)
    (D := DH hp i G0 P Z X hseg) (r0 := fun _ => Dd.r0) (r1 := fun _ => r1c) (asm := asm) (E := E)
    hR1 (fun _ => rfl) (fun _ => rfl) hwf hCl
    (X64HelloRec.hrec_okHRc pT0 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hG hwf
      (fun _ _ _ _ _ _ _ hm hg => X64HelloSelfOK.selfOK_placedH hp i hpin2 hm hg)) (fun _ => rfl)
      (L := LH hp i) (a := a) (fun w st T W h => by
        rw [own_QH] at h
        obtain ⟨rfl, rfl⟩ := X64HelloHPre.wakeOwnXW_inj_at h
        exact ⟨rfl, rfl, rfl, X64HelloOInit.hlab_H hp i hpa hhp hlo, hDd, hexe⟩)
  hello_obligations hwf rfl rfl hC
    (X64WakeHStart.hstart_of_loadOk hpa hd (hoffs ▸ PlaceWX.loadOk_link_of_placeWX i hp) hE) O
    (X64HelloSpawnR.spawn_RH arch R1 (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT)
      (PaH hp i E asm) (GH hp i G0) passT (MH hp i G0 E hpa) (DH hp i G0 P Z X hseg) (fun _ => Dd.r0)
      (fun _ => r1c) (LH hp i).Λ asm E (X64HelloHPre.FrH Dd) (fun _ => WakeP.wakeP_frz_cov)
      (fun w => WakeP.wakeP_foot_cov (X64HelloMs.helloLocs_okG _ w.1 (X64HelloOkHR.okHR_self w))) pass
      (own_QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c)
      (fun h => X64HelloMs.tcbM_ne_tcbWH (LH hp i) (congrArg Loc.addr h))
      (fun _ => WakeP.wakeP_own_cov (.inl ⟨rfl, rfl⟩)) (fun _ => WakeP.wakeP_own_cov (.inr ⟨rfl, rfl⟩))
      hpre hMainR hWi)
    { R with post_step0 := X64HelloM0.post_step0H rfl rfl hwf rfl, unpark_src := X64HelloUnpk.unpark_srcH hwf rfl
             post_progress := fun hC => X64HelloProgress.post_progressH rfl rfl hC (fun _ _ => rfl)
               (MH hp i G0 E hpa).off (fun _ s c h _ => (X64HelloMainInv.mainInvP_W s c h).2.1.1) hhalt1
               (X64WakeMappedRow.hM_of (fun _ => rfl) (fun _ _ _ h => h.1.1)
                 (fun _ s c h => (X64HelloMainInv.mainInvP_W s c h).2.2.1)) hmapW
             cert_step := fun hC => X64HelloCert.cert_stepH rfl rfl hC (R.hconv hC) }
    (PlaceWX.link i hp) hpa

end Inst

end Spike.Lib.X64HelloAssemblyI

/-- info: 'Spike.Lib.X64HelloAssemblyI.cwvH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.cwvH

/-- info: 'Spike.Lib.X64HelloAssemblyI.hcwH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hcwH

/-- info: 'Spike.Lib.X64HelloAssemblyI.hemH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hemH

/-- info: 'Spike.Lib.X64HelloAssemblyI.own_QH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.own_QH


/-- info: 'Spike.Lib.X64HelloAssemblyI.hello_obligations_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hello_obligations_I
