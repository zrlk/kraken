/-
**hello.w on x86-64: the `WakeObligations` assembly at the placed instance, `hMainR` discharged** (the twin of
`Spike/Lib/HelloAssemblyIM.lean`): `X64HelloAssemblyI.hello_obligations_I` at hello's root value invariant
`G0H` (`X64HelloGOf2H.GOf2H` at the placed output's initial memory) and at the pre-spawn relation with the
privacy conjunct `R1 ∧ VPriv L.Λ E` (`X64HelloMainG.pre1T_privH`), its `hMainR` by
`X64HelloMainGH.hMainRH_ofGH`.

- `G0H`: hello's root value invariant at the placed output.
- `hello_obligations_IM`: the assembly at the instance, `hMainR` replaced by its open rows `hsub1` and
  `hpc` (the worker's progress rows `hhalt1`, `hmapW` and `hello_obligations_I`'s `hlo`, `hZW`, `hDd`, `hexe`
  passed through).

## Unlike AArch64

- main's memory side `msHX` owns its TCB self word, so `hMainRH_ofGH` closes the park's ownership of it (AArch64's
  park reads a register); the worker's segment `hseg` is at the worker's owning side `msWHX`.
- The loader's parses are `cellsOf asm = some …`, the data sections `asm.text`'s, and the listing's label offsets
  a further premise `hoffs` (as `hello_obligations_I`); the clone's `ClonePreH` carries no label prefix; the
  segment end's region is `⟨Rm.base, -128, 40⟩`, its bound at `(R.fp 8).addr 0 - 8 - 16` (AArch64
  `⟨Rm.base, -144, 48⟩`, `R.addr (-32)`).
-/
import Spike.Lib.X64HelloMainGH
import Spike.Lib.X64HelloGOf2H

namespace Spike.Lib.X64HelloAssemblyIM

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Inv2Core Spike.Lib.X64WakeInst
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1Store (ZStoreOk)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH AbW)
open Spike.Lib.X64HelloOwnLift (msWHX)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.X64HelloSpawnR (PreRH HWiH)
open Spike.Lib.X64HelloMainHRD (MainSegH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64WakePrivR (VPriv)
open Spike.Lib.X64HelloAssembly (HelloRowsW)
open Spike.Lib.X64HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH hcwH hemH)
open Spike.Lib.X64.Rt (RuntimeLayout)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **hello's root value invariant** at the placed output (what `X64HelloMainGH.hMainRH_ofGH`'s `hG0` asks). -/
abbrev G0H (_ : ιH hp i) : Loc → Val → Prop :=
  X64HelloGOf2H.GOf2H (LH hp i) (Spike.Lib.X64.PhRec.m0Of (LH hp i).Λ o.prog o.secs)

variable (P Z X : ιH hp i → FragS isa)
  /- the worker's segment at hello's memory side (as `hello_obligations_I`'s `hseg`) -/
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => msWHX (LH hp i) (GH hp i (G0H hp i)) (SRH hp i) w) (P w) (fun _ _ _ => False))

set_option hygiene false in
/-- The pre-spawn relation with its privacy conjunct. -/
local notation "R1V" => fun d s => R1 d s ∧ VPriv (LH hp i).Λ E d

/-- **The assembly at the placed instance, `hMainR` discharged** (see the module doc). -/
theorem hello_obligations_IM {arch : WeakMem.Arch} {B : Budget} {asm : Asm} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {passT : State → Prop} {Dd : ODataH} {r1c : Range}
    {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
    /- the loader's parses (the trust boundary) -/
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    /- The entry state is clear of the layout. -/
    (hE : E.clear (LH hp i).Λ = true)
    /- The pinned region reaches `pinA + 200` (the records' `SelfOK`). -/
    (hpin2 : (LH hp i).pinA.toNat + 200 ≤ (LH hp i).Λ.pinned.lo + (LH hp i).Λ.pinned.size)
    /- The code is placed at hello's `lo`. -/
    (hlo : Λ0.code.lo = Spike.Lib.X64.HelloPh.lo)
    /- The pre-spawn half. -/
    (O : Pre1T arch (LH hp i).Λ B asm E R1 Ab Ac helloSrc)
    /- `R1` is the pre-spawn relation with its source conjuncts. -/
    (hR1 : ∀ d s, R1 d s → R1OH arch (LH hp i).Λ (X64HelloAssemblyI.μH hp i E asm) Dd XH d s)
    /- The clone's facts at the pre-spawn segment's end. -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1V) E hpa passT Dd r1c) (LH hp i).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      X64Consumer.HeldOk2 (LH hp i).Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 (LH hp i).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH (LH hp i).Λ Dd.r0 r1c X lbl d s)
    /- The data's guarantee is below every record's. -/
    (hG : ∀ w m, MemInv Dd.G m → MemInv (GH hp i (G0H hp i) w) m)
    /- (the record's park permit word at the clone; any) -/ (pT0 : Loc)
    /- The target store point (`WCompatH.pass`). -/
    (pass : X64HelloW1.PassH (DH hp i (G0H hp i) P Z X hseg) passT)
    /- The store phase's pc facts on the segment's `Z`. -/
    (hZ : ZStoreOk (LH hp i).exe Z)
    /- The store phase's instructions write off the worker's TCB self word (`hello_obligations_I`'s `hZW`;
    discharged at `AssemblyRS` by the worker fragment's `OwnW (tcbWH)` conjunct, in progress). -/
    (hZW : ∀ w s c, Z w s c [] → c.hold = none → X64HelloW1Store.StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH (LH hp i)) s c)
    /- The data's own map (`hello_obligations_I`'s `hDd`). -/
    {a : BitVec 64} (hDd : ∀ s fs, Dd.own s fs = Spike.Lib.X64.HelloPh.ownGHXW (LH hp i) a s)
    /- main's thread at the clone runs the layout's executable (`hello_obligations_I`'s `hexe`). -/
    (hexe : ∀ d s th stack tls r, SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1V) E hpa passT Dd r1c)
      (LH hp i).Λ asm E 0 d s th stack tls r → th.st.exe = (LH hp i).exe)
    /- The records' `r1` in the stack pool. -/
    (hsub1 : (r1c).Sub (LH hp i).Λ.stackPool)
    /- The segment end, per clone (`hMainRH_ofGH`'s `hpc`). -/
    (hpc : ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (QH hp i (G0H hp i) P Z X hseg arch (R1V) E hpa passT Dd r1c) (LH hp i).Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch (R1V) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
        (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa) (DH hp i (G0H hp i) P Z X hseg) (fun _ => Dd.r0)
        (fun _ => r1c) (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      X64HelloHPre.FrH Dd lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH (LH hp i).exe (endH hp i) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = (LH hp i).pinA + 0#64 + 8#64 ∧
        (LH hp i).stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat)
    /- The child in the worker side's invariant. -/
    (hWi : HWiH arch (R1V) (SRH hp i) (fun w => w.1.cT) (fun w => w.1.cS) (fun w => w.1.pT) (PaH hp i E asm)
      (GH hp i (G0H hp i)) passT (MH hp i (G0H hp i) E hpa) (DH hp i (G0H hp i) P Z X hseg) (fun _ => Dd.r0)
      (fun _ => r1c) (LH hp i).Λ asm E (X64HelloHPre.FrH Dd))
    /- The worker's states run at a system call. -/
    (hhalt1 : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = true →
      (isa.exec s).isSome)
    /- The worker's instructions touch only locations mapped in `K0`. -/
    (hmapW : ∀ w s c fs, (DH hp i (G0H hp i) P Z X hseg).Wi w s c fs → abi.atSys s = false → ∀ e,
      isa.exec s = some e →
      ¬ Kernel.Touches (fun l w => Kernel.mapped (X64Consumer.K0 (LH hp i).Λ) w l = false) e)
    /- See `HelloRowsW`' fields. -/
    (R : HelloRowsW arch (LH hp i).Λ B asm (QH hp i (G0H hp i) P Z X hseg arch (R1V) E hpa passT Dd r1c) E
      (DH hp i (G0H hp i) P Z X hseg) (MH hp i (G0H hp i) E hpa) (AbW (LH hp i).exe)
      (hcwH hp i (G0H hp i) P Z X hseg) (hemH hp i (G0H hp i) P Z X hseg hZ) Ab Ac Tw) :
    WakeObligationsR arch (LH hp i).Λ B asm (QH hp i (G0H hp i) P Z X hseg arch (R1V) E hpa passT Dd r1c) E
      (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc :=
  X64HelloAssemblyI.hello_obligations_I hp i (G0H hp i) P Z X hseg hpa hhp hd hoffs hE hpin2 hlo
    (X64HelloMainG.pre1T_privH hp i hpa O) (fun d s h => hR1 d s h.1) hCl hG pT0 pass hZ hZW hDd hexe
    (X64HelloMainGH.hMainRH_ofGH hp i hpa hhp (fun _ => rfl) (fun _ => hsub1) hpc) hWi hhalt1 hmapW R

end Inst

end Spike.Lib.X64HelloAssemblyIM

/-- info: 'Spike.Lib.X64HelloAssemblyIM.hello_obligations_IM' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyIM.hello_obligations_IM
