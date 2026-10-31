/-
**wake.w on x86-64: the assembly at main's instance** (in the manner of
`Spike/Lib/WakeAssemblyI.lean`). `X64WakeAssembly.wake_obligations` at the
relation `X64WakeQ.wakeQ` with main's side
`X64WakeInst.wakeM hp i T W ok lab μ hoff`, the layout
`(RuntimeLayout.ofPlaceWX hp i).Λ` and main's marks the loaded program's
(`μ := (target (kernel 2) E).marks asm Λ`). Discharged here:

- `hwf` by `X64WakeQ.hwf_ofPlaceOK`; `hPT0`, `hKR`, `hown` by `rfl`
  (`X64WakeQ.hPT0`, `hKR`, `hown`);
- `hhalt0` by `X64WakeInst.hhalt0_I`, `hmapM` by `X64WakeInst.hmapM_I`,
  `hMμ` by `X64WakeInst.hMμ_I`.

`wake_obligations_IW` folds the worker's three facts into one `hW`: the
worker's states inside `NNZ exe endPc (ZX.wakeZX Λw lbl' cSf W' exe kp)`, with
one flag `cSf` for the family (`hcS`): `hhalt1` by `ZX.hhalt1_ofX`, `hW1` by
`ZX.hW1_ofX`, and `hmapW` by `X64WakeMappedRow.hW_of` with
`X64WakeLabMapped.labMapped_flag` at `wakeZX`'s flag pointer, the flag's
word placed and shared by `hC`'s `cT`/`cTin`; only the memory sides' `mp`
mapped in `K0 Λ` (`hmp`) is new.

`wake_obligations_IWP` adds `post_wit` by `X64WakePostWit.post_wit_of`
(`hPT0`/`hPT1` by `rfl`): main's states placed by `X64WakeInst.placed_I`,
the worker's by `ZX.placed` through `hW`, at `wakeZX`'s layout the
instance's; the spawn records' labels are the instance's (`hSR`) and one map
for the family (`hlbl`).

`wake_obligations_IWW` is `wake_obligations_IWP` at the worker's side
`D := X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf`, `hW` and
`hmp` by `X64WakeWorkerX.hW_I`, `hmp_I`.

**Unlike AArch64** (forced by the x64 shape):
- `X64WakeQ.wakeQ` takes the store point `passT` and the two TCB self
  words `T W`; main's side `wakeM` takes `T W` (its memory side `msM`).
- `wakeZX` carries the worker's TCB word; in `wake_obligations_IWW` it is
  the relation's `W` (the worker side `wakeD` keeps `wakeZX … W …`).
- `hpl : PlaceWX` and `hpa : cellsOf asm = some po.prog` (AArch64:
  `PlaceW`, `textProgram`); the end is `endOf exe SccCode.wakeCells kp`.
-/
import Spike.Lib.X64WakeAssembly
import Spike.Lib.X64WakeInst
import Spike.Lib.X64WakeZX
import Spike.Lib.X64WakeLabMapped
import Spike.Lib.X64WakePostWit
import Spike.Lib.X64WakeMappedRow
import Spike.Lib.X64WakeWorkerX
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeAssemblyI

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakeW1 Spike.Lib.X64WakePreTi
open Spike.Lib.Inv2Core Spike.Lib.Handover Spike.Lib.X64WakeInst
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Worker (NNZ)
open Spike.Lib.X64.Flow.Worker.Wake.ZX (wakeZX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  {arch : WeakMem.Arch} {B : Budget} {asm : Asm} {E : Entry}
  {ok : Gh → Prop} {lab : String → Int64} {T W : BitVec 64}
  {R1 : Cfg → TermRun.Cfg → Prop} {SR : {g : Gh // ok g} → SpawnRec}
  {cT : {g : Gh // ok g} → Loc} {cS : {g : Gh // ok g} → WeakMem.Address} {pT : {g : Gh // ok g} → Loc}
  {P : {g : Gh // ok g} → Inv2Params isa} {G : {g : Gh // ok g} → Loc → Val → Prop}
  {D : WSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range} {passT : State → Prop}

/-- **The assembly at main's instance**: `X64WakeAssembly.wake_obligations`
with main's facts discharged by `X64WakeInst` (see the module doc). -/
theorem wake_obligations_I {Ab Ac : State → Prop}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
    (hC : WCompat (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ arch)
    (hx : WCompatX (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D)
    /- (main's side; its `relW0` is `X64WakeInst.relW0_I`) OPEN -/
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
    /- OPEN: the worker's facts (one `hW` in `wake_obligations_IW`) -/
    (hhalt1 : ∀ w s c, D.Wi w s c → abi.atSys s = true → (isa.exec s).isSome)
    (hmapW : ∀ w s c, D.Wi w s c → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (X64Consumer.K0 (RuntimeLayout.ofPlaceWX hp i).Λ) w l = false) e)
    (hW1 : ∀ w s c e, D.Wi w s c → isa.exec s = some e → EvTree.RelW1 Arch.tso e)
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg' (RuntimeLayout.ofPlaceWX hp i).Λ po)
    (hpa : cellsOf asm = some po.prog)
    /- OPEN (`wake_obligations_IWP`) -/
    (post_wit : ∀ t s,
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W).Post
        (RuntimeLayout.ofPlaceWX hp i).Λ t s → X64WakeRunInv.RunInv (RuntimeLayout.ofPlaceWX hp i).Λ E t →
      ∃ w, Components (machine (kernel 2)) (RuntimeLayout.ofPlaceWX hp i).Λ w t s) :
    WakeObligations arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) E
      (TiPre Ab Ac) :=
  X64WakeAssembly.wake_obligations (X64WakeQ.hwf_ofPlaceOK hp i) rfl rfl rfl hC hx hC0 hstart O spawn
    (hhalt0_I hp i T W) hhalt1 (hmapM_I hp i T W) hmapW (hMμ_I hp i T W) hpl hpa hW1 post_wit

/-- info: 'Spike.Lib.X64WakeAssemblyI.wake_obligations_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_I

/-- **The assembly at main's instance, the worker's facts from one `hW`**:
`wake_obligations_I` with `hhalt1`, `hmapW` and `hW1` from the worker's
states inside `NNZ exe endPc (wakeZX Λw lbl' cSf W' exe kp)` (see the module
doc). -/
theorem wake_obligations_IW {Ab Ac : State → Prop}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    (hC : WCompat (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ arch)
    (hx : WCompatX (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D)
    (hC0 : X64WakeM0.WCompat0
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W)
      (wakeM hp i T W ok lab _ hoff)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ)
    (hstart : ∃ d, (target (kernel 1) E).load asm (RuntimeLayout.ofPlaceWX hp i).Λ = some d)
    (O : Pre1T arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W).Post
          (RuntimeLayout.ofPlaceWX hp i).Λ (afterClone abi d tid th stack tls r) s')
    /- OPEN: the worker's states keep `wakeZX`, one flag for the family -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address} {W' : BitVec 64}
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe SccCode.wakeCells kp)
    (hW : ∀ w s c, D.Wi w s c → NNZ exe endPc (wakeZX Λw lbl' cSf W' exe kp) s c)
    (hcS : ∀ w, cS w = cSf)
    /- OPEN: the rows' memory sides read and write mapped words -/
    (hmp : ∀ w L wr, (D.ms w).mp L wr →
      Kernel.mapped (X64Consumer.K0 (RuntimeLayout.ofPlaceWX hp i).Λ) wr L = true)
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg' (RuntimeLayout.ofPlaceWX hp i).Λ po)
    (hpa : cellsOf asm = some po.prog)
    (post_wit : ∀ t s,
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W).Post
        (RuntimeLayout.ofPlaceWX hp i).Λ t s → X64WakeRunInv.RunInv (RuntimeLayout.ofPlaceWX hp i).Λ E t →
      ∃ w, Components (machine (kernel 2)) (RuntimeLayout.ofPlaceWX hp i).Λ w t s) :
    WakeObligations arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) E
      (TiPre Ab Ac) :=
  wake_obligations_I hp i hoff hC hx hC0 hstart O spawn
    (Spike.Lib.X64.Flow.Worker.Wake.ZX.hhalt1_ofX hend (cOf := id) hW)
    (X64WakeMappedRow.hW_of hC.K hmp fun w s c hi => by
      obtain ⟨a, hTa, hAa, -⟩ := hC.cT w
      rw [hC.lbl w]
      exact X64WakeLabMapped.labMapped_flag
        (fun sa hpt => (Spike.Lib.X64.Flow.Worker.Wake.ZX.labPtr (hW w s c hi).2 sa hpt).trans (hcS w).symm)
        hAa hTa (hC.cTin w))
    (Spike.Lib.X64.Flow.Worker.Wake.ZX.hW1_ofX (cOf := id) hW) hpl hpa post_wit

/-- info: 'Spike.Lib.X64WakeAssemblyI.wake_obligations_IW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_IW

/-- **The assembly at main's instance, `post_wit` discharged**:
`wake_obligations_IW` at `wakeZX`'s layout the instance's, with `post_wit`
by `X64WakePostWit.post_wit_of` (see the module doc). -/
theorem wake_obligations_IWP {Ab Ac : State → Prop}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    (hC : WCompat (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ arch)
    (hx : WCompatX (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) D)
    (hC0 : X64WakeM0.WCompat0
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W)
      (wakeM hp i T W ok lab _ hoff)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ)
    (hstart : ∃ d, (target (kernel 1) E).load asm (RuntimeLayout.ofPlaceWX hp i).Λ = some d)
    (O : Pre1T arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W).Post
          (RuntimeLayout.ofPlaceWX hp i).Λ (afterClone abi d tid th stack tls r) s')
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address} {W' : BitVec 64}
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe SccCode.wakeCells kp)
    (hW : ∀ w s c, D.Wi w s c → NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf W' exe kp) s c)
    (hcS : ∀ w, cS w = cSf)
    /- (instance data; `rfl` at `X64WakeInst.wakeQI`) the spawn records'
    labels are the instance's, and one map for the family -/
    (hSR : ∀ w, (SR w).lbl = (wakeSR w.1).lbl) (hlbl : ∀ w, (SR w).lbl = lbl')
    (hmp : ∀ w L wr, (D.ms w).mp L wr →
      Kernel.mapped (X64Consumer.K0 (RuntimeLayout.ofPlaceWX hp i).Λ) wr L = true)
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg' (RuntimeLayout.ofPlaceWX hp i).Λ po)
    (hpa : cellsOf asm = some po.prog) :
    WakeObligations arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff) D r0 r1 passT T W) E
      (TiPre Ab Ac) :=
  wake_obligations_IW hp i hoff hC hx hC0 hstart O spawn hend hW hcS hmp hpl hpa
    (X64WakePostWit.post_wit_of rfl rfl (X64WakeQ.hwf_ofPlaceOK hp i)
      (fun w s c h => (hSR w).symm ▸ placed_I hp i T W w s c h)
      (fun w s c h => (hlbl w).symm ▸ Spike.Lib.X64.Flow.Worker.Wake.ZX.placed (hW w s c h).2))

/-- info: 'Spike.Lib.X64WakeAssemblyI.wake_obligations_IWP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_IWP

/-- **The assembly at main's instance and the worker's side**:
`wake_obligations_IWP` at `D := X64WakeWorkerX.wakeD hp i T W ok exe endPc kp
lbl' cSf`, `hW` by `X64WakeWorkerX.hW_I` and `hmp` by `X64WakeWorkerX.hmp_I`
(see the module doc). -/
theorem wake_obligations_IWW {Ab Ac : State → Prop}
    (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.X64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- the worker's side's data (`X64WakeWorkerX.wakeD`): the listing's
    executable, its end, labels `lbl'` and flag `cSf` of `wakeZX` -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    (hC : WCompat (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff)
      (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf) r0 r1 passT T W)
      (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ arch)
    (hx : WCompatX (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff)
      (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf) r0 r1 passT T W)
      (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf))
    (hC0 : X64WakeM0.WCompat0 (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff)
      (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf) r0 r1 passT T W)
      (wakeM hp i T W ok lab _ hoff)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) (RuntimeLayout.ofPlaceWX hp i).Λ)
    (hstart : ∃ d, (target (kernel 1) E).load asm (RuntimeLayout.ofPlaceWX hp i).Λ = some d)
    (O : Pre1T arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm E R1 Ab Ac)
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceWX hp i).Λ) tid
        (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧
        (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff)
          (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf) r0 r1 passT T W).Post
          (RuntimeLayout.ofPlaceWX hp i).Λ (afterClone abi d tid th stack tls r) s')
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe SccCode.wakeCells kp)
    (hcS : ∀ w, cS w = cSf)
    (hSR : ∀ w, (SR w).lbl = (wakeSR w.1).lbl) (hlbl : ∀ w, (SR w).lbl = lbl')
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg' (RuntimeLayout.ofPlaceWX hp i).Λ po)
    (hpa : cellsOf asm = some po.prog) :
    WakeObligations arch (RuntimeLayout.ofPlaceWX hp i).Λ B asm
      (X64WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i T W ok lab _ hoff)
        (X64WakeWorkerX.wakeD hp i T W ok exe endPc kp lbl' cSf) r0 r1 passT T W) E (TiPre Ab Ac) :=
  wake_obligations_IWP hp i hoff hC hx hC0 hstart O spawn hend
    (X64WakeWorkerX.hW_I hp i T W ok exe endPc kp lbl' cSf) hcS hSR hlbl
    (X64WakeWorkerX.hmp_I hp i T W ok exe endPc kp lbl' cSf) hpl hpa

/-- info: 'Spike.Lib.X64WakeAssemblyI.wake_obligations_IWW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_IWW

end Spike.Lib.X64WakeAssemblyI
