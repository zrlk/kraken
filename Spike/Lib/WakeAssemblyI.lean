/-
**wake.w on AArch64: the assembly at main's instance**.
`WakeAssembly.wake_obligations` at the relation `WakeQ.wakeQ` with main's
side `WakeInst.wakeM hp i ok lab μ hoff`, the layout
`(RuntimeLayout.ofPlaceW hp i).Λ` and main's marks the loaded program's
(`μ := (target (kernel 2) E).marks asm Λ`). Discharged here:

- `hwf` by `WakeQ.hwf_ofPlaceOK`; `hPT0`, `hKR`, `hown` by `rfl`
  (`WakeQ.hPT0`, `WakeQ.hKR`, `WakeQ.hown`);
- `hhalt0` by `WakeInst.hhalt0_I`, `hmapM` by `WakeInst.hmapM_I`, `hMμ` by
  `WakeInst.hMμ_I`.

`hC0` stays a hypothesis (the `WCompat0` structure); its 16th field `relW0`
is `WakeInst.relW0_I` at this instance.

**Open**: `hstart`; the worker's `hhalt1`, `hmapW`, `hW1`
(planned as one `hW`); `post_wit`; `hC0`, `O`, `spawn`; the worker side's `hC`, `hx` and the parse `hpa`.

`wake_obligations_IW` folds the worker's three facts into one `hW`: the worker's states inside `NNZ exe endPc (ZX.wakeZX Λw lbl' cSf exe kp)`
at the program's end `endPc`, with one flag `cSf` for the family (`hcS`):
`hhalt1` by `ZX.hhalt1_ofX`, `hW1` by `ZX.hW1_ofX`, and `hmapW` by
`WakeMappedRow.hW_of` with `WakeLabMapped.labMapped_flag` at `wakeZX`'s flag
pointer, the flag's word placed and shared by `hC`'s `cT`/`cTin`; only the
memory sides' `mp` mapped in `K0 Λ` (`hmp`) is new.

`wake_obligations_IWP` adds `post_wit` by `WakePostWit.post_wit_of` (`hwf` by
`WakeQ.hwf_ofPlaceOK`, `hPT0`/`hPT1` by `rfl`): main's states placed by
`WakeInst.placed_I`, the worker's by `ZX.placed` through `hW`, at
`wakeZX`'s layout the instance's. The adapters: `placed_I` is at the
instance's spawn labels `(wakeSR w.1).lbl` (`hSR`, `rfl` at
`WakeInst.wakeQI`), and `wakeZX`'s labels `lbl'` are one for the family, so
each spawn's labels must be them (`hlbl`).

`wake_obligations_IWW` is `wake_obligations_IWP` at the worker side
`D := WakeWorkerX.wakeD` (the union of the segments keeping `wakeZX`, at the
records' placements and memory sides), `hW` and `hmp` by
`WakeWorkerX.hW_I`, `hmp_I`.
-/
import Spike.Lib.WakeInst
import Spike.Lib.A64WakeZX
import Spike.Lib.WakeLabMapped
import Spike.Lib.WakePostWit
import Spike.Lib.WakeWorkerX
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeAssemblyI

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakePreTi Spike.Lib.Handover
open Spike.Lib.Inv2Core Spike.Lib.WakeInst
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  {arch : WeakMem.Arch} {B : Budget} {asm : String} {E : Entry}
  {ok : Gh → Prop} {lab : String → Int64}
  {R1 : Cfg → TermRun.Cfg → Prop} {SR : {g : Gh // ok g} → SpawnRec}
  {cT : {g : Gh // ok g} → Loc} {cS : {g : Gh // ok g} → WeakMem.Address} {pT : {g : Gh // ok g} → Loc}
  {P : {g : Gh // ok g} → Inv2Params isaLSE2} {G : {g : Gh // ok g} → Loc → Val → Prop}
  {D : WSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range}

/-- **The assembly at main's instance**: `WakeAssembly.wake_obligations`
with main's facts discharged by `WakeInst` (see the module doc). -/
theorem wake_obligations_I {Ab Ac : State → Prop}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
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
    /- OPEN: the worker's facts (planned: one `hW`) -/
    (hhalt1 : ∀ w s c, D.Wi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    (hmapW : ∀ w s c, D.Wi w s c → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) w l = false) e)
    (hW1 : ∀ w s c e, D.Wi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e)
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    (hpl : PlaceW pcfg' (RuntimeLayout.ofPlaceW hp i).Λ po)
    (hpa : textProgram asm = .ok po.prog)
    /- OPEN -/
    (post_wit : ∀ t s, (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1).Post
      (RuntimeLayout.ofPlaceW hp i).Λ t s → WakeRunInv.RunInv (RuntimeLayout.ofPlaceW hp i).Λ E t →
      ∃ w, Components (machine (kernel 2)) (RuntimeLayout.ofPlaceW hp i).Λ w t s) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B asm
      (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1) E (TiPre Ab Ac) :=
  WakeAssembly.wake_obligations (WakeQ.hwf_ofPlaceOK hp i) rfl rfl rfl hC hx hC0 hstart O spawn
    (hhalt0_I hp i) hhalt1 (hmapM_I hp i) hmapW (hMμ_I hp i) hpl hpa hW1 post_wit

/-- info: 'Spike.Lib.WakeAssemblyI.wake_obligations_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_I

open Spike.Lib.A64.Flow.Worker (NNZ) in
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX) in
/-- **The assembly at main's instance, the worker's facts from one `hW`**:
`wake_obligations_I` with `hhalt1`, `hmapW` and `hW1` from the worker's states
inside `NNZ exe endPc (wakeZX Λw lbl' cSf exe kp)` (see the module doc). -/
theorem wake_obligations_IW {Ab Ac : State → Prop}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
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
    /- (`Child.seg_childPreNNA'` at `wakeZX`, through `WorkerSide.side`)
    OPEN: the worker's states keep `wakeZX`, one flag for the family -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe Spike.Lib.A64.WakeLabels.wakeProg kp)
    (hW : ∀ w s c, D.Wi w s c → NNZ exe endPc (wakeZX Λw lbl' cSf exe kp) s c)
    (hcS : ∀ w, cS w = cSf)
    /- OPEN: the rows' memory sides read and write mapped words -/
    (hmp : ∀ w L wr, (D.ms w).mp L wr →
      Kernel.mapped (A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) wr L = true)
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    (hpl : PlaceW pcfg' (RuntimeLayout.ofPlaceW hp i).Λ po)
    (hpa : textProgram asm = .ok po.prog)
    /- OPEN -/
    (post_wit : ∀ t s, (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1).Post
      (RuntimeLayout.ofPlaceW hp i).Λ t s → WakeRunInv.RunInv (RuntimeLayout.ofPlaceW hp i).Λ E t →
      ∃ w, Components (machine (kernel 2)) (RuntimeLayout.ofPlaceW hp i).Λ w t s) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B asm
      (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1) E (TiPre Ab Ac) :=
  wake_obligations_I hp i hoff hC hx hC0 hstart O spawn
    (Spike.Lib.A64.Flow.Worker.Wake.ZX.hhalt1_ofX hend (cOf := id) hW)
    (WakeMappedRow.hW_of hC.K hmp fun w s c hi => by
      obtain ⟨a, hTa, hAa, -⟩ := hC.cT w
      rw [hC.lbl w]
      exact WakeLabMapped.labMapped_flag
        (fun sa hpt => (Spike.Lib.A64.Flow.Worker.Wake.ZX.labPtr (hW w s c hi).2 sa hpt).trans (hcS w).symm)
        hAa hTa (hC.cTin w))
    (Spike.Lib.A64.Flow.Worker.Wake.ZX.hW1_ofX (cOf := id) hW) hpl hpa post_wit

/-- info: 'Spike.Lib.WakeAssemblyI.wake_obligations_IW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_IW

open Spike.Lib.A64.Flow.Worker (NNZ) in
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX) in
/-- **The assembly at main's instance, `post_wit` discharged**:
`wake_obligations_IW` at `wakeZX`'s layout the instance's, with `post_wit`
by `WakePostWit.post_wit_of` (see the module doc). -/
theorem wake_obligations_IWP {Ab Ac : State → Prop}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
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
    /- (`Child.seg_childPreNNA'` at `wakeZX`, through `WorkerSide.side`)
    OPEN: the worker's states keep `wakeZX` at the instance's layout, one
    flag and one label map for the family -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe Spike.Lib.A64.WakeLabels.wakeProg kp)
    (hW : ∀ w s c, D.Wi w s c → NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf exe kp) s c)
    (hcS : ∀ w, cS w = cSf)
    /- (instance data; `rfl` at `WakeInst.wakeQI`) the spawn records' labels
    are the instance's, and one map for the family -/
    (hSR : ∀ w, (SR w).lbl = (wakeSR w.1).lbl) (hlbl : ∀ w, (SR w).lbl = lbl')
    /- OPEN: the rows' memory sides read and write mapped words -/
    (hmp : ∀ w L wr, (D.ms w).mp L wr →
      Kernel.mapped (A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) wr L = true)
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    (hpl : PlaceW pcfg' (RuntimeLayout.ofPlaceW hp i).Λ po)
    (hpa : textProgram asm = .ok po.prog) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B asm
      (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff) D r0 r1) E (TiPre Ab Ac) :=
  wake_obligations_IW hp i hoff hC hx hC0 hstart O spawn hend hW hcS hmp hpl hpa
    (WakePostWit.post_wit_of rfl rfl (WakeQ.hwf_ofPlaceOK hp i)
      (fun w s c h => (hSR w).symm ▸ placed_I hp i w s c h)
      (fun w s c h => (hlbl w).symm ▸ Spike.Lib.A64.Flow.Worker.Wake.ZX.placed (hW w s c h).2))

/-- info: 'Spike.Lib.WakeAssemblyI.wake_obligations_IWP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_IWP

open Spike.Lib.A64.Flow.Worker (NNZ) in
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX) in
/-- **The assembly at main's instance and the worker's side**:
`wake_obligations_IWP` at `D := WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf`, `hW` by `WakeWorkerX.hW_I` and `hmp` by `WakeWorkerX.hmp_I` (see the
module doc). -/
theorem wake_obligations_IWW {Ab Ac : State → Prop}
    (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c →
      ∀ k a, ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ).abortAt k = some a → pcOf s ≠ a)
    /- the worker's side's data (`WakeWorkerX.wakeD`): the listing's
    executable, its end, labels `lbl'` and flag `cSf` of `wakeZX` -/
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
    (hC : WCompat (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff)
      (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) r0 r1) (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf)
      ((target (kernel 2) E).marks asm (RuntimeLayout.ofPlaceW hp i).Λ) (RuntimeLayout.ofPlaceW hp i).Λ arch)
    (hx : WCompatX (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff)
      (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) r0 r1)
      (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf))
    /- (its `relW0` is `WakeInst.relW0_I`) OPEN -/
    (hC0 : WakeM0.WCompat0 (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff)
      (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) r0 r1)
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
        (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff)
          (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) r0 r1).Post
          (RuntimeLayout.ofPlaceW hp i).Λ (afterClone abi d tid th stack tls r) s')
    /- `wakeZX`'s end; one flag for the family -/
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe Spike.Lib.A64.WakeLabels.wakeProg kp)
    (hcS : ∀ w, cS w = cSf)
    /- (instance data; `rfl` at `WakeInst.wakeQI`) the spawn records' labels
    are the instance's, and one map for the family -/
    (hSR : ∀ w, (SR w).lbl = (wakeSR w.1).lbl) (hlbl : ∀ w, (SR w).lbl = lbl')
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg' : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    (hpl : PlaceW pcfg' (RuntimeLayout.ofPlaceW hp i).Λ po)
    (hpa : textProgram asm = .ok po.prog) :
    WakeObligations arch (RuntimeLayout.ofPlaceW hp i).Λ B asm
      (WakeQ.wakeQ arch R1 _ SR cT cS pT P G (wakeM hp i ok lab _ hoff)
        (WakeWorkerX.wakeD hp i ok exe endPc kp lbl' cSf) r0 r1) E (TiPre Ab Ac) :=
  wake_obligations_IWP hp i hoff hC hx hC0 hstart O spawn hend (WakeWorkerX.hW_I hp i ok exe endPc kp lbl' cSf) hcS
    hSR hlbl (WakeWorkerX.hmp_I hp i ok exe endPc kp lbl' cSf) hpl hpa

/-- info: 'Spike.Lib.WakeAssemblyI.wake_obligations_IWW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations_IWW

end Spike.Lib.WakeAssemblyI
