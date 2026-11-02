/-
**hello.w's first `scc_rt_thread_init` call lifted to `ownGHXW`, the take site's frame also `P`** (x86-64 only;
the hello twin of `Spike/Lib/X64WakeOwnStartTiP.lean`): `Rt.TiWAtP … x8L P` inside `StartWf.WSH` (at `ownGH`,
`StartTi.startTi_WSPH`) is inside `WSHX` (at `ownGHXW`). The second obligation is `OwnSt.tiLH`'s (`TiWAt` inside
`LftH`, at `F`); the take site's obligation, asked under `F ∧ P` in `TakeWP`, is `tiLH`'s under `F` at the same
state (wake's `TiWAtP.imp`, generic).

- `tiXPH`: `TiWAtP` inside `WSH` is inside `WSHX`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (its thread pointer is a register). Against x86-64 wake's
`OwnSt.tiXP`: the level is hello's (`WSH`/`WSHX`, `tiLH`), `scc_rt_thread_init` returns to `.x8` (`Rt.x8L`; wake's
`.x7`), the code is helloCells and `hW` is about the worker's word `tcbWH L` (`pinA + 112`). Wake's `At.monoF`,
`TakeWP.imp` and `TiWAtP.imp` are program independent and used as they are.
-/
import Spike.Lib.X64HelloOwnStartTi
import Spike.Lib.X64WakeOwnStartTiP

namespace Spike.Lib.X64.HelloPh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout x8L)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.Flow.Ret0 (TiG)
open Spike.Lib.X64.WakePh (tcbM)
open Spike.Lib.X64.WakePh.StartTi (BandI)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`TiWAtP` inside `WSH` is inside `WSHX`** at the first `scc_rt_thread_init` call (`tiLH`), at any take-site
condition `P`. -/
theorem tiXPH (hbdI : BandI L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {K : State → State → Prop} {M P : MachineData → Prop}
    (q : TiG) (htcb : q.tcb = tcbM L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec)
    (h : ∀ i, Spike.Lib.X64.Rt.TiWAtP (StartWf.WSH L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M
      q x8L P i) :
    ∀ i, Spike.Lib.X64.Rt.TiWAtP (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M
      q x8L P i := fun i =>
  Spike.Lib.X64.WakePh.TiWAtP.imp (h i) (tiLH hp hlab hsite hsep ha hW hbdI hR hRlo hhi hFr q htcb hunT hra i)
    fun _ _ h1 h2 => h2 h1

end Spike.Lib.X64.HelloPh.OwnSt

/-- info: 'Spike.Lib.X64.HelloPh.OwnSt.tiXPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSt.tiXPH
