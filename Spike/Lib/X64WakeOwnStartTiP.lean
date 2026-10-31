/-
**The first `scc_rt_thread_init` call lifted to `ownGXW`, the take site's
frame also `P`** (x86-64; X64-OwnW lift layer, row X64-tiXP):
`Rt.TiWAtP … P` inside `StartWf.WS` (at `ownG`) is inside `WSX` (at
`ownGXW`), the `P` twin of `OwnSt.tiX` (`Spike/Lib/X64WakeOwnStartTi.lean`),
as `OwnSt.startEXP` is `startEX`'s.

The second obligation is `OwnSt.tiL`'s (`TiWAt` inside `Lft`, at `F`): the
nodes other than the take site are `TiWAt`'s / `TakeW`'s; the take site's
obligation, asked under `F ∧ P` in `TakeWP`, is `tiL`'s under `F` at the
same state (`At.monoF`).

- `At.monoF`: an `At` state at a narrower frame condition is one at a wider.
- `TakeWP.imp`, `TiWAtP.imp`: the `P` twins of `TakeW.imp`, `TiWAt.imp`
  (`Spike/Lib/X64WakeOwnImp.lean`), the second obligation `P`-free.
- `tiXP`: `TiWAtP` inside `WS` is inside `WSX`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnStartTi
import Spike.Lib.Rt.X64SegsA

namespace Spike.Lib.X64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (ND At)
open Spike.Lib.X64.Flow.Ret0 (TK TI TiG TakeG TakeW)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.StartTi (BandI)
open Spike.Lib (Arena FragS)

section Imp

variable {W W1 W2 : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- An `At` state at a narrower frame condition is one at a wider. -/
theorem At.monoF {F' : MachineData → Prop} {n : ND} {s : State} {c : Spike.Lib.Ctl}
    (h : At exe endPc R F' n s c) (hFF : ∀ m, F' m → F m) : At exe endPc R F n s c :=
  let ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  ⟨he, hn, hdc, hpc, σ, hA, hFF _ hD, hJ⟩

/-- **`TakeW.imp` with `P` at the take site**: the second obligation
`P`-free. -/
theorem TakeWP.imp {M P : MachineData → Prop} {q : TakeG} {i : TK}
    (h1 : Spike.Lib.X64.Rt.TakeWP W1 K exe endPc R F M q P i)
    (h2 : TakeW W2 (fun _ _ => False) exe endPc R F M q i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.TakeWP W K exe endPc R F M q P i := by
  cases i
  case site =>
    exact fun s c hA => hw s c (h1 s c hA) (h2 s c (At.monoF hA fun _ h => h.1))
  all_goals (dsimp only [Spike.Lib.X64.Rt.TakeWP] at h1 ⊢; exact TakeW.imp h1 h2 hw)

/-- **`TiWAt.imp` with `P` at the take site**: the second obligation
`P`-free. -/
theorem TiWAtP.imp {M P : MachineData → Prop} {q : TiG} {x : Label} {i : TI}
    (h1 : Spike.Lib.X64.Rt.TiWAtP W1 K exe endPc R F M q x P i)
    (h2 : Spike.Lib.X64.Rt.TiWAt W2 (fun _ _ => False) exe endPc R F M q x i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.TiWAtP W K exe endPc R F M q x P i := by
  cases i
  case call => exact fun g hg j => TakeWP.imp (h1 g hg j) (h2 g hg j) hw
  all_goals (dsimp only [Spike.Lib.X64.Rt.TiWAtP] at h1 ⊢; exact TiWAt.imp h1 h2 hw)

end Imp

namespace OwnSt

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`TiWAtP` inside `WS` is inside `WSX`** at the first
`scc_rt_thread_init` call (`tiL`), at any take-site condition `P`; the
premises are `tiX`'s. -/
theorem tiXP (hbdI : BandI L R (-248)) (hR : R.OK) (hRlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) {K : State → State → Prop} {M P : MachineData → Prop}
    (q : TiG) (htcb : q.tcb = tcbM L)
    (hunT : ∀ b ∈ Spike.Lib.X64.Rt.Ti.tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem b 8 = none)
    (hra : q.g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec)
    (h : ∀ i, Spike.Lib.X64.Rt.TiWAtP (WS L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M
      q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L P i) :
    ∀ i, Spike.Lib.X64.Rt.TiWAtP (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) K L.exe L.endPc R F M
      q Spike.Lib.X64.Flow.Ret0.ThreadInit.x7L P i := fun i =>
  TiWAtP.imp (h i) (tiL hp hlab hsite hsep ha hW hbdI hR hRlo hhi hFr q htcb hunT hra i) fun _ _ h1 h2 => h2 h1

end OwnSt

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.TiWAtP.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.TiWAtP.imp

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.tiXP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.tiXP
