/-
**hello.w's first `scc_rt_alloc_tcb` call inside `WSHX`, in the start's shape** (x86-64 only; the hello twin of
`Spike/Lib/X64WakeOwnStartG.lean`): `startTcbXH` composes `StartTcb.startTcb_WSH` (the call's node obligations
inside `WSH`) with `OwnSt.tcbXH` (inside `LftH`) at the callee's region `(R.callee (-8) (-296) 8).callee (-48 - 0)
(-184) 8` of `scc_rt_start`'s region `R` and the frame `F'` of the start's `htcb` premise
(`StartWf.startEW_W0SH`, `startEWP_W0SH`). The callee frame's band `BandT` comes from `R`'s offsets
`[-240, -48]` off the pool (wake's `OwnSt.bandT_of`, program independent).

- `startTcbXH`: the start's `htcb` inside `WSHX`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (its thread pointer is a register). Against x86-64 wake's
`OwnSt.startTcbX`: the producers are hello's (`StartTcb.startTcb_WSH`, `tcbXH`), the code is helloCells, the level
is `WSH`/`WSHX` and `hW` is about the worker's word `tcbWH L` (`pinA + 112`). Wake's `bandT_of` and `hoffP_of`
read no program and are used as they are (no twins).
-/
import Spike.Lib.X64HelloOwnStartTcb
import Spike.Lib.X64WakeOwnStartG

namespace Spike.Lib.X64.HelloPh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh (tcbM WSep inPc BandOffP)
open Spike.Lib.X64.WakePh.StartTcb (BandT)
open Spike.Lib.X64.Flow.Ret0 (TcbG TcbW)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Arena FragS Region)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl lbl' : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

set_option maxHeartbeats 1600000 in
/-- **`StartWf.startEWP_W0SH`'s `htcb` at `WSHX`**: the first `scc_rt_alloc_tcb` call (`n0 = 0`)
inside `WSHX` at any frame `F'` below `F`, from `StartTcb.startTcb_WSH` and `tcbXH`. -/
theorem startTcbXH (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    {c0 : Spike.Lib.Ctl} {rS : Range} {n0 : BitVec 64}
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])
    (hX0 : ∀ s, inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s → X0 s)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName) (hs : WSep L a) (hC0 : CFacts L.Λ lbl' c0)
    (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hband : BandOffP L R (-240) (-48))
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF L m) (hn0 : n0 = 0#64)
    (hoffP : ¬ (ar.heap ≤ L.pnA.toNat ∧ L.pnA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pnA, 8⟩ : Loc) ≠ ar.ctrLoc)
    (hoffH : ¬ (ar.heap ≤ L.pinA.toNat ∧ L.pinA.toNat < ar.heap + 16 * ar.cells) ∧
      (⟨L.pinA, 8⟩ : Loc) ≠ ar.ctrLoc) :
    ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      TcbW (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, n0, c0⟩ i := by
  intro F' _ _ hF' g hra
  have hbd := Spike.Lib.X64.WakePh.OwnSt.bandT_of hband
  have hR1 : (R.callee (-8) (-296) 8).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hR2 : ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8).OK :=
    Region.callee_ok hR1 (by show (-296 : Int) ≤ _; decide) (by decide) (by show _ < (8 : Int); decide) (by show _ ≤ (8 : Int); decide)
  have hFr' : ∀ m, F' m → Spike.Lib.X64.Rt.rtF L m := fun m h => hFr m (hF' m h)
  exact tcbXH hp hlab hsite hsep ha hW hbd hR2 (Int.le_refl _) (Int.le_refl _) hFr' ⟨g, n0, c0⟩ hn0 hra
    (Spike.Lib.X64.HelloPh.StartTcb.startTcb_WSH (rS := rS) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hC0
      hR2 (Int.le_refl _) (Int.le_refl _) hFr' ⟨g, n0, c0⟩ rfl hn0 hra hoffP hoffH)

end Spike.Lib.X64.HelloPh.OwnSt

/-- info: 'Spike.Lib.X64.HelloPh.OwnSt.startTcbXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSt.startTcbXH
