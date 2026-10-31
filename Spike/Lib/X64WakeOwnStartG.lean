/-
**The first `scc_rt_alloc_tcb` call inside `WSX`, in `startEX`'s shape**
(x64): `startTcbX` composes `StartTcb.startTcb_WS` (the call's
node obligations inside `WS`) with `OwnSt.tcbX` (inside `Lft`) at the
callee's region `(R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8` of
`scc_rt_start`'s region `R` and the frame `F'` of `startEX`'s `htcbX`.

The callee frame's band `BandT` is reduced to a band of the caller's region
(`bandT_of`: `R`'s offsets `[-240, -48]` off the pool, `BandOffP L R (-240)
(-48)`); the x64 `StartPlace` twin discharges it at the entry region, as
A64's `offE`. `startEX`'s own `hoffP` is that band's `-56` word
(`hoffP_of`).

- `bandT_of`, `hoffP_of`: the bands.
- `startTcbX`: `htcbX`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnStartE
import Spike.Lib.X64WakeOwnStartTcb

namespace Spike.Lib.X64.WakePh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize CFacts)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib.X64.WakePh.StartTcb (BandT)
open Spike.Lib.X64.Flow.Ret0 (TcbG TcbW)
open Spike.Lib (Arena FragS Region)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl lbl' : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-- **The first `scc_rt_alloc_tcb` call's frame off the pool**, from
`scc_rt_start`'s offsets `[-240, -48]` off it. -/
theorem bandT_of (h : BandOffP L R (-240) (-48)) :
    BandT L ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) := fun k h1 h2 => by
  rw [Region.callee_addr, Region.callee_addr, show -8 + (-48 - 0 + k) = -56 + k by omega]
  exact h _ (by omega) (by omega)

/-- **`startEX`'s `hoffP`** from the same band. -/
theorem hoffP_of (h : BandOffP L R (-240) (-48)) :
    ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) := by
  rw [Region.callee_addr]; exact h _ (by decide) (by decide)

set_option maxHeartbeats 1600000 in
/-- **`startEX`'s `htcbX`**: the first `scc_rt_alloc_tcb` call (`n0 = 0`)
inside `WSX` at any frame `F'` below `F`, from `startTcb_WS` and `tcbX`. -/
theorem startTcbX (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
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
      TcbW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, n0, c0⟩ i := by
  intro F' _ _ hF' g hra
  have hbd := bandT_of hband
  have hR1 : (R.callee (-8) (-296) 8).OK := Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hR2 : ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8).OK :=
    Region.callee_ok hR1 (by show (-296 : Int) ≤ _; decide) (by decide) (by show _ < (8 : Int); decide) (by show _ ≤ (8 : Int); decide)
  have hFr' : ∀ m, F' m → Spike.Lib.X64.Rt.rtF L m := fun m h => hFr m (hF' m h)
  exact tcbX hp hlab hsite hsep ha hW hbd hR2 (Int.le_refl _) (Int.le_refl _) hFr' ⟨g, n0, c0⟩ hn0 hra
    (Spike.Lib.X64.WakePh.StartTcb.startTcb_WS (rS := rS) hp hlo hlab hsite hcl hc0 hpl0 hX0 hbd hΛ hs hC0
      hR2 (Int.le_refl _) (Int.le_refl _) hFr' ⟨g, n0, c0⟩ rfl hn0 hra hoffP hoffH)

end Spike.Lib.X64.WakePh.OwnSt

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.startTcbX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.startTcbX
