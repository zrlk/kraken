/-
**wake.w's `scc_rt_start` lifted to `ownGXW`, the take site's frame also
`P`** (x86-64; X64-OwnW lift layer): `StartWf.startEWP_W0S`'s
`Rt.StartEWFP` inside `StartWf.WS` (at `ownG`) is inside `WSX` (at
`ownGXW`), given the two callees' states inside `WSX` (`htcbX`:
`scc_rt_alloc_tcb`; `htiX`: `scc_rt_thread_init` as `TiWAtP … P`), the
`P` twin of `OwnSt.startEX` (`Spike/Lib/X64WakeOwnStartE.lean`).

The own nodes are `OwnSt.startL`'s (`StartLft`, inside `Lft`, at any frame
condition); the two nodes after the switch, at `Fw ∧ swFSL …` in
`SwEWF`, are `startL`'s at `swFSL …` narrowed (`Ret0.nodeW_mono`,
`Ret0.blkW_mono`), as `startEWP_W0S` narrows `startEW_W0S`'s.

- `startEXP`: `StartEWFP` inside `WSX`.

**Deviations.** None: a new lemma. `OwnSt.startEX`'s proof was split into
`StartLft`/`startL` (its own nodes inside `Lft`) and the combination, so
that `startEXP` reuses the node proofs; `startEX`'s statement is unchanged.
-/
import Spike.Lib.X64WakeOwnStartE
import Spike.Lib.Rt.X64StartEFA

namespace Spike.Lib.X64.WakePh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Spike.Lib (Arena FragS)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **wake.w's `scc_rt_start` inside `WSX`, the take site's frame also
`P`** (`Rt.StartEWFP` at any `Fw`): `h` (inside `WS`,
`StartWf.startEWP_W0S`) and the own nodes inside `Lft` (`startL`), the two
callees' states inside `WSX` (`htcbX`, `htiX`: `scc_rt_thread_init`'s
`TiWAtP … P`). The premises on the region and the new stack are
`startEX`'s. -/
theorem startEXP (hlo : L.Λ.code.lo = lo) {rS : Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {D : Int}
    (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hL : 8 ≤ D)
    (hok : (swR (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64) (-D) 0).OK)
    (hoffP : ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (hrS : rS = ⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    {P : MachineData → Prop} {Fw : _root_.Mem 64 → Prop}
    (h : Spike.Lib.X64.Rt.StartEWFP (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F Fw rS n0 k0 c0 D Spike.Lib.X64.Rt.Code.Ti.x7L P)
    (htcbX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, n0, c0⟩ i)
    (htiX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, Spike.Lib.X64.Flow.Ret0.pinA L.lab + n0 + 8#64, k0, c0⟩ Spike.Lib.X64.Rt.Code.Ti.x7L P i) :
    Spike.Lib.X64.Rt.StartEWFP (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F Fw rS n0 k0 c0 D Spike.Lib.X64.Rt.Code.Ti.x7L P := by
  have hw : ∀ s c, WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c → Lft L a ar p Dt Cl Ctx lbl lsize frM X0 s c →
      WSX L a ar p Dt Cl Ctx lbl lsize frM X0 s c := fun _ _ h1 h2 => h2 h1
  have hL' := startL (ar := ar) (p := p) (Dt := Dt) (Cl := Cl) (Ctx := Ctx) (lbl := lbl) (lsize := lsize)
    (frM := frM) (X0 := X0) (F := F) (n0 := n0) (c0 := c0) hp hlab hsite hsep ha hW hlo hR hRlo hhi hL hok
    hoffP hrS hsub
  exact ⟨Spike.Lib.X64.WakePh.EntryW.imp h.e hL'.e hw, fun F' hFs hKs hF' =>
    ⟨⟨Spike.Lib.X64.WakePh.XStartW.imp (h.s F' hFs hKs hF').s1.start (hL'.start F') hw,
      Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s1.blk (hL'.blk F') hw, htcbX F' hFs hKs hF'⟩,
    ⟨Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s2.b0 (hL'.b0 F') hw, htiX F' hFs hKs hF',
      Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s2.fs (hL'.fs F') hw,
      Spike.Lib.X64.AllocG.NodeW.imp (h.s F' hFs hKs hF').s2.sys (hL'.sys F') hw,
      Spike.Lib.X64.AllocG.BlkW.imp (h.s F' hFs hKs hF').s2.sw (hL'.sw F') hw⟩,
    ⟨Spike.Lib.X64.AllocG.NodeW.imp (h.s F' hFs hKs hF').s3.sw (hL'.s3 F').sw hw,
      fun v => Spike.Lib.X64.AllocG.NodeW.imp ((h.s F' hFs hKs hF').s3.xor v)
        (Spike.Lib.X64.Flow.Ret0.nodeW_mono ((hL'.s3 F').xor v) fun _ h => h.2) hw,
      fun v => Spike.Lib.X64.AllocG.BlkW.imp ((h.s F' hFs hKs hF').s3.blk v)
        (Spike.Lib.X64.Flow.Ret0.blkW_mono ((hL'.s3 F').blk v) fun _ h => h.2) hw⟩⟩⟩

end Spike.Lib.X64.WakePh.OwnSt

/-- info: 'Spike.Lib.X64.WakePh.OwnSt.startEXP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.OwnSt.startEXP
