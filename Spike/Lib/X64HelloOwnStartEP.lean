/-
**hello.w's `scc_rt_start` lifted to `ownGHXW`, the take site's frame also `P`** (x86-64 only; the hello twin of
`Spike/Lib/X64WakeOwnStartEP.lean`): `StartWf.startEWP_W0SH`'s `Rt.StartEWFP … x8L P` inside `StartWf.WSH` (at
`ownGH`) is inside `WSHX` (at `ownGHXW`), given the two callees' states inside `WSHX`.

- `startEXPH`: `StartEWFP` inside `WSHX`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (its thread pointer is a register). Against x86-64 wake's
`OwnSt.startEXP`: the level is hello's (`WSH`/`WSHX`, `startLH`), `scc_rt_thread_init` returns to `.x8`
(`Rt.x8L`; wake's `.x7`), the code is helloCells and `hW` is about the worker's word `tcbWH L` (`pinA + 112`).
-/
import Spike.Lib.X64HelloOwnStartE
import Spike.Lib.X64WakeOwnStartEP

namespace Spike.Lib.X64.HelloPh.OwnSt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (swR)
open Spike.Lib.X64.WakePh (tcbM)
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

/-- **hello.w's `scc_rt_start` inside `WSHX`, the take site's frame also `P`** (`Rt.StartEWFP` at any `Fw`,
`scc_rt_thread_init` returning to `.x8`): `h` (inside `WSH`, `StartWf.startEWP_W0SH`) and the own nodes inside
`LftH` (`startLH`), the two callees' states inside `WSHX` (`htcbX`: `OwnSt.startTcbXH`; `htiX`:
`scc_rt_thread_init`'s `TiWAtP … x8L P`, `OwnSt.tiXPH`). The two nodes after the switch, at `Fw ∧ swFSL …`, are
`startLH`'s narrowed (`Ret0.nodeW_mono`, `Ret0.blkW_mono`). -/
theorem startEXPH (hlo : L.Λ.code.lo = lo) {rS : Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {D : Int}
    (hR : R.OK) (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hL : 8 ≤ D)
    (hok : (swR (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0 + 16384#64) (-D) 0).OK)
    (hoffP : ¬ (L.Λ.stackPool.lo < ((R.callee (-8) (-296) 8).addr (-48)).toNat ∧
      ((R.callee (-8) (-296) 8).addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (hrS : rS = ⟨(Spike.Lib.X64.Flow.Ret0.stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    {P : MachineData → Prop} {Fw : _root_.Mem 64 → Prop}
    (h : Spike.Lib.X64.Rt.StartEWFP (StartWf.WSH L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F Fw rS n0 k0 c0 D Spike.Lib.X64.Rt.x8L P)
    (htcbX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x0L).toBitVec → ∀ i,
      Spike.Lib.X64.Flow.Ret0.TcbW (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F' ⟨g, n0, c0⟩ i)
    (htiX : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable (Spike.Lib.X64.PhRec.K L rS) F' → (∀ m, F' m → F m) →
      ∀ g, g.ra = (L.lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ i,
      Spike.Lib.X64.Rt.TiWAtP (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe
        L.endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F' (Spike.Lib.X64.Flow.Ret0.StackM rS)
        ⟨g, Spike.Lib.X64.Flow.Ret0.pinA L.lab + n0 + 8#64, k0, c0⟩ Spike.Lib.X64.Rt.x8L P i) :
    Spike.Lib.X64.Rt.StartEWFP (WSHX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F Fw rS n0 k0 c0 D Spike.Lib.X64.Rt.x8L P := by
  have hw : ∀ s c, StartWf.WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c → LftH L a ar p Dt Cl Ctx lbl lsize frM X0 s c →
      WSHX L a ar p Dt Cl Ctx lbl lsize frM X0 s c := fun _ _ h1 h2 => h2 h1
  have hL' := startLH (ar := ar) (p := p) (Dt := Dt) (Cl := Cl) (Ctx := Ctx) (lbl := lbl) (lsize := lsize)
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

end Spike.Lib.X64.HelloPh.OwnSt

/-- info: 'Spike.Lib.X64.HelloPh.OwnSt.startEXPH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnSt.startEXPH
