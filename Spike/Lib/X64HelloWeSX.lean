/-
**hello.w on x86-64: the state at `wc_rodata`'s entry after `call wc_rodata` inside the start's level at
`ownGHXW`** (x86-64 only; the `ownGHXW` instance of `Spike/Lib/X64HelloWeS.lean`, as `X64HelloRdWfSFX` is
`X64HelloRdWfSF`'s): a state at `Hello1.mNC` is inside `WSHFg (ownGHXW L a) … []`, so inside
`StartWcS.WSg (ownGHXW L a) … []`.

The proof is `WeS.hWe_W0SH`'s, through `RdWfSFX.proW_rdWSHX` in place of `RdWfSF.proW_rdWSHF`: the state is the
prologue's first block at its first instruction (`WeS.blkW_at0`) at the entry invariant `WeS.rdJe`, placed at every
state (`hpl0`, `WeS.proW_ofCtl`).

- `hWe_W0SHX`: `mNC`'s states inside `WSHFg (ownGHXW L a) … []`.
- `hWe_WSX`: the same at `StartWcS.WSg (ownGHXW L a) … []`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against `X64HelloWeS`: the level is at `ownGHXW L a`, and
the premises `hsep`, `ha`, `hW` (`ownGHXW`'s separation) and `hb` (`wc_rodata`'s region's band on the pool) are
new, as `RdWfSFX.proW_rdWSHX` asks them (discharged at the root as `HrdRootX.hrd_RX` does).
-/
import Spike.Lib.X64HelloWeS
import Spike.Lib.X64HelloRdWfSFX

namespace Spike.Lib.X64.HelloPh.WeSX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.WakeWf (RunWf)
open Spike.Lib.X64.HelloPh (ownGHXW)
open Spike.Lib.X64.HelloPh.WcW (freeNH)
open Spike.Lib.X64.HelloWf (WSHFg)
open Spike.Lib.X64.HelloPh.WeS (msT rdJe blkW_at0 proW_ofCtl)
open Spike.Lib.X64.Flow.Hello1 (mNC mR mF)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Arena FragS Ctl Region)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

section Hello

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = Spike.Lib.X64.HelloPh.lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hX0 : ∀ s, freeNH (pcOf s) = true → X0 s)
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE L.Λ lbl s c0 [])

include hp hlo hΛ hlab hsite hcl hX0 hc0 hpl0

/-- **`mNC`'s states inside `WSHFg (ownGHXW L a)`** (`WeS.hWe_W0SH` through `RdWfSFX.proW_rdWSHX`): `hWe_W0SH`'s
premises, `ownGHXW`'s separation (`hsep`, `ha`, `hW`), and the band of `wc_rodata`'s region `mR R` on the pool
(`hb`). -/
theorem hWe_W0SHX (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hb : BandOnP L (mR R) (-208) 8)
    (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J : FAS → Ctl → Prop} {tp : UInt64} (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    ∀ s c, At L.exe L.endPc R F (mNC L.lab R J) s c →
      WSHFg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 [] s c := by
  intro s c h
  obtain ⟨m0, σC, hA⟩ := Spike.Lib.X64.at_enter (e0 := 0) (lo' := -208) (hi' := 8)
    (show R.lo ≤ (mNC L.lab R J).o.sp - 0 + -208 by simp only [mNC]; omega)
    (show (mNC L.lab R J).o.sp - 0 + 8 ≤ R.hi by simp only [mNC]; omega)
    (show ((mNC L.lab R J).o.sp - 0) % 8 = 0 by simp only [mNC]; decide) h
  have hmR : (mR R).OK := Spike.Lib.Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have hctl : ∀ σ c', rdJe L.lab R J c σC σ c' → c' = c0 := by
    rintro σ c' ⟨rfl, -, σe, hJe, -⟩
    exact (hJ σe c' hJe).1
  have hpro := Spike.Lib.X64.HelloPh.RdWfSFX.proW_rdWSHX (fs := []) (a := a) (rS := ⟨0, 0⟩) (ar := ar) (p := p)
    (Dt := Dt) (Ctx := Ctx) (lsize := lsize) (frM := frM) (lbl := lbl) (ms := msT)
    (F := mF R F m0 σC) hp hlo hΛ hlab hsite hcl hX0 (.inl rfl) hsep ha hW hb hmR
    (by simp only [mR, Region.callee]; omega) (by simp only [mR, Region.callee]; omega)
    (J0 := rdJe L.lab R J c σC) (tp := tp)
    (by
      rintro σ c' ⟨-, rfl, σe, hJe, -, -, -, -, ht, -, -⟩
      exact ht.trans (hJ σe c hJe).2)
    hmr (fun m hm => hun m hm.1)
    (fun σ c' h => by rw [hctl σ c' h]; exact ⟨fun _ => hc0.1, hc0.2⟩)
    (proW_ofCtl fun σ c' h s => by rw [hctl σ c' h]; exact hpl0 s)
  exact blkW_at0 hpro.w0 (by decide) hA

/-- **`hWe_W0SHX` at the start's level with frames** (`StartWcS.WSg (ownGHXW L a) … []`). -/
theorem hWe_WSX (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (hb : BandOnP L (mR R) (-208) 8)
    (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J : FAS → Ctl → Prop} {tp : UInt64} (hJ : ∀ σ c, J σ c → c = c0 ∧ σ.regs.fsBase = tp)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 L.Λ) false ⟨Spike.Lib.X64.Flow.Ret0.limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    ∀ s c, At L.exe L.endPc R F (mNC L.lab R J) s c →
      Spike.Lib.X64.HelloPh.StartWcS.WSg (ownGHXW L a) L ar p Dt Cl Ctx lbl lsize frM X0 s c [] :=
  hWe_W0SHX hp hlo hΛ hlab hsite hcl hX0 hc0 hpl0 hsep ha hW hb hR hRlo hhi hJ hmr hun

end Hello

end Spike.Lib.X64.HelloPh.WeSX

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WeSX.hWe_W0SHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeSX.hWe_W0SHX

/-- info: 'Spike.Lib.X64.HelloPh.WeSX.hWe_WSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeSX.hWe_WSX
