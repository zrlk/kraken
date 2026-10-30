/-
**The counter add's tail with the child's stack unmapped** (wake.w, AArch64):
`RootUL.HLandU` from `wc_main`'s `hWp`/`hWs` at `StartH0U.msU` (as
`StartH0U.hst0_ofU` takes them), with no `hUn1`.

- `hland_RU`: `Land.hland_seg` at `msU … CtxR`, its `hxa` from `h1`'s
  statement (`Hxa.box_landing` at `U r1Of`); moved to
  `unXa (msBot E []) r1Of` (`SegW.mono_xa`) and `keepUn` (the take of `rS0`
  keeps `r1Of` unmapped); then `Land5.inv0_of_habW`.
-/
import Spike.Lib.A64WakeLand4
import Spike.Lib.A64WakeRootUL

namespace Spike.Lib.A64.WakePh.RootUL

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakeWf (DtW X0W)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "MS" => Spike.Lib.WakeRoot.msBot hp IW ls0 (Land.CtxR hp IW ls0) E []

set_option hygiene false in
local notation "MU" => Spike.Lib.A64.WakePh.StartH0U.msU hp ls0 (Land.CtxR hp IW ls0) E []

set_option hygiene false in
local notation "TGE" => Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))
  (WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp IW) wakeSrc DtW
    (Spike.Lib.WakeOD.ClW hp IW) (Land.CtxR hp IW ls0 E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
    (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E)))

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

/-- **`HLandU` at `IW`** from `msU`-form `hWp`/`hWs` and `h1`'s statement
(no `hUn1`): `hland_seg` at `msU`, `keepUn`, `inv0_of_habW`. -/
theorem hland_RU (E : Entry) (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    {F0 : MachineData → Prop} (h1 : Spike.Lib.WakeRoot.H1R hp IW ls0 (Land.CtxR hp IW ls0) MS F0 E)
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m → F0 m)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (TGE) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MU (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC) ((JW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (TGE) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MU (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC)) :
    HLandU hp ls0 frM E := by
  -- the ranges: `r1Of` in the pool, disjoint from `rS0`
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp IW hA13
  have hbd' : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
    rw [(Ly).lab_stacks]; exact Spike.Lib.WakeHClW.hbd_W hp IW hsub1
  obtain ⟨h1l, h1s⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  -- `hxa` at `msU`: the landing is a `Box` given `U r1Of` (`hst0_ofU`'s)
  have hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
        (bX MU (Ly).lab ((JW) σC) l A) s c → TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) s →
        (MU).xa l A 1 s c := by
    intro v m0 σC l A s c hl hA htp
    obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, q, hq1, hq2, hq3⟩ := hA
    have hA' : At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
        (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (bX MS (Ly).lab ((JW) σC) l A) s c :=
      ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hq1, hq2, hq3⟩
    obtain ⟨-, -, -, -, -, -, -, q', -, -, -, ob, hAo, hlt⟩ := id hA'
    have hf : (MS).off 1 q'.1.τ = 8 := Spike.Lib.LowerA64.arOf_off_eq (Λ := (Ly).Λ) q'.2.toS.accs
    have hu : 1 ≤ (MS).units 1 q'.1.τ := Spike.Lib.LowerA64.arOf_units_pos (Λ := (Ly).Λ) q'.2.toS.accs
    have hcl : (MS).cells = 4194304 := rfl
    have hAL : Spike.Lib.HeapLand.AllocLand (Spike.Lib.WakeOD.arW hp IW).heap
        (Spike.Lib.WakeOD.arW hp IW).cells A 1 := by
      show (MS).heap + 8 ≤ A ∧ A + 8 * 1 ≤ (MS).heap + 16 * (MS).cells ∧ 1 + 1 ≤ (MS).cells
      rw [hf] at hAo; omega
    refine ⟨hAL, fun hU => .inr ⟨l, A, 1, hl, hAL, rfl, rfl, (h1 l A 1 hl hAL).2.1 s c ?_⟩⟩
    exact Spike.Lib.A64.WakePh.Hxa.box_landing hp ls0 (Land.CtxR hp IW ls0) E hA13 hF0 hA' htp hU
  intro ms0 R F q hms hG hok s c hAt htp hu
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { Land.refW hp IW ls0 E with xa := X } := ⟨_, hms⟩
  obtain ⟨v, m0, σC, rfl, rfl, hra⟩ := hG
  have hS := Land.hland_seg hp ls0 frM E (ms := MU) rfl hpa hwp hlo0 hc hWp hWs hxa v m0 σC q
    { hok.okb with toS := { hok.okb.toS with } } hra
  have hS1 := Spike.Lib.A64.WakePh.StartH0U.SegW.mono_xa (ms' := unXa MS R1) hS rfl
    fun _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩
  have hS2 := Spike.Lib.A64.KeepUn.SegW.keepUn rfl hS1 fun _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hwS hs
  exact Spike.Lib.A64.WakePh.Land5.inv0_of_habW hp ls0 (Land.CtxR hp IW ls0) frM E hpa hwp hlo0
    (hS2.mono_post fun _ _ h => h.1) s c ⟨⟨hAt, htp⟩, hu⟩

end Spike.Lib.A64.WakePh.RootUL

/-- info: 'Spike.Lib.A64.WakePh.RootUL.hland_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.RootUL.hland_RU
