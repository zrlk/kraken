/-
**`RootOpen.hst0` at `iW` without `hxa`** (wake.w, AArch64): `hst0_ofW`
with the child's stack `r1Of` carried unmapped along the start segment
(`KeepUn.SegW.keepUn`), so the box's landing gets the child's stack unmapped
from the segment itself, and `hxa` follows from `h1`'s
statement (`Hxa.box_landing`).

The start segment `StartH0G.wake_start_wc_h0W` runs at `msU`: `msBot E []`
with every allocation landing asked only with `r1Of` unmapped (`invU`);
`SegW.mono_xa` moves it to `KeepUn.unXa (msBot E []) r1Of`, `keepUn` (the
take of `rS0`, disjoint from `r1Of`, keeps it unmapped) back to
`msBot E []`, the entry's `U r1Of` discharged at the loaded thread
(`wideSt_threadAt`, `WakeOHinit.unowned_stack`) through `hst0_of`'s `Pe`,
beside the site frame `Pz rS0` (`StartH0R.pz_rS0_load`).

- `SegW.mono_xa`: a segment under a memory side with a larger allocation
  fragment.
- `hst0_ofU`: the statement; `wc_main`'s `hWp`/`hWs` are left at `msU`.
-/
import Spike.Lib.A64WakeHxa
import Spike.Lib.A64KeepUn
import Spike.Lib.A64OwnedPz
import Spike.Lib.WakeOHinit
import Spike.Lib.A64WakeStartPlaceLy

namespace Spike.Lib.A64.WakePh.StartH0U

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry Range)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS msOfA I2)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX wX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.KeepUn (U unXa)
open Spike.Lib (FragS SegW SegWS)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib.WakeOPremW (W0W)

/-- **A segment under a memory side with a larger allocation fragment**
(`Out.mono_xa` at every state of the invariant). -/
theorem SegW.mono_xa {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog} {lbl : Lbl}
    {ms ms' : MemSide isaLSE2} {P Q : Frag isaLSE2} (h : SegW W K p lbl ms P Q)
    (he : ms' = { ms with xa := ms'.xa }) (hxa : ∀ l b n s c, ms.xa l b n s c → ms'.xa l b n s c) :
    SegW W K p lbl ms' P Q := by
  obtain ⟨inv, hP, hW, hcl⟩ := h
  exact ⟨inv, hP, hW, fun s c hi =>
    ⟨fun hk => Spike.Lib.A64ConsumerA.Out.mono_xa ((hcl s c hi).1 hk) he hxa, (hcl s c hi).2⟩⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "MS" => Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []

/-- **`msBot E []`'s fragment asked only with the child's stack unmapped.** -/
abbrev invU (E : Entry) : Spike.Lib.A64ConsumerS.InvS := fun lbl lsize s c fs =>
  U R1 s → I2 (Spike.Lib.WakeOD.arW hp IW) (L0T (Ly).Λ) (ls0T (ls0 E)) (fun _ _ _ => False)
    (Spike.Lib.WakeRoot.inv1R hp IW ls0 Ctx E) lbl lsize s c fs

/-- **`msBot E fs` at `invU`.** -/
noncomputable abbrev msU (E : Entry) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  msOfA (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ) (fun _ => True)
    (Spike.Lib.WakeOG.gW hp IW (Spike.Lib.WakeHG.cTW hp IW))
    (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s)
    (Spike.Lib.WakeOD.arW hp IW) (invU hp ls0 Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) fs

set_option hygiene false in
local notation "MU" => msU hp ls0 Ctx E []

set_option hygiene false in
local notation "WSE" => Spike.Lib.A64.WakePh.StartWf.WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
  (Spike.Lib.WakeOD.arW hp IW) wakeSrc DtW (Spike.Lib.WakeOD.ClW hp IW) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
  (Spike.Lib.A64.WakeWf.X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))

set_option hygiene false in
/-- The start's fragment needed only at main's thread pointer (`WakeWc.tpG`). -/
local notation "TGE" => Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WSE)

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPW" => TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))

/-- **`RootOpen.hst0` at `iW`, `hxa` from `h1`'s statement**: the start
segment at `msU`, `keepUn` carrying `r1Of` unmapped, `hst0_of`'s `Pe` the
loaded thread's `Pz rS0` and `U r1Of`; `hxa` by `Hxa.box_landing` at `U`. -/
theorem hst0_ofU (E : Entry) (hE : E.Ok (Ly).Λ)
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    {F0 : MachineData → Prop} (h1 : Spike.Lib.WakeRoot.H1R hp IW ls0 Ctx MS F0 E)
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m → F0 m)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (TGE) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MU (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC) ((JW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (TGE) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MU (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC)) :
    SegWS (W0W hp IW E DtW (Ctx E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW))
      wakeSrc (L0T (Ly).Λ) (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E)
      (Spike.Lib.WakeRoot.StartP hp IW E) (fun _ _ _ => False) := by
  -- the ranges: `r1Of` in the pool, disjoint from `rS0`, both in the address space
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp IW hA13
  have hbd' : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
    rw [(Ly).lab_stacks]; exact Spike.Lib.WakeHClW.hbd_W hp IW hsub1
  obtain ⟨h1l, h1s⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hst := (Ly).stacks_sub
  have hpf := (Ly).pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  -- `hxa` at `msU`: the landing is a `Box` given `U r1Of`
  have hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
        (bX MU (Ly).lab ((JW) σC) l A) s c → TPW s → (MU).xa l A 1 s c := by
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
    exact Spike.Lib.A64.WakePh.Hxa.box_landing hp ls0 Ctx E hA13 hF0 hA' htp hU
  -- the start segment at `msU`, then at `unXa (msBot E []) r1Of`, then `keepUn`
  have hG0 := Spike.Lib.A64.WakePh.StartH0G.wake_start_wc_h0W hp IW (I := invU hp ls0 Ctx E) (pS := wakeSrc)
    hE hpa hwp hlo0 hstat hA13 hpin2 hctrD hc (Spike.Lib.WakeImmsC0.placedSE_c0WW hp)
    (Spike.Lib.A64.WakeC0CF.cfacts_c0WW hp)
    hWp hWs hxa
  have hG1 := (SegW.mono_xa (ms' := unXa MS R1) hG0 rfl fun _ _ _ _ _ h hU => ⟨h.1, h.2 hU⟩)
  have hG := Spike.Lib.A64.KeepUn.SegW.keepUn rfl hG1 fun _ _ _ s' hk hs => by
    obtain ⟨-, pm, rfl⟩ := hk; exact Spike.Lib.A64.KeepUn.take_un pm hd hw1 hwS hs
  refine Spike.Lib.A64.WakePh.StartH0B.hst0_of hp IW ls0 Ctx frM E hE hpa hwp hlo0
    (Spike.Lib.WakeImmsC0.placedSE_start2W hp) (Pe := fun s => Spike.Lib.A64Consumer.Pz RS s.st.1 ∧ U R1 s)
    ⟨Spike.Lib.A64.WakePh.StartH0R.pz_rS0_load hp E hE,
      Scc.Cert.WideA64.wideSt_threadAt (PlaceW.wideIn_of_placeW hp) E _ _,
      Spike.Lib.WakeOHinit.unowned_stack hp IW hE.1 hsub1 hw1 _ rfl⟩
    ((hG.mono_pre fun _ _ ⟨h, hz, hu⟩ => ⟨⟨h, hz⟩, hu⟩).mono_post fun s c hQ => ?_)
    (Spike.Lib.A64.WakePh.StartH0C.wake_hab_closed hp IW hpa hwp hlo0 (Spike.Lib.WakeImmsC0.placedSE_c0WW hp))
  obtain ⟨⟨v, m0, σC, ⟨he, hn, hdc, hpc, σ, hAb, hD, h0, h30, q, hq, hJ⟩, htp⟩, -⟩ := hQ
  refine ⟨v, m0, σC, ?_, htp⟩
  exact ⟨he, hn, hdc, hpc, σ, hAb, hD, h0, h30, ⟨q.1, { q.2 with toS := { q.2.toS with } }⟩, hq, hJ⟩

end Spike.Lib.A64.WakePh.StartH0U

/-- info: 'Spike.Lib.A64.WakePh.StartH0U.hst0_ofU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0U.hst0_ofU
