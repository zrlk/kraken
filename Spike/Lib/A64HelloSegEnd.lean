/-
**Main's segment end from the pre-spawn fragment** (AArch64): `HelloMainHRI.hMainRH_ofI`'s
`hpc` (the one per-clone premise of main's invariant past the clone) from the level-2 fragment's clone state.

At a `clone` call (`SpawnPrem`) the fragment state at the record's placement (`FrH`) is at the clone's pc
(`HelloHClW.pc_of_cloneH`), so in the third level (`h0`'s and `h1`'s levels are never there), whose invariant
`HelloH2Inv.inv2H` gives `CloneInvH` (`ClonePostH`: the thread pointer, `sp` 224 below stack 0's top) and the level's
clone-state conjunct `HelloCloneSeg.CloneSegH` (`hseg`): `MainSegH`'s `At` in the widened region, its base, alignment
and the return address. `c`'s label is the record's `l` (`PreRH.hsp`'s `c` against `SpawnSrcH`'s), placed at `x13`,
the cell `cA`.

- `hpc_ofR`: `hMainRH_ofI`'s `hpc` at any layout `L` of `helloProg` and `Fr := HelloHPre.FrH Dd` (the pre-spawn
  fragment at the record's placement, `HPreH`'s clone facts), from the levels' statements, the fragment's nodes and
  take site, `hinv2` (`inv2 := inv2H`) and `hseg` (`CloneSegH` at the level's clone states,
  `HelloSegEndX2.hseg_X2`).
-/
import Spike.Lib.A64HelloCloneSeg
import Spike.Lib.A64HelloHClWF
import Spike.Lib.A64HelloH2Inv
import Spike.Lib.HelloMainHRI
import Spike.Lib.HelloHPre

namespace Spike.Lib.HelloSegEnd

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Entry Range Inv1)
open Scc.Sem.A64 (abi pcOf)
open Scc.Cert.Rt.A64 (endOf)
open Spike.Lib (Arena FragS MemSide Region)
open Spike.Lib.WakeA64 (Cfg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HelloPreA (clonePcH CloneInvH ClonePostH H0StmtH H1StmtHF H2StmtH)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.HelloO (ODataH IH)
open Spike.Lib.HelloH2Inv (inv2H cloneInv2_of)
open Spike.Lib.HelloCloneSeg (CloneSegH)
open Spike.Lib.HelloHClW (pc_of_cloneH)

section Rel

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → Spike.Lib.Inv2Core.SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Spike.Lib.Inv2Core.Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : Spike.Lib.WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range} {asm : String} {E : Entry}
  {μ : Marks} {Dd : ODataH} {L : RuntimeLayout} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isaLSE2} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isaLSE2}
  {Start : FragS isaLSE2} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {a : Int64} {ls0 : Lsize}

/-- **`hMainRH_ofI`'s `hpc` from the pre-spawn fragment** (module doc). -/
theorem hpc_ofR (hprog : L.prog = SccCode.helloProg)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0)
    /- the level's clone states carry `CloneSegH` (the fence's conjunct at the clone's pc) -/
    (hseg : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      CloneSegH L L.endPc s c) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) L.Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 L.Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Spike.Lib.HelloHPre.FrH Dd lbl lsize th s →
      ∃ c Rm F₂ cA x29 ra tp, MainSegH L.exe (endOf L.exe SccCode.helloProg L.pfx) th c Rm F₂ cA x29 ra tp ∧
        lbl l = some cA.toNat ∧ tp = L.pinA + 0#64 + 8#64 ∧
        L.stacksA.toNat + 4096 ≤ ((⟨Rm.base, -144, 48⟩ : Region).addr (-32)).toNat := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨th0, hd, hs, hI⟩ := hFr
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := id hP
  have hE : L.endPc = endOf L.exe SccCode.helloProg L.pfx := by rw [← hprog]
  -- the state is at the clone's pc, in the third level
  have hpc := pc_of_cloneH hN hT hCl hI h4 h7
  rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ | ⟨l1, b1, n1, l', b', n', -, -, -, -, rfl, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
  obtain ⟨Rm, F₂, cA, x29, ra, tp, hAt, hRb, hOK, hal, hra, h13⟩ := hseg _ _ _ _ _ _ _ _ _ hi hpc
  rw [hinv2] at hi
  obtain ⟨-, t, l2, ws, ⟨-, -, -, -, -, -, -, -, -, -, -, hsp, htp, ht⟩, hS, h13l, -, -⟩ :=
    cloneInv2_of hi hpc
  -- `c`'s label is the record's
  obtain ⟨th0', ws', hs', hc, -⟩ := hR.hsp
  obtain rfl : th0 = th0' := by rw [hs] at hs'; simpa using hs'
  have hl : l2 = l := by
    have h := hS.2.2.1
    rw [hc] at h
    obtain ⟨-, h⟩ := Prod.mk.inj (Option.some.inj h)
    cases (List.cons.inj h).1
    rfl
  subst hl
  -- `tp` is the thread pointer
  obtain ⟨-, -, -, -, σ, hA, -, -, -, -, -, htpJ⟩ := id hAt
  refine ⟨_, Rm, F₂, cA, x29, ra, tp, ⟨by rw [← hE]; exact hAt, hRb, hOK, hal, hra⟩, ?_, ?_, ?_⟩
  · refine h13l.trans ?_
    show some th.st.st.1.regs.X13.toBitVec.toNat = _
    rw [h13]
  · rw [← htpJ, ← hA.regs, htp, ht]
  · have hb := Region.addr_toNat_of (R := ⟨Rm.base, -144, 48⟩) hOK (k := -32) (show (-144 : Int) ≤ -32 by decide) (show (-32 : Int) < 48 by decide)
    have hlo := hOK.lo
    dsimp only at hb hlo
    omega

end Rel

end Spike.Lib.HelloSegEnd

/-- info: 'Spike.Lib.HelloSegEnd.hpc_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSegEnd.hpc_ofR
