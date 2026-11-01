/-
**Main's executable facts at the clone** (AArch64): `HelloWiI.hWiH_I`'s
`hX` — main's thread at its `clone` runs the layout's executable to its end with no declarations — from the
pre-spawn fragment at the record's placement (`HelloHPre.FrH`, `HPreH`'s clone facts; the shape `hMainRH_ofI`'s
`hpc` has, so `hX` is to gain the same `Fr lbl lsize th s` antecedent rather than `PreRH` a field): at a `clone`
call the fragment state is in the third level (`HelloHClW.pc_of_cloneH`, the first two levels never at the clone),
whose invariant `inv2H` gives `CloneInvH`, hence `ClonePostH`'s `At`, whose first three conjuncts are the facts.

- `hX_ofR`: `hX` with the `FrH Dd` antecedent, at any layout `L` of `helloProg` (`endH hp i = L.endPc` at
  `L := LH hp i` by `hprog`).
-/
import Spike.Lib.A64HelloHClWR
import Spike.Lib.A64HelloH2Inv
import Spike.Lib.HelloHPre

namespace Spike.Lib.HelloXOk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Entry Range)
open Scc.Sem.A64 (abi pcOf)
open Scc.Cert.Rt.A64 (endOf)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.WakeA64 (Cfg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HelloPreA (clonePcH H0StmtH H1StmtHF)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloSpawnR (PreRH)
open Spike.Lib.HelloO (ODataH IH)
open Spike.Lib.HelloH2Inv (inv2H cloneInv2_of)
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
  {a : Int64} {ls0 : Lsize}

/-- **`hWiH_I`'s `hX` from the pre-spawn fragment** (module doc). -/
theorem hX_ofR (hprog : L.prog = SccCode.helloProg)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) L.Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 L.Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Spike.Lib.HelloHPre.FrH Dd lbl lsize th s →
      th.st.exe = L.exe ∧ th.st.endPc = endOf L.exe SccCode.helloProg L.pfx ∧ th.st.decls = {} := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP _ _ hFr
  obtain ⟨th0, hd, -, hI⟩ := hFr
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := id hP
  have hpc := pc_of_cloneH hN hT hCl hI h4 h7
  rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ | ⟨l1, b1, n1, l', b', n', -, -, -, -, -, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
  rw [hinv2] at hi
  obtain ⟨-, t, l2, ws, ⟨R, F₂, tc, k, sl, me, cA, frp, -, ⟨he, hn, hdc, -⟩, -⟩, -⟩ := cloneInv2_of hi hpc
  exact ⟨he, by rw [hn, ← hprog], hdc⟩

end Rel

end Spike.Lib.HelloXOk

/-- info: 'Spike.Lib.HelloXOk.hX_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloXOk.hX_ofR
