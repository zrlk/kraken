/-
**hello.w on x86-64: main's segment end from the pre-spawn fragment** (the twin of
`Spike/Lib/A64HelloSegEnd.lean`): `X64HelloMainHRI.hMainRH_ofI`'s `hpc` (the per-clone premise of main's
invariant past the clone) from the level-2 fragment's clone state.

At a `clone` call (`SpawnPrem`) the fragment state at the record's placement (`FrH`) is at the clone's pc
(`X64HelloHClW.pc_of_cloneH`), so in the third level (`h0`'s and `h1`'s levels are never there), whose invariant
`X64HelloH2Inv.inv2H` gives `CloneInvH` (`ClonePostH`: the thread pointer, `%rsp` 224 below stack 0's top) and
the level's clone-state conjunct `X64HelloCloneSeg.CloneSegH` (`hseg`): `MainSegH`'s `At` in the widened region,
its base and the return address. `c`'s label is the record's `l` (`PreRH.hsp`'s `c` against `SpawnSrcH`'s),
placed at `%r15`, the cell `cA`.

- `hpc_ofR`: `hMainRH_ofI`'s `hpc` at any layout `L` of `helloCells` and `Fr := X64HelloHPre.FrH Dd` (the
  pre-spawn fragment at the record's placement), from the levels' statements, the fragment's nodes and take site,
  `hinv2` (`inv2 := inv2H`), `hseg` (`CloneSegH` at the level's clone states, `X64HelloSegEndX2.hseg_X2`) and
  `hfp` (the saved frame pointer at the level's clone states).

**Where this differs from AArch64** (forced by the x86-64 shape):
- x86-64's `MainSegH` has the frame pointer field `hfp : fp = ⟨Rm.base, -128, 40⟩.addr 80` (`JS`'s saved
  `%rbp` at slot `0`; AArch64 has none), which `CloneSegD` does not state, so `hpc_ofR` takes it open (`hfp`, at
  the level's clone states, for the clone's `At` in the widened region), as `X64WakeMainHRI.hMainR_I` does.
- The region is `⟨Rm.base, -128, 40⟩` (AArch64 `-144, 48`), the stacks bound at
  `(R.fp 8).addr 0 - 8 - 16` (`hMainRH_ofI`'s statement; AArch64 `R.addr (-32)`), the cell in `%r15` (AArch64
  `x13`), the code `helloCells` (AArch64 `helloProg`); `MainSegH` has no alignment field.
-/
import Spike.Lib.X64HelloCloneSeg
import Spike.Lib.X64HelloHClWF
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64HelloMainHRI
import Spike.Lib.X64HelloHPre

namespace Spike.Lib.X64HelloSegEnd

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Entry Range)
open Scc.Sem.X64 (abi pcOf)
open Scc.Cert.Rt.X64 (endOf)
open Spike.Lib (Arena FragS MemSide Region)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64ConsumerA (NodesA)
open Spike.Lib.X64ConsumerS (TakeSiteS)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (JS oP)
open Spike.Lib.X64HelloPreA (clonePcH cloneAtH H0StmtH H1StmtHF)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloMainHRD (MainSegH)
open Spike.Lib.X64HelloO (ODataH IH)
open Spike.Lib.X64HelloH2Inv (inv2H cloneInv2_of)
open Spike.Lib.X64HelloCloneSeg (CloneSegH)
open Spike.Lib.X64HelloHClW (pc_of_cloneH)

section Rel

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → Spike.Lib.Inv2Core.SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Spike.Lib.Inv2Core.Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : Spike.Lib.X64WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range} {asm : Scc.Sem.X64.Asm} {E : Entry}
  {μ : Marks} {Dd : ODataH} {L : RuntimeLayout} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isa} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isa}
  {Start : FragS isa} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {a : Int64} {ls0 : Lsize}

/-- **`hMainRH_ofI`'s `hpc` from the pre-spawn fragment** (module doc). -/
theorem hpc_ofR (hprog : L.prog = SccCode.helloCells)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0)
    /- the level's clone states carry `CloneSegH` (the fence's conjunct at the clone's pc) -/
    (hseg : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      CloneSegH L L.endPc s c)
    /- OPEN: the saved frame pointer at the level's clone states -/
    (hfp : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      ∀ (Rm : Region) (F₂ : MachineData → Prop) (cA fp ra tp : BitVec 64),
        At L.exe L.endPc ⟨Rm.base, -128, 40⟩ F₂ ⟨cloneAtH L.exe, oP, JS c cA fp ra tp⟩ s c →
        fp = (⟨Rm.base, -128, 40⟩ : Region).addr 80) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) L.Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 L.Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Spike.Lib.X64HelloHPre.FrH Dd lbl lsize th s →
      ∃ c Rm F₂ cA fp ra tp, MainSegH L.exe (endOf L.exe SccCode.helloCells L.pfx) th c Rm F₂ cA fp ra tp ∧
        lbl l = some cA.toNat ∧ tp = L.pinA + 0#64 + 8#64 ∧
        L.stacksA.toNat + 4096 ≤
          (((⟨Rm.base, -128, 40⟩ : Region).fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec).toNat := by
  intro d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l hP hrun hR hFr
  obtain ⟨th0, hd, hs, hI⟩ := hFr
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := id hP
  have hE : L.endPc = endOf L.exe SccCode.helloCells L.pfx := by rw [← hprog]
  -- the state is at the clone's pc, in the third level
  have hpc := pc_of_cloneH hN hT hCl hI h4 h7
  rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ | ⟨l1, b1, n1, l', b', n', -, -, -, -, rfl, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
  obtain ⟨Rm, F₂, cA, fp, ra, tp, hAt, hRb, hOK, -, hra, h15⟩ := hseg _ _ _ _ _ _ _ _ _ hi hpc
  have hfp' := hfp _ _ _ _ _ _ _ _ _ hi hpc Rm F₂ cA fp ra tp hAt
  rw [hinv2] at hi
  obtain ⟨-, t, l2, ws, ⟨-, -, -, -, -, -, -, -, -, -, -, hsp, htp, ht⟩, hS, h15l, -, -⟩ :=
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
  refine ⟨_, Rm, F₂, cA, fp, ra, tp, ⟨by rw [← hE]; exact hAt, hRb, hOK, hfp', hra⟩, ?_, ?_, ?_⟩
  · refine h15l.trans ?_
    rw [h15]
  · rw [← htpJ, ← hA.regs, htp, ht]
  · rw [Region.fp_addr, Region.addr]
    have hlo := hOK.lo
    dsimp only at hRb hlo
    have e8 : BitVec.ofInt 64 (8 + 0) = 8#64 := rfl
    have e16 : (16 : Int64).toBitVec = 16#64 := rfl
    rw [e8, e16]
    bv_omega

end Rel

end Spike.Lib.X64HelloSegEnd

/-- info: 'Spike.Lib.X64HelloSegEnd.hpc_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSegEnd.hpc_ofR
