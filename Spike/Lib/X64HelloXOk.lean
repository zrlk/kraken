/-
**Main's executable facts at the clone** (x86-64; the twin of `Spike/Lib/HelloXOk.lean`): `X64HelloWiI.hWiH_I`'s
`hX` — main's thread at its `clone` runs the layout's executable to its end with no declarations — from the
pre-spawn fragment at the record's placement (`X64HelloHPre.FrH`, `HPreH`'s clone facts): at a `clone` call the
fragment state is in the third level (`X64HelloHClW.pc_of_cloneH`, the first two levels never at the clone), whose
invariant `inv2H` gives `CloneInvH`, hence `ClonePostH`'s `At`, whose first three conjuncts are the facts.

- `hX_ofR`: `hX` with the `FrH Dd` antecedent, at any layout `L` of `helloCells` (`endH hp i = L.endPc` at
  `L := LH hp i` by `hprog`).
- `hexe_of`: the executable conjunct alone from `SpawnPrem` (`hello_obligations_RSg`'s `hexe`), the fragment
  state read off the relation's pre-exit disjunct (`RSAH`; its post-exit disjunct contradicts `SpawnPrem`'s
  `exited = none`).

## Unlike AArch64

- The layout's program is the cell list `SccCode.helloCells` (AArch64 `helloProg`), and the instruction set `isa`.
- The second level's statement `H1StmtHF` is `X64HelloWcInv3F`'s (its segment a `SegInvSP`); only its
  never-at-the-clone conjunct is read.
-/
import Spike.Lib.X64HelloHClWR
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64HelloHPre
import Spike.Lib.X64HelloWcInv3F

namespace Spike.Lib.X64HelloXOk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Entry Range)
open Scc.Sem.X64 (abi pcOf)
open Scc.Cert.Rt.X64 (endOf)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64HelloPreA (clonePcH H0StmtH H1StmtHF)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloO (ODataH IH)
open Spike.Lib.X64HelloH2Inv (inv2H cloneInv2_of)
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

/-- **`hWiH_I`'s `hX` from the pre-spawn fragment** (module doc). -/
theorem hX_ofR (hprog : L.prog = SccCode.helloCells)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0)
    (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ l,
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) L.Λ asm E 0 d s th stack tls r →
      (helloS arch).Run s [] s' →
      PreRH arch R1 SR cT cS pT Pa G passT M D r0 r1 L.Λ w d th stack s s' s0 s1 lbl lsize ts j own₀ l →
      Spike.Lib.X64HelloHPre.FrH Dd lbl lsize th s →
      th.st.exe = L.exe ∧ th.st.endPc = endOf L.exe SccCode.helloCells L.pfx ∧ th.st.decls = {} := by
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

/-- **The executable at main's clone from `SpawnPrem` alone** (module doc): `Q.R1` gives `RSAH` at `IH Dd`; before
the exit, main's one thread is `SpawnPrem`'s `th` and its fragment state is at the clone, hence in the third level
(`pc_of_cloneH`), whose invariant gives the executable (`cloneInv2_of`); after the exit `SpawnPrem`'s
`exited = none` fails. -/
theorem hexe_of {Q : Spike.Lib.X64WakeA64.WakeRel} {P : Scc.Sem.SrcSem.SrcParams} {G' : Loc → Val → Prop}
    {own : OwnS} {H : State → List (Nat × Range) → Prop} {μ' : Marks} {ar : Arena}
    (hR : ∀ d s, Q.R1 d s → RSAH L.Λ P helloSrc G' own (IH Dd) H μ' ar d s)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0)
    (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0) :
    ∀ d s th stack tls r, SpawnPrem Q L.Λ asm E 0 d s th stack tls r → th.st.exe = L.exe := by
  intro d s th stack tls r hP
  obtain ⟨hR1, -, h3, h4, -, h6, h7, -⟩ := hP
  rcases hR d s hR1 with
    ⟨th', th0, j, lbl, lsize, ts, hl, pm, hd, hth, -, -, -, -, -, -, -, -, hI, -⟩ |
    ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, -⟩
  · rw [hth] at h3
    obtain rfl : th' = th := by simpa using h3
    have hpc := pc_of_cloneH hN hT hCl hI h4 h7
    rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ | ⟨l1, b1, n1, l', b', n', -, -, -, -, -, -, hi⟩
    · exact absurd hpc (h0.2.2 _ _ _ hi)
    · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
    rw [hinv2] at hi
    obtain ⟨-, t, l2, ws, ⟨R, F₂, tc, k, sl, me, cA, frp, -, ⟨he, -, -, -⟩, -⟩, -⟩ := cloneInv2_of hi hpc
    exact he
  · rw [hk] at h6; cases h6

end Rel

end Spike.Lib.X64HelloXOk

/-- info: 'Spike.Lib.X64HelloXOk.hX_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloXOk.hX_ofR

/-- info: 'Spike.Lib.X64HelloXOk.hexe_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloXOk.hexe_of
