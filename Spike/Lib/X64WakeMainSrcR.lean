/-
**main's source pieces of `MainPieces` from `src_fields`** (x86-64): the x64 twin of `Spike/Lib/WakeMainSrcR.lean` (over
`X64SpawnViewLtSteps.src_fields` at the spawn's parent).

`MainPieces`' source fields (`htP`, `hlP`, `hwc`, `hval`, `hloc`, `hin`) at
`cP = Ctl.of s0`, `w = cst (.loc ⟨l,0⟩ 0)`, `tyP = .ptr .pub .int`:

- `src_pieces`: the form, with each input a named premise —
  `hs'` (the spawned configuration is `spawnCfg s 0 th0 "t" mTail …`),
  `hc` (`c`'s binding in `th0`), `hA` (`lbl l = some cA.toNat`),
  `hlsz` (`0 < lsize l`) and `hcS` (the record's flag address).

**Deviations.** The x64 ghost record (`WakeInst.Gh`'s twin) and `PreR`
(`WakeSpawnR`'s twin) are not yet on this branch, so
`src_pieces` takes the record's fields `lbl`, `lsize`, `cS` directly in
place of `g : Gh` (instantiate with `g.lbl`, `g.lsize`, `g.cS`; the
statement is otherwise A64's), and `src_pieces_R` (the `PreR` corollary:
`hc := PreR.hc`, `hlsz := PreR.hin`, `hcS`/`hA` via `PreR.hw`) is left to
the x64 `PreR`'s file / `hMainR_ofD`, where it is a three-line wrapper.
-/
import Spike.Lib.X64SpawnViewLtSteps

namespace Spike.Lib.X64WakeMainSrcR

open CoreLang CoreTerm
open Scc.Sem (ValRep LocRep)
open Spike.Lib.X64WakeM0 (mTail)

/-- **The source fields** (see the module doc). -/
theorem src_pieces {s s' : TermRun.Cfg} {th0 s0 s1 : TermRun.TTh} {ws : List TermRun.Word}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {cS : WeakMem.Address}
    {l : WeakMem.AllocLabel} {cA : BitVec 64}
    (hs' : s' = TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws)
    (hths : s.ths = #[th0]) (hths' : s'.ths = #[s0, s1])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hA : lbl l = some cA.toNat) (hlsz : 0 < lsize l) (hcS : cS = ⟨l, 0⟩) :
    (Ctl.of s0).term = mTail ∧
      TermRun.lookupE (Ctl.of s0).env "c" = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc cS 0 ∧
      ValRep lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat ∧
      LocRep lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat 0 ∧
      ∃ sa, (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc sa 0 ∧ sa.offset < lsize sa.label := by
  have hs0 : s0 = TermSpawnStep.spawnPar s 0 th0 "t" mTail := by
    subst hs'
    have h := congrArg (·[0]?) hths'
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hths] at h
    exact h.symm
  subst hs0
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Spike.Lib.X64SpawnViewLtSteps.src_fields (i := 0) hc hA hlsz
  exact ⟨h1, h2, by rw [hcS]; exact h3, h4, h5, h6⟩

end Spike.Lib.X64WakeMainSrcR

/-- info: 'Spike.Lib.X64WakeMainSrcR.src_pieces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainSrcR.src_pieces
