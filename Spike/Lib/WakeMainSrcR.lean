/-
**main's source pieces of `MainPieces` from `src_fields`** (`SpawnViewLtSteps.src_fields` at the spawn's parent).

`MainPieces`' source fields (`htP`, `hlP`, `hwc`, `hval`, `hloc`, `hin`) at
`cP = Ctl.of s0`, `w = cst (.loc ⟨l,0⟩ 0)`, `tyP = .ptr .pub .int` and the
record `g = w.1`:

- `src_pieces`: the form, with each input a named premise —
  `hs'` (the spawned configuration is `spawnCfg s 0 th0 "t" mTail …`),
  `hc` (`c`'s binding in `th0`), `hA` (`lbl l = some cA.toNat`),
  `hlsz` (`0 < lsize l`); and `hg` (the record's
  placement and `cS`, from `PreR.hw` via `recW`).
- `src_pieces_R`: at `PreR`; `hc` from `PreR.hc`, `hlsz` from `PreR.hin`,
  `hg` from `PreR.hw`; open `hs'` and `hA`.
-/
import Spike.Lib.WakeSpawnR
import Spike.Lib.SpawnViewLtSteps
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeMainSrcR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeSpawnR
open Spike.Lib.WakeInst (Gh)
open Spike.Lib.WakeM0 (mTail)

/-- **The source fields** (see the module doc). -/
theorem src_pieces {s s' : TermRun.Cfg} {th0 s0 s1 : TermRun.TTh} {ws : List TermRun.Word}
    {g : Gh} {l : WeakMem.AllocLabel} {cA : BitVec 64}
    (hs' : s' = TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws)
    (hths : s.ths = #[th0]) (hths' : s'.ths = #[s0, s1])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hA : g.lbl l = some cA.toNat) (hlsz : 0 < g.lsize l) (hcS : g.cS = ⟨l, 0⟩) :
    (Ctl.of s0).term = mTail ∧
      TermRun.lookupE (Ctl.of s0).env "c" = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc g.cS 0 ∧
      ValRep g.lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat ∧
      LocRep g.lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat 0 ∧
      ∃ sa, (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc sa 0 ∧ sa.offset < g.lsize sa.label := by
  have hs0 : s0 = TermSpawnStep.spawnPar s 0 th0 "t" mTail := by
    subst hs'
    have h := congrArg (·[0]?) hths'
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hths] at h
    exact h.symm
  subst hs0
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := SpawnViewLtSteps.src_fields (i := 0) hc hA hlsz
  exact ⟨h1, h2, by rw [hcS]; exact h3, h4, h5, h6⟩

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **The source fields at `PreR`** (see the module doc); open `hs'`, `hA`. -/
theorem src_pieces_R {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {d : Cfg} {th : Thread isaLSE2} {stack : Nat}
    {s s' : TermRun.Cfg} {w : ιR hp i} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
    {T S : Nat} {l : WeakMem.AllocLabel} {pT : Loc} {w1 w2 : TermRun.Word} {ty1 : Ty} {r0' : Range}
    {X : State → Prop} {q : Spike.Lib.A64.Rt.TcbGG} {cA : BitVec 64}
    (hR : PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q)
    (hs' : ∃ th0 ws, s.ths = #[th0] ∧
      s' = TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws)
    (hA : lbl l = some cA.toNat) :
    (Ctl.of s0).term = mTail ∧
      TermRun.lookupE (Ctl.of s0).env "c" = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc w.1.cS 0 ∧
      ValRep w.1.lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat ∧
      LocRep w.1.lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat 0 ∧
      ∃ sa, (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc sa 0 ∧ sa.offset < w.1.lsize sa.label := by
  obtain ⟨th0, ws, hths, hs'⟩ := hs'
  obtain ⟨th0', hths0, hc⟩ := hR.hc
  rw [hths] at hths0
  obtain rfl : th0 = th0' := by simpa using hths0
  have hw := hR.hw
  exact src_pieces (g := w.1) hs' hths hR.pre.ths hc (by rw [hw]; exact hA) (by rw [hw]; exact hR.hin)
    (by rw [hw]; rfl)

end Inst

end Spike.Lib.WakeMainSrcR

/-- info: 'Spike.Lib.WakeMainSrcR.src_pieces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeMainSrcR.src_pieces

/-- info: 'Spike.Lib.WakeMainSrcR.src_pieces_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeMainSrcR.src_pieces_R
