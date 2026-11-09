/-
**hello.w's counters are not the second limit word** (AArch64): at the placed layout the
runtime's counter words `pnA`, `lockA`, `freeNA`, `nextA` (`rtWords`) differ from the second TCB's limit word
`lim2AH = pinA + 152` — that word is `spawnWords`' sixth (`pinA + 112 + 8 * 5`), and A13's data part keeps
`spawnWords` apart from `rtWords` (`H1Rt.a13_facts`). This is `HelloGOf2H.hctr2_of_dataH`'s conclusion without its
`hctrD` (the counters in `.data`): `PlaceW`'s `wordOk` allows a runtime word in `.data` *or* the pinned region, so
`hctrD` is not a consequence of `PlaceW`, while `hctr2` (its only use, `StartH0G0`/`StartH0G`) follows from `hA13`.

- `lim2_spawn`: `lim2AH Ly ∈ spawnWords Ly.pinA`.
- `hctr2_H`: `hctr2` at the instance, from `hA13`.
-/
import Spike.Lib.A64WakeH1Rt
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.HelloCtr2

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

/-- **The second limit word is a spawn word** (`pinA + 112 + 8 * 5`). -/
theorem lim2_spawn : Spike.Lib.HelloGOf2H.lim2AH (Ly) ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA := by
  refine List.mem_map.2 ⟨5, List.mem_range.2 (by decide), ?_⟩
  show (Ly).pinA + BitVec.ofNat 64 (112 + 8 * 5) = (Ly).pinA + 152#64
  rfl

/-- (row root-hctrD) **`hctr2` at the instance** (`StartH0G0`/`StartH0G`'s use of `hctrD`), from A13's data part:
the counters are runtime words, the second limit word a spawn word, and the two lists are apart. -/
theorem hctr2_H (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly) := by
  have hA := (Spike.Lib.A64.WakePh.H1Rt.a13_facts hp i hA13).2.2.2.2 _ (lim2_spawn hp i)
  intro a ha he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact hA _ (Ly).pn_mem he.symm
  · exact hA _ (Ly).lock_mem he.symm
  · exact hA _ (Ly).freeN_mem he.symm
  · exact hA _ (Ly).next_mem he.symm

end Spike.Lib.HelloCtr2

/-- info: 'Spike.Lib.HelloCtr2.lim2_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCtr2.lim2_spawn

/-- info: 'Spike.Lib.HelloCtr2.hctr2_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloCtr2.hctr2_H
