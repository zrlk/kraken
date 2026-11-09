/-
**`hti_W`'s frame premises from the root's frame** (wake.w, x86-64): at
any frame condition `F` inside `RootU.wFU` (`BoxPure`'s `∀ m, F m → F0 m`
at `F0 := wFU`), the runtime's words and the second TCB's words load none
(`hFr`, `hunF` of `X64WakeTi2Hat.hti_W`), since `wFU`'s frames leave every
word of `.data` and `pinned` unloaded (`RootU.hunB_wFU`).

- `tiAddr_spawn`: a word of the second TCB (`tiAddrs (t2 lab)`, `pinA +
  136 + 8 k`) is `spawnWords`' word `3 + k`.
- `hFr_U`: `rtF` under `F` (`words_mapped`).
- `hunF_U`: the second TCB's words load none under `F` (A13's
  `spawnWords`, `H1Rt.a13_facts`).

AArch64's `WakeTiA.tiA_of` carries both as premises; here they are
discharged at the root's frame. The second TCB's words are placed through
A13's `spawnWords` rather than `pinned`'s bound `hpin2`, so no layout
premise beyond A13's data part is needed.
-/
import Spike.Lib.X64WakeRootU
import Spike.Lib.X64WakeTi2Hat

namespace Spike.Lib.X64.WakeTiF

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.WakeWc (t2)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **A word of the second TCB is a spawn word**: `pinA + 136 + 8 k` is
`spawnWords`' word `3 + k`. -/
theorem tiAddr_spawn {a : BitVec 64} (ha : a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab)) :
    a ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA := by
  have ht : t2 (Ly).lab = (Ly).pinA + 136#64 := by
    show Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 136#64 = _
    rw [(Ly).lab_pin]
  have hadd : ∀ c, (Ly).pinA + 136#64 + BitVec.ofNat 64 c = (Ly).pinA + BitVec.ofNat 64 (136 + c) := fun c => by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have hw : ∀ k < 6, (Ly).pinA + BitVec.ofNat 64 (136 + 8 * k) ∈ Scc.Cert.Spawn.X64.spawnWords (Ly).pinA :=
    fun k hk => List.mem_map.2 ⟨3 + k, List.mem_range.2 (by
      have : 9 ≤ 1 + Scc.IR.Tcb.size / 8 + Scc.IR.maxSpawnArgs := by decide
      omega), by congr 2; omega⟩
  rw [ht] at ha
  simp only [Spike.Lib.X64.Rt.Ti.tiAddrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hadd]; exact hw 0 (by decide)
  · rw [hadd]; exact hw 1 (by decide)
  · rw [hadd]; exact hw 2 (by decide)
  · rw [hadd]; exact hw 3 (by decide)
  · rw [hadd]; exact hw 4 (by decide)
  · rw [hadd]; exact hw 5 (by decide)

variable {F : MachineData → Prop} (hF : ∀ m, F m → Spike.Lib.X64.WakePh.RootU.wFU hp i m)
include hF

/-- **`hti_W`'s `hFr`**: the runtime's words load none under `F`. -/
theorem hFr_U : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m := fun m h a ha =>
  Spike.Lib.X64.WakePh.RootU.hunB_wFU hp i a ((Ly).words_mapped a ha).2.2 m (hF m h)

/-- **`hti_W`'s `hunF`**: the second TCB's words load none under `F`. -/
theorem hunF_U (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ a ∈ Spike.Lib.X64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none :=
  fun a ha m h => Spike.Lib.X64.WakePh.RootU.hunB_wFU hp i a
    ((Spike.Lib.X64.WakePh.H1Rt.a13_facts hp i hA13).2.1 a (tiAddr_spawn hp i ha)) m (hF m h)

end Spike.Lib.X64.WakeTiF

/-- info: 'Spike.Lib.X64.WakeTiF.tiAddr_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeTiF.tiAddr_spawn

/-- info: 'Spike.Lib.X64.WakeTiF.hFr_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeTiF.hFr_U

/-- info: 'Spike.Lib.X64.WakeTiF.hunF_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeTiF.hunF_U
