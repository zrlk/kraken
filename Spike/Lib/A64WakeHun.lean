/-
**`H1G`'s "unmapped under `F`" premises from `wc_main`'s frame** (wake.w,
AArch64): `scc_rt_nthreads`, `scc_rt_pinned_next`, the second TCB's header
`pinA + 96` and id word `t2 + 56` load none in every memory of
`wF (swR v (-384) 0) 336 (FS …)` (the root's `wFU`, so every `F` with
`BoxPure`'s `F ⊆ wFU`): `FS`'s `WordsNoneP` at a word whose bytes each lie in
`.data` or `pinned` (A13's `spawnWords`/`ntA`, A8's `words_mapped`).

- `hun_W`: the generic step; `hunN_W`, `hunP_W`, `hunH_W`, `hunT_W`: the four.
-/
import Spike.Lib.A64WakeH1Rt
import Spike.Lib.A64WakeMainGlue

namespace Spike.Lib.A64.WakePh.Hun

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.WakeM (wF)
open Spike.Lib.A64.WakePh.MainGlue (FS)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- `wc_main`'s frame at the base `v` (the root's `wFU` is its union). -/
abbrev WF (v : BitVec 64) (m0 : MachineData) (σC : Spike.Lib.A64.Flow.AS) : MachineData → Prop :=
  wF (swR v (-384) 0) 336 (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) 384 0#64 v) m0 σC

/-- **A word of `.data` or `pinned`, byte by byte, loads none** under `WF`. -/
theorem hun_W {a : BitVec 64}
    (hb : ∀ j < 8, (Ly).Λ.data.contains (a.toNat + j) ∨ (Ly).Λ.pinned.contains (a.toNat + j)) :
    ∀ v m0 σC m, WF hp i v m0 σC m → Mem.loadInt m.dmem a 8 = none :=
  fun _ _ _ _ h => h.1.1 a fun j hj => (hb j hj).elim (.inr ∘ .inl) (.inr ∘ .inr)

variable (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
include hA13

/-- **`hunN`**: `scc_rt_nthreads`. -/
theorem hunN_W : ∀ v m0 σC m, WF hp i v m0 σC m →
    Mem.loadInt m.dmem (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) 8 = none :=
  hun_W hp i (H1Rt.a13_facts hp i hA13).1

omit hA13 in
/-- **`hunP`**: `scc_rt_pinned_next`. -/
theorem hunP_W : ∀ v m0 σC m, WF hp i v m0 σC m → Mem.loadInt m.dmem (Ly).pnA 8 = none :=
  hun_W hp i ((Ly).words_mapped _ (Ly).pn_mem).2.2

/-- **`hunH`**: the second TCB's header `pinA + 96`. -/
theorem hunH_W : ∀ v m0 σC m, WF hp i v m0 σC m → Mem.loadInt m.dmem ((Ly).pinA + 96#64) 8 = none :=
  hun_W hp i ((H1Rt.a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨2, List.mem_range.2 (by decide), rfl⟩))

/-- **`hunT`**: the second TCB's id word `t2 + 56 = pinA + 160`. -/
theorem hunT_W : ∀ v m0 σC m, WF hp i v m0 σC m →
    Mem.loadInt m.dmem (Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64) 8 = none := by
  have e : Spike.Lib.A64.Flow.WakeWc.t2 (Ly).lab + 56#64 = (Ly).pinA + BitVec.ofNat 64 160 := by
    show Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64 = _
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl
  rw [e]
  exact hun_W hp i ((H1Rt.a13_facts hp i hA13).2.1 _ (List.mem_map.2 ⟨10, List.mem_range.2 (by decide), rfl⟩))

end Spike.Lib.A64.WakePh.Hun

/-- info: 'Spike.Lib.A64.WakePh.Hun.hunN_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Hun.hunN_W

/-- info: 'Spike.Lib.A64.WakePh.Hun.hunP_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Hun.hunP_W

/-- info: 'Spike.Lib.A64.WakePh.Hun.hunH_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Hun.hunH_W

/-- info: 'Spike.Lib.A64.WakePh.Hun.hunT_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Hun.hunT_W
