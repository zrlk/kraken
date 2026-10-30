/-
**wake.w's `scc_rt_thread_init` call with no outside moves** (AArch64): the
node obligations of `TiW` / `TakeW` weaken in the outside move `K` (each
node only asks no state of it moved by `K`), so `startTi_WS` / `takeW_WS`
hold at `K = False` (`hatW`'s `hti` at `K := False`, `KStable.none`).

- `TakeW.kMono`, `TiW.kMono`: `TakeW` / `TiW` at a smaller outside move.
At `K = False`: `(startTi_WS … i).kMono (fun _ _ h => h.elim)` (likewise
`takeW_WS`).
-/
import Spike.Lib.A64WakeStartTiW

namespace Spike.Lib.A64.Flow.Ret0

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow (BlkW NodeW ND)

variable {W : Frag isaLSE2} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F M P : MachineData → Prop}

/-- A node obligation at a smaller outside move. -/
theorem nodeW_kMono {n : ND} (h : NodeW W K exe endPc R F n) (hK : ∀ s s', K' s s' → K s s') :
    NodeW W K' exe endPc R F n :=
  fun s c hA => ⟨(h s c hA).1, fun s' hk => (h s c hA).2 s' (hK _ _ hk)⟩

/-- A block obligation at a smaller outside move. -/
theorem blkW_kMono {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk)
    (hK : ∀ s s', K' s s' → K s s') : BlkW W K' exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
    ⟨(h s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
      fun s' hk' => (h s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2 s' (hK _ _ hk')⟩

/-- **`TakeW` at a smaller outside move.** -/
theorem TakeW.kMono {q : TakeG} {i : TK} (h : TakeW W K exe endPc R F M q i P) (hK : ∀ s s', K' s s' → K s s') :
    TakeW W K' exe endPc R F M q i P := by
  cases i <;> dsimp only [TakeW] at h ⊢
  all_goals first
    | exact blkW_kMono h hK
    | exact nodeW_kMono h hK
    | exact ⟨nodeW_kMono h.1 hK, nodeW_kMono h.2 hK⟩
    | exact h

/-- **`TiW` at a smaller outside move.** -/
theorem TiW.kMono {q : TiG} {i : TI} (h : TiW W K exe endPc R F M q i P) (hK : ∀ s s', K' s s' → K s s') :
    TiW W K' exe endPc R F M q i P := by
  cases i <;> dsimp only [TiW] at h ⊢
  all_goals first
    | exact blkW_kMono h hK
    | exact nodeW_kMono h hK
    | exact fun g hg i => (h g hg i).kMono hK

end Spike.Lib.A64.Flow.Ret0

/-- info: 'Spike.Lib.A64.Flow.Ret0.TakeW.kMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Ret0.TakeW.kMono

/-- info: 'Spike.Lib.A64.Flow.Ret0.TiW.kMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Ret0.TiW.kMono
