/-
**x64 MP with an unlocked `incl` release: no non-temporal store, and
purity, by `vcgen`**: the writer in `(relPureQ Arch.tso (fun _ _ => False)).within
[(f, 4), (d, 4)]` (every write a release), one `vcgen [inc32_shared_spec]`
call. `inc32_shared` is environment-generic, so the store half of `incl`
gets the all-release env's `ok` like any `mov` store.
The reader is `X64MpRelPure.mpReaderX_noNT` (unchanged program).
-/
import Kraken.Promising.SLR.EnvG.X64MpRelPure
import Kraken.Promising.SLR.EnvG.X64MpInc

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.MpInc

open Kraken.Promising.X64.EnvG.MpRelPure

set_option mvcgen.warning false
set_option experimental.vcgen true

variable [layout : _root_.Layout]

local instance mpIncWriterX.envR : CodeEnv := ⟨layout mpIncWriterX⟩

/-- **The x64 `incl` writer makes only release writes** (under `Arch.tso`). -/
theorem mpIncWriterX_noNT (f d : BitVec 64) :
    TripleEnv (EnvR f d)
      (fun s _ => s.regs.get64 .rdi = f ∧ s.regs.get64 .rsi = d ∧ Mem.loadInt s.dmem f 4 = none ∧
        Mem.loadInt s.dmem d 4 = none)
      mpIncWriterX (fun _ _ => True) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpIncWriterX
  vcgen [inc32_shared_spec]
  case vc5 s σ hpre _ _ _ _ _ _ =>
    obtain ⟨hx0, -, -, -⟩ := hpre
    refine ⟨?_, fun _ _ _ _ _ _ => Eventually.done _ (Or.inl ⟨rfl, trivial⟩)⟩
    simp_all
    all_goals exact fun h => h rfl
  all_goals simp_all
  all_goals first | exact fun h => h rfl | trivial

end Kraken.Promising.X64.EnvG.MpInc
