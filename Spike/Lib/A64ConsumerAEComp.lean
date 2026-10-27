/-
**The components in the middle of the output `write`** (`CompAE` of
`Spike/Lib/A64ConsumerAEStart.lean`), with `Components` exempting the
output extern's model frame (`Scc.Sem.ExternFrame`) from `env_rep` and
`env_total`: the source's current frame is inside `print` (`Top`), so the
witness places none of its words; the suspended frames are placed
(`FramesPlaced`).

- `components_oneSE` (`Spike/Lib/A64PlacedSE.lean`): `components_oneS` with
  the current frame unplaced, at a model term or a term reading no variable.
- `r_componentsAE`: `CompAE` from `Top` at such terms.
-/
import Spike.Lib.A64ConsumerAEStart
import Spike.Lib.A64PlacedSE

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {Top : Ctl → Prop}

/-- **The components in the middle of the output `write`** (`CompAE`),
given that every control of `Top` is at a model term of the output extern
or at a term reading no variable (`components_oneSE`; the suspended frames
by `EmitJ`'s `FramesPlaced`). -/
theorem r_componentsAE (hwf : Λ.WF)
    (hTop : ∀ c, Top c → c.term ∈ externModelTerms ∨ exprFv c.term = []) {rS : Range} {Tk : State → Prop} :
    CompAE Λ P p G own I Top rS Tk μ ar := by
  intro t s h
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, hh, -, -, hs0, -, -, hJ, -, -, -, hinv,
    hown, hmi, -⟩ := h
  obtain ⟨-, hT, -, hfp, -⟩ := hJ
  exact (components_oneSE hwf hth (by rw [hk]; rfl) hh hmi hs0 (hTop _ hT) hfp hinv hown).imp fun _ h => h.1

end Spike.Lib.A64ConsumerA
