/-
**The source's reads are numbers** for an `Accepted2` program
(ISA-neutral): `SrcRd … IsNum` (`Spike/Lib/Consumer1.lean`), the read side
the consumer supplies at `rd := IsNum`. Every message of a reachable
configuration that thread 0 has not promised is a number (`invN_reach`'s
`MemNP`); a value representing it (`ValRep`) puts it below `2^64`.

- `srcRd_isNum`: that.
-/
import Spike.Lib.Src.SrcNum2
import Spike.Lib.Src.NJ3

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm TermRun Scc.Sem
open TermFul (promsOf promsOf_some)
open Scc.Lower (litWalks2 shapeOf Accepted2 setupOf)
open Scc.Sem.SrcSem
open Spike.Lib.Consumer1 (SrcRd)

/-- **The source's reads are numbers** for an `Accepted2` program from the
start before its setup block (`invN_reach`). -/
theorem srcRd_isNum {P : SrcParams} {p : Prog} (hacc : Accepted2 p = true)
    (hn : ∀ q ∈ litWalks2 p, numQ q = true)
    (hset : ∀ s, setupOf p = some s → Compat s (shapeOf s) = true) {s0 : Ty}
    (hsetup : setupOf p = some s0)
    (hinit : ∀ c, P.init c → ∃ meW, c = setupStart P.cap meW)
    (hH : P.hooks = SrcHooks.none ∨ SrcOutProto.UsesWc P p) : SrcRd P p IsNum := by
  intro tr s th k m lbl x hr hs hp hm hrep
  obtain ⟨⟨-, hnp⟩, -, -⟩ := invN_reach hacc hset (goodBlocks_of hacc hn) hsetup hinit hH hr
  have hth : s.ths[0]? = some th := by rw [hs]; rfl
  obtain ⟨n, hv⟩ := hnp k m hm (by rw [promsOf_some hth, hp]; exact List.not_mem_nil)
  refine ⟨n, hv, ?_⟩
  have h := hrep
  rw [hv] at h
  exact h.1

end Spike.Lib.LowerNode
