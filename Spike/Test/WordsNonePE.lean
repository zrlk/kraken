import Spike.Test.WakeLinkedA64
import Spike.Lib.Rt.A64WordsNoneP

/-!
# `WordsNoneP` at the real start (non-vacuity, `Le`)

The entry stack's memory of every admissible entry state at `Le` loads no
word of the heap, `.data` or `pinned` — the start frame `FWN`'s first
conjunct (`StartH0B.entry_atW`) is inhabited at the linked layout.
-/

namespace Spike.Test.WakeLinkedA64

example (E : Scc.Sem.Entry) (hE : E.Ok Le.Λ) : Spike.Lib.DmemPriv.WordsNoneP Le.Λ E.stackMem :=
  Spike.Lib.DmemPriv.wordsNoneP_stackMem (Spike.Lib.PlaceW.wf_link_of_placeW ie placeW_e) hE.1

end Spike.Test.WakeLinkedA64
