import Spike.Test.WakeLinkedA64Ctr
import Spike.Lib.A64WakeLdFacts

/-!
# `wcMainW_wf`'s loader facts at `Le` (non-vacuity)

`A64WakeLdFacts`' five lemmas instantiated at `placeW_e`, from A13's data part
at `Le` (`hA13_e`).
-/

namespace Spike.Test.WakeLinkedA64

open Spike.Lib.A64.WakePh.LdFacts

example := hhdr_W placeW_e ie hA13_e
example := hmP_W placeW_e ie
example := hmH_W placeW_e ie hA13_e
example := htid1_W placeW_e ie hA13_e
example := htid3_W placeW_e ie hA13_e

end Spike.Test.WakeLinkedA64
