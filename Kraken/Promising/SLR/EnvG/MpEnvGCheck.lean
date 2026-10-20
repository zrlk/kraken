/-
**Statement checks for the EnvG MP theorems**: a leaf
module, so that `EnvG/MpEnvGPublic2.lean` need not import `SLR/MpPublic.lean`
(and the old MP proofs) for its `type_of%` check (moved here unchanged).
-/
import Kraken.Promising.SLR.EnvG.MpEnvGPublic
import Kraken.Promising.SLR.EnvG.MpEnvGPublic2

namespace Kraken.Promising.SLR.EnvG.MpLink

open Kraken.Promising.SLR.MpPublic

/-- `mp_envG'` has exactly the statement of `mp_public`. -/
example : type_of% @mp_envG' = type_of% @mp_public := rfl

end Kraken.Promising.SLR.EnvG.MpLink
