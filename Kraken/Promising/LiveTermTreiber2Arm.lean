/-
**Stage 4: termination of the `treiber2_arm.kl` workers
on the semantic machine, under every schedule**: `LiveTermTreiber2.lean`
re-elaborated by `#tk_clone` (`LiveTicketAlClone.lean`) at
`treiber2ArmWorker` (start states `StartWA`). Namespace `Live.TermTreiber2Arm`; the theorem
`treiber2_arm_term_sem_gen`; every other name as in `Live.TermTreiber2` (the rank table
from `LiveTermTreiber2Rank.lean`, cloned first). The statements are restated explicitly in
`LiveTermTreiber2Thm.lean`.
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTermTreiber2ArmTrees
import Kraken.Promising.LiveTermTreiber2Rank
import Kraken.Promising.LiveTermTreiber2
import Kraken.Promising.SLR.EnvG.Treiber2ArmRelPure

#tk_clone "LiveTermTreiber2Rank.lean" with ["treiber2DWorker" => "treiber2ArmWorker", "StartWD" => "StartWA",
    "TermTreiber2Trees" => "TermTreiber2ArmTrees", "TermTreiber2" => "TermTreiber2Arm", "Treiber2" => "Treiber2Arm",
    "treiber2_term_sem_gen" => "treiber2_arm_term_sem_gen"]

#tk_clone "LiveTermTreiber2.lean" with ["treiber2DWorker" => "treiber2ArmWorker", "StartWD" => "StartWA",
    "TermTreiber2Trees" => "TermTreiber2ArmTrees", "TermTreiber2" => "TermTreiber2Arm", "Treiber2" => "Treiber2Arm",
    "treiber2_term_sem_gen" => "treiber2_arm_term_sem_gen"]
