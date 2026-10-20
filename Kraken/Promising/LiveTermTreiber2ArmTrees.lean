/-
**Stage 4: the event trees of the `treiber2_arm.kl`
worker** `treiber2ArmWorker` (`EnvG/Treiber2ArmVCGen.lean`):
`LiveTermTreiber2Trees.lean` re-elaborated by `#tk_clone`
(`LiveTicketAlClone.lean`) with `treiber2DWorker` → `treiber2ArmWorker`.
The two workers have the same cells at the same positions except the kinds
of the push's load of `top` (`ldr`, position 3) and of the two CASes
(`casl` at 6, `cas` at 14); the statements of those cells quantify over the
kind, so the cloned proofs read the `treiber2_arm` kinds off the cells.
Namespace `Live.TermTreiber2ArmTrees`; every other name as in
`Live.TermTreiber2Trees`.
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTermTreiber2Trees
import Kraken.Promising.SLR.EnvG.Treiber2ArmVCGen

#tk_clone "LiveTermTreiber2Trees.lean" with ["treiber2DWorker" => "treiber2ArmWorker", "StartWD" => "StartWA",
    "TermTreiber2Trees" => "TermTreiber2ArmTrees", "TermTreiber2" => "TermTreiber2Arm", "Treiber2" => "Treiber2Arm",
    "treiber2_term_sem_gen" => "treiber2_arm_term_sem_gen"]
