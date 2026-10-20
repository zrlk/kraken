/-
**Stage 4: termination of the `treiber2_relaxed.kl`
workers on the semantic machine, under every schedule**:
`LiveTermTreiber2.lean` re-elaborated by `#tk_clone`
(`LiveTicketAlClone.lean`) at `Reach.Treiber2Relaxed.code` (start states
`StartWR`). Namespace `Live.TermTreiber2Relaxed`; the theorem
`treiber2_relaxed_term_sem_gen`; every other name as in `Live.TermTreiber2` (the
rank table from `LiveTermTreiber2Rank.lean`, cloned first).
Termination does not depend on the orderings: this worker is not safe
(`treiber2_relaxed_reachable`), but it terminates. Restated in
`LiveTermTreiber2Thm.lean`.
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTermTreiber2RelaxedTrees
import Kraken.Promising.LiveTermTreiber2Rank
import Kraken.Promising.LiveTermTreiber2

#tk_clone "LiveTermTreiber2Rank.lean" with ["Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker StartWD)" => "Kraken.Promising.Reach.Treiber2Relaxed (StartWR)",
    "Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker)" => "Kraken.Promising.Reach.Treiber2Relaxed (StartWR)",
    "treiber2DWorker" => "Reach.Treiber2Relaxed.code", "StartWD" => "StartWR",
    "TermTreiber2Trees" => "TermTreiber2RelaxedTrees", "TermTreiber2" => "TermTreiber2Relaxed",
    "treiber2_term_sem_gen" => "treiber2_relaxed_term_sem_gen"]

#tk_clone "LiveTermTreiber2.lean" with ["Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker StartWD)" => "Kraken.Promising.Reach.Treiber2Relaxed (StartWR)",
    "Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker)" => "Kraken.Promising.Reach.Treiber2Relaxed (StartWR)",
    "treiber2DWorker" => "Reach.Treiber2Relaxed.code", "StartWD" => "StartWR",
    "TermTreiber2Trees" => "TermTreiber2RelaxedTrees", "TermTreiber2" => "TermTreiber2Relaxed",
    "treiber2_term_sem_gen" => "treiber2_relaxed_term_sem_gen"]
