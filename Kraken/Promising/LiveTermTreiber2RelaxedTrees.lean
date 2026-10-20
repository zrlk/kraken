/-
**Stage 4: the event trees of the `treiber2_relaxed.kl`
worker** `Reach.Treiber2Relaxed.code` (`ReachA64Treiber2Relaxed.lean`; plain
`LDR` of `top` and plain `CAS` everywhere, the cells of `treiber2DWorker`
otherwise): `LiveTermTreiber2Trees.lean` re-elaborated by `#tk_clone`
(`LiveTicketAlClone.lean`). The cells whose kind differs are stated for some
kind. Namespace `Live.TermTreiber2RelaxedTrees`; every other name as in
`Live.TermTreiber2Trees`. Also `Reach.Treiber2Relaxed.StartWR`, the start
states (`StartWD` at this worker).
-/
import Kraken.Promising.LiveTicketAlClone
import Kraken.Promising.LiveTermTreiber2Trees
import Kraken.Promising.ReachA64Treiber2Relaxed

namespace Kraken.Promising.Reach.Treiber2Relaxed

open Kraken Kraken.Promising Kraken.Promising.AArch64

variable [layout : _root_.Layout]

/-- **A `treiber2_relaxed` worker's start state** (as `Treiber2.StartWD`):
at the start of `code` with `x0 = t`, `x1 = n`, `w9 = d`; no declarations;
no private copy of any 8- or 4-byte word. -/
structure StartWR (t n : BitVec 64) (d : BitVec 32) (s : isa.State) : Prop where
  exe : s.exe = layout code
  decls : s.decls = {}
  endPc : s.endPc = (layout code).addrOf code.length
  pc : s.st.2 = (layout code).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec = n
  x9 : s.st.1.regs.X9.toBitVec.setWidth 32 = d
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Kraken.Promising.Reach.Treiber2Relaxed

#tk_clone "LiveTermTreiber2Trees.lean" with ["Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker StartWD)" => "Kraken.Promising.Reach.Treiber2Relaxed (StartWR)",
    "Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker)" => "Kraken.Promising.Reach.Treiber2Relaxed (StartWR)",
    "treiber2DWorker" => "Reach.Treiber2Relaxed.code", "StartWD" => "StartWR",
    "TermTreiber2Trees" => "TermTreiber2RelaxedTrees", "TermTreiber2" => "TermTreiber2Relaxed",
    "treiber2_term_sem_gen" => "treiber2_relaxed_term_sem_gen"]
