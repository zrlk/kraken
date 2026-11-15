import WeakCore.TermC1Defs
import WeakCore.TermStep

/-! # TermC1Drf: `drf1` under closing and folding (G8)

`PubCpl1` reads `drf1` where `PubCpl` read `rgnFree`.  The publish family proves `rgnFree` of the
closed cell type with `rgnFree_cl0` (closing) and `rgnFree_Fd` (folding, through `rgnFree_cl_shift`
and `rgnFree_unfold`).  These are the `drf1` counterparts.  `drf1` also looks behind references, so
closing needs every witness to be `drf1` (`hW`), not only the unguarded `share` ones.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermStep TermScope

end TermC1

#print axioms TermC1.drfM_clM
#print axioms TermC1.drf1_clK_up
#print axioms TermC1.drf1_clK
#print axioms TermC1.drf1_cl
#print axioms TermC1.drf1_cl0K
#print axioms TermC1.drf1_cl0
#print axioms TermC1.drf1_cl_shift
#print axioms TermC1.drf1_unfold
#print axioms TermC1.drf1_Fd
#print axioms TermC1.drf1_of_drf
