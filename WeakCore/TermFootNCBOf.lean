import WeakCore.TermNoFulRun
import WeakCore.TermFootNCB

/-! # TermFootNCBOf: the `FootNCB` slot, discharged

`footNCB_of : FootNCB p` for every `p`, from `TermFootNCB.tstep_footprintK_ncB`.
-/

namespace TermPtrKey
open CoreTerm

/-- **`FootNCB` holds unconditionally.** -/
theorem footNCB_of (p : Prog) (hPS : TermSound.PwSkel) (hSub : TermSound.PwSubS) (hSig : TermSound.PwSig) : FootNCB p :=
  fun hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hZ hgp hrp =>
    TermFootNCB.tstep_footprintK_ncB (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hZ hgp (hRP := hrp)

#print axioms footNCB_of

end TermPtrKey
