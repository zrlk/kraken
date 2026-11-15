import WeakCore.TermC1Rgn

/-! # TermC1RgnR: `region` and `intoRgn` as `publish`, with resources

The resource layer of TermC1Rgn: the step publishes the cell exactly as `tstepMR_publish` does.  The
view change flips the cell's accounting (`MemHeld_pubS`, side condition `hwp : FlipOK`), the credits
move, and the cell's own key leaves the frame (`SeenOK`, from `RgnLe1`).  A `region` also mints the
fresh region's key (`MintStep.fresh`'s `rg + wd`, the bound's `+ F`); an `intoRgn` mints nothing.

New here: `RgnLe1`, the own-key bound at `region` / `intoRgn` (as `PubLe1` at `publish`; both follow
from `OwnLe1`).
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
  {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}


end

end TermC1

#print axioms TermC1.RgnLe1.of_le1
#print axioms TermC1.pubStepR1
#print axioms TermC1.tstepMR_region1
#print axioms TermC1.tstepMR_intoRgn1
#print axioms TermC1.tstepMC_region1_of
#print axioms TermC1.tstepMC_intoRgn1_of
