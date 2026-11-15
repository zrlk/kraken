import WeakCore.TermC1Lem

/-! # TermC1Ld: `load` and `store` at region cells

Under c1 a region reference is held to the `pub` clause (`ModeOK1`), so a region-cell load or store
is a `pub` one: `tstepM_loadCell` / `tstepM_storeCell` (TermStep, any mode whose clause gives a
`pub`-like frontier).  Today's `VR` has no frontier at `.rgn` (`ModeOK .rgn _ = True`); the lemmas
here take it as the explicit hypothesis `hmo`, which the switch to the c1 definitions discharges from
`VR` with `ModeOK1`.

The bound type is `adapt r u`; the cell's type is `noOwnIn` (pre-state `PubCpl`, at the frontier
`hmo` gives), so `adapt r u = u` (`rgn_adapt`).  A `loadCap`/`storeCap` derivation at a region cell
takes the same route; `loadTorn` is a torn read that `ruleA` admits (`rgnLoad_ruleA`) and `loadTornRgn_step` steps.

Since the switch these lemmas live in TermStep; the #print lines keep the gate's checks.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}

end


section
variable {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
  {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {r : Idx} {u : Ty} {e : Expr} {Rf Rs H : Res}

end

end TermC1

#print axioms TermC1.arrFree_adapt
#print axioms TermC1.adapt_cl
#print axioms TermC1.rgnV
#print axioms TermC1.rgn_adaptT
#print axioms TermC1.rgn_adapt
#print axioms TermC1.rgnLoc_adaptL
#print axioms TermC1.accs_rgnSub
#print axioms TermC1.rgnLoc_adaptS
#print axioms TermC1.rgnLoad_facts
#print axioms TermC1.rgnSub
#print axioms TermC1.rgnStore_facts
#print axioms TermC1.tstepM_loadRgn1
#print axioms TermC1.tstepMR_loadRgn1
#print axioms TermC1.tstepMC_loadRgn1
#print axioms TermC1.tstepM_storeRgn1
#print axioms TermC1.tstepMR_storeRgn1
#print axioms TermC1.tstepMC_storeRgn1
#print axioms TermC1.tstepM_loadRgnLoc1
#print axioms TermC1.tstepMR_loadRgnLoc1
#print axioms TermC1.tstepMC_loadRgnLoc1
#print axioms TermC1.tstepM_storeRgnLoc1
#print axioms TermC1.tstepMR_storeRgnLoc1
#print axioms TermC1.tstepMC_storeRgnLoc1
