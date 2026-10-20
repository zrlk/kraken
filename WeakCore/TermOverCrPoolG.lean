import WeakCore.TermOverCrPoolF
import WeakCore.TermFreeQWP

/-! # TermOverCrPoolG: the foreign cover chain at an explicit upgraded pre-cover (hWbR route (iii))

Copies of `overCr_foreignO`/`overCr_foreignMO`/`foreign_overCrPZO` (TermOverCrWb)
whose pre-cover is an explicit list `Gs` (`OverCrL` + `HolderLow`, in place of `OverCrE`) and whose
window premises (`hG`/`hcovD`, `hWbO`/`hent`) admit a third disjunct "covered by a `Gs` item's `K` bit";
and copies of `foreign_overCrCfgWV`/`Cfg1WV`/`Cfg1PV` (TermOverCrPoolF) taking the cell's upgraded
pre-cover and window transport from `HWbRUp` (the `hWbRUp_of`) in place of `hOC` + `hWbR`.
The proofs are otherwise unchanged.

(R4 dedup) the declarations now live in `TermFreeQW` (`overCr_foreignOG`, `overCr_foreignMOG`,
`foreign_overCrPZOG`, `HWbRUp`, `foreign_overCrCfgWVG`, `foreign_overCrCfg1WVG`) and `TermPdR`
(`foreign_overCrCfg1PVG`); this module keeps their axiom prints.
-/

#print axioms TermOverCrW.overCr_foreignOG
#print axioms TermOverCrW.overCr_foreignMOG
#print axioms TermOverCrW.foreign_overCrPZOG
#print axioms TermFreeQW.foreign_overCrCfgWVG
#print axioms TermFreeQW.foreign_overCrCfg1WVG
#print axioms TermOverCrW.foreign_overCrCfg1PVG
