/-
**The AArch64 compiler theorem for an `Accepted2` program at the
configurations with the header bound** (the twin of the x86-64
`Closed2StmtH`, `Spike/Lib/LowerX64/G1Closed2Final.lean`): `Closed2StmtA`
(`Spike/Lib/LowerA64/Closed2StmtA.lean`) at every configuration whose
object layout's header scalar count starts below bit 22, proved by
`closed2StmtA_g1` (`Spike/Lib/LowerA64/G1Closed2Fin.lean`).

- `Closed2StmtAH`: `Closed2StmtA` with the premise
  `Scc.Obj.nShift cfg.layout.obj < 22`;
- `closed2StmtAH_final`: **`Closed2StmtAH`**, with no premises.
-/
import Spike.Lib.LowerA64.Closed2StmtA
import Spike.Lib.LowerA64.G1Closed2Fin

namespace Spike.Lib.LowerA64

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- **`Closed2StmtA` at the configurations with the header bound**
(`Scc.Obj.nShift cfg.layout.obj < 22`, the configuration premise of the
AArch64 theorem). -/
def Closed2StmtAH : Prop :=
  ∀ (cfg : Scc.Config), Scc.Obj.nShift cfg.layout.obj < 22 →
  ∀ (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (Λ : Scc.Sem.Layout),
    Scc.Lower.Accepted2 p = true → Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true →
    CfgNeedOkA pcfg = true →
    ∀ {asm : String}, Scc.Cert.Link.A64.parsesTo asm
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.A64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B asm

/-- **The AArch64 compiler theorem at the configurations with the header
bound** (`closed2StmtA_g1`). -/
theorem closed2StmtAH_final : Closed2StmtAH := fun cfg hobj => closed2StmtA_g1 cfg hobj

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.closed2StmtAH_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.closed2StmtAH_final
