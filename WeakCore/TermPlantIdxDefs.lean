import WeakCore.TermPtrRtsDefs

/-! # TermPlantIdxDefs: the `SysInvN` clause `plantIdx` (definitions only)

Below `TermMainDefs` (which imports this module), over the `TermPtrRtsDefs` (`tminG`).
The key gate `KeyG` (final) and the plant-index clause `PlantIdxG`; `plantIdx_none` gives the
clause at a configuration without frontiers (the initial one, `InitOK`'s `∀ l, Eg.pfr l = none`).
Moved verbatim from `TermPlantAtT` (which now imports it); names unchanged.
-/

namespace TermPlantAtT
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The key gate**: thread `j` still holds the own key of `l` (frame or holdings). -/
def KeyG (Tot HP : Nat → Res) (j : Nat) (l : AllocLabel) : Prop := 0 < (Tot j + HP j) (.own l)

/-- **The plant-index clause** at `(Eg, c)` under the key gate, for the plant-edge selector `tm`. -/
def PlantIdxG (tm : GEnv → Cfg → Nat → AllocLabel → Option Ts) (Eg : GEnv) (Tot HP : Nat → Res) (c : Cfg) :
    Prop :=
  ∀ (j : Nat) (th : TTh) (l : AllocLabel) (cl : Cell), c.ths[j]? = some th → Eg.sto l = some cl →
    cl.owner = some j → Eg.pfr l ≠ none →
    (KeyG Tot HP j l → ∃ (t : Ts) (mP : Msg), tm Eg c j l = some t ∧ c.mem[t]? = some mP ∧
      t ∈ th.promises ∧ th.vs.vWr ≤ mP.view ∧
      (∀ u m, c.mem[u]? = some m → m.loc.label = l → u ≤ t → u ∈ th.promises ∨ u ≤ th.vs.coh m.loc) ∧
      (∀ u m, u ∈ Eg.fpOf j → c.mem[u]? = some m → m.loc.label = l → t < u))

/-- The clause holds where no cell has a frontier. -/
theorem plantIdx_none {tm : GEnv → Cfg → Nat → AllocLabel → Option Ts} {Eg : GEnv} {Tot HP : Nat → Res}
    {c : Cfg} (h : ∀ l, Eg.pfr l = none) : PlantIdxG tm Eg Tot HP c :=
  fun _ _ l _ _ _ _ hpf => absurd (h l) hpf

end TermPlantAtT

#print axioms TermPlantAtT.plantIdx_none
