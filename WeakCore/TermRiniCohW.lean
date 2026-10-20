import WeakCore.TermRiniCoh
import WeakCore.TermOwnX2

/-!
# TermRiniCohW: install-side adapters for `RiniCoh`

* (moved to `TermRiniCoh`) `hltOwn_of_frlt`: the `frlt` (`f ≤ size - 1`) plus `0 < size` at own positive-width array cells
  (the `memPos_of_own`) gives the strict frontier `HltOwn` the lemmas consume.
* (moved to `TermRiniCoh`) `hltOwn_cut`: `HltOwn` at `Eg` holds at its cut for thread `i`.
* `riniCoh_thread`: `riniCoh_step` with `WrSiteA` from `WrIniC.wrA` (the dispatchers' route).
-/

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermMain
open TermTyped (RiniCoh)

namespace TermRiniCohW

theorem riniCoh_thread [TermTyped.WrIniC] {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {r : Memory × List Ts × TTh} {E' : TEnv}
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term)
    (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts) (hr : r ∈ tstep g mem pairs th)
    (hF : EFoot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hB : TermPlant.BiOut th E')
    (hlt : TermRiniCoh.HltOwn (CE η).sto (CE η).pfr (CE η).tid mem.size)
    (h : RiniCoh (CE η) (stOf mem pairs th)) : RiniCoh E' (stOf r.1 r.2.1 r.2.2) :=
  TermRiniCoh.riniCoh_step hm hF (TermTyped.WrIniC.wrA hE hT htv hi hm hsc hvr hr) hB hlt h

end TermRiniCohW

#print axioms TermRiniCohW.riniCoh_thread
