import WeakCore.TermMainDefs
import WeakCore.TermPiece

/-! # TermReadClsDefs: the read classification interface (consumer side)

`ReadClsF`: at a thread step of `i` (any step kind), under `PromAbove` after the step, if the
stepper's coherence at a non-word unit `b` of one of its own frontier cells rises to an *old*
message (`< c.mem.size`) that was not one of its own promises, then the step read `b`, and the
piece of the cell containing `b` is non-affine.

(Writes cannot land there: a write's coherence is a new message or a fulfilled own promise
(`storeUnits_cohW`, `tstep_fulC`).  A read of `b` is a load-family op, whose loaded component
contains the piece (`TermOwnCLoad.load_piece_affine`), or a `cas`/`fetch` read of a one-word solid
component (`TermFulW.cas_cls1`/`fetch_cls1`, `piece_one`, `TermOwnCR5.aff_int`).)
-/

namespace TermReadClsDefs

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

def ReadClsF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ (b : Address) (cl : Cell), (CE η).sto b.label = some cl → cl.owner = some i →
      (CE η).pfr b.label ≠ none → ¬ WordUnit (CE η) b →
      th.vs.coh b < r.2.2.vs.coh b → r.2.2.vs.coh b < c.mem.size → r.2.2.vs.coh b ∉ th.promises →
      ∃ q U us, TermPiece.Piece cl.ty q U ∧ accs U = some us ∧ q ≤ b.offset ∧ b.offset < q + nWords us ∧
        Ty.affine U = false

/-- **A step's new messages end at or below its coherence** (at an address of the pre-step Σ):
every message the step appends is at most the stepper's post-step coherence at its address
(`TermPiece.storeUnits_newCoh` for the `storeUnits` ops; `stepRmw` likewise). -/
def NewCohF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    ∀ (t : Ts) (m : Msg) (cl : Cell), c.mem.size ≤ t → r.1[t]? = some m → (CE η).sto m.loc.label = some cl →
      t ≤ r.2.2.vs.coh m.loc

end TermReadClsDefs
