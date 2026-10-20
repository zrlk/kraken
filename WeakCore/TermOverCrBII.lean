import WeakCore.TermPoolDefs
import WeakCore.TermMainDefs
import WeakCore.TermOwnG0Defs

/-! # TermOverCrBII: the open staging obligations of the `pool` clause's cover

Named `Prop`s, threaded as hypotheses (never gated as closed):
* `OpenOverCrOwn`: the stepping thread's own cover after its step (split by step kind:
  `OpenOverCrOwnA` for the own-path ops, `opAtomP` some; `OpenOverCrOwnC` for the rest);
* `OpenOverCrProm`: the cover after a promise step.
The credits are `crPl` (`TermPool`): the stepping thread's are its new credits `cr'` plus its
kept pool credits and the step's new pool credits `plh`.
-/

namespace TermOverCrBII
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The stepping thread's pool credits after its step: the old ones at its still outstanding
promises, plus the step's new ones `plh`. -/
noncomputable def plStep (pl : Nat → Ts → Res) (i : Nat) (s' : St) (plh : Ts → Res) : Ts → Res := by
  classical
  exact fun t => (if t ∈ s'.promises then pl i t else .zero) + plh t

/-- (a‴, R4 resplit) **The stepper's credits `crS`**: the stepping thread's pre credits `cr i` plus
the pool credits `plq` it moves back at promises the step discharges (each `plq t` is `0` or the whole
`pl i t`, and nonzero only off the post promises `P'`).  The members keep the pre-step `TCtx`, cover,
tags and `PoolInv` at `(cr, pl)`; the stepper's outputs (`TOut`, `KeepQRS(B)`, `IneqH`, the inequality)
are at `crS`.  Since `plq` lives off `P'`, `plStep pl i` drops it, so `plq` is counted once (in `crS`). -/
def StepCrQ (cr pl : Nat → Ts → Res) (i : Nat) (P' : List Ts) (crS : Ts → Res) : Prop :=
  ∃ plq : Ts → Res, (∀ t, crS t = cr i t + plq t) ∧ (∀ t, plq t = .zero ∨ plq t = pl i t) ∧
    ∀ t, plq t ≠ .zero → t ∉ P'

/-- (staging, thread step, stepping thread `i`) **The own cover after the step**, restricted to
the step kinds `K` (on the pre-step term).  Hypotheses: the step context, the stepper's output at
its witness `E'` (with the new pool credits `plh`, the `KeepQRS` slot), and the pre-state's pool
cover and tags. -/
def OpenOverCrOwnK (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (K : TEnv → Cx → TTh → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    (pl : Nat → Ts → Res),
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    K (CE η) cx th → PromAbove (stOf r.1 r.2.1 r.2.2) →
    TermOverCr.OverCrG Eg c (crPl cr pl) → PoolTag Eg c pl →
    ∀ (crS : Ts → Res), StepCrQ cr pl i r.2.2.promises crS →
    ∀ (Tot' H' C F : Res) (cr' db' plh : Ts → Res) (Gd : List TermPiece.GdE) (E' : TEnv),
    TermPlant.BiOut th E' → TermPlant.KeepQRSB (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) th crS cr' plh →
    IniFixZ { gOf p k arch c i with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
      (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
    (TermPlant.OwnFrOp (CE η) cx th → r.1 = c.mem) →
    EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) →
    SeenOK (CE η) E' Tot' H' → ThInvRE p E' r.2.2 Tot' → MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2) →
    MemHeld E' (stOf r.1 r.2.1 r.2.2) H' → TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db' →
    MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F →
    TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd →
    Tot' + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf c.mem c.pairs th) (db i) + C +
        Res.sum (Gd.map TermPiece.GdE.R) + pSum (stOf r.1 r.2.1 r.2.2) plh ≤
      Rf + Rs + (HP i + HS) + pSum (stOf c.mem c.pairs th) crS + pSum (stOf r.1 r.2.1 r.2.2) db' + F →
    (∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) → (∀ t, TermPlant.CrKeys (plh t)) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ (Sj : AllocLabel → Prop) l cl,
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj).sto l = some cl → cl.owner = some i →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none →
      TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i Sj)
        (stOf c'.mem c'.pairs r.2.2) (fun t => cr' t + plStep pl i (stOf r.1 r.2.1 r.2.2) plh t) l cl

/-- The own-path op kinds (store, xchg, xchgAt, xchgAtF, stl, stlw, bufInit) at an own frontier
target (`OwnFrOp`): the share. -/
def KindA (E : TEnv) (cx : Cx) (th : TTh) : Prop :=
  (TermPiece.opAtomP th.term).isSome = true ∧ TermPlant.OwnFrOp E cx th

/-- The remaining kinds (memory-appending, alloc, publish, load, …, and the own-path ops off an own
frontier target): the share. -/
def KindC (E : TEnv) (cx : Cx) (th : TTh) : Prop := ¬ KindA E cx th

/-- (staging) The own cover at the own-path op kinds. -/
def OpenOverCrOwnA (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop := OpenOverCrOwnK p k arch Sp Init MintOK c0 KindA

/-- (staging) The own cover at the remaining kinds. -/
def OpenOverCrOwnC (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop := OpenOverCrOwnK p k arch Sp Init MintOK c0 KindC

/-- (staging) The own cover at every step kind. -/
def OpenOverCrOwn (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop := OpenOverCrOwnK p k arch Sp Init MintOK c0 (fun _ _ _ => True)

/-- The two shares give the whole. -/
theorem openOverCrOwn_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hA : OpenOverCrOwnA p k arch Sp Init MintOK c0) (hC : OpenOverCrOwnC p k arch Sp Init MintOK c0) :
    OpenOverCrOwn p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs pl X Y _
  by_cases e : KindA (CE η) cx th
  · exact hA pl X Y e
  · exact hC pl X Y e

/-- (staging, promise step of `j`) **The cover after a promise step**: the pool is unchanged
(the new promise carries no pool credit), the promiser's credits are its new ones `cr'`
(`PAcct`, `ThSys` at the planted environment). -/
def OpenOverCrProm (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (pl : Nat → Ts → Res),
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size →
    TermOverCr.OverCrG Eg c (crPl cr pl) → PoolTag Eg c pl →
    ∀ (HP' HS' : Res) (cr' db' : Ts → Res),
    PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' →
    (∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop, ¬ WordUnit (Cut Eg j S) m.loc →
      cr' t = cr j t) →
    ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
      (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db' →
    TermOverCr.OverCrG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w)
      (crPl (upd cr j cr') pl)

end TermOverCrBII
