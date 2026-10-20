/-
Step lemmas for program proofs over the `EnvG` state. ISA-neutral.

What a per-access verification condition over `EnvG` needs, as found by the
MP smoke test (`EnvG/MpSmoke.lean`): after `step_storeFacts`/`step_loadFacts`
the goal mentions the plan (`Plan.rel`/`gives`/`give`/`keep`/`after` on a
concrete entry list), the split resources (`Res.only`/`Res.drop`), the write
set update (`Res.addW`), the effective release kind (`effRel`), the read
bound and the forwarding buffer, and the re-anchor (`AnchorOk`: ghost and
snapshot). The lemmas:

- **`@[simp]`, `ok`/`step`** (`envG_ok_load_st`, `envG_ok_fence_st`,
  `envG_ok_store`, `envG_ok_rmw`, `envG_step_load`, `envG_step_store`,
  `envG_step_rmw`, `envG_step_fence`): the environment's `ok`/`step` at an
  access become `StoreOk`/`RmwOk`/`LoadOut`/`StoreOut`/`RmwOut`/`FenceOut`.
  They are stated at states typed `(EnvG I A tid pl).State`, as `vcgen` goals
  carry them; `simp` does not match the `State I`-typed `envG_ok_load` of
  `EnvG/Env.lean` there. Without them `simp` unfolds `step` to the raw `match`
  on the access and cannot normalise the access's address and value.
- **`@[simp]`, plans** (`Plan.find?_mk_nil`, `Plan.find?_mk_cons`,
  `Plan.rel_eq`, `Plan.gives_eq`, `Plan.give_eq`, `Plan.keep_eq`,
  `Plan.after_eq`): a plan given by an entry list reduces to `if`s on location
  and value equalities, which `simp` decides from disequality hypotheses.
- **`@[simp]`, split resources** (`Res.only_wr`, `Res.only_acq`,
  `Res.drop_wr`, `Res.drop_acq`).
- **`@[simp]`, kinds** (`effRel_rel`, `storeKind_rel`, `loadKind_acq`,
  `isAcquire_acq`, `armv8_storeKind_plain`, `armv8_loadKind_plain`).
- **`@[simp]`, fences and `seen`** (`fenceSetsR_sy`, …, `seenAfter_plain`):
  the bits and the `seen` list after a fence / non-acquire load.
- **Forward lemmas** (not `simp`; a VC applies them to the facts it
  destructures): `AnchorOk.rel`/`AnchorOk.acqPred` (the world facts carry
  over a re-anchor), `SnapLe.read?`/`AnchorOk.read?` (a message read at the
  old snapshot is read at the new one), `LoadViews.getFwd` (a load keeps the
  forwarding buffers), `not_fwded_of_none`, `le_readBound_vrNew`.
-/
import Kraken.Promising.SLR.EnvG.Env
import Kraken.Promising.SLR.EnvG.Seen

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## `ok` and `step` as the named predicates

Without these, `simp` reduces `(EnvG I A tid pl).step a …` to the raw `match`
on the access, which blocks normalising the access's address and value
(`vcgen` goals). With them, the step becomes the opaque `LoadOut`/`StoreOut`
/`RmwOut`/`FenceOut` with normalised arguments, ready for `loadOut_facts`
etc. -/

/-- `envG_ok_load` (`EnvG/Env.lean`) at a state typed `(EnvG I A tid pl).State`,
as `vcgen` goals carry it. -/
@[simp] theorem envG_ok_load_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvG I A tid pl).State) (k : LoadKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) : (EnvG I A tid pl).ok (.load k xcl addr n) σ := trivial

/-- `envG_ok_fence` at a state typed `(EnvG I A tid pl).State`. -/
@[simp] theorem envG_ok_fence_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvG I A tid pl).State) (k : FenceKind) :
    (EnvG I A tid pl).ok (.fence k) σ := trivial

@[simp] theorem envG_ok_store (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvG I A tid pl).State) (k : StoreKind)
    (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvG I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envG_ok_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvG I A tid pl).State) (k : RmwKind) (addr : BitVec 64)
    (n : Nat) (op : Val → Option Val) : (EnvG I A tid pl).ok (.rmw k addr n op) σ = RmwOk A tid pl σ k ⟨addr, n⟩ op :=
  rfl

@[simp] theorem envG_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvG I A tid pl).State) (k : LoadKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvG I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOut A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envG_step_store (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvG I A tid pl).State) (k : StoreKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvG I A tid pl).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envG_step_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvG I A tid pl).State) (k : RmwKind) (addr : BitVec 64)
    (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvG I A tid pl).step (.rmw k addr n op) σ old σ' = RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old := rfl

@[simp] theorem envG_step_fence (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvG I A tid pl).State) (k : FenceKind) (u : Unit) :
    (EnvG I A tid pl).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-! ## Plans on concrete entry lists -/

namespace Plan

@[simp] theorem find?_mk_nil (l : Loc) (v : Val) : Plan.find? ⟨[]⟩ l v = none := rfl

@[simp] theorem find?_mk_cons (e : Plan.Entry) (es : List Plan.Entry) (l : Loc) (v : Val) :
    Plan.find? ⟨e :: es⟩ l v =
      if e.loc = l ∧ (∀ w, e.val = some w → w = v) then some e else Plan.find? ⟨es⟩ l v := by
  unfold find?
  rw [List.find?_cons]
  cases hv : e.val with
  | none => by_cases hl : e.loc = l <;> simp [hl]
  | some w => by_cases hl : e.loc = l <;> by_cases hw : w = v <;> simp [hl, hw]

@[simp] theorem rel_eq (pl : Plan) (l : Loc) (v : Val) : pl.rel l v = (pl.find? l v).isSome := rfl

@[simp] theorem gives_eq (pl : Plan) (l : Loc) (v : Val) : pl.gives l v = ((pl.find? l v).map (·.gives)).getD [] :=
  rfl

theorem give_eq (pl : Plan) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    pl.give l v cl r = match pl.find? l v with
      | some e => e.give cl r
      | none => Res.only [] r := rfl

theorem keep_eq (pl : Plan) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    pl.keep l v cl r = match pl.find? l v with
      | some e => e.keep cl r
      | none => Res.drop [] r := rfl

theorem after_eq (pl : Plan) (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    pl.after l v tw cl r = if pl.rel l v then (pl.keep l v cl r).addW l (v, tw) else r.addW l (v, tw) := rfl

/-- A whole-location entry gives `Res.only gives` (F1). -/
@[simp] theorem Entry.give_none (loc : Loc) (val : Option Val) (gives : List Loc) (cl : Prop) (r : Res) :
    Plan.Entry.give { loc, val, gives, split := none } cl r = Res.only gives r := rfl

/-- A whole-location entry keeps `Res.drop gives` (F1). -/
@[simp] theorem Entry.keep_none (loc : Loc) (val : Option Val) (gives : List Loc) (cl : Prop) (r : Res) :
    Plan.Entry.keep { loc, val, gives, split := none } cl r = Res.drop gives r := rfl

attribute [simp] give_eq keep_eq after_eq

/-- The knowledge a whole-location release's split was chosen with is
irrelevant: `StoreFacts`' `∃ P, (σ.cl → P) ∧ σ'.r = …` with a `P`-free
right side simplifies to the equation (F1). -/
@[simp] theorem _root_.Kraken.Promising.SLR.EnvG.exists_imp_prop (c : Prop) : (∃ P : Prop, c → P) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨True, fun _ => trivial⟩⟩

end Plan

/-! ## Split resources -/

@[simp] theorem Res.only_wr (L : List Loc) (r : Res) (x : Loc) :
    (Res.only L r).wr x = if x ∈ L then r.wr x else Perm.unit := rfl

@[simp] theorem Res.only_acq (L : List Loc) (r : Res) (x : Loc) (ι : PredId) :
    (Res.only L r).acq x ι = if x ∈ L then r.acq x ι else 0 := rfl

@[simp] theorem Res.drop_wr (L : List Loc) (r : Res) (x : Loc) :
    (Res.drop L r).wr x = if x ∈ L then Perm.unit else r.wr x := rfl

@[simp] theorem Res.drop_acq (L : List Loc) (r : Res) (x : Loc) (ι : PredId) :
    (Res.drop L r).acq x ι = if x ∈ L then 0 else r.acq x ι := rfl

/-! ## Kinds -/

@[simp] theorem storeKind_rel (A : Arch) : A.storeKind .rel = .rel := rfl

@[simp] theorem loadKind_acq (A : Arch) : A.loadKind .acq = .acq := rfl

@[simp] theorem isAcquire_acq : LoadKind.isAcquire .acq = true := rfl

@[simp] theorem armv8_storeKind_plain : Arch.armv8.storeKind .plain = .plain := rfl

@[simp] theorem armv8_loadKind_plain : Arch.armv8.loadKind .plain = .plain := rfl

/-- A release store is an effective release in every state. -/
@[simp] theorem effRel_rel (A : Arch) (σ : State I) : effRel A σ .rel := .inl rfl

/-! ## Fence bits and `seen` -/

@[simp] theorem fenceSetsR_sy : fenceSetsR .sy = true := rfl
@[simp] theorem fenceSetsW_sy : fenceSetsW .sy = true := rfl
@[simp] theorem fenceSetsW_st : fenceSetsW .st = true := rfl
@[simp] theorem fenceSetsR_ld : fenceSetsR .ld = false := rfl
@[simp] theorem fenceSetsW_ld : fenceSetsW .ld = false := rfl

/-- A non-acquire load records nothing. -/
@[simp] theorem seenAfter_plain (σ : State I) (g : Ghost) (l : Loc) (tr : Time) :
    seenAfter Arch.armv8 .plain σ g l tr = σ.seen := rfl

/-! ## Forward lemmas: re-anchors -/

/-- The release predicates carry over a re-anchor. -/
theorem AnchorOk.rel {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (h : AnchorOk tid σ c g) :
    g.rel = σ.g.rel :=
  h.ghost.rel

/-- An allocated acquire id keeps its predicate over a re-anchor. -/
theorem AnchorOk.acqPred {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (h : AnchorOk tid σ c g)
    {ι : PredId} (hι : ι < σ.g.acqTab.length) : g.acqPred ι = σ.g.acqPred ι :=
  Ghost.acqPred_of_prefix h.ghost.acqTab hι

/-- An allocated acquire id stays allocated over a re-anchor. -/
theorem AnchorOk.acqLen {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (h : AnchorOk tid σ c g)
    {ι : PredId} (hι : ι < σ.g.acqTab.length) : ι < g.acqTab.length :=
  Nat.lt_of_lt_of_le hι h.ghost.acqTab.length_le

/-- A message read at a snapshot is read at every later anchor. -/
theorem SnapLe.read? {tid : Nat} {c c' : Config I} (h : SnapLe tid c c') {l : Loc} {ts : Time} {v : Val}
    (hr : c.mem.read? l ts = some v) : c'.mem.read? l ts = some v := by
  have hpre : c.mem.Prefix c'.mem := ⟨h.init, h.msgs⟩
  have hle : ts ≤ c.mem.last := by
    unfold Memory.read? at hr
    split at hr
    · next h0 => rw [h0]; exact Nat.zero_le _
    · split at hr
      · next w hw => exact c.mem.last_le_of_get?_eq_some hw
      · cases hr
  rw [hpre.read? hle]; exact hr

theorem AnchorOk.read? {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (h : AnchorOk tid σ c g) {l : Loc}
    {ts : Time} {v : Val} (hr : σ.snap.mem.read? l ts = some v) : c.mem.read? l ts = some v :=
  h.snap.read? hr

/-! ## Forward lemmas: views -/

/-- A load keeps the forwarding buffers. -/
theorem LoadViews.getFwd {A : Arch} {vs vs' : Views} {k : LoadKind} {l : Loc} {tr : Time}
    (h : LoadViews A vs vs' k l tr) (l' : Loc) : vs'.getFwd l' = vs.getFwd l' := by
  simp only [Views.getFwd, h.fwdb]

/-- No forwarding item, no forwarded read. -/
theorem not_fwded_of_none {vs : Views} {l : Loc} {tr : Time} (h : vs.getFwd l = none) : ¬ Fwded vs l tr :=
  fun ⟨_, hf, _⟩ => by rw [h] at hf; cases hf

/-- The read bound is at least `vrNew`. -/
theorem le_readBound_vrNew (A : Arch) (vs : Views) (k : LoadKind) (l : Loc) : vs.vrNew ≤ readBound A vs k l :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)

end Kraken.Promising.SLR.EnvG
