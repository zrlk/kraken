/-
Part 5: **the ownership plan of the Treiber stack
`treiber_pp.kl`** (1 push ∥ 1 pop with retry, `LDAR` + `CASAL`) on the
claim-conditional environment with failing release RMWs (`EnvGC`, the `FC`
link `ThreadRuleRXF.ofSafelyEnvGFC`). ISA-neutral.

Thread `0` (pusher) writes the node's data word `n1d := 1`, links
`n1n := top` and publishes `n1` by `casal` on `top`, retrying on failure.
Thread `1` (popper) reads `top` by `ldar` until non-zero, reads `next`, and
swings `top` to it by `casal`, retrying on failure; then it reads the data
word.

## The protocol of `top`

- A message of `top` is a **pusher message** if its timestamp is non-zero
  and its writer is thread `0` (`PusherMsg`), an **other message** if its
  timestamp is non-zero and its writer is not thread `0` (`OtherMsg`). Both
  are stated as "every message at `V` is …", so they are antitone in the
  memory (`Memory.Prefix`) and the predicates below are monotone.
- Acquire id `0` (`predP`, held by the popper, persistent slots): an other
  message carries the ghost token `tok` whole; a pusher message has the value
  `n1`.
- Update id `1` (`predU`, claimed by the RMW reading the message): a pusher
  message has value `n1` and carries the node (`Node`: all of `n1d` and `n1n`,
  `n1d`'s maximal write `(1, t)` with `t` at most the message's timestamp).
- `relTop`: the separating conjunction of the two. **No value of `top` is
  pure** (`relTop_not_pure`): the popper writes a loaded value, so its plan
  entry must match every value (`val := none`), and a planned release needs an
  impure value. The initial message `(top, 0)` is therefore in release mode
  with unit slots.
- Every other location has the release predicate `Pred.emp`.

## Plans

- pusher: a write of `n1` to `top` gives `[n1d, n1n]` (`pushPlan`);
- popper: any write to `top` gives `[tok]` (`popPlan`).

## Why the popper's conclusions hold (see `EnvG/TreiberVC.lean`: `vc_pop_cas`, `other_absurd`, `vc_pop_ldr`)

Under the clean erasure: its `ldar` of a non-zero value reads a pusher message
(an other message's `predP` slot holds `tok` whole, which the popper also
holds), hence `n1`; the message its successful `casal` read is a pusher
message (two other messages would be two `predP` slots holding `tok` whole),
so the claimed `predU` slot carries the node.

Contents: `Params`, `TLocs`, `PusherMsg`, `OtherMsg`, `Node`, `predP`,
`predU`, `relTop`, `ghost₀`, `pushPlan`, `popPlan` (+ validity), the initial
resources `pushRes`/`popRes`/`tRes` and the initial erasure `erase_init`.
-/
import Kraken.Promising.SLR.EnvG.State
import Kraken.Promising.SLR.EnvG.Plan
import Kraken.Promising.SLR.InitGhost
import Kraken.Promising.SLR.SpinInitRes

namespace Kraken.Promising.SLR.EnvG.Treiber

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Parameters -/

/-- The stack's locations: `top`, the node's data word `n1d` and link word
`n1n`, the ghost token `tok` (never accessed by the code), and the node's
address `n1` as a value. -/
structure Params where
  top : Loc
  n1d : Loc
  n1n : Loc
  tok : Loc
  n1 : Val

/-- The locations are pairwise distinct. -/
structure TLocs (P : Params) : Prop where
  top_d : P.top ≠ P.n1d
  top_n : P.top ≠ P.n1n
  top_t : P.top ≠ P.tok
  d_n : P.n1d ≠ P.n1n
  d_t : P.n1d ≠ P.tok
  n_t : P.n1n ≠ P.tok

/-! ## Who wrote a message -/

/-- The message at `V` (non-zero) is by the pusher, thread `0`. -/
def PusherMsg (m : Memory) (V : View) : Prop := V ≠ 0 ∧ ∀ w, m.get? V = some w → w.tid = 0

/-- The message at `V` (non-zero) is not by the pusher. -/
def OtherMsg (m : Memory) (V : View) : Prop := V ≠ 0 ∧ ∀ w, m.get? V = some w → w.tid ≠ 0

theorem PusherMsg.anti {m m' : Memory} (h : m.Prefix m') {V : View} (hp : PusherMsg m' V) : PusherMsg m V :=
  ⟨hp.1, fun w hw => hp.2 w (Memory.get?_of_prefix h.2 hw)⟩

theorem OtherMsg.anti {m m' : Memory} (h : m.Prefix m') {V : View} (hp : OtherMsg m' V) : OtherMsg m V :=
  ⟨hp.1, fun w hw => hp.2 w (Memory.get?_of_prefix h.2 hw)⟩

theorem pusherMsg_of_get {m : Memory} {V : View} {w : Msg} (hV : V ≠ 0) (hw : m.get? V = some w) (h0 : w.tid = 0) :
    PusherMsg m V :=
  ⟨hV, fun w' hw' => by rw [hw] at hw'; cases hw'; exact h0⟩

theorem otherMsg_of_get {m : Memory} {V : View} {w : Msg} (hV : V ≠ 0) (hw : m.get? V = some w) (h0 : w.tid ≠ 0) :
    OtherMsg m V :=
  ⟨hV, fun w' hw' => by rw [hw] at hw'; cases hw'; exact h0⟩

theorem not_otherMsg_of_pusher {m : Memory} {V : View} {w : Msg} (hw : m.get? V = some w) (hp : PusherMsg m V) :
    ¬ OtherMsg m V := fun ho => ho.2 w hw (hp.2 w hw)

/-! ## The predicates -/

/-- The node, as the pusher's release message at `V` carries it: all of `n1d`
and `n1n`, and `n1d`'s maximal write is `(1, t)` with `t ≤ V`. -/
def Node (P : Params) (V : View) (R : Res) : Prop :=
  (R.wr P.n1d).q = 1 ∧ (R.wr P.n1n).q = 1 ∧
    ∃ t, t ≤ V ∧ (R.wr P.n1d).X (1#128, t) ∧ ∀ p, (R.wr P.n1d).X p → p.2 ≤ t

/-- **Acquire id `0`** (held by the popper): an other message carries the
token whole; a pusher message has the value `n1`. -/
def predP (P : Params) : Pred where
  P v m V R := (OtherMsg m V → (R.wr P.tok).q = 1) ∧ (PusherMsg m V → v = P.n1)
  mono _ _ _ _ _ hpre h := ⟨fun ho => h.1 (ho.anti hpre), fun hp => h.2 (hp.anti hpre)⟩

/-- **Update id `1`**: a pusher message has the value `n1` and carries the
node. -/
def predU (P : Params) : Pred where
  P v m V R := PusherMsg m V → v = P.n1 ∧ Node P V R
  mono _ _ _ _ _ hpre h := fun hp => h (hp.anti hpre)

/-- **The release predicate of `top`**: `predP ⊛ predU`. -/
def relTop (P : Params) : Pred where
  P v m V R := ∃ R₁ R₂, R = R₁.op R₂ ∧ (predP P).P v m V R₁ ∧ (predU P).P v m V R₂
  mono v m m' V R hpre h := by
    obtain ⟨R₁, R₂, he, h1, h2⟩ := h
    exact ⟨R₁, R₂, he, (predP P).mono v m m' V R₁ hpre h1, (predU P).mono v m m' V R₂ hpre h2⟩

/-- No value of `top` is pure: at a pusher message, the empty resource holds
no node. -/
theorem relTop_not_pure (P : Params) (v : Val) : ¬ Pred.Pure (relTop P) v := by
  intro h
  let m : Memory := { init := [], msgs := #[⟨P.top, v, 0⟩] }
  obtain ⟨R₁, R₂, he, -, h2⟩ := h m 1
  have hp : PusherMsg m 1 := pusherMsg_of_get (w := ⟨P.top, v, 0⟩) (by decide) rfl rfl
  obtain ⟨-, hq, -⟩ := h2 hp
  have e := congrArg (fun r : Res => (r.wr P.n1d).q) he
  simp only [Res.unit, Perm.unit, Res.op, Perm.op] at e
  have h1 := (R₁.wr P.n1d).nonneg
  rw [hq] at e
  grind

/-- **The release predicate of `top` from its parts.** -/
theorem relTop_of {P : Params} {v : Val} {m : Memory} {V : View} {R₁ R₂ : Res} (h1 : (predP P).P v m V R₁)
    (h2 : (predU P).P v m V R₂) : (relTop P).P v m V (R₁.op R₂) :=
  ⟨R₁, R₂, rfl, h1, h2⟩

/-! ## The initial ghost -/

/-- **The initial ghost**: `relTop` at `top` (`Pred.emp` elsewhere); acquire
table `[predP, predU]`; the initial message of `top` in release mode with
unit slots for both ids; update id `1` at `top`. -/
def ghost₀ (P : Params) : Ghost where
  rel x := if x = P.top then relTop P else Pred.emp
  acqTab := [predP P, predU P]
  u := [⟨(P.top, 0), 0, Res.unit⟩, ⟨(P.top, 0), 1, Res.unit⟩]
  relMsgs := [(P.top, 0)]
  pend := []
  upd x := if x = P.top then [1] else []
  claims := []

theorem ghost₀_rel_top (P : Params) : (ghost₀ P).rel P.top = relTop P := by simp [ghost₀]

theorem ghost₀_rel_ne {P : Params} {x : Loc} (h : x ≠ P.top) : (ghost₀ P).rel x = Pred.emp := by
  simp [ghost₀, h]

theorem ghost₀_acqPred_zero (P : Params) : (ghost₀ P).acqPred 0 = predP P := rfl

theorem ghost₀_acqPred_one (P : Params) : (ghost₀ P).acqPred 1 = predU P := rfl

theorem ghost₀_upd_top (P : Params) : (ghost₀ P).upd P.top = [1] := by simp [ghost₀]

theorem ghost₀_pend (P : Params) : ∀ ts, ts ∉ (ghost₀ P).pend := fun _ h => by cases h

/-! ## The plans -/

/-- **The pusher's plan**: publishing `n1` on `top` gives the node. -/
def pushPlan (P : Params) : Plan := ⟨[{ loc := P.top, val := some P.n1, gives := [P.n1d, P.n1n] }]⟩

/-- **The popper's plan**: every write to `top` gives the token. -/
def popPlan (P : Params) : Plan := ⟨[{ loc := P.top, gives := [P.tok] }]⟩

theorem pushPlan_valid {P : Params} (hL : TLocs P) : (pushPlan P).Valid := by
  intro e he
  simp only [pushPlan, List.mem_singleton] at he
  subst he
  simp [hL.top_d, hL.top_n]

theorem popPlan_valid {P : Params} (hL : TLocs P) : (popPlan P).Valid := by
  intro e he
  simp only [popPlan, List.mem_singleton] at he
  subst he
  simp [hL.top_t]

theorem pushPlan_rel (P : Params) (l : Loc) (v : Val) : (pushPlan P).rel l v = (decide (l = P.top) && decide (v = P.n1)) := by
  by_cases h1 : l = P.top
  · subst h1
    by_cases h2 : v = P.n1
    · subst h2; simp [pushPlan, Plan.rel, Plan.find?]
    · simp [pushPlan, Plan.rel, Plan.find?, Ne.symm h2, h2]
  · simp [pushPlan, Plan.rel, Plan.find?, Ne.symm h1, h1]

theorem pushPlan_gives (P : Params) : (pushPlan P).gives P.top P.n1 = [P.n1d, P.n1n] := by
  simp [pushPlan, Plan.gives, Plan.find?]

theorem pushPlan_give (P : Params) (cl : Prop) (r : Res) :
    (pushPlan P).give P.top P.n1 cl r = Res.only [P.n1d, P.n1n] r := by
  simp [pushPlan, Plan.give, Plan.find?, Plan.Entry.give]

theorem popPlan_rel (P : Params) (l : Loc) (v : Val) : (popPlan P).rel l v = decide (l = P.top) := by
  by_cases h1 : l = P.top
  · subst h1; simp [popPlan, Plan.rel, Plan.find?]
  · simp [popPlan, Plan.rel, Plan.find?, Ne.symm h1, h1]

theorem popPlan_gives (P : Params) (v : Val) : (popPlan P).gives P.top v = [P.tok] := by
  simp [popPlan, Plan.gives, Plan.find?]

theorem popPlan_give (P : Params) (v : Val) (cl : Prop) (r : Res) :
    (popPlan P).give P.top v cl r = Res.only [P.tok] r := by
  simp [popPlan, Plan.give, Plan.find?, Plan.Entry.give]

/-! ## The initial resources -/

/-- The pusher's initial fractions: two thirds of `top` (more than half: the
pusher's token in the shared postcondition), all of the node. -/
def pushFrac (P : Params) (x : Loc) : Rat :=
  if x = P.top then 2 / 3 else if x = P.n1d ∨ x = P.n1n then 1 else 0

/-- The popper's initial fractions: a third of `top`, all of the token. -/
def popFrac (P : Params) (x : Loc) : Rat :=
  if x = P.top then 1 / 3 else if x = P.tok then 1 else 0

theorem pushFrac_nonneg (P : Params) (x : Loc) : 0 ≤ pushFrac P x := by
  unfold pushFrac; split
  · grind
  · split <;> grind

theorem popFrac_nonneg (P : Params) (x : Loc) : 0 ≤ popFrac P x := by
  unfold popFrac; split
  · grind
  · split <;> grind

/-- The pusher's initial resource. -/
def pushRes (m : Memory) (P : Params) : Res := Res.initOf m (pushFrac P) (pushFrac_nonneg P)

/-- The popper's initial resource: its fractions and the acquire id `0` of
`top`. -/
def popRes (m : Memory) (P : Params) : Res :=
  ⟨(Res.initOf m (popFrac P) (popFrac_nonneg P)).wr, fun x ι => if x = P.top ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: thread `0` the pusher, thread `1` the
popper. -/
def tRes (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then pushRes m P else if i = 1 then popRes m P else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost₀ (P : Params) : (ghost₀ P).slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost₀, Res.prod, Res.op_unit]

/-- The initial total: the pusher's and the popper's resources. -/
theorem total_init (P : Params) (m : Memory) :
    total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem) = (pushRes m P).op (popRes m P) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes m P 0, tRes m P 1] = _
  simp [tRes, Res.op_unit]

theorem total_init_q (P : Params) (m : Memory) (x : Loc) :
    ((total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem)).wr x).q = pushFrac P x + popFrac P x := by
  rw [total_init]; rfl

theorem total_init_acq (P : Params) (m : Memory) (x : Loc) (ι : PredId) :
    (total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem)).acq x ι = if x = P.top ∧ ι = 0 then 1 else 0 := by
  rw [total_init]
  show 0 + _ = _
  exact Nat.zero_add _

theorem total_init_X (P : Params) (m : Memory) (x : Loc) (p : Val × Time) :
    ((total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem)).wr x).X p ↔
      (0 < pushFrac P x ∨ 0 < popFrac P x) ∧ p = (m.initVal x, 0) := by
  rw [total_init]
  show (0 < pushFrac P x ∧ p = _) ∨ (0 < popFrac P x ∧ p = _) ↔ _
  constructor
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact ⟨.inl h, rfl⟩
    · exact ⟨.inr h, rfl⟩
  · rintro ⟨h | h, rfl⟩
    · exact .inl ⟨h, rfl⟩
    · exact .inr ⟨h, rfl⟩

/-- **Initial erasure of the Treiber stack.** -/
theorem erase_init {P : Params} (hL : TLocs P) (T : Nat → Prop) :
    Erase (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) T (Config.init [s0, s1] initMem) := by
  have hq := total_init_q (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha := total_init_acq (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have hX := total_init_X (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have htd := hL.top_d; have htn := hL.top_n; have htt := hL.top_t
  have hdn := hL.d_n; have hdt := hL.d_t; have hnt := hL.n_t
  have hids : ∀ x, (ghost₀ P).acqIds
      (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) (Config.init [s0, s1] initMem)).acq x =
        if x = P.top then [0] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (ghost₀ P).acqTab.length = 2 from rfl]
    by_cases hx : x = P.top <;> simp [hx, ha, List.range_succ]
  refine Erase.init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- valid
    refine ⟨fun x => ?_, fun x ι => ?_⟩
    · rw [hq]
      unfold pushFrac popFrac
      by_cases h1 : x = P.top
      · simp [h1]; grind
      · by_cases h2 : x = P.n1d
        · subst h2; simp [h1, hdt] <;> grind
        · by_cases h3 : x = P.n1n
          · subst h3; simp [h1, h2, hnt] <;> grind
          · by_cases h4 : x = P.tok <;> simp [h1, h2, h3, h4] <;> grind
    · rw [ha]; split <;> decide
  · -- slot ids
    intro s hs
    simp only [ghost₀, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [ghost₀]
  · -- held acquire ids
    intro x ι h
    rw [ha] at h
    split at h
    · next he => rw [he.2]; simp [ghost₀]
    · exact absurd h (by decide)
  · -- release predicates split
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    by_cases hx : x = P.top
    · subst hx
      rw [ghost₀_rel_top] at h
      obtain ⟨R₁, R₂, rfl, h1, h2⟩ := h
      simp only [↓reduceIte, List.map_cons, List.map_nil, Ghost.updPreds, ghost₀_upd_top, List.cons_append,
        List.nil_append]
      exact ⟨R₁, R₂, rfl, h1, R₂, Res.unit, (Res.op_unit R₂).symm, h2, rfl⟩
    · rw [ghost₀_rel_ne hx] at h
      simp only [hx, ↓reduceIte, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact h
  · -- write sets
    intro x hpos p
    rw [hX]
    have : 0 < pushFrac P x ∨ 0 < popFrac P x := by
      rw [hq] at hpos
      have := pushFrac_nonneg P x; have := popFrac_nonneg P x
      by_cases h0 : 0 < pushFrac P x
      · exact .inl h0
      · exact .inr (by grind)
    simp [this]
  · -- relaxed initial messages are pure
    intro x hx
    have hx' : x ≠ P.top := fun h => hx (by simp [ghost₀, h])
    rw [ghost₀_rel_ne hx']
    exact Pred.emp_pure _
  · -- release messages are initial
    intro k hk
    simp only [ghost₀, List.mem_singleton] at hk
    subst hk; rfl
  · -- slots are distinct
    simp [ghost₀]
  · -- slot domain
    intro k ι
    rw [ha]
    simp only [ghost₀, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨s, rfl | rfl, rfl, rfl⟩
      · simp
      · simp
    · rintro ⟨rfl, h⟩
      by_cases h0 : ι = 0
      · subst h0; exact ⟨_, .inl rfl, rfl, rfl⟩
      · have : ι = 1 := by
          rcases h with h | h
          · simp [h0] at h
          · simpa using h
        subst this; exact ⟨_, .inr rfl, rfl, rfl⟩
  · -- slots satisfy their predicates at the initial message (view `0`)
    intro s hs
    simp only [ghost₀, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨fun ho => absurd rfl ho.1, fun hp => absurd rfl hp.1⟩
    · exact fun hp => absurd rfl hp.1
  · -- update ids
    intro x
    by_cases hx : x = P.top
    · subst hx
      rw [ghost₀_upd_top]
      refine ⟨by simp, fun ι hι => ?_⟩
      rw [List.mem_singleton] at hι
      subst hι
      exact ⟨by simp [ghost₀], by rw [ha]; simp⟩
    · simp [ghost₀, hx]

end Init

end Kraken.Promising.SLR.EnvG.Treiber
