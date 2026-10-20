/-
Part 1: **the ownership plan of the two-thread
Treiber stack** `treiber2_nodes.kl` / `treiber2.kl` (thread `w` pushes node
`w` by `ldar`/`str`/`casal`, then pops once by `ldar`/`ldr`/`casal`) on the
adjacency link `EnvGCAdj` (`EnvG/AdjSpike.lean`). ISA-neutral.

## Why not a history predicate with pop values

A history invariant constraining the value a pop writes (`next` of the node
it read) cannot be established in a pop's release obligation: the popper
does not own the node's link at its `ldr`, and the RMW adds no clean-erasure
knowledge. So the release predicate of `top` only **freezes the pusher's
node** at its push message; all history reasoning happens at the final clean
erasure (`EnvG/Treiber2Final.lean`, `EnvG/Treiber2Hist.lean`).

## The protocol of `top`

- Acquire id `0` (`predA`, held by thread `0` for good): every non-initial
  message of `top` is by a thread `w < 2` and is
  - a **push form** of `w` (`PushF`): its value is the node `nv w`, it
    carries the node's link `nd w` and data word `dd w` whole, whose maximal
    writes are below the message, and the message of `top` it overwrites is
    adjacent and has the value the link holds (`NoTopIn`, from
    `AdjAt.lastAt`); or
  - a **pop form** of `w` (`PopF`): it carries the pop token `pt w`, and an
    earlier message of `top` by `w` has the value `nv w`.
- Acquire id `1` (`Pred.top`, held by thread `1`): identity only (the shared
  postcondition tells the two threads apart by it).
- `relTop := predA`, impure at every value (`relTop_not_pure`), so every
  plan entry of `top` is `val := none` and the initial message is in release
  mode with unit slots. Every other location has `Pred.emp`.

## Plans

Thread `w` has one entry: every write to `top` releases with the split
`split w`: before its push (`top`'s write set holds only the initial
message) the node `[nd w, dd w]`, afterwards the pop token `[pt w]`.

Contents: `Params` (concrete locations from `t`, `n w`; the data-word
property `D`), `TLocs`, `NoTopIn`, `PushF`, `PopF`, `predA`, `relTop`,
`ghost₀`, `split`, `plan` (+ validity), the initial resources and
`erase_init`.
-/
import Kraken.Promising.SLR.EnvG.TreiberVC

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber (read?_of_get? get?_of_read? initVal_eq)

variable {I : ISA}

/-! ## Parameters -/

/-- The stack's parameters: `top` at `t` (8 bytes); node `w` at `n w`, its
data word `[n w]` (4 bytes) and link `[n w + 8]` (8 bytes); the data-word
property `D w` the push freezes (`True` without data words). -/
structure Params where
  t : BitVec 64
  n : Nat → BitVec 64
  D : Nat → Val → Prop

namespace Params

variable (P : Params)

/-- `top`. -/
def top : Loc := ⟨P.t, 8⟩

/-- Node `w`'s link word. -/
def nd (w : Nat) : Loc := ⟨P.n w + 8, 8⟩

/-- Node `w`'s data word. -/
def dd (w : Nat) : Loc := ⟨P.n w, 4⟩

/-- Thread `w`'s pop token (a ghost location: no access of the code has
`1` or `2` bytes). -/
def pt (w : Nat) : Loc := ⟨P.t, if w = 0 then 1 else 2⟩

/-- Node `w`'s address as a value. -/
def nv (w : Nat) : Val := BitVec.setWidth 128 (P.n w)

end Params

/-- The layout hypotheses: `top` is not a link word, the nodes are distinct
and non-null. -/
structure TLocs (P : Params) : Prop where
  top_nd : ∀ w, w < 2 → P.t ≠ P.n w + 8
  n_ne : P.n 0 ≠ P.n 1
  n_nz : ∀ w, w < 2 → P.n w ≠ 0

namespace TLocs

variable {P : Params} (hL : TLocs P)
include hL

theorem top_nd' {w : Nat} (hw : w < 2) : P.top ≠ P.nd w := by
  intro h
  simp only [Params.top, Params.nd, Loc.mk.injEq, and_true] at h
  exact hL.top_nd w hw h

theorem nd_ne : P.nd 0 ≠ P.nd 1 := by
  intro h
  simp only [Params.nd, Loc.mk.injEq, and_true] at h
  exact hL.n_ne (by bv_omega)

theorem dd_ne : P.dd 0 ≠ P.dd 1 := by
  intro h
  simp only [Params.dd, Loc.mk.injEq, and_true] at h
  exact hL.n_ne h

theorem nv_ne : P.nv 0 ≠ P.nv 1 := by
  intro h
  have := congrArg (BitVec.setWidth 64) h
  simp [Params.nv] at this
  exact hL.n_ne this

end TLocs

section Distinct

variable (P : Params) (w w' : Nat)

theorem top_dd : P.top ≠ P.dd w := by simp [Params.top, Params.dd]
theorem top_pt : P.top ≠ P.pt w := by simp only [Params.top, Params.pt, ne_eq, Loc.mk.injEq]; split <;> omega
theorem nd_dd : P.nd w ≠ P.dd w' := by simp [Params.nd, Params.dd]
theorem nd_pt : P.nd w ≠ P.pt w' := by simp only [Params.nd, Params.pt, ne_eq, Loc.mk.injEq]; split <;> omega
theorem dd_pt : P.dd w ≠ P.pt w' := by simp only [Params.dd, Params.pt, ne_eq, Loc.mk.injEq]; split <;> omega
theorem pt_ne : P.pt 0 ≠ P.pt 1 := by simp [Params.pt]

end Distinct

/-! ## Memory facts -/

-- A read is stable under memory growth (`TreiberCommon.read?_mono`). 
hoist_alias [Kraken.Promising.SLR.EnvG.TreiberCommon.read?_mono ↦ Kraken.Promising.SLR.EnvG.Treiber2.read?_mono]

/-- **No message of `top` strictly between `a` and `b`.** -/
def NoTopIn (P : Params) (m : Memory) (a b : Time) : Prop :=
  ∀ p wm, a < p → p < b → m.get? p = some wm → wm.loc ≠ P.top

theorem NoTopIn.mono {P : Params} {m m' : Memory} (h : m.Prefix m') {a b : Time} (hb : b ≤ m.last)
    (hn : NoTopIn P m a b) : NoTopIn P m' a b := fun p wm h1 h2 hw =>
  hn p wm h1 h2 (Memory.get?_of_prefix_le h.2 (by simp only [Time] at *; omega) hw)

/-! ## The predicates -/

/-- **The push form** of thread `w` at the message `(v, V)` of `top`: the
value is node `w`; the resource holds the node's link and data word whole;
the link's maximal write `(y, t)` is below `V`, and the message `tr` of `top`
the push overwrote (no message of `top` strictly between) has the value `y`
(64 bits); the data word's maximal write `(d, t')` is below `V` with
`D w d`. -/
def PushF (P : Params) (w : Nat) (v : Val) (m : Memory) (V : View) (R : Res) : Prop :=
  v = P.nv w ∧ (R.wr (P.nd w)).q = 1 ∧ (R.wr (P.dd w)).q = 1 ∧
    (∃ y t, (R.wr (P.nd w)).X (y, t) ∧ (∀ p, (R.wr (P.nd w)).X p → p.2 ≤ t) ∧ t < V ∧
      ∃ tr y', tr < V ∧ m.read? P.top tr = some y' ∧ BitVec.setWidth 64 y' = BitVec.setWidth 64 y ∧
        NoTopIn P m tr V) ∧
    (∃ d t, (R.wr (P.dd w)).X (d, t) ∧ (∀ p, (R.wr (P.dd w)).X p → p.2 ≤ t) ∧ t < V ∧ P.D w d)

/-- **The pop form** of thread `w` at a message of `top` at `V`: the
resource holds the pop token, and an earlier message of `top` by `w` has
the value `nv w`. -/
def PopF (P : Params) (w : Nat) (m : Memory) (V : View) (R : Res) : Prop :=
  1 ≤ (R.wr (P.pt w)).q ∧ ∃ P', P' < V ∧ m.get? P' = some ⟨P.top, P.nv w, w⟩

/-- **Acquire id `0`**: every non-initial message of `top` is by a thread
`w < 2`, in push or pop form of `w`. -/
def predA (P : Params) : Pred where
  P v m V R := V ≠ 0 → ∃ w, w < 2 ∧ m.get? V = some ⟨P.top, v, w⟩ ∧ (PushF P w v m V R ∨ PopF P w m V R)
  mono v m m' V R hpre h := by
    intro hV
    obtain ⟨w, hw, hg, hf⟩ := h hV
    have hle : V ≤ m.last := m.last_le_of_get?_eq_some hg
    refine ⟨w, hw, Memory.get?_of_prefix hpre.2 hg, ?_⟩
    rcases hf with ⟨h1, h2, h3, ⟨y, t, h4, h5, h6, tr, y', h7, h8, h9, h10⟩, h11⟩ | ⟨h1, P', h2, h3⟩
    · exact .inl ⟨h1, h2, h3, ⟨y, t, h4, h5, h6, tr, y', h7, read?_mono hpre h8, h9, h10.mono hpre hle⟩, h11⟩
    · exact .inr ⟨h1, P', h2, Memory.get?_of_prefix hpre.2 h3⟩

/-- **The release predicate of `top`**: `predA`. -/
abbrev relTop (P : Params) : Pred := predA P

/-- No value of `top` is pure: at a message by thread `0`, the empty
resource holds neither the node nor the pop token. -/
theorem relTop_not_pure (P : Params) (v : Val) : ¬ Pred.Pure (relTop P) v := by
  intro h
  let m : Memory := { init := [], msgs := #[⟨P.top, v, 0⟩] }
  obtain ⟨w, -, -, hf⟩ := h m 1 (by decide)
  rcases hf with ⟨-, hq, -⟩ | ⟨hq, -⟩
  · simp [Res.unit, Perm.unit] at hq
  · simp only [Res.unit, Perm.unit] at hq; exact absurd hq (by decide)

/-! ## The initial ghost -/

/-- **The initial ghost**: `relTop` at `top` (`Pred.emp` elsewhere);
acquire table `[predA, Pred.top]`; the initial message of `top` in release
mode with unit slots for both ids; no update ids. -/
def ghost₀ (P : Params) : Ghost where
  rel x := if x = P.top then relTop P else Pred.emp
  acqTab := [predA P, Pred.top]
  u := [⟨(P.top, 0), 0, Res.unit⟩, ⟨(P.top, 0), 1, Res.unit⟩]
  relMsgs := [(P.top, 0)]
  pend := []
  upd _ := []
  claims := []

theorem ghost₀_rel_top (P : Params) : (ghost₀ P).rel P.top = relTop P := by simp [ghost₀]

theorem ghost₀_rel_ne {P : Params} {x : Loc} (h : x ≠ P.top) : (ghost₀ P).rel x = Pred.emp := by
  simp [ghost₀, h]

theorem ghost₀_pend (P : Params) : ∀ ts, ts ∉ (ghost₀ P).pend := fun _ h => by cases h

/-! ## The plans -/

/-- Node `w`'s words, as the push gives them (`top` filtered out, so that
the split keeps `top` without layout hypotheses; `nodeL_eq`). -/
def nodeL (P : Params) (w : Nat) : List Loc := [P.nd w, P.dd w].filter (· != P.top)

theorem top_not_mem_nodeL (P : Params) (w : Nat) : P.top ∉ nodeL P w := by
  simp [nodeL]

theorem nodeL_eq {P : Params} (hL : TLocs P) {w : Nat} (hw : w < 2) : nodeL P w = [P.nd w, P.dd w] := by
  have h1 := hL.top_nd' hw; have h2 := top_dd P w
  simp [nodeL, Ne.symm h1, Ne.symm h2]

/-- `top`'s write set holds a non-initial message: the thread has pushed. -/
def Pushed (P : Params) (r : Res) : Prop := ∃ p, (r.wr P.top).X p ∧ p.2 ≠ 0

open Classical in
/-- **Thread `w`'s split of a write to `top`**: the node before the push,
the pop token after it. -/
noncomputable def split (P : Params) (w : Nat) : Plan.Split P.top where
  give _ r := if Pushed P r then Res.only [P.pt w] r else Res.only (nodeL P w) r
  keep _ r := if Pushed P r then Res.drop [P.pt w] r else Res.drop (nodeL P w) r
  op_eq _ r := by
    by_cases h : Pushed P r
    · simp only [h, ↓reduceIte]; exact Res.only_op_drop _ _
    · simp only [h, ↓reduceIte]; exact Res.only_op_drop _ _
  pos _ r hq := by
    by_cases h : Pushed P r
    · simp only [h, ↓reduceIte, Res.drop, List.mem_singleton, top_pt]; exact hq
    · simp only [h, ↓reduceIte, Res.drop, top_not_mem_nodeL]; exact hq

/-- **Thread `w`'s plan**: every write to `top` releases with `split w`. -/
noncomputable def plan (P : Params) (w : Nat) : Plan :=
  ⟨[{ loc := P.top, gives := [], split := some (split P w) }]⟩

theorem plan_valid (P : Params) (w : Nat) : (plan P w).Valid := by
  intro e he
  simp only [plan, List.mem_singleton] at he
  subst he
  simp

theorem plan_rel (P : Params) (w : Nat) (l : Loc) (v : Val) : (plan P w).rel l v = decide (l = P.top) := by
  by_cases h1 : l = P.top
  · subst h1; simp [plan, Plan.rel, Plan.find?]
  · simp [plan, Plan.rel, Plan.find?, Ne.symm h1, h1]

theorem plan_gives (P : Params) (w : Nat) (v : Val) : (plan P w).gives P.top v = [] := by
  simp [plan, Plan.gives, Plan.find?]

theorem plan_give (P : Params) (w : Nat) (v : Val) (cl : Prop) (r : Res) :
    (plan P w).give P.top v cl r = (split P w).give cl r := by
  simp [plan, Plan.give, Plan.find?, Plan.Entry.give]

theorem plan_after_ne (P : Params) (w : Nat) {x : Loc} (hx : x ≠ P.top) (v : Val) (tw : Time) (cl : Prop)
    (r : Res) : (plan P w).after x v tw cl r = r.addW x (v, tw) := by
  unfold Plan.after
  rw [plan_rel]
  simp [hx]

theorem plan_after_top (P : Params) (w : Nat) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    (plan P w).after P.top v tw cl r = ((split P w).keep cl r).addW P.top (v, tw) := by
  unfold Plan.after
  rw [plan_rel]
  simp [Plan.keep, plan, Plan.find?, Plan.Entry.keep]

theorem split_give_pushed {P : Params} {w : Nat} {r : Res} (h : Pushed P r) (cl : Prop) :
    (split P w).give cl r = Res.only [P.pt w] r := by
  simp [split, h]

theorem split_give_fresh {P : Params} {w : Nat} {r : Res} (h : ¬ Pushed P r) (cl : Prop) :
    (split P w).give cl r = Res.only (nodeL P w) r := by
  simp [split, h]

theorem split_keep_pushed {P : Params} {w : Nat} {r : Res} (h : Pushed P r) (cl : Prop) :
    (split P w).keep cl r = Res.drop [P.pt w] r := by
  simp [split, h]

theorem split_keep_fresh {P : Params} {w : Nat} {r : Res} (h : ¬ Pushed P r) (cl : Prop) :
    (split P w).keep cl r = Res.drop (nodeL P w) r := by
  simp [split, h]

/-! ## The initial resources -/

/-- Thread `w`'s initial fractions: half of `top`, all of its node's link
and data word and of its pop token. -/
def frac (P : Params) (w : Nat) (x : Loc) : Rat :=
  if x = P.top then 1 / 2 else if x = P.nd w ∨ x = P.dd w ∨ x = P.pt w then 1 else 0

theorem frac_nonneg (P : Params) (w : Nat) (x : Loc) : 0 ≤ frac P w x := by
  unfold frac; split
  · grind
  · split <;> grind

/-- Thread `w`'s initial resource: its fractions and the acquire id `w` of
`top`. -/
def thrRes (m : Memory) (P : Params) (w : Nat) : Res :=
  ⟨(Res.initOf m (frac P w) (frac_nonneg P w)).wr, fun x ι => if x = P.top ∧ ι = w then 1 else 0⟩

/-- The initial thread resources. -/
def tRes (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then thrRes m P 0 else if i = 1 then thrRes m P 1 else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost₀ (P : Params) : (ghost₀ P).slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost₀, Res.prod, Res.op_unit]

theorem total_init (P : Params) (m : Memory) :
    total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem) = (thrRes m P 0).op (thrRes m P 1) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes m P 0, tRes m P 1] = _
  simp [tRes, Res.op_unit]

theorem frac_add_le {P : Params} (hL : TLocs P) (x : Loc) : frac P 0 x + frac P 1 x ≤ 1 := by
  have h1 := hL.nd_ne; have h2 := hL.dd_ne; have h3 := pt_ne P
  have h4 := nd_dd P 0 1; have h5 := nd_dd P 1 0; have h6 := nd_pt P 0 1; have h7 := nd_pt P 1 0
  have h8 := dd_pt P 0 1; have h9 := dd_pt P 1 0
  unfold frac
  by_cases ht : x = P.top
  · simp [ht]; grind
  · simp only [ht, ↓reduceIte]
    by_cases ha : x = P.nd 0 ∨ x = P.dd 0 ∨ x = P.pt 0
    · have hb : ¬ (x = P.nd 1 ∨ x = P.dd 1 ∨ x = P.pt 1) := by
        rintro (rfl | rfl | rfl) <;> rcases ha with h | h | h <;> simp_all [eq_comm]
      simp only [ha, hb, ↓reduceIte]; grind
    · simp only [ha, ↓reduceIte]; split <;> grind

/-- **Initial erasure of the two-thread Treiber stack.** -/
theorem erase_init {P : Params} (hL : TLocs P) (T : Nat → Prop) :
    Erase (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) T (Config.init [s0, s1] initMem) := by
  have htot := total_init (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha : ∀ x ι, (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).acq x ι = (if x = P.top ∧ ι = 0 then 1 else 0) +
        (if x = P.top ∧ ι = 1 then 1 else 0) := by
    intro x ι; rw [htot]; rfl
  have hq : ∀ x, ((total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).wr x).q = frac P 0 x + frac P 1 x := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).wr x).X p ↔
        (0 < frac P 0 x ∨ 0 < frac P 1 x) ∧ p = ((Config.init [s0, s1] initMem).mem.initVal x, 0) := by
    intro x p; rw [htot]
    show (0 < frac P 0 x ∧ p = _) ∨ (0 < frac P 1 x ∧ p = _) ↔ _
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨.inl h, rfl⟩
      · exact ⟨.inr h, rfl⟩
    · rintro ⟨h | h, rfl⟩
      · exact .inl ⟨h, rfl⟩
      · exact .inr ⟨h, rfl⟩
  have hids : ∀ x, (ghost₀ P).acqIds
      (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) (Config.init [s0, s1] initMem)).acq x =
        if x = P.top then [0, 1] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (ghost₀ P).acqTab.length = 2 from rfl]
    by_cases hx : x = P.top <;> simp [hx, ha, List.range_succ]
  refine Erase.init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- valid
    refine ⟨fun x => by rw [hq]; exact frac_add_le hL x, fun x ι => ?_⟩
    rw [ha]; split <;> split <;> grind
  · -- slot ids
    intro s hs
    simp only [ghost₀, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [ghost₀]
  · -- held acquire ids
    intro x ι h
    rw [ha] at h
    show ι < 2
    split at h <;> split at h <;> grind
  · -- release predicates split
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    by_cases hx : x = P.top
    · subst hx
      rw [ghost₀_rel_top] at h
      simp only [↓reduceIte, List.map_cons, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, Res.unit, Res.unit, (Res.op_unit _).symm, trivial, rfl⟩
    · rw [ghost₀_rel_ne hx] at h
      simp only [hx, ↓reduceIte, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact h
  · -- write sets
    intro x hpos p
    rw [hX]
    have : 0 < frac P 0 x ∨ 0 < frac P 1 x := by
      rw [hq] at hpos
      have := frac_nonneg P 0 x; have := frac_nonneg P 1 x
      by_cases h0 : 0 < frac P 0 x
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
    · rintro ⟨s, rfl | rfl, rfl, rfl⟩ <;> simp
    · rintro ⟨rfl, h⟩
      by_cases h0 : ι = 0
      · subst h0; exact ⟨_, .inl rfl, rfl, rfl⟩
      · have : ι = 1 := by
          by_cases h1 : ι = 1
          · exact h1
          · simp [h0, h1] at h
        subst this; exact ⟨_, .inr rfl, rfl, rfl⟩
  · -- slots satisfy their predicates at the initial message (view `0`)
    intro s hs
    simp only [ghost₀, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact fun h => absurd rfl h
    · trivial
  · -- update ids
    intro x
    simp [ghost₀]

end Init

end Kraken.Promising.SLR.EnvG.Treiber2
