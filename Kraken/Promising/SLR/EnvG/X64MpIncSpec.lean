/-
**x64 message passing with an unlocked `incl` release, the specification**
The flag predicate, initial ghost, initial erasure
and final argument of `mp_incl.kl` (writer `movl $42, (%rsi); incl (%rdi)`,
the reader of `X64MpVCGen.mpReaderX`).

**Why not `X64MpSpec.flagPred`.** The writer's flag store is the store half
of `incl`. Its value is the loaded value plus one, and the load runs in
`EnvGLR`, which gives no clean-erasure knowledge of the value. A planned
release must be impure at its value (`StoreOk`, `Env.lean`), and it must be
permitted after every load outcome the env offers, including the load of
`0xFFFFFFFF`, after which the store writes `0`. `flagPred` is pure at a zero
low word, so neither plan entry works for it: `val := some 1` leaves every
other value unplanned (and then it must be pure), and `val := none` needs
impurity at `0`. `Pred.Pure` depends on the value only, and the initial flag
value is `0`, so no predicate of the value alone is impure at every `incl`
result and pure initially.

**The predicate used here**, `flagPredI`: `Good` whenever the view is
non-zero or the low word is non-zero. It is impure at every value
(`flagPredI_impure`) and trivial at view `0`. The initial flag message is
therefore in release mode: `mpGhostI` lists `(Fl, 0)` as a release message
with one slot, for the reader's acquire id `0`, holding the empty resource
(its predicate holds at view `0` and the initial value `0`). The rest of
the specification reuses `X64MpSpec` (`Params`, `Good`, `Own0`/`Own1`,
`ReaderDone`, `mpRes`).

`erase_initGhost` (`InitGhost.lean`) cannot be used: it gives release-mode
initial locations update ids and forbids held acquire ids there. The initial
erasure is an instance of its variant `erase_initGhostAcq` (held
acquire ids at release-mode locations, no update ids): `mpGhostI` is
`initGhostAcq` at `[Fl]` with the slot `(Fl, 0, ∅)`.

- `flagPredI`, `φI`, `flagPredI_impure`, `mpGhostI`, `erase_mpIncInit`;
- `WorldWI`, `WorldRI` (+ `mono`), `MpPostI`;
- `slot_of_seenI`, `mp_finalI` (as `X64MpSpec.slot_of_seen`/`mp_final`).
-/
import Kraken.Promising.SLR.EnvG.X64MpSpec

namespace Kraken.Promising.X64.EnvG.MpInc

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.X64.EnvG.Mp

/-! ## The flag predicate -/

/-- **The flag's release and acquire predicate for the `incl` writer**:
`Good` at a non-zero view or a non-zero low word. -/
def flagPredI (Dt : Loc) : Pred where
  P v _ V r := (V ≠ 0 ∨ BitVec.setWidth 32 v ≠ 0) → Good Dt V r
  mono _ _ _ _ _ _ h := h

/-- The flag's predicate for these parameters. -/
abbrev φI (P : Params) : Pred := flagPredI P.Dt

/-- `flagPredI` is impure at every value. -/
theorem flagPredI_impure {Dt : Loc} (v : Val) : ¬ Pred.Pure (flagPredI Dt) v :=
  fun h => by
    have := (h default 1 (.inl (by decide))).1
    simp [Res.unit, Perm.unit] at this

/-- `flagPredI` satisfies the reader's `FlagLaw` (`X64MpSpec.lean`): the
generic reader (`…G`) instantiates at `φI`. -/
theorem flagPredI_law (Dt : Loc) : FlagLaw Dt (flagPredI Dt) := ⟨fun _ => flagPredI_impure _, fun hv h => h (.inr hv)⟩

/-! ## The world facts and the postcondition -/

/-- The writer's world facts: the flag's release predicate is `φI`, the
data's is pure. -/
def WorldWI (P : Params) (g : Ghost) : Prop := g.rel P.Fl = φI P ∧ ∀ v, Pred.Pure (g.rel P.Dt) v

/-- The reader's world facts: the flag's release predicate is `φI`, and the
reader holds an acquire id of `Fl` with predicate `φI`. -/
def WorldRI (P : Params) (r : Res) (g : Ghost) : Prop :=
  g.rel P.Fl = φI P ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = φI P ∧ r.acq P.Fl ι = 1

theorem WorldRI.mono {P : Params} {r : Res} {g g' : Ghost} (h : WorldRI P r g) (hle : g.Le g') :
    WorldRI P r g' :=
  WorldRG.mono (φ := φI P) h hle

/-- **The shared postcondition** (`NPSafe`'s `B`): the writer's token, or the
reader's result with its acquire id. -/
def MpPostI (P : Params) (rd : Nat) (c : Config isa) (r : Res) (g : Ghost) : Prop :=
  1 ≤ (r.wr P.W).q ∨
    (ReaderDone P rd c ∧ ∃ ι, ι < g.acqTab.length ∧ g.acqPred ι = φI P ∧ r.acq P.Fl ι = 1)

/-! ## The initial ghost -/

/-- The slot of the initial flag message: acquire id `0`, no resource. -/
def initSlot (P : Params) : Slot := ⟨(P.Fl, 0), 0, Res.unit⟩

/-- **The initial ghost**: `Fl`'s predicate is `φI`, and its initial message
is a release message with the slot `initSlot`. -/
def mpGhostI (P : Params) : Ghost where
  rel x := if x = P.Fl then φI P else Pred.emp
  acqTab := [φI P]
  u := [initSlot P]
  relMsgs := [(P.Fl, 0)]
  pend := []
  upd _ := []
  claims := []

theorem mpGhostI_rel_Fl {P : Params} : (mpGhostI P).rel P.Fl = φI P := by simp [mpGhostI]

theorem mpGhostI_rel_ne {P : Params} {x : Loc} (h : x ≠ P.Fl) : (mpGhostI P).rel x = Pred.emp := by
  simp [mpGhostI, h]

theorem pend_mpGhostI {P : Params} : ∀ ts, ts ∉ (mpGhostI P).pend := fun _ h => by cases h

/-! ## Initial erasure -/

section Init

variable {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- The initial total: the writer's and the reader's resources (the slot is
empty). -/
theorem total_mpIncInit (P : Params) (m : Memory) :
    total (mpRes m P) (mpGhostI P) (Config.init [sW, sR] initMem) = (writerRes m P).op (readerRes P) := by
  simp only [total, Config.init_size, threadsRes, Ghost.slotsRes, mpGhostI, initSlot, List.map_cons,
    List.map_nil, List.length_cons, List.length_nil]
  show (Res.prod [mpRes m P 0, mpRes m P 1]).op (Res.prod [Res.unit]) = _
  simp [mpRes, Res.op_unit, Res.prod]

theorem total_mpIncInit_q (P : Params) (m : Memory) (x : Loc) :
    ((total (mpRes m P) (mpGhostI P) (Config.init [sW, sR] initMem)).wr x).q = writerFrac P x := by
  rw [total_mpIncInit]
  show writerFrac P x + 0 = _
  exact Rat.add_zero _

theorem total_mpIncInit_acq (P : Params) (m : Memory) (x : Loc) (ι : PredId) :
    (total (mpRes m P) (mpGhostI P) (Config.init [sW, sR] initMem)).acq x ι =
      if x = P.Fl ∧ ι = 0 then 1 else 0 := by
  rw [total_mpIncInit]
  show 0 + _ = _
  exact Nat.zero_add _

/-- **Initial erasure of MP with the `incl` writer** (initial flag value
`0`). -/
theorem erase_mpIncInit (P : Params) (T : Nat → Prop)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal P.Fl = 0) :
    Erase (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhostI P) T (Config.init [sW, sR] initMem) := by
  have hg : mpGhostI P =
      initGhostAcq (fun x => if x = P.Fl then φI P else Pred.emp) [φI P] [P.Fl] [(P.Fl, 0, Res.unit)] := rfl
  have hq := total_mpIncInit_q (sW := sW) (sR := sR) (initMem := initMem) P (Config.init [sW, sR] initMem).mem
  have ha := total_mpIncInit_acq (sW := sW) (sR := sR) (initMem := initMem) P (Config.init [sW, sR] initMem).mem
  have hids : ∀ x, (mpGhostI P).acqIds
      (total (mpRes (Config.init [sW, sR] initMem).mem P) (mpGhostI P) (Config.init [sW, sR] initMem)).acq x =
        if x = P.Fl then [0] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (mpGhostI P).acqTab.length = 1 from rfl, List.range_one]
    by_cases hx : x = P.Fl <;> simp [hx, ha]
  rw [hg] at hq ha hids ⊢
  refine erase_initGhostAcq T (by simp) ⟨fun x => by rw [hq]; exact writerFrac_le_one P x,
    fun x ι => by rw [ha]; split <;> decide⟩ ?_ ?_ ?_ ?_ (by simp) ?_ (by simp) ?_
  · -- held ids
    intro x ι h
    rw [ha] at h
    split at h
    · next he => rw [he.2]; exact Nat.zero_lt_one
    · exact absurd h (by decide)
  · -- the release predicates split
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    by_cases hx : x = P.Fl
    · subst hx
      simp only [↓reduceIte, List.map_cons, List.map_nil] at h ⊢
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · simp only [hx, ↓reduceIte, List.map_nil] at h ⊢
      exact h
  · -- write sets
    intro x hpos p
    rw [← hg, total_mpIncInit] at hpos ⊢
    show (0 < writerFrac P x ∧ p = _) ∨ False ↔ _
    have : 0 < writerFrac P x := by
      have h2 : ((writerRes (Config.init [sW, sR] initMem).mem P).op (readerRes P)).wr x =
        ((writerRes (Config.init [sW, sR] initMem).mem P).wr x).op Perm.unit := rfl
      rw [h2, Perm.op_unit] at hpos
      exact hpos
    simp [this]
  · -- relaxed initial messages are pure
    intro x hx
    have hne : x ≠ P.Fl := fun he => hx (by simp [he])
    simp only [hne, ↓reduceIte]
    exact Pred.emp_pure _
  · -- the held ids are the slots
    intro x hx ι
    simp only [List.mem_singleton] at hx
    subst hx
    rw [ha]
    simp [eq_comm]
  · -- the slot's predicate at view `0`
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    intro h
    rcases h with h | h
    · exact absurd rfl h
    · simp [hF0] at h

end Init

/-! ## The final argument -/

section Slot

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **The slot of a seen flag message** (`X64MpSpec.slot_of_seen` with
`φI`): if the total holds the acquire id `ι` of `Fl` (predicate `φI`), a
flag message with a non-zero low word carries a slot for `ι` satisfying
`Good` at the message's timestamp. -/
theorem slot_of_seenI {P : Params} (E : Erase rF g T c) (hrel : g.rel P.Fl = φI P) {ι : PredId}
    (hι : g.acqPred ι = φI P) (hacq : (total rF g c).acq P.Fl ι = 1) {ts : Time} {v : Val}
    (hrd : c.mem.read? P.Fl ts = some v) (hv : BitVec.setWidth 32 v ≠ 0) :
    ∃ s ∈ g.u, s.key = (P.Fl, ts) ∧ s.id = ι ∧ Good P.Dt ts s.res :=
  slot_of_seenG (flagPredI_law _) E hrel hι hacq hrd hv

end Slot

/-- **The final argument** (`X64MpSpec.mp_final` with `MpPostI`): from
erasure at a final configuration of two threads whose final resources
satisfy `MpPostI P 1`, the reader's `ebx` and the data word's final value
are `42`. -/
theorem mp_finalI {P : Params} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hrel : g.rel P.Fl = φI P) (hB : ∀ tid, c.Done tid → MpPostI P 1 c (rF tid) g) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 42) ∧
      c.mem.finalVal P.Dt = dataVal :=
  mp_finalG (flagPredI_law _) E hf hsize hrel hB

end Kraken.Promising.X64.EnvG.MpInc
