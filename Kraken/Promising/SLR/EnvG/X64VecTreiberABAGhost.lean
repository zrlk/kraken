/-
**`treiber_aba_tagged.kl`, part 1: the ownership
plan** of the tagged-pointer Treiber stack
(`Kraken/Examples/LockFree/X64/treiber_aba_tagged.kl`) on `EnvGCAdj`.
ISA-neutral.

The proof uses **no release predicate**: every location's predicate is
`Pred.emp`, no thread plans a release (`plan0`, the empty plan: every write
is relaxed and joins the writer's write set, `plan0_after`), and the
initial ghost is empty (`ghost₀`: no acquire id, no slot). What a final
configuration knows of a message it learns from the **write sets**: at a
final clean erasure every settled message of a tracked location is in the
total write set (`Erase.writes`), and the threads' fractions are tight
enough there that the total write set is the two threads' (`total_X_two`,
`X64VecTreiberABAFinal.lean`).

Initial resources (`frac`):
- thread `0`: half of `head` (16 bytes) and the whole token `tok0`
  (`⟨head, 1⟩`, a ghost location: no access of the code has 1 byte);
- thread `1`: half of `head`, the whole token `tok1` (`⟨head, 2⟩`), and every
  8-byte location (its push stores to `⟨r12, 8⟩` for the popped `r12`,
  whatever that is).

The tokens tell the two threads' final facts apart (`B` of the rule link is
one predicate for both threads).

Contents: `Params`, `hd`/`nd`/`tok0`/`tok1`, `ghost₀`, `plan0` (+ validity,
`plan0_rel`, `plan0_after`), `frac`, `thrRes`, `tRes`, `erase_init`.
-/
import Kraken.Promising.SLR.EnvG.TreiberVCCommon

namespace Kraken.Promising.X64.EnvG.VecABA

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-! ## Parameters -/

/-- The stack's parameters: `head` at `h` (16 bytes: pointer in the low 8
bytes, tag in the high 8), nodes `A` at `a` and `B` at `b` (one 8-byte
`next` word each). -/
structure Params where
  h : BitVec 64
  a : BitVec 64
  b : BitVec 64

namespace Params

variable (P : Params)

/-- `head` (16 bytes). -/
def hd : Loc := ⟨P.h, 16⟩

/-- Thread `0`'s token (a ghost location, 1 byte). -/
def tok0 : Loc := ⟨P.h, 1⟩

/-- Thread `1`'s token (a ghost location, 2 bytes). -/
def tok1 : Loc := ⟨P.h, 2⟩

end Params

/-- The 8-byte word at `p` (a node's `next`). -/
def nd (p : BitVec 64) : Loc := ⟨p, 8⟩

theorem hd_ne_tok0 (P : Params) : P.hd ≠ P.tok0 := by simp [Params.hd, Params.tok0]
theorem hd_ne_tok1 (P : Params) : P.hd ≠ P.tok1 := by simp [Params.hd, Params.tok1]
theorem tok0_ne_tok1 (P : Params) : P.tok0 ≠ P.tok1 := by simp [Params.tok0, Params.tok1]
theorem nd_ne_hd (P : Params) (p : BitVec 64) : nd p ≠ P.hd := by simp [nd, Params.hd]
theorem nd_ne_tok0 (P : Params) (p : BitVec 64) : nd p ≠ P.tok0 := by simp [nd, Params.tok0]
theorem nd_ne_tok1 (P : Params) (p : BitVec 64) : nd p ≠ P.tok1 := by simp [nd, Params.tok1]
@[simp] theorem nd_bytes (p : BitVec 64) : (nd p).bytes = 8 := rfl
@[simp] theorem hd_bytes (P : Params) : P.hd.bytes = 16 := rfl
@[simp] theorem tok0_bytes (P : Params) : P.tok0.bytes = 1 := rfl
@[simp] theorem tok1_bytes (P : Params) : P.tok1.bytes = 2 := rfl

/-! ## The initial ghost and the plan -/

/-- **The initial ghost**: `Pred.emp` everywhere, no acquire id, no slot,
no release message, no update id. -/
def ghost₀ : Ghost where
  rel _ := Pred.emp
  acqTab := []
  u := []
  relMsgs := []
  pend := []
  upd _ := []
  claims := []

theorem ghost₀_pend : ∀ ts, ts ∉ ghost₀.pend := fun _ h => by cases h

/-- **The empty plan**: no write is a planned release. -/
def plan0 : Plan := ⟨[]⟩

theorem plan0_valid : plan0.Valid := by
  intro e he
  cases he

@[simp] theorem plan0_rel (l : Loc) (v : Val) : plan0.rel l v = false := by
  simp [plan0, Plan.rel, Plan.find?]

@[simp] theorem plan0_after (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    plan0.after l v tw cl r = r.addW l (v, tw) := by
  simp [Plan.after, plan0, Plan.find?]

/-! ## The initial resources -/

/-- Thread `w`'s initial fractions. -/
def frac (P : Params) (w : Nat) (x : Loc) : Rat :=
  if x = P.hd then 1 / 2
  else if w = 0 then (if x = P.tok0 then 1 else 0)
  else if x = P.tok1 then 1 else if x.bytes = 8 then 1 else 0

theorem frac_nonneg (P : Params) (w : Nat) (x : Loc) : 0 ≤ frac P w x := by
  unfold frac; split
  · grind
  · split
    · split <;> grind
    · split
      · grind
      · split <;> grind

/-- Thread `w`'s initial resource: its fractions, no acquire id. -/
def thrRes (m : Memory) (P : Params) (w : Nat) : Res := Res.initOf m (frac P w) (frac_nonneg P w)

/-- The initial thread resources. -/
def tRes (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then thrRes m P 0 else if i = 1 then thrRes m P 1 else Res.unit

theorem frac_add_le (P : Params) (x : Loc) : frac P 0 x + frac P 1 x ≤ 1 := by
  unfold frac
  by_cases h : x = P.hd
  · simp only [h, ↓reduceIte]; grind
  · simp only [h, ↓reduceIte, Nat.one_ne_zero]
    by_cases h0 : x = P.tok0
    · subst h0; simp [Params.tok0, Params.tok1]; grind
    · simp only [h0, ↓reduceIte]; split
      · grind
      · split <;> grind

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost₀ : ghost₀.slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost₀]

theorem total_init (P : Params) (m : Memory) :
    total (tRes m P) ghost₀ (Config.init [s0, s1] initMem) = (thrRes m P 0).op (thrRes m P 1) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes m P 0, tRes m P 1] = _
  simp [tRes, Res.op_unit]

/-- **Initial erasure of the tagged Treiber stack.** -/
theorem erase_init (P : Params) (T : Nat → Prop) :
    Erase (tRes (Config.init [s0, s1] initMem).mem P) ghost₀ T (Config.init [s0, s1] initMem) := by
  have htot := total_init (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha : ∀ x ι, (total (tRes (Config.init [s0, s1] initMem).mem P) ghost₀
      (Config.init [s0, s1] initMem)).acq x ι = 0 := by
    intro x ι; rw [htot]; rfl
  have hq : ∀ x, ((total (tRes (Config.init [s0, s1] initMem).mem P) ghost₀
      (Config.init [s0, s1] initMem)).wr x).q = frac P 0 x + frac P 1 x := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes (Config.init [s0, s1] initMem).mem P) ghost₀
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
  refine Erase.init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · exact ⟨fun x => by rw [hq]; exact frac_add_le P x, fun x ι => by rw [ha]; exact Nat.zero_le _⟩
  · intro s hs; cases hs
  · intro x ι h; rw [ha] at h; cases h
  · intro x v m V r h
    simp only [Ghost.acqPreds, Ghost.acqIds, ghost₀, List.length_nil, List.range_zero, List.filter_nil,
      List.map_nil, Ghost.updPreds, List.append_nil]
    exact h
  · intro x hpos p
    rw [hX]
    have : 0 < frac P 0 x ∨ 0 < frac P 1 x := by
      rw [hq] at hpos
      have := frac_nonneg P 0 x; have := frac_nonneg P 1 x
      by_cases h0 : 0 < frac P 0 x
      · exact .inl h0
      · exact .inr (by grind)
    simp [this]
  · intro x _; exact Pred.emp_pure _
  · intro k hk; cases hk
  · simp [ghost₀]
  · intro k ι
    simp [ghost₀]
  · intro s hs; cases hs
  · intro x; simp [ghost₀]

end Init

end Kraken.Promising.X64.EnvG.VecABA
