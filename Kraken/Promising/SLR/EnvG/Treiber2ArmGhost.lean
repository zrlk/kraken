/-
Part 2: **the ghost of the Arm-minimal Treiber stack**
`treiber2_arm.kl` (push `ldr`/`str`/`casl`, pop `ldar`/`ldr`/`cas`), on the
adjacency environment `EnvGCAdj`. ISA-neutral.

## Why not `Treiber2Ghost`'s protocol

`treiber2`'s release predicate of `top` (`Treiber2.predA`) is impure at every
value, so every write to `top` must be a ghost release. The pop's plain `CAS`
is not a release RMW, so it must write a value pure for `top`'s predicate
(`RmwOkCAdj`; `PromisePure'`); it writes `0` or a node address, the values a
push writes. So `top`'s release predicate here is `Pred.emp`, and no write is
a planned release (`planA`, empty): the `casl` and the `cas` are both erased as
plain writes. The history is recovered from the threads' own resources
(`EnvG/Treiber2ArmOwn.lean`, `EnvG/Treiber2ArmFinal.lean`).

## The ghost

- `relA := Pred.emp` everywhere (`ghost₀A`);
- acquire table `[Pred.top, Pred.top]`: ids `0` and `1` of `top`, held by
  threads `0` and `1` for good, only tell the threads apart in the shared
  postcondition (`acq_pair_false`);
- the initial message of `top` in release mode with unit slots, as in
  `Treiber2.ghost₀`.

The initial resources are `Treiber2.thrRes`/`tRes` unchanged: half of `top`,
node `w`'s link and data word and the (here unused) pop token whole.
-/
import Kraken.Promising.SLR.EnvG.Treiber2Ghost

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber2

variable {I : ISA}

/-- **The initial ghost**: `Pred.emp` everywhere; acquire table
`[Pred.top, Pred.top]`; the initial message of `top` in release mode with
unit slots for both ids; no update ids. -/
def ghost₀A (P : Params) : Ghost where
  rel _ := Pred.emp
  acqTab := [Pred.top, Pred.top]
  u := [⟨(P.top, 0), 0, Res.unit⟩, ⟨(P.top, 0), 1, Res.unit⟩]
  relMsgs := [(P.top, 0)]
  pend := []
  upd _ := []
  claims := []

theorem ghost₀A_rel (P : Params) (x : Loc) : (ghost₀A P).rel x = Pred.emp := rfl

theorem ghost₀A_pend (P : Params) : ∀ ts, ts ∉ (ghost₀A P).pend := fun _ h => by cases h

/-- **The plan**: no planned release. -/
def planA : Plan := ⟨[]⟩

theorem planA_valid : planA.Valid := by intro e he; cases he

@[simp] theorem planA_rel (l : Loc) (v : Val) : planA.rel l v = false := rfl

@[simp] theorem planA_after (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    planA.after l v tw cl r = r.addW l (v, tw) := rfl

/-- **The ghost facts**: the release predicates of `ghost₀A`, an acquire
table extending `[Pred.top, Pred.top]`. -/
def GWA (P : Params) (g : Ghost) : Prop :=
  g.rel = (ghost₀A P).rel ∧ (ghost₀A P).acqTab <+: g.acqTab

namespace GWA

variable {P : Params} {g g' : Ghost}

theorem mono (h : GWA P g) (hle : g.Le g') : GWA P g' :=
  ⟨hle.rel.trans h.1, h.2.trans hle.acqTab⟩

theorem rel_eq (h : GWA P g) (x : Loc) : g.rel x = Pred.emp := by rw [h.1]; rfl

theorem pure (h : GWA P g) (x : Loc) (v : Val) : Pred.Pure (g.rel x) v := by
  rw [h.rel_eq]; exact Pred.emp_pure v

end GWA

theorem ghost₀A_gw (P : Params) : GWA P (ghost₀A P) := ⟨rfl, List.prefix_refl _⟩

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost₀A (P : Params) : (ghost₀A P).slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost₀A, Res.prod, Res.op_unit]

theorem total_initA (P : Params) (m : Memory) :
    total (tRes m P) (ghost₀A P) (Config.init [s0, s1] initMem) = (thrRes m P 0).op (thrRes m P 1) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀A, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes m P 0, tRes m P 1] = _
  simp [tRes, Res.op_unit]

/-- **Initial erasure** of `treiber2_arm` (as `Treiber2.erase_init`, at
`ghost₀A`). -/
theorem erase_initA {P : Params} (hL : TLocs P) (T : Nat → Prop) :
    Erase (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀A P) T (Config.init [s0, s1] initMem) := by
  have htot := total_initA (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha : ∀ x ι, (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀A P)
      (Config.init [s0, s1] initMem)).acq x ι = (if x = P.top ∧ ι = 0 then 1 else 0) +
        (if x = P.top ∧ ι = 1 then 1 else 0) := by
    intro x ι; rw [htot]; rfl
  have hq : ∀ x, ((total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀A P)
      (Config.init [s0, s1] initMem)).wr x).q = frac P 0 x + frac P 1 x := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀A P)
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
  have hids : ∀ x, (ghost₀A P).acqIds
      (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀A P) (Config.init [s0, s1] initMem)).acq x =
        if x = P.top then [0, 1] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (ghost₀A P).acqTab.length = 2 from rfl]
    by_cases hx : x = P.top <;> simp [hx, ha, List.range_succ]
  refine Erase.init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- valid
    refine ⟨fun x => by rw [hq]; exact frac_add_le hL x, fun x ι => ?_⟩
    rw [ha]; split <;> split <;> grind
  · -- slot ids
    intro s hs
    simp only [ghost₀A, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [ghost₀A]
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
      simp only [↓reduceIte, List.map_cons, List.map_nil, Ghost.updPreds, ghost₀A, List.append_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, trivial, Res.unit, Res.unit, (Res.op_unit _).symm, trivial, rfl⟩
    · simp only [hx, ↓reduceIte, List.map_nil, Ghost.updPreds, ghost₀A, List.append_nil]
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
    intro x _
    exact Pred.emp_pure _
  · -- release messages are initial
    intro k hk
    simp only [ghost₀A, List.mem_singleton] at hk
    subst hk; rfl
  · -- slots are distinct
    simp [ghost₀A]
  · -- slot domain
    intro k ι
    rw [ha]
    simp only [ghost₀A, List.mem_cons, List.not_mem_nil, or_false]
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
  · -- slots satisfy their predicates at the initial message
    intro s hs
    simp only [ghost₀A, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> trivial
  · -- update ids
    intro x
    simp [ghost₀A]

end Init

end Kraken.Promising.SLR.EnvG.Treiber2Arm
