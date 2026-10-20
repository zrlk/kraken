/-
**`treiber_aba_tagged.kl` in the value environment**: both threads' verbatim runs (`p0V_memVals`,
`p1V_memVals`), counted and partial, in `(valEnv L V).within abaS`.

- `abaS`: the declared layout, `head` (16 bytes), `A` and `B` (8 bytes).
- `L` (`AbaValL`): the locations of `abaS`.
- `V` (`AbaValV`): values whose low quadword is `0`, `A` or `B`.

`head`'s low quadword is the top pointer and a node's quadword its `next`,
so every pointer the threads dereference (`movq (%rax),%rbx` with `rax ≠ 0`
the top read from `head`, and the push's `movq %rax,(%r12)` with `r12 ≠ 0`
the node popped first) is `A` or `B`: an access exactly at a location of
`abaS`. Every write keeps `V`: the pops' `lock cmpxchg16b` writes the node's
`next` (read from an `L`-location) as the new top, the push writes the old
top to the node and the node as the new top.

The tables are the existing runs' private stack `Stk` (`p0V_noNT`,
`p1V_noNT`, `X64VecTreiberABANoNT.lean`) with the stack's domain clear of
`A` and `B`, and thread `1`'s popped node `r12` in `{0, A, B}` after the
first pop (`≠ 0` at `p1push1`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64VecTreiberABARun1

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.VecABA

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The value invariant -/

/-- The locations of the value invariant: `head` and the two nodes. -/
def AbaValL (h a b : BitVec 64) : Loc → Prop := fun l => l = ⟨h, 16⟩ ∨ l = ⟨a, 8⟩ ∨ l = ⟨b, 8⟩

/-- A pointer of the stack: `0`, `A` or `B`. -/
abbrev AbaPtr (a b x : BitVec 64) : Prop := x = 0 ∨ x = a ∨ x = b

/-- The values of the value invariant: low quadword `0`, `A` or `B`. -/
def AbaValV (a b : BitVec 64) : Val → Prop := fun v => AbaPtr a b (lo v)

theorem lo_append (a b : BitVec 64) : lo (a ++ b) = b := by
  unfold lo; ext i hi; rw [BitVec.getElem_extractLsb', BitVec.getLsbD_append]; simp [hi]

theorem lo_eq_setWidth (u : Val) : lo u = u.setWidth 64 := by
  unfold lo; ext i hi; simp

theorem lo_setWidth (x : BitVec 64) : lo (x.setWidth 128) = x := by
  unfold lo; ext i hi; simp [show i < 128 by omega, BitVec.getLsbD_eq_getElem hi]

theorem abaPtr_ne0 {a b x : BitVec 64} (h : AbaPtr a b x) (hx : ¬ x = 0) : x = a ∨ x = b :=
  h.resolve_left hx

variable [layout : _root_.Layout]

/-- The declared layout: `head` (16 bytes), `A`, `B` (8 bytes). -/
abbrev abaS : SharedEnv.Layout := [(symV "head", 16), (symV "A", 8), (symV "B", 8)]

/-- The threads' environment: the value environment at `abaS`. -/
abbrev abaValEnv : SharedEnv :=
  (SharedEnv.valEnv (AbaValL (symV "head") (symV "A") (symV "B")) (AbaValV (symV "A") (symV "B"))).within abaS

/-- `head`'s value is a `V`-value. -/
theorem hdV {g g' : abaValEnv.State} {x : Val} (h : abaValEnv.step (.load .plain false (symV "head") 16) g x g') :
    AbaValV (symV "A") (symV "B") x :=
  h (Or.inl rfl)

/-- **The node load** from `A` or `B` off the stack reads a pointer. -/
theorem nodeV {S : BitVec 64 → Prop} {p x : BitVec 64} {g g' : abaValEnv.State} (hA : ¬ S (symV "A"))
    (hB : ¬ S (symV "B")) (hp : p = symV "A" ∨ p = symV "B")
    (h : (S p ∧ g' = g) ∨ ∃ u, abaValEnv.step (.load .plain false p 8) g u g' ∧ x = BitVec.setWidth 64 u) :
    AbaPtr (symV "A") (symV "B") x := by
  rcases h with ⟨hs, -⟩ | ⟨u, hu, rfl⟩
  · rcases hp with rfl | rfl
    · exact absurd hs hA
    · exact absurd hs hB
  · rw [← lo_eq_setWidth]
    refine hu ?_
    rcases hp with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- A pointer `A`/`B` is a location of `abaS`. -/
theorem node_in {p : BitVec 64} (hp : p = symV "A" ∨ p = symV "B") : (p, 8) ∈ abaS := by
  rcases hp with rfl | rfl <;> simp

variable [Executable.ValidLayout (layout abaImageV)]

local instance abaImageV.envMV : CodeEnv := ⟨layout abaImageV⟩

/-- The private stack, its domain clear of the nodes. -/
abbrev StkV (S : BitVec 64 → Prop) (s : MachineData) : Prop :=
  Stk S (symV "head") s ∧ ¬ S (symV "A") ∧ ¬ S (symV "B")

set_option maxHeartbeats 4000000 in
/-- **Thread `0`'s verbatim run in the value environment** (counted,
partial). -/
theorem p0V_memVals (S : BitVec 64 → Prop) (hal : isAligned 16 (symV "head") = true) :
    ∀ s g, StkV S s →
      Safely (cenv.instrStepEnv (SharedEnv.counted abaValEnv))
        (fun x => (x.1.2 = labV "done" ∧ True) ∨ False) ((s, labV "p0"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted abaValEnv)
    (Q := fun _ _ => True) (E := fun _ _ _ => False)
    (fun lb s _ => StkV S s ∧ (lb = "p0" ∨ lb = "done")) ?_ rfl (by decide) abaCodeV_placedIn
    abaCodeV_last s g ⟨hsg, .inl rfl⟩
  cfg_cases_env [abaCodeV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hstk, hnA, hnB⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals try simp (config := { decide := true }) only [] at hT
  all_goals try simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 =>
    have hn := ‹Mem.loadInt _ _ 8 = none›
    rw [loadInt_store16_lo] at hn; cases hn
  case vc7 =>
    have hn := ‹Mem.loadInt _ _ 8 = none›
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hn
    rw [neg8_eq, ← BitVec.add_assoc, loadInt_store16_hi] at hn; cases hn
  case vc8 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hld hm1 hm2 _
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2
    simp only [SharedAccess.tick] at h1
    omega
  case vc9 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hn hld hm1 hm2 _
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hp := abaPtr_ne0 (hdV (x := v) hld.1) hz
    refine ⟨trivial, ?_⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [show Int64.toBitVec 0 = 0 from rfl, show lo v + 0 = lo v from BitVec.add_zero _]
    exact node_in hp
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 hld hm1 hm2 hnode _
    obtain ⟨hn, -⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    obtain ⟨h1, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨h2, rfl⟩ := rd_hi hm2
    rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
    subst h1 h2
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hp := abaPtr_ne0 (hdV (x := v) hld.1) hz
    have hn := nodeAddr (p' := lo v) (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact BitVec.add_zero _) hn
    have hu := nodeV hnA hnB hp hn
    refine ⟨fun old new hop _ _ => ?_, by simp [SharedEnv.AccessIn]⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hop
    split at hop
    · cases hop
      show AbaPtr _ _ (lo _)
      rw [lo_append]; exact hu
    · cases hop
  all_goals
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 old g5 heq hnz hld hm1 hm2 hnode hcas _
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    obtain ⟨-, hc⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, by decide⟩, ?_⟩
    first
      | exact .inl (by decide)
      | (refine .inr fun ⟨_, hg⟩ => ?_
         subst hg
         have h1 := hld.2; have h3 := hcas.2
         simp only [SharedAccess.tick] at h1 h3
         omega)

set_option hygiene false in
/-- The `head` load and the slot round trip: `rax = lo v`, `rdx = hi v`. -/
local macro "rd_v" : tactic => `(tactic| (
  obtain ⟨h1, rfl⟩ := rd_lo hm1
  simp only [Reg64s.get64_set64] at hm2
  obtain ⟨h2, rfl⟩ := rd_hi hm2
  rw [VecPublish.vec_get_setLegacy_xmm] at h1 h2
  subst h1 h2))

set_option hygiene false in
/-- A register read through the run's register updates. -/
local macro "regs" : tactic => `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])

set_option hygiene false in
/-- The slot round trips of `movq -16(%rsp)` / `movq -8(%rsp)` are mapped. -/
local macro "slot_ok" : tactic => `(tactic| first
  | (have hn := ‹Mem.loadInt _ _ 8 = none›
     rw [loadInt_store16_lo] at hn; cases hn)
  | (have hn := ‹Mem.loadInt _ _ 8 = none›
     simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hn
     rw [neg8_eq, ← BitVec.add_assoc, loadInt_store16_hi] at hn; cases hn))

set_option hygiene false in
/-- A pop's node load is at a pointer `A`/`B`. -/
local macro "node_ok" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hn hld hm1 hm2 _
  rd_v
  simp [CondCode.interp, StatusFlags.from_result] at hz
  have hp := abaPtr_ne0 (hdV (x := v) hld.1) hz
  refine ⟨trivial, ?_⟩
  regs
  rw [show Int64.toBitVec 0 = 0 from rfl, show lo v + 0 = lo v from BitVec.add_zero _]
  exact node_in hp))

set_option hygiene false in
/-- A pop's `cmpxchg16b` writes the node's `next`. -/
local macro "pop_ok" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 hld hm1 hm2 hnode _
  obtain ⟨hn, -⟩ := nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode
  rd_v
  simp [CondCode.interp, StatusFlags.from_result] at hz
  have hp := abaPtr_ne0 (hdV (x := v) hld.1) hz
  have hn := nodeAddr (p' := lo v) (by regs; exact BitVec.add_zero _) hn
  have hu := nodeV hnA hnB hp hn
  refine ⟨fun old new hop _ _ => ?_, by simp [SharedEnv.AccessIn]⟩
  simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hop
  split at hop
  · cases hop
    show AbaPtr _ _ (lo _)
    rw [lo_append]; exact hu
  · cases hop))

set_option hygiene false in
/-- The table's tick component of a branch. -/
local macro "tick1" : tactic => `(tactic| first
  | exact .inl (by decide)
  | (refine .inr fun ⟨_, hg⟩ => ?_
     subst hg
     have h1 := hld.2
     simp only [SharedAccess.tick] at h1
     omega))

set_option hygiene false in
/-- The table's tick component of a branch after a `cmpxchg16b`. -/
local macro "tick2" : tactic => `(tactic| first
  | exact .inl (by decide)
  | (refine .inr fun ⟨_, hg⟩ => ?_
     subst hg
     have h1 := hld.2; have h3 := hcas.2
     simp only [SharedAccess.tick] at h1 h3
     omega))

set_option hygiene false in
/-- A pop's branch or fallthrough after its `cmpxchg16b`. -/
local macro "pop_names" : tactic => `(tactic| (
  rename_i s1 g0 v g1 r1 g2 r2 g3 af hz u g4 old g5 heq hnz hld hm1 hm2 hnode hcas _
  have hc := (nodeLd (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 hnode).2
  rd_v))

/-- Thread `1`'s table: the stack, the first pop's node `r12` a pointer
after it, and not `0` at the push. -/
abbrev p1TableV (S : BitVec 64 → Prop) :
    Label → MachineData → (SharedEnv.counted abaValEnv).State → Prop :=
  fun lb s _ => StkV S s ∧ ((lb = "p1pop2" ∨ lb = "p1push") → AbaPtr (symV "A") (symV "B") (s.regs.get64 .r12)) ∧
    (lb = "p1push1" → s.regs.get64 .r12 = symV "A" ∨ s.regs.get64 .r12 = symV "B")

set_option maxHeartbeats 8000000 in
/-- **Thread `1`'s verbatim run in the value environment** (counted,
partial). -/
theorem p1V_memVals (S : BitVec 64 → Prop) (hal : isAligned 16 (symV "head") = true) :
    ∀ s g, StkV S s →
      Safely (cenv.instrStepEnv (SharedEnv.counted abaValEnv))
        (fun x => (x.1.2 = labV "done" ∧ True) ∨ False) ((s, labV "p1"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted abaValEnv)
    (Q := fun _ _ => True) (E := fun _ _ _ => False)
    (p1TableV S) ?_ abaCode1_eq abaCode1_wf abaCode1_placedIn
    abaCode1_last s g ⟨hsg, by simp, by simp⟩
  cfg_cases_env [abaCode1]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hstk, hnA, hnB⟩, h12, h12'⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals try simp (config := { decide := true }) only [true_implies, false_implies] at h12 h12'
  all_goals try simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  case vc1 => exact ⟨⟨hstk, hnA, hnB⟩, fun h => by simp at h, fun h => by simp at h⟩
  -- `p1pop1`
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => slot_ok
  case vc7 => slot_ok
  case vc8 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hld hm1 hm2 _
    rd_v
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_,
      fun h => by simp at h⟩, by tick1⟩
    regs; exact .inl rfl
  case vc9 => node_ok
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 => pop_ok
  case vc13 =>
    pop_names
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun h => by simp at h,
      fun h => by simp at h⟩, by tick2⟩
  case vc14 =>
    pop_names
    refine ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_, fun h => by simp at h⟩
    regs; exact hdV (x := v) hld.1
  case vc15 =>
    pop_names
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun h => by simp at h,
      fun h => by simp at h⟩, by tick2⟩
  case vc16 =>
    pop_names
    refine ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_, fun h => by simp at h⟩
    regs; exact hcas.1 (Or.inl rfl)
  -- `p1pop2`
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => slot_ok
  case vc7 => slot_ok
  case vc8 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 af hz hld hm1 hm2 _
    rd_v
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_,
      fun h => by simp at h⟩, by tick1⟩
    regs; exact h12
  case vc9 => node_ok
  case vc10 => exact hal
  case vc11 => exact (Stk.store hstk.1 hstk.2.1 hstk.2.1).1.loadInt_none hstk.2.2.2 (by decide)
  case vc12 => pop_ok
  case vc13 =>
    pop_names
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_,
      fun h => by simp at h⟩, by tick2⟩
    regs; exact h12
  case vc14 =>
    pop_names
    refine ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_, fun h => by simp at h⟩
    regs; exact h12
  case vc15 =>
    pop_names
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_,
      fun h => by simp at h⟩, by tick2⟩
    regs; exact h12
  case vc16 =>
    pop_names
    refine ⟨⟨Stk.slot hstk (by simp) rfl, hnA, hnB⟩, fun _ => ?_, fun h => by simp at h⟩
    regs; exact h12
  -- `p1push`
  case vc1 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨hstk, hnA, hnB⟩, fun h => by simp at h, fun h => by simp at h⟩,
      .inl (by decide)⟩
  case vc2 =>
    rename_i af hz _
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact ⟨⟨hstk, hnA, hnB⟩, fun h => by simp at h, fun _ => abaPtr_ne0 h12 hz⟩
  -- `p1push1`
  case vc1 => exact hal
  case vc2 => exact hstk.hd_none
  case vc3 => exact ⟨trivial, by simp [SharedEnv.AccessIn]⟩
  case vc4 => exact hstk.2.2.1
  case vc5 => exact hstk.2.1
  case vc6 => slot_ok
  case vc7 => slot_ok
  case vc8 =>
    -- the push's store: the old top to the node
    rename_i s1 g0 v g1 r1 g2 r2 g3 hn hld hm1 hm2 _
    rd_v
    refine ⟨fun _ => ?_, ?_⟩
    · regs
      show AbaPtr _ _ (lo _)
      rw [lo_setWidth]; exact hdV (x := v) hld.1
    · regs
      rw [show Int64.toBitVec 0 = 0 from rfl,
        show s1.regs.get64 .r12 + 0 = s1.regs.get64 .r12 from BitVec.add_zero _]
      exact node_in h12'
  case vc9 => exact hal
  case vc10 =>
    rename_i s1 g0 v g1 r1 g2 r2 g3 dm g4 hld hm1 hm2 hst _
    obtain ⟨-, -, hD, -⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 rfl rfl hst
    exact hD.loadInt_none hstk.2.2.2 (by decide)
  case vc11 =>
    -- the push's `cmpxchg16b`: the node as the new top
    rename_i s1 g0 v g1 r1 g2 r2 g3 dm g4 hld hm1 hm2 hst _
    refine ⟨fun old new hop _ _ => ?_, by simp [SharedEnv.AccessIn]⟩
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hop
    split at hop
    · cases hop
      show AbaPtr _ _ (lo _)
      rw [lo_append]; exact .inr h12'
    · cases hop
  all_goals
    rename_i s1 g0 v g1 r1 g2 r2 g3 dm g4 old g5 heq hnz hld hm1 hm2 hst hcas _
    obtain ⟨-, rfl⟩ := rd_lo hm1
    simp only [Reg64s.get64_set64] at hm2
    obtain ⟨-, rfl⟩ := rd_hi hm2
    obtain ⟨-, hcnt, hD, hmono⟩ := stCase (Stk.store hstk.1 hstk.2.1 hstk.2.1).1 rfl rfl hst
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨Stk.ofDom hstk (by simp) hD
      (hmono _ _ (Stk.store hstk.1 hstk.2.1 hstk.2.1).2), hnA, hnB⟩, fun h => by simp at h, fun h => ?_⟩, ?_⟩
    · first | (simp at h; done) | (regs; exact h12')
    · tick2

end Kraken.Promising.X64.EnvG.VecABA
