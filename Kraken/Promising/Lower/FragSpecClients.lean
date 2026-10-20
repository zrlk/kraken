/-
**Validation part 2: the fragment specifications
instantiated at other programs.** ISA: AArch64; machine:
the executable machine's per-thread environment semantics, partial
correctness.

- **The allocation pilot** (`allocP`): `Alloc.push_spec`, `pop_spec`, `push_pure`, `pop_pure`
  (`Lower/AllocSpecs.lean`, `Lower/AllocPure.lean`, about 220 lines of copied
  proof there) re-derived from the first lowering pilot's fragment specifications
  (`Lower/FragSpecPilot.lean`), one line each, with `rfl` statement checks.
  The allocator itself as a fragment specification, in every environment:
  `allocFrag_spec`, and `alloc_spec_viaFrag`.
- **The stack-frame pilot** (`pilot2`): the same four the first lowering pilot fragment specifications at
  `pilot2`'s layout, one line each. They are true facts about `pilot2`, but
  `pilot2`'s own `main` cannot use them: its `dmem` holds the call stack, so
  `NoDmem` fails, and it works in the value-tracking environment `EWV`
  (`EnvGCAdjV`), not `EW`. `Pilot2.push_spec2` etc. are different
  specifications of the same fragment.
-/
import Kraken.Promising.Lower.FragSpecPilot
import Kraken.Promising.Lower.AllocPure
import Kraken.Promising.Lower.Pilot2Specs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Alloc

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP pushFrag popFrag PushPre PushPost PopPre PopPost
  pushFrag_spec popFrag_spec pushFrag_pure popFrag_pure)

/-- **`alloc`'s specification, placement-independent**, in every
environment (`Alloc.alloc_spec`). -/
theorem allocFrag_spec (env : SharedEnv) [env.FenceMono] (R : env.State → Prop)
    (hR : ∀ g g', R g → SharedEnv.FenceMono.le g g' → R g') (n : BitVec 64) :
    FragSpecEnv env allocFrag "alloc" (AllocPre env R n) (AllocPost env R n) := by
  refine FragSpecEnv.of_cfg (fun _ t _ lb s σ => lb = "alloc" ∧ s = t ∧ R σ) rfl (by decide)
    (fun _ _ _ ⟨_, _, _, hg⟩ => ⟨rfl, rfl, hg⟩) ?_
  intro _ ra t g ⟨hlr, h27, hlim, hg⟩
  cfg_cases_env [allocFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨-, rfl, hR0⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp [AllocPost, AllocSaved, MachineData.lr] at *
  case vc1 =>
    rename_i hhi _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc2 =>
    refine .inr ?_
    repeat (first | exact hR0 | refine hR _ _ ?_ (by assumption))

section AllocP

variable [layout : _root_.Layout] [Executable.ValidLayout (layout allocP)]

attribute [local instance] allocP.env

theorem alloc_spec_viaFrag (env : SharedEnv) [env.FenceMono] (R : env.State → Prop)
    (hR : ∀ g g', R g → SharedEnv.FenceMono.le g g' → R g') (n : BitVec 64) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label "alloc") (AllocPre env R n)
      (AllocPost env R n) :=
  (allocFrag_spec env R hR n).of_placed allocP_placed (by decide)

theorem push_spec_viaFrag (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "push") (PushPre P w)
      (PushPost P w) :=
  (pushFrag_spec P w hL hw).of_placed allocP_placed (by decide)

theorem pop_spec_viaFrag (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) :=
  (popFrag_spec P w hw).of_placed allocP_placed (by decide)

theorem push_pure_viaFrag (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushFrag_pure rel t n hn).of_placed allocP_placed (by decide)

theorem pop_pure_viaFrag (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pure rel t).of_placed allocP_placed (by decide)

end AllocP

example : @alloc_spec_viaFrag = @alloc_spec := rfl
example : @push_spec_viaFrag = @push_spec := rfl
example : @pop_spec_viaFrag = @pop_spec := rfl
example : @push_pure_viaFrag = @push_pure := rfl
example : @pop_pure_viaFrag = @pop_pure := rfl

end Kraken.Promising.Lower.Alloc

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP PushPre PushPost PopPre PopPost
  pushFrag_spec popFrag_spec pushFrag_pure popFrag_pure)

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

attribute [local instance] pilot2.env

/-- The first lowering pilot's `push` specification at `pilot2`. -/
theorem push_spec_viaFrag (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "push") (PushPre P w)
      (PushPost P w) :=
  (pushFrag_spec P w hL hw).of_placed pilot2_placed (by decide)

/-- The first lowering pilot's `pop` specification at `pilot2`. -/
theorem pop_spec_viaFrag (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) :=
  (popFrag_spec P w hw).of_placed pilot2_placed (by decide)

/-- The first lowering pilot's `push` purity at `pilot2`. -/
theorem push_pure_viaFrag (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ NoDmem s)
      (fun _ s _ s' _ => CalleeSaved s s') :=
  (pushFrag_pure rel t n hn).of_placed pilot2_placed (by decide)

/-- The first lowering pilot's `pop` purity at `pilot2`. -/
theorem pop_pure_viaFrag (rel : Loc → Pred) (t : BitVec 64) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') :=
  (popFrag_pure rel t).of_placed pilot2_placed (by decide)

end Kraken.Promising.Lower.Pilot2
