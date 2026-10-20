/-
Part 9: **the threads of `treiber_pp.kl` are pure**
(`SwplLockRelPure.lean` for `treiberPusher`/`treiberPopper`): in
`SharedEnv.relPure Arch.armv8 rel` for any release predicates `rel` that are
pure at the node's data word `[n]` (4 bytes) and link word `[n + 8]`
(8 bytes). The pusher's non-release writes are the two plain `str`s of the
node; both `casal`s are release RMWs (unconstrained); the popper has no other
write.

The purity half of `final_of_relPureSafelyF`: `treiberPureSpec` and
`treiberPureSpec_init`.

The purity runs are stated once over any ambient code
(`treiberPusher_relPure_at`, `treiberPopper_relPure_at`;
`EnvG/A64MaskRunAt.lean`); the per-thread triples and the whole-image runs
(`EnvG/A64WholeTreiberVCGen.lean`) are their instances.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.TreiberSmoke
import Kraken.AArch64.EnvCfg
import Kraken.Promising.SLR.EnvG.A64MaskRunAt

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber

set_option mvcgen.warning false
set_option experimental.vcgen true

section PusherAt

variable [CodeEnv]

/-- The pusher's purity table: the frame everywhere. -/
abbrev pushPureTable (t n : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem t 8 = none ∧ Mem.loadInt s.dmem n 4 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none ∧
    (lb = "pusher" ∨ lb = "push" ∨ lb = "pdone")

/-- **`treiberPusher_relPure` in any ambient code** in which `treiberPusher`
is `PlacedIn`, from `pusher` to the end address `endA` of its last block. -/
theorem treiberPusher_relPure_at (rel : Loc → Pred) (t n : BitVec 64)
    (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v)
    (hpl : Program.PlacedIn treiberPusher) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt treiberPusher l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, pushPureTable t n rel "pusher" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "pusher"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (pushPureTable t n rel) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [treiberPusher]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdt, hdd, hdn, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  all_goals have hn' : ∀ v : Val, Pred.Pure (rel ⟨n + 8#64, 8⟩) v := hn
  all_goals try (simp [hx0, hx1, hdt, hdd, hdn', SharedEnv.relPureQ, Arch.storeKind, hd, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc3 =>
    rename_i s σ0 rng dm σ1 hst _
    simp [hx1, hdd] at hst
    obtain ⟨rfl, -⟩ := hst
    simp (config := { decide := true }) [hx0, hx1, hdt, hdd, hdn']
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hdn'] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hdt]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hdn'] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hdn'] at hst
    obtain ⟨rfl, hst2⟩ := hst
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdt], by simp [hdd],
      by simp [hdn'], .inr (.inl rfl)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hdn'] at hst
    obtain ⟨rfl, -⟩ := hst
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hdt], by simp [hdd],
      by simp [hdn'], .inr (.inr rfl)⟩, .inl (by decide)⟩
  all_goals done

end PusherAt

section Pusher

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPusher)]

local instance treiberPusher.env : CodeEnv := ⟨layout treiberPusher⟩

/-- **The pusher is pure** (counted, partial): its `str`s write the node,
pure there; the `casal` is a release. -/
theorem treiberPusher_relPure (rel : Loc → Pred) (t n : BitVec 64)
    (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem t 8 = none ∧ Mem.loadInt s.dmem n 4 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none)
      treiberPusher (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed treiberPusher "pusher" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [pushPureTable]) fun _ hlast =>
    treiberPusher_relPure_at rel t n hd hn hpl.toPlacedIn hlast

end Pusher

section PopperAt

variable [CodeEnv]

/-- The popper's purity table: the frame everywhere. -/
abbrev popPureTable (t : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ Mem.loadInt s.dmem t 8 = none ∧ (lb = "popper" ∨ lb = "qdone")

/-- **`treiberPopper_relPure` in any ambient code** in which `treiberPopper`
is `PlacedIn`, from `popper` to the end address `endA` of its last block. -/
theorem treiberPopper_relPure_at (rel : Loc → Pred) (t : BitVec 64)
    (hpl : Program.PlacedIn treiberPopper) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt treiberPopper l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, popPureTable t rel "popper" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "popper"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (popPureTable t rel) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [treiberPopper]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hdt, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hdt, SharedEnv.relPureQ]; done)
  case vc4 =>
    rename_i s σ0 v σ1 hz hld _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2
    simp only [SharedEnv.tick_load] at h1
    omega
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, _, h, _⟩
      · exact Nat.le_refl _
      · omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], .inl rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc13 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], .inr rfl⟩, .inl (by decide)⟩
  all_goals done

end PopperAt

section Popper

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberPopper)]

local instance treiberPopper.env : CodeEnv := ⟨layout treiberPopper⟩

/-- **The popper is pure** (counted, partial): its only write is the
`casal`, a release. -/
theorem treiberPopper_relPure (rel : Loc → Pred) (t : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = t ∧ Mem.loadInt s.dmem t 8 = none)
      treiberPopper (fun _ _ => True) (fun _ _ _ => False) :=
  have hpl : Program.Placed treiberPopper "popper" := Program.placed_of_layout (by decide) (by rfl) (by decide)
  PartialTripleEnv.of_runAtT hpl (by funext s g; simp [popPureTable]) fun _ hlast =>
    treiberPopper_relPure_at rel t hpl.toPlacedIn hlast

end Popper

/-! ## Start states and the purity specifications -/

section Start

variable [layout : _root_.Layout]

/-- **The pusher's start state** (`0:X0=top; 0:X1=n1; 0:X9=1`): at the start
of `treiberPusher` with `x0 = t`, `x1 = n`, `w9 = 1`; no private copy of
`top` or of the node's words. -/
structure StartPush (t n : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiberPusher
  decls : s.decls = {}
  endPc : s.endPc = (layout treiberPusher).addrOf treiberPusher.length
  pc : s.st.2 = (layout treiberPusher).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec = n
  x9 : s.st.1.regs.X9.toBitVec.setWidth 32 = 1
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  dd : Mem.loadInt s.st.1.dmem n 4 = none
  dn : Mem.loadInt s.st.1.dmem (n + 8) 8 = none

/-- **The popper's start state** (`1:X0=top`): at the start of
`treiberPopper` with `x0 = t`; no private copy of `top` or of any 4-byte
word (the data load's address is a loaded value). -/
structure StartPop (t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiberPopper
  decls : s.decls = {}
  endPc : s.endPc = (layout treiberPopper).addrOf treiberPopper.length
  pc : s.st.2 = (layout treiberPopper).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = t
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Start

/-- The threads' purity specifications: the pusher (layout `lP`) at thread
`0`, the popper (layout `lQ`) elsewhere. -/
def treiberPureSpec (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusher)]
    [Executable.ValidLayout (lQ treiberPopper)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := lP) treiberPusher fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := lQ) treiberPopper fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states**, for release
predicates pure at the node's words. -/
theorem treiberPureSpec_init (lP lQ : _root_.Layout) [Executable.ValidLayout (lP treiberPusher)]
    [Executable.ValidLayout (lQ treiberPopper)] {rel : Loc → Pred} {t n : BitVec 64}
    (hd : ∀ v : Val, Pred.Pure (rel ⟨n, 4⟩) v) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v)
    {sP sQ : isa.State} (hP : StartPush (layout := lP) t n sP) (hQ : StartPop (layout := lQ) t sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberPureSpec lP lQ rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, -, hdt, hdd, hdn⟩ := hP
    letI : CodeEnv := ⟨lP treiberPusher⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lP)
      (treiberPusher_relPure (layout := lP) rel t n hd hn).uncount rfl he hds hend hpc ⟨0, hx0, hx1, hdt, hdd, hdn⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hdt, -⟩ := hQ
    letI : CodeEnv := ⟨lQ treiberPopper⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lQ)
      (treiberPopper_relPure (layout := lQ) rel t).uncount rfl he hds hend hpc ⟨0, hx0, hdt⟩
  | _ + 2, _, hs => by cases hs

end Kraken.Promising.SLR.EnvG.Treiber
