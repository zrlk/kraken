/-
**Part 2: the SPSC threads make only release
writes** (`EnvG/X64TreiberRelPure.lean`'s pattern): `spscProducerX_noNT`
and `spscConsumerX_noNT`, each thread in
`(relPureQ Arch.tso (fun _ _ => False)).within sAll`, by one
`cfgEnv_partial` table and `vcgen`.

Under `Arch.tso` every plain `movl` store is a release, so the purity
obligation is vacuous. In the all-release environment a load returns an
arbitrary value, so the slot address `buf0 + (k << 8)` is arbitrary: the
layout is `sAll` (every 4- and 8-byte location, `X64TreiberVC.lean`), whose
`Split` asks for a private memory that maps no byte (the start hypothesis
`dmem` of `StartPX`/`StartCX`). The table is that frame.

Also the start states `StartPX`, `StartCX` and the purity specifications
`spscNoNTSpecX` with `spscNoNTSpecX_init`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64
import Kraken.Promising.SLR.EnvG.X64TreiberVC
import Kraken.Promising.SLR.EnvG.X64SpscProg
import Kraken.Promising.SLR.EnvG.X64SpscWP

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken.Promising.X64.EnvG.TreiberX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The all-release environment on `sAll`. -/
abbrev EnvRA : SharedEnv := (SharedEnv.relPureQ Arch.tso fun _ _ => False).within sAll

/-- Close a permission goal of the counted all-release environment on `sAll`
(the `X64TreiberRelPure` script; its `simp` is a `try simp`, as it may make
no progress at an absolute address, so `X64SpscAbsVCGen` shares it). -/
macro "rel_ok" : tactic => `(tactic| (
  simp only [Kraken.SharedEnv.counted_ok]
  refine ⟨?_, Kraken.Promising.X64.EnvG.TreiberX.mem_sAll4 _⟩
  try simp
  first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl |
    (simp [Kraken.SharedEnv.relPureQ]; done)))

set_option hygiene false in
/-- The x64 SPSC producer's only-release-writes script, after `cfg_cases_env`
over its cells (shared by `spscProducerX_noNT` and the verbatim image's
`SpscAbs.spscProducerV_noNT`). -/
macro "spsc_noNT_producer" : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals try (obtain ⟨hd, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›; exact hd _)
  all_goals try rel_ok
  case vc3 => simp
  case vc2 s σ pre v σ1 hld hz =>
    -- `je pfull`: the back edge; the counter moved
    obtain ⟨hd, rfl, rfl⟩ := pre
    obtain ⟨w, -, h1, -⟩ := Kraken.Promising.X64.EnvG.SpscX.ld_out hd hld
    exact _root_.Table.ofLabelsEnv_at ⟨by decide, hd, .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  all_goals
    rename_i s σ pre v σ1 hld hz st dm σ2 hst dm2 σ3 hst2 hz2
    obtain ⟨hd, rfl, rfl⟩ := pre
    rcases hld with ⟨w, hw, -⟩ | ⟨-, w, hw, -⟩
    · simp [hd] at hw
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, ok, hs⟩
    · simp [hd] at hv
    rcases hst2 with ⟨hv, -⟩ | ⟨-, rfl, ok2, hs2⟩
    · simp [hd] at hv
    refine _root_.Table.ofLabelsEnv_at ⟨by decide, ?_, ?_⟩
    · intro a; exact hd a
    · have h1 : σ1.2 = σ.2 + 1 := hw.2
      have h2 : σ2.2 = σ1.2 + 1 := hs.2
      have h3 : σ3.2 = σ2.2 + 1 := hs2.2
      first | exact .inl (by decide) | exact .inr fun h => absurd (congrArg Prod.snd h.2) (by omega)))

set_option hygiene false in
/-- The x64 SPSC consumer's only-release-writes script, after `cfg_cases_env`
over its cells (shared by `spscConsumerX_noNT` and the verbatim image's
`SpscAbs.spscConsumerV_noNT`). -/
macro "spsc_noNT_consumer" : tactic => `(tactic| (
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals try rel_ok
  all_goals try (show ¬(Int64.toBitVec 8).toNat % 32 = 0; simp)
  -- `consumer` → `cempty0` (fall-through)
  · rename_i s σ pre v σ1 hld a
    exact pre.1 a
  -- the `je cemptyK` back edges and the fall-throughs into `cempty1`, `cempty2`, `cdone`
  all_goals first
    | (rename_i s σ pre v σ1 hld hz st v2 σ2 hld2 af dm σ3 hst a
       obtain ⟨hd, -, -⟩ := pre
       rcases hst with ⟨hv, -⟩ | ⟨-, rfl, -⟩
       · simp [hd] at hv
       exact hd a)
    | (rename_i s σ pre v σ1 hld hz st v2 σ2 hld2 af dm σ3 hst
       obtain ⟨hd, -, -⟩ := pre
       rcases hst with ⟨hv, -⟩ | ⟨-, rfl, -⟩
       · simp [hd] at hv
       exact _root_.Table.ofLabelsEnv_at ⟨by decide, hd, .inl (by decide)⟩)
    | (rename_i s σ pre v σ1 hld hz
       obtain ⟨hd, rfl, rfl⟩ := pre
       rcases hld with ⟨w, hw, -⟩ | ⟨-, w, hw, -⟩
       · simp [hd] at hw
       have h1 : σ1.2 = σ.2 + 1 := hw.2
       exact _root_.Table.ofLabelsEnv_at ⟨by decide, hd, .inr fun h => absurd (congrArg Prod.snd h.2) (by omega)⟩)))

section Producer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscProducerX)]

local instance spscProducerX.envR : CodeEnv := ⟨layout spscProducerX⟩

/-- **The x64 SPSC producer makes only release writes** (counted, partial). -/
theorem spscProducerX_noNT :
    PartialTripleEnv (SharedEnv.counted EnvRA) (fun s _ => DFrame s) spscProducerX
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (fun (_ : Label) s (_ : (SharedEnv.counted EnvRA).State) =>
    DFrame s) (hP := by funext s g; simp)
  cfg_cases_env [spscProducerX]
  spsc_noNT_producer
end Producer

section Consumer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscConsumerX)]

local instance spscConsumerX.envR : CodeEnv := ⟨layout spscConsumerX⟩

/-- **The x64 SPSC consumer makes only release writes** (counted, partial). -/
theorem spscConsumerX_noNT :
    PartialTripleEnv (SharedEnv.counted EnvRA) (fun s _ => DFrame s) spscConsumerX
      (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (fun (_ : Label) s (_ : (SharedEnv.counted EnvRA).State) =>
    DFrame s) (hP := by funext s g; simp)
  cfg_cases_env [spscConsumerX]
  spsc_noNT_consumer
end Consumer

/-! ## Start states and the purity specifications -/

section Start

variable [layout : _root_.Layout]

/-- **The producer's start state** (`0:rbx=buf0`, `(tail)` in `rdi`,
`(head)` in `rsi`): at the start of `spscProducerX`, with a private memory
that maps no byte. -/
structure StartPX (b h t : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout spscProducerX
  decls : s.decls = {}
  endPc : s.endPc = (layout spscProducerX).addrOf spscProducerX.length
  pc : s.st.2 = (layout spscProducerX).addrOf 0
  rbx : s.st.1.regs.get64 .rbx = b
  rdi : s.st.1.regs.get64 .rdi = t
  rsi : s.st.1.regs.get64 .rsi = h
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The consumer's start state** (`1:rbx=buf0`, `(tail)` in `rdi`,
`(head)` in `rsi`): at the start of `spscConsumerX`, with a private memory
that maps no byte. -/
structure StartCX (b h t : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout spscConsumerX
  decls : s.decls = {}
  endPc : s.endPc = (layout spscConsumerX).addrOf spscConsumerX.length
  pc : s.st.2 = (layout spscConsumerX).addrOf 0
  rbx : s.st.1.regs.get64 .rbx = b
  rdi : s.st.1.regs.get64 .rdi = t
  rsi : s.st.1.regs.get64 .rsi = h
  dmem : ∀ k, s.st.1.dmem.get? k = none

omit layout in
/-- A private memory that maps no byte is split from every layout. -/
theorem split_of_empty {S : SharedEnv.Layout} {d : DataMem} (h : ∀ k, d.get? k = none) : Split S d :=
  fun k _ => h k

omit layout in
/-- A private memory that maps no byte maps no 4-byte word. -/
theorem dFrame_of_empty {s : MachineData} (h : ∀ k, s.dmem.get? k = none) : DFrame s :=
  fun a => (split_sAll h).loadInt_none (mem_sAll4 a) (by decide) (by decide)

end Start

/-- The threads' all-release specifications (both at `sAll`): the producer
(layout `lP`) at thread `0`, the consumer (layout `lC`) elsewhere. -/
noncomputable def spscNoNTSpecX (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProducerX)]
    [Executable.ValidLayout (lC spscConsumerX)] : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := lP) sAll sAll_le16 spscProducerX fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpecQX.ofProgram (layout := lC) sAll sAll_le16 spscConsumerX fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the start states.** -/
theorem spscNoNTSpecX_init (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProducerX)]
    [Executable.ValidLayout (lC spscConsumerX)] {b h t : BitVec 64} {sP sC : State}
    (hP : StartPX (layout := lP) b h t sP) (hC : StartCX (layout := lC) b h t sC) :
    ∀ tid s, [sP, sC][tid]? = some s → (spscNoNTSpecX lP lC tid).Holds s
  | 0, s, hs => by
    cases hs
    letI : CodeEnv := ⟨lP spscProducerX⟩
    obtain ⟨he, hds, hend, hpc, -, -, -, hdm⟩ := hP
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lP) (spscProducerX_noNT (layout := lP)).uncount
      rfl he hds hend hpc (split_of_empty hdm) ⟨0, dFrame_of_empty hdm⟩
  | 1, s, hs => by
    cases hs
    letI : CodeEnv := ⟨lC spscConsumerX⟩
    obtain ⟨he, hds, hend, hpc, -, -, -, hdm⟩ := hC
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lC) (spscConsumerX_noNT (layout := lC)).uncount
      rfl he hds hend hpc (split_of_empty hdm) ⟨0, dFrame_of_empty hdm⟩
  | _ + 2, _, hs => by cases hs

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.spscProducerX_noNT
#print axioms Kraken.Promising.X64.EnvG.SpscX.spscConsumerX_noNT
#print axioms Kraken.Promising.X64.EnvG.SpscX.spscNoNTSpecX_init
