/-
**`spsc_queue.kl` never faults at the runner's declarations**: `x64_spsc_envG_runner_faultFree` and its concrete
instance `x64_spsc_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included).

The slot accesses `(%rbx,%rdx,1)` are at `buf0 + (i << 8)` for an index `i`
loaded from `tail` (producer) or `head` (consumer); the purity
specifications sit at `sAll`, which the runner's declarations do not agree
on. Here both threads get **value specifications** (`MemValsX64.ValSpecX`)
at the declared layout `spscS` (`buf0`, `buf0 + 256`, `head`, `tail`), with
the value invariant

- `L` (`SpscValL`): the 4-byte words `head` and `tail`;
- `V` (`SpscValV`): values whose low word is `0` or `1`.

An `L = ∅` specification does not suffice: with arbitrary loaded indices the
slot address is arbitrary. Both threads store `(i + 1) & 1` to their index,
so `MemVals L V` holds at every reachable configuration, and the slot
address is `buf0` or `buf0 + 256` (`spscProducerV_memVals`,
`spscConsumerV_memVals`: the `…V_noNT` scripts in `(valEnv L V).within
spscS`, the index kept in the table at the loop heads). The initial memory
must give `head` and `tail` the value `0`; at the runner's `spscInitMemV`
this is `decide`.

Phase-1 limit: single-access trees (`spscImageV_phase1X`).
-/
import Kraken.Promising.SLR.EnvG.MemValsX64
import Kraken.Promising.SLR.EnvG.X64SpscAbsRunner

namespace Kraken.Promising.X64.EnvG.SpscAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpscX Kraken.Promising.X64.EnvG.TreiberX

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The value invariant -/

/-- The locations of the value invariant: the indices `head` and `tail`. -/
def SpscValL (h t : BitVec 64) : Loc → Prop := fun l => l = ⟨h, 4⟩ ∨ l = ⟨t, 4⟩

/-- The values of the value invariant: low word `0` or `1`. -/
def SpscValV : Val → Prop := fun v => v.setWidth 32 = 0 ∨ v.setWidth 32 = 1

/-- The threads' environment: the value environment at `spscS`. -/
abbrev spscValEnv (P : SP) : SharedEnv := (SharedEnv.valEnv (SpscValL P.h P.t) SpscValV).within (spscS P)

/-- A 64-bit register whose low word is `0` or `1`. -/
abbrev Bit32 (x : BitVec 64) : Prop := x.setWidth 32 = 0 ∨ x.setWidth 32 = 1

/-- `(y &&& 1)` has low word `0` or `1`. -/
theorem spscVal_and1 (y : BitVec 32) : y &&& 1#32 = 0 ∨ y &&& 1#32 = 1 := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases y.getLsbD 0 <;> decide

/-- A `Bit32` index shifted by `8`, as a 64-bit offset, is `0` or `256`. -/
theorem spscVal_slot {x : BitVec 64} (h : Bit32 x) :
    (x.setWidth 32 <<< 8#32).setWidth 64 = 0 ∨ (x.setWidth 32 <<< 8#32).setWidth 64 = 256 := by
  rcases h with h | h <;> rw [h] <;> decide

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageV)]

/-! ## The threads -/

section Runs

local instance spscImageV.envMemVals : CodeEnv := ⟨layout spscImageV⟩

/-- The producer's table: the frame, and at `pfull` the loaded index and the
next one in `{0, 1}`. -/
abbrev prodTableV : Label → MachineData → (SharedEnv.counted (spscValEnv spscP)).State → Prop :=
  fun lb s _ => FrameA spscP s ∧ (lb = "pfull" → Bit32 (s.regs.get64 .rax) ∧ Bit32 (s.regs.get64 .rcx))

/-- **The verbatim producer in the value environment** (counted, partial):
its slot store is at `buf0 + (i << 8)` with `i ∈ {0, 1}` the `tail` it
read, and it stores `(i + 1) & 1` to `tail`. -/
theorem spscProducerV_memVals (hL : SpscLocs spscP) :
    ∀ s g, FrameA spscP s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (spscValEnv spscP)))
        (fun x => (x.1.2 = labS "pdone" ∧ True) ∨ False) ((s, labS "producer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (spscValEnv spscP)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) prodTableV ?_
    producerFragV_eq producerFragV_wf producerFragV_placedIn producerFragV_last s g ⟨hs, by simp⟩
  cfg_cases_env [producerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals clear ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0
  all_goals try (simp only [SharedEnv.counted_ok]; refine ⟨trivial, ?_⟩; simp [SharedEnv.AccessIn]; done)
  case vc1 => exact ⟨⟨by simp [hx0], by simpa using hdf⟩, by simp⟩
  case vc2 =>
    -- `produce` → `pfull`
    rename_i v σ1 hld af
    obtain ⟨w, hw, -, rfl⟩ := ld_out hdf hld
    have hv : SpscValV w := hw (Or.inr rfl)
    refine ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => ⟨?_, ?_⟩⟩
    · simpa [SpscValV] using hv
    · simpa using spscVal_and1 _
  case vc2 =>
    -- the `je pfull` back edge
    rename_i v σ1 hld hz
    obtain ⟨w, -, h1, rfl⟩ := ld_out hdf hld
    have hT := hT rfl
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using hT⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc3 => simp
  case vc4 =>
    -- the slot store
    have hT := hT rfl
    simp only [SharedEnv.counted_ok]
    have h := hT.1
    simp only [Reg64s.get64] at h
    rcases h with h | h
    · refine ⟨fun hl => ?_, ?_⟩
      · simp [hx0, h, SpscValL, Reg64s.get_low32] at hl
        rcases hl with hl | hl
        · exact absurd hl hL.bh
        · exact absurd hl hL.bt
      · simp [hx0, h, SharedEnv.AccessIn, Reg64s.get_low32]
    · refine ⟨fun hl => ?_, ?_⟩
      · simp [hx0, h, SpscValL, Reg64s.get_low32] at hl
        rcases hl with hl | hl
        · exact absurd hl hL.b1h
        · exact absurd hl hL.b1t
      · simp [hx0, h, SharedEnv.AccessIn, Reg64s.get_low32]
  case vc5 =>
    -- the `tail` store
    have hT := hT rfl
    simp only [SharedEnv.counted_ok]
    exact ⟨fun _ => by simpa [SpscValV] using hT.2, by simp [SharedEnv.AccessIn]⟩
  all_goals
    rename_i s0 σ v σ1 hld hz st dm σ2 hst dm2 σ3 hst2 hz2
    rcases hld with ⟨w, hw, -⟩ | ⟨-, w, hw, -⟩
    · simp [hdf] at hw
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, ok, hs⟩
    · simp [hdf] at hv
    rcases hst2 with ⟨hv, -⟩ | ⟨-, rfl, ok2, hs2⟩
    · simp [hdf] at hv
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, by simp⟩, ?_⟩
    have h1 : σ1.2 = σ.2 + 1 := hw.2
    have h2 : σ2.2 = σ1.2 + 1 := hs.2
    have h3 : σ3.2 = σ2.2 + 1 := hs2.2
    first | exact .inl (by decide) | exact .inr fun h => absurd (congrArg Prod.snd h.2) (by omega)

/-- The consumer's table: the frame, and at the loop heads the index in
`{0, 1}`. -/
abbrev consTableV : Label → MachineData → (SharedEnv.counted (spscValEnv spscP)).State → Prop :=
  fun lb s _ => FrameA spscP s ∧ (lb = "cempty0" ∨ lb = "cempty1" ∨ lb = "cempty2" → Bit32 (s.regs.get64 .rax))

set_option maxHeartbeats 1000000 in
/-- **The verbatim consumer in the value environment** (counted, partial):
its slot loads are at `buf0 + (i << 8)` with `i ∈ {0, 1}` the `head` it
read, and it stores `(i + 1) & 1` to `head`. -/
theorem spscConsumerV_memVals :
    ∀ s g, FrameA spscP s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (spscValEnv spscP)))
        (fun x => (x.1.2 = labS "cdone" ∧ True) ∨ False) ((s, labS "consumer"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (spscValEnv spscP)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) consTableV ?_
    consumerFragV_eq consumerFragV_wf consumerFragV_placedIn consumerFragV_last s g ⟨hs, by simp⟩
  cfg_cases_env [consumerFragV]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hdf⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals clear ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0
  all_goals try (simp only [SharedEnv.counted_ok]; refine ⟨trivial, ?_⟩; simp [SharedEnv.AccessIn]; done)
  case vc2 =>
    -- `consumer` → `cempty0`
    rename_i v σ1 hld
    obtain ⟨w, hw, -, rfl⟩ := ld_out hdf hld
    exact ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa [SpscValV] using hw (Or.inl rfl)⟩
  case vc2 =>
    -- the `je cemptyK` back edge
    rename_i v σ1 hld hz
    obtain ⟨w, -, h1, rfl⟩ := ld_out hdf hld
    have hT := hT (by simp)
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using hT⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc3 => simp
  case vc4 =>
    -- the slot load
    simp only [SharedEnv.counted_ok]
    refine ⟨trivial, ?_⟩
    have h := hT (by simp)
    simp only [Reg64s.get64] at h
    rcases h with h | h <;> simp [hx0, h, SharedEnv.AccessIn, Reg64s.get_low32]
  case vc5 =>
    -- the `head` store
    simp only [SharedEnv.counted_ok]
    refine ⟨fun _ => ?_, by simp [SharedEnv.AccessIn]⟩
    simpa [SpscValV] using spscVal_and1 _
  case vc6 =>
    -- the round's end
    rename_i v σ1 hld hz st v2 σ2 hld2 af dm σ3 hst
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, -⟩
    · simp [hdf] at hv
    first
      | exact ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using spscVal_and1 _⟩
      | exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, by simp⟩, .inl (by decide)⟩
  case vc2 =>
    -- the `je cemptyK` back edge
    rename_i v σ1 hld hz
    obtain ⟨w, -, h1, rfl⟩ := ld_out hdf hld
    have hT := hT (by simp)
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using hT⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc3 => simp
  case vc4 =>
    -- the slot load
    simp only [SharedEnv.counted_ok]
    refine ⟨trivial, ?_⟩
    have h := hT (by simp)
    simp only [Reg64s.get64] at h
    rcases h with h | h <;> simp [hx0, h, SharedEnv.AccessIn, Reg64s.get_low32]
  case vc5 =>
    -- the `head` store
    simp only [SharedEnv.counted_ok]
    refine ⟨fun _ => ?_, by simp [SharedEnv.AccessIn]⟩
    simpa [SpscValV] using spscVal_and1 _
  case vc6 =>
    -- the round's end
    rename_i v σ1 hld hz st v2 σ2 hld2 af dm σ3 hst
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, -⟩
    · simp [hdf] at hv
    first
      | exact ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using spscVal_and1 _⟩
      | exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, by simp⟩, .inl (by decide)⟩
  case vc2 =>
    -- the `je cemptyK` back edge
    rename_i v σ1 hld hz
    obtain ⟨w, -, h1, rfl⟩ := ld_out hdf hld
    have hT := hT (by simp)
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using hT⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc3 => simp
  case vc4 =>
    -- the slot load
    simp only [SharedEnv.counted_ok]
    refine ⟨trivial, ?_⟩
    have h := hT (by simp)
    simp only [Reg64s.get64] at h
    rcases h with h | h <;> simp [hx0, h, SharedEnv.AccessIn, Reg64s.get_low32]
  case vc5 =>
    -- the `head` store
    simp only [SharedEnv.counted_ok]
    refine ⟨fun _ => ?_, by simp [SharedEnv.AccessIn]⟩
    simpa [SpscValV] using spscVal_and1 _
  case vc6 =>
    -- the round's end
    rename_i v σ1 hld hz st v2 σ2 hld2 af dm σ3 hst
    rcases hst with ⟨hv, -⟩ | ⟨-, rfl, -⟩
    · simp [hdf] at hv
    first
      | exact ⟨⟨by simp [hx0], by simpa using hdf⟩, fun _ => by simpa using spscVal_and1 _⟩
      | exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hdf⟩, by simp⟩, .inl (by decide)⟩


end Runs

/-! ## The specifications -/

/-- **The whole image is phase-1** (both roles' cells, the trailer). -/
theorem spscImageV_phase1X : Phase1TreeX Arch.tso (layout spscImageV) := by
  refine phase1TreeX_of_dirs (dirsPhase1X_layout ?_)
  rw [show spscImageV = producerFragV ++ consumerFragV ++ spscDataV by decide]
  intro d hd
  simp only [List.mem_append] at hd
  rcases hd with (hd | hd) | hd
  · exact producerFragV_dirsPhase1X d hd
  · exact consumerFragV_dirsPhase1X d hd
  · simp only [spscDataV, List.mem_cons, List.not_mem_nil, or_false] at hd
    intro e z s pc
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [_root_.Directive.interp, Kraken.Promising.X64.toEv, Phase1Shape, DetAccess, SingleAccessS]

/-- The verbatim threads' value specifications at `spscS`. -/
noncomputable def spscValSpec : Nat → ValSpecX (SpscValL spscP.h spscP.t) SpscValV
  | 0 =>
    { S := spscS spscP
      le16 := spscS_le16 _
      e := layout spscImageV
      valid := inferInstance
      endPc := labS "pdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labS "pdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := spscS spscP
      le16 := spscS_le16 _
      e := layout spscImageV
      valid := inferInstance
      endPc := labS "cdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labS "cdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The value specifications hold at the start states with declarations.** -/
theorem spscValSpec_initD (hL : SpscLocs spscP) {ds : Decls} {sP sC : State} (hP : StartPVD ds sP)
    (hC : StartCVD ds sC) : ∀ tid s, [sP, sC][tid]? = some s → (spscValSpec tid).HoldsD ds s
  | 0, s, hs => by
    cases hs
    refine ⟨hP.exe, hP.endPc, hP.decls, split_of_empty hP.dmem, ?_⟩
    rw [show sP.st = (sP.st.1, labS "producer") from Prod.ext rfl hP.pc]
    exact Safely.uncountS (spscProducerV_memVals hL sP.st.1 ((), 0) ⟨hP.rbx, dFrame_of_empty hP.dmem⟩)
  | 1, s, hs => by
    cases hs
    refine ⟨hC.exe, hC.endPc, hC.decls, split_of_empty hC.dmem, ?_⟩
    rw [show sC.st = (sC.st.1, labS "consumer") from Prod.ext rfl hC.pc]
    exact Safely.uncountS (spscConsumerV_memVals sC.st.1 ((), 0) ⟨hC.rbx, dFrame_of_empty hC.dmem⟩)
  | _ + 2, _, hs => by cases hs

omit layout [Executable.ValidLayout (layout spscImageV)] in
/-- The initial memory of `Config.init` satisfies the value invariant when
`head` and `tail` start at `0` (no messages yet). -/
theorem memVals_spsc_init {h t : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hH0 : (Config.init states initMem).mem.initVal ⟨h, 4⟩ = 0)
    (hT0 : (Config.init states initMem).mem.initVal ⟨t, 4⟩ = 0) :
    MemVals (SpscValL h t) SpscValV (Config.init states initMem).mem := by
  refine ⟨fun l hl => ?_, fun ts w hw _ => ?_⟩
  · rcases hl with rfl | rfl
    · simp only [SpscValV, hH0]; simp
    · simp only [SpscValV, hT0]; simp
  · simp [Memory.get?] at hw

/-! ## The theorem -/

/-- **No reachable configuration of the verbatim `spsc_queue.kl` threads
with the runner's declarations has a faulting step**, under any
architecture (promises included), for `ds` agreeing on `spscS` (`buf0`,
`buf0 + 256`, `head`, `tail`) and an initial memory with `head` and `tail`
at `0`. -/
theorem x64_spsc_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hL : SpscLocs spscP) (hag : ds.AgreesOn (spscS spscP)) {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPVD ds sP) (hC : StartCVD ds sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "tail", 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨symS "head", 4⟩ = 0) :
    Config.FaultFree A fuel (Config.init [sP, sC] initMem) :=
  x64_faultFree_of_valSpecs spscValSpec (fun _ => ds) (fun _ => hsz)
    (fun tid => by rcases tid with _ | _ <;> exact hag)
    (fun tid => by rcases tid with _ | _ <;> exact spscImageV_noFaultCode)
    (fun tid => by rcases tid with _ | _ <;> exact rootOnlyD_of_phase1TreeX spscImageV_phase1X)
    (memVals_spsc_init hH0 hT0) (init_threads_of (spscValSpec_initD hL hP hC))

end Kraken.Promising.X64.EnvG.SpscAbs

namespace Kraken.Promising.X64.EnvG.SpscAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.SpscAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.SpscX

section
attribute [local instance] spscLayoutV

/-- **`spsc_queue.kl` never faults**, from the runner's exact configuration
(threads `spscP0D`, `spscC1D` with the runner's declarations `spscDeclsD`,
initial memory `spscInitMemV`). -/
theorem x64_spsc_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [spscP0D, spscC1D] spscInitMemV) :=
  x64_spsc_envG_runner_faultFree (layout := spscLayoutV) spscDeclsD_sized
    (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [symS_buf0, symS_head, symS_tail] <;> decide)
    (by
      show spscDeclsD.AgreesOn [(symS "buf0", 4), (symS "buf0" + 256, 4), (symS "head", 4), (symS "tail", 4)]
      rw [symS_buf0, symS_head, symS_tail]; decls_agrees_on)
    spscP0D_start spscC1D_start
    (by rw [symS_tail]; simp only [Config.init_mem]; decide)
    (by rw [symS_head]; simp only [Config.init_mem]; decide)

end

end Kraken.Promising.X64.EnvG.SpscAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpscAbs.x64_spsc_envG_runner_faultFree
#print axioms Kraken.Promising.X64.EnvG.SpscAbs.Concrete.x64_spsc_envG_runner_faultFree_concrete
