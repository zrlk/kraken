/-
**`treiber_pp.kl` (AArch64) never faults at the runner's declarations**
`treiber_pp_envG_runner_faultFree` and its
concrete instance `treiber_pp_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included).

The popper loads `[X2, #8]` and `[X2]` at an address it read from `top`; no
fixed-layout address run covers that. Both threads get **value
specifications** (`MemValsA64.ValSpecA`) over `inv S G` at the layout
`treiberSA top n1` (`top`, `n1`'s data word, `n1`'s `next` word), with

- `L` (`TreiberValLA`): the words `top` and `n1 + 8`;
- `V` (`TreiberValVA n1`): `0` or `n1` (low 64 bits).

The pusher writes `n1` to `top` (`casal`) and the `top` it read to
`n1 + 8`; the popper writes the `next` it read to `top`; a non-zero `top`
the popper reads is `n1`, so its loads are at `n1 + 8` and `n1`, inside the
layout (`treiberPusher_val_at`, `treiberPopper_val_at`: `vcgen` in the
counted `inv S G`, register tables only). The initial memory must give `top`
and `n1 + 8` the value `0`, and the popper must hold no private copy of
`n1 + 8`; at the runner's configuration all three are `decide`/`simp`.

Phase-1 limit: single-access trees (`treiberImageA_phase1F`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64
import Kraken.Promising.SLR.EnvG.A64WholeTreiberRunner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The locations of the value invariant: `top` and `n1`'s `next` word. -/
def TreiberValLA (t n : BitVec 64) : Loc → Prop := fun l => l = ⟨t, 8⟩ ∨ l = ⟨n + 8, 8⟩

/-- The values of the value invariant: the empty stack `0` or the node `n`. -/
def TreiberValVA (n : BitVec 64) : Val → Prop := fun v => v.setWidth 64 = 0 ∨ v.setWidth 64 = n

/-- The value condition. -/
abbrev treiberGA (t n : BitVec 64) : Loc → Val → Prop := fun l v => TreiberValLA t n l → TreiberValVA n v

/-- The threads' layout: `top`, `n1`'s data word and its `next` word. -/
abbrev treiberSA (t n : BitVec 64) : SharedEnv.Layout := [(t, 8), (n, 4), (n + 8, 8)]

/-- The threads' environment. -/
abbrev treiberEnvA (t n : BitVec 64) : SharedEnv := SharedEnv.inv (treiberSA t n) (treiberGA t n)

/-- A 64-bit compare-and-swap writing a `V`-value writes a `V`-value
(`MemValsA64.rmwOpBits_cas_val`). -/
theorem treiberValA_cas {n c y : BitVec 64} (hy : y = 0 ∨ y = n) :
    ∀ old v, rmwOpBits 64 (fun old => if old = c then some y else none) old = some v → TreiberValVA n v :=
  rmwOpBits_cas_val (P := fun x => x = 0 ∨ x = n) hy

section PopperAt

variable [CodeEnv]

/-- The popper's value table: `X0 = top`, neither `top` nor `n1 + 8` private. -/
abbrev popValTable (t n : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (treiberEnvA t n)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ Mem.loadInt s.dmem t 8 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none ∧
    (lb = "popper" ∨ lb = "qdone")

/-- **The popper in the value environment** (counted, partial, any ambient
code in which `treiberPopper` is `PlacedIn`): a non-zero `top` it reads is
`n1`, so its loads are at `n1 + 8` and `n1`; its `casal` writes the `next`
it read. -/
theorem treiberPopper_val_at (t n : BitVec 64) (hpl : Program.PlacedIn treiberPopper) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt treiberPopper l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, popValTable t n "popper" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (treiberEnvA t n)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "popper"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (treiberEnvA t n))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (popValTable t n) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [treiberPopper]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hdt, hdn, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, TreiberValLA, TreiberValVA]; done)
  case vc9 =>
    rename_i s σ0 v σ1 hnz rng x4 σ2 hld hld2 _
    have hv : TreiberValVA n v := by simpa [hx0, TreiberValLA] using hld.1
    simp [Reg64s.setXReg] at hnz
    have hx2 : v.setWidth 64 = n := hv.resolve_left hnz
    have hdn' : Mem.loadInt s.dmem (n + 8#64) 8 = none := hdn
    simp [Reg64s.setXReg, hx2, hdn', SharedEnv.inv, TreiberValLA] at hld2
    obtain ⟨w, ⟨hw, -⟩, rfl⟩ := hld2
    simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx2, TreiberValLA]
    exact fun old _ => treiberValA_cas hw old
  case vc4 =>
    rename_i s σ0 v σ1 hz hld _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], by simpa using hdn, .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2
    simp only [SharedEnv.tick_load] at h1
    omega
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, _, h, _⟩
      · exact Nat.le_refl _
      · omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], by simpa using hdn, .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc13 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hdt], by simpa using hdn, .inr rfl⟩,
      .inl (by decide)⟩

/-- The pusher's value table: `X0 = top`, `X1 = n1`, none of the three
words private. -/
abbrev pushValTable (t n : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (treiberEnvA t n)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ Mem.loadInt s.dmem t 8 = none ∧
    Mem.loadInt s.dmem n 4 = none ∧ Mem.loadInt s.dmem (n + 8) 8 = none ∧
    (lb = "pusher" ∨ lb = "push" ∨ lb = "pdone")

/-- **The pusher in the value environment** (counted, partial): it writes
the `top` it read to `n1 + 8` and `n1` to `top`. -/
theorem treiberPusher_val_at (t n : BitVec 64) (hpl : Program.PlacedIn treiberPusher) {endA : Int64}
    (hlast : ∀ l blk, Program.blockAt treiberPusher l = some blk → blk.next = none →
      cenv.after ((_root_.Executable.labels cenv).label l) blk.body = endA) :
    ∀ s g, pushValTable t n "pusher" s g →
      Safely (cenv.instrStepEnv (SharedEnv.counted (treiberEnvA t n)))
        (fun x => (x.1.2 = endA ∧ True) ∨ False) ((s, (_root_.Executable.labels cenv).label "pusher"), g) := by
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (treiberEnvA t n))
    (Q := fun _ _ => True) (E := fun _ _ _ => False) (pushValTable t n) ?_ (by rfl) (by decide) hpl hlast
  cfg_cases_env [treiberPusher]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdt, hdd, hdn, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, TreiberValLA, TreiberValVA]; done)
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hdn'] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx1, TreiberValLA]
    exact fun old _ => treiberValA_cas (Or.inr rfl) old
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

end PopperAt

/-! ## The image, the specifications and the theorem -/

/-- The initial memory satisfies the value invariant when `top` and
`n1 + 8` start at `0` (no messages yet). -/
theorem memValsA_treiber_init {t n : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hT0 : (Config.init states initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init states initMem).mem.initVal ⟨n + 8, 8⟩ = 0) :
    MemVals (TreiberValLA t n) (TreiberValVA n) (Config.init states initMem).mem := by
  refine ⟨fun l hl => ?_, fun ts w h _ => ?_⟩
  · rcases hl with rfl | rfl
    · simp only [TreiberValVA, hT0]; simp
    · simp only [TreiberValVA, hN0]; simp
  · simp [Memory.get?, Config.init] at h


section Image

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageA)]

local instance treiberImageA.envVal : CodeEnv := ⟨layout treiberImageA⟩

/-- The pusher's value run in the image. -/
theorem pusherW_val (t n : BitVec 64) :
    ∀ s g, pushValTable t n "pusher" s g →
      Safely ((layout treiberImageA).instrStepEnv (SharedEnv.counted (treiberEnvA t n)))
        (fun x => (x.1.2 = labT "pdone" ∧ True) ∨ False) ((s, labT "pusher"), g) :=
  treiberPusher_val_at t n pushA_placedIn (Program.last_of_check treiberPusher_exit)

/-- The popper's value run in the image. -/
theorem popperW_val (t n : BitVec 64) :
    ∀ s g, popValTable t n "popper" s g →
      Safely ((layout treiberImageA).instrStepEnv (SharedEnv.counted (treiberEnvA t n)))
        (fun x => (x.1.2 = labT "qdone" ∧ True) ∨ False) ((s, labT "popper"), g) :=
  treiberPopper_val_at t n popA_placedIn (Program.last_of_check treiberPopper_exit)

/-- A thread of the image as a value specification, ending at `endPc`. -/
def treiberSpecA (t n : BitVec 64) (endPc : Int64) : ValSpecA (treiberGA t n) where
  S := treiberSA t n
  e := layout treiberImageA
  e' := layout treiberImageA
  valid := inferInstance
  endPc := endPc
  post y := y.1.2 = endPc
  post_end _ h := h
  noPairs := treiberImageA_noPairs
  mask := MaskOf.refl _
  rmwLive := treiberImageA_rmwLive
  noFault := treiberImageA_noFault
  rootOnly st he hd tree hex := rootOnlyDA_of_phase1ShapeF (treiberImageA_phase1F st he hd tree hex)

/-- The pusher (thread `0`) and the popper. -/
def treiberValSpecA (t n : BitVec 64) : Nat → ValSpecA (treiberGA t n)
  | 0 => treiberSpecA t n (labT "pdone")
  | _ + 1 => treiberSpecA t n (labT "qdone")

/-- **No reachable configuration of the verbatim `treiber_pp.kl` threads
with the runner's declarations has a faulting step**, for strict sized `ds`
agreeing on `top`, `n1`'s data word and its `next` word, a popper with no
private `n1 + 8`, and an initial memory with `top` and `n1 + 8` at `0`. -/
theorem treiber_pp_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.StrictSized)
    (t n : BitVec 64) (hag : ds.AgreesOnA (treiberSA t n)) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushWD ds t n sP) (hQ : StartPopWD ds t sQ) (hdnQ : Mem.loadInt sQ.st.1.dmem (n + 8) 8 = none)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨n + 8, 8⟩ = 0) :
    Config.FaultFree A fuel (Config.init [sP, sQ] initMem) := by
  refine a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (treiberValSpecA t n) (fun _ => ds) (fun _ => hsz)
    (fun | 0 => hag | _ + 1 => hag) (memValsA_treiber_init hT0 hN0) (init_threads_of2 ?_ ?_)
  · obtain ⟨he, hds, hpc, hend, hx0, hx1, -, hdt, hdd, hdn⟩ := hP
    refine ⟨he, hds, hend, ?_⟩
    rw [show sP.st = (sP.st.1, labT "pusher") from Prod.ext rfl hpc]
    exact (Safely.uncountA (pusherW_val t n _ ((), 0) ⟨hx0, hx1, hdt, hdd, hdn, .inl rfl⟩)).mono
      fun _ ⟨_, h⟩ => h.elim And.left False.elim
  · obtain ⟨he, hds, hpc, hend, hx0, hdt, -⟩ := hQ
    refine ⟨he, hds, hend, ?_⟩
    rw [show sQ.st = (sQ.st.1, labT "popper") from Prod.ext rfl hpc]
    exact (Safely.uncountA (popperW_val t n _ ((), 0) ⟨hx0, hdt, hdnQ, .inl rfl⟩)).mono
      fun _ ⟨_, h⟩ => h.elim And.left False.elim

end Image

open Kraken.Promising.SLR.EnvG.ConcreteTreiber in
set_option maxRecDepth 8192 in
/-- **`treiber_pp.kl` never faults**, from the runner's exact configuration
(`[pusherWD0, popperWD1]` with the runner's declarations, initial memory
`treiberInitMem`), under any architecture. -/
theorem treiber_pp_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [pusherWD0, popperWD1] treiberInitMem) :=
  treiber_pp_envG_runner_faultFree (layout := wLayoutT) treiberDeclsD_sized topAddr n1Addr
    (by decls_agrees_on_a) pusherWD0_start popperWD1_start
    (by simp [popperWD1, popperW1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, n1Addr])
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)

end Kraken.Promising.SLR.EnvG.Treiber

#print axioms Kraken.Promising.SLR.EnvG.Treiber.treiber_pp_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.Treiber.treiber_pp_envG_runner_faultFree_concrete
