/-
**Part 5: the three-thread relay through a
release-only swap, end to end** (`mp_relay3_swpl.kl`; the relay proof's
`EnvG/RelayPublic.lean` with the relay's `stlr` replaced by `swpl`).

Threads: MP's `mpWriter` (thread `0`, flag `f1`), the `relaySwpl` (thread
`1`, `EnvG/RelaySwplSpec.lean`), MP's `mpReader` text on `f2` (thread `2`,
run on `EnvGT`). **`mp_relay3_swpl_envG`**: at every reachable final
configuration the reader's `W4` is `43` and the data word's final value is
`43` — the conclusion of the relay proof's `mp_relay3_envG`.

Reused unchanged from the relay proof: the parameters (`relayParams`, `RelayLocs`),
the initial ghost and resources (`relayGhost`, `relayRes`) and their erasure
(`erase_relayInit`), the postcondition `YPost` and the final argument
`relay_final`, the writer (`relayRuleW`, `invYW_init`, `relayRuleW_noFault`)
and the reader (`relay_npSafeD`, `invD_init`, `relayRuleR_noFault`).

New, for the relay only:
- `StartYS`: `StartY` for the text `relaySwpl`.
- The relay's rule: **`ThreadRuleRXGS.ofSafelyEnvGTRC`** (the claim-conditional extension's
  claim-conditional environment with taking loads, `EnvG/RmwGhostTake.lean`)
  from `relaySwpl_envGTC`, with `Phase1TreeR` (`dirs_phase1R`: the release
  swap is a release-kind RMW). No `RelRmwGiveOk`, no `Plan.Whole`.
  `relaySwpl_npSafeY` (`npSafeP_of_safelyEnvGTRC`), `invYS_init`
  (`invGTRC_init`).
- **No fault**, per thread: `relaySwplRuleY_noFault`
  (`noFaultRule_ofSafelyEnvGTRC_struct`, unconditional in promises), with
  the relay proof's `relayRuleW_noFault` and `relayRuleR_noFault`. Adequacy does not
  consume them.
- **Purity**: `final_of_relPureSafelyS`, with `mpWriter_relPure`,
  `relaySwpl_relPure` and `mpReader_relPure`.
-/
import Kraken.Promising.SLR.EnvG.RelaySwplVCGen
import Kraken.Promising.SLR.EnvG.RelaySwplRelPure
import Kraken.Promising.SLR.EnvG.RelayPublic

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp

/-! ## The start state -/

section Start

variable [layout : _root_.Layout]

/-- The `swpl` relay at its start (the label `spin`): `X0 = f1`, `X1 = d`,
`X2 = f2`, none of the three words in `dmem`. -/
structure StartYS (f1 f2 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relaySwpl
  decls : s.decls = {}
  endPc : s.endPc = (layout relaySwpl).addrOf 8
  pc : s.st.2 = (layout relaySwpl).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f1
  x1 : s.st.1.regs.X1.toBitVec = d
  x2 : s.st.1.regs.X2.toBitVec = f2
  df1 : Mem.loadInt s.st.1.dmem f1 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none
  df2 : Mem.loadInt s.st.1.dmem f2 4 = none

end Start

/-! ## The relay -/

section Relay

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relaySwpl)]

omit [Executable.ValidLayout (layout relaySwpl)] in
theorem relaySwpl_rmwLive : (layout relaySwpl).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

/-- The relay's text has phase-1 trees with release-kind RMWs. -/
theorem relaySwpl_phase1R : Phase1TreeR Arch.armv8 (layout relaySwpl) :=
  phase1TreeR_of_dirs (by dirs_phase1R relaySwpl)

omit [Executable.ValidLayout (layout relaySwpl)] in
theorem relaySwpl_noFault : DirsNoFault (layout relaySwpl) := by dirs_no_fault' relaySwpl

/-- The relay's postcondition: the end of its text and `RK4` (the counter of
`relaySwpl_envGTC` projected away). -/
abbrev postYS (rp : RP) : MachineState × EStateA → Prop := postOf relaySwpl fun _ σ => ∃ _ : Nat, RK4 rp σ

omit [Executable.ValidLayout (layout relaySwpl)] in
/-- **`hB` for the relay**: it keeps the token `W2`. -/
theorem hB_YS (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postYS rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.Q) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl hW)
  · rw [hp] at hts; cases hts

/-- **The relay's rule** (`ThreadRuleRXGS.ofSafelyEnvGTRC`: taking loads,
claim-conditional RMWs). -/
def relaySwplRuleY (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : ThreadRuleRXGS G₀ Arch.armv8 (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTRC (e := layout relaySwpl) (post := postYS rp) (mpPlan_valid hL)
    relaySwpl_rmwLive relaySwpl_phase1R postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_YS rp tid)

/-- **The relay's no-fault rule** (`NoFaultRuleS` of its rule; unconditional
in promises). -/
theorem relaySwplRuleY_noFault (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    NoFaultRuleS (relaySwplRuleY rp hL tid) :=
  noFaultRule_ofSafelyEnvGTRC_struct _ _ _ _ _ _ relaySwpl_noFault

/-- **`NPSafeP` for the relay** from its invariant (`EnvGTC`). -/
theorem relaySwpl_npSafeY (rp : RP) (hL : MpLocs rp.Q) (n m : Nat) {cl : Prop} {c : Config isa} {r : Res}
    {g : Ghost}
    (h : InvGR (I := isa) 1 (mpPlan rp.Q)
      (QA64TC Arch.armv8 1 (mpPlan rp.Q) (layout relaySwpl) ((layout relaySwpl).addrOf relaySwpl.length)
        (postYS rp)) cl c r g) :
    NPSafeP (model isa) Arch.armv8 (YPost rp) 1 G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  npSafeP_of_safelyEnvGTRC (mpPlan_valid hL) relaySwpl_rmwLive relaySwpl_phase1R postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_YS rp 1) n m h

end Relay

/-! ## The relay's initial invariant -/

section Inv

variable [layout : _root_.Layout] {f1 f2 d : BitVec 64} {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The relay's initial invariant** (thread `1`): `RK1` at `σInit`. -/
theorem invYS_init [Executable.ValidLayout (layout relaySwpl)] (hL : RelayLocs f1 f2 d)
    (hY : StartYS f1 f2 d sY) :
    InvGR (I := isa) 1 (mpPlan (relayParams f1 f2 d).Q)
      (QA64TC Arch.armv8 1 (mpPlan (relayParams f1 f2 d).Q) (layout relaySwpl)
        ((layout relaySwpl).addrOf relaySwpl.length) (postYS (relayParams f1 f2 d)))
      True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout relaySwpl⟩
  refine invGTRC_init (s := sY) rfl rfl (qa64TC_of_partialTripleEnv (relaySwpl_envGTC _ hL.Q 1).uncount rfl hY.exe
    hY.decls hY.endPc hY.pc ⟨0, ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
      ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, relayThreadRes]
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

end Inv

/-! ## `NPSafeP`, purity and the theorem -/

/-- **The `NPSafeP` side**: the writer through its `ThreadRuleRX`
(`NPSafe.toP`), the relay through `EnvGTC`, the reader through the take
route. -/
theorem relaySwpl_npSafe (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relaySwpl)] [Executable.ValidLayout (lR mpReader)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f1 d sW) (hY : StartYS (layout := lY) f1 f2 d sY)
    (hR : StartR (layout := lR) f2 d sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (YPost (relayParams f1 f2 d)) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) tid)
      (relayGhost (relayParams f1 f2 d)) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleW (layout := lW) _ hL.P 0) n m _ _ _ _ (invYW_init (layout := lW) hL hW))
  | 1, _ =>
    exact relaySwpl_npSafeY (layout := lY) _ hL.Q n m (invYS_init (layout := lY) hL hY)
  | 2, _ =>
    exact relay_npSafeD (layout := lR) _ n m (invD_init (layout := lR) hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

/-- The threads' purity specifications: the writer (layout `lW`) at thread
`0`, the `swpl` relay (layout `lY`) at thread `1`, the reader (layout `lR`)
elsewhere. -/
def relaySwplPureSpec (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relaySwpl)] [Executable.ValidLayout (lR mpReader)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := lW) mpWriter fun _ _ => True
  | 1 => RelPureSpec.ofProgram (layout := lY) relaySwpl fun _ _ => ∃ _ : Nat, True
  | _ + 2 => RelPureSpec.ofProgram (layout := lR) mpReader fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states.** -/
theorem relaySwplPureSpec_init (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relaySwpl)] [Executable.ValidLayout (lR mpReader)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} (hW : StartW (layout := lW) f1 d sW)
    (hY : StartYS (layout := lY) f1 f2 d sY) (hR : StartR (layout := lR) f2 d sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s →
      (relaySwplPureSpec lW lY lR (relayGhost (relayParams f1 f2 d)).rel tid).Holds s := by
  intro tid s hs
  match tid, hs with
  | 0, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hdf, hdd⟩ := hW
    letI : CodeEnv := ⟨lW mpWriter⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lW)
      (mpWriter_relPure (layout := lW) _ f1 d (relayGhost_rel_Dt hL)).partial rfl he hds hend hpc ⟨hx0, hx1, hdf, hdd⟩
  | 1, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hx2, hdf, hdd, hdg⟩ := hY
    letI : CodeEnv := ⟨lY relaySwpl⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lY)
      (relaySwpl_relPure (layout := lY) _ f1 d f2 (relayGhost_rel_Dt hL)).uncount
      rfl he hds hend hpc ⟨0, hx0, hx1, hx2, hdf, hdd, hdg⟩
  | 2, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, -, hdf, -⟩ := hR
    letI : CodeEnv := ⟨lR mpReader⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lR) (mpReader_relPure (layout := lR) _ f2).uncount rfl
      he hds hend hpc ⟨0, hx0, hdf⟩
  | _ + 3, hs => cases hs

/-- **A three-thread ownership relay through a release-only swap, for AArch64
under `Arch.armv8`** (`mp_relay3_swpl.kl`): MP's writer `mpWriter` (thread
`0`, layout `lW`, `X0 = f1`, `X1 = d`), the `relaySwpl` (thread `1`, layout
`lY`, `X0 = f1`, `X1 = d`, `X2 = f2`) and MP's reader `mpReader` (thread `2`,
layout `lR`, `X0 = f2`, `X1 = d`), started from an initial memory with both
flags at `0`: at every reachable final configuration the reader's `W4` is
`43` and the data word's final value is `43`. The relay takes the data at its
acquire load of `f1`, writes it and releases it with `swpl f2` (a
release-only RMW giving the data away: `EnvGTC`,
`ThreadRuleRXGS.ofSafelyEnvGTRC`); the reader takes it at its acquire load of
`f2`. Statement shape and conclusion as `mp_relay3_envG`. -/
theorem mp_relay3_swpl_envG {fuel : Nat} (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relaySwpl)] [Executable.ValidLayout (lR mpReader)] (f1 f2 d : BitVec 64)
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f1 d sW) (hY : StartYS (layout := lY) f1 f2 d sY)
    (hR : StartR (layout := lR) f2 d sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := YPost (relayParams f1 f2 d))
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_relayInit hL _ hF1 hF2) initGhost_pend
    (relaySwplPureSpec lW lY lR _) (relaySwplPureSpec_init lW lY lR hL hW hY hR)
    (relaySwpl_npSafe lW lY lR hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_swpl_envG
#print axioms Kraken.Promising.SLR.EnvG.Relay.relaySwplRuleY_noFault
