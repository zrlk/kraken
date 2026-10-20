/-
Part 7: **the two-thread Treiber stack
`treiber2_arm.kl` (Arm-minimal annotations), end to end** (on the adjacency
environment `EnvGCAdj`): `treiber2_arm_envG`, the `.kl`'s property
`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨ (0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`
at every final configuration reachable under `Arch.armv8`, for all layouts.

The assembly of the worker `treiber2ArmWorker` (`EnvG/Treiber2ArmVCGen.lean`)
with the ghost-free `top` (`EnvG/Treiber2ArmGhost.lean`), as
`EnvG/Treiber2DataPublic.lean`:

- **Parameters**: `Treiber2.tPD` (node `w`'s data word `w + 1`);
- **shared postcondition** (`TB2A`): some `w < 2` with thread `w` done with
  its data read (`DoneRA`, `EnvG/Treiber2ArmFinal.lean`); `hB` from `DnDA`
  (`DoneRA.mono`);
- **start**: `Pu0A` at `σInit` with `ghost₀A` (`pu0A_init`: half of `top`,
  its only write the initial one, no forwarding);
- **final**: `acq_pair_false` (ids `0` and `1`) and `final_values_dataA`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2DataPublic
import Kraken.Promising.SLR.EnvG.Treiber2ArmRelPure

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)
open Kraken.Promising.SLR.EnvG.Treiber2 (Params TLocs tPD tLocs_tPD frac thrRes tRes top_dd acq_pair_false
  x32_tPD Treiber2DFinal)

/-! ## The shared postcondition -/

/-- Thread `w` is done on the resource `r`: its `X10`, `X11` and `DoneRA`. -/
def FFA (P : Params) (w : Nat) (c : Config isa) (r : Res) : Prop :=
  ∃ th, c.threads[w]? = some th ∧
    DoneRA P w c.mem r th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec

/-- **The shared postcondition**: some thread done on the resource. -/
def TB2A (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop := ∃ w, w < 2 ∧ FFA P w c r

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ArmWorker)]

/-- The worker's postcondition: the end of its text and `DnDA`. -/
abbrev postWA (P : Params) (w : Nat) : MachineState × EStateA → Prop :=
  postOf treiber2ArmWorker fun s σ => ∃ _ : Nat, DnDA P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ

omit [Executable.ValidLayout (layout treiber2ArmWorker)] in
/-- **`hB` for thread `w`**: `DnDA` at the anchor gives `DoneRA` at the
configuration. -/
theorem hB_wA (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postWA P w (t.st.st, σ) → t.prom = [] → EnvRel w planA σ c t r g cl → cl → TB2A P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, -, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hd.mono hpre⟩
  · rw [hp] at hts; cases hts

/-- **Thread `w`'s rule**. -/
noncomputable def wRuleA (P : Params) (w : Nat) (hw : w < 2) : ThreadRuleRXF (I := isa) Arch.armv8 (TB2A P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postWA P w) planA_valid treiber2ArmWorker_rmwLive
    treiber2ArmWorker_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_wA P hw)

/-- **Thread `w`'s rule excludes faults** (unconditional in promises). -/
theorem wRuleA_noFault (P : Params) (w : Nat) (hw : w < 2) : NoFaultRuleF (wRuleA P w hw) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ treiber2ArmWorker_noFault

end Rule

/-! ## The start -/

/-- **`Pu0A` at the start** (`top` initially `0`). -/
theorem pu0A_init (P : Params) (hL : TLocs P) {w : Nat} (hw : w < 2) (c : Config isa)
    (hT0 : c.mem.initVal P.top = 0) : Pu0A P w (σInit c (thrRes c.mem P w) (ghost₀A P)) := by
  have htn := hL.top_nd' hw
  have htd := top_dd P w
  have hq : ∀ x, ((σInit c (thrRes c.mem P w) (ghost₀A P)).r.wr x).q = frac P w x := fun _ => rfl
  have hX : ∀ x p, ((σInit c (thrRes c.mem P w) (ghost₀A P)).r.wr x).X p ↔
      0 < frac P w x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  refine ⟨⟨ghost₀A_gw P, ?_, ?_, hT0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq]; simp only [frac, ↓reduceIte]
  · show 1 ≤ (if P.top = P.top ∧ w = w then 1 else 0); simp
  · intro f hf; simp [σInit, Views.getFwd] at hf
  · intro p hp
    rw [((hX _ _).mp hp).2]
  · rw [hq]; simp [frac, Ne.symm htn]
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.zero_le _
  · rw [hq]; simp [frac, Ne.symm htd]
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.zero_le _

section Start

variable [layout : _root_.Layout] {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant** (`w9 = d9`, every data word with low
32 bits `d9` allowed). -/
theorem invWA_init [Executable.ValidLayout (layout treiber2ArmWorker)] {P : Params} (hL : TLocs P) {w : Nat}
    (hw : w < 2) {d9 : BitVec 32} (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : StartWA P.t (P.n w) d9 s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRuleA P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀A P) := by
  letI : CodeEnv := ⟨layout treiber2ArmWorker⟩
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  exact invGFCAdj_init hs rfl (qa64CAdj_of_partialTripleEnv (workerA_envGCAdj P w hL hw d9 hD).uncount rfl
    hS.exe hS.decls hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, hS.x9, pu0A_init P hL hw _ hT0⟩)

end Start

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for `treiber2_arm`**: both threads at
the initial configuration (`w9 = 1`, `2`), through their rules. -/
theorem treiber2A_npSafeF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2ArmWorker)]
    [Executable.ValidLayout (l1 treiber2ArmWorker)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartWA (layout := l0) t n0 1 s0)
    (h1 : StartWA (layout := l1) t n1 2 s1) (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2A (tPD t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
      (ghost₀A (tPD t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWA_init (layout := l0) hL (by decide) (fun _ h => h) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWA_init (layout := l1) hL (by decide) (fun _ h => h) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-thread Treiber stack `treiber2_arm.kl` (push `ldr`/`casl`, pop
`ldar`/`cas`) for AArch64 under `Arch.armv8`, on `EnvGCAdj`**: for all
layouts `l0`, `l1` of the worker, all addresses `t` of `top` (8 bytes) and
`n0`, `n1` of the nodes (data words `[n0]`, `[n1]`, 4 bytes; links
`[n0 + 8]`, `[n1 + 8]`, 8 bytes) with `t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`,
`n0 ≠ 0`, `n1 ≠ 0`: if thread `0` starts the worker with `x0 = t`, `x1 = n0`,
`w9 = 1` and thread `1` with `x0 = t`, `x1 = n1`, `w9 = 2` (`StartWA`), and
`top` is initially `0`, then every final configuration reachable under
`Arch.armv8` has `(0:X10 = n0 ∧ 0:X11 = 1 ∧ 1:X10 = n1 ∧ 1:X11 = 2) ∨
(0:X10 = n1 ∧ 0:X11 = 2 ∧ 1:X10 = n0 ∧ 1:X11 = 1)` (the `.kl`'s `forall`,
with `n1`, `n2` of the `.kl` as `n0`, `n1`).

Only the addresses' `Loc`s are distinguished, as in `treiber2_envG`. -/
theorem treiber2_arm_envG {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2ArmWorker)]
    [Executable.ValidLayout (l1 treiber2ArmWorker)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWA (layout := l0) t n0 1 s0) (h1 : StartWA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB2A (tPD t n0 n1)) (Φ := Treiber2DFinal n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_initA hL _) (ghost₀A_pend _) (treiber2ArmPureSpec l0 l1 _)
    (treiber2ArmPureSpec_init l0 l1 (fun v => Pred.emp_pure v) (fun v => Pred.emp_pure v)
      (fun v => Pred.emp_pure v) (fun v => Pred.emp_pure v) (fun v => Pred.emp_pure v) h0 h1)
    (treiber2A_npSafeF l0 l1 hL h0 h1 hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hall : ∀ k, k < cfg.threads.size → k = 0 ∨ k = 1 := by
    intro k hk; rw [hsize] at hk; simp at hk; omega
  have hall' : ∀ k, k < cfg.threads.size → k = 1 ∨ k = 0 := fun k hk => (hall k hk).symm
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · refine ⟨th, th', hth, hth', ?_⟩
      rcases final_values_dataA E' hL hno hi0 hi1 (by decide) hall hd0 hd1 with
        ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · omega
  · rcases w1 with _ | _ | w1
    · refine ⟨th', th, hth', hth, ?_⟩
      rcases final_values_dataA E' hL hno hi1 hi0 (by decide) hall' hd1 hd0 with
        ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · exact absurd rfl hww
    · omega
  · omega

end Kraken.Promising.SLR.EnvG.Treiber2Arm
