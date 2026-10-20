/-
Part 8: **the two-thread Treiber stack
`treiber2_nodes.kl`, end to end** (on the adjacency environment `EnvGCAdj`):
`treiber2_nodes_envG`, the `.kl`'s property
`(0:X10=n1 ∧ 1:X10=n2) ∨ (0:X10=n2 ∧ 1:X10=n1)` at every final configuration
reachable under `Arch.armv8`, for all layouts.

- **Parameters** (`tP2`): `top = ⟨t, 8⟩`, node `w` at `n0`/`n1` (link
  `[n + 8]`, 8 bytes), no data-word constraint; `TLocs` from
  `t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`, `n0 ≠ 0`, `n1 ≠ 0` (`tLocs_tP2`).
- **Shared postcondition** (`TB2`): some `w < 2` with thread `w` done
  (`DoneR`, `EnvG/Treiber2Final.lean`) on the resource. Thread `w` reaches
  `Dn` (`worker_envGCAdj`); its anchor's facts lift to the final memory
  (`DonePop.mono`, `DoneCbz.mono`) and `prom = []` makes the resource the
  thread's (`hB_w`).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdj` from `worker_envGCAdj`
  (`EnvG/Treiber2VCGen.lean`), with `Phase1TreeF`; per-thread no-fault by
  `noFaultRuleF_ofSafelyEnvGFCAdj_struct` (`DirsNoFault`), unconditional in
  the threads' promises (`wRule_noFault`).
- **Start**: `invGFCAdj_init` at `σInit` with `tRes`/`ghost₀`
  (`EnvG/Treiber2Ghost.lean`), `QA64CAdj` by `qa64CAdj_of_partialTripleEnv`
  (`EnvG/AdjVCGenA64.lean`, an instance of the generic
  `safely_start_of_partialTripleEnv`); `Pu` at the start
  (`pu_init`) needs `top` initially `0`.
- **Assembly**: `final_of_relPureSafelyF` (`EnvG/A64RmwFailFinal.lean`),
  purity `treiber2PureSpec_init` (`EnvG/Treiber2RelPure.lean`), initial
  erasure `erase_init`. At the final configuration both threads give
  `DoneR` on their resources: two resources with the same acquire id `w` of
  `top` contradict validity (`acq_pair_false`), so the ids are `0` and `1`,
  and `final_values` gives the property.
-/
import Kraken.Promising.SLR.EnvG.Treiber2VCGen
import Kraken.Promising.SLR.EnvG.Treiber2RelPure
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal
import Kraken.Promising.SLR.EnvG.AdjVCGenA64

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-! ## Parameters and the shared postcondition -/

/-- The parameters of `treiber2_nodes.kl` at `top = t`, nodes `n0` (thread
`0`) and `n1` (thread `1`), no data-word constraint. -/
def tP2 (t n0 n1 : BitVec 64) : Params := ⟨t, fun w => if w = 0 then n0 else n1, fun _ _ => True⟩

theorem tLocs_tP2 {t n0 n1 : BitVec 64} (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0)
    (hn1 : n1 ≠ 0) : TLocs (tP2 t n0 n1) where
  top_nd w hw := by
    rcases w with _ | _ | w
    · exact ht0
    · exact ht1
    · omega
  n_ne := hn
  n_nz w hw := by
    rcases w with _ | _ | w
    · exact hn0
    · exact hn1
    · omega

/-- Thread `w` is done on the resource `r`: its `X10` and `DoneR`. -/
def FF (P : Params) (w : Nat) (c : Config isa) (r : Res) : Prop :=
  ∃ th, c.threads[w]? = some th ∧ DoneR P w c.mem r th.st.st.1.regs.X10.toBitVec

/-- **The shared postcondition**: some thread done on the resource. -/
def TB2 (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop := ∃ w, w < 2 ∧ FF P w c r

/-- **The `.kl`'s property**: the threads popped the two nodes. -/
def Treiber2Final (n0 n1 : BitVec 64) (c : Config isa) : Prop :=
  ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
    ((th0.st.st.1.regs.X10.toBitVec = n0 ∧ th1.st.st.1.regs.X10.toBitVec = n1) ∨
      (th0.st.st.1.regs.X10.toBitVec = n1 ∧ th1.st.st.1.regs.X10.toBitVec = n0))

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2Worker)]

/-- The worker's postcondition: the end of its text and `Dn`. -/
abbrev postW (P : Params) (w : Nat) : MachineState × EStateA → Prop :=
  postOf treiber2Worker fun s σ => ∃ _ : Nat, Dn P w s.regs.X10.toBitVec σ

omit [Executable.ValidLayout (layout treiber2Worker)] in
/-- **`hB` for thread `w`**: `Dn` at the anchor gives `DoneR` at the
configuration (the anchor's memory is a prefix; with no promise the resource
is the thread's). -/
theorem hB_w (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postW P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2 P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePop.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **Thread `w`'s rule**. -/
noncomputable def wRule (P : Params) (w : Nat) (hw : w < 2) : ThreadRuleRXF (I := isa) Arch.armv8 (TB2 P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postW P w) (plan_valid P w) treiber2Worker_rmwLive
    treiber2Worker_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_w P hw)

/-- **Thread `w`'s rule excludes faults** (unconditional in promises). -/
theorem wRule_noFault (P : Params) (w : Nat) (hw : w < 2) : NoFaultRuleF (wRule P w hw) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ treiber2Worker_noFault

end Rule

/-! ## The start -/

/-- **`Pu` at the start** (`top` initially `0`, every data word allowed). -/
theorem pu_init (P : Params) (hL : TLocs P) {w : Nat} (hw : w < 2) (hD : ∀ d, P.D w d) (c : Config isa)
    (hT0 : c.mem.initVal P.top = 0) : Pu P w (σInit c (thrRes c.mem P w) (ghost₀ P)) := by
  have htn := hL.top_nd' hw
  have htd := top_dd P w
  have htp := top_pt P w
  have hq : ∀ x, ((σInit c (thrRes c.mem P w) (ghost₀ P)).r.wr x).q = frac P w x := fun _ => rfl
  have hX : ∀ x p, ((σInit c (thrRes c.mem P w) (ghost₀ P)).r.wr x).X p ↔
      0 < frac P w x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  refine ⟨⟨ghost₀_gw P, ?_, ?_, hT0, ?_⟩, ?_, ?_, ?_, ⟨?_, c.mem.initVal (P.dd w), 0, ?_, ?_, Nat.zero_le _, hD _⟩,
    ?_⟩
  · rw [hq]; simp only [frac, ↓reduceIte]; grind
  · show 1 ≤ (if P.top = P.top ∧ w = w then 1 else 0); simp
  · intro f hf; simp [σInit, Views.getFwd] at hf
  · rintro ⟨p, hp, hne⟩
    exact hne (by rw [((hX _ _).mp hp).2])
  · rw [hq]; simp [frac, Ne.symm htn]
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.zero_le _
  · rw [hq]; simp [frac, Ne.symm htd]
  · rw [hX]; refine ⟨?_, rfl⟩; simp [frac, Ne.symm htd]; try grind
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.le_refl _
  · rw [hq]; simp [frac, Ne.symm htp]

section Start

variable [layout : _root_.Layout] {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant**. -/
theorem invW_init [Executable.ValidLayout (layout treiber2Worker)] {P : Params} (hL : TLocs P) {w : Nat}
    (hw : w < 2) (hD : ∀ d, P.D w d) {s : isa.State} (hs : [s0, s1][w]? = some s) (hS : StartW P.t (P.n w) s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRule P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀ P) := by
  letI : CodeEnv := ⟨layout treiber2Worker⟩
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  exact invGFCAdj_init hs rfl (qa64CAdj_of_partialTripleEnv (worker_envGCAdj P w hL hw).uncount rfl hS.exe
    hS.decls hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, pu_init P hL hw hD _ hT0⟩)

end Start

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for `treiber2_nodes`**: both threads
at the initial configuration, through their rules. -/
theorem treiber2_npSafeF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2Worker)]
    [Executable.ValidLayout (l1 treiber2Worker)] {t n0 n1 : BitVec 64} (hL : TLocs (tP2 t n0 n1))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartW (layout := l0) t n0 s0)
    (h1 : StartW (layout := l1) t n1 s1) (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2 (tP2 t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tP2 t n0 n1) tid)
      (ghost₀ (tP2 t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invW_init (layout := l0) hL (by decide) (fun _ => trivial) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invW_init (layout := l1) hL (by decide) (fun _ => trivial) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- Two thread resources with the same acquire id contradict erasure. -/
theorem acq_pair_false {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa} (E : Erase rF g T c)
    {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j) {x : Loc} {ι : PredId}
    (h1 : 1 ≤ (rF i).acq x ι) (h2 : 1 ≤ (rF j).acq x ι) : False :=
  TreiberCommon.acq_pair_false E hi hj hij h1 h2

/-- **The two-thread Treiber stack `treiber2_nodes.kl` for AArch64 under
`Arch.armv8`, on `EnvGCAdj`**: for all layouts `l0`, `l1` of the worker, all
addresses `t` of `top` (8 bytes) and `n0`, `n1` of the nodes (links
`[n0 + 8]`, `[n1 + 8]`, 8 bytes) with `t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`,
`n0 ≠ 0`, `n1 ≠ 0`: if thread `0` starts the worker with `x0 = t`, `x1 = n0`
and thread `1` with `x0 = t`, `x1 = n1` (`StartW`), and `top` is initially
`0`, then every final configuration reachable under `Arch.armv8` has
`(0:X10 = n0 ∧ 1:X10 = n1) ∨ (0:X10 = n1 ∧ 1:X10 = n0)` (the `.kl`'s
`forall`, with `n1`, `n2` of the `.kl` as `n0`, `n1`).

Only the addresses' `Loc`s are distinguished (`t ≠ n + 8`): the model's
mixed-size gap as in `treiber_pp_envG`. -/
theorem treiber2_nodes_envG {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2Worker)]
    [Executable.ValidLayout (l1 treiber2Worker)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartW (layout := l0) t n0 s0) (h1 : StartW (layout := l1) t n1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th0 th1, cfg.threads[0]? = some th0 ∧ cfg.threads[1]? = some th1 ∧
      ((th0.st.st.1.regs.X10.toBitVec = n0 ∧ th1.st.st.1.regs.X10.toBitVec = n1) ∨
        (th0.st.st.1.regs.X10.toBitVec = n1 ∧ th1.st.st.1.regs.X10.toBitVec = n0)) := by
  have hL := tLocs_tP2 ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB2 (tP2 t n0 n1)) (Φ := Treiber2Final n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiber2PureSpec l0 l1 _)
    (treiber2PureSpec_init l0 l1 (fun v => ?_) (fun v => ?_) h0 h1) (treiber2_npSafeF l0 l1 hL h0 h1 hT0) hc hf
    fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ (tP2 t n0 n1)).rel ((tP2 t n0 n1).nd 0)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tP2 t n0 n1)).rel ((tP2 t n0 n1).nd 1)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw (tP2 t n0 n1)).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · exact ⟨th, th', hth, hth', final_values E' hW hL hno hi0 hi1 hd0 hd1⟩
    · omega
  · rcases w1 with _ | _ | w1
    · have := final_values E' hW hL hno hi1 hi0 hd1 hd0
      exact ⟨th', th, hth', hth, this⟩
    · exact absurd rfl hww
    · omega
  · omega

end Kraken.Promising.SLR.EnvG.Treiber2
