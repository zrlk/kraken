/-
Part 13: **the two-thread Treiber stack
`treiber2.kl` with its data word, end to end** (on the adjacency environment
`EnvGCAdj`): `treiber2_envG`, the `.kl`'s property
`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨ (0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`
at every final configuration reachable under `Arch.armv8`, for all layouts.

The assembly of `treiber2_nodes_envG` (`EnvG/Treiber2Public.lean`) with the
data worker `treiber2DWorker` (`EnvG/Treiber2DataVCGen.lean`):

- **Parameters** (`tPD`): those of `tP2` with node `w`'s data word
  `[n]` (4 bytes) constrained to `w + 1` (`D w d := d[31:0] = w + 1`);
- **shared postcondition** (`TB2D`): some `w < 2` with thread `w` done with
  its data read (`DoneRD`, `EnvG/Treiber2DataVC.lean`); `hB` from `DnD`
  (`DonePopD.mono`, `DoneCbz.mono`);
- **start**: `Pu0` at `σInit` (`pu0_init`: the data word's only write is the
  initial one);
- **final**: `acq_pair_false` (ids `0` and `1`) and `final_values_data`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2Public
import Kraken.Promising.SLR.EnvG.Treiber2DataRelPure

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Parameters and the shared postcondition -/

/-- The parameters of `treiber2.kl` at `top = t`, nodes `n0` (thread `0`) and
`n1` (thread `1`), node `w`'s data word `w + 1`. -/
def tPD (t n0 n1 : BitVec 64) : Params :=
  ⟨t, fun w => if w = 0 then n0 else n1, fun w d => BitVec.setWidth 32 d = BitVec.ofNat 32 (w + 1)⟩

theorem tLocs_tPD {t n0 n1 : BitVec 64} (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0)
    (hn1 : n1 ≠ 0) : TLocs (tPD t n0 n1) where
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

theorem DonePopD.mono {P : Params} {w : Nat} {m m' : Memory} (h : m.Prefix m') {v x : BitVec 64}
    (hd : DonePopD P w m v x) : DonePopD P w m' v x := by
  obtain ⟨Pw, tr0, hd, tl, u, hr, hx, hw⟩ := hd
  have hle : tr0 ≤ m.last := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h5, _⟩ := hd
    exact read?_le_last h5
  exact ⟨Pw, tr0, hd.mono h, tl, u, read?_mono h hr, hx,
    fun p wm a b hg => hw p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg)⟩

/-- Thread `w` is done on the resource `r`: its `X10`, `X11` and `DoneRD`. -/
def FFD (P : Params) (w : Nat) (c : Config isa) (r : Res) : Prop :=
  ∃ th, c.threads[w]? = some th ∧
    DoneRD P w c.mem r th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec

/-- **The shared postcondition**: some thread done on the resource. -/
def TB2D (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop := ∃ w, w < 2 ∧ FFD P w c r

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2DWorker)]

/-- The data worker's postcondition: the end of its text and `DnD`. -/
abbrev postWD (P : Params) (w : Nat) : MachineState × EStateA → Prop :=
  postOf treiber2DWorker fun s σ => ∃ _ : Nat, DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ

omit [Executable.ValidLayout (layout treiber2DWorker)] in
/-- **`hB` for thread `w`**: `DnD` at the anchor gives `DoneRD` at the
configuration. -/
theorem hB_wD (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postWD P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2D P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePopD.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **Thread `w`'s rule**. -/
noncomputable def wRuleD (P : Params) (w : Nat) (hw : w < 2) : ThreadRuleRXF (I := isa) Arch.armv8 (TB2D P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postWD P w) (plan_valid P w) treiber2DWorker_rmwLive
    treiber2DWorker_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_wD P hw)

/-- **Thread `w`'s rule excludes faults** (unconditional in promises). -/
theorem wRuleD_noFault (P : Params) (w : Nat) (hw : w < 2) : NoFaultRuleF (wRuleD P w hw) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ treiber2DWorker_noFault

end Rule

/-! ## The start -/

/-- **`Pu0` at the start** (`top` initially `0`). -/
theorem pu0_init (P : Params) (hL : TLocs P) {w : Nat} (hw : w < 2) (c : Config isa)
    (hT0 : c.mem.initVal P.top = 0) : Pu0 P w (σInit c (thrRes c.mem P w) (ghost₀ P)) := by
  have htn := hL.top_nd' hw
  have htd := top_dd P w
  have htp := top_pt P w
  have hq : ∀ x, ((σInit c (thrRes c.mem P w) (ghost₀ P)).r.wr x).q = frac P w x := fun _ => rfl
  have hX : ∀ x p, ((σInit c (thrRes c.mem P w) (ghost₀ P)).r.wr x).X p ↔
      0 < frac P w x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  refine ⟨⟨ghost₀_gw P, ?_, ?_, hT0, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq]; simp only [frac, ↓reduceIte]; grind
  · show 1 ≤ (if P.top = P.top ∧ w = w then 1 else 0); simp
  · intro f hf; simp [σInit, Views.getFwd] at hf
  · rintro ⟨p, hp, hne⟩
    exact hne (by rw [((hX _ _).mp hp).2])
  · rw [hq]; simp [frac, Ne.symm htn]
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.zero_le _
  · rw [hq]; simp [frac, Ne.symm htd]
  · intro p hp
    rw [((hX _ _).mp hp).2]; exact Nat.zero_le _
  · rw [hq]; simp [frac, Ne.symm htp]

section Start

variable [layout : _root_.Layout] {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant** (`w9 = d9`, every data word with low
32 bits `d9` allowed). -/
theorem invWD_init [Executable.ValidLayout (layout treiber2DWorker)] {P : Params} (hL : TLocs P) {w : Nat}
    (hw : w < 2) {d9 : BitVec 32} (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : StartWD P.t (P.n w) d9 s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (wRuleD P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀ P) := by
  letI : CodeEnv := ⟨layout treiber2DWorker⟩
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  exact invGFCAdj_init hs rfl (qa64CAdj_of_partialTripleEnv (workerD_envGCAdj P w hL hw d9 hD).uncount rfl
    hS.exe hS.decls hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, hS.x9, pu0_init P hL hw _ hT0⟩)

end Start

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for `treiber2`**: both threads at the
initial configuration (`w9 = 1`, `2`), through their rules. -/
theorem treiber2D_npSafeF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2DWorker)]
    [Executable.ValidLayout (l1 treiber2DWorker)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartWD (layout := l0) t n0 1 s0)
    (h1 : StartWD (layout := l1) t n1 2 s1) (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2D (tPD t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
      (ghost₀ (tPD t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWD_init (layout := l0) hL (by decide) (fun _ h => h) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invWD_init (layout := l1) hL (by decide) (fun _ h => h) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- `X11` from `final_values_data` at `tPD`: node `w`'s data `w + 1`. -/
theorem x32_tPD {t n0 n1 : BitVec 64} {w : Nat} (hw : w < 2) {x : BitVec 64}
    (h : ∃ d, (tPD t n0 n1).D w d ∧ x32 d = x) : x = BitVec.ofNat 64 (w + 1) := by
  obtain ⟨d, hd, rfl⟩ := h
  have hd' : BitVec.setWidth 32 d = BitVec.ofNat 32 (w + 1) := hd
  rw [x32, hd']
  rcases w with _ | _ | w
  · decide
  · decide
  · omega

/-- **The `.kl`'s property**: the threads popped the two nodes with their
data. -/
def Treiber2DFinal (n0 n1 : BitVec 64) (c : Config isa) : Prop :=
  ∃ th0 th1, c.threads[0]? = some th0 ∧ c.threads[1]? = some th1 ∧
    ((th0.st.st.1.regs.X10.toBitVec = n0 ∧ th0.st.st.1.regs.X11.toBitVec = 1 ∧
        th1.st.st.1.regs.X10.toBitVec = n1 ∧ th1.st.st.1.regs.X11.toBitVec = 2) ∨
      (th0.st.st.1.regs.X10.toBitVec = n1 ∧ th0.st.st.1.regs.X11.toBitVec = 2 ∧
        th1.st.st.1.regs.X10.toBitVec = n0 ∧ th1.st.st.1.regs.X11.toBitVec = 1))

/-- **The two-thread Treiber stack `treiber2.kl` for AArch64 under
`Arch.armv8`, on `EnvGCAdj`**: for all layouts `l0`, `l1` of the worker, all
addresses `t` of `top` (8 bytes) and `n0`, `n1` of the nodes (data words
`[n0]`, `[n1]`, 4 bytes; links `[n0 + 8]`, `[n1 + 8]`, 8 bytes) with
`t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`, `n0 ≠ 0`, `n1 ≠ 0`: if thread `0`
starts the worker with `x0 = t`, `x1 = n0`, `w9 = 1` and thread `1` with
`x0 = t`, `x1 = n1`, `w9 = 2` (`StartWD`), and `top` is initially `0`, then
every final configuration reachable under `Arch.armv8` has
`(0:X10 = n0 ∧ 0:X11 = 1 ∧ 1:X10 = n1 ∧ 1:X11 = 2) ∨
(0:X10 = n1 ∧ 0:X11 = 2 ∧ 1:X10 = n0 ∧ 1:X11 = 1)` (the `.kl`'s `forall`,
with `n1`, `n2` of the `.kl` as `n0`, `n1`).

Only the addresses' `Loc`s are distinguished (`t ≠ n + 8`; the data words
`⟨n, 4⟩` differ from `top` and the links by their width): the model's
mixed-size gap as in `treiber_pp_envG`. -/
theorem treiber2_envG {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2DWorker)]
    [Executable.ValidLayout (l1 treiber2DWorker)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWD (layout := l0) t n0 1 s0) (h1 : StartWD (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB2D (tPD t n0 n1)) (Φ := Treiber2DFinal n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (treiber2DPureSpec l0 l1 _)
    (treiber2DPureSpec_init l0 l1 (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) h0 h1)
    (treiber2D_npSafeF l0 l1 hL h0 h1 hT0) hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).dd 0)) v
    rw [ghost₀_rel_ne (Ne.symm (top_dd _ 0))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).dd 1)) v
    rw [ghost₀_rel_ne (Ne.symm (top_dd _ 1))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).nd 0)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost₀ (tPD t n0 n1)).rel ((tPD t n0 n1).nd 1)) v
    rw [ghost₀_rel_ne (Ne.symm (hL.top_nd' (by decide)))]; exact Pred.emp_pure v
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw (tPD t n0 n1)).mono hle
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
      rcases final_values_data E' hW hL hno hi0 hi1 hd0 hd1 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · omega
  · rcases w1 with _ | _ | w1
    · refine ⟨th', th, hth', hth, ?_⟩
      rcases final_values_data E' hW hL hno hi1 hi0 hd1 hd0 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
      · exact .inl ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
      · exact .inr ⟨ha, x32_tPD (by decide) hc, hb, x32_tPD (by decide) hd⟩
    · exact absurd rfl hww
    · omega
  · omega

end Kraken.Promising.SLR.EnvG.Treiber2
