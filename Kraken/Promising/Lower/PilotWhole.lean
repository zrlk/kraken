/-
**The whole program on the Promising model.**

`pilot_promising`: two threads running the hand-lowered `pilot` (`main` calls
`push` and `pop` under the draft calling convention), each from a start state of
the runtime (`StartP`: `x30` the end of the text, `&top` in `x21`, the bump
arena `x27`/`x28`, the payload in `w9`); every final configuration reachable
under `Arch.armv8` has each thread's popped node in `x10` and its payload in
`x11`: the two nodes with payloads `1`, `2`, in either assignment (in
particular every popped node was pushed, and no thread found the stack empty).

The assembly is `treiber2_envG` (`EnvG/Treiber2DataPublic.lean`) with the
inlined worker replaced by `pilot`: the thread rule from `main_partialTripleEnv`
(`Lower/PilotMain.lean`), the purity specification from `main_pure`
(`Lower/PilotPure.lean`); the parameters `tPD`, the shared postcondition
`TB2D`, `pu0_init` and the final-configuration argument are reused unchanged.
-/
import Kraken.Promising.Lower.PilotPure
import Kraken.Promising.SLR.EnvG.Treiber2DataPublic
import Kraken.Promising.SLR.EnvG.ConcreteCommon

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-! ## The rule -/

section Rule

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot)]

/-- `pilot`'s postcondition: the end of its text and `DnD`. -/
abbrev postP (P : Params) (w : Nat) : MachineState × EStateA → Prop :=
  postOf pilot fun s σ => ∃ _ : Nat, DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ

omit [Executable.ValidLayout (layout pilot)] in
/-- **`hB` for thread `w`** (`hB_wD` for `pilot`). -/
theorem hB_P (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postP P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2D P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePopD.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **Thread `w`'s rule**. -/
noncomputable def ruleP (P : Params) (w : Nat) (hw : w < 2) : ThreadRuleRXF (I := isa) Arch.armv8 (TB2D P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postP P w) (plan_valid P w) pilot_rmwLive
    pilot_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_P P hw)

/-- **Thread `w`'s rule excludes faults**. -/
theorem ruleP_noFault (P : Params) (w : Nat) (hw : w < 2) : NoFaultRuleF (ruleP P w hw) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ pilot_noFault

end Rule

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- **A thread's start state for `pilot`** (the runtime's side of the
draft calling convention): at the start of the text, returning to its end; `&top` in the
callee-saved `x21`; the bump pointer `x27` at the thread's node `n` with room
for one 16-byte node below the limit `x28`; the payload `d` in `w9`; no
private copy of any 8- or 4-byte word. -/
structure StartP (t n : BitVec 64) (d : BitVec 32) (s : isa.State) : Prop where
  exe : s.exe = layout pilot
  decls : s.decls = {}
  endPc : s.endPc = (layout pilot).addrOf pilot.length
  pc : s.st.2 = (layout pilot).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout pilot).addrOf pilot.length
  x21 : s.st.1.regs.X21.toBitVec = t
  x27 : s.st.1.regs.X27.toBitVec = n
  x28 : s.st.1.regs.X27.toBitVec + 16 ≤ s.st.1.regs.X28.toBitVec
  x9 : s.st.1.regs.X9.toBitVec.setWidth 32 = d
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **Thread `w`'s initial invariant**. -/
theorem invP_init [Executable.ValidLayout (layout pilot)] {P : Params} (hL : TLocs P) {w : Nat}
    (hw : w < 2) {d9 : BitVec 32} (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) {s : isa.State}
    (hs : [s0, s1][w]? = some s) (hS : StartP P.t (P.n w) d9 s)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    (ruleP P w hw).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w)
      (ghost₀ P) := by
  letI : CodeEnv := ⟨layout pilot⟩
  have htr : tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w := by
    rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  rw [htr]
  exact invGFCAdj_init hs rfl (qa64CAdj_of_partialTripleEnv (main_partialTripleEnv P w hL hw d9 hD).uncount rfl
    hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x30, hS.x21, hS.x27, hS.x28, hS.x9, ⟨hS.d8, hS.d4⟩, pu0_init P hL hw _ hT0⟩)

end Start

/-- The threads' purity specifications: `pilot` at layout `l0` at thread `0`,
at layout `l1` elsewhere. -/
def pilotPureSpec (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := l0) pilot fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := l1) pilot fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states**. -/
theorem pilotPureSpec_init (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] {rel : Loc → Pred} {t n0 n1 : BitVec 64} {d0 d1 : BitVec 32}
    (hd0 : ∀ v : Val, Pred.Pure (rel ⟨n0, 4⟩) v) (hd1 : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hn0 : ∀ v : Val, Pred.Pure (rel ⟨n0 + 8, 8⟩) v) (hn1 : ∀ v : Val, Pred.Pure (rel ⟨n1 + 8, 8⟩) v)
    {s0 s1 : isa.State} (h0 : StartP (layout := l0) t n0 d0 s0) (h1 : StartP (layout := l1) t n1 d1 s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (pilotPureSpec l0 l1 rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, -, hd8, hd4⟩ := h0
    letI : CodeEnv := ⟨l0 pilot⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l0)
      (main_pure (layout := l0) rel t n0 hd0 hn0).uncount rfl he hds hend hpc
      ⟨0, h30, h21, h27, h28, hd8, hd4⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, -, hd8, hd4⟩ := h1
    letI : CodeEnv := ⟨l1 pilot⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l1)
      (main_pure (layout := l1) rel t n1 hd1 hn1).uncount rfl he hds hend hpc
      ⟨0, h30, h21, h27, h28, hd8, hd4⟩
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for `pilot`**. -/
theorem pilot_npSafeF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartP (layout := l0) t n0 1 s0)
    (h1 : StartP (layout := l1) t n1 2 s1) (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (TB2D (tPD t n0 n1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
      (ghost₀ (tPD t n0 n1)) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invP_init (layout := l0) hL (by decide) (fun _ h => h) rfl h0 hT0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _
      (invP_init (layout := l1) hL (by decide) (fun _ h => h) rfl h1 hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The hand-lowered two-thread Treiber client on the Promising model**
(AArch64, `Arch.armv8`, the `isa` instruction set): for all layouts `l0`,
`l1` of `pilot`, all addresses `t` of `top` and `n0`, `n1` of the two bump-
allocated nodes (payload `[n]`, 4 bytes; link `[n + 8]`, 8 bytes) with
`t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`, `n0 ≠ 0`, `n1 ≠ 0`: if thread `0`
starts `pilot` with its arena at `n0` and payload `1`, thread `1` with its
arena at `n1` and payload `2` (`StartP`), and `top` is initially `0`, then
every final configuration reachable under `Arch.armv8` has
`(0:X10 = n0 ∧ 0:X11 = 1 ∧ 1:X10 = n1 ∧ 1:X11 = 2) ∨
(0:X10 = n1 ∧ 0:X11 = 2 ∧ 1:X10 = n0 ∧ 1:X11 = 1)`. A final configuration has
no faulted thread, so no fault is reachable in a completed run. -/
theorem pilot_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 pilot)]
    [Executable.ValidLayout (l1 pilot)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := TB2D (tPD t n0 n1)) (Φ := Treiber2DFinal n0 n1)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (pilotPureSpec l0 l1 _)
    (pilotPureSpec_init l0 l1 (fun v => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) h0 h1)
    (pilot_npSafeF l0 l1 hL h0 h1 hT0) hc hf fun rF' g' E' hle hsize hB => ?_
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


/-! ## The concrete instance (`PilotProg`'s explorer configuration) -/

section
attribute [local instance] pLayout

theorem thread_start (base v : UInt64) (n : BitVec 64) (d : BitVec 32) (hn : base.toBitVec = n)
    (hlim : base.toBitVec + 16 ≤ (base + 0x100).toBitVec) (hd : v.toBitVec.setWidth 32 = d) :
    StartP 0x1000 n d (thread base v) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hn, hlim, hd, ?_, ?_⟩ <;> try (simp only [thread]; decide)
  all_goals
    simp [thread, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **Non-vacuity**: `pilot_promising` at the explorer's configuration
(`pilotRun`, `Lower/PilotProg.lean`): `top` at `0x1000`, arenas at `0x2000`
and `0x3000`, payloads `1` and `2`. -/
theorem pilot_promising_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [thread 0x2000 1, thread 0x3000 2] initMem) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 c :=
  pilot_promising pLayout pLayout 0x1000 0x2000 0x3000 (by decide) (by decide) (by decide) (by decide)
    (by decide) (thread_start _ _ _ _ rfl (by decide) (by decide))
    (thread_start _ _ _ _ rfl (by decide) (by decide)) (by simp only [Config.init_mem]; decide) hc hf

end Kraken.Promising.Lower.Pilot
