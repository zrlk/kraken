/-
**The per-thread EnvG premise of the x64
bridge for `pilotX`.**

From `main_specX` (`Lower/PilotX64Main.lean`): the thread's start
(`StartPX`), its postcondition `postPX` (the end of the text, `Dn` of the
popped node in `r12`), the per-thread `QX64CAdjV` at `σInitX`
(`qx64CAdjV_pilotX`), the text's end stuck (`pilotX_stuck`), `hB`
(`hB_pX`, the x64 Treiber proof's `hB_wV` with `postPX`), the per-thread premise of
`EnvGValsBridgeX` in its exact shape (`hthr_pX`), the final case split
(`pilotX_final`, from `x64_treiber2_envG_verbatim`), and the assembly
conditional on the open parts (`pilotX_promising_of_bridge_pure`).

**Not here:** the purity judgments `RelPureSpecQX.HoldsV` of `pilotX` (a
second VC pass in `relInvX (SL P) (GV P)`) and the whole-program theorem; both
are in `Lower/PilotX64Whole.lean` (`pilotX_promising`, the statement below
without `hbridge`, via `Vals.envGValsBridgeX_ofPure`). The statement as planned:

```
theorem pilotX_promising_of_envGValsBridgeX {fuel : Nat} (l0 l1 : _root_.Layout)
    [Executable.ValidLayout (l0 pilotX)] [Executable.ValidLayout (l1 pilotX)] {P : Params} (hL : TLocs P)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartPX (layout := l0) P 0 s0) (h1 : StartPX (layout := l1) P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    (hm0 : MemInv (GV P) (Config.init [s0, s1] initMem).mem)
    (hbridge : EnvGValsBridgeX (SL P) (GV P))
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg
```
-/
import Kraken.Promising.Lower.PilotX64Main

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64
open Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.PilotX

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.SLR.EnvG.TreiberCommon (initVal_eq)

variable [layout : _root_.Layout]

/-- The end of `pilotX`'s text (`main`'s return address). -/
abbrev endPX : Int64 := (layout pilotX).addrOf pilotX.length

/-- Thread `w`'s postcondition: the end of the text, the popped node in
`r12` (`Dn`). -/
abbrev postPX (P : Params) (w : Nat) : MachineState × EStateX → Prop :=
  fun x => x.1.2 = endPX ∧ Dn P w (x.1.1.regs.get64 .r12) x.2

theorem postPX_end (P : Params) (w : Nat) : ∀ y, postPX P w y → y.1.2 = endPX := fun _ h => h.1

/-- **No instruction steps at the end of the text** (behind the trailing
`done:`). -/
theorem pilotX_stuck [Executable.ValidLayout (layout pilotX)] (env : SharedEnv) :
    ∀ x R, x.1.2 = endPX → ¬ (layout pilotX).instrStepEnv env x R :=
  not_instrStepEnv_of_end_labels env 1

/-- **Thread `w` at its start**: the text, no declarations, pc at `main`, end
at the end of the text, `rbx = &top`, the arena at node `w` with room for it,
the end address in `main`'s return-address slot, the callees' slot mapped,
the shared layout off `dmem`. -/
structure StartPX (P : Params) (w : Nat) (s : isa.State) : Prop where
  exe : s.exe = layout pilotX
  decls : s.decls = {}
  pc : s.st.2 = (layout pilotX).addrOf 0
  endPc : s.endPc = endPX
  rbx : s.st.1.regs.get64 .rbx = P.t
  r14 : s.st.1.regs.get64 .r14 = P.n w
  r15 : s.st.1.regs.get64 .r14 + 16 ≤ s.st.1.regs.get64 .r15
  ret : RetAt s.st.1 endPX
  slot : (Mem.loadInt s.st.1.dmem (s.st.1.regs.get64 .rsp - 16) 8).isSome = true
  heap : Split (SL P) s.st.1.dmem

/-- **The per-thread `QX64CAdjV`** from `main_specX` (uncounted). -/
theorem qx64CAdjV_pilotX [Executable.ValidLayout (layout pilotX)] (P : Params) (w : Nat) (hL : TLocs P)
    (hw : w < 2) {s : isa.State} (hS : StartPX P w s) {σ : EStateX} (hPu : Pu P w σ) :
    QX64CAdjV Arch.tso w (plan P w) (SL P) (GV P) (layout pilotX) endPX (postPX P w) s σ := by
  letI : CodeEnv := ⟨layout pilotX⟩
  refine ⟨hS.exe, hS.decls, hS.endPc, hS.heap, ?_⟩
  have hst : s.st = (s.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hS.pc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  refine (Program.instrStepEnv_of_partialTripleEnv (main_specX P w hL hw endPX) (g := (σ, 0))
    ⟨hS.rbx, hS.r14, hS.r15, hS.ret, hS.slot, hS.heap, hPu⟩).uncountEnv.mono ?_
  rintro _ ⟨_, ⟨-, ⟨⟩⟩ | ⟨h1, h2⟩⟩
  exact ⟨h1, h2⟩

/-- **`hB` for thread `w`**: `Dn` at the anchor gives `DoneR` at the
configuration (`hB_wV` with `postPX`). -/
theorem hB_pX (P : Params) {w : Nat} (hw : w < 2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPX P w (t.st.st, σ) → t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2X P c r g := by
  rintro c t r g cl σ ⟨_, hcom, hd⟩ hp hrel -
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePop.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

omit layout in
/-- **`EnvGValsBridgeX`'s per-thread premise for `pilotX`**, in its exact
shape, at the two-thread start (thread `w` at layout `l w`). -/
theorem hthr_pX (l : Nat → _root_.Layout) [hv : ∀ w, Executable.ValidLayout (l w pilotX)] {P : Params}
    (hL : TLocs P) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartPX (layout := l 0) P 0 s0) (h1 : StartPX (layout := l 1) P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0) :
    ∀ tid, tid < [s0, s1].length →
      Kraken.Executable.ValidLayout (l tid pilotX) ∧ (plan P tid).Valid ∧ Phase1TreeFX (l tid pilotX) ∧
      (∀ y, postPX (layout := l tid) P tid y → y.1.2 = endPX (layout := l tid)) ∧
      (∀ x R, x.1.2 = endPX (layout := l tid) →
        ¬ (l tid pilotX).instrStepEnv (EnvGCAdjXV Arch.tso tid (plan P tid) (SL P) (GV P)) x R) ∧
      (∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), postPX (layout := l tid) P tid (t.st.st, σ) →
        t.prom = [] → EnvRel tid (plan P tid) σ c t r g cl → cl → TB2X P c r g) ∧
      ∃ s, [s0, s1][tid]? = some s ∧
        QX64CAdjV Arch.tso tid (plan P tid) (SL P) (GV P) (l tid pilotX) (endPX (layout := l tid))
          (postPX (layout := l tid) P tid) s
          (σInitX (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P tid) (ghost₀ P)) := by
  intro tid htid
  have H : ∀ w (hw : w < 2) s, StartPX (layout := l w) P w s →
      tRes (Config.init [s0, s1] initMem).mem P w = thrRes (Config.init [s0, s1] initMem).mem P w →
      QX64CAdjV Arch.tso w (plan P w) (SL P) (GV P) (l w pilotX) (endPX (layout := l w))
        (postPX (layout := l w) P w) s
        (σInitX (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P w) (ghost₀ P)) :=
    fun w hw s hS htr => by
      rw [htr]; exact qx64CAdjV_pilotX (layout := l w) P w hL hw hS (pu_init P hL hw _ hT0)
  have hw : tid < 2 := by simpa using htid
  refine ⟨hv tid, plan_valid P tid, ?_, postPX_end (layout := l tid) P tid,
    pilotX_stuck (layout := l tid) _, hB_pX (layout := l tid) P hw, ?_⟩
  · exact @pilotX_phase1FX (l tid) (hv tid)
  rcases tid with _ | _ | i
  · exact ⟨s0, rfl, H 0 hw s0 h0 rfl⟩
  · exact ⟨s1, rfl, H 1 hw s1 h1 rfl⟩
  · omega

omit layout in
/-- **The final case split** (`x64_treiber2_envG_verbatim`'s): at a final
configuration where every done thread satisfies `TB2X`, the threads popped
the two nodes. -/
theorem pilotX_final {P : Params} (hL : TLocs P) {cfg : Config isa} (hf : cfg.final = true) {rF' : Nat → Res}
    {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg) (hle : (ghost₀ P).Le g') (hsize : cfg.threads.size = 2)
    (hB : ∀ tid, cfg.Done tid → TB2X P cfg (rF' tid) g') : Treiber2FinalX (P.n 0) (P.n 1) cfg := by
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; decide
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; decide
  have hW := (ghost₀_gw P).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨w0, hw0, th, hth, hd0⟩ := hB 0 (Config.final_done hf hi0)
  obtain ⟨w1, hw1, th', hth', hd1⟩ := hB 1 (Config.final_done hf hi1)
  by_cases hww : w0 = w1
  · subst hww
    exact (TreiberCommon.acq_pair_false E' hi0 hi1 (by decide) hd0.1 hd1.1).elim
  rcases w0 with _ | _ | w0
  · rcases w1 with _ | _ | w1
    · exact absurd rfl hww
    · exact ⟨th, th', hth, hth', final_values E' hW hL hno hi0 hi1 hd0 hd1⟩
    · omega
  · rcases w1 with _ | _ | w1
    · exact ⟨th', th, hth', hth, final_values E' hW hL hno hi1 hi0 hd1 hd0⟩
    · exact absurd rfl hww
    · omega
  · omega

omit layout in
/-- **The assembly, conditional on the open parts**: the bridge, the purity
judgments of the start states (`HoldsV`, not proved here) and `hvals` (not
proved here). Checks that `hthr_pX` and `pilotX_final` fit the bridge;
the planned `pilotX_promising_of_envGValsBridgeX` (module docstring)
discharges `h0` and `hvals` from the start states. -/
theorem pilotX_promising_of_bridge_pure {fuel : Nat} (l : Nat → _root_.Layout)
    [∀ w, Executable.ValidLayout (l w pilotX)] {P : Params} (hL : TLocs P) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartPX (layout := l 0) P 0 s0) (h1 : StartPX (layout := l 1) P 1 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal P.top = 0)
    (hbridge : EnvGValsBridgeX (SL P) (GV P)) (sp : Nat → RelPureSpecQX Arch.tso fun _ _ => False)
    (hsp : ∀ tid s, [s0, s1][tid]? = some s → (sp tid).HoldsV (GV P) s)
    (hvals : ∀ c, Reachable Arch.tso fuel (Config.init [s0, s1] initMem) c → MemInv (GV P) c.mem)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2FinalX (P.n 0) (P.n 1) cfg :=
  hbridge (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl) fuel [s0, s1] initMem (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) (TB2X P)
    (Treiber2FinalX (P.n 0) (P.n 1)) (plan P) (fun w => l w pilotX) (fun w => endPX (layout := l w))
    (fun w => postPX (layout := l w) P w) (erase_init hL _) (ghost₀_pend _) sp hsp hvals
    (hthr_pX l hL h0 h1 hT0) cfg hc hf fun _ _ E' hle hsize hB => pilotX_final hL hf E' hle hsize hB

end Kraken.Promising.Lower.PilotX
