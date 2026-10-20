/-
**The whole program on the executable Promising
machine (`Reachable Arch.armv8`), through the kit** (`Kit.lower_promising`).
Per program: `hB_A`, `allocT`, `StartA` and its
discharge; the final reading is `KitPilot.treiber2DFinal_of_hB`.
-/
import Kraken.Promising.Lower.AllocPure
import Kraken.Promising.Lower.KitPilot

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Alloc

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-- **`hB` for thread `w`**: `DnD` at the end of the text is `TB2D`. -/
theorem hB_A [layout : _root_.Layout] (P : Params) {w : Nat} (hw : w < 2) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf allocP (fun s g => ∃ _ : Nat, DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec g) (t.st.st, σ) →
    t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2D P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePopD.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **`allocP` as a lowered thread** at layout `l`, thread `w`. -/
noncomputable def allocT (l : _root_.Layout) [Executable.ValidLayout (l allocP)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) where
  l := l
  p := allocP
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  live := allocP_rmwLive (layout := l)
  shape := allocP_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := hB_A (layout := l) P hw
  PreR s _ := MainPreR (layout := l) P.t (P.n w) s
  QR _ _ := True
  pure := main_pure (layout := l) _ P.t (P.n w) hd hn
  Pre := MainPre (layout := l) P w d
  main := main_partialTripleEnv (layout := l) P w hL hw d hD

/-- **A thread's start for `allocP`** (the runtime's side): `&top` in `x21`, the
bump pointer `x27 = n` with room for one node below `x28`, the payload in
`w20`, no `dmem` word. Nothing about the arena's contents. -/
structure StartA [layout : _root_.Layout] (t n : BitVec 64) (d : BitVec 32) (s : isa.State) : Prop where
  exe : s.exe = layout allocP
  decls : s.decls = {}
  endPc : s.endPc = (layout allocP).addrOf allocP.length
  pc : s.st.2 = (layout allocP).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout allocP).addrOf allocP.length
  x21 : s.st.1.regs.X21.toBitVec = t
  x27 : s.st.1.regs.X27.toBitVec = n
  x28 : s.st.1.regs.X27.toBitVec + 16 ≤ s.st.1.regs.X28.toBitVec
  x20 : s.st.1.regs.X20.toBitVec.setWidth 32 = d
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

theorem allocT_start (l : _root_.Layout) [Executable.ValidLayout (l allocP)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d : BitVec 32} (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {hd hn}
    {s : isa.State} (hS : StartA (layout := l) P.t (P.n w) d s) {c : Config isa} (hT0 : c.mem.initVal P.top = 0) :
    (allocT l P w hL hw d hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h20, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h20, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-- **The allocating Treiber client on the Promising model** (AArch64,
`Arch.armv8`, `isa`): for all layouts `l0`, `l1` of `allocP`, all addresses
`t` of `top` and `n0`, `n1` of the two arena nodes with `t ≠ n0 + 8`,
`t ≠ n1 + 8`, `n0 ≠ n1`, `n0 ≠ 0`, `n1 ≠ 0`: if thread `0` starts with its
arena at `n0` and payload `1`, thread `1` at `n1` with payload `2` (`StartA`),
and `top` is initially `0` (the arenas' initial contents are arbitrary), then
every final configuration reachable under `Arch.armv8` has
`(0:X10 = n0 ∧ 0:X11 = 1 ∧ 1:X10 = n1 ∧ 1:X11 = 2) ∨ (0:X10 = n1 ∧ 0:X11 = 2 ∧
1:X10 = n0 ∧ 1:X11 = 1)`: each popped node was allocated, initialised and
pushed by a thread, with that thread's payload; no thread found the stack
empty. -/
theorem alloc_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 allocP)]
    [Executable.ValidLayout (l1 allocP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartA (layout := l0) t n0 1 s0) (h1 : StartA (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg := by
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  refine lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl
    (fun tid h => match tid, h with
      | 0, _ => allocT l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
        (hr _ (hL.top_nd' (by decide)).symm)
      | 1, _ => allocT l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
        (hr _ (hL.top_nd' (by decide)).symm)
      | _ + 2, h => absurd h (by simp))
    (fun tid h => ?_) hc hf (KitPilot.treiber2DFinal_of_hB hL hf rfl)
  rcases tid with _ | _ | _
  · exact allocT_start l0 (w := 0) hL (by decide) _ h0 hT0
  · exact allocT_start l1 (w := 1) hL (by decide) _ h1 hT0
  · simp at h; omega

/-! ## The concrete instance (the explorer's configuration, garbage arenas) -/

section
attribute [local instance] aLayout

theorem thread_start (base v : UInt64) (n : BitVec 64) (d : BitVec 32) (hn : base.toBitVec = n)
    (hlim : base.toBitVec + 16 ≤ (base + 0x100).toBitVec) (hd : v.toBitVec.setWidth 32 = d) :
    StartA (layout := aLayout) 0x1000 n d (thread base v) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, hn, hlim, hd, ?_, ?_⟩ <;> try (simp only [thread]; decide)
  all_goals simp [thread, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **Non-vacuity**: `alloc_promising` at the explorer's configuration
(`AllocProg`): `top` at `0x1000`, arenas at `0x2000`/`0x3000` holding garbage
(`7`), payloads `1`, `2`. No hypothesis beyond reachability and finality. -/
theorem alloc_promising_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [thread 0x2000 1, thread 0x3000 2] initMem) c)
    (hf : c.final = true) : Treiber2DFinal 0x2000 0x3000 c :=
  alloc_promising aLayout aLayout 0x1000 0x2000 0x3000 (by decide) (by decide) (by decide) (by decide)
    (by decide) (thread_start _ _ _ _ rfl (by decide) (by decide))
    (thread_start _ _ _ _ rfl (by decide) (by decide)) (by simp only [Config.init_mem]; decide) hc hf

end Kraken.Promising.Lower.Alloc
