/-
**The whole program, through the kit.** ISA: AArch64 (`isa`; `isaLSE2` for `_lse2`); `Arch.armv8`;
the executable machine (`Reachable`). The allocation pilot's `Lower/AllocWhole.lean` and
`Lower/AllocLSE2.lean` at `publishP`: `hB_P`, `publishT`, `StartP` (`StartA`'s
fields at `publishP`); final reading `KitPilot.treiber2DFinal_of_hB`; the LSE2
`hfree` is `publishP_lse2Free` (from `publishP_wcLowerable`).
-/
import Kraken.Promising.Lower.PublishPure
import Kraken.Promising.Lower.KitPilot
import Kraken.Promising.Lower.KitLSE2

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Lower.Variant Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.Publish

open Kraken.Promising.SLR.EnvG.Treiber2 Kraken.Promising.Lower.Kit
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-- **`hB` for thread `w`**: `DnD` at the end of the text is `TB2D`. -/
theorem hB_P [layout : _root_.Layout] (P : Params) {w : Nat} (hw : w < 2) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf publishP (fun s g => ∃ _ : Nat, DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec g) (t.st.st, σ) →
    t.prom = [] → EnvRel w (plan P w) σ c t r g cl → cl → TB2D P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact ⟨w, hw, t, hrel.ht, hcom.2.2.1, by rw [initVal_eq hrel.snap.init]; exact hcom.2.2.2.1,
      hd.imp (DonePopD.mono hpre) (DoneCbz.mono hpre)⟩
  · rw [hp] at hts; cases hts

/-- **`publishP` as a lowered thread** at layout `l`, thread `w`. -/
noncomputable def publishT (l : _root_.Layout) [Executable.ValidLayout (l publishP)] (P : Params) (w : Nat)
    (hL : TLocs P) (hw : w < 2) (d : BitVec 32) (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v)
    (hd : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w, 4⟩) v)
    (hn : ∀ v : Val, Pred.Pure ((ghost₀ P).rel ⟨P.n w + 8, 8⟩) v) :
    LowerThread Arch.armv8 w (ghost₀ P).rel (TB2D P) where
  l := l
  p := publishP
  valid := inferInstance
  pl := plan P w
  hpl := plan_valid P w
  live := publishP_rmwLive (layout := l)
  shape := publishP_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1
  hB := hB_P (layout := l) P hw
  PreR s _ := MainPreR (layout := l) P.t (P.n w) s
  QR _ _ := True
  pure := main_pure (layout := l) _ P.t (P.n w) hd hn
  Pre := MainPre (layout := l) P w d
  main := main_partialTripleEnv (layout := l) P w hL hw d hD

/-- **A thread's start for `publishP`**: `Alloc.StartA`'s fields at
`publishP` (`&top` in `x21`, room for one node at `x27 = n` below `x28`, the
payload in `w20`, no `dmem` word; nothing about the arena's contents). -/
structure StartP [layout : _root_.Layout] (t n : BitVec 64) (d : BitVec 32) (s : isa.State) : Prop where
  exe : s.exe = layout publishP
  decls : s.decls = {}
  endPc : s.endPc = (layout publishP).addrOf publishP.length
  pc : s.st.2 = (layout publishP).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout publishP).addrOf publishP.length
  x21 : s.st.1.regs.X21.toBitVec = t
  x27 : s.st.1.regs.X27.toBitVec = n
  x28 : s.st.1.regs.X27.toBitVec + 16 ≤ s.st.1.regs.X28.toBitVec
  x20 : s.st.1.regs.X20.toBitVec.setWidth 32 = d
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

theorem publishT_start (l : _root_.Layout) [Executable.ValidLayout (l publishP)] {P : Params} {w : Nat}
    (hL : TLocs P) (hw : w < 2) {d : BitVec 32} (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {hd hn}
    {s : isa.State} (hS : StartP (layout := l) P.t (P.n w) d s) {c : Config isa} (hT0 : c.mem.initVal P.top = 0) :
    (publishT l P w hL hw d hD hd hn).Start (σInit c (thrRes c.mem P w) (ghost₀ P)) s := by
  obtain ⟨he, hds, hend, hpc, h30, h21, h27, h28, h20, hd8, hd4⟩ := hS
  exact ⟨⟨he, hds, hend, hpc, 0, h30, h21, h27, h28, hd8, hd4⟩,
    0, h30, h21, h27, h28, h20, ⟨hd8, hd4⟩, pu0_init P hL hw _ hT0⟩

/-- The two lowered threads, at layouts `l0`, `l1`. -/
noncomputable abbrev publishTs (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] (t n0 n1 : BitVec 64) (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} : ∀ tid, tid < [s0, s1].length → LowerThread Arch.armv8 tid (ghost₀ (tPD t n0 n1)).rel
      (TB2D (tPD t n0 n1)) :=
  have hr : ∀ l, l ≠ (tPD t n0 n1).top → ∀ v, Pred.Pure ((ghost₀ (tPD t n0 n1)).rel l) v :=
    fun l hl v => by rw [ghost₀_rel_ne hl]; exact Pred.emp_pure v
  fun tid h => match tid, h with
    | 0, _ => publishT l0 _ 0 hL (by decide) 1 (fun _ h => h) (hr _ (top_dd _ 0).symm)
      (hr _ (hL.top_nd' (by decide)).symm)
    | 1, _ => publishT l1 _ 1 hL (by decide) 2 (fun _ h => h) (hr _ (top_dd _ 1).symm)
      (hr _ (hL.top_nd' (by decide)).symm)
    | _ + 2, h => absurd h (by simp)

theorem publishTs_start (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] {t n0 n1 : BitVec 64} (hL : TLocs (tPD t n0 n1))
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0) :
    ∀ tid (h : tid < [s0, s1].length), (publishTs l0 l1 t n0 n1 hL tid h).Start
      (σInit (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem (tPD t n0 n1) tid)
        (ghost₀ (tPD t n0 n1))) [s0, s1][tid] := by
  intro tid h
  rcases tid with _ | _ | _
  · exact publishT_start l0 (w := 0) hL (by decide) _ h0 hT0
  · exact publishT_start l1 (w := 1) hL (by decide) _ h1 hT0
  · simp at h; omega

/-- **The allocating Treiber client with WeakCore's `publish` barrier, on the
Promising model** (AArch64, `Arch.armv8`, `isa`, executable machine). For all
layouts `l0`, `l1` of `publishP`, all addresses `t` of `top` and `n0`, `n1` of
the two arena nodes with `t ≠ n0 + 8`, `t ≠ n1 + 8`, `n0 ≠ n1`, `n0 ≠ 0`,
`n1 ≠ 0`: if thread `0` starts with its arena at `n0` and payload `1`, thread
`1` at `n1` with payload `2` (`StartP`), and `top` is initially `0`, then
every final configuration reachable under `Arch.armv8` has
`Treiber2DFinal n0 n1` (`Alloc.alloc_promising`'s conclusion): each popped
node was allocated, initialised, published (`dmb ishst`) and pushed by a
thread, with its payload; no thread found the stack empty. -/
theorem publish_promising {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) rfl
    (publishTs l0 l1 t n0 n1 hL) (publishTs_start l0 l1 hL h0 h1 hT0) hc hf
    (KitPilot.treiber2DFinal_of_hB hL hf rfl)

/-- **`publish_promising` on `isaLSE2`** (AArch64 with FEAT_LSE2, the WeakCore
lowering target; `Arch.armv8`, executable machine), through
`Kit.lower_promising_lse2`: same hypotheses, the conclusion read in
`Config isa` through `ofL`. -/
theorem publish_promising_lse2 {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 publishP)]
    [Executable.ValidLayout (l1 publishP)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8)
    (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartP (layout := l0) t n0 1 s0) (h1 : StartP (layout := l1) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem : Config isa).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isaLSE2} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 (ofL cfg) :=
  have hL := tLocs_tPD ht0 ht1 hn hn0 hn1
  lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init hL _) rfl
    (publishTs l0 l1 t n0 n1 hL) (publishTs_start l0 l1 hL h0 h1 hT0)
    (fun tid h => match tid, h with
      | 0, _ => publishP_lse2Free
      | 1, _ => publishP_lse2Free
      | _ + 2, h => absurd h (by simp))
    (fun _ hf' => KitPilot.treiber2DFinal_of_hB hL hf' rfl) hc hf

end Kraken.Promising.Lower.Publish

#print axioms Kraken.Promising.Lower.Publish.publish_promising
#print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2
