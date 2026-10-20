/-
**The faithful WeakCore MS queue, shape B**
(enqueuer `enq(1); enq(2)` = `WcMsq.progE`, thread `0`; two dequeuers
calling `deq()` once = `progD1`, threads `1`, `2`).
AArch64, `Arch.armv8`; MsQueue3's protocol (`planE2`, `planD2` for both
dequeuers, `tRes3`), `bdeq_spec` at `k = 1, 2`. Machines: `wcMsqB_promising`
executable (`isa`), `_lse2` executable (`isaLSE2`), `_lse2_semInf` fuel-free
semantic (`isaLSE2`). **Proved** (`WcMsqBFinal`): each result empty or tag
`0` with payload `1` or `2`; both dequeued: `1`, `2` in some order. The
explorer's shape-B set (`wcMsqRunB`) plus `(E,v2)`, `(v2,E)` (never reached;
excluding them needs per-writer `head` messages, as in shape A).
-/
import Kraken.Promising.Lower.WcMsqBVC
import Kraken.Promising.Lower.WcMsqForms
import Kraken.Promising.SLR.EnvG.MsQueue3Public
import Kraken.Promising.SLR.EnvG.A64MaskHelpers

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Live.Bridge

namespace Kraken.Promising.Lower.WcMsq

open Kraken.Promising.SLR.EnvG.MsQueue Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem RP)
open Kraken.Promising.Lower.MsqPilot (PFrame dPre blTo)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- Behind `main_d1`'s `bl deq`: the result to `x10, x11`, return. -/
def d1Tail : Program := parseAArch64("
    mov x10, x0
    mov x11, x1
    mov x30, x19
    ret
")

theorem mainD1Body_eq : mainD1Body = dPre ++ blTo "deq" :: d1Tail := by decide
/-- A dequeuer's result: empty, or tag `0` and `DoneK … k` of the payload. -/
def BRes (m : Memory) (P : Params2) (k : Nat) (t v : BitVec 64) : Prop := t = 1 ∨ (t = 0 ∧ DoneK m P k v)

section MainD1

variable [layout : _root_.Layout] [Executable.ValidLayout (layout progD1)]

local instance progD1.env' : CodeEnv := ⟨layout progD1⟩

abbrev endD1 : Int64 := (layout progD1).addrOf progD1.length

/-- At `main_d1`: the return address, `q = &head` in `x21`, no `dmem`, `ComD3`. -/
def MainD1Pre (P : Params2) (k : Nat) (s : MachineData) (σ : (SharedEnv.counted (ED3 P k)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = endD1 ∧ s.regs.X21.toBitVec = P.h ∧ NoDmem s ∧ ComD3 P k σ.1

/-- **`main_d1` as a partial triple of `progD1`**, through `bdeq_spec`. -/
theorem mainD1_partialTripleEnv (P : Params2) (hL : QLocs2 P) (k : Nat) :
    PartialTripleEnv (SharedEnv.counted (ED3 P k)) (MainD1Pre P k) progD1
      (fun s σ => ComD3 P k σ.1 ∧ BRes σ.1.snap.mem P k s.regs.X10.toBitVec s.regs.X11.toBitVec)
      (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt progD1 "main_d1" = some ⟨"main_d1", mainD1Body, some "deq"⟩ := by decide
  have hbody : PartialWpEnv (SharedEnv.counted (ED3 P k)) mainD1Body (fun _ _ => False)
      (fun a s σ => a = endD1 ∧ ComD3 P k σ.1 ∧ BRes σ.1.snap.mem P k s.regs.X10.toBitVec s.regs.X11.toBitVec)
      s σ := by
    have h1 : ∀ s₀ g₀, ⦃ fun s σ => MainD1Pre P k s σ ∧ s = s₀ ∧ σ = g₀ ⦄
        (⟨dPre⟩ : EnvProgram (SharedEnv.counted (ED3 P k)))
        ⦃ (fun _ s σ => s.regs.X0.toBitVec = P.h ∧ Int64.ofBitVec s.regs.X19.toBitVec = endD1 ∧ NoDmem s ∧
          ComD3 P k σ.1); fun _ _ _ => False ⦄ := by
      intro s₀ g₀; unfold dPre; vcgen
      all_goals obtain ⟨⟨h30, h21, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
      rename_i s σ0 σ1 σ2 hf1 hf2 _
      simp [NoDmem, h21, h30, hd8, hd4]
      exact (hT.fence hf1.1).fence hf2.1
    have h3 : ∀ s₀ g₀, ⦃ fun s σ => (Int64.ofBitVec s.regs.X19.toBitVec = endD1 ∧ ComD3 P k σ.1 ∧
          BRes σ.1.snap.mem P k s.regs.X0.toBitVec s.regs.X1.toBitVec) ∧ s = s₀ ∧ σ = g₀ ⦄
        (⟨d1Tail⟩ : EnvProgram (SharedEnv.counted (ED3 P k)))
        ⦃ (fun _ _ _ => False); fun a s σ => a = endD1 ∧ ComD3 P k σ.1 ∧
          BRes σ.1.snap.mem P k s.regs.X10.toBitVec s.regs.X11.toBitVec ⦄ := by
      intro s₀ g₀; unfold d1Tail; vcgen
      all_goals obtain ⟨⟨h19, hC, hD⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
      rename_i s σ0 σ1 σ2 σ3 σ4 hf1 hf2 hf3 hf4 _
      refine ⟨by simpa using h19, (((hC.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1, ?_⟩
      simpa [hf1.1.snap, hf2.1.snap, hf3.1.snap, hf4.1.snap] using hD
    rw [mainD1Body_eq]
    have h1' := (h1 s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1'
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1')
    rintro s1 σ1 ⟨h0, h19, ⟨hd8, hd4⟩, hC⟩
    refine PartialWpEnv.call (bdeq_spec P hL k) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩, hC⟩, ?_⟩
    rintro s2 σ2 ⟨⟨f19, -, -, -, -, -, -, -, -, -, -⟩, hC2, hR2⟩
    have h3' := (h3 s2 σ2).le_wp s2 σ2 ⟨⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
      hC2, hR2⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h3'
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3')
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progD1) progD1 [] 0 (by simp)
  rw [← progD1_placed.entry pc hpc]
  refine (hbody _ (progD1_placed.block _ _ hb)).mono fun x hx => ?_
  obtain ⟨hx, hd⟩ := hx.resolve_left fun h => h.2
  refine .inl ⟨?_, hd⟩
  rw [hx, progD1_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

set_option hygiene false in
local macro "pure_vcs" : tactic => `(tactic| (
  all_goals try (simp [hd8, hd4, SharedEnv.relPureQ]; done)
  all_goals try (simp [SharedEnv.relPureQ]; exact fun h => (h (by decide)).elim)
  all_goals try (exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩)
  all_goals try (exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
    by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩,
    .inl (by decide)⟩))
  all_goals try (exact ⟨⟨by simpa using hd8, by simpa using hd4, by simpa [MachineData.lr] using hlr,
    by simpa [CalleeSaved] using hfr⟩, by simp (config := { decide := true })⟩)
  all_goals (
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simpa using hd8, by simpa using hd4,
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr⟩,
      by simp (config := { decide := true })⟩, ?_⟩)
    exact .inr fun ⟨_, hg⟩ => by
      subst hg; simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at *
      grind)))

/-- **WeakCore's `deq` in `progD1` is pure** (`wdeq_pure` at this placement). -/
theorem bdeq_pure (rel : Loc → Pred) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "deq")
      (fun ra s _ => s.lr = ra ∧ NoDmem s) (fun _ s _ s' _ => CalleeSaved s s') := by
  rintro ra t0 g ⟨hlr, ⟨hd8, hd4⟩⟩
  refine cfgEnv_partial_fun (p := wcDeqFrag)
    (fun lb s (_ : (RP rel).State) => PFrame ra t0 s ∧ (lb = "deq" ∨ lb = "deq_empty"))
    (E := fun a s (_ : (RP rel).State) => a = ra ∧ CalleeSaved t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE progD1_placed (by decide)) t0 g
    ⟨⟨hd8, hd4, hlr, by simp [CalleeSaved]⟩, .inl rfl⟩
  cfg_cases_env [wcDeqFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hd8, hd4, hlr, hfr⟩, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  pure_vcs

/-- **`main_d1` is pure**, through `bdeq_pure`. -/
theorem mainD1_pure (rel : Loc → Pred) :
    PartialTripleEnv (RP rel) (fun s _ => Int64.ofBitVec s.regs.X30.toBitVec = endD1 ∧ NoDmem s) progD1
      (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt progD1 "main_d1" = some ⟨"main_d1", mainD1Body, some "deq"⟩ := by decide
  have hbody : PartialWpEnv (RP rel) mainD1Body (fun _ _ => False) (fun a _ _ => a = endD1) s σ := by
    have h1 : ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => (Int64.ofBitVec s.regs.X30.toBitVec = endD1 ∧ NoDmem s) ∧
        s = s₀ ∧ σ = g₀ ⦄ (⟨dPre⟩ : EnvProgram (RP rel))
        ⦃ (fun _ s _ => Int64.ofBitVec s.regs.X19.toBitVec = endD1 ∧ NoDmem s); fun _ _ _ => False ⦄ := by
      intro s₀ g₀; unfold dPre; vcgen
      all_goals obtain ⟨⟨h30, ⟨hd8, hd4⟩⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      simp [NoDmem, h30, hd8, hd4]
    have h3 : ∀ s₀ g₀, ⦃ fun s (σ : (RP rel).State) => Int64.ofBitVec s.regs.X19.toBitVec = endD1 ∧ s = s₀ ∧
        σ = g₀ ⦄ (⟨d1Tail⟩ : EnvProgram (RP rel)) ⦃ (fun _ _ _ => False); fun a _ _ => a = endD1 ⦄ := by
      intro s₀ g₀; unfold d1Tail; vcgen
      all_goals obtain ⟨h19, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      simpa using h19
    rw [mainD1Body_eq]
    have h1' := (h1 s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1'
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h.elim) h1')
    rintro s1 σ1 ⟨h19, ⟨hd8, hd4⟩⟩
    refine PartialWpEnv.call (bdeq_pure rel) fun ra => ⟨⟨by simp [MachineData.lr, MachineData.setLr],
      ⟨by simpa [MachineData.setLr] using hd8, by simpa [MachineData.setLr] using hd4⟩⟩, ?_⟩
    rintro s2 σ2 ⟨f19, -, -, -, -, -, -, -, -, -, -⟩
    have h3' := (h3 s2 σ2).le_wp s2 σ2 ⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19, rfl, rfl⟩
    rw [wpEnv_eq] at h3'
    exact PartialWpEnv.of_wpEnv (Executable.wpEnv_mono (fun _ _ h => h.elim) (fun _ _ _ h => h) h3')
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := progD1) progD1 [] 0 (by simp)
  rw [← progD1_placed.entry pc hpc]
  refine (hbody _ (progD1_placed.block _ _ hb)).mono fun x hx => .inl ⟨?_, trivial⟩
  rw [hx.resolve_left fun h => h.2, progD1_placed.entry _ hs0, Nat.zero_add] at *
  exact haf.symm

end MainD1

section Static

variable [layout : _root_.Layout]

theorem progD1_rmwLive : (layout progD1).rmwLive = true := by rw [Layout.apply_rmwLive]; decide
theorem progD1_phase1F [Executable.ValidLayout (layout progD1)] : Phase1TreeF (layout progD1) :=
  phase1TreeF_of_dirs (dirsPhase1F_layout (by
    simp only [progD1, mainD1Body, wcDeqFrag, List.cons_append, List.nil_append]; dirs_phase1F_any progD1))

/-- A shape-B dequeuer's start state (`StartD` for `progD1`). -/
structure StartD1 (h : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout progD1
  decls : s.decls = {}
  endPc : s.endPc = (layout progD1).addrOf progD1.length
  pc : s.st.2 = (layout progD1).addrOf 0
  x30 : Int64.ofBitVec s.st.1.regs.X30.toBitVec = (layout progD1).addrOf progD1.length
  x21 : s.st.1.regs.X21.toBitVec = h
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

end Static
theorem progD1_wcLowerable : progD1.WCLowerable := by decide

/-- The shared postcondition (MsQueue3's `MB3` with `BRes`). -/
def WB3 (P : Params2) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧ BRes c.mem P 1 th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧
      InitV2 c.mem P ∧ ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∨
    (∃ th, c.threads[2]? = some th ∧ BRes c.mem P 2 th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧
      1 ≤ (r.wr (tokD2 P)).q) ∨ 1 ≤ (r.wr P.tokE).q

theorem hB_EF3 (l : _root_.Layout) (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) progE (fun _ σ => ∃ _ : Nat, ComE2 P σ) (t.st.st, σ) → t.prom = [] →
    EnvRel 0 (planE2 P) σ c t r g cl → cl → WB3 P c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inr hcom.2.2.1)
  · rw [hp] at hts; cases hts

theorem hB_DB (l : _root_.Layout) (P : Params2) (k : Nat) (hk : k = 1 ∨ k = 2) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA), postOf (layout := l) progD1 (fun s σ =>
      ∃ _ : Nat, ComD3 P k σ ∧ BRes σ.snap.mem P k s.regs.X10.toBitVec s.regs.X11.toBitVec) (t.st.st, σ) →
      t.prom = [] → EnvRel k (planD2 P) σ c t r g cl → cl → WB3 P c r g := by
  intro c t r g cl σ hpost hp hrel _
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  have hd' : BRes c.mem P k _ _ := (hd : BRes _ _ _ _ _).imp_right fun ⟨e, h⟩ => ⟨e, h.mono hpre⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · rcases hk with rfl | rfl
    · exact .inl ⟨t, hrel.ht, hd', hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1.1 rfl⟩
    · exact .inr (.inl ⟨t, hrel.ht, hd', hcom.2.2.2.1.2 rfl⟩)
  · rw [hp] at hts; cases hts

/-- **A shape-B dequeuer** (thread `k ∈ {1, 2}`, `progD1`). -/
noncomputable def deqTB (l : _root_.Layout) [Executable.ValidLayout (l progD1)] (P : Params2) (hL : QLocs2 P)
    (k : Nat) (hk : k = 1 ∨ k = 2) : LowerThread Arch.armv8 k (ghost2 P).rel (WB3 P) where
  l := l
  p := progD1
  valid := inferInstance
  pl := planD2 P
  hpl := planD2_valid P
  live := progD1_rmwLive (layout := l)
  shape := progD1_phase1F (layout := l)
  stuck env := not_instrStepEnv_of_end_labels (layout := l) env 1
  Q s σ := ComD3 P k σ.1 ∧ BRes σ.1.snap.mem P k s.regs.X10.toBitVec s.regs.X11.toBitVec
  hB := hB_DB l P k hk
  PreR s _ := Int64.ofBitVec s.regs.X30.toBitVec = endD1 (layout := l) ∧ NoDmem s
  QR _ _ := True
  pure := mainD1_pure (layout := l) _
  Pre := MainD1Pre (layout := l) P k
  main := mainD1_partialTripleEnv (layout := l) P hL k

/-- The threads of shape B. -/
noncomputable def wcTsB (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD1)] [Executable.ValidLayout (l2 progD1)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) : ∀ tid, tid < 3 → LowerThread Arch.armv8 tid (ghost2 P).rel (WB3 P)
  | 0, _ => { enqTF l0 P hL ht (g2pure (not_isW_dat _)) (g2pure (not_isW_dat2 _)) with hB := hB_EF3 l0 P }
  | 1, _ => deqTB l1 P hL 1 (.inl rfl)
  | 2, _ => deqTB l2 P hL 2 (.inr rfl)
  | _ + 3, hh => absurd hh (by omega)

theorem wcTsB_start {h t d n1 n2 : BitVec 64} {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (hi : InitV2 (Config.init [s0, s1, s2] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 progE)] [Executable.ValidLayout (l1 progD1)]
    [Executable.ValidLayout (l2 progD1)] (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) (ht : t = h + 8)
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD1 (layout := l1) h s1) (h2 : StartD1 (layout := l2) h s2) :
    ∀ tid (hh : tid < [s0, s1, s2].length), (wcTsB l0 l1 l2 _ hL ht tid hh).Start
      (σInit (Config.init [s0, s1, s2] initMem) (tRes3 (Config.init [s0, s1, s2] initMem : Config isa).mem
        ⟨⟨h, t, d, n1⟩, n2⟩ tid) (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩)) [s0, s1, s2][tid] := by
  intro tid hh
  rcases tid with _ | _ | _ | _
  · obtain ⟨he, hds, hend, hpc, h30, h21, h22, h23, hd8, hd4⟩ := h0
    exact ⟨⟨he, hds, hend, hpc, 0, h30, h22, h23, hd8, hd4⟩, 0, h30, h21, h22, h23, ⟨hd8, hd4⟩, start1_init3 hL _⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h1
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comDa3_init _ _ hi⟩
  · obtain ⟨he, hds, hend, hpc, h30, h21, hd8, hd4⟩ := h2
    exact ⟨⟨he, hds, hend, hpc, 0, h30, hd8, hd4⟩, 0, h30, h21, ⟨hd8, hd4⟩, comDb3_init _ _ hi⟩
  · simp at hh; omega

theorem wcTsB_free (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD1)] [Executable.ValidLayout (l2 progD1)] (P : Params2) (hL : QLocs2 P)
    (ht : P.t = P.h + 8) {s0 s1 s2 : isa.State} :
    ∀ tid (hh : tid < [s0, s1, s2].length), ∀ x ∈ (wcTsB l0 l1 l2 P hL ht tid hh).p, x.LSE2Free
  | 0, _ => progE_wcLowerable.lse2Free | 1, _ => progD1_wcLowerable.lse2Free
  | 2, _ => progD1_wcLowerable.lse2Free | _ + 3, hh => absurd hh (by simp)

/-- **The two results by value**: each empty, or `1` or `2`; both: distinct. -/
def BVals (t1 v1 t2 v2 : BitVec 64) : Prop :=
  (t1 = 1 ∨ (t1 = 0 ∧ (v1 = 1 ∨ v1 = 2))) ∧ (t2 = 1 ∨ (t2 = 0 ∧ (v2 = 1 ∨ v2 = 2))) ∧
    (t1 = 0 → t2 = 0 → (v1 = 1 ∧ v2 = 2) ∨ (v1 = 2 ∧ v2 = 1))

/-- **Shape B's property**: `BVals` of threads `1`, `2`'s `x10, x11`. -/
def WcMsqBFinal (c : Config isa) : Prop :=
  ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧ BVals th1.st.st.1.regs.X10.toBitVec
    th1.st.st.1.regs.X11.toBitVec th2.st.st.1.regs.X10.toBitVec th2.st.st.1.regs.X11.toBitVec

/-- **The final step** (`msqueue3_final_of_hB` with `WB3`, `deq_val`). -/
theorem wcMsqB_final_of_hB {h t d n1 n2 : BitVec 64} (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) {cfg : Config isa}
    (hf : cfg.final = true) {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg)
    (hle : (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).Le g') (hsize : cfg.threads.size = 3)
    (hB : ∀ tid, cfg.Done tid → WB3 ⟨⟨h, t, d, n1⟩, n2⟩ cfg (rF' tid) g') : WcMsqBFinal cfg := by
  have hlt : ∀ i, i < 3 → i < cfg.threads.size := fun i hi => by rw [hsize]; simpa using hi
  have hW := (ghost2_gw ⟨⟨h, t, d, n1⟩, n2⟩).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨⟨i, hi3, th1, hth1, hd1, hiv, hacq⟩, ⟨-, -, th2, hth2, hd2, -⟩⟩ := pigeon3
    (A := fun i => i < 3 ∧ ∃ th : Thread isa, cfg.threads[1]? = some th ∧
      BRes cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ 1 th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧
      InitV2 cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ ∧ ∀ x, Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ x → 1 ≤ (rF' i).acq x 0)
    (B := fun i => i < 3 ∧ ∃ th : Thread isa, cfg.threads[2]? = some th ∧
      BRes cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ 2 th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧
      1 ≤ ((rF' i).wr (tokD2 ⟨⟨h, t, d, n1⟩, n2⟩)).q)
    (C := fun i => i < 3 ∧ 1 ≤ ((rF' i).wr (Params.tokE ⟨h, t, d, n1⟩)).q)
    ((hB 0 (Config.final_done hf (hlt 0 (by decide)))).imp (⟨by decide, ·⟩)
      (Or.imp (⟨by decide, ·⟩) (⟨by decide, ·⟩)))
    ((hB 1 (Config.final_done hf (hlt 1 (by decide)))).imp (⟨by decide, ·⟩)
      (Or.imp (⟨by decide, ·⟩) (⟨by decide, ·⟩)))
    ((hB 2 (Config.final_done hf (hlt 2 (by decide)))).imp (⟨by decide, ·⟩)
      (Or.imp (⟨by decide, ·⟩) (⟨by decide, ·⟩)))
    (fun i j hij ⟨hi3, _, _, _, _, ha⟩ ⟨hj3, _, _, _, _, hb⟩ =>
      TreiberCommon.acq_pair_false E' (hlt i hi3) (hlt j hj3) hij (ha _ (.inl rfl)) (hb _ (.inl rfl)))
    (fun i j hij ⟨hi3, _, _, _, ha⟩ ⟨hj3, _, _, _, hb⟩ => tokD2_pair_false E' (hlt i hi3) (hlt j hj3) hij ha hb)
    (fun i j hij ⟨hi3, ha⟩ ⟨hj3, hb⟩ =>
      tokE_pair_false (P := (⟨h, t, d, n1⟩ : Params)) E' (hlt i hi3) (hlt j hj3) hij ha hb)
  have htot := fun x hx => TreiberCommon.total_acq_of_ge E' (hlt i hi3) (hacq x hx)
  have hv : ∀ {k x}, DoneK cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ k x → x = 1 ∨ x = 2 :=
    fun ⟨_, hV⟩ => deq_val E' hW hL hiv htot hno hV.deq
  exact ⟨th1, th2, hth1, hth2, hd1.imp_right fun ⟨e, hd⟩ => ⟨e, hv hd⟩, hd2.imp_right fun ⟨e, hd⟩ => ⟨e, hv hd⟩,
    fun e1 e2 => final_values3 E' hW hL hiv htot hno (hd1.resolve_left (by rw [e1]; decide)).2
      (hd2.resolve_left (by rw [e2]; decide)).2⟩

/-- **The faithful WeakCore MS queue, shape B, on the Promising model**
(`isa`, executable machine): from `StartEF`/`StartD1`/`StartD1`, msqueue2's
layout facts `QLocs2` and `InitV2`, every reachable final config has `WcMsqBFinal`. -/
theorem wcMsqB_promising {fuel : Nat} (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD1)] [Executable.ValidLayout (l2 progD1)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD1 (layout := l1) h s1) (h2 : StartD1 (layout := l2) h s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1, s2] initMem) cfg)
    (hf : cfg.final = true) : WcMsqBFinal cfg :=
  lower_promising Arch.armv8 fuel (fun _ hc' => Config.ntFree_armv8 hc') (erase_init3 hL _) rfl
    (wcTsB l0 l1 l2 _ hL ht) (wcTsB_start hi l0 l1 l2 hL ht h0 h1 h2) hc hf
    fun _ _ E' hle hsize hB => wcMsqB_final_of_hB hL hf E' hle hsize hB

/-- **`wcMsqB_promising` on `isaLSE2`** (executable machine). -/
theorem wcMsqB_promising_lse2 {fuel : Nat} (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD1)] [Executable.ValidLayout (l2 progD1)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD1 (layout := l1) h s1) (h2 : StartD1 (layout := l2) h s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2}
    (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1, s2] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqBFinal (ofL cfg) :=
  lower_promising_lse2 Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init3 hL _) rfl
    (wcTsB l0 l1 l2 _ hL ht) (wcTsB_start hi l0 l1 l2 hL ht h0 h1 h2) (wcTsB_free l0 l1 l2 _ hL ht)
    (fun _ hf' _ _ E' hle hsize hB => wcMsqB_final_of_hB hL hf' E' hle hsize hB) hc hf

/-- **`wcMsqB_promising_lse2`, fuel-free semantic machine**
(`Live.Inf.ReachableSemInf` of `isaLSE2`): same hypotheses and conclusion. -/
theorem wcMsqB_promising_lse2_semInf (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 progE)]
    [Executable.ValidLayout (l1 progD1)] [Executable.ValidLayout (l2 progD1)] (h t d n1 n2 : BitVec 64)
    (ht : t = h + 8) (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEF (layout := l0) h n1 n2 s0) (h1 : StartD1 (layout := l1) h s1) (h2 : StartD1 (layout := l2) h s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem : Config isa).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s0, s1, s2] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WcMsqBFinal (ofL cfg) :=
  lower_promising_lse2_semInf Arch.armv8 (fun _ hc' => Config.ntFree_armv8K hc') (erase_init3 hL _) rfl
    (wcTsB l0 l1 l2 _ hL ht) (wcTsB_start hi l0 l1 l2 hL ht h0 h1 h2) (wcTsB_free l0 l1 l2 _ hL ht)
    (fun _ hf' _ _ E' hle hsize hB => wcMsqB_final_of_hB hL hf' E' hle hsize hB) hc hf

end Kraken.Promising.Lower.WcMsq

#print axioms Kraken.Promising.Lower.WcMsq.wcMsqB_promising
#print axioms Kraken.Promising.Lower.WcMsq.wcMsqB_promising_lse2
#print axioms Kraken.Promising.Lower.WcMsq.wcMsqB_promising_lse2_semInf
