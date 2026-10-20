/-
**The value specification of `pilot2`.** ISA: AArch64; environment:
`SharedEnv.counted (SharedEnv.inv (SLay P) (GV P))` (`treiber2EnvA` at `P`).

The per-thread value specification `J` the value bridge bridge
(`envGValsBridge_ofSpecs`, `EnvG/ValsA64.lean`) asks for: `pilot2` (`main`
with its `dmem` frame, `push`/`pop` called by `bl`/`ret`) as a
`PartialTripleEnv` in the invariant environment of the Treiber values
(`top` and both links hold `0`, `n0` or `n1`). The structure is
`Lower/Pilot2Pure.lean`'s (function specifications for `push`/`pop`, then
`main`'s prefix, middle and tail), with `MemValsA64Treiber2.treiber2DWorker_val`'s
value side:
- every shared access is at a location of `SLay P` (`top`, the own node's data
  word and link, the link and data word of a popped node, a node by
  `top_node`: the `G` answer of the `ldar` and `PtrsInHeap`), and off `dmem`
  (`HeapOff (HP P)`);
- `push` writes the `G`-value it read from `top` to its node's link and its
  node to `top` (`treiber2ValA_cas`), `pop` the `G`-value of the link;
- `pop` returns null or a node (`PopVal`), for `main`'s payload load;
- the frame `str`/`ldr x30` is private (the slot is mapped).
The tree law of `J := ThreadSpec.Holds` is `threadSpec_allInv` (inside the
bridge); `pilot2ValSpec_holds` gives `J` at a `MainPreR2` start.
-/
import Kraken.Promising.Lower.Pilot2Pure
import Kraken.Promising.SLR.EnvG.ValsA64

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved pushFrag popFrag mainMid)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The value environment of thread code at `P`: `inv (SLay P) (GV P)`, counted. -/
abbrev IV (P : Params) : SharedEnv := SharedEnv.counted (SharedEnv.inv (SLay P) (GV P))

/-- A pointer `pop` may return: null or a node. -/
def PopVal (P : Params) (x : BitVec 64) : Prop := x = 0 ∨ x = P.n 0 ∨ x = P.n 1

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

local instance pilot2.envV : CodeEnv := ⟨layout pilot2⟩

/-! ## `push` and `pop` -/

/-- `push`'s value table. -/
abbrev pushVTable2 (P : Params) (w : Nat) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (IV P).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem ∧ s.lr = ra ∧
    Saved2 t0 s ∧ lb = "push"

/-- **`push` in the value environment**: it writes the `top` it read to its
node's link and its node to `top`. -/
theorem push_val2 (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (IV P) ((_root_.Executable.labels cenv).label "push")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s') := by
  have hw' := pn_cases (P := P) hw
  rintro ra t0 g ⟨hlr, hx0, hx1, hH⟩
  refine cfgEnv_partial_fun (p := pushFrag) (pushVTable2 P w ra t0)
    (E := fun a s (_ : (IV P).State) => a = ra ∧ Saved2 t0 s) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) t0 g
    ⟨hx0, hx1, hH, hlr, Saved2.refl t0, rfl⟩
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hd.loadInt_none (hp_top P) (n := 8) (by decide)
  all_goals have hn8 := hd.loadInt_none (hp_link hw') (n := 8) (by decide)
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, Treiber2ValLA, Treiber2ValVA]; done)
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx1, Treiber2ValLA]
    exact fun old _ => treiber2ValA_cas (by rcases hw' with h | h <;> simp [h]) old
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr⟩
  all_goals done

/-- `pop`'s value table. -/
abbrev popVTable2 (P : Params) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (IV P).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem ∧ s.lr = ra ∧ Saved2 t0 s ∧
    (lb = "pop" ∨ (lb = "pop_done" ∧ PopVal P s.regs.X2.toBitVec))

/-- **`pop` in the value environment**: a non-null `top` it reads is a node
(`top_node`), so the link load is at a location of the layout; it writes the
link it read to `top`, and returns null or a node. -/
theorem pop_val2 (P : Params) :
    FunSpecPartialEnv (IV P) ((_root_.Executable.labels cenv).label "pop")
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem)
      (fun _ s _ s' _ => Saved2 s s' ∧ PopVal P s'.regs.X0.toBitVec) := by
  rintro ra t0 g ⟨hlr, hx0, hH⟩
  refine cfgEnv_partial_fun (p := popFrag) (popVTable2 P ra t0)
    (E := fun a s (_ : (IV P).State) => a = ra ∧ Saved2 t0 s ∧ PopVal P s.regs.X0.toBitVec) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) t0 g
    ⟨hx0, hH, hlr, Saved2.refl t0, .inl rfl⟩
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hd.loadInt_none (hp_top P) (n := 8) (by decide)
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, Treiber2ValLA, Treiber2ValVA]; done)
  case vc4 =>
    rename_i s σ0 v σ1 hz hld _
    simp at hz
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
      .inr ⟨rfl, .inl (by simpa [Reg64s.setXReg] using hz)⟩⟩, .inl (by decide)⟩)
  case vc9 =>
    rename_i s σ0 v σ1 hnz rng x4 σ2 hld hld2 _
    simp at hnz
    have hn := top_node (by simpa [hx0] using hld.1) hnz
    have hl8 := hd.loadInt_none (hp_link hn) (n := 8) (by decide)
    simp [hl8] at hld2
    obtain ⟨u, ⟨hu, -⟩, rfl⟩ := hld2
    rcases hn with hn | hn <;>
    · simp [hn, Treiber2ValLA] at hu
      simp [SharedEnv.inv, Reg64s.setXReg, hx0, hn, Treiber2ValLA]
      exact fun old _ => treiber2ValA_cas hu old
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, ⟨_, h⟩, _⟩ <;> omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp at hnz
    have hn := top_node (by simpa [hx0] using hld.1) hnz
    exact ⟨by simp [hx0], by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [Saved2, CalleeSaved] using hfr, .inr ⟨trivial, .inr (by simpa [Reg64s.setXReg] using hn)⟩⟩
  case vc1 =>
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
      by simpa [Reg64s.setXReg, PopVal] using hT⟩
  all_goals done

/-! ## `main` -/

/-- The tail's value table: the frame, `pop`'s result null or a node. -/
abbrev tailVTable2 (P : Params) (lo : BitVec 64) (n : Nat) : Label → MachineData → (IV P).State → Prop :=
  fun lb s _ => FrameOK P lo n s ∧ ((lb = "ret_pop" ∧ PopVal P s.regs.X0.toBitVec) ∨ lb = "empty")

set_option linter.unusedSectionVars false in
/-- **The tail**: the payload load of a popped node is at its data word. -/
theorem main_tail_val2 (P : Params) (lo : BitVec 64) (n : Nat) : ∀ s (σ : (IV P).State),
    FrameOK P lo n s → PopVal P s.regs.X0.toBitVec → Safely (cenv.instrStepEnv (IV P)) (fun x => x.1.2 = mainEnd2)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ hF hR
  refine cfgEnv_partial_fun (p := tailFrag2) (tailVTable2 P lo n) (E := fun a _ _ => a = mainEnd2) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) s σ ⟨hF, .inl ⟨rfl, hR⟩⟩
  cfg_cases_env [tailFrag2]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hF, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp; done)
  case vc1 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa [FrameOK, Slot] using hF, .inr rfl⟩, .inl (by decide)⟩)
  case vc3 =>
    rename_i s _ hnz _ _ _
    have hnz' : s.regs.X0.toBitVec ≠ 0 := by
      rw [Reg64s.getRegOrZr_X] at hnz; simpa [Reg64s.getXReg] using hnz
    rcases hT.resolve_left hnz' with h | h <;> simp [Reg64s.setXReg, h]
  case vc4 =>
    simpa [FrameOK, Slot] using hF
  case vc1 =>
    simpa using hF.2.1
  case vc2 =>
    rename_i _ _ _ hn _
    obtain ⟨-, -, ⟨u, hu, -⟩⟩ := hF
    simp [hu] at hn
  case vc3 =>
    rename_i s σ0 rng v σ1 hld _
    obtain ⟨-, -, ⟨u, hu, hv⟩⟩ := hF
    simp [hu] at hld
    obtain ⟨rfl, rfl⟩ := hld
    exact .inr (by simpa using hv)
  all_goals done

set_option linter.unusedSectionVars false in
/-- **The prefix**: the payload store is at the own node's data word (no
value condition there); the link goes to the private frame slot. -/
theorem main_prefix_val2 (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    ∀ s₀ g₀, ⦃ fun s (σ : (IV P).State) => MainPreR2 P w lo n s ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainPre2⟩ : EnvProgram (IV P))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ s.regs.X21.toBitVec = P.t ∧
        FrameOK P lo n s); fun _ _ _ => False ⦄ := by
  have hw' := pn_cases (P := P) hw
  intro s₀ g₀
  unfold mainPre2
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, ⟨hH, hS⟩, hal, hr⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hal]; done)
  all_goals simp at *
  all_goals have hsl := slot_isSome (‹MainPreR2 _ _ _ _ _›.2.2.2.2.1.2) ‹MainPreR2 _ _ _ _ _›.2.2.2.2.2.2
  case vc2 =>
    exact absurd ‹Mem.loadInt _ _ 8 = none› (Option.ne_none_iff_isSome.mpr hsl)
  case vc3 =>
    rename_i hhi _ _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc5 =>
    rw [h27]; rcases hw' with h | h <;> simp [h, Treiber2ValLA]
  case vc6 =>
    rename_i s σ0 rng dm σ1 rng2 dm2 σ2 hhi hst1 hst2 _
    obtain ⟨-, rfl, rfl⟩ := hst1.resolve_right fun ⟨hn, _⟩ => absurd hn (Option.ne_none_iff_isSome.mpr hsl)
    have hH' := hH.storeInt hsl
    have hx27 := hp_data (Eq.subst (motive := fun x => x = P.n 0 ∨ x = P.n 1) h27.symm hw')
    have hd4 := fun v => (hH' v).loadInt_none hx27 (n := 4) (by decide)
    simp [hd4] at hst2
    obtain ⟨rfl, -⟩ := hst2
    refine ⟨h21, h27, h21, ⟨hH' _, hS.storeInt _ _ _⟩, ?_, ?_⟩
    · simp [Reg64s.setXReg]
      exact aligned_sub16 _ hal
    · refine ⟨Int.ofBytes (Int.toBytes 8 s.regs.X30.toBitVec.toInt), ?_, ?_⟩
      · simp [Reg64s.setXReg]
        exact Mem.loadInt_storeInt _ _ _ _ (by decide)
      · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        simpa using h30

set_option linter.unusedSectionVars false in
theorem main_mid_val2 (P : Params) (lo : BitVec 64) (n : Nat) :
    ∀ s₀ g₀, ⦃ fun s (σ : (IV P).State) => (s.regs.X21.toBitVec = P.t ∧ FrameOK P lo n s) ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainMid⟩ : EnvProgram (IV P))
    ⦃ (fun _ s _ => s.regs.X0.toBitVec = P.t ∧ FrameOK P lo n s); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h21, hF⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  exact ⟨by simpa using h21, by simpa [FrameOK, Slot] using hF⟩

/-- **`pilot2` in the value environment**: a `PartialTripleEnv` of the whole
text from `MainPreR2`, through `push_val2` and `pop_val2`. -/
theorem main_val2 (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    PartialTripleEnv (IV P) (fun s _ => MainPreR2 P w lo n s) pilot2 (fun _ _ => True) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt pilot2 "main" = some ⟨"main", mainBody2, some "ret_pop"⟩ := by decide
  have hbody : PartialWpEnv (IV P) mainBody2 (fun s _ => FrameOK P lo n s ∧ PopVal P s.regs.X0.toBitVec)
      (fun _ _ _ => False) s σ := by
    have h1 := (main_prefix_val2 P w hw lo n s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
    rw [wpEnv_eq] at h1
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
    rintro s1 σ1 ⟨h0, h1, h21, hF⟩
    refine PartialWpEnv.call (push_val2 P w hw) fun ra => ⟨?_, ?_⟩
    · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
        by simpa [MachineData.setLr, Reg64s.setXReg] using h1, (hF.setLr ra).1.1⟩
    rintro s2 σ2 hsv
    have hF2 := (hF.setLr ra).saved hsv
    have h21' : s2.regs.X21.toBitVec = P.t := by
      obtain ⟨⟨-, -, f21, -⟩, -⟩ := hsv
      simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21
    have h2 := (main_mid_val2 P lo n s2 σ2).le_wp s2 σ2 ⟨⟨h21', hF2⟩, rfl, rfl⟩
    rw [wpEnv_eq] at h2
    refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
    rintro s3 σ3 ⟨h0', hF3⟩
    refine PartialWpEnv.call (pop_val2 P) fun ra => ⟨?_, ?_⟩
    · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
        (hF3.setLr ra).1.1⟩
    rintro s4 σ4 ⟨hsv', hR⟩
    exact PartialWpEnv.nil ⟨(hF3.setLr ra).saved hsv', hR⟩
  rw [← pilot2_placed.entry pc hpc]
  refine Safely.bind (hbody _ (pilot2_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hF, hR⟩ | hF)
  · dsimp only at ha hF hR
    rw [pilot2_placed.next _ _ _ hb rfl] at ha
    subst ha
    refine (main_tail_val2 P lo n s' g' hF hR).mono fun x hx => .inl ⟨?_, trivial⟩
    obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := pilot2) pilot2 [] 0 (by simp)
    rw [hx, pilot2_placed.entry _ hs0, Nat.zero_add] at *
    exact haf.symm
  · exact hF.elim

end Kraken.Promising.Lower.Pilot2
