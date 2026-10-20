/-
**Part 4: `main` from the function specifications.**
ISA: AArch64; environment: `counted (EW P w)` as in
`Lower/PilotSpecs.lean`.

`main`'s run is assembled without re-proving `push` or `pop`:

- the straight-line prefix (link save, bump allocation with the limit check,
  payload store, argument set-up) by one `vcgen` call (`main_prefix`);
- `bl push` and `bl pop` by `MachineWP.PartialWpEnv.call` through
  `push_spec` and `pop_spec` (`main_body`); the callee-saved frame carries
  `x19` (the saved link), `x21` (`&top`) and `dmem` across the calls;
- the tail behind `bl pop` (from the label `ret_pop`: null test, payload
  load, link restore, `ret`) by `cfgEnv_partial_fun` (`main_tail`);
- `main_run`: the run from `main` to the return into the runtime's address
  (the end of the text) with `DnD` (the treiber2 data post);
  `main_partialTripleEnv`: the same as a `PartialTripleEnv` of the whole
  text, the form `qa64CAdj_of_partialTripleEnv` takes.
-/
import Kraken.Promising.Lower.PilotSpecs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `main`'s straight-line prefix, up to `bl push`. -/
def mainPre : Program := parseAArch64("
    mov x19, x30
    mov x1, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi oom
    str w9, [x1]
    mov x0, x21
")

/-- The argument set-up between the calls. -/
def mainMid : Program := parseAArch64("
    mov x0, x21
")

/-- `main`'s first block: the prefix, `bl push`, the set-up, `bl pop`. -/
def mainBody : Program :=
  mainPre ++ (Directive.instr ⟨.W64, .BL (.label "push")⟩ :: (mainMid ++ [Directive.instr ⟨.W64, .BL (.label "pop")⟩]))

/-- The tail behind `bl pop`. -/
def tailFrag : Program := parseAArch64("
ret_pop:
    cbz x0, empty
    mov x10, x0
    ldr w11, [x10]
empty:
    mov x30, x19
    ret
")

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot)]

local instance pilot.env' : CodeEnv := ⟨layout pilot⟩

/-- The end of the text: where the runtime's return address points. -/
abbrev mainEnd : Int64 := (layout pilot).addrOf pilot.length

/-! ## The tail -/

/-- At `ret_pop`: the saved link is the end of the text, no `dmem` word, the
result of `pop` in `x0`. -/
def TailPre (P : Params) (w : Nat) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s ∧ PopRes P w s.regs.X0.toBitVec σ.1

/-- The tail's table. -/
abbrev tailTable (P : Params) (w : Nat) : Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "ret_pop" ∧ PopRes P w s.regs.X0.toBitVec σ.1) ∨
      (lb = "empty" ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1))

/-- **The tail**: from `ret_pop` to the return at the end of the text, with
`DnD`. -/
theorem main_tail (P : Params) (w : Nat) : ∀ s σ, TailPre P w s σ →
    Safely (cenv.instrStepEnv (SharedEnv.counted (EW P w)))
      (fun x => x.1.2 = mainEnd ∧ DnD P w x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ ⟨h19, ⟨hd8, hd4⟩, hR⟩
  refine cfgEnv_partial_fun (p := tailFrag) (tailTable P w)
    (E := fun a (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) => a = mainEnd ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot_placed (by decide)) s σ ⟨h19, hd8, hd4, .inl ⟨rfl, hR⟩⟩
  cfg_cases_env [tailFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨h19, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [h19, hd8, hd4]; done)
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    have hz' : s.regs.X0.toBitVec = 0 := by
      rw [Reg64s.getRegOrZr_X] at hz; simpa [Reg64s.getXReg] using hz
    unfold PopRes at hT; rw [hz'] at hT
    obtain ⟨-, hD⟩ | ⟨hne, -⟩ := hT
    · exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa using h19, by simpa using hd8, by simpa using hd4,
        .inr ⟨rfl, (hD _ _).fence hf.1⟩⟩, .inl (by decide)⟩)
    · exact absurd rfl hne
  case vc4 =>
    rename_i s σ0 hnz σ1 σ2 rng v σ3 hf1 hf2 hld _
    have hnz' : s.regs.X0.toBitVec ≠ 0 := by
      rw [Reg64s.getRegOrZr_X] at hnz; simpa [Reg64s.getXReg] using hnz
    rcases hT with ⟨h0, -⟩ | ⟨-, hB⟩
    · exact absurd h0 hnz'
    simp [hd4] at hld
    obtain ⟨u, h3, rfl⟩ := hld
    have hfin := vc_ldr_data _ ((hB.fence hf1.1).fence hf2.1) u σ3.1 (by simpa using h3.1)
    refine ⟨by simpa using h19, by simpa using hd8, by simpa using hd4, .inr ⟨by first | rfl | trivial, ?_⟩⟩
    simpa using hfin
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    exact .inr ⟨by simpa using h19, by simpa using (hT.fence hf1.1).fence hf2.1⟩
  all_goals done

/-! ## The prefix -/

/-- At `main`: the runtime's return address (the end of the text) in `x30`,
`&top` in `x21`, the bump pointer `x27` at this thread's node with room below
the limit `x28`, the payload in `w9`, no `dmem` word, `Pu0`. -/
def MainPre (P : Params) (w : Nat) (d9 : BitVec 32) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = P.t ∧ s.regs.X27.toBitVec = P.n w ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ s.regs.X9.toBitVec.setWidth 32 = d9 ∧ NoDmem s ∧ Pu0 P w σ.1

/-- At `bl push`: `push`'s arguments, the saved link in `x19`, `&top` in `x21`. -/
def Mid1 (P : Params) (w : Nat) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
    s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Pu P w σ.1

omit [Executable.ValidLayout (layout pilot)] in
/-- **The prefix** by `vcgen`: the limit check never branches to `oom`. -/
theorem main_prefix (P : Params) (w : Nat) (d9 : BitVec 32) (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) :
    ∀ s₀ g₀, ⦃ fun s σ => MainPre P w d9 s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainPre⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => Mid1 P w s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainPre
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, h9, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals simp [Mid1, NoDmem] at *
  case vc1 =>
    rename_i s σ0 σ1 σ2 σ3 σ4 σ5 _ _ _ _ _ hhi _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc3 =>
    rename_i s σ0 σ1 σ2 σ3 σ4 σ5 rng hf1 hf2 hf3 hf4 hf5 hhi hdm _
    have hP := ((((hT.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1).fence hf5.1
    have h := (vc_data_str _ hP (BitVec.setWidth 128 d9) (hD _ (by simp))).1
    rw [h27, h9]; simpa [Params.dd] using h
  case vc4 =>
    rename_i s σ0 σ1 σ2 σ3 σ4 σ5 rng dm σ6 σ7 hf1 hf2 hf3 hf4 hf5 hf6 hhi hst _
    have hP := ((((hT.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1).fence hf5.1
    simp [hd4] at hst
    obtain ⟨rfl, hso, -⟩ := hst
    have hP' : Pu P w σ6.1 := by
      rcases hso with h | h <;>
        exact (vc_data_str _ hP (BitVec.setWidth 128 d9) (hD _ (by simp))).2 _ σ6.1
          (by simpa [Params.dd, h27, h9] using h)
    exact ⟨h21, h27, h30, h21, ⟨hd8, hd4⟩, hP'.fence hf6.1⟩
  all_goals done


/-- Between the calls: the saved link in `x19`, `&top` in `x21`, no `dmem`
word, `Po`. -/
def Mid2 (P : Params) (w : Nat) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Po P w σ.1

omit [Executable.ValidLayout (layout pilot)] in
/-- **The argument set-up for `pop`** by `vcgen`. -/
theorem main_mid (P : Params) (w : Nat) :
    ∀ s₀ g₀, ⦃ fun s σ => Mid2 P w s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainMid⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => s.regs.X0.toBitVec = P.t ∧ Mid2 P w s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h19, h21, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  all_goals simp [Mid2, NoDmem] at *
  rename_i s σ0 σ1 hf _
  exact ⟨h21, h19, h21, ⟨hd8, hd4⟩, hT.fence hf.1⟩

/-- **`main`'s first block** (`main` up to `ret_pop`): the prefix, then
`bl push` and `bl pop` through their partial specifications. -/
theorem main_body (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32)
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) (s : MachineData)
    (σ : (SharedEnv.counted (EW P w)).State) (hpre : MainPre P w d9 s σ) :
    PartialWpEnv (SharedEnv.counted (EW P w)) mainBody (TailPre P w) (fun _ _ _ => False) s σ := by
  have h1 := (main_prefix P w d9 hD s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  rintro s1 σ1 ⟨h0, h1, h19, h21, ⟨hd8, hd4⟩, hP⟩
  refine PartialWpEnv.call (push_spec P w hL hw) fun ra => ⟨?_, ?_⟩
  · refine ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h1, ⟨by simpa [MachineData.setLr] using hd8,
      by simpa [MachineData.setLr] using hd4⟩, hP⟩
  rintro s2 σ2 ⟨⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩, hPo⟩
  have h2 := (main_mid P w s2 σ2).le_wp s2 σ2 ⟨⟨by simpa [f19, MachineData.setLr, Reg64s.setXReg] using h19,
    by simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21,
    ⟨by simpa [fdm, MachineData.setLr] using hd8, by simpa [fdm, MachineData.setLr] using hd4⟩, hPo⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
  rintro s3 σ3 ⟨h0', h19', h21', ⟨hd8', hd4'⟩, hPo'⟩
  refine PartialWpEnv.call (pop_spec P w hw) fun ra => ⟨?_, ?_⟩
  · refine ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
      ⟨by simpa [MachineData.setLr] using hd8', by simpa [MachineData.setLr] using hd4'⟩, hPo'⟩
  rintro s4 σ4 ⟨⟨g19, -, -, -, -, -, -, -, -, -, gdm⟩, hR⟩
  exact PartialWpEnv.nil ⟨by simpa [g19, MachineData.setLr, Reg64s.setXReg] using h19',
    ⟨by simpa [gdm, MachineData.setLr] using hd8', by simpa [gdm, MachineData.setLr] using hd4'⟩, hR⟩


/-! ## The run of `main` -/

/-- **`main`'s run**: from `main` to the return into the end of the text,
with `DnD`. -/
theorem main_run (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32)
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) (s : MachineData)
    (σ : (SharedEnv.counted (EW P w)).State) (hpre : MainPre P w d9 s σ) :
    Safely (cenv.instrStepEnv (SharedEnv.counted (EW P w)))
      (fun x => x.1.2 = mainEnd ∧ DnD P w x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "main"), σ) := by
  have hb : Program.blockAt pilot "main" = some ⟨"main", mainBody, some "ret_pop"⟩ := by decide
  refine Safely.bind (main_body P w hL hw d9 hD s σ hpre _ (pilot_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hT⟩ | hF)
  · dsimp only at ha hT
    rw [pilot_placed.next _ _ _ hb rfl] at ha
    subst ha
    exact main_tail P w s' g' hT
  · exact hF.elim

/-- **`main` as a partial triple of the whole text**: from `MainPre`, every
run ends at the end of the text with `DnD`, or runs forever; no other exit. -/
theorem main_partialTripleEnv (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32)
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) :
    PartialTripleEnv (SharedEnv.counted (EW P w)) (MainPre P w d9) pilot
      (fun s σ => DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := pilot) pilot [] 0 (by simp)
  rw [← pilot_placed.entry pc hpc]
  refine (main_run P w hL hw d9 hD s σ hpre).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
  rw [hx, pilot_placed.entry _ hs0]
  rw [Nat.zero_add] at haf
  exact haf.symm

end Kraken.Promising.Lower.Pilot
