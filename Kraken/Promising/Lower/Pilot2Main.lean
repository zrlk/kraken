/-
**Part 4: `main` with its `dmem` frame, from the
function specifications.** Environment: `counted (EWV P w)`.

As `Lower/PilotMain.lean`, with the link on the stack: the prologue writes the
mapped slot `[sp - 16, sp - 8)` (a private store, no event), establishing
`FrameOK` (stack interface, `sp` aligned, the slot holding the return address);
`Saved2` carries it across `bl push`/`bl pop` (`push_spec2`/`pop_spec2`); the
tail loads the popped node's payload (a heap address by `PopRes2`), and the
epilogue reads the slot back from `dmem` before `ret`.
-/
import Kraken.Promising.Lower.Pilot2Specs
import Kraken.Promising.Lower.PilotMain

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved PopRes mainMid)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `main`'s straight-line prefix, up to `bl push`. -/
def mainPre2 : Program := parseAArch64("
    str x30, [sp, #-16]!
    mov x1, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi oom
    str w9, [x1]
    mov x0, x21
")

/-- `main`'s first block. -/
def mainBody2 : Program :=
  mainPre2 ++ (Directive.instr ⟨.W64, .BL (.label "push")⟩ :: (mainMid ++ [Directive.instr ⟨.W64, .BL (.label "pop")⟩]))

/-- The tail behind `bl pop`. -/
def tailFrag2 : Program := parseAArch64("
ret_pop:
    cbz x0, empty
    mov x10, x0
    ldr w11, [x10]
empty:
    ldr x30, [sp], #16
    ret
")

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

local instance pilot2.env' : CodeEnv := ⟨layout pilot2⟩

/-- The end of the text: where the runtime's return address points. -/
abbrev mainEnd2 : Int64 := (layout pilot2).addrOf pilot2.length

/-- The slot at `sp` holds the runtime's return address. -/
def Slot (s : MachineData) : Prop :=
  ∃ v, Mem.loadInt s.dmem s.regs.SP.toBitVec 8 = some v ∧ Int64.ofBitVec (BitVec.ofInt 64 v) = mainEnd2

/-- **`main`'s frame invariant** between its prologue and epilogue. -/
def FrameOK (P : Params) (lo : BitVec 64) (n : Nat) (s : MachineData) : Prop :=
  StackOK P lo n s.dmem ∧ s.regs.SP.toBitVec % 16#64 = 0 ∧ Slot s

omit [Executable.ValidLayout (layout pilot2)] in
/-- A callee keeping `Saved2` keeps the frame. -/
theorem FrameOK.saved {P : Params} {lo : BitVec 64} {n : Nat} {s t : MachineData} (h : FrameOK P lo n s)
    (hs : Saved2 s t) : FrameOK P lo n t := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hd⟩, hsp⟩ := hs
  simpa [FrameOK, Slot, hd, hsp] using h

omit [Executable.ValidLayout (layout pilot2)] in
theorem FrameOK.setLr {P : Params} {lo : BitVec 64} {n : Nat} {s : MachineData} (h : FrameOK P lo n s)
    (ra : Int64) : FrameOK P lo n (s.setLr ra) := by
  simpa [FrameOK, Slot, MachineData.setLr] using h

/-! ## The tail -/

/-- At `ret_pop`: the frame, `pop`'s result in `x0`. -/
def TailPre2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  FrameOK P lo n s ∧ PopRes2 P w s.regs.X0.toBitVec σ.1

/-- The tail's table. -/
abbrev tailTable2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) :
    Label → MachineData → (SharedEnv.counted (EWV P w)).State → Prop :=
  fun lb s σ => FrameOK P lo n s ∧
    ((lb = "ret_pop" ∧ PopRes2 P w s.regs.X0.toBitVec σ.1) ∨
      (lb = "empty" ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1))

/-- **The tail**: from `ret_pop` to the return at the end of the text. -/
theorem main_tail2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) : ∀ s σ, TailPre2 P w lo n s σ →
    Safely (cenv.instrStepEnv (SharedEnv.counted (EWV P w)))
      (fun x => x.1.2 = mainEnd2 ∧ DnD P w x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ ⟨hF, hR⟩
  refine cfgEnv_partial_fun (p := tailFrag2) (tailTable2 P w lo n)
    (E := fun a (s : MachineData) (σ : (SharedEnv.counted (EWV P w)).State) =>
      a = mainEnd2 ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) s σ ⟨hF, .inl ⟨rfl, hR⟩⟩
  cfg_cases_env [tailFrag2]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hF, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
    SharedEnv.counted_step, SharedEnv.counted_ok, and_true] at *
  all_goals have hH := hF.1.1
  all_goals try (simp; done)
  case vc1 =>
    rename_i s σ0 hz σ1 hf _
    have hz' : s.regs.X0.toBitVec = 0 := by
      rw [Reg64s.getRegOrZr_X] at hz; simpa [Reg64s.getXReg] using hz
    obtain ⟨hP, -⟩ := hT
    unfold PopRes at hP; rw [hz'] at hP
    obtain ⟨-, hD⟩ | ⟨hne, -⟩ := hP
    · exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simpa [FrameOK, Slot] using hF,
        .inr ⟨rfl, (hD _ _).fence hf.1⟩⟩, .inl (by decide)⟩)
    · exact absurd rfl hne
  case vc4 =>
    rename_i s σ0 hnz σ1 σ2 rng v σ3 hf1 hf2 hld _
    have hnz' : s.regs.X0.toBitVec ≠ 0 := by
      rw [Reg64s.getRegOrZr_X] at hnz; simpa [Reg64s.getXReg] using hnz
    have hl4 := hH.loadInt_none (hp_data (hT.2 hnz')) (n := 4) (by decide)
    rcases hT.1 with ⟨h0, -⟩ | ⟨-, hB⟩
    · exact absurd h0 hnz'
    simp [hl4] at hld
    obtain ⟨u, h3, rfl⟩ := hld
    have hfin := vc_ldr_data _ ((hB.fence hf1.1).fence hf2.1) u σ3.1 (by simpa using h3.1.1)
    refine ⟨by simpa [FrameOK, Slot] using hF, .inr ⟨by first | rfl | trivial, ?_⟩⟩
    simpa using hfin
  case vc1 =>
    simpa using hF.2.1
  case vc3 =>
    rename_i s σ0 rng v σ1 σ2 hld hf _
    obtain ⟨-, -, ⟨u, hu, hv⟩⟩ := hF
    simp [hu] at hld
    obtain ⟨rfl, rfl⟩ := hld
    refine .inr ⟨by simpa using hv, by simpa using hT.fence hf.1⟩
  all_goals done

/-! ## The prefix -/

/-- At `main`: as `Pilot.MainPre`, with the stack interface for `[lo, lo + n)`
in place of `NoDmem`, `sp` 16-byte aligned and the frame slot `[sp - 16, sp - 8)`
inside the region. -/
def MainPre2 (P : Params) (w : Nat) (d9 : BitVec 32) (lo : BitVec 64) (n : Nat) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd2 ∧ s.regs.X21.toBitVec = P.t ∧ s.regs.X27.toBitVec = P.n w ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ s.regs.X9.toBitVec.setWidth 32 = d9 ∧
    StackOK P lo n s.dmem ∧ s.regs.SP.toBitVec % 16#64 = 0 ∧ (s.regs.SP.toBitVec - 16#64 - lo).toNat + 8 ≤ n ∧
    Pu0 P w σ.1

/-- At `bl push`: `push`'s arguments, `&top` in `x21`, the frame. -/
def Mid1_2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ s.regs.X21.toBitVec = P.t ∧ FrameOK P lo n s ∧
    Pu P w σ.1

omit layout [Executable.ValidLayout (layout pilot2)] in
/-- `sp - 16` keeps the 16-byte alignment. -/
theorem aligned_sub16 (x : BitVec 64) (hx : x % 16#64 = 0#64) :
    (x + 18446744073709551600#64) % 16#64 = 0#64 := by
  have hx' : x.toNat % 16 = 0 := by
    have := congrArg BitVec.toNat hx
    rwa [BitVec.toNat_umod] at this
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_add]
  have hd : (16 : Nat) ∣ 2 ^ 64 := ⟨2 ^ 60, by rw [show 64 = 4 + 60 from rfl, Nat.pow_add]⟩
  show (x.toNat + 18446744073709551600) % 2 ^ 64 % 16 = 0
  rw [Nat.mod_mod_of_dvd _ hd, Nat.add_mod, hx']

omit layout [Executable.ValidLayout (layout pilot2)] in
/-- The frame slot `[sp - 16, sp - 8)` is in the mapped region. -/
theorem slot_isSome {lo : BitVec 64} {n : Nat} {s : MachineData} (hS : StackFull lo n s.dmem)
    (hr : (s.regs.SP.toBitVec - 16#64 - lo).toNat + 8 ≤ n) :
    (Mem.loadInt s.dmem (s.regs.SP.toBitVec + 18446744073709551600#64) 8).isSome = true := by
  rw [show s.regs.SP.toBitVec + 18446744073709551600#64 = s.regs.SP.toBitVec - 16#64 by bv_omega]
  exact hS.loadInt_isSome hr

set_option linter.unusedSectionVars false in
/-- **The prefix** by `vcgen`: the link goes to the private frame slot, the
payload store to the shared node; the limit check never branches to `oom`. -/
theorem main_prefix2 (P : Params) (w : Nat) (hw : w < 2) (d9 : BitVec 32) (lo : BitVec 64) (n : Nat)
    (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) :
    ∀ s₀ g₀, ⦃ fun s σ => MainPre2 P w d9 lo n s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainPre2⟩ : EnvProgram (SharedEnv.counted (EWV P w)))
    ⦃ (fun _ s σ => Mid1_2 P w lo n s σ); fun _ _ _ => False ⦄ := by
  have hw' := pn_cases (P := P) hw
  intro s₀ g₀
  unfold mainPre2
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, h9, ⟨hH, hS⟩, hal, hr, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
    SharedEnv.counted_step, SharedEnv.counted_ok, and_true] at *
  all_goals try (simp [hal]; done)
  all_goals simp [Mid1_2] at *
  all_goals have hsl := slot_isSome (‹MainPre2 _ _ _ _ _ _ _›.2.2.2.2.2.1.2) ‹MainPre2 _ _ _ _ _ _ _›.2.2.2.2.2.2.2.1
  case vc2 =>
    exact absurd ‹Mem.loadInt _ _ 8 = none› (Option.ne_none_iff_isSome.mpr hsl)
  case vc3 =>
    rename_i hhi _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc5 =>
    rename_i dm σ1 σ2 σ3 σ4 σ5 rng2 hf1 hf2 hf3 hf4 _ hhi hn4 hst1
    obtain ⟨-, -, rfl⟩ := hst1.resolve_right fun ⟨hn, _⟩ => absurd hn (Option.ne_none_iff_isSome.mpr hsl)
    have hP := (((hT.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    have h := (vc_data_str _ hP (BitVec.setWidth 128 d9) (hD _ (by simp))).1
    rw [h27, h9]; simpa [Params.dd] using h
  case vc6 =>
    rename_i s σ0 rng dm σ1 σ2 σ3 σ4 σ5 rng2 dm2 σ6 σ7 hf1 hf2 hf3 hf4 hf5 _ hhi hst1 hst2
    obtain ⟨-, rfl, rfl⟩ := hst1.resolve_right fun ⟨hn, _⟩ => absurd hn (Option.ne_none_iff_isSome.mpr hsl)
    have hP := (((hT.fence hf1.1).fence hf2.1).fence hf3.1).fence hf4.1
    have hH' := hH.storeInt hsl
    have hx27 := hp_data (Eq.subst (motive := fun x => x = P.n 0 ∨ x = P.n 1) h27.symm hw')
    have hd4 := fun v => (hH' v).loadInt_none hx27 (n := 4) (by decide)
    simp [hd4] at hst2
    obtain ⟨rfl, hso, -⟩ := hst2
    have hP' : Pu P w σ6.1 := by
      rcases hso with h | h <;>
        exact (vc_data_str _ hP (BitVec.setWidth 128 d9) (hD _ (by simp))).2 _ σ6.1
          (by simpa [Params.dd, h27, h9] using h)
    refine ⟨h21, h27, h21, ⟨⟨hH' _, hS.storeInt _ _ _⟩, ?_, ?_⟩, hP'.fence hf5.1⟩
    · simp [Reg64s.setXReg]
      exact aligned_sub16 _ hal
    · refine ⟨Int.ofBytes (Int.toBytes 8 s.regs.X30.toBitVec.toInt), ?_, ?_⟩
      · simp [Reg64s.setXReg]
        exact Mem.loadInt_storeInt _ _ _ _ (by decide)
      · rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        simpa using h30

/-- Between the calls: `&top` in `x21`, the frame, pushed (`Po`). -/
def Mid2_2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  s.regs.X21.toBitVec = P.t ∧ FrameOK P lo n s ∧ Po P w σ.1

set_option linter.unusedSectionVars false in
/-- **The argument set-up for `pop`** by `vcgen`. -/
theorem main_mid2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) :
    ∀ s₀ g₀, ⦃ fun s σ => Mid2_2 P w lo n s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainMid⟩ : EnvProgram (SharedEnv.counted (EWV P w)))
    ⦃ (fun _ s σ => s.regs.X0.toBitVec = P.t ∧ Mid2_2 P w lo n s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainMid
  vcgen
  all_goals obtain ⟨⟨h21, hF, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_valsEnv, fenceMono_le_envGCAdj] at *
  rename_i s σ0 σ1 hf _
  exact ⟨by simpa using h21, by simpa using h21, by simpa [FrameOK, Slot] using hF, hT.fence hf.1⟩

/-- **`main`'s first block** (`main` up to `ret_pop`): the prefix, then
`bl push` and `bl pop` through `push_spec2`/`pop_spec2`; `Saved2` carries the
frame across both calls. -/
theorem main_body2 (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32) (lo : BitVec 64)
    (n : Nat) (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) (hpre : MainPre2 P w d9 lo n s σ) :
    PartialWpEnv (SharedEnv.counted (EWV P w)) mainBody2 (TailPre2 P w lo n) (fun _ _ _ => False) s σ := by
  have h1 := (main_prefix2 P w hw d9 lo n hD s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  rintro s1 σ1 ⟨h0, h1, h21, hF, hP⟩
  refine PartialWpEnv.call (push_spec2 P w hL hw lo n) fun ra => ⟨?_, ?_⟩
  · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0,
      by simpa [MachineData.setLr, Reg64s.setXReg] using h1, (hF.setLr ra).1, hP⟩
  rintro s2 σ2 ⟨hsv, -, hPo⟩
  have hF2 := (hF.setLr ra).saved hsv
  have h21' : s2.regs.X21.toBitVec = P.t := by
    obtain ⟨⟨-, -, f21, -⟩, -⟩ := hsv
    simpa [f21, MachineData.setLr, Reg64s.setXReg] using h21
  have h2 := (main_mid2 P w lo n s2 σ2).le_wp s2 σ2 ⟨⟨h21', hF2, hPo⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
  rintro s3 σ3 ⟨h0', -, hF3, hPo'⟩
  refine PartialWpEnv.call (pop_spec2 P w hw lo n) fun ra => ⟨?_, ?_⟩
  · exact ⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr, Reg64s.setXReg] using h0',
      (hF3.setLr ra).1, hPo'⟩
  rintro s4 σ4 ⟨hsv', -, hR⟩
  exact PartialWpEnv.nil ⟨(hF3.setLr ra).saved hsv', hR⟩

/-! ## The run of `main` -/

/-- **`main`'s run**: from `main` to the return into the end of the text,
with `DnD`. -/
theorem main_run2 (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32) (lo : BitVec 64)
    (n : Nat) (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) (s : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) (hpre : MainPre2 P w d9 lo n s σ) :
    Safely (cenv.instrStepEnv (SharedEnv.counted (EWV P w)))
      (fun x => x.1.2 = mainEnd2 ∧ DnD P w x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "main"), σ) := by
  have hb : Program.blockAt pilot2 "main" = some ⟨"main", mainBody2, some "ret_pop"⟩ := by decide
  refine Safely.bind (main_body2 P w hL hw d9 lo n hD s σ hpre _ (pilot2_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hT⟩ | hF)
  · dsimp only at ha hT
    rw [pilot2_placed.next _ _ _ hb rfl] at ha
    subst ha
    exact main_tail2 P w lo n s' g' hT
  · exact hF.elim

/-- **`main` as a partial triple of the whole text**: from `MainPre2`, every
run ends at the end of the text with `DnD`, or runs forever. -/
theorem main_partialTripleEnv2 (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d9 : BitVec 32)
    (lo : BitVec 64) (n : Nat) (hD : ∀ d : Val, BitVec.setWidth 32 d = d9 → P.D w d) :
    PartialTripleEnv (SharedEnv.counted (EWV P w)) (MainPre2 P w d9 lo n) pilot2
      (fun s σ => DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := pilot2) pilot2 [] 0 (by simp)
  rw [← pilot2_placed.entry pc hpc]
  refine (main_run2 P w hL hw d9 lo n hD s σ hpre).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
  rw [hx, pilot2_placed.entry _ hs0]
  rw [Nat.zero_add] at haf
  exact haf.symm

end Kraken.Promising.Lower.Pilot2
