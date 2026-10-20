/-
**Parts 2–3: the function specifications in
`publishP`, and `main` from them.** ISA: AArch64;
machine: the executable machine's per-thread environment semantics, partial
correctness; env `counted (EW P w)` (the allocation pilot's).

- `pushp_spec`: **`pushp`'s fragment specification from `push`'s**
  (`Pilot.pushFrag_spec`, used as is, not re-proved) by `FragSpecEnvL.tail`:
  same pre (`Pu`) and post (`Po`). The barrier's VCs close by
  `SharedEnv.FenceMono.ok_fence`/`le_of_fence_step` (`Lower/FenceMono.lean`)
  and `Pu.fence`: `dmb ishst` raises `vwNew` (and sets nothing the `Pu`
  facts read), so the push protocol is untouched.
- `alloc_spec`, `pushp_spec_at`, `pop_spec`: the fragment specifications
  (`Alloc.allocFrag_spec`, `pushp_spec`, `Pilot.popFrag_spec`) at the
  laid-out `publishP`, one line each.
- `main`: the allocation pilot's proof (`Lower/AllocMain.lean`) at `publishP` (`bl pushp`
  for `bl push`). The allocation pilot's block lemmas are tied to `allocP`'s placement and
  end address, so they are restated here with the same proofs.
-/
import Kraken.Promising.Lower.PublishProg
import Kraken.Promising.Lower.FragSpecCalls
import Kraken.Promising.Lower.FenceMono

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Publish

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem PopRes PopRes.fence tailFrag mainMid pushFrag popFrag PushPre
  PushPost PopPre PopPost pushFrag_spec popFrag_spec)
open Kraken.Promising.Lower.Alloc (mainInit mainSave pu_of_pu2 AllocPre AllocPost allocFrag allocFrag_spec)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `main`'s first block, up to `ret_pop`: the allocation pilot's, calling `pushp`. -/
def mainBody : Program :=
  mainSave ++ (Directive.instr ⟨.W64, .BL (.label "alloc")⟩ :: (mainInit ++
    (Directive.instr ⟨.W64, .BL (.label "pushp")⟩ :: (mainMid ++ [Directive.instr ⟨.W64, .BL (.label "pop")⟩]))))

/-! ## `pushp` -/

/-- `Pu` is monotone in the counted env's fence order. -/
theorem pu_le {P : Params} {w : Nat} {σ σ' : (SharedEnv.counted (EW P w)).State}
    (h : SharedEnv.FenceMono.le σ σ') (hp : Pu P w σ.1) : Pu P w σ'.1 := by
  simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at h
  exact hp.fence h.1

/-- `pushp`'s body: WeakCore's `publish` barrier, then the tail call. -/
def pushpBody : Program := parseAArch64("
    dmb ishst
    b push
")

/-- `pushp`'s text, as a fragment of `publishP`. -/
def pushpFrag : Program := parseAArch64("
pushp:
    dmb ishst
    b push
")

/-- **`pushp`'s specification**, from `push`'s by `FragSpecEnvL.tail`: same
pre and post; placed by `[pushpFrag, pushFrag]`. -/
theorem pushp_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FragSpecEnvL (SharedEnv.counted (EW P w)) [pushpFrag, pushFrag] "pushp" (PushPre P w) (PushPost P w) := by
  refine FragSpecEnvL.tail (pushFrag_spec P w hL hw).toL (blk := ⟨"pushp", pushpBody, none⟩) (by decide) ?_
  intro _ ra t g
  unfold pushpBody
  dsimp only
  vcgen
  · exact SharedEnv.FenceMono.ok_fence _ _
  · rename_i s σ hpre σ1 hst σ2 hle
    obtain ⟨⟨hlr, hx0, hx1, hnd, hPu⟩, hs, hg⟩ := hpre
    subst hs hg
    exact .inl ⟨rfl, ⟨hlr, hx0, hx1, hnd, pu_le hle (pu_le (SharedEnv.FenceMono.le_of_fence_step hst) hPu)⟩,
      fun _ _ h => h⟩

/-! ## At the laid-out `publishP` -/

variable [layout : _root_.Layout] [Executable.ValidLayout (layout publishP)]

local instance publishP.env : CodeEnv := ⟨layout publishP⟩

/-- The end of the text (the runtime's return address). -/
abbrev mainEnd : Int64 := (layout publishP).addrOf publishP.length

omit layout [Executable.ValidLayout (layout publishP)] in
theorem publishP_wf : Program.WF publishP := by decide

theorem publishP_placed : Program.Placed publishP "main" :=
  Program.placed_of_layout publishP_wf rfl (by decide)

/-- `alloc`'s specification at `publishP`, in every environment. -/
theorem alloc_spec (env : SharedEnv) [env.FenceMono] (R : env.State → Prop)
    (hR : ∀ g g', R g → SharedEnv.FenceMono.le g g' → R g') (n : BitVec 64) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label "alloc") (AllocPre env R n)
      (AllocPost env R n) :=
  (allocFrag_spec env R hR n).of_placed publishP_placed (by decide)

/-- `pushp`'s specification at `publishP`. -/
theorem pushp_spec_at (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pushp") (PushPre P w)
      (PushPost P w) :=
  (pushp_spec P w hL hw).of_placed publishP_placed (by decide)

/-- `pop`'s specification at `publishP`. -/
theorem pop_spec (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) :=
  (popFrag_spec P w hw).of_placed publishP_placed (by decide)


/-! ## The tail (the first lowering pilot's) -/

/-- The tail's table. -/
abbrev tailTable (P : Params) (w : Nat) : Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "ret_pop" ∧ PopRes P w s.regs.X0.toBitVec σ.1) ∨
      (lb = "empty" ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1))

/-- **The tail**: from `ret_pop` to the return at the end of the text, `DnD`. -/
theorem main_tail (P : Params) (w : Nat) : ∀ s σ, Int64.ofBitVec s.regs.X19.toBitVec = mainEnd → NoDmem s →
    PopRes P w s.regs.X0.toBitVec σ.1 →
    Safely (cenv.instrStepEnv (SharedEnv.counted (EW P w)))
      (fun x => x.1.2 = mainEnd ∧ DnD P w x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1)
      ((s, (_root_.Executable.labels cenv).label "ret_pop"), σ) := by
  rintro s σ h19 ⟨hd8, hd4⟩ hR
  refine cfgEnv_partial_fun (p := tailFrag) (tailTable P w)
    (E := fun a (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) =>
      a = mainEnd ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE publishP_placed (by decide)) s σ ⟨h19, hd8, hd4, .inl ⟨rfl, hR⟩⟩
  cfg_cases_env [tailFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨h19, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step, SharedEnv.counted_ok] at *
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

/-! ## The straight-line blocks -/

/-- At `main`: `x30` the end, `x21 = &top`, `x27 = P.n w` with room, payload `w20`, `Pu0`. -/
def MainPre (P : Params) (w : Nat) (d : BitVec 32) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = P.t ∧ s.regs.X27.toBitVec = P.n w ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ s.regs.X20.toBitVec.setWidth 32 = d ∧ NoDmem s ∧ Pu0 P w σ.1

omit [Executable.ValidLayout (layout publishP)] in
/-- The link save. -/
theorem main_save (P : Params) (w : Nat) (d : BitVec 32) :
    ∀ s₀ g₀, ⦃ fun s σ => MainPre P w d s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainSave⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = P.t ∧
        s.regs.X27.toBitVec = P.n w ∧ s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧
        s.regs.X20.toBitVec.setWidth 32 = d ∧ NoDmem s ∧ Pu0 P w σ.1); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainSave
  vcgen
  all_goals obtain ⟨⟨h30, h21, h27, hlim, h20, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj] at *
  all_goals simp [NoDmem] at *
  rename_i s σ0 σ1 hf _
  exact ⟨h30, h21, h27, hlim, h20, ⟨hd8, hd4⟩, hT.fence hf.1⟩

/-- At `bl push`: `push`'s arguments, the saved link, `&top`, `Pu`. -/
def Mid1 (P : Params) (w : Nat) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
    s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Pu P w σ.1

omit [Executable.ValidLayout (layout publishP)] in
/-- **The initial stores** of `new` on the fresh node, and `push`'s arguments. -/
theorem main_init (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) :
    ∀ s₀ g₀, ⦃ fun s σ => (s.regs.X0.toBitVec = P.n w ∧ Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧
        s.regs.X20.toBitVec.setWidth 32 = d ∧ s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Pu0 P w σ.1) ∧
        s = s₀ ∧ σ = g₀ ⦄
      (⟨mainInit⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => Mid1 P w s σ); fun _ _ _ => False ⦄ := by
  intro s₀ g₀
  unfold mainInit
  vcgen
  all_goals obtain ⟨⟨h0, h19, h20, h21, ⟨hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals simp [Mid1, NoDmem] at *
  case vc2 =>
    rw [h0, h20]; simpa [Params.dd] using (vc_data_str _ hT (BitVec.setWidth 128 d) (hD _ (by simp))).1
  case vc4 =>
    rename_i s σ0 rng dm σ1 rng2 _ hst1 _
    simp [hd4] at hst1
    obtain ⟨rfl, hso, -⟩ := hst1
    have hP : Pu P w σ1.1 := by
      rcases hso with h | h <;> exact (vc_data_str _ hT (BitVec.setWidth 128 d) (hD _ (by simp))).2 _ σ1.1
        (by simpa [Params.dd, h0, h20] using h)
    rw [h0]; simpa [Params.nd] using (vc_push_str hL hw _ hP 0).1
  case vc5 =>
    rename_i s σ0 rng dm σ1 rng2 dm2 σ2 σ3 σ4 hf1 hf2 hst1 hst2 _
    simp [hd4] at hst1
    obtain ⟨rfl, hso, -⟩ := hst1
    have hP : Pu P w σ1.1 := by
      rcases hso with h | h <;> exact (vc_data_str _ hT (BitVec.setWidth 128 d) (hD _ (by simp))).2 _ σ1.1
        (by simpa [Params.dd, h0, h20] using h)
    simp [hd8] at hst2
    obtain ⟨rfl, hso2, -⟩ := hst2
    have hP2 : Pu P w σ2.1 := by
      rcases hso2 with h | h <;>
        exact pu_of_pu2 ((vc_push_str hL hw _ hP 0).2 _ σ2.1 (by simpa [Params.nd, h0] using h))
    exact ⟨h21, h0, h19, h21, ⟨hd8, hd4⟩, (hP2.fence hf1.1).fence hf2.1⟩

/-- Between the calls: the saved link, `&top`, no `dmem` word, `Po`. -/
def Mid2 (P : Params) (w : Nat) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Po P w σ.1

omit [Executable.ValidLayout (layout publishP)] in
/-- The argument set-up for `pop`. -/
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

/-! ## The body: three calls -/

section
attribute [local simp] MachineData.lr MachineData.setLr Reg64s.setXReg

/-- **`main`'s first block**: three calls through their specifications. -/
theorem main_body (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) (s : MachineData)
    (σ : (SharedEnv.counted (EW P w)).State) (hpre : MainPre P w d s σ) :
    PartialWpEnv (SharedEnv.counted (EW P w)) mainBody
      (fun s σ => Int64.ofBitVec s.regs.X19.toBitVec = mainEnd ∧ NoDmem s ∧ PopRes P w s.regs.X0.toBitVec σ.1)
      (fun _ _ _ => False) s σ := by
  have h1 := (main_save P w d s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  rintro s1 σ1 ⟨h19, h21, h27, hlim, h20, ⟨hd8, hd4⟩, hP⟩
  refine PartialWpEnv.call (alloc_spec (SharedEnv.counted (EW P w)) (fun σ => Pu0 P w σ.1)
    (fun _ _ h hle => h.fence ((fenceMono_le_counted _ _ _).mp hle).1) (P.n w))
    fun ra => ⟨⟨by simp, by simpa using h27, by simpa using hlim, hP⟩, ?_⟩
  rintro s2 σ2 ⟨a0, -, ⟨f19, f20, f21, -, -, -, -, -, -, fdm⟩, hP2⟩
  have h2 := (main_init P w hL hw d hD s2 σ2).le_wp s2 σ2 ⟨⟨a0, by simpa [f19] using h19, by simpa [f20] using h20,
    by simpa [f21] using h21, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩, hP2⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
  clear h19 h21 hd8 hd4
  rintro s3 σ3 ⟨h0, h1, h19, h21, ⟨hd8, hd4⟩, hP⟩
  refine PartialWpEnv.call (pushp_spec_at P w hL hw) fun ra =>
    ⟨⟨by simp, by simpa using h0, by simpa using h1, ⟨by simpa using hd8, by simpa using hd4⟩, hP⟩, ?_⟩
  rintro s4 σ4 ⟨⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩, hPo⟩
  have h3 := (main_mid P w s4 σ4).le_wp s4 σ4 ⟨⟨by simpa [f19] using h19, by simpa [f21] using h21,
    ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩, hPo⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h3)
  rintro s5 σ5 ⟨h0', h19', h21', ⟨hd8', hd4'⟩, hPo'⟩
  refine PartialWpEnv.call (pop_spec P w hw) fun ra =>
    ⟨⟨by simp, by simpa using h0', ⟨by simpa using hd8', by simpa using hd4'⟩, hPo'⟩, ?_⟩
  rintro s6 σ6 ⟨⟨g19, -, -, -, -, -, -, -, -, -, gdm⟩, hR⟩
  exact PartialWpEnv.nil ⟨by simpa [g19] using h19', ⟨by simpa [gdm] using hd8', by simpa [gdm] using hd4'⟩, hR⟩

end

/-! ## The run of `main` -/

/-- **`main` as a partial triple of the whole text**, `MainPre` to `DnD`. -/
theorem main_partialTripleEnv (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) :
    PartialTripleEnv (SharedEnv.counted (EW P w)) (MainPre P w d) publishP
      (fun s σ => DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1) (fun _ _ _ => False) := by
  intro s σ hpre pc hpc
  have hb : Program.blockAt publishP "main" = some ⟨"main", mainBody, some "ret_pop"⟩ := by decide
  obtain ⟨hs0, haf⟩ := Executable.walk_addrOf (p := publishP) publishP [] 0 (by simp)
  rw [← publishP_placed.entry pc hpc]
  refine Safely.bind (main_body P w hL hw d hD s σ hpre _ (publishP_placed.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, h19, hdm, hR⟩ | hF)
  · dsimp only at ha h19 hdm hR
    rw [publishP_placed.next _ _ _ hb rfl] at ha
    subst ha
    refine (main_tail P w s' g' h19 hdm hR).mono fun x ⟨hx, hd⟩ => .inl ⟨?_, hd⟩
    rw [hx, publishP_placed.entry _ hs0, Nat.zero_add] at *
    exact haf.symm
  · exact hF.elim

end Kraken.Promising.Lower.Publish
