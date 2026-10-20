/-
**The allocating Treiber client's `main` as
one placement-independent fragment specification.**
ISA: AArch64; machine: the executable machine's per-thread environment
semantics, partial correctness; env `counted (EW P w)` (the allocation pilot's).

The allocation pilot (`Lower/AllocMain.lean`) and the publish pilot (`Lower/PublishMain.lean`) proved
the same `main` twice, each at its own text: the block lemmas mention the
end address `mainEnd = (layout q).addrOf q.length` and `q_placed`. Here it is
proved once, with the runtime's return address `ra` in place of `mainEnd`:

- `mainBodyG lp`: `main`'s first block calling the push entry `lp`
  (`"push"` in `allocP`, `"pushp"` in `publishP`; `rfl` to `Alloc.mainBody`
  and `Publish.mainBody`); `mainFragG lp`: `main`'s fragment (the first
  block, then the first lowering pilot's `tailFrag`).
- `tail_spec`: the tail (`ret_pop:` … `ret`) as a `FragSpecEnv`, returning to
  the link saved in `x19` (the first lowering pilot's `main_tail` with `ra` for `mainEnd`).
- `main_save`, `main_init`, `main_mid`: the straight-line `vcgen` blocks,
  the allocation pilot's with `ra` for `mainEnd`; `main_body`: the three calls through
  `FunSpecPartialEnv` hypotheses.
- **`main_fragL`**: `main`'s `FragSpecEnvL` over `F :: allocFrag :: popFrag
  :: Gp`, for every push entry `lp` with a spec `FragSpecEnvL _ Gp lp PushPre
  PushPost` (`Pilot.pushFrag_spec.toL`, `Publish.pushp_spec`) and every
  fragment `F` holding `main`'s first block and the tail (both decidable).
  Pre `MainPreF` (the allocation pilot's `MainPre` with `ra` for `mainEnd`), post `DnD`.

`Lower/KitFrag.lean`'s `partialTripleEnv_of_fragL` turns `main_fragL` into
the kit's `main` field at every laid-out text (`Lower/FragKitPublish.lean`).
-/
import Kraken.Promising.Lower.FragSpecClients
import Kraken.Promising.Lower.FragSpecCalls

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.FragKit

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem PopRes PopRes.fence tailFrag mainMid pushFrag popFrag PushPre
  PushPost PopPre PopPost popFrag_spec)
open Kraken.Promising.Lower.Alloc (mainInit mainSave pu_of_pu2 AllocPre AllocPost allocFrag allocFrag_spec)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `main`'s first block, calling the push entry `lp`. -/
def mainBodyG (lp : Label) : Program :=
  mainSave ++ (Directive.instr ⟨.W64, .BL (.label "alloc")⟩ :: (mainInit ++
    (Directive.instr ⟨.W64, .BL (.label lp)⟩ :: (mainMid ++ [Directive.instr ⟨.W64, .BL (.label "pop")⟩]))))

/-- `main`'s fragment: the label, the first block, the tail. -/
def mainFragG (lp : Label) : Program := Directive.label "main" :: (mainBodyG lp ++ tailFrag)

/-! ## The tail -/

/-- At `ret_pop`: the saved link `ra` in `x19`, no `dmem` word, `pop`'s result. -/
def TailPreF (P : Params) (w : Nat) (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) :
    Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ NoDmem s ∧ PopRes P w s.regs.X0.toBitVec σ.1

/-- `DnD` of the result registers (`main`'s and the tail's post). -/
def MainPostF (P : Params) (w : Nat) (_ : Int64) (_ : MachineData) (_ : (SharedEnv.counted (EW P w)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1

/-- The tail's table. -/
abbrev tailTableF (P : Params) (w : Nat) (ra : Int64) :
    Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧
    ((lb = "ret_pop" ∧ PopRes P w s.regs.X0.toBitVec σ.1) ∨
      (lb = "empty" ∧ DnD P w s.regs.X10.toBitVec s.regs.X11.toBitVec σ.1))

/-- **The tail, placement-independent**: from `ret_pop` it returns to the link
saved in `x19` with `DnD` (the first lowering pilot's `main_tail`, `ra` for `mainEnd`). -/
theorem tail_spec (P : Params) (w : Nat) :
    FragSpecEnv (SharedEnv.counted (EW P w)) tailFrag "ret_pop" (TailPreF P w) (MainPostF P w) := by
  refine FragSpecEnv.of_cfg (fun ra _ _ => tailTableF P w ra) rfl (by decide)
    (fun ra t g ⟨h19, ⟨hd8, hd4⟩, hR⟩ => ⟨h19, hd8, hd4, .inl ⟨rfl, hR⟩⟩) ?_
  intro _ ra t g _
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
    exact .inr ⟨by simpa using h19, by simpa [MainPostF] using (hT.fence hf1.1).fence hf2.1⟩
  all_goals done

/-! ## The straight-line blocks -/

/-- At `main`: `x30 = ra`, `x21 = &top`, `x27 = P.n w` with room, payload
`w20`, `Pu0` (the allocation pilot's `MainPre` with `ra` for `mainEnd`). -/
def MainPreF (P : Params) (w : Nat) (d : BitVec 32) (ra : Int64) (s : MachineData)
    (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  Int64.ofBitVec s.regs.X30.toBitVec = ra ∧ s.regs.X21.toBitVec = P.t ∧ s.regs.X27.toBitVec = P.n w ∧
    s.regs.X27.toBitVec + 16 ≤ s.regs.X28.toBitVec ∧ s.regs.X20.toBitVec.setWidth 32 = d ∧ NoDmem s ∧ Pu0 P w σ.1

variable [CodeEnv]

/-- The link save. -/
theorem main_save (P : Params) (w : Nat) (d : BitVec 32) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => MainPreF P w d ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainSave⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X21.toBitVec = P.t ∧
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

/-- At `bl lp`: `push`'s arguments, the saved link, `&top`, `Pu`. -/
def Mid1 (P : Params) (w : Nat) (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
    s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Pu P w σ.1

/-- **The initial stores** of `new` on the fresh node, and `push`'s arguments. -/
theorem main_init (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => (s.regs.X0.toBitVec = P.n w ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra ∧
        s.regs.X20.toBitVec.setWidth 32 = d ∧ s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Pu0 P w σ.1) ∧
        s = s₀ ∧ σ = g₀ ⦄
      (⟨mainInit⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => Mid1 P w ra s σ); fun _ _ _ => False ⦄ := by
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
def Mid2 (P : Params) (w : Nat) (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) : Prop :=
  Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X21.toBitVec = P.t ∧ NoDmem s ∧ Po P w σ.1

/-- The argument set-up for `pop`. -/
theorem main_mid (P : Params) (w : Nat) (ra : Int64) :
    ∀ s₀ g₀, ⦃ fun s σ => Mid2 P w ra s σ ∧ s = s₀ ∧ σ = g₀ ⦄
      (⟨mainMid⟩ : EnvProgram (SharedEnv.counted (EW P w)))
    ⦃ (fun _ s σ => s.regs.X0.toBitVec = P.t ∧ Mid2 P w ra s σ); fun _ _ _ => False ⦄ := by
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

/-- **`main`'s first block**: three calls through their specifications, at
any code where those hold (`lp` the push entry). -/
theorem main_body (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {lp : Label}
    (hA : FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "alloc")
      (AllocPre (SharedEnv.counted (EW P w)) (fun σ => Pu0 P w σ.1) (P.n w))
      (AllocPost (SharedEnv.counted (EW P w)) (fun σ => Pu0 P w σ.1) (P.n w)))
    (hPu : FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label lp) (PushPre P w)
      (PushPost P w))
    (hPo : FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w))
    (ra : Int64) (s : MachineData) (σ : (SharedEnv.counted (EW P w)).State) (hpre : MainPreF P w d ra s σ) :
    PartialWpEnv (SharedEnv.counted (EW P w)) (mainBodyG lp) (TailPreF P w ra) (fun _ _ _ => False) s σ := by
  have h1 := (main_save P w d ra s σ).le_wp s σ ⟨hpre, rfl, rfl⟩
  rw [wpEnv_eq] at h1
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h1)
  rintro s1 σ1 ⟨h19, h21, h27, hlim, h20, ⟨hd8, hd4⟩, hP⟩
  refine PartialWpEnv.call hA fun ra' => ⟨⟨by simp, by simpa using h27, by simpa using hlim, hP⟩, ?_⟩
  rintro s2 σ2 ⟨a0, -, ⟨f19, f20, f21, -, -, -, -, -, -, fdm⟩, hP2⟩
  have h2 := (main_init P w hL hw d hD ra s2 σ2).le_wp s2 σ2 ⟨⟨a0, by simpa [f19] using h19,
    by simpa [f20] using h20, by simpa [f21] using h21, ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩, hP2⟩,
    rfl, rfl⟩
  rw [wpEnv_eq] at h2
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h2)
  clear h19 h21 hd8 hd4
  rintro s3 σ3 ⟨h0, h1, h19, h21, ⟨hd8, hd4⟩, hP⟩
  refine PartialWpEnv.call hPu fun ra' =>
    ⟨⟨by simp, by simpa using h0, by simpa using h1, ⟨by simpa using hd8, by simpa using hd4⟩, hP⟩, ?_⟩
  rintro s4 σ4 ⟨⟨f19, -, f21, -, -, -, -, -, -, -, fdm⟩, hPo4⟩
  have h3 := (main_mid P w ra s4 σ4).le_wp s4 σ4 ⟨⟨by simpa [f19] using h19, by simpa [f21] using h21,
    ⟨by simpa [fdm] using hd8, by simpa [fdm] using hd4⟩, hPo4⟩, rfl, rfl⟩
  rw [wpEnv_eq] at h3
  refine PartialWpEnv.of_wpEnv (Executable.wpEnv_mono ?_ (fun _ _ _ h => h) h3)
  rintro s5 σ5 ⟨h0', h19', h21', ⟨hd8', hd4'⟩, hPo'⟩
  refine PartialWpEnv.call hPo fun ra' =>
    ⟨⟨by simp, by simpa using h0', ⟨by simpa using hd8', by simpa using hd4'⟩, hPo'⟩, ?_⟩
  rintro s6 σ6 ⟨⟨g19, -, -, -, -, -, -, -, -, -, gdm⟩, hR⟩
  exact PartialWpEnv.nil ⟨by simpa [g19] using h19', ⟨by simpa [gdm] using hd8', by simpa [gdm] using hd4'⟩, hR⟩

end

omit [CodeEnv]

/-! ## `main`, once -/

/-- **`main`'s fragment specification, placement-independent and generic in
the push entry**: for every push entry `lp` with a spec over `Gp` and every
fragment `F` holding `main`'s first block (falling into `ret_pop`) and the
tail, `main` from `MainPreF` returns to `ra` with `DnD`, in every code placing
`F`, `alloc`, `pop` and `Gp`. -/
theorem main_fragL (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (d : BitVec 32)
    (hD : ∀ v : Val, BitVec.setWidth 32 v = d → P.D w v) {F : Program} {lp : Label} {Gp : List Program}
    (hpush : FragSpecEnvL (SharedEnv.counted (EW P w)) Gp lp (PushPre P w) (PushPost P w))
    (hb : Program.blockAt F "main" = some ⟨"main", mainBodyG lp, some "ret_pop"⟩)
    (ht : Program.subBlocksOfE tailFrag F = true) :
    FragSpecEnvL (SharedEnv.counted (EW P w)) (F :: allocFrag :: popFrag :: Gp) "main" (MainPreF P w d)
      (MainPostF P w) := by
  refine ⟨fun hpl ra t g hp => ?_⟩
  have hF := hpl F List.mem_cons_self
  have hA := (allocFrag_spec (SharedEnv.counted (EW P w)) (fun σ => Pu0 P w σ.1)
    (fun _ _ h hle => h.fence ((fenceMono_le_counted _ _ _).mp hle).1) (P.n w)).spec (hpl _ (by simp))
  have hPu := hpush.at_sub hpl fun q hq => by simp [hq]
  have hPo := (popFrag_spec P w hw).spec (hpl _ (by simp))
  refine Safely.bind (main_body P w hL hw d hD hA hPu hPo ra t g hp _ (hF.block _ _ hb)) ?_
  rintro ⟨⟨s', a⟩, g'⟩ (⟨ha, hT⟩ | hF')
  · dsimp only at ha hT
    rw [hF.next _ _ _ hb rfl] at ha
    subst ha
    exact ((tail_spec P w).spec (hF.of_sub ht) ra s' g' hT).mono fun _ ⟨hx, hd⟩ => ⟨hx, hd⟩
  · exact hF'.elim

end Kraken.Promising.Lower.FragKit
