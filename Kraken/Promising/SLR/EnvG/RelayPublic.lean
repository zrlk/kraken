/-
**Part 4: the three-thread relay, end to end**
(the `EnvG/TakeMpPublic.lean` pattern, three threads).

Threads: MP's `mpWriter` (thread `0`, flag `f1`), the `relay` (thread `1`,
`EnvG/RelaySpec.lean`), MP's `mpReader` text on `f2` (thread `2`, run on
`EnvGT`). **`mp_relay3_envG`**: at every reachable final configuration the
reader's `W4` is `43` and the data word's final value is `43`.

- **Initial ghost** `relayGhost`: `initGhost` with release predicates `φ`
  (MP's `flagPred`) at `f1` and `flag43` at `f2`, acquire ids `0 ↦ φ`,
  `1 ↦ flag43`, no release-mode location. **Initial resources** `relayRes`:
  the writer MP's `writerRes` (all of `Dt`, `f1`, `W`); the relay all of
  `f2` and `W2` and the acquire id `0` of `f1`; the reader the acquire id
  `1` of `f2`. Initial erasure `erase_relayInit` (`erase_initGhost`).
- **Postcondition** `YPost rp`: the token `W`, or the token `W2`, or the
  reader's result (`W4 = 43` of thread `2`) with `Own43`.
- **Writer**: `ThreadRuleRX.ofSafelyEnvG` from MP's `mpWriter_envG` with
  `hB_YW`, into the take route by `NPSafe.toP`. **Relay** and **reader**:
  `npSafeP_of_safelyEnvGT` from `relay_envGT` / `reader_envGT`.
- **No fault**, per thread: `relayRuleW_noFault` (`noFaultRule_ofSafelyEnvG_struct`),
  `relayRuleY_noFault`, `relayRuleR_noFault` (`noFaultRule_ofSafelyEnvGT_struct`,
  unconditional in promises). Adequacy does not consume them.
- **Final argument** `relay_final`: three threads, two tokens, so some
  thread has the reader's disjunct (`Erase.q_add_le_one`); it holds all of
  `Dt` (`total_max_of_thread`), hence the final value.
- **Purity**: `final_of_relPureSafelyS`, with `mpWriter_relPure`,
  `relay_relPure` and `mpReader_relPure`.

The relay releases with a **store** (`stlr`): a release-only RMW (`swpl`) is
not provable on phase-1 EnvG (`KNOWN_GAPS.md`; `mp_relay3_swpl.kl`).
-/
import Kraken.Promising.SLR.EnvG.RelayVCGen
import Kraken.Promising.SLR.EnvG.RelayRelPure
import Kraken.Promising.SLR.EnvG.TakeMpPublic

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp

/-! ## Parameters -/

/-- The relay's ghost parameters: tokens `W = ⟨0, 5⟩` (as MP's
`ghostParams`) and `W2 = ⟨0, 6⟩`. -/
def relayParams (f1 f2 d : BitVec 64) : RP := ⟨f1, f2, d, ⟨0, 5⟩, ⟨0, 6⟩⟩

theorem relayParams_P (f1 f2 d : BitVec 64) : (relayParams f1 f2 d).P = ghostParams f1 d := rfl

/-- The three words are distinct. -/
structure RelayLocs (f1 f2 d : BitVec 64) : Prop where
  f1d : f1 ≠ d
  f2d : f2 ≠ d
  f12 : f1 ≠ f2

theorem RelayLocs.P {f1 f2 d : BitVec 64} (h : RelayLocs f1 f2 d) : MpLocs (relayParams f1 f2 d).P :=
  ghostParams_mpLocs h.f1d

theorem RelayLocs.Q {f1 f2 d : BitVec 64} (h : RelayLocs f1 f2 d) : MpLocs (relayParams f1 f2 d).Q :=
  ⟨h.f2d, by simp [relayParams, Params.Fl], by simp [relayParams, Params.Dt]⟩

/-! ## The initial ghost and resources -/

/-- The release predicates: `φ` at `f1`, `flag43` at `f2`, else `emp`. -/
def relayRel (rp : RP) (x : Loc) : Pred :=
  if x = rp.P.Fl then rp.P.φ else if x = rp.Q.Fl then flag43 rp.Q.Dt else Pred.emp

/-- **The initial ghost of the relay.** -/
abbrev relayGhost (rp : RP) : Ghost := initGhost (relayRel rp) [rp.P.φ, flag43 rp.Q.Dt] []

/-- The relay's initial fractions: all of `f2` and `W2`. -/
def yFrac (rp : RP) (x : Loc) : Rat := if x = rp.Q.Fl ∨ x = rp.Q.W then 1 else 0

theorem yFrac_nonneg (rp : RP) (x : Loc) : 0 ≤ yFrac rp x := by
  unfold yFrac; split <;> decide

/-- The relay's initial resource: all of `f2` and `W2`, the acquire id `0`
of `f1`. -/
def relayThreadRes (m : Memory) (rp : RP) : Res :=
  ⟨(Res.initOf m (yFrac rp) (yFrac_nonneg rp)).wr, fun x ι => if x = rp.P.Fl ∧ ι = 0 then 1 else 0⟩

/-- The reader's initial resource: the acquire id `1` of `f2`. -/
def readerThreadRes (rp : RP) : Res := ⟨fun _ => Perm.unit, fun x ι => if x = rp.Q.Fl ∧ ι = 1 then 1 else 0⟩

/-- The initial thread resources. -/
def relayRes (m : Memory) (rp : RP) (i : Nat) : Res :=
  if i = 0 then writerRes m rp.P else if i = 1 then relayThreadRes m rp else if i = 2 then readerThreadRes rp
    else Res.unit

/-! ## Initial erasure -/

section Init

variable {sW sY sR : isa.State} {initMem : List (Loc × Val)}

theorem total_relayInit (rp : RP) (m : Memory) :
    total (relayRes m rp) (relayGhost rp) (Config.init [sW, sY, sR] initMem) =
      (writerRes m rp.P).op ((relayThreadRes m rp).op (readerThreadRes rp)) := by
  simp only [total, Config.init_size, threadsRes, Ghost.slotsRes, initGhost, List.map_nil, Res.prod_nil,
    Res.op_unit, List.length_cons, List.length_nil]
  show Res.prod [relayRes m rp 0, relayRes m rp 1, relayRes m rp 2] = _
  simp [relayRes, Res.op_unit]

theorem total_relayInit_q (rp : RP) (m : Memory) (x : Loc) :
    ((total (relayRes m rp) (relayGhost rp) (Config.init [sW, sY, sR] initMem)).wr x).q =
      writerFrac rp.P x + (yFrac rp x + 0) := by
  rw [total_relayInit]; rfl

theorem total_relayInit_acq (rp : RP) (m : Memory) (x : Loc) (ι : PredId) :
    (total (relayRes m rp) (relayGhost rp) (Config.init [sW, sY, sR] initMem)).acq x ι =
      0 + ((if x = rp.P.Fl ∧ ι = 0 then 1 else 0) + (if x = rp.Q.Fl ∧ ι = 1 then 1 else 0)) := by
  rw [total_relayInit]; rfl

/-- **Initial erasure of the relay**, for parameters whose flags differ and
whose writer and relay fractions are disjoint (both flags initially `0`). -/
theorem erase_relayInit' {rp : RP} (h12 : rp.Q.Fl ≠ rp.P.Fl) (hdisj : ∀ x, writerFrac rp.P x + yFrac rp x ≤ 1)
    (T : Nat → Prop) (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal rp.P.Fl = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal rp.Q.Fl = 0) :
    Erase (relayRes (Config.init [sW, sY, sR] initMem).mem rp) (relayGhost rp) T (Config.init [sW, sY, sR] initMem) := by
  have hq := total_relayInit_q (sW := sW) (sY := sY) (sR := sR) (initMem := initMem) rp (Config.init (I := isa) [sW, sY, sR] initMem).mem
  have ha := total_relayInit_acq (sW := sW) (sY := sY) (sR := sR) (initMem := initMem) rp (Config.init (I := isa) [sW, sY, sR] initMem).mem
  have h12' : rp.f2 ≠ rp.f1 := fun h => h12 (by simp [Params.Fl, h])
  have hids : ∀ x, (relayGhost rp).acqIds (total (relayRes (Config.init (I := isa) [sW, sY, sR] initMem).mem rp) (relayGhost rp) (Config.init (I := isa) [sW, sY, sR] initMem)).acq x =
      if x = rp.P.Fl then [0] else if x = rp.Q.Fl then [1] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (relayGhost rp).acqTab.length = 2 from rfl]
    by_cases hx : x = rp.P.Fl
    · subst hx; simp [ha, Ne.symm h12, List.range_succ]
    · by_cases hy : x = rp.Q.Fl
      · subst hy; simp [ha, h12, List.range_succ]
      · simp [ha, hx, hy]
  have hA : ∀ x ι, 1 ≤ (total (relayRes (Config.init (I := isa) [sW, sY, sR] initMem).mem rp) (relayGhost rp) (Config.init (I := isa) [sW, sY, sR] initMem)).acq x ι → ι < 2 := by
    intro x ι h
    rw [ha] at h
    split at h <;> split at h <;> grind
  have hR : ∀ x v m V r, (relayRel rp x).P v m V r → Pred.SepList ((relayGhost rp).acqPreds
      (total (relayRes (Config.init (I := isa) [sW, sY, sR] initMem).mem rp) (relayGhost rp) (Config.init (I := isa) [sW, sY, sR] initMem)).acq x ++ (relayGhost rp).updPreds x) v m V r := by
    intro x
    refine relAcq_single (g := relayGhost rp) (x := x) ?_
    by_cases hx : x = rp.P.Fl
    · refine .inr ⟨0, ?_, ?_⟩
      · rw [hids]; simp [hx, initGhost]
      · simp [Ghost.acqPred, initGhost, relayRel, hx]
    · by_cases hy : x = rp.Q.Fl
      · refine .inr ⟨1, ?_, ?_⟩
        · rw [hids]; simp [hy, initGhost, h12']
        · simp [Ghost.acqPred, initGhost, relayRel, hy, h12']
      · refine .inl ⟨?_, fun v m V r h => ?_⟩
        · rw [hids]; simp [hx, hy, initGhost]
        · simp only [initGhost, relayRel, hx, hy, ↓reduceIte] at h; exact h
  have hWr : ∀ x, 0 < ((total (relayRes (Config.init (I := isa) [sW, sY, sR] initMem).mem rp) (relayGhost rp) (Config.init (I := isa) [sW, sY, sR] initMem)).wr x).q → ∀ p,
      ((total (relayRes (Config.init (I := isa) [sW, sY, sR] initMem).mem rp) (relayGhost rp) (Config.init (I := isa) [sW, sY, sR] initMem)).wr x).X p ↔ p = ((Config.init (I := isa) [sW, sY, sR] initMem).mem.initVal x, 0) := by
    intro x hpos p
    rw [hq] at hpos
    rw [total_relayInit]
    show (0 < writerFrac rp.P x ∧ p = _) ∨ ((0 < yFrac rp x ∧ p = _) ∨ False) ↔ _
    have hw0 := writerFrac_nonneg rp.P x
    have hy0 := yFrac_nonneg rp x
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩ | h)
      · exact h
      · exact h
      · exact h.elim
    · intro h
      by_cases hw : 0 < writerFrac rp.P x
      · exact .inl ⟨hw, h⟩
      · exact .inr (.inl ⟨by grind, h⟩)
  have hP : ∀ x, Pred.Pure (relayRel rp x) ((Config.init (I := isa) [sW, sY, sR] initMem).mem.initVal x) := by
    intro x
    unfold relayRel
    by_cases hx : x = rp.P.Fl
    · subst hx; simp only [↓reduceIte]; rw [hF1]; exact flagPred_pure (by decide)
    · by_cases hy : x = rp.Q.Fl
      · subst hy; simp only [hx, ↓reduceIte]; rw [hF2]; exact flag43_pure (by decide)
      · simp only [hx, hy, ↓reduceIte]; exact Pred.emp_pure _
  have hV : (total (relayRes (Config.init (I := isa) [sW, sY, sR] initMem).mem rp) (relayGhost rp) (Config.init (I := isa) [sW, sY, sR] initMem)).valid :=
    ⟨fun x => by rw [hq, Rat.add_zero]; exact hdisj x, fun x ι => by rw [ha]; split <;> split <;> grind⟩
  exact erase_initGhost (rls := []) T List.nodup_nil hV hA hR hWr (fun x _ => hP x) (fun _ h => by cases h)
    (fun _ h => by cases h) (fun _ h => by cases h)


/-- **Initial erasure of the relay** (both flags initially `0`). -/
theorem erase_relayInit {f1 f2 d : BitVec 64} (hL : RelayLocs f1 f2 d) (T : Nat → Prop)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0) :
    Erase (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d))
      (relayGhost (relayParams f1 f2 d)) T (Config.init [sW, sY, sR] initMem) := by
  refine erase_relayInit' (fun h => hL.f12 (congrArg Loc.addr h).symm) (fun x => ?_) T hF1 hF2
  unfold writerFrac yFrac
  by_cases hw : x = (relayParams f1 f2 d).P.Dt ∨ x = (relayParams f1 f2 d).P.Fl ∨ x = (relayParams f1 f2 d).P.W
  · have : ¬ (x = (relayParams f1 f2 d).Q.Fl ∨ x = (relayParams f1 f2 d).Q.W) := by
      rintro (rfl | rfl) <;> rcases hw with h | h | h <;> simp [relayParams, Params.Fl, Params.Dt] at h <;>
        first | exact hL.f2d h | exact hL.f12 h.symm
    simp only [hw, this, ↓reduceIte]; grind
  · simp only [hw, ↓reduceIte]; split <;> grind

end Init

theorem relayGhost_rel_F1 (rp : RP) : (relayGhost rp).rel rp.P.Fl = rp.P.φ := by
  simp [initGhost, relayRel]

theorem relayGhost_rel_F2 {rp : RP} (h : rp.Q.Fl ≠ rp.P.Fl) : (relayGhost rp).rel rp.Q.Fl = flag43 rp.Q.Dt := by
  simp [initGhost, relayRel, h]

theorem relayGhost_rel_Dt {f1 f2 d : BitVec 64} (hL : RelayLocs f1 f2 d) (v : Val) :
    Pred.Pure ((relayGhost (relayParams f1 f2 d)).rel ⟨d, 4⟩) v := by
  have h1 : (⟨d, 4⟩ : Loc) ≠ (relayParams f1 f2 d).P.Fl := fun h => hL.f1d (congrArg Loc.addr h).symm
  have h2 : (⟨d, 4⟩ : Loc) ≠ (relayParams f1 f2 d).Q.Fl := fun h => hL.f2d (congrArg Loc.addr h).symm
  simp only [initGhost, relayRel, h1, h2, ↓reduceIte]
  exact Pred.emp_pure v

theorem RelayLocs.q_ne {f1 f2 d : BitVec 64} (hL : RelayLocs f1 f2 d) :
    (relayParams f1 f2 d).Q.Fl ≠ (relayParams f1 f2 d).P.Fl := fun h => hL.f12 (congrArg Loc.addr h).symm

/-! ## The postcondition and the final argument -/

/-- The reader's result: thread `2` has `W4 = 43`, and the resource holds all
of `Dt` with maximal write `43`. -/
def ROut (rp : RP) (c : Config isa) (r : Res) : Prop :=
  (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧ Own43 rp.Q r

/-- **The shared postcondition**: the writer's token `W`, or the relay's
token `W2`, or the reader's result (thread `2` has `W4 = 43`) with all of
`Dt` and maximal write `43`. -/
def YPost (rp : RP) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  1 ≤ (r.wr rp.P.W).q ∨ 1 ≤ (r.wr rp.Q.W).q ∨ ROut rp c r

/-- **The final argument**: three threads, two tokens, so some thread has
the reader's disjunct; it holds all of `Dt`, whose maximal write is `43`. -/
theorem relay_final {rp : RP} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 3)
    (hB : ∀ tid, c.Done tid → YPost rp c (rF tid) g) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal rp.Q.Dt = 43#128 := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have h2 : (2 : Nat) < c.threads.size := by rw [hsize]; decide
  have hR : ∃ j, j < c.threads.size ∧ ROut rp c (rF j) := by
    by_cases r0 : ROut rp c (rF 0)
    · exact ⟨0, h0, r0⟩
    by_cases r1 : ROut rp c (rF 1)
    · exact ⟨1, h1, r1⟩
    by_cases r2 : ROut rp c (rF 2)
    · exact ⟨2, h2, r2⟩
    exfalso
    have t0 := (hB 0 (Config.final_done hf h0)).imp_right fun h => h.resolve_right r0
    have t1 := (hB 1 (Config.final_done hf h1)).imp_right fun h => h.resolve_right r1
    have t2 := (hB 2 (Config.final_done hf h2)).imp_right fun h => h.resolve_right r2
    have e01 := E.q_add_le_one h0 h1 (by decide) rp.P.W
    have e02 := E.q_add_le_one h0 h2 (by decide) rp.P.W
    have e12 := E.q_add_le_one h1 h2 (by decide) rp.P.W
    have f01 := E.q_add_le_one h0 h1 (by decide) rp.Q.W
    have f02 := E.q_add_le_one h0 h2 (by decide) rp.Q.W
    have f12 := E.q_add_le_one h1 h2 (by decide) rp.Q.W
    rcases t0 with a0 | a0 <;> rcases t1 with a1 | a1 <;> rcases t2 with a2 | a2 <;> grind
  obtain ⟨j, hj, hx4, hq, tw, hX, hmax⟩ := hR
  obtain ⟨hpos, hXT, hmaxT⟩ := total_max_of_thread E hj hq hX hmax
  exact ⟨hx4, E.finalVal_of_max hf hpos hXT hmaxT⟩

/-! ## The start states -/

section Start

variable [layout : _root_.Layout]

/-- The relay at its start (the label `spin`): `X0 = f1`, `X1 = d`,
`X2 = f2`, none of the three words in `dmem`. -/
structure StartY (f1 f2 d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout relay
  decls : s.decls = {}
  endPc : s.endPc = (layout relay).addrOf 8
  pc : s.st.2 = (layout relay).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f1
  x1 : s.st.1.regs.X1.toBitVec = d
  x2 : s.st.1.regs.X2.toBitVec = f2
  df1 : Mem.loadInt s.st.1.dmem f1 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none
  df2 : Mem.loadInt s.st.1.dmem f2 4 = none

end Start

/-! ## The writer -/

section Writer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpWriter)]

omit [Executable.ValidLayout (layout mpWriter)] in
/-- **`hB` for the writer**: it keeps the token `W`. -/
theorem hB_YW (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postW rp.P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.P) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The writer's rule** for `YPost` (MP's writer, `ThreadRuleRX.ofSafelyEnvG`). -/
def relayRuleW (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : ThreadRuleRX (I := isa) Arch.armv8 (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvG (post := postW rp.P) (mpPlan_valid hL) mpWriter_rmwLive mpWriter_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_YW rp tid)

/-- **The writer's rule excludes faults.** -/
theorem relayRuleW_noFault (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : NoFaultRule (relayRuleW rp hL tid) :=
  noFaultRule_ofSafelyEnvG_struct _ _ _ _ _ _ mpWriter_noFault

end Writer

/-! ## The relay -/

section Relay

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relay)]

omit [Executable.ValidLayout (layout relay)] in
theorem relay_rmwLive : (layout relay).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem relay_phase1 : Phase1Tree Arch.armv8 (layout relay) := phase1Tree_of_dirs (by dirs_phase1 relay)

omit [Executable.ValidLayout (layout relay)] in
theorem relay_noFault : DirsNoFault (layout relay) := by dirs_no_fault' relay

/-- The relay's postcondition: the end of its text and `RK4` (the counter of
`relay_envGT` projected away). -/
abbrev postY (rp : RP) : MachineState × EStateA → Prop := postOf relay fun _ σ => ∃ _ : Nat, RK4 rp σ

omit [Executable.ValidLayout (layout relay)] in
/-- **`hB` for the relay**: it keeps the token `W2`. -/
theorem hB_Y (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postY rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.Q) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl hW)
  · rw [hp] at hts; cases hts

/-- **The relay's no-fault rule** (`NoFaultRuleS` of its take-route rule). -/
theorem relayRuleY_noFault (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGT (e := layout relay) (post := postY rp) (mpPlan_valid hL)
      relay_rmwLive relay_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_Y rp tid)) :=
  noFaultRule_ofSafelyEnvGT_struct _ _ _ _ _ _ relay_noFault

/-- **`NPSafeP` for the relay** from its invariant (the take route). -/
theorem relay_npSafeY (rp : RP) (hL : MpLocs rp.Q) (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) Arch.armv8 1 (mpPlan rp.Q)
      (QA64T Arch.armv8 1 (mpPlan rp.Q) (layout relay) ((layout relay).addrOf relay.length) (postY rp)) cl c r g) :
    NPSafeP (model isa) Arch.armv8 (YPost rp) 1 G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  npSafeP_of_safelyEnvGT (mpPlan_valid hL) relay_rmwLive relay_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_Y rp 1) n m h

end Relay

/-! ## The reader -/

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpReader)]

/-- The reader's postcondition: the end of its text, `Own43`, and `W4 = 43`
under the clean flag (the counter of `reader_envGT` projected away). -/
abbrev postD (rp : RP) : MachineState × EStateA → Prop :=
  postOf mpReader fun s σ => ∃ _ : Nat, Own43 rp.Q σ.r ∧ (σ.cl → s.regs.X4.toBitVec.setWidth 32 = 43)

omit [Executable.ValidLayout (layout mpReader)] in
/-- **`hB` for the reader** (thread `2`): `Own43` and `W4 = 43`. -/
theorem hB_D (rp : RP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postD rp (t.st.st, σ) → t.prom = [] → EnvRel 2 rdPlan σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, hown, hx4⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr (.inr ⟨⟨t, hrel.ht, hx4 (hrel.cl hcl)⟩, hown⟩)

/-- **The reader's no-fault rule** (`NoFaultRuleS` of its take-route rule). -/
theorem relayRuleR_noFault (rp : RP) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGT (e := layout mpReader) (post := postD rp) (tid := 2) rdPlan_valid
      mpReader_rmwLive mpReader_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_D rp)) :=
  noFaultRule_ofSafelyEnvGT_struct _ _ _ _ _ _ mpReader_noFault

/-- **`NPSafeP` for the reader** (thread `2`) from its invariant (the take
route). -/
theorem relay_npSafeD (rp : RP) (n m : Nat) {cl : Prop} {c : Config isa} {r : Res} {g : Ghost}
    (h : InvG (I := isa) Arch.armv8 2 rdPlan
      (QA64T Arch.armv8 2 rdPlan (layout mpReader) ((layout mpReader).addrOf mpReader.length) (postD rp)) cl c r g) :
    NPSafeP (model isa) Arch.armv8 (YPost rp) 2 G₀ (K2Scope (model isa) AllocIds) n m cl c r g :=
  npSafeP_of_safelyEnvGT rdPlan_valid mpReader_rmwLive mpReader_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_D rp) n m h

end Reader

/-! ## The initial invariants -/

section Inv

variable [layout : _root_.Layout] {f1 f2 d : BitVec 64} {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The writer's initial invariant** (thread `0`). -/
theorem invYW_init [Executable.ValidLayout (layout mpWriter)] (hL : RelayLocs f1 f2 d) (hW : StartW f1 d sW) :
    (relayRuleW (relayParams f1 f2 d) hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout mpWriter⟩
  refine invG_init (s := sW) rfl rfl (qa64_of_partialTripleEnv (mpWriter_envG _ hL.P 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc ⟨hW.x0, hW.x1, hW.df, hW.dd, ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩)
  simp only [σInit, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The relay's initial invariant** (thread `1`): `RK1` at `σInit`. -/
theorem invY_init [Executable.ValidLayout (layout relay)] (hL : RelayLocs f1 f2 d) (hY : StartY f1 f2 d sY) :
    InvG (I := isa) Arch.armv8 1 (mpPlan (relayParams f1 f2 d).Q)
      (QA64T Arch.armv8 1 (mpPlan (relayParams f1 f2 d).Q) (layout relay) ((layout relay).addrOf relay.length)
        (postY (relayParams f1 f2 d)))
      True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout relay⟩
  refine invGT_init (s := sY) rfl rfl (qa64T_of_partialTripleEnv (relay_envGT _ hL.Q 1).uncount rfl hY.exe
    hY.decls hY.endPc hY.pc ⟨0, ⟨hY.x0, hY.x1, hY.x2, hY.df1, hY.dd, hY.df2⟩,
      ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, relayThreadRes]
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInit, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

/-- **The reader's initial invariant** (thread `2`): `DK1` at `σInit`. -/
theorem invD_init [Executable.ValidLayout (layout mpReader)] (hL : RelayLocs f1 f2 d) (hR : StartR f2 d sR) :
    InvG (I := isa) Arch.armv8 2 rdPlan
      (QA64T Arch.armv8 2 rdPlan (layout mpReader) ((layout mpReader).addrOf mpReader.length)
        (postD (relayParams f1 f2 d)))
      True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout mpReader⟩
  refine invGT_init (s := sR) rfl rfl (qa64T_of_partialTripleEnv (reader_envGT _ 2).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc ⟨0, hR.x0, hR.x1, hR.df, hR.dd, relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_,
      OkPred43.flag⟩)
  · simp [σInit, Views.getFwd]
  · simp [σInit, relayRes, readerThreadRes]

end Inv

/-! ## `NPSafeP`, purity and the theorem -/

/-- **The `NPSafeP` side for the relay**: the writer through its
`ThreadRuleRX` (`NPSafe.toP`), the relay and the reader through the take
route. -/
theorem relay_npSafe (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relay)] [Executable.ValidLayout (lR mpReader)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f1 d sW) (hY : StartY (layout := lY) f1 f2 d sY)
    (hR : StartR (layout := lR) f2 d sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (YPost (relayParams f1 f2 d)) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) tid)
      (relayGhost (relayParams f1 f2 d)) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleW (layout := lW) _ hL.P 0) n m _ _ _ _ (invYW_init (layout := lW) hL hW))
  | 1, _ =>
    exact relay_npSafeY (layout := lY) _ hL.Q n m (invY_init (layout := lY) hL hY)
  | 2, _ =>
    exact relay_npSafeD (layout := lR) _ n m (invD_init (layout := lR) hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

/-- The threads' purity specifications: the writer (layout `lW`) at thread
`0`, the relay (layout `lY`) at thread `1`, the reader (layout `lR`)
elsewhere. -/
def relayPureSpec (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relay)] [Executable.ValidLayout (lR mpReader)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := lW) mpWriter fun _ _ => True
  | 1 => RelPureSpec.ofProgram (layout := lY) relay fun _ _ => ∃ _ : Nat, True
  | _ + 2 => RelPureSpec.ofProgram (layout := lR) mpReader fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states.** -/
theorem relayPureSpec_init (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relay)] [Executable.ValidLayout (lR mpReader)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} (hW : StartW (layout := lW) f1 d sW)
    (hY : StartY (layout := lY) f1 f2 d sY) (hR : StartR (layout := lR) f2 d sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s →
      (relayPureSpec lW lY lR (relayGhost (relayParams f1 f2 d)).rel tid).Holds s := by
  intro tid s hs
  match tid, hs with
  | 0, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hdf, hdd⟩ := hW
    letI : CodeEnv := ⟨lW mpWriter⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lW)
      (mpWriter_relPure (layout := lW) _ f1 d (relayGhost_rel_Dt hL)).partial rfl he hds hend hpc ⟨hx0, hx1, hdf, hdd⟩
  | 1, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hx2, hdf, hdd, hdg⟩ := hY
    letI : CodeEnv := ⟨lY relay⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lY)
      (relay_relPure (layout := lY) _ f1 d f2 (relayGhost_rel_Dt hL)).uncount
      rfl he hds hend hpc ⟨0, hx0, hx1, hx2, hdf, hdd, hdg⟩
  | 2, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, -, hdf, -⟩ := hR
    letI : CodeEnv := ⟨lR mpReader⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lR) (mpReader_relPure (layout := lR) _ f2).uncount rfl
      he hds hend hpc ⟨0, hx0, hdf⟩
  | _ + 3, hs => cases hs

/-- **A three-thread ownership relay, for AArch64 under `Arch.armv8`**: MP's
writer `mpWriter` (thread `0`, layout `lW`, `X0 = f1`, `X1 = d`), the
`relay` (thread `1`, layout `lY`, `X0 = f1`, `X1 = d`, `X2 = f2`) and MP's
reader `mpReader` (thread `2`, layout `lR`, `X0 = f2`, `X1 = d`), started
from an initial memory with both flags at `0`: at every reachable final
configuration the reader's `W4` is `43` and the data word's final value is
`43`. The relay takes the data at its acquire load of `f1`, writes it and
releases it with `stlr f2`; the reader takes it at its acquire load of `f2`
(the take route, `npSafeP_of_safelyEnvGT`). -/
theorem mp_relay3_envG {fuel : Nat} (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lY relay)] [Executable.ValidLayout (lR mpReader)] (f1 f2 d : BitVec 64)
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f1 d sW) (hY : StartY (layout := lY) f1 f2 d sY)
    (hR : StartR (layout := lR) f2 d sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := YPost (relayParams f1 f2 d))
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_relayInit hL _ hF1 hF2) initGhost_pend
    (relayPureSpec lW lY lR _) (relayPureSpec_init lW lY lR hL hW hY hR) (relay_npSafe lW lY lR hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_envG
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleW_noFault
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleY_noFault
#print axioms Kraken.Promising.SLR.EnvG.Relay.relayRuleR_noFault
