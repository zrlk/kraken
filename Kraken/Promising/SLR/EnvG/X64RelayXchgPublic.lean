/-
**Part 6: the x64 three-thread relay through
`xchg`, end to end** (`Kraken/Examples/LockFree/X64/mp_relay3_xchg.kl`;
the `swpl` relay's `EnvG/RelaySwplPublic.lean` for x64 under `Arch.tso`).

Threads: x64 MP's `mpWriterX` (thread `0`, flag `f1`), the relay `relayX`
(thread `1`, `EnvG/X64RelayXchgSpec.lean`: spin on `f1`, store `43` to the
data, `xchgl` `1` into `f2`), x64 MP's `mpReaderX` text on `f2` (thread `2`,
run on `EnvGTX`). **`mp_relay3_xchg_envG`**: at every reachable final
configuration the reader's `ebx` is `43` and the data word's final value is
`43` — the conclusion of `mp_relay3_swpl_envG`, with `W4` read as `ebx`.

Copied from the relay proof's `EnvG/RelayPublic.lean` with the x64 names (that file is
AArch64-only): the parameters (`relayParams`, `RelayLocs`), the initial ghost
and resources (`relayGhost`, `relayRes`) and their erasure
(`erase_relayInit`), the postcondition `YPost` and the final argument
`relay_final`.

- **Writer**: `relayRuleWX`, `ThreadRuleRX.ofSafelyEnvGX` from
  `mpWriterX_envG`; into the take route by `NPSafe.toP`.
- **Relay**: **`ThreadRuleRXGS.ofSafelyEnvGTRCX`** (`EnvG/X64RmwGhostLink.lean`:
  taking loads, claim-conditional RMWs; every x64 RMW claims, the `xchg` gives
  `Dt` from the relay's own resource) from `relayX_envGTC`, with
  `Phase1TreeRX` (`dirs_phase1RX`). `invYX_init` (`invGTRCX_init`).
- **Reader**: `ThreadRuleRXGS.ofSafelyEnvGTX` from `readerX_envGT`
  (`invDX_init`, `invGTX_init`).
- **No fault**, per thread: `relayRuleWX_noFault`, `relayRuleYX_noFault`,
  `relayRuleDX_noFault`. Adequacy does not consume them.
- **Assembly**: `final_of_relPureSafelyQX_tsoS` with one all-release
  specification per thread (`mpWriterX_noNT`, `relayX_noNT`,
  `mpReaderX_noNT`).
-/
import Kraken.Promising.SLR.EnvG.X64MpPublic
import Kraken.Promising.SLR.EnvG.X64TakeMpPublic
import Kraken.Promising.SLR.EnvG.X64RelayXchgVCGen
import Kraken.Promising.SLR.EnvG.X64RelayXchgRelPure
import Kraken.Promising.SLR.EnvG.TakeX64Final

namespace Kraken.Promising.X64.EnvG.RelayX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.TakeMp

/-! ## Parameters -/

/-- The relay's ghost parameters: tokens `W = ⟨0, 5⟩` (as x64 MP's
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

theorem RelayLocs.Q {f1 f2 d : BitVec 64} (h : RelayLocs f1 f2 d) : MpLocs (relayParams f1 f2 d).Q where
  fd := h.f2d
  wf h := by have := congrArg Loc.bytes h; simp [relayParams] at this
  wd h := by have := congrArg Loc.bytes h; simp [relayParams] at this

theorem RelayLocs.q_ne {f1 f2 d : BitVec 64} (hL : RelayLocs f1 f2 d) :
    (relayParams f1 f2 d).Q.Fl ≠ (relayParams f1 f2 d).P.Fl := fun h => hL.f12 (congrArg Loc.addr h).symm

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
  refine erase_relayInit' hL.q_ne (fun x => ?_) T hF1 hF2
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

/-! ## The postcondition and the final argument -/

/-- The reader's result: thread `2` has `ebx = 43`, and the resource holds
all of `Dt` with maximal write `43`. -/
def ROut (rp : RP) (c : Config isa) (r : Res) : Prop :=
  (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧ Own43 rp.Q r

/-- **The shared postcondition**: the writer's token `W`, or the relay's
token `W2`, or the reader's result. -/
def YPost (rp : RP) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  1 ≤ (r.wr rp.P.W).q ∨ 1 ≤ (r.wr rp.Q.W).q ∨ ROut rp c r

/-- **The final argument**: three threads, two tokens, so some thread has
the reader's disjunct; it holds all of `Dt`, whose maximal write is `43`. -/
theorem relay_final {rp : RP} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 3)
    (hB : ∀ tid, c.Done tid → YPost rp c (rF tid) g) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
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
  obtain ⟨j, hj, hx, hq, tw, hX, hmax⟩ := hR
  obtain ⟨hpos, hXT, hmaxT⟩ := SLR.total_max_of_thread E hj hq hX hmax
  exact ⟨hx, E.finalVal_of_max hf hpos hXT hmaxT⟩

/-! ## The start state -/

section Start

variable [layout : _root_.Layout]

/-- The x64 relay at its start (the label `spin`): `rdi = f1`, `rsi = d`,
`rdx = f2`, none of the three words in the private memory. -/
structure StartYX (f1 f2 d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout relayX
  decls : s.decls = {}
  endPc : s.endPc = (layout relayX).addrOf relayX.length
  pc : s.st.2 = (layout relayX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = f1
  rsi : s.st.1.regs.get64 .rsi = d
  rdx : s.st.1.regs.get64 .rdx = f2
  split : Split [(f1, 4), (d, 4), (f2, 4)] s.st.1.dmem

omit layout in
theorem split3_f1 {f1 d f2 : BitVec 64} {m : DataMem} (h : Split [(f1, 4), (d, 4), (f2, 4)] m) :
    Mem.loadInt m f1 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

omit layout in
theorem split3_d {f1 d f2 : BitVec 64} {m : DataMem} (h : Split [(f1, 4), (d, 4), (f2, 4)] m) :
    Mem.loadInt m d 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

omit layout in
theorem split3_f2 {f1 d f2 : BitVec 64} {m : DataMem} (h : Split [(f1, 4), (d, 4), (f2, 4)] m) :
    Mem.loadInt m f2 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

end Start

/-! ## The writer -/

section Writer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpWriterX)]

omit [Executable.ValidLayout (layout mpWriterX)] in
/-- **`hB` for the writer**: it keeps the token `W`. -/
theorem hB_YW (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postW rp.P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.P) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The x64 writer's rule** for `YPost` (x64 MP's writer,
`ThreadRuleRX.ofSafelyEnvGX`). -/
def relayRuleWX (rp : RP) (hL : MpLocs rp.P) (tid : Nat) : ThreadRuleRX (I := isa) Arch.tso (YPost rp) tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := mpS rp.P) (post := postW rp.P) (mpPlan_valid hL) (mpS_le16 rp.P)
    mpWriterX_phase1 postOfX_end (not_instrStepEnv_of_end_labels _ 0) (hB_YW rp tid)

/-- **The x64 writer's rule excludes faults.** -/
theorem relayRuleWX_noFault (rp : RP) (hL : MpLocs rp.P) (tid : Nat) :
    NoFaultRule (relayRuleWX (layout := layout) rp hL tid) :=
  noFaultRule_ofSafelyEnvGX_struct _ _ _ _ _ _ mpWriterX_noFault

end Writer

/-! ## The relay -/

section Relay

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relayX)]

/-- The relay's text has phase-1 trees with release-kind RMWs (`xchgl` is an
`.acqRel` RMW that never fails). -/
theorem relayX_phase1 : Phase1TreeRX Arch.tso (layout relayX) := by
  refine phase1TreeRX_of_dirs ?_
  dirs_phase1RX relayX
  -- `je spin`: the branch is inside `toEv`, which the tactic's `split` misses
  all_goals by_cases h : s.status.zf = true <;>
    simp [h, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]

omit [Executable.ValidLayout (layout relayX)] in
theorem relayX_noFault : DirsNoFault (layout relayX) := by
  dirs_no_fault relayX
  -- `je spin`, as in `relayX_phase1`
  all_goals by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The relay's postcondition: the end of its text and `RK4` (the counter of
`relayX_envGTC` projected away). -/
abbrev postYX (rp : RP) : MachineState × EStateX → Prop := postOfX relayX fun _ σ => ∃ _ : Nat, RK4 rp σ

omit [Executable.ValidLayout (layout relayX)] in
/-- **`hB` for the relay**: it keeps the token `W2`. -/
theorem hB_YX (rp : RP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postYX rp (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan rp.Q) σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl hW)
  · rw [hp] at hts; cases hts

/-- **The x64 relay's rule** (`ThreadRuleRXGS.ofSafelyEnvGTRCX`: taking
loads, claim-conditional RMWs). -/
def relayRuleYX (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (YPost rp) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTRCX (S := relayS rp) (post := postYX rp) (mpPlan_valid hL) (relayS_le16 rp)
    relayX_phase1 postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_YX rp tid)

/-- **The x64 relay's no-fault rule** (`NoFaultRuleSX` of its rule;
unconditional in promises). -/
theorem relayRuleYX_noFault (rp : RP) (hL : MpLocs rp.Q) (tid : Nat) :
    NoFaultRuleSX (relayRuleYX (layout := layout) rp hL tid) :=
  noFaultRule_ofSafelyEnvGTRCX_struct _ _ _ _ _ _ relayX_noFault

end Relay

/-! ## The reader -/

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpReaderX)]

/-- The reader's postcondition: the end of its text, `Own43`, and `ebx = 43`
under the clean flag (the counter of `readerX_envGT` projected away). -/
abbrev postDX (rp : RP) : MachineState × EStateX → Prop :=
  postOfX mpReaderX fun s σ => ∃ _ : Nat, Own43 rp.Q σ.r ∧ (σ.cl → (s.regs.get64 .rbx).setWidth 32 = 43)

omit [Executable.ValidLayout (layout mpReaderX)] in
/-- **`hB` for the reader** (thread `2`): `Own43` and `ebx = 43`. -/
theorem hB_DX (rp : RP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postDX rp (t.st.st, σ) → t.prom = [] → EnvRel 2 rdPlanX σ c t r g cl → cl → YPost rp c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, hown, hx⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr (.inr ⟨⟨t, hrel.ht, hx (hrel.cl hcl)⟩, hown⟩)

/-- **The x64 reader's rule on the take route** (thread `2`). -/
def relayRuleDX (rp : RP) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (YPost rp) 2 :=
  ThreadRuleRXGS.ofSafelyEnvGTX (S := mpS rp.Q) (post := postDX rp) rdPlanX_valid (mpS_le16 rp.Q)
    mpReaderX_phase1 postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_DX rp)

/-- **The x64 reader's no-fault rule** (`NoFaultRuleSX` of its take-route
rule). -/
theorem relayRuleDX_noFault (rp : RP) : NoFaultRuleSX (relayRuleDX (layout := layout) rp) :=
  noFaultRule_ofSafelyEnvGTX_struct _ _ _ _ _ _ mpReaderX_noFault

end Reader

/-! ## The initial invariants -/

section Inv

variable [layout : _root_.Layout] {f1 f2 d : BitVec 64} {sW sY sR : isa.State} {initMem : List (Loc × Val)}

/-- **The writer's initial invariant** (thread `0`). -/
theorem invYW_init [Executable.ValidLayout (layout mpWriterX)] (hL : RelayLocs f1 f2 d)
    (hW : StartWX f1 d sW) :
    (relayRuleWX (relayParams f1 f2 d) hL.P 0).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 0) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout mpWriterX⟩
  refine invGX_init (s := sW) rfl rfl (qx64_of_partialTripleEnv (mpWriterX_envG _ hL.P 0).partial rfl hW.exe
    hW.decls hW.endPc hW.pc hW.split ⟨hW.rdi, hW.rsi, split_df hW.split, split_dd hW.split,
      ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL⟩, ?_⟩)
  simp only [σInitX, Own0, relayRes, ↓reduceIte, writerRes, Res.initOf, Perm.init, writerFrac]
  exact ⟨by simp, fun p hp => by rw [hp.2], by simp, by simp <;> decide⟩

/-- **The relay's initial invariant** (thread `1`): `RK1` at `σInitX`. -/
theorem invYX_init [Executable.ValidLayout (layout relayX)] (hL : RelayLocs f1 f2 d) (hY : StartYX f1 f2 d sY) :
    (relayRuleYX (relayParams f1 f2 d) hL.Q 1).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 1) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout relayX⟩
  refine invGTRCX_init (s := sY) rfl rfl (qx64TC_of_partialTripleEnv (relayX_envGTC _ hL.Q 1).uncount rfl hY.exe
    hY.decls hY.endPc hY.pc hY.split ⟨0, ⟨hY.rdi, hY.rsi, hY.rdx, split3_f1 hY.split, split3_d hY.split,
      split3_f2 hY.split⟩,
      ⟨relayGhost_rel_F1 _, relayGhost_rel_Dt hL, ?_, 0, by show 0 < 2; decide, ?_, OkPred.flag⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, ?_⟩)
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, relayRes, relayThreadRes]
  · simp [σInitX, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]; grind
  · simp [σInitX, relayRes, relayThreadRes, Res.initOf, Perm.init, yFrac]

/-- **The reader's initial invariant** (thread `2`): `DK1` at `σInitX`. -/
theorem invDX_init [Executable.ValidLayout (layout mpReaderX)] (hL : RelayLocs f1 f2 d) (hR : StartRX f2 d sR) :
    (relayRuleDX (relayParams f1 f2 d)).Inv True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) 2) (relayGhost (relayParams f1 f2 d)) := by
  letI : CodeEnv := ⟨layout mpReaderX⟩
  refine invGTX_init (s := sR) rfl rfl (qx64T_of_partialTripleEnv (readerX_envGT _ 2).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc hR.split ⟨0, ⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩,
      relayGhost_rel_F2 hL.q_ne, ?_, 1, by show 1 < 2; decide, ?_, OkPred43.flag⟩)
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, relayRes, readerThreadRes]

end Inv

/-! ## `NPSafeP`, purity and the theorem -/

/-- **The `NPSafeP` side**: the writer through its `ThreadRuleRX`
(`NPSafe.toP`), the relay through `EnvGTCX`, the reader through the take
route. -/
theorem relayX_npSafe (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lY relayX)] [Executable.ValidLayout (lR mpReaderX)] {f1 f2 d : BitVec 64}
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWX (layout := lW) f1 d sW) (hY : StartYX (layout := lY) f1 f2 d sY)
    (hR : StartRX (layout := lR) f2 d sR) :
    ∀ tid, tid < [sW, sY, sR].length → ∀ n m, NPSafeP (model isa) Arch.tso (YPost (relayParams f1 f2 d)) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sY, sR] initMem)
      (relayRes (Config.init [sW, sY, sR] initMem).mem (relayParams f1 f2 d) tid)
      (relayGhost (relayParams f1 f2 d)) := by
  intro tid htid n m
  match tid, htid with
  | 0, _ =>
    exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (relayRuleWX (layout := lW) _ hL.P 0) n m _ _ _ _ (invYW_init (layout := lW) hL hW))
  | 1, _ =>
    exact NPSafeP.of_ruleRXGS (relayRuleYX (layout := lY) _ hL.Q 1) n m _ _ _ _ (invYX_init (layout := lY) hL hY)
  | 2, _ =>
    exact NPSafeP.of_ruleRXGS (relayRuleDX (layout := lR) _) n m _ _ _ _ (invDX_init (layout := lR) hL hR)
  | _ + 3, h => simp only [List.length_cons, List.length_nil] at h; omega

/-- The threads' all-release specifications: the writer (layout `lW`) at
thread `0`, the relay (layout `lY`) at thread `1`, the reader (layout `lR`)
elsewhere. -/
def relayNoNTSpecX (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lY relayX)] [Executable.ValidLayout (lR mpReaderX)] (f1 f2 d : BitVec 64) :
    Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := lW) [(f1, 4), (d, 4)] (mpS_le16 ⟨f1, d, ⟨0, 5⟩⟩) mpWriterX
      fun _ _ => True
  | 1 => RelPureSpecQX.ofProgram (layout := lY) [(f1, 4), (d, 4), (f2, 4)] (relayS_le16 (relayParams f1 f2 d))
      relayX fun _ _ => ∃ _ : Nat, True
  | _ + 2 => RelPureSpecQX.ofProgram (layout := lR) [(f2, 4), (d, 4)] (mpS_le16 ⟨f2, d, ⟨0, 6⟩⟩) mpReaderX
      fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the start states.** -/
theorem relayNoNTSpecX_init (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lY relayX)] [Executable.ValidLayout (lR mpReaderX)] {f1 f2 d : BitVec 64}
    {sW sY sR : isa.State} (hW : StartWX (layout := lW) f1 d sW) (hY : StartYX (layout := lY) f1 f2 d sY)
    (hR : StartRX (layout := lR) f2 d sR) :
    ∀ tid s, [sW, sY, sR][tid]? = some s → (relayNoNTSpecX lW lY lR f1 f2 d tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hW
    letI : CodeEnv := ⟨lW mpWriterX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lW) (mpWriterX_noNT (layout := lW) f1 d).partial rfl
      he hds hend hpc hsp ⟨hx0, hx1⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hx2, hsp⟩ := hY
    letI : CodeEnv := ⟨lY relayX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lY) (relayX_noNT (layout := lY) f1 d f2).uncount rfl
      he hds hend hpc hsp ⟨0, hx0, hx1, hx2, split3_f1 hsp, split3_d hsp, split3_f2 hsp⟩
  | 2, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hR
    letI : CodeEnv := ⟨lR mpReaderX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lR) (mpReaderX_noNT (layout := lR) f2 d).uncount rfl
      he hds hend hpc hsp ⟨0, hx0, hx1, split_df hsp⟩
  | _ + 3, _, hs => by cases hs

/-- **A three-thread ownership relay through `xchg`, for x64 under
`Arch.tso`** (`mp_relay3_xchg.kl`): x64 MP's writer `mpWriterX` (thread `0`,
layout `lW`, `rdi = f1`, `rsi = d`), the relay `relayX` (thread `1`, layout
`lY`, `rdi = f1`, `rsi = d`, `rdx = f2`) and x64 MP's reader `mpReaderX`
(thread `2`, layout `lR`, `rdi = f2`, `rsi = d`), none of the words in a
thread's private memory, started from an initial memory with both flags at
`0`: at every reachable final configuration the reader's `ebx` is `43` and
the data word's final value is `43`. The relay takes the data at its load of
`f1` (an acquire under `Arch.tso`), writes it and releases it with
`xchgl f2` (an `.acqRel` RMW giving the data away: `EnvGTCX`,
`ThreadRuleRXGS.ofSafelyEnvGTRCX`); the reader takes it at its load of `f2`.
Statement shape and conclusion as `mp_relay3_swpl_envG`.

As for `x64_mp_public`: only final configurations are constrained (no
fairness), `RelayLocs` does not exclude overlapping words, and faults are not
covered by the conclusion (`relayRuleWX_noFault`, `relayRuleYX_noFault`,
`relayRuleDX_noFault` are the per-thread no-fault facts). -/
theorem mp_relay3_xchg_envG {fuel : Nat} (lW lY lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lY relayX)] [Executable.ValidLayout (lR mpReaderX)] (f1 f2 d : BitVec 64)
    (hL : RelayLocs f1 f2 d) {sW sY sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWX (layout := lW) f1 d sW) (hY : StartYX (layout := lY) f1 f2 d sY)
    (hR : StartRX (layout := lR) f2 d sR)
    (hF1 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f1, 4⟩ = 0)
    (hF2 : (Config.init [sW, sY, sR] initMem).mem.initVal ⟨f2, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sY, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyQX_tsoS fuel (B := YPost (relayParams f1 f2 d))
    (Φ := fun c => (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (erase_relayInit hL _ hF1 hF2) initGhost_pend
    (relayNoNTSpecX lW lY lR f1 f2 d) (relayNoNTSpecX_init lW lY lR hW hY hR)
    (relayX_npSafe lW lY lR hL hW hY hR) hc hf
    fun _ _ E' _ hsize hB => relay_final E' hf hsize hB

end Kraken.Promising.X64.EnvG.RelayX

#print axioms Kraken.Promising.X64.EnvG.RelayX.mp_relay3_xchg_envG
#print axioms Kraken.Promising.X64.EnvG.RelayX.relayRuleWX_noFault
#print axioms Kraken.Promising.X64.EnvG.RelayX.relayRuleYX_noFault
#print axioms Kraken.Promising.X64.EnvG.RelayX.relayRuleDX_noFault
