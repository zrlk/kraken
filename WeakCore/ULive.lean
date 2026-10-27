/-
# ULive — liveness transfer to UnElab (T3)

The U machine as labelled systems, and the core liveness statements transferred to it.

* `umstep`/`umstepX` (`USpawnBy`): `TermLiveMach.mstep`/`TermLiveX.mstepX` over `UCfg`;
  `machineU`/`machineXU`/`machineXCU` (design T3 verbatim): a labelled step between images of hygienic U
  configurations (`UInv`) that the U machine takes.  Labels, `actor` and `thr` are the core's.
* `ImgU U c := ∃ u, UInv U u ∧ c = toCoreCfg u`.  On `ImgU` the U systems' steps are exactly the core
  systems' (`machineU_S_iff`, …), and `ImgU` is closed under the core steps (`imgU_closed`, …).
* **`liveness_iff`** (one theorem per headline, `liveness_iff_robust` … `liveness_iff_livelockXC`):
  `H (machineU U k arch) (S ∧ ImgU U) … ↔ H (machine (elabProg U) k arch) (S ∧ ImgU U) …` for the four
  `TermLiveMach` headlines and the three `TermLiveGrow` `…X` headlines (over `machineX` and `machineXC`).  The
  core side quantifies over the same runs (labels `Nat × Bool`), from the same start configurations.  With the
  antitone lemmas (`…_anti`: `H sys S → H sys (S ∧ Q)`) a core proof of `H (machine (elabProg U) k arch) S` gives
  `H (machineU U k arch) (S ∧ ImgU U)`.  There is no `machineU_sound` (design [K1]).
* **`explorer_iff`** (scope: per-edge, crash, `ClassHyp`): every `successorsL` edge out of an image is a U move
  of that thread into an image (`successorsL_img`); `crashCfg` commutes with `uCrashCfg` (`crashCfg_elab`);
  `ClassHyp` for a class inside `ImgU` is the same for `machineU` and `machine` (`classHyp_iff`).  Nothing is
  claimed about `exploreG`'s loop itself (its graph construction, dedup and bounds).
-/
import WeakCore.UHyg
import WeakCore.TermLiveXM0

set_option linter.unusedSimpArgs false

namespace UnElab
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermStartW TermLiveMach TermLiveGrow TermLiveX
  TermLiveXM0 TermLive
open WeakMem (Memory Ts VState AllocLabel Address Val Arch)

/-! ## §1 Two labelled systems that agree on a closed set -/

/-- A labelled system with the machine's labels, `actor` and `thr`. -/
def mkSys (S : Cfg → Nat × Bool → Cfg → Prop) : LSys where
  L := Nat × Bool
  S := S
  actor l := some l.1
  thr i := (i, true)

/-- `S₁` and `S₂` agree on `Img`, and `Img` is closed under `S₂`. -/
structure Agree (S₁ S₂ : Cfg → Nat × Bool → Cfg → Prop) (Img : Cfg → Prop) : Prop where
  iff : ∀ c, Img c → ∀ l c', S₁ c l c' ↔ S₂ c l c'
  closed : ∀ c l c', Img c → S₂ c l c' → Img c'

theorem run_img_of {S : Cfg → Nat × Bool → Cfg → Prop} {Img : Cfg → Prop}
    (hcl : ∀ c l c', Img c → S c l c' → Img c') {r : LRun (Nat × Bool)} (hr : (mkSys S).Run r)
    (h0 : Img (r.cfg 0)) : ∀ n, Img (r.cfg n)
  | 0 => h0
  | n + 1 => by
    have ih := run_img_of hcl hr h0 n
    have hm := hr n
    revert hm
    cases r.lbl n with
    | none => intro hm; rw [show r.cfg (n + 1) = r.cfg n from hm]; exact ih
    | some l => intro hm; exact hcl _ _ _ ih hm

theorem ev_mono {P Q : Nat → Prop} (h : Ev P) (f : ∀ n, P n → Q n) : Ev Q :=
  let ⟨n, hn⟩ := h
  ⟨n, fun m hm => f m (hn m hm)⟩

theorem often_mono {P Q : Nat → Prop} (h : Often P) (f : ∀ n, P n → Q n) : Often Q :=
  fun n => let ⟨m, hm, hp⟩ := h n; ⟨m, hm, f m hp⟩

section Agree
variable {S₁ S₂ : Cfg → Nat × Bool → Cfg → Prop} {Img : Cfg → Prop}

theorem Agree.closed₁ (hA : Agree S₁ S₂ Img) : ∀ c l c', Img c → S₁ c l c' → Img c' :=
  fun c l c' hc h => hA.closed c l c' hc ((hA.iff c hc l c').mp h)

theorem Agree.run_iff (hA : Agree S₁ S₂ Img) {r : LRun (Nat × Bool)} (h0 : Img (r.cfg 0)) :
    (mkSys S₁).Run r ↔ (mkSys S₂).Run r := by
  constructor
  · intro hr n
    have hI := run_img_of hA.closed₁ hr h0 n
    have hm := hr n
    revert hm
    cases r.lbl n with
    | none => exact id
    | some l => exact (hA.iff _ hI l _).mp
  · intro hr n
    have hI := run_img_of hA.closed hr h0 n
    have hm := hr n
    revert hm
    cases r.lbl n with
    | none => exact id
    | some l => exact (hA.iff _ hI l _).mpr

theorem Agree.fair_iff (hA : Agree S₁ S₂ Img) {r : LRun (Nat × Bool)} (hI : ∀ n, Img (r.cfg n))
    (D : Nat → Option Nat) (RF : LRun (Nat × Bool) → Prop) :
    Fair (mkSys S₁) r D RF ↔ Fair (mkSys S₂) r D RF := by
  constructor
  · intro h
    exact ⟨fun i hi hev => h.weak i hi (ev_mono hev fun n ⟨c', hc⟩ => ⟨c', (hA.iff _ (hI n) _ _).mpr hc⟩),
      fun i hi ho => h.prog i hi (often_mono ho fun n ⟨c', hc, hp⟩ => ⟨c', (hA.iff _ (hI n) _ _).mpr hc, hp⟩),
      h.ext⟩
  · intro h
    exact ⟨fun i hi hev => h.weak i hi (ev_mono hev fun n ⟨c', hc⟩ => ⟨c', (hA.iff _ (hI n) _ _).mp hc⟩),
      fun i hi ho => h.prog i hi (often_mono ho fun n ⟨c', hc, hp⟩ => ⟨c', (hA.iff _ (hI n) _ _).mp hc, hp⟩),
      h.ext⟩

theorem Agree.fairX_iff (hA : Agree S₁ S₂ Img) {r : LRun (Nat × Bool)} (hI : ∀ n, Img (r.cfg n))
    (D : Nat → Option Nat) (RF : LRun (Nat × Bool) → Prop) :
    FairX (mkSys S₁) r D RF ↔ FairX (mkSys S₂) r D RF := by
  constructor
  · intro h
    exact ⟨fun i hi hev => h.weak i hi (ev_mono hev fun n ⟨c', hc⟩ => ⟨c', (hA.iff _ (hI n) _ _).mpr hc⟩),
      fun i hi ho => h.prog i hi (often_mono ho fun n ⟨c', hc, hp⟩ => ⟨c', (hA.iff _ (hI n) _ _).mpr hc, hp⟩),
      h.ext⟩
  · intro h
    exact ⟨fun i hi hev => h.weak i hi (ev_mono hev fun n ⟨c', hc⟩ => ⟨c', (hA.iff _ (hI n) _ _).mp hc⟩),
      fun i hi ho => h.prog i hi (often_mono ho fun n ⟨c', hc, hp⟩ => ⟨c', (hA.iff _ (hI n) _ _).mp hc, hp⟩),
      h.ext⟩

variable (hA : Agree S₁ S₂ Img) {Setting : Cfg → Prop} (hSI : ∀ c, Setting c → Img c)
include hA hSI

theorem Agree.robust_iff (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robust (mkSys S₁) Setting Mentioned hv ↔
      no_induced_livelock_robust (mkSys S₂) Setting Mentioned hv := by
  constructor
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mpr hr) h0 hcoh hres hcr
      ((hA.fair_iff (run_img_of hA.closed hr hI0) D _).mpr hf)
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mp hr) h0 hcoh hres hcr
      ((hA.fair_iff (run_img_of hA.closed₁ hr hI0) D _).mp hf)

theorem Agree.tokenFree_iff (Mentioned : Proto → Prop) (hv : HoldView) :
    robust_tokenFree (mkSys S₁) Setting Mentioned hv ↔ robust_tokenFree (mkSys S₂) Setting Mentioned hv := by
  constructor
  · intro H c₀ hS hR r hr h0
    exact H c₀ hS hR r ((hA.run_iff (h0 ▸ hSI _ hS)).mpr hr) h0
  · intro H c₀ hS hR r hr h0
    exact H c₀ hS hR r ((hA.run_iff (h0 ▸ hSI _ hS)).mp hr) h0

theorem Agree.forced_iff (hv : HoldView) :
    forced_wait_is_livelock (mkSys S₁) Setting hv ↔ forced_wait_is_livelock (mkSys S₂) Setting hv := by
  constructor
  · intro H c₀ hS r D i b n P h m n₀ hr h0 hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS r D i b n P h m n₀ ((hA.run_iff hI0).mpr hr) h0 hcr
      ((hA.fair_iff (run_img_of hA.closed hr hI0) D _).mpr hf)
  · intro H c₀ hS r D i b n P h m n₀ hr h0 hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS r D i b n P h m n₀ ((hA.run_iff hI0).mp hr) h0 hcr
      ((hA.fair_iff (run_img_of hA.closed₁ hr hI0) D _).mp hf)

theorem Agree.livelock_iff (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop) :
    no_induced_livelock (mkSys S₁) Setting Mentioned Reclaimed hv RF ReclaimerOK ↔
      no_induced_livelock (mkSys S₂) Setting Mentioned Reclaimed hv RF ReclaimerOK := by
  constructor
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf hok
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mpr hr) h0 hcoh hres hcr
      ((hA.fair_iff (run_img_of hA.closed hr hI0) D _).mpr hf) hok
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf hok
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mp hr) h0 hcoh hres hcr
      ((hA.fair_iff (run_img_of hA.closed₁ hr hI0) D _).mp hf) hok

theorem Agree.robustX_iff (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robustX (mkSys S₁) Setting Mentioned hv ↔
      no_induced_livelock_robustX (mkSys S₂) Setting Mentioned hv := by
  constructor
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mpr hr) h0 hcoh hres hcr
      ((hA.fairX_iff (run_img_of hA.closed hr hI0) D _).mpr hf)
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mp hr) h0 hcoh hres hcr
      ((hA.fairX_iff (run_img_of hA.closed₁ hr hI0) D _).mp hf)

theorem Agree.forcedX_iff (hv : HoldView) :
    forced_wait_is_livelockX (mkSys S₁) Setting hv ↔ forced_wait_is_livelockX (mkSys S₂) Setting hv := by
  constructor
  · intro H c₀ hS r D i b n P h m n₀ hr h0 hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS r D i b n P h m n₀ ((hA.run_iff hI0).mpr hr) h0 hcr
      ((hA.fairX_iff (run_img_of hA.closed hr hI0) D _).mpr hf)
  · intro H c₀ hS r D i b n P h m n₀ hr h0 hcr hf
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS r D i b n P h m n₀ ((hA.run_iff hI0).mp hr) h0 hcr
      ((hA.fairX_iff (run_img_of hA.closed₁ hr hI0) D _).mp hf)

theorem Agree.livelockX_iff (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop) :
    no_induced_livelockX (mkSys S₁) Setting Mentioned Reclaimed hv RF ReclaimerOK ↔
      no_induced_livelockX (mkSys S₂) Setting Mentioned Reclaimed hv RF ReclaimerOK := by
  constructor
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf hok
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mpr hr) h0 hcoh hres hcr
      ((hA.fairX_iff (run_img_of hA.closed hr hI0) D _).mpr hf) hok
  · intro H c₀ hS hR r D hr h0 hcoh hres hcr hf hok
    have hI0 : Img (r.cfg 0) := h0 ▸ hSI _ hS
    exact H c₀ hS hR r D ((hA.run_iff hI0).mp hr) h0 hcoh hres hcr
      ((hA.fairX_iff (run_img_of hA.closed₁ hr hI0) D _).mp hf) hok

end Agree

/-! ## §2 The U labelled systems -/

/-- `mstep` over U configurations: `(i, true)` a certified thread step, `(i, false)` a certified promise. -/
def umstep (U : UProg) (k : Promises.Knobs) (arch : Arch) (u : UCfg) : Nat × Bool → UCfg → Prop
  | (i, true), u' => u' ∈ uThreadSteps U k arch u i ∧ UCertified U k arch u' i
  | (i, false), u' => ∃ a v w, i < u.ths.size ∧ w < u.mem.size ∧
      UCertified U k arch (uPromise u i a v w) i ∧ u' = uPromise u i a v w

/-- Thread `i` of `u` spawns (`SpawnBy` over U configurations). -/
def USpawnBy (_U : UProg) (_k : Promises.Knobs) (_arch : Arch) (cap : Nat) (u : UCfg) (i : Nat) (u' : UCfg) :
    Prop :=
  ∃ (x f : String) (a : At) (T : Ty) (ts : List Ty) (j : Nat) (e : UExpr) (th : UTTh) (rt : Ty) (ws : List Word),
    u.ths[i]? = some th ∧ layer th.ctr th.term = .letOp x (.spawn f a T ts) j e ∧ th.promises = [] ∧
    u.ths.size < cap ∧ evalAt th.env a = some (rt, ws) ∧ u' = uSpawnCfg u i th x e j f ts T ws

/-- `mstepX` over U configurations. -/
def umstepX (U : UProg) (k : Promises.Knobs) (arch : Arch) (cap : Nat) (u : UCfg) : Nat × Bool → UCfg → Prop
  | (i, true), u' => umstep U k arch u (i, true) u' ∨ USpawnBy U k arch cap u i u'
  | (i, false), u' => umstep U k arch u (i, false) u'

/-- The core configurations that are images of hygienic U configurations. -/
def ImgU (U : UProg) (c : Cfg) : Prop := ∃ u, UInv U u ∧ c = toCoreCfg u

/-- **The U machine** (design T3): a step between images of hygienic U configurations that the U machine
takes. -/
def machineU (U : UProg) (k : Promises.Knobs) (arch : Arch) : LSys where
  L := Nat × Bool
  S c l c' := ∃ u u', UInv U u ∧ c = toCoreCfg u ∧ c' = toCoreCfg u' ∧ umstep U k arch u l u'
  actor l := some l.1
  thr i := (i, true)

/-- The U spawn machine at capacity `cap`. -/
def machineXU (U : UProg) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : LSys where
  L := Nat × Bool
  S c l c' := ∃ u u', UInv U u ∧ c = toCoreCfg u ∧ c' = toCoreCfg u' ∧ umstepX U k arch cap u l u'
  actor l := some l.1
  thr i := (i, true)

/-- The U spawn machine at the source configuration's own capacity (`machineXC`). -/
def machineXCU (U : UProg) (k : Promises.Knobs) (arch : Arch) : LSys where
  L := Nat × Bool
  S c l c' := ∃ u u', UInv U u ∧ c = toCoreCfg u ∧ c' = toCoreCfg u' ∧ umstepX U k arch u.cap u l u'
  actor l := some l.1
  thr i := (i, true)

section Lifts
variable {U : UProg} {k : Promises.Knobs} {arch : Arch}

theorem umstep.toCore {u u' : UCfg} {l : Nat × Bool} (h : umstep U k arch u l u') :
    mstep (elabProg U) k arch (toCoreCfg u) l (toCoreCfg u') := by
  obtain ⟨i, b⟩ := l
  cases b with
  | true =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨mem_threadSteps_elab.mpr ⟨_, h1, rfl⟩, uCertified_iff.mp h2⟩
  | false =>
    obtain ⟨a, v, w, hi, hw, hc, rfl⟩ := h
    exact ⟨a, v, w, by simpa using hi, by simpa using hw, by rw [promise_elab]; exact uCertified_iff.mp hc,
      (promise_elab u i a v w).symm⟩

theorem umstep.ofCore {u : UCfg} {l : Nat × Bool} {d : Cfg} (h : mstep (elabProg U) k arch (toCoreCfg u) l d) :
    ∃ u', umstep U k arch u l u' ∧ d = toCoreCfg u' := by
  obtain ⟨i, b⟩ := l
  cases b with
  | true =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨u', h1', rfl⟩ := mem_threadSteps_elab.mp h1
    exact ⟨u', ⟨h1', uCertified_iff.mpr h2⟩, rfl⟩
  | false =>
    obtain ⟨a, v, w, hi, hw, hc, rfl⟩ := h
    refine ⟨uPromise u i a v w, ⟨a, v, w, by simpa using hi, by simpa using hw, ?_, rfl⟩, promise_elab u i a v w⟩
    rw [uCertified_iff, ← promise_elab]; exact hc

theorem USpawnBy.toCore {cap : Nat} {u u' : UCfg} {i : Nat} (h : USpawnBy U k arch cap u i u') :
    SpawnBy (elabProg U) k arch cap (toCoreCfg u) i (toCoreCfg u') := by
  obtain ⟨x, f, a, T, ts, j, e, th, rt, ws, hth, hl, hp, hcap, hev, rfl⟩ := h
  refine ⟨x, f, a, T, ts, elabT j e, toCoreTh th, rt, ws, by rw [toCoreCfg_get, hth]; rfl, ?_, hp,
    by simpa using hcap, hev, spawnCfg_elab u i th x e j f ts T ws⟩
  show elabT th.ctr th.term = _
  rw [elab_layer, hl]; rfl

theorem USpawnBy.ofCore {cap : Nat} {u : UCfg} {i : Nat} {d : Cfg}
    (h : SpawnBy (elabProg U) k arch cap (toCoreCfg u) i d) : ∃ u', USpawnBy U k arch cap u i u' ∧ d = toCoreCfg u' := by
  obtain ⟨x, f, a, T, ts, e, th', rt, ws, hth, hterm, hp, hcap, hev, rfl⟩ := h
  rw [toCoreCfg_get] at hth
  cases hc : u.ths[i]? with
  | none => rw [hc] at hth; simp at hth
  | some th =>
    rw [hc] at hth
    simp only [Option.map_some, Option.some.injEq] at hth
    subst hth
    obtain ⟨j, e', hl, rfl⟩ := layer_let_inv hterm
    exact ⟨_, ⟨x, f, a, T, ts, j, e', th, rt, ws, hc, hl, hp, by simpa using hcap, hev, rfl⟩,
      (spawnCfg_elab u i th x e' j f ts T ws).symm⟩

theorem umstepX.toCore {cap : Nat} {u u' : UCfg} {l : Nat × Bool} (h : umstepX U k arch cap u l u') :
    mstepX (elabProg U) k arch cap (toCoreCfg u) l (toCoreCfg u') := by
  obtain ⟨i, b⟩ := l
  cases b with
  | true =>
    rcases h with h | h
    · exact Or.inl h.toCore
    · exact Or.inr h.toCore
  | false => exact umstep.toCore (l := (i, false)) h

theorem umstepX.ofCore {cap : Nat} {u : UCfg} {l : Nat × Bool} {d : Cfg}
    (h : mstepX (elabProg U) k arch cap (toCoreCfg u) l d) : ∃ u', umstepX U k arch cap u l u' ∧ d = toCoreCfg u' := by
  obtain ⟨i, b⟩ := l
  cases b with
  | true =>
    rcases h with h | h
    · obtain ⟨u', h', rfl⟩ := umstep.ofCore (l := (i, true)) h
      exact ⟨u', Or.inl h', rfl⟩
    · obtain ⟨u', h', rfl⟩ := USpawnBy.ofCore h
      exact ⟨u', Or.inr h', rfl⟩
  | false => exact umstep.ofCore (l := (i, false)) h

theorem umstep.inv {u u' : UCfg} {l : Nat × Bool} (h : umstep U k arch u l u') (hu : UInv U u) : UInv U u' := by
  obtain ⟨i, b⟩ := l
  cases b with
  | true => exact uThreadSteps_inv hu h.1
  | false =>
    obtain ⟨a, v, w, -, -, -, rfl⟩ := h
    exact uPromise_inv a v w hu

theorem USpawnBy.inv {cap : Nat} {u u' : UCfg} {i : Nat} (h : USpawnBy U k arch cap u i u') (hu : UInv U u) :
    UInv U u' := by
  obtain ⟨x, f, a, T, ts, j, e, th, rt, ws, hth, hl, -, -, -, rfl⟩ := h
  exact uSpawnCfg_inv f ts T ws hu hth hl

theorem umstepX.inv {cap : Nat} {u u' : UCfg} {l : Nat × Bool} (h : umstepX U k arch cap u l u')
    (hu : UInv U u) : UInv U u' := by
  obtain ⟨i, b⟩ := l
  cases b with
  | true =>
    rcases h with h | h
    · exact umstep.inv (l := (i, true)) h hu
    · exact h.inv hu
  | false => exact umstep.inv (l := (i, false)) h hu

/-! ## §3 Agreement on images -/

/-- **(ii)** On images the U machine's steps are the core machine's. -/
theorem machineU_S_iff {c : Cfg} (hc : ImgU U c) (l : Nat × Bool) (c' : Cfg) :
    (machineU U k arch).S c l c' ↔ (machine (elabProg U) k arch).S c l c' := by
  constructor
  · rintro ⟨u, u', -, rfl, rfl, h⟩
    exact h.toCore
  · intro h
    obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨u', h', rfl⟩ := umstep.ofCore h
    exact ⟨u, u', hu, rfl, rfl, h'⟩

/-- Images are closed under the core machine's steps. -/
theorem imgU_closed {c : Cfg} {l : Nat × Bool} {c' : Cfg} (hc : ImgU U c)
    (h : (machine (elabProg U) k arch).S c l c') : ImgU U c' := by
  obtain ⟨u, hu, rfl⟩ := hc
  obtain ⟨u', h', rfl⟩ := umstep.ofCore h
  exact ⟨u', h'.inv hu, rfl⟩

theorem machineXU_S_iff {cap : Nat} {c : Cfg} (hc : ImgU U c) (l : Nat × Bool) (c' : Cfg) :
    (machineXU U k arch cap).S c l c' ↔ (machineX (elabProg U) k arch cap).S c l c' := by
  constructor
  · rintro ⟨u, u', -, rfl, rfl, h⟩
    exact h.toCore
  · intro h
    obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨u', h', rfl⟩ := umstepX.ofCore h
    exact ⟨u, u', hu, rfl, rfl, h'⟩

theorem imgU_closedX {cap : Nat} {c : Cfg} {l : Nat × Bool} {c' : Cfg} (hc : ImgU U c)
    (h : (machineX (elabProg U) k arch cap).S c l c') : ImgU U c' := by
  obtain ⟨u, hu, rfl⟩ := hc
  obtain ⟨u', h', rfl⟩ := umstepX.ofCore h
  exact ⟨u', h'.inv hu, rfl⟩

theorem machineXCU_S_iff {c : Cfg} (hc : ImgU U c) (l : Nat × Bool) (c' : Cfg) :
    (machineXCU U k arch).S c l c' ↔ (machineXC (elabProg U) k arch).S c l c' := by
  constructor
  · rintro ⟨u, u', -, rfl, rfl, h⟩
    exact h.toCore
  · intro h
    obtain ⟨u, hu, rfl⟩ := hc
    obtain ⟨u', h', rfl⟩ := umstepX.ofCore h
    exact ⟨u, u', hu, rfl, rfl, h'⟩

theorem imgU_closedXC {c : Cfg} {l : Nat × Bool} {c' : Cfg} (hc : ImgU U c)
    (h : (machineXC (elabProg U) k arch).S c l c') : ImgU U c' := by
  obtain ⟨u, hu, rfl⟩ := hc
  obtain ⟨u', h', rfl⟩ := umstepX.ofCore h
  exact ⟨u', h'.inv hu, rfl⟩

theorem agree_machine : Agree (machineU U k arch).S (machine (elabProg U) k arch).S (ImgU U) :=
  ⟨fun _ hc => machineU_S_iff hc, fun _ _ _ hc h => imgU_closed hc h⟩

theorem agree_machineX (cap : Nat) :
    Agree (machineXU U k arch cap).S (machineX (elabProg U) k arch cap).S (ImgU U) :=
  ⟨fun _ hc => machineXU_S_iff hc, fun _ _ _ hc h => imgU_closedX hc h⟩

theorem agree_machineXC : Agree (machineXCU U k arch).S (machineXC (elabProg U) k arch).S (ImgU U) :=
  ⟨fun _ hc => machineXCU_S_iff hc, fun _ _ _ hc h => imgU_closedXC hc h⟩

/-- The wrapper start of a program with no reserved user name is an image. -/
theorem imgU_startW (hU : noReserved U = true) (cap : Nat) : ImgU U (startW (elabProg U) cap) :=
  ⟨startU U cap, uInv_start hU cap, (toCoreCfg_startU U cap).symm⟩

end Lifts

/-! ## §4 Liveness transfer (T3)

Each `liveness_iff_…` states, for one core headline `H`, that `H` for the U system and `H` for the core system
are equivalent over start configurations satisfying `S` that are images of hygienic U configurations.  Both
sides quantify over the same runs `LRun (Nat × Bool)`, crash maps, holds and fairness extensions.  The
`…_anti` lemmas weaken a setting, and the `…_transfer` corollaries combine the two: a core `H` for
`machine (elabProg U) k arch` and any `S` gives the U `H` on `S ∧ ImgU U`.  No `machineU_sound` is stated
(design [K1]). -/

section Transfer
variable {U : UProg} {k : Promises.Knobs} {arch : Arch}

/-! Antitone in the setting. -/

theorem robust_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robust sys S Mentioned hv → no_induced_livelock_robust sys S' Mentioned hv :=
  fun H c₀ h => H c₀ (hS _ h)

theorem tokenFree_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (Mentioned : Proto → Prop) (hv : HoldView) :
    robust_tokenFree sys S Mentioned hv → robust_tokenFree sys S' Mentioned hv :=
  fun H c₀ h => H c₀ (hS _ h)

theorem forced_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (hv : HoldView) :
    forced_wait_is_livelock sys S hv → forced_wait_is_livelock sys S' hv :=
  fun H c₀ h => H c₀ (hS _ h)

theorem livelock_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun sys.L → Prop)
    (ReclaimerOK : LRun sys.L → (Nat → Option Nat) → Prop) :
    no_induced_livelock sys S Mentioned Reclaimed hv RF ReclaimerOK → no_induced_livelock sys S' Mentioned Reclaimed hv RF ReclaimerOK :=
  fun H c₀ h => H c₀ (hS _ h)

theorem robustX_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robustX sys S Mentioned hv → no_induced_livelock_robustX sys S' Mentioned hv :=
  fun H c₀ h => H c₀ (hS _ h)

theorem forcedX_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (hv : HoldView) :
    forced_wait_is_livelockX sys S hv → forced_wait_is_livelockX sys S' hv :=
  fun H c₀ h => H c₀ (hS _ h)

theorem livelockX_anti (sys : LSys) {S S' : Cfg → Prop} (hS : ∀ c, S' c → S c) (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun sys.L → Prop)
    (ReclaimerOK : LRun sys.L → (Nat → Option Nat) → Prop) :
    no_induced_livelockX sys S Mentioned Reclaimed hv RF ReclaimerOK → no_induced_livelockX sys S' Mentioned Reclaimed hv RF ReclaimerOK :=
  fun H c₀ h => H c₀ (hS _ h)

/-- **T3 (no_induced_livelock_robust)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_robust (S : Cfg → Prop) (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robust (machineU U k arch) (fun c => S c ∧ ImgU U c) Mentioned hv ↔
      no_induced_livelock_robust (machine (elabProg U) k arch) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (agree_machine).robust_iff (fun _ h => h.2) Mentioned hv

theorem robust_transfer {S : Cfg → Prop} (Mentioned : Proto → Prop) (hv : HoldView)
    (h : no_induced_livelock_robust (machine (elabProg U) k arch) S Mentioned hv) :
    no_induced_livelock_robust (machineU U k arch) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (liveness_iff_robust S Mentioned hv).mpr (robust_anti _ (fun _ hc => hc.1) Mentioned hv h)

/-- **T3 (robust_tokenFree)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_tokenFree (S : Cfg → Prop) (Mentioned : Proto → Prop) (hv : HoldView) :
    robust_tokenFree (machineU U k arch) (fun c => S c ∧ ImgU U c) Mentioned hv ↔
      robust_tokenFree (machine (elabProg U) k arch) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (agree_machine).tokenFree_iff (fun _ h => h.2) Mentioned hv

theorem tokenFree_transfer {S : Cfg → Prop} (Mentioned : Proto → Prop) (hv : HoldView)
    (h : robust_tokenFree (machine (elabProg U) k arch) S Mentioned hv) :
    robust_tokenFree (machineU U k arch) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (liveness_iff_tokenFree S Mentioned hv).mpr (tokenFree_anti _ (fun _ hc => hc.1) Mentioned hv h)

/-- **T3 (forced_wait_is_livelock)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_forced (S : Cfg → Prop) (hv : HoldView) :
    forced_wait_is_livelock (machineU U k arch) (fun c => S c ∧ ImgU U c) hv ↔
      forced_wait_is_livelock (machine (elabProg U) k arch) (fun c => S c ∧ ImgU U c) hv :=
  (agree_machine).forced_iff (fun _ h => h.2) hv

theorem forced_transfer {S : Cfg → Prop} (hv : HoldView)
    (h : forced_wait_is_livelock (machine (elabProg U) k arch) S hv) :
    forced_wait_is_livelock (machineU U k arch) (fun c => S c ∧ ImgU U c) hv :=
  (liveness_iff_forced S hv).mpr (forced_anti _ (fun _ hc => hc.1) hv h)

/-- **T3 (no_induced_livelock)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_livelock (S : Cfg → Prop) (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop) :
    no_induced_livelock (machineU U k arch) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK ↔
      no_induced_livelock (machine (elabProg U) k arch) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK :=
  (agree_machine).livelock_iff (fun _ h => h.2) Mentioned Reclaimed hv RF ReclaimerOK

theorem livelock_transfer {S : Cfg → Prop} (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop)
    (h : no_induced_livelock (machine (elabProg U) k arch) S Mentioned Reclaimed hv RF ReclaimerOK) :
    no_induced_livelock (machineU U k arch) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK :=
  (liveness_iff_livelock S Mentioned Reclaimed hv RF ReclaimerOK).mpr (livelock_anti (machine (elabProg U) k arch) (fun _ hc => hc.1) Mentioned Reclaimed hv RF ReclaimerOK h)

/-- **T3 (no_induced_livelock_robustX, spawn machine at capacity `cap`)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_robustX {cap : Nat} (S : Cfg → Prop) (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robustX (machineXU U k arch cap) (fun c => S c ∧ ImgU U c) Mentioned hv ↔
      no_induced_livelock_robustX (machineX (elabProg U) k arch cap) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (agree_machineX cap).robustX_iff (fun _ h => h.2) Mentioned hv

theorem robustX_transfer {cap : Nat} {S : Cfg → Prop} (Mentioned : Proto → Prop) (hv : HoldView)
    (h : no_induced_livelock_robustX (machineX (elabProg U) k arch cap) S Mentioned hv) :
    no_induced_livelock_robustX (machineXU U k arch cap) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (liveness_iff_robustX S Mentioned hv).mpr (robustX_anti _ (fun _ hc => hc.1) Mentioned hv h)

/-- **T3 (forced_wait_is_livelockX, spawn machine at capacity `cap`)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_forcedX {cap : Nat} (S : Cfg → Prop) (hv : HoldView) :
    forced_wait_is_livelockX (machineXU U k arch cap) (fun c => S c ∧ ImgU U c) hv ↔
      forced_wait_is_livelockX (machineX (elabProg U) k arch cap) (fun c => S c ∧ ImgU U c) hv :=
  (agree_machineX cap).forcedX_iff (fun _ h => h.2) hv

theorem forcedX_transfer {cap : Nat} {S : Cfg → Prop} (hv : HoldView)
    (h : forced_wait_is_livelockX (machineX (elabProg U) k arch cap) S hv) :
    forced_wait_is_livelockX (machineXU U k arch cap) (fun c => S c ∧ ImgU U c) hv :=
  (liveness_iff_forcedX S hv).mpr (forcedX_anti _ (fun _ hc => hc.1) hv h)

/-- **T3 (no_induced_livelockX, spawn machine at capacity `cap`)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_livelockX {cap : Nat} (S : Cfg → Prop) (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop) :
    no_induced_livelockX (machineXU U k arch cap) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK ↔
      no_induced_livelockX (machineX (elabProg U) k arch cap) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK :=
  (agree_machineX cap).livelockX_iff (fun _ h => h.2) Mentioned Reclaimed hv RF ReclaimerOK

theorem livelockX_transfer {cap : Nat} {S : Cfg → Prop} (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop)
    (h : no_induced_livelockX (machineX (elabProg U) k arch cap) S Mentioned Reclaimed hv RF ReclaimerOK) :
    no_induced_livelockX (machineXU U k arch cap) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK :=
  (liveness_iff_livelockX S Mentioned Reclaimed hv RF ReclaimerOK).mpr (livelockX_anti (machineX (elabProg U) k arch cap) (fun _ hc => hc.1) Mentioned Reclaimed hv RF ReclaimerOK h)

/-- **T3 (no_induced_livelock_robustX, spawn machine at the configuration's capacity)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_robustXC (S : Cfg → Prop) (Mentioned : Proto → Prop) (hv : HoldView) :
    no_induced_livelock_robustX (machineXCU U k arch) (fun c => S c ∧ ImgU U c) Mentioned hv ↔
      no_induced_livelock_robustX (machineXC (elabProg U) k arch) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (agree_machineXC).robustX_iff (fun _ h => h.2) Mentioned hv

theorem robustXC_transfer {S : Cfg → Prop} (Mentioned : Proto → Prop) (hv : HoldView)
    (h : no_induced_livelock_robustX (machineXC (elabProg U) k arch) S Mentioned hv) :
    no_induced_livelock_robustX (machineXCU U k arch) (fun c => S c ∧ ImgU U c) Mentioned hv :=
  (liveness_iff_robustXC S Mentioned hv).mpr (robustX_anti _ (fun _ hc => hc.1) Mentioned hv h)

/-- **T3 (forced_wait_is_livelockX, spawn machine at the configuration's capacity)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_forcedXC (S : Cfg → Prop) (hv : HoldView) :
    forced_wait_is_livelockX (machineXCU U k arch) (fun c => S c ∧ ImgU U c) hv ↔
      forced_wait_is_livelockX (machineXC (elabProg U) k arch) (fun c => S c ∧ ImgU U c) hv :=
  (agree_machineXC).forcedX_iff (fun _ h => h.2) hv

theorem forcedXC_transfer {S : Cfg → Prop} (hv : HoldView)
    (h : forced_wait_is_livelockX (machineXC (elabProg U) k arch) S hv) :
    forced_wait_is_livelockX (machineXCU U k arch) (fun c => S c ∧ ImgU U c) hv :=
  (liveness_iff_forcedXC S hv).mpr (forcedX_anti _ (fun _ hc => hc.1) hv h)

/-- **T3 (no_induced_livelockX, spawn machine at the configuration's capacity)**: the U system and the core system agree on image starts. -/
theorem liveness_iff_livelockXC (S : Cfg → Prop) (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop) :
    no_induced_livelockX (machineXCU U k arch) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK ↔
      no_induced_livelockX (machineXC (elabProg U) k arch) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK :=
  (agree_machineXC).livelockX_iff (fun _ h => h.2) Mentioned Reclaimed hv RF ReclaimerOK

theorem livelockXC_transfer {S : Cfg → Prop} (Mentioned Reclaimed : Proto → Prop) (hv : HoldView) (RF : LRun (Nat × Bool) → Prop)
    (ReclaimerOK : LRun (Nat × Bool) → (Nat → Option Nat) → Prop)
    (h : no_induced_livelockX (machineXC (elabProg U) k arch) S Mentioned Reclaimed hv RF ReclaimerOK) :
    no_induced_livelockX (machineXCU U k arch) (fun c => S c ∧ ImgU U c) Mentioned Reclaimed hv RF ReclaimerOK :=
  (liveness_iff_livelockXC S Mentioned Reclaimed hv RF ReclaimerOK).mpr (livelockX_anti (machineXC (elabProg U) k arch) (fun _ hc => hc.1) Mentioned Reclaimed hv RF ReclaimerOK h)

end Transfer

/-! ## §5 The explorer (`explorer_iff`; scope: per edge, crash, `ClassHyp`)

`successorsL`'s edges out of an image are U moves of the edge's thread into images; `crashCfg` commutes with
`uCrashCfg`; `ClassHyp` is the same for `machineU` and `machine` on classes of images.  Nothing here is about
`exploreG`'s loop (graph construction, deduplication, bounds): only about the successor function and crash it
calls, and the class hypothesis its verdict is read against. -/

/-- The three kinds of `successorsL` edge: a thread step, a promise, an extern move of the edge's thread. -/
theorem successorsL_cases {p : Prog} {k : Promises.Knobs} {arch : Arch} {b : Bounds} {c : Cfg} {i : Nat}
    {t : Bool} {d : Cfg} (h : (i, t, d) ∈ successorsL p k arch b c) :
    d ∈ threadSteps p k arch c i ∨ (∃ a v w, d = promise c i a v w) ∨ d ∈ extSuccs p k arch b c i ∨
      d ∈ wakeSuccs p k arch b c i := by
  unfold successorsL at h
  dsimp only at h
  split at h
  · simp only [List.mem_map, Prod.mk.injEq] at h
    obtain ⟨c', hc', rfl, -, rfl⟩ := h
    exact Or.inl hc'
  · simp only [List.mem_flatMap, List.mem_append] at h
    obtain ⟨i', -, h⟩ := h
    rcases h with ((h | h) | h) | h
    · simp only [List.mem_map, List.mem_filter, Prod.mk.injEq] at h
      obtain ⟨c', ⟨hc', -⟩, rfl, -, rfl⟩ := h
      exact Or.inl hc'
    · split at h
      · split at h
        · simp only [List.mem_map, List.mem_filter, List.mem_flatMap, Prod.mk.injEq] at h
          obtain ⟨c', ⟨⟨av, -, w, -, rfl⟩, -⟩, rfl, -, rfl⟩ := h
          exact Or.inr (Or.inl ⟨av.1, av.2, w, rfl⟩)
        · simp at h
      · simp at h
    · simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨c', hc', rfl, -, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl hc'))
    · simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨c', hc', rfl, -, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inr hc'))

/-- Thread `i` of a U configuration stops (`crashCfg`): its term becomes `ret crashed`, its stack empty. -/
def uCrashCfg (u : UCfg) (i : Nat) : Option UCfg :=
  match u.ths[i]? with
  | some th =>
      if uIsDone th || !th.promises.isEmpty then none
      else some { u with ths := u.ths.set! i { th with term := .ret (.at (.var "crashed")), stack := [] } }
  | none => none

/-- (D4) `uWake` keeps the hygiene invariant: it changes only a permit. -/
theorem uWake_inv {U : UProg} {c : UCfg} (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) (hc : UInv U c) :
    UInv U (uWake c i v n ws) := by
  refine ⟨hc.1, fun i' t ht => ?_⟩
  rcases uWake_get c i v n ws i' with h' | ⟨t0, _, h2, h3⟩
  · rw [h'] at ht; exact hc.2 i' t ht
  · rw [h3] at ht; obtain rfl := Option.some.inj ht; exact hc.2 i' t0 h2

section Explorer
variable {U : UProg} {k : Promises.Knobs} {arch : Arch}

/-- **Explorer edges** out of an image are U moves of the edge's thread (a thread step, a promise, an extern
move at an extern layer) into hygienic configurations. -/
theorem successorsL_img {b : Bounds} {u : UCfg} {i : Nat} {t : Bool} {d : Cfg} (hu : UInv U u)
    (h : (i, t, d) ∈ successorsL (elabProg U) k arch b (toCoreCfg u)) :
    ∃ u', UInv U u' ∧ d = toCoreCfg u' ∧
      (u' ∈ uThreadSteps U k arch u i ∨ (∃ a v w, u' = uPromise u i a v w) ∨
        ∃ (th : UTTh) (x : String) (n : ExtName) (a : At) (j : Nat) (e : UExpr) (ws rs : List Word),
          u.ths[i]? = some th ∧ layer th.ctr th.term = .letOp x (.ext n a) j e ∧
          u' = uWake (uExtCfg u i th x n e j ws rs) i (relView th.vs) n ws) := by
  rcases successorsL_cases h with h | ⟨a, v, w, rfl⟩ | h | h
  · obtain ⟨u', h', rfl⟩ := mem_threadSteps_elab.mp h
    exact ⟨u', uThreadSteps_inv hu h', rfl, Or.inl h'⟩
  · exact ⟨uPromise u i a v w, uPromise_inv a v w hu, promise_elab u i a v w, Or.inr (Or.inl ⟨a, v, w, rfl⟩)⟩
  · unfold extSuccs at h
    rw [toCoreCfg_get] at h
    cases hth : u.ths[i]? with
    | none => simp [hth] at h
    | some th =>
      simp only [hth, Option.map_some] at h
      split at h
      · rename_i x n a e heq
        obtain ⟨j, e', hl, rfl⟩ := layer_let_inv heq
        split at h
        · simp at h
        · split at h
          · rename_i ws _
            simp only [List.mem_map, List.mem_filter] at h
            obtain ⟨rs, -, rfl⟩ := h
            refine ⟨uWake (uExtCfg u i th x n e' j ws rs) i (relView th.vs) n ws,
              uWake_inv i (relView th.vs) n ws (uExtCfg_inv ws rs hu hth hl),
              by rw [wake_elab, extCfg_elab hth x n e' j ws rs]; rfl, Or.inr (Or.inr ⟨th, x, n, a, j, e', ws, rs, rfl, hl, rfl⟩)⟩
          · simp at h
      · simp at h
  · unfold wakeSuccs at h
    rw [toCoreCfg_get] at h
    cases hth : u.ths[i]? with
    | none => simp [hth] at h
    | some th =>
      simp only [hth, Option.map_some] at h
      split at h
      · rename_i x a e heq
        obtain ⟨j, e', hl, rfl⟩ := layer_let_inv heq
        split at h
        · simp at h
        · split at h
          · rename_i ws _
            simp only [List.mem_filter, List.mem_singleton] at h
            obtain ⟨rfl, -⟩ := h
            refine ⟨uWake (uExtCfg u i th x .park e' j ws []) i (relView th.vs) .park ws,
              uWake_inv i (relView th.vs) .park ws (uExtCfg_inv ws [] hu hth hl),
              by rw [wake_elab, extCfg_elab hth x .park e' j ws []]; try rfl,
              Or.inr (Or.inr ⟨th, x, .park, a, j, e', ws, [], rfl, hl, rfl⟩)⟩
          · simp at h
      · simp at h

/-- **Crash commutes with the image.** -/
theorem crashCfg_elab (u : UCfg) (i : Nat) : crashCfg (toCoreCfg u) i = (uCrashCfg u i).map toCoreCfg := by
  unfold crashCfg uCrashCfg
  rw [toCoreCfg_get]
  cases h : u.ths[i]? with
  | none => rfl
  | some th =>
    simp only [Option.map_some, isDone_elab]
    have hp : (toCoreTh th).promises = th.promises := rfl
    rw [hp]
    split
    · rfl
    · simp [toCoreCfg, Array.set!, toCoreTh, elabT, elabArg, lets]

theorem uCrashCfg_inv {u u' : UCfg} {i : Nat} (hu : UInv U u) (h : uCrashCfg u i = some u') : UInv U u' := by
  unfold uCrashCfg at h
  cases hth : u.ths[i]? with
  | none => simp [hth] at h
  | some th =>
    simp only [hth] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨hu.1, uInv_set hu ?_ _ rfl⟩
      have ht := hu.2 i th hth
      refine ⟨?_, ht.2.1, fun f hf => by simp at hf⟩
      intro s hs
      simp only [uNames, argNames, atNames, List.append_nil, List.mem_singleton] at hs
      subst hs
      exact okName_of_res (by simp [reserved])

/-- **`ClassHyp` on a class of images** is the same for the U machine and the core machine. -/
theorem classHyp_iff {C : List Cfg} {E : List Edge} {c₀ : Cfg} {i : Nat} (hC : ∀ c ∈ C, ImgU U c) :
    ClassHyp (machineU U k arch) C E c₀ i ↔ ClassHyp (machine (elabProg U) k arch) C E c₀ i := by
  constructor
  · intro h
    exact { edge := fun e he =>
              let ⟨h1, h2, h3, h4⟩ := h.edge e he
              ⟨(machineU_S_iff (hC _ h2) _ _).mp h1, h2, h3, h4⟩,
            conn := h.conn, inside := h.inside, start := h.start,
            closed := fun c hc j c' hj hs => h.closed c hc j c' hj ((machineU_S_iff (hC c hc) _ _).mpr hs),
            coh := h.coh, guard := h.guard }
  · intro h
    exact { edge := fun e he =>
              let ⟨h1, h2, h3, h4⟩ := h.edge e he
              ⟨(machineU_S_iff (hC _ h2) _ _).mpr h1, h2, h3, h4⟩,
            conn := h.conn, inside := h.inside, start := h.start,
            closed := fun c hc j c' hj hs => h.closed c hc j c' hj ((machineU_S_iff (hC c hc) _ _).mp hs),
            coh := h.coh, guard := h.guard }

/-- **`explorer_iff`** (scope: per edge, crash, `ClassHyp`; not `exploreG`'s loop): on images, every explorer
edge is a U move of its thread into an image, crash commutes with the image, and the class hypothesis for a class
of images is the same for `machineU` and `machine`. -/
theorem explorer_iff (b : Bounds) :
    (∀ (u : UCfg) (i : Nat) (t : Bool) (d : Cfg), UInv U u →
      (i, t, d) ∈ successorsL (elabProg U) k arch b (toCoreCfg u) →
      ∃ u', UInv U u' ∧ d = toCoreCfg u' ∧
        (u' ∈ uThreadSteps U k arch u i ∨ (∃ a v w, u' = uPromise u i a v w) ∨
          ∃ (th : UTTh) (x : String) (n : ExtName) (a : At) (j : Nat) (e : UExpr) (ws rs : List Word),
            u.ths[i]? = some th ∧ layer th.ctr th.term = .letOp x (.ext n a) j e ∧
            u' = uWake (uExtCfg u i th x n e j ws rs) i (relView th.vs) n ws)) ∧
    (∀ (u : UCfg) (i : Nat), crashCfg (toCoreCfg u) i = (uCrashCfg u i).map toCoreCfg ∧
      ∀ u', UInv U u → uCrashCfg u i = some u' → UInv U u') ∧
    (∀ (C : List Cfg) (E : List Edge) (c₀ : Cfg) (i : Nat), (∀ c ∈ C, ImgU U c) →
      (ClassHyp (machineU U k arch) C E c₀ i ↔ ClassHyp (machine (elabProg U) k arch) C E c₀ i)) :=
  ⟨fun _ _ _ _ hu h => successorsL_img hu h, fun u i => ⟨crashCfg_elab u i, fun _ hu h => uCrashCfg_inv hu h⟩,
    fun _ _ _ _ hC => classHyp_iff hC⟩

end Explorer

end UnElab

#print axioms UnElab.liveness_iff_robust
#print axioms UnElab.liveness_iff_tokenFree
#print axioms UnElab.liveness_iff_forced
#print axioms UnElab.liveness_iff_livelock
#print axioms UnElab.liveness_iff_robustX
#print axioms UnElab.liveness_iff_forcedX
#print axioms UnElab.liveness_iff_livelockX
#print axioms UnElab.liveness_iff_robustXC
#print axioms UnElab.liveness_iff_forcedXC
#print axioms UnElab.liveness_iff_livelockXC
#print axioms UnElab.robust_transfer
#print axioms UnElab.tokenFree_transfer
#print axioms UnElab.forced_transfer
#print axioms UnElab.livelock_transfer
#print axioms UnElab.robustX_transfer
#print axioms UnElab.forcedX_transfer
#print axioms UnElab.livelockX_transfer
#print axioms UnElab.robustXC_transfer
#print axioms UnElab.forcedXC_transfer
#print axioms UnElab.livelockXC_transfer
#print axioms UnElab.machineU_S_iff
#print axioms UnElab.machineXU_S_iff
#print axioms UnElab.machineXCU_S_iff
#print axioms UnElab.imgU_closed
#print axioms UnElab.imgU_startW
#print axioms UnElab.successorsL_img
#print axioms UnElab.crashCfg_elab
#print axioms UnElab.classHyp_iff
#print axioms UnElab.explorer_iff
