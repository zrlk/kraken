/-
**Stage 3: the x64 `lock cmpxchg` spinlock
invariant on the semantic machine** (`InvS`), with outstanding promises. The
x64 counterpart of `LiveSpinSemInv.lean` (AArch64 CAS), with the same global
part.

Each thread satisfies the solo-run predicates of `LiveSpinX64SemCmpxSolo`
(`TS`): `SInv`, `PromIn`, every promise above its coherence view (from the
last certification: `Sem.coh_lt_of_certOkN`), and a certification without
fresh writes (`NACertG`; on TSO every certifiable worker has one, and it
replays against larger memories); `Good` follows (`TS.good`). Globally
(`Held`): a non-zero lock has its last write owned by a thread (`Own`) that
still promises it, or holds the lock with the write in its coherence view.

- `inv_instr`, `inv_prom`, `inv_step`: every semantic step keeps `InvS`.
- `inv_init`, `trace_invS`.
-/
import Kraken.Promising.LiveSpinX64SemCmpxSolo

namespace Kraken.Promising.Live.SpinX64SemCmpxInv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinX64SemCmpxSolo
open Kraken.Promising.Live.SpinX64CmpxInv (LkL CtL Static Holder holder_of_pc)
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-! ## The invariant -/

/-- The per-thread part of the invariant. -/
structure TS (fuel : Nat) (i : Nat) (u : Thread isa) (mem : Memory) : Prop where
  sinv : SInv u.st
  promIn : PromIn i u mem
  coh : ∀ ts ∈ u.prom, ∀ w, mem.get? ts = some w → u.views.getCoh w.loc < ts
  nac : NACertG Arch.tso fuel i u mem

theorem TS.good {fuel i : Nat} {u : Thread isa} {mem : Memory} (hlc : LkL ≠ CtL) (h : TS fuel i u mem) :
    Good u mem :=
  good_of_nacert hlc h.nac h.sinv h.promIn

theorem TS.mono {fuel i : Nat} {u : Thread isa} {mem mem' : Memory}
    (hT : TS fuel i u mem) (hb : u.Bnd mem.last) (hp : mem.Prefix mem') : TS fuel i u mem' :=
  ⟨hT.sinv, hT.promIn.mono hp, fun ts hts w hw => hT.coh ts hts w (by rw [← hT.promIn.get hp hts]; exact hw),
    SpinX64SemCmpxSolo.NACert.replay hT.nac hT.sinv hb hp⟩

/-- `TS` after a certified step. -/
theorem ts_of_cert {fuel i : Nat} {u : Thread isa} {mem : Memory}
    (hc : CertOkN Arch.tso i u mem fuel) (hS : SInv u.st) (hP : PromIn i u mem) : TS fuel i u mem :=
  ⟨hS, hP, fun _ hts _ hw => coh_lt_of_certOkN hc hts hw, nacert_of_certOkN hc hS hP.le⟩

/-- Thread `u` owns the lock's last write: it still promises it, or holds the
lock with the write in its coherence view. -/
def Own (mem : Memory) (u : Thread isa) : Prop :=
  mem.lastWrite LkL ∈ u.prom ∨ (Holder u ∧ mem.lastWrite LkL ≤ u.views.getCoh LkL)

/-- A non-zero lock: its last write is a non-zero message owned by its
writer. -/
def Held (cfg : Config isa) : Prop :=
  cfg.mem.finalVal LkL ≠ 0 → ∃ w u, cfg.mem.get? (cfg.mem.lastWrite LkL) = some w ∧ w.loc = LkL ∧
    w.val ≠ 0 ∧ cfg.threads[w.tid]? = some u ∧ Own cfg.mem u

/-- **The `lock cmpxchg` spinlock invariant with promises.** -/
structure InvS (fuel : Nat) (cfg : Config isa) : Prop where
  hlc : LkL ≠ CtL
  bnd : cfg.Bnd
  held : Held cfg
  thr : ∀ (i : Nat) u, cfg.threads[i]? = some u → TS fuel i u cfg.mem

/-! ## Preservation -/

section Pres

variable {fuel : Nat} {cfg : Config isa} {tid : Nat} {t : Thread isa}
  (h : InvS fuel cfg) (ht : cfg.threads[tid]? = some t)
include h ht

/-- `Held` when the lock's last write and value stay. -/
theorem held_same {t' : Thread isa} {mem' : Memory} (hpre : cfg.mem.Prefix mem')
    (hlw : mem'.lastWrite LkL = cfg.mem.lastWrite LkL) (hfv : mem'.finalVal LkL = cfg.mem.finalVal LkL)
    (hown : ∀ w, cfg.mem.get? (cfg.mem.lastWrite LkL) = some w → w.loc = LkL → w.val ≠ 0 → w.tid = tid →
      Own cfg.mem t → Own cfg.mem t') :
    Held (cfg.withThread tid t' mem') := by
  intro hne
  obtain ⟨w, u, hw, hl, hv, hu, ho⟩ := h.held (by rw [← hfv]; exact hne)
  have hw' : mem'.get? (mem'.lastWrite LkL) = some w := by
    rw [hlw, hpre.get? (cfg.mem.last_le_of_get?_eq_some hw)]; exact hw
  have ho' : ∀ {u}, Own cfg.mem u → Own mem' u := fun h' => by unfold Own; rw [hlw]; exact h'
  by_cases e : w.tid = tid
  · rw [e, ht] at hu; cases hu
    exact ⟨w, t', hw', hl, hv, by rw [e]; exact wt_tid ht, ho' (hown w hw hl hv e ho)⟩
  · exact ⟨w, u, hw', hl, hv, by rw [wt_ne ht e]; exact hu, ho' ho⟩

omit h in
/-- `Held` after `tid` appends a lock message. -/
theorem held_append {t' : Thread isa} {v : Val}
    (hown : v ≠ 0 → Own (cfg.mem.append { loc := LkL, val := v, tid }).1 t') :
    Held (cfg.withThread tid t' (cfg.mem.append { loc := LkL, val := v, tid }).1) := by
  intro hne
  have hfv : (cfg.mem.append { loc := LkL, val := v, tid }).1.finalVal LkL = v := by
    rw [finalVal_append, ite_eq_left rfl]
  have hv : v ≠ 0 := by rw [← hfv]; exact hne
  have hlw : (cfg.mem.append { loc := LkL, val := v, tid }).1.lastWrite LkL = cfg.mem.last + 1 := by
    rw [Memory.lastWrite_append, ite_eq_left rfl]
  refine ⟨{ loc := LkL, val := v, tid }, t', ?_, rfl, hv, wt_tid ht, hown hv⟩
  show (cfg.mem.append { loc := LkL, val := v, tid }).1.get?
    ((cfg.mem.append { loc := LkL, val := v, tid }).1.lastWrite LkL) = _
  rw [hlw]; exact Memory.get?_append_last _ _

/-- The invariant after a step of `tid`, from `TS` and `Held`. -/
theorem build {t' : Thread isa} {mem' : Memory} (hpre : cfg.mem.Prefix mem') (hb : (cfg.withThread tid t' mem').Bnd)
    (hT : TS fuel tid t' mem') (hH : Held (cfg.withThread tid t' mem')) :
    InvS fuel (cfg.withThread tid t' mem') := by
  refine ⟨h.hlc, hb, hH, fun i u hu => ?_⟩
  rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
  · exact hT
  · exact (h.thr i u hu).mono (h.bnd i u hu) hpre

/-- **An instruction step keeps the invariant.** -/
theorem inv_instr {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hs : stepOne Arch.tso t tid cfg.mem = some outs) (ho : .ok oc ∈ outs)
    (hc : CertOkN Arch.tso tid oc.thread oc.mem fuel) (hb : (cfg.withThread tid oc.thread oc.mem).Bnd) :
    InvS fuel (cfg.withThread tid oc.thread oc.mem) := by
  have hT0 := h.thr tid t ht
  have r := step_solo h.hlc hT0.sinv hT0.promIn hs ho
  have hpre : cfg.mem.Prefix oc.mem := (stepOne_dord _ hs ho).2.2.1
  have hcoh := (stepOne_dord _ hs ho).2.1 LkL
  refine build h ht hpre hb (ts_of_cert hc r.sinv r.promIn) ?_
  cases r.eff with
  | quiet hm hkeep hh =>
    have hfr : oc.mem.lastWrite LkL = cfg.mem.lastWrite LkL ∧ oc.mem.finalVal LkL = cfg.mem.finalVal LkL := by
      rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
      · exact ⟨rfl, rfl⟩
      · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem { loc := CtL, val := v, tid } (Ne.symm h.hlc)
        exact ⟨a2, a1⟩
    refine held_same h ht hpre hfr.1 hfr.2 fun w hw hl _ _ ho' => ?_
    rcases ho' with a | ⟨a, b⟩
    · exact .inl (hkeep _ a w hw hl)
    · exact .inr ⟨hh a, Nat.le_trans b hcoh⟩
  | acqFresh v hv hm hh hc' =>
    rw [hm]
    refine held_append ht fun _ => .inr ⟨hh, ?_⟩
    rw [Memory.lastWrite_append, ite_eq_left rfl]; exact hc'
  | acqFul ts hts w hw hl hv hm hpr hh hnh hc' =>
    rw [hm] at hpre ⊢
    refine held_same h ht hpre rfl rfl fun w' hw' hl' _ _ ho' => ?_
    rcases ho' with a | ⟨a, -⟩
    · by_cases e : cfg.mem.lastWrite LkL = ts
      · exact .inr ⟨hh, by rw [e]; exact hc'⟩
      · exact .inl (by rw [hpr]; exact (List.mem_erase_of_ne e).mpr a)
    · exact absurd a hnh
  | relFresh hm _ =>
    rw [hm]
    exact held_append ht fun h0 => absurd rfl h0
  | relFul ts hts hw hc' hm hpr hh =>
    rw [hm] at hpre ⊢
    refine held_same h ht hpre rfl rfl fun w' hw' hl' hv' _ ho' => ?_
    rcases ho' with a | ⟨-, b⟩
    · rcases (hT0.good h.hlc).loc _ a w' hw' with ⟨-, -, d⟩ | ⟨d, -⟩ | ⟨-, d, -⟩
      · exact absurd hh d.2
      · exact absurd (hl'.symm.trans d) h.hlc
      · exact absurd d hv'
    · have hle : ts ≤ cfg.mem.lastWrite LkL := Nat.le_of_not_lt fun hlt =>
        Memory.not_write_of_lastWrite_lt _ _ hlt hw rfl
      exact absurd (Nat.lt_of_le_of_lt b (Nat.lt_of_lt_of_le hc' hle)) (Nat.lt_irrefl _)

/-- **A promise step keeps the invariant.** -/
theorem inv_prom {w : Msg} (hwt : w.tid = tid)
    (hc : CertOkN Arch.tso tid (promThread t cfg.mem w) (cfg.mem.append w).1 fuel)
    (hb : (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1).Bnd) :
    InvS fuel (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1) := by
  have hT0 := h.thr tid t ht
  have hpre : cfg.mem.Prefix (cfg.mem.append w).1 := Memory.Prefix.append _ _
  have hmem : ∀ ts, ts ∈ (promThread t cfg.mem w).prom ↔ ts ∈ t.prom ∨ ts = cfg.mem.last + 1 := fun ts => by
    simp only [List.mem_append, List.mem_singleton]; rfl
  have hP' : PromIn tid (promThread t cfg.mem w) (cfg.mem.append w).1 := by
    intro ts hts
    rcases (hmem ts).mp hts with hts | rfl
    · rw [hT0.promIn.get hpre hts]; exact hT0.promIn ts hts
    · exact ⟨w, Memory.get?_append_last _ _, hwt⟩
  refine build h ht hpre hb (ts_of_cert hc hT0.sinv hP') ?_
  have hold : Own cfg.mem t → Own cfg.mem (promThread t cfg.mem w) := fun ho =>
    ho.imp_left fun a => (hmem _).mpr (.inl a)
  by_cases hl : w.loc = LkL
  · obtain ⟨loc, v, tid'⟩ := w
    simp only at hl hwt
    subst hl hwt
    exact held_append ht fun _ => .inl ((hmem _).mpr (.inr (by rw [Memory.lastWrite_append, ite_eq_left rfl])))
  · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem w hl
    exact held_same h ht hpre a2 a1 fun _ _ _ _ _ => hold

/-- **A semantic step keeps the invariant.** -/
theorem inv_step {cfg' : Config isa} (hst : StepSem Arch.tso fuel tid cfg cfg') : InvS fuel cfg' := by
  have hb := h.bnd.semStep hst
  rcases hst with ⟨t1, outs, oc, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, hwt, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    exact inv_instr h ht hs ho hc hb
  · rw [ht] at ht1; cases ht1
    exact inv_prom h ht hwt hc hb

end Pres

/-! ## Initially and along traces -/

theorem inv_init {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) : InvS fuel (Config.init states initMem) := by
  have h0 := SpinX64CmpxInv.inv_init hs
  refine ⟨h0.hlc, h0.bnd, fun hne => absurd ?_ hne, fun i t h => ?_⟩
  · have := hs.hL0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · have hT := h0.thr i t h
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hm, rfl⟩ := h
    have hs := hs.hst s (List.mem_of_getElem? hm)
    exact ⟨⟨hT.st, 1, by decide, by show s.st.2 = _; rw [hs.pc, hs.exe]; exact label_worker,
      pci_triv (by decide) (by decide)⟩, fun ts h => by simp [Thread.init] at h,
      fun ts h => by simp [Thread.init] at h, ⟨_, .refl _ _, rfl⟩⟩

/-- **The invariant along a semantic trace from a start configuration.** -/
theorem trace_invS {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) (tr : TraceSem Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, InvS fuel (tr.cfg i)
  | 0 => h0 ▸ inv_init hs
  | i + 1 => by
    have h := trace_invS hs tr h0 i
    rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
    · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact inv_step h ht hst
    · rw [he]; exact h

end Kraken.Promising.Live.SpinX64SemCmpxInv
