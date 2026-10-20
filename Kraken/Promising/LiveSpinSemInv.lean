/-
**Stage 3: the CAS-spinlock invariant on the
semantic machine** (`InvS`), with outstanding promises.

Each thread satisfies the solo-run predicates of `LiveSpinSemSolo` (`TS`):
`SInv`, `PromIn`, `Good`, every promise above its coherence view (from the
last certification: `Sem.coh_lt_of_certOkN`), and `NACert` when it is not
pre-acquire or holds an acquire promise. Globally (`Held`): a non-zero lock
has its last write owned by a thread (`Own`) that still promises it, or holds
the lock with the write in its coherence view. The second disjunct survives a
release *fulfilment* (above the coherence view, so not below the last write);
an appended release makes the lock `0`.

- `inv_instr`, `inv_prom`, `inv_step`: every semantic step keeps `InvS`.
- `inv_init`, `trace_invS`.
-/
import Kraken.Promising.LiveSpinSemSolo

namespace Kraken.Promising.Live.SpinSemInv

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinSemSolo
open Kraken.Promising.Live.SpinCasInv (Static Holder holder_of_pc)
open Kraken.Promising.Live.TicketInv (L4 loc_ne)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-! ## The invariant -/

/-- The per-thread part of the invariant. -/
structure TS (fuel : Nat) (l c : BitVec 64) (i : Nat) (u : Thread isa) (mem : Memory) : Prop where
  sinv : SInv l c u.st
  promIn : PromIn i u mem
  good : Good l c u mem
  coh : ∀ ts ∈ u.prom, ∀ w, mem.get? ts = some w → u.views.getCoh w.loc < ts
  nac : NA l u mem → NACert fuel i u mem

theorem TS.mono {fuel : Nat} {l c : BitVec 64} {i : Nat} {u : Thread isa} {mem mem' : Memory}
    (hT : TS fuel l c i u mem) (hb : u.Bnd mem.last) (hp : mem.Prefix mem') : TS fuel l c i u mem' :=
  ⟨hT.sinv, hT.promIn.mono hp, hT.good.mono hp hT.promIn,
    fun ts hts w hw => hT.coh ts hts w (by rw [← hT.promIn.get hp hts]; exact hw), fun hn =>
    (hT.nac (hn.imp_right fun ⟨ts, hts, w, hw, hl⟩ => ⟨ts, hts, w, by rw [← hT.promIn.get hp hts]; exact hw, hl⟩)).replay
      hT.sinv hb hp⟩

/-- `TS` after a certified step. -/
theorem ts_of_cert {fuel : Nat} {l c : BitVec 64} {i : Nat} {u : Thread isa} {mem : Memory} (hlc : L4 l ≠ L4 c)
    (hc : CertOkN Arch.armv8 i u mem fuel) (hS : SInv l c u.st) (hP : PromIn i u mem) : TS fuel l c i u mem :=
  ⟨hS, hP, good_of_certOkN hlc hc hS hP, fun _ hts _ hw => coh_lt_of_certOkN hc hts hw,
    nacert_of_certOkN hlc hc hS hP⟩

/-- Thread `u` owns the lock's last write: it still promises it, or holds the
lock with the write in its coherence view. -/
def Own (l : BitVec 64) (mem : Memory) (u : Thread isa) : Prop :=
  mem.lastWrite (L4 l) ∈ u.prom ∨ (Holder u ∧ mem.lastWrite (L4 l) ≤ u.views.getCoh (L4 l))

/-- A non-zero lock: its last write is a non-zero message owned by its
writer. -/
def Held (l : BitVec 64) (cfg : Config isa) : Prop :=
  cfg.mem.finalVal (L4 l) ≠ 0 → ∃ w u, cfg.mem.get? (cfg.mem.lastWrite (L4 l)) = some w ∧ w.loc = L4 l ∧
    w.val ≠ 0 ∧ cfg.threads[w.tid]? = some u ∧ Own l cfg.mem u

/-- **The CAS-spinlock invariant with promises.** -/
structure InvS (fuel : Nat) (l c : BitVec 64) (cfg : Config isa) : Prop where
  hlc : L4 l ≠ L4 c
  bnd : cfg.Bnd
  held : Held l cfg
  thr : ∀ (i : Nat) u, cfg.threads[i]? = some u → TS fuel l c i u cfg.mem

/-! ## Preservation -/

section Pres

variable {fuel : Nat} {l c : BitVec 64} {cfg : Config isa} {tid : Nat} {t : Thread isa}
  (h : InvS fuel l c cfg) (ht : cfg.threads[tid]? = some t)
include h ht

/-- `Held` when the lock's last write and value stay. -/
theorem held_same {t' : Thread isa} {mem' : Memory} (hpre : cfg.mem.Prefix mem')
    (hlw : mem'.lastWrite (L4 l) = cfg.mem.lastWrite (L4 l)) (hfv : mem'.finalVal (L4 l) = cfg.mem.finalVal (L4 l))
    (hown : ∀ w, cfg.mem.get? (cfg.mem.lastWrite (L4 l)) = some w → w.loc = L4 l → w.val ≠ 0 → w.tid = tid →
      Own l cfg.mem t → Own l cfg.mem t') :
    Held l (cfg.withThread tid t' mem') := by
  intro hne
  obtain ⟨w, u, hw, hl, hv, hu, ho⟩ := h.held (by rw [← hfv]; exact hne)
  have hw' : mem'.get? (mem'.lastWrite (L4 l)) = some w := by
    rw [hlw, hpre.get? (cfg.mem.last_le_of_get?_eq_some hw)]; exact hw
  have ho' : ∀ {u}, Own l cfg.mem u → Own l mem' u := fun h' => by unfold Own; rw [hlw]; exact h'
  by_cases e : w.tid = tid
  · rw [e, ht] at hu; cases hu
    exact ⟨w, t', hw', hl, hv, by rw [e]; exact wt_tid ht, ho' (hown w hw hl hv e ho)⟩
  · exact ⟨w, u, hw', hl, hv, by rw [wt_ne ht e]; exact hu, ho' ho⟩

omit h in
/-- `Held` after `tid` appends a lock message. -/
theorem held_append {t' : Thread isa} {v : Val}
    (hown : v ≠ 0 → Own l (cfg.mem.append { loc := L4 l, val := v, tid }).1 t') :
    Held l (cfg.withThread tid t' (cfg.mem.append { loc := L4 l, val := v, tid }).1) := by
  intro hne
  have hfv : (cfg.mem.append { loc := L4 l, val := v, tid }).1.finalVal (L4 l) = v := by
    rw [finalVal_append, ite_eq_left rfl]
  have hv : v ≠ 0 := by rw [← hfv]; exact hne
  have hlw : (cfg.mem.append { loc := L4 l, val := v, tid }).1.lastWrite (L4 l) = cfg.mem.last + 1 := by
    rw [Memory.lastWrite_append, ite_eq_left rfl]
  refine ⟨{ loc := L4 l, val := v, tid }, t', ?_, rfl, hv, wt_tid ht, hown hv⟩
  show (cfg.mem.append { loc := L4 l, val := v, tid }).1.get?
    ((cfg.mem.append { loc := L4 l, val := v, tid }).1.lastWrite (L4 l)) = _
  rw [hlw]; exact Memory.get?_append_last _ _

/-- The invariant after a step of `tid`, from `TS` and `Held`. -/
theorem build {t' : Thread isa} {mem' : Memory} (hpre : cfg.mem.Prefix mem') (hb : (cfg.withThread tid t' mem').Bnd)
    (hT : TS fuel l c tid t' mem') (hH : Held l (cfg.withThread tid t' mem')) :
    InvS fuel l c (cfg.withThread tid t' mem') := by
  refine ⟨h.hlc, hb, hH, fun i u hu => ?_⟩
  rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
  · exact hT
  · exact (h.thr i u hu).mono (h.bnd i u hu) hpre

/-- **An instruction step keeps the invariant.** -/
theorem inv_instr {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hs : stepOne Arch.armv8 t tid cfg.mem = some outs) (ho : .ok oc ∈ outs)
    (hc : CertOkN Arch.armv8 tid oc.thread oc.mem fuel) (hb : (cfg.withThread tid oc.thread oc.mem).Bnd) :
    InvS fuel l c (cfg.withThread tid oc.thread oc.mem) := by
  have hT0 := h.thr tid t ht
  have r := step_solo h.hlc hT0.sinv hT0.promIn hs ho
  have hpre : cfg.mem.Prefix oc.mem := (stepOne_dord _ hs ho).2.2.1
  have hcoh := (stepOne_dord _ hs ho).2.1 (L4 l)
  refine build h ht hpre hb (ts_of_cert h.hlc hc r.sinv r.promIn) ?_
  cases r.eff with
  | quiet hm hkeep hh =>
    have hfr : oc.mem.lastWrite (L4 l) = cfg.mem.lastWrite (L4 l) ∧
        oc.mem.finalVal (L4 l) = cfg.mem.finalVal (L4 l) := by
      rcases hm with hm | ⟨v, hm⟩ <;> rw [hm]
      · exact ⟨rfl, rfl⟩
      · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem { loc := L4 c, val := v, tid } (Ne.symm h.hlc)
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
    · by_cases e : cfg.mem.lastWrite (L4 l) = ts
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
    · rcases hT0.good.loc _ a w' hw' with ⟨-, -, d⟩ | ⟨d, -⟩ | ⟨-, d, -⟩
      · exact absurd hh d.2
      · exact absurd (hl'.symm.trans d) h.hlc
      · exact absurd d hv'
    · have hle : ts ≤ cfg.mem.lastWrite (L4 l) := Nat.le_of_not_lt fun hlt =>
        Memory.not_write_of_lastWrite_lt _ _ hlt hw rfl
      exact absurd (Nat.lt_of_le_of_lt b (Nat.lt_of_lt_of_le hc' hle)) (Nat.lt_irrefl _)

/-- **A promise step keeps the invariant.** -/
theorem inv_prom {w : Msg} (hwt : w.tid = tid)
    (hc : CertOkN Arch.armv8 tid (promThread t cfg.mem w) (cfg.mem.append w).1 fuel)
    (hb : (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1).Bnd) :
    InvS fuel l c (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1) := by
  have hT0 := h.thr tid t ht
  have hpre : cfg.mem.Prefix (cfg.mem.append w).1 := Memory.Prefix.append _ _
  have hmem : ∀ ts, ts ∈ (promThread t cfg.mem w).prom ↔ ts ∈ t.prom ∨ ts = cfg.mem.last + 1 := fun ts => by
    simp only [List.mem_append, List.mem_singleton]; rfl
  have hP' : PromIn tid (promThread t cfg.mem w) (cfg.mem.append w).1 := by
    intro ts hts
    rcases (hmem ts).mp hts with hts | rfl
    · rw [hT0.promIn.get hpre hts]; exact hT0.promIn ts hts
    · exact ⟨w, Memory.get?_append_last _ _, hwt⟩
  refine build h ht hpre hb (ts_of_cert h.hlc hc hT0.sinv hP') ?_
  have hold : Own l cfg.mem t → Own l cfg.mem (promThread t cfg.mem w) := fun ho =>
    ho.imp_left fun a => (hmem _).mpr (.inl a)
  by_cases hl : w.loc = L4 l
  · obtain ⟨loc, v, tid'⟩ := w
    simp only at hl hwt
    subst hl hwt
    exact held_append ht fun _ => .inl ((hmem _).mpr (.inr (by rw [Memory.lastWrite_append, ite_eq_left rfl])))
  · obtain ⟨a1, a2, -⟩ := mem_frame cfg.mem w hl
    exact held_same h ht hpre a2 a1 fun _ _ _ _ _ => hold

/-- **A semantic step keeps the invariant.** -/
theorem inv_step {cfg' : Config isa} (hst : StepSem Arch.armv8 fuel tid cfg cfg') : InvS fuel l c cfg' := by
  have hb := h.bnd.semStep hst
  rcases hst with ⟨t1, outs, oc, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, hwt, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    exact inv_instr h ht hs ho hc hb
  · rw [ht] at ht1; cases ht1
    exact inv_prom h ht hwt hc hb

end Pres

/-! ## Initially and along traces -/

theorem inv_init {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) : InvS fuel l c (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  refine ⟨loc_ne hs.hlc, Config.init_bnd _ _, fun hne => absurd ?_ hne, fun i t h => ?_⟩
  · have := hs.hL0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  · obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    refine ⟨⟨⟨hs.exe, hs.decls, hs.endPc, hs.x0, hs.x1, hs.dl, hs.dc⟩, 1, by decide, hs.pc.trans addrOf_0,
      fun h => absurd rfl h, fun h => absurd h (by decide)⟩, fun ts h => by simp [Thread.init] at h,
      good_nil rfl, fun ts h => by simp [Thread.init] at h, fun _ => ⟨_, .refl _ _, rfl⟩⟩

/-- **The invariant along a semantic trace from a start configuration.** -/
theorem trace_invS {fuel : Nat} {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, InvS fuel l c (tr.cfg i)
  | 0 => h0 ▸ inv_init hs
  | i + 1 => by
    have h := trace_invS hs tr h0 i
    rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
    · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact inv_step h ht hst
    · rw [he]; exact h

end Kraken.Promising.Live.SpinSemInv
