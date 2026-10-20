/-
**Stage 3: the x64 `xchg`-spinlock invariant
on the semantic machine** (`InvS`), with outstanding promises, under
`Arch.tso`: the port of `LiveSpinSemSwpInv` to the verbatim
image `SpinAbs.spinImageV`.

Each thread satisfies the solo-run predicates of `LiveSpinX64SemXchgSolo`
(`TS`): `SInv`, `PromIn`, `Good`, `CohLt` (from the last certification), a
certification without fresh writes (`NACertG`; on TSO every certifiable
worker has one), and: its own writes of `0` to the lock are promises or
behind it (`own0`). Globally (`Held`): above the last zero `z` of the lock
(`TopZ`), the first lock message `m` (`Gap`) is a promise of its writer,
pinned to `z` (`ZNot`), or its writer holds the lock with `m` in its
coherence view. A failing `xchgl` writes too, so the promise-free invariant
(`SpinX64XchgInv.InvX`) does not carry over; but the first write after a zero
reads that zero, by atomicity.

- `held_of`: `Held` after a step, from the stepping thread's part;
- `inv_instr`, `inv_prom`, `inv_step`: every semantic step keeps `InvS`;
- `inv_init`, `trace_invS`.
-/
import Kraken.Promising.LiveSpinX64SemXchgSolo

namespace Kraken.Promising.Live.SpinX64SemXchgInv

set_option linter.unusedSectionVars false

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinX64SemXchgSolo
open Kraken.Promising.Live.SpinX64XchgInv (Static Holder LkL CtL)
open Kraken.Promising.Live.SpinSemSwpSolo (ZeroAt ZNot Gap TopZ)
open Kraken.Promising.Live.SpinStep (wt_get wt_tid wt_ne loc_ne)
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV)

/-! ## Appends (`SpinSemSwpInv.get_new`/`get_none`, ISA-neutral in `LiveSemShape`) -/

section MemFacts

variable {mem : Memory}

theorem get_new {w w' : Msg} {m : Time} (h : (mem.append w).1.get? m = some w') (hm : ¬ m ≤ mem.last) :
    m = mem.last + 1 ∧ w' = w := SpinSemSwpInv.get_new h hm

theorem get_none {w : Msg} {m : Time} (h : mem.get? m = some w) (hm : ¬ m ≤ mem.last) : False :=
  SpinSemSwpInv.get_none h hm

end MemFacts

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-! ## The invariant -/

/-- The per-thread part of the invariant. -/
structure TS (fuel : Nat) (i : Nat) (u : Thread isa) (mem : Memory) : Prop where
  sinv : SInv u.st
  promIn : PromIn i u mem
  good : Good u mem
  coh : CohLt u mem
  nac : NACertG Arch.tso fuel i u mem
  /-- The thread's own writes of `0` to the lock are promises, or it is past
  its release. -/
  own0 : ∀ m w, mem.get? m = some w → w.tid = i → w.loc = LkL → w.val = 0 → m ∈ u.prom ∨ Past u

theorem TS.mono {fuel : Nat} {i : Nat} {u : Thread isa} {mem mem' : Memory}
    (hT : TS fuel i u mem) (hb : u.Bnd mem.last) (hp : mem.Prefix mem')
    (hnew : ∀ m w, mem'.get? m = some w → mem.last < m → w.tid ≠ i) : TS fuel i u mem' :=
  ⟨hT.sinv, hT.promIn.mono hp, hT.good.mono hp hT.promIn,
    fun ts hts w hw => hT.coh ts hts w (by rw [← hT.promIn.get hp hts]; exact hw),
    nacert_replay hT.nac hT.sinv hb hp,
    fun m w hw ht hl hv => by
      by_cases hm : m ≤ mem.last
      · rw [hp.get? hm] at hw; exact hT.own0 m w hw ht hl hv
      · exact absurd ht (hnew m w hw (by omega_t))⟩

/-- `TS` after a certified step. -/
theorem ts_of_cert {fuel : Nat} {i : Nat} {u : Thread isa} {mem : Memory} (hlc : LkL ≠ CtL)
    (hc : CertOkN Arch.tso i u mem fuel) (hS : SInv u.st) (hP : PromIn i u mem)
    (hO : ∀ m w, mem.get? m = some w → w.tid = i → w.loc = LkL → w.val = 0 → m ∈ u.prom ∨ Past u) :
    TS fuel i u mem :=
  ⟨hS, hP, good_of_certOkN hlc hc hS hP, fun _ hts _ hw => coh_lt_of_certOkN hc hts hw,
    nacert_of_certOkN hc hS hP.le, hO⟩

/-- **Above the last zero of the lock, the first lock message** is a promise
of its writer, which did not write the zero, or its writer holds the lock
with the message in its coherence view. -/
def Held (cfg : Config isa) : Prop :=
  ∀ z m w, ZeroAt LkL cfg.mem z → TopZ LkL cfg.mem z → z < m → Gap LkL cfg.mem z m →
    cfg.mem.get? m = some w → w.loc = LkL → ∃ u, cfg.threads[w.tid]? = some u ∧
      ((m ∈ u.prom ∧ ZNot cfg.mem z w.tid) ∨ (Holder u ∧ m ≤ u.views.getCoh LkL))

/-- **The `xchg`-spinlock invariant with promises.** -/
structure InvS (fuel : Nat) (cfg : Config isa) : Prop where
  hlc : LkL ≠ CtL
  bnd : cfg.Bnd
  init0 : cfg.mem.initVal LkL = 0
  held : Held cfg
  thr : ∀ (i : Nat) u, cfg.threads[i]? = some u → TS fuel i u cfg.mem

/-! ## Preservation -/

section Pres

variable {fuel : Nat} {cfg : Config isa} {tid : Nat} {t : Thread isa}
  (h : InvS fuel cfg) (ht : cfg.threads[tid]? = some t)
include h ht

/-- **`Held` after a step of `tid`** appending at most one message, from what
happens to `tid`'s old first-above-zero messages (`hold`) and to the new
message (`hnew`). -/
theorem held_of {t' : Thread isa} {mem' : Memory} (hpre : cfg.mem.Prefix mem')
    (hlast : mem'.last ≤ cfg.mem.last + 1) (hnt : ∀ w, mem'.get? (cfg.mem.last + 1) = some w → w.tid = tid)
    (hold : ∀ z m, z < m → m ≤ cfg.mem.last → ZeroAt LkL cfg.mem z → Gap LkL cfg.mem z m →
      TopZ LkL mem' z → (∃ w, cfg.mem.get? m = some w ∧ w.loc = LkL) →
      (m ∈ t.prom ∧ ZNot cfg.mem z tid) ∨ (Holder t ∧ m ≤ t.views.getCoh LkL) →
      (m ∈ t'.prom ∧ ZNot cfg.mem z tid) ∨ (Holder t' ∧ m ≤ t'.views.getCoh LkL))
    (hnew : ∀ z w, mem'.get? (cfg.mem.last + 1) = some w → w.loc = LkL → ZeroAt LkL mem' z →
      TopZ LkL mem' z → z < cfg.mem.last + 1 → Gap LkL mem' z (cfg.mem.last + 1) →
      (cfg.mem.last + 1 ∈ t'.prom ∧ ZNot mem' z tid) ∨
        (Holder t' ∧ cfg.mem.last + 1 ≤ t'.views.getCoh LkL)) :
    Held (cfg.withThread tid t' mem') := by
  intro z m w hz htop hzm hgap hw hl
  rcases Nat.lt_or_ge cfg.mem.last m with hgt | hle
  · have hmle : m ≤ mem'.last := mem'.last_le_of_get?_eq_some hw
    obtain rfl : m = cfg.mem.last + 1 := by omega_t
    have e := hnt w hw
    refine ⟨t', by rw [e]; exact wt_tid ht, ?_⟩
    rw [e]; exact hnew z w hw hl hz htop hzm hgap
  · have hw0 : cfg.mem.get? m = some w := by rw [← hpre.get? hle]; exact hw
    obtain ⟨u, hu, hd⟩ := h.held z m w (zeroAt_back hpre (by omega_t) hz) (topZ_back hpre htop) hzm
      (gap_back hpre hgap) hw0 hl
    by_cases e : w.tid = tid
    · rw [e, ht] at hu; cases hu
      rw [e] at hd ⊢
      refine ⟨t', wt_tid ht, ?_⟩
      rcases hold z m hzm hle (zeroAt_back hpre (by omega_t) hz) (gap_back hpre hgap) htop ⟨w, hw0, hl⟩ hd with
        ⟨a, b⟩ | b
      · exact .inl ⟨a, b.mono hpre⟩
      · exact .inr b
    · refine ⟨u, by rw [wt_ne ht e]; exact hu, ?_⟩
      rcases hd with ⟨a, b⟩ | b
      · exact .inl ⟨a, b.mono hpre⟩
      · exact .inr b

/-- The invariant after a step of `tid`, from `TS` and `Held`. -/
theorem build {t' : Thread isa} {mem' : Memory} (hpre : cfg.mem.Prefix mem') (hb : (cfg.withThread tid t' mem').Bnd)
    (hnew : ∀ m w, mem'.get? m = some w → cfg.mem.last < m → w.tid = tid)
    (hT : TS fuel tid t' mem') (hH : Held (cfg.withThread tid t' mem')) :
    InvS fuel (cfg.withThread tid t' mem') := by
  refine ⟨h.hlc, hb, by show mem'.initVal _ = 0; rw [hpre.initVal]; exact h.init0, hH, fun i u hu => ?_⟩
  rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨hne, hu⟩
  · exact hT
  · exact (h.thr i u hu).mono (h.bnd i u hu) hpre fun m w hw hm e => hne (e.symm.trans (hnew m w hw hm))

/-- **An instruction step keeps the invariant.** -/
theorem inv_instr {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hs : stepOne Arch.tso t tid cfg.mem = some outs) (ho : .ok oc ∈ outs)
    (hc : CertOkN Arch.tso tid oc.thread oc.mem fuel) (hb : (cfg.withThread tid oc.thread oc.mem).Bnd) :
    InvS fuel (cfg.withThread tid oc.thread oc.mem) := by
  have hT0 := h.thr tid t ht
  have r := step_solo h.hlc hT0.sinv hT0.promIn hs ho
  have hpre : cfg.mem.Prefix oc.mem := (stepOne_dord _ hs ho).2.2.1
  have hcoh := (stepOne_dord _ hs ho).2.1 LkL
  have hshape : oc.mem = cfg.mem ∨ ∃ w : Msg, w.tid = tid ∧ oc.mem = (cfg.mem.append w).1 := by
    cases r.eff with
    | quiet hm =>
      rcases hm with hm | ⟨v, hm⟩
      · exact .inl hm
      · exact .inr ⟨_, rfl, hm⟩
    | swpFresh hm => exact .inr ⟨_, rfl, hm⟩
    | swpFul _ _ _ hm => exact .inl hm
    | relFresh hm => exact .inr ⟨_, rfl, hm⟩
    | relFul _ _ _ _ hm => exact .inl hm
  have hlast : oc.mem.last ≤ cfg.mem.last + 1 := by
    rcases hshape with hm | ⟨w, -, hm⟩ <;> rw [hm]
    · exact Nat.le_succ _
    · exact (Nat.le_of_eq (Memory.last_append _ _))
  have hnew : ∀ m w, oc.mem.get? m = some w → cfg.mem.last < m → w.tid = tid := by
    intro m w hw hm
    rcases hshape with e | ⟨w', hw', e⟩ <;> rw [e] at hw
    · exact (get_none hw (by omega_t)).elim
    · obtain ⟨-, rfl⟩ := get_new hw (by omega_t); exact hw'
  have hO : ∀ m w, oc.mem.get? m = some w → w.tid = tid → w.loc = LkL → w.val = 0 →
      m ∈ oc.thread.prom ∨ Past oc.thread := by
    intro m w hw hwt hl hv
    by_cases hm : m ≤ cfg.mem.last
    · have hw0 : cfg.mem.get? m = some w := by rw [← hpre.get? hm]; exact hw
      rcases hT0.own0 m w hw0 hwt hl hv with a | a
      · cases r.eff with
        | quiet _ hkeep _ => exact .inl (hkeep m a w hw0 hl)
        | swpFresh _ hpr => exact .inl (by rw [hpr]; exact a)
        | swpFul ts _ hw' _ hpr =>
          have hne : m ≠ ts := fun e => by subst e; rw [hw0] at hw'; cases hw'; exact v1_ne hv
          exact .inl (by rw [hpr]; exact (List.mem_erase_of_ne hne).mpr a)
        | relFresh _ _ hpast => exact .inr hpast
        | relFul _ _ _ _ _ _ _ hpast => exact .inr hpast
      · exact .inr (r.past a)
    · cases r.eff with
      | quiet hm' =>
        rcases hm' with hm' | ⟨v, hm'⟩ <;> rw [hm'] at hw
        · exact (get_none hw hm).elim
        · obtain ⟨-, rfl⟩ := get_new hw hm; exact (h.hlc hl.symm).elim
      | swpFresh hm' =>
        rw [hm'] at hw; obtain ⟨-, rfl⟩ := get_new hw hm; exact (v1_ne hv).elim
      | swpFul _ _ _ hm' => rw [hm'] at hw; exact (get_none hw hm).elim
      | relFresh _ _ hpast => exact .inr hpast
      | relFul _ _ _ _ _ _ _ hpast => exact .inr hpast
  have hT' := ts_of_cert h.hlc hc r.sinv r.promIn hO
  have hnt : ∀ w, oc.mem.get? (cfg.mem.last + 1) = some w → w.tid = tid := fun w hw =>
    hnew _ w hw (Nat.lt_succ_self _)
  refine build h ht hpre hb hnew hT' (held_of h ht hpre hlast hnt ?_ ?_)
  · cases r.eff with
    | quiet hm hkeep hh =>
      exact fun z m _ _ _ _ _ ⟨w, hw, hl⟩ d =>
        d.imp (fun ⟨a, b⟩ => ⟨hkeep m a w hw hl, b⟩) (fun ⟨a, b⟩ => ⟨hh a, Nat.le_trans b hcoh⟩)
    | swpFresh hm hpr hpre' =>
      exact fun z m _ _ _ _ _ _ d =>
        d.imp (fun ⟨a, b⟩ => ⟨by rw [hpr]; exact a, b⟩) (fun ⟨a, _⟩ => absurd a hpre'.2)
    | swpFul ts hts hw hm hpr hpre' hco hz =>
      intro z m hzm _ hzc hgc _ _ d
      rcases d with ⟨a, b⟩ | ⟨a, -⟩
      · by_cases e : m = ts
        · subst e; exact .inr ⟨hz z hzc b hzm hgc, hco⟩
        · exact .inl ⟨by rw [hpr]; exact (List.mem_erase_of_ne e).mpr a, b⟩
      · exact absurd a hpre'.2
    | relFresh hm =>
      intro z m hzm hle _ _ htop _ _
      exact absurd rfl (htop (cfg.mem.last + 1) _ (by omega_t) (by rw [hm]; exact Memory.get?_append_last _ _) rfl)
    | relFul ts hts hw hc' hm hpr =>
      intro z m hzm _ _ _ htop _ d
      have hle : ts ≤ z := Nat.le_of_not_lt fun hlt => absurd rfl (htop ts _ hlt (by rw [hm]; exact hw) rfl)
      rcases d with ⟨a, b⟩ | ⟨-, b⟩
      · exact .inl ⟨by rw [hpr]; exact (List.mem_erase_of_ne (by omega_t)).mpr a, b⟩
      · exact absurd hc' (by omega_t)
  · cases r.eff with
    | quiet hm =>
      intro z w hw hl
      exfalso
      rcases hm with hm | ⟨v, hm⟩ <;> rw [hm] at hw
      · exact get_none hw (by omega_t)
      · rw [Memory.get?_append_last] at hw; cases hw; exact h.hlc hl.symm
    | swpFresh hm hpr hpre' hco hz =>
      intro z w hw hl hz' _ hzl hgap
      have hz0 := zeroAt_back hpre (by omega_t) hz'
      have hzn : ZNot cfg.mem z tid := by
        rcases hz0 with ⟨rfl, -⟩ | ⟨wz, hwz, hlz, hvz⟩
        · exact .inl rfl
        · by_cases e : wz.tid = tid
          · exfalso
            rcases hT0.own0 z wz hwz e hlz hvz with a | a
            · have := hT'.coh z (by rw [hpr]; exact a) wz (by rw [hpre.get? (by omega_t)]; exact hwz)
              rw [hlz] at this; omega_t
            · exact not_past_of_preAcq hpre' a
          · exact .inr ⟨wz, hwz, e⟩
      exact .inr ⟨hz z hz0 hzn hzl (gap_back hpre hgap), hco⟩
    | swpFul _ _ _ hm =>
      intro z w' hw'
      rw [hm] at hw'; exact (get_none hw' (by omega_t)).elim
    | relFresh hm =>
      intro z w hw hl _ htop hzl _
      have hw' := hw
      rw [hm, Memory.get?_append_last] at hw'; cases hw'
      exact absurd rfl (htop _ _ hzl hw hl)
    | relFul _ _ _ _ hm =>
      intro z w' hw'
      rw [hm] at hw'; exact (get_none hw' (by omega_t)).elim

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
  have hnew : ∀ m w', (cfg.mem.append w).1.get? m = some w' → cfg.mem.last < m → w'.tid = tid := by
    intro m w' hw' hm
    obtain ⟨-, rfl⟩ := get_new hw' (by omega_t); exact hwt
  have hO : ∀ m w', (cfg.mem.append w).1.get? m = some w' → w'.tid = tid → w'.loc = LkL → w'.val = 0 →
      m ∈ (promThread t cfg.mem w).prom ∨ Past (promThread t cfg.mem w) := by
    intro m w' hw' hwt' hl hv
    by_cases hm : m ≤ cfg.mem.last
    · rw [hpre.get? hm] at hw'
      exact (hT0.own0 m w' hw' hwt' hl hv).imp (fun a => (hmem _).mpr (.inl a)) id
    · obtain ⟨rfl, -⟩ := get_new hw' hm; exact .inl ((hmem _).mpr (.inr rfl))
  have hT' := ts_of_cert h.hlc hc hT0.sinv hP' hO
  have hnp : cfg.mem.last + 1 ∈ (promThread t cfg.mem w).prom := (hmem _).mpr (.inr rfl)
  refine build h ht hpre hb hnew hT' (held_of h ht hpre (Nat.le_of_eq (Memory.last_append _ _))
    (fun w' hw' => hnew _ w' hw' (Nat.lt_succ_self _))
    (fun _ _ _ _ _ _ _ _ d => d.imp (fun ⟨a, b⟩ => ⟨(hmem _).mpr (.inl a), b⟩) id) ?_)
  intro z w' hw' hl hz' htop hzl _
  have hw0 := hw'
  rw [Memory.get?_append_last] at hw0; cases hw0
  by_cases hv0 : w.val = 0
  · exact absurd hv0 (htop _ w hzl hw' hl)
  refine .inl ⟨hnp, ZNot.mono hpre ?_⟩
  rcases zeroAt_back hpre (by omega_t) hz' with ⟨rfl, -⟩ | ⟨wz, hwz, hlz, hvz⟩
  · exact .inl rfl
  by_cases e : wz.tid = tid
  · exfalso
    have hwz' : (cfg.mem.append w).1.get? z = some wz := by rw [hpre.get? (by omega_t)]; exact hwz
    have hpa := hT'.good.acq _ hnp w hw' hl hv0
    have hz5 : z ∈ t.prom := (hT0.own0 z wz hwz e hlz hvz).resolve_right fun h' => not_past_of_preAcq hpa h'
    have := hT'.good.rel z ((hmem _).mpr (.inl hz5)) wz hwz' hlz hvz _ hnp w hw' hl hv0
    omega_t
  · exact .inr ⟨wz, hwz, e⟩

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
    (hs : SpinX64Xchg.XchgStart states initMem) : InvS fuel (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  refine ⟨loc_ne hs.hlc, Config.init_bnd _ _, hs.hL0, fun z m w _ _ _ _ hw => ?_, fun i t h => ?_⟩
  · simp [Config.init, Memory.get?] at hw
  · have hT := (SpinX64XchgInv.inv_init hs).thr i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    have hpc : s.st.2 = pcA 1 := by rw [hs.pc, hs.exe]; exact label_worker
    refine ⟨⟨hT.st, ⟨1, by decide, hpc⟩, fun e => absurd (addrOf_inj (by decide) (by decide) (hpc.symm.trans e))
      (by decide)⟩, fun ts h => by simp [Thread.init] at h, good_nil rfl, fun ts h => by simp [Thread.init] at h,
      ⟨_, .refl _ _, rfl⟩, ?_⟩
    intro m w hw
    simp [Config.init, Memory.get?] at hw

/-- **The invariant along a semantic trace from a start configuration.** -/
theorem trace_invS {fuel : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64Xchg.XchgStart states initMem) (tr : TraceSem Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, InvS fuel (tr.cfg i)
  | 0 => h0 ▸ inv_init hs
  | i + 1 => by
    have h := trace_invS hs tr h0 i
    rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
    · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact inv_step h ht hst
    · rw [he]; exact h

end Kraken.Promising.Live.SpinX64SemXchgInv
