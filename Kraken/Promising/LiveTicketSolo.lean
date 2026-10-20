/-
**Stage 3: solo runs of the ticket-lock worker
with outstanding promises.**

A worker's run alone (`ThreadNPn`) can only fulfil a promise at the position
that writes its location: `next` (`x`) at the `LDADDA` (position 2), the
counter (`c`) at the `STR` (9), `owner` (`o`) at the `STLR` (11); positions
are visited in order (`rk`), except for the spin loop. So a certifiable
worker (`Good`, from any certification: `good_of_run`):

- has promises only to `x` before its `LDADDA`, to `c` up to its `STR`, to `o`
  up to its `STLR`, at most one per location, each above its `coh` of the
  location;
- has its `owner` promise above its `vwOld` (a release write's pre-view
  takes `vwOld`, and any fresh write raises `vwOld` past every promise);
- has, for a `next` promise, the value one above an atomically preceding
  read of `next`; for an `owner` promise, the value one above its ticket (or,
  before its `LDADDA`, the value of its `next` promise), and a readable
  `owner` message whose value is the ticket.

`RInv` collects the register facts the worker establishes for itself, and
`PromIn` that its promises are messages of its own in memory.

A *ticketed* worker, or one holding a `next` promise, certifies without any
fresh write (`nacert_of_run`, the run stops once the promise set is empty):
such a certification (`NACert`) replays against any larger memory
(`nacert_replay`) and gives an instruction step (`instrEnabledSem_of`).
-/
import Kraken.Promising.LiveTicketDrop
import Kraken.Promising.LiveSem
import Kraken.Promising.LiveSemShape

namespace Kraken.Promising.Live.TicketSolo

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.TicketInv
open Kraken.Promising.Live.TicketDrop Kraken.Promising.Live.Sem Kraken.Promising.Live.SemShape
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkWorker).addrOf

/-! ## Positions in order -/

/-- The order of positions (the spin loop is one rank). -/
def rk : Nat → Nat
  | 1 => 0 | 2 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 6 | 11 => 7 | 12 => 8
  | _ => 9

/-- The thread's position has rank at most `r`. -/
def RkLe (t : Thread isa) (r : Nat) : Prop := ∀ i ∈ tkPcs, t.st.st.2 = pcA i → rk i ≤ r

theorem rkLe_iff {t : Thread isa} {p : Nat} (hp : p ∈ tkPcs) (ht : t.st.st.2 = pcA p) (r : Nat) :
    RkLe t r ↔ rk p ≤ r :=
  ⟨fun h => h p hp ht, fun h i hi hi' => by rw [addrOf_inj hi hp (hi'.symm.trans ht)]; exact h⟩

theorem pc_ne {s : isa.State} {i j : Nat} (hi : s.st.2 = pcA i) (hj : s.st.2 = pcA j) (hi' : i ∈ tkPcs)
    (hj' : j ∈ tkPcs) (h : i ≠ j) : False :=
  h (addrOf_inj hi' hj' (hi.symm.trans hj))

/-! ## The solo-run predicates -/

/-- A readable `owner` value: some message (or the initial value) of `o`
whose low word is `k`. -/
def ORd (o : BitVec 64) (mem : Memory) (k : Nat) : Prop :=
  ∃ tr v, mem.read? (L4 o) tr = some v ∧ v.toNat % 2 ^ 32 = k

/-- The register facts a worker establishes for itself. -/
structure RInv (o : BitVec 64) (t : Thread isa) (mem : Memory) : Prop where
  f2 : t.st.st.2 = pcA 2 → wn t.st.st.1.regs.X6 = 1
  f5 : t.st.st.2 = pcA 5 → ORd o mem (wn t.st.st.1.regs.X4)
  f6 : t.st.st.2 = pcA 6 → t.st.st.1.status.z = true → ORd o mem (wn t.st.st.1.regs.X3)
  f7 : ∀ i ∈ [7, 8, 9, 10, 11], t.st.st.2 = pcA i → ORd o mem (wn t.st.st.1.regs.X3)
  f11 : t.st.st.2 = pcA 11 → wn t.st.st.1.regs.X4 = (wn t.st.st.1.regs.X3 + 1) % 2 ^ 32

/-- Every promise of `tid` is a message of its own in memory. -/
def PromIn (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.tid = tid

/-- The thread holds a promise to `next`. -/
def HasX (x : BitVec 64) (t : Thread isa) (mem : Memory) : Prop :=
  ∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 x

/-- **What a certifiable worker's promises satisfy.** -/
structure Good (x o c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) : Prop where
  loc : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w →
    (w.loc = L4 x ∧ RkLe t 1) ∨ (w.loc = L4 c ∧ RkLe t 5) ∨ (w.loc = L4 o ∧ RkLe t 7)
  uniq : ∀ ts1 ∈ t.prom, ∀ ts2 ∈ t.prom, ∀ w1 w2, mem.get? ts1 = some w1 → mem.get? ts2 = some w2 →
    w1.loc = w2.loc → ts1 = ts2
  coh : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts
  vw : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 o → t.views.vwOld < ts
  xval : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 x →
    ∃ tr v, mem.read? (L4 x) tr = some v ∧ tr < ts ∧ mem.atomic (L4 x) tid tr ts = true ∧
      w.val.toNat = (v.toNat % 2 ^ 32 + 1) % 2 ^ 32
  oval : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 o →
    (Ticketed t → w.val.toNat = (tk t + 1) % 2 ^ 32 ∧ ORd o mem (tk t)) ∧
    (¬ Ticketed t → ∃ tsx ∈ t.prom, ∃ wx, mem.get? tsx = some wx ∧ wx.loc = L4 x ∧
      w.val.toNat = wx.val.toNat ∧ ∃ k, ORd o mem k ∧ (k + 1) % 2 ^ 32 = w.val.toNat)

theorem good_nil {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory} (h : t.prom = []) :
    Good x o c tid t mem := by
  constructor <;> (intro ts hts; rw [h] at hts; cases hts)

/-! ## Larger memories -/

theorem ORd.mono {o : BitVec 64} {mem mem' : Memory} (hp : mem.Prefix mem') {k : Nat} (h : ORd o mem k) :
    ORd o mem' k := by
  obtain ⟨tr, v, hr, hv⟩ := h
  refine ⟨tr, v, ?_, hv⟩
  have : tr ≤ mem.last := by
    rcases mem.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw, -, -⟩
    · exact Nat.zero_le _
    · exact mem.last_le_of_get?_eq_some hw
  rw [hp.read? this]; exact hr

theorem RInv.mono {o : BitVec 64} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : RInv o t mem) :
    RInv o t mem' :=
  ⟨h.f2, fun a => (h.f5 a).mono hp, fun a b => (h.f6 a b).mono hp, fun i hi a => (h.f7 i hi a).mono hp, h.f11⟩

theorem PromIn.get {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem)
    {ts : Time} (hts : ts ∈ t.prom) : mem'.get? ts = mem.get? ts := by
  obtain ⟨w, hw, -⟩ := h ts hts
  exact hp.get? (mem.last_le_of_get?_eq_some hw)

theorem PromIn.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem) :
    PromIn tid t mem' := fun ts hts => by rw [h.get hp hts]; exact h ts hts

theorem PromIn.le {tid : Nat} {t : Thread isa} {mem : Memory} (h : PromIn tid t mem) : ∀ ts ∈ t.prom, ts ≤ mem.last :=
  fun ts hts => let ⟨_, hw, _⟩ := h ts hts; mem.last_le_of_get?_eq_some hw

theorem HasX.mono {x : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : HasX x t mem) : HasX x t mem' := by
  obtain ⟨ts, hts, w, hw, hl⟩ := h
  exact ⟨ts, hts, w, by rw [hP.get hp hts]; exact hw, hl⟩

theorem Good.mono {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : Good x o c tid t mem) : Good x o c tid t mem' := by
  have e := fun {ts} (hts : ts ∈ t.prom) => hP.get hp hts
  refine ⟨fun ts hts w hw => h.loc ts hts w (by rw [← e hts]; exact hw),
    fun ts1 h1 ts2 h2 w1 w2 hw1 hw2 => h.uniq ts1 h1 ts2 h2 w1 w2 (by rw [← e h1]; exact hw1) (by rw [← e h2]; exact hw2),
    fun ts hts w hw => h.coh ts hts w (by rw [← e hts]; exact hw),
    fun ts hts w hw => h.vw ts hts w (by rw [← e hts]; exact hw), fun ts hts w hw hl => ?_,
    fun ts hts w hw hl => ?_⟩
  · obtain ⟨tr, v, h1, h2, h3, h4⟩ := h.xval ts hts w (by rw [← e hts]; exact hw) hl
    have htl := hP.le ts hts
    refine ⟨tr, v, ?_, h2, ?_, h4⟩
    · rw [hp.read? (Nat.le_of_lt (Nat.lt_of_lt_of_le h2 htl))]; exact h1
    · rw [hp.atomic_eq h2 htl]; exact h3
  · obtain ⟨h1, h2⟩ := h.oval ts hts w (by rw [← e hts]; exact hw) hl
    refine ⟨fun hk => ⟨(h1 hk).1, (h1 hk).2.mono hp⟩, fun hk => ?_⟩
    obtain ⟨tsx, hx, wx, hwx, a, b, k, hk', hk''⟩ := h2 hk
    exact ⟨tsx, hx, wx, by rw [e hx]; exact hwx, a, b, k, hk'.mono hp, hk''⟩

/-! ## Quiet steps -/

/-- A step that keeps memory and promises, does not lower `coh`, `vwOld` or
the rank, and keeps the ticket. -/
theorem good_quiet {x o c : BitVec 64} {tid : Nat} {t t' : Thread isa} {mem : Memory}
    (hg : Good x o c tid t' mem) (hp : t'.prom = t.prom) (hcoh : ∀ l, t.views.getCoh l ≤ t'.views.getCoh l)
    (hvw : t.views.vwOld ≤ t'.views.vwOld) (hrk : ∀ r, RkLe t' r → RkLe t r)
    (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t) : Good x o c tid t mem := by
  refine ⟨fun ts hts w hw => ?_, fun ts1 h1 ts2 h2 => hg.uniq ts1 (hp ▸ h1) ts2 (hp ▸ h2),
    fun ts hts w hw => Nat.lt_of_le_of_lt (hcoh _) (hg.coh ts (hp ▸ hts) w hw),
    fun ts hts w hw hl => Nat.lt_of_le_of_lt hvw (hg.vw ts (hp ▸ hts) w hw hl),
    fun ts hts => hg.xval ts (hp ▸ hts), fun ts hts w hw hl => ?_⟩
  · rcases hg.loc ts (hp ▸ hts) w hw with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact .inl ⟨a, hrk _ b⟩
    · exact .inr (.inl ⟨a, hrk _ b⟩)
    · exact .inr (.inr ⟨a, hrk _ b⟩)
  · obtain ⟨h1, h2⟩ := hg.oval ts (hp ▸ hts) w hw hl
    refine ⟨fun hkt => by rw [← hk hkt]; exact h1 (htk.mpr hkt), fun hkt => ?_⟩
    obtain ⟨tsx, hx, rest⟩ := h2 (fun h => hkt (htk.mp h))
    exact ⟨tsx, hp ▸ hx, rest⟩

/-! ## One step of a worker alone -/

local macro "goto_static" hS:ident hst:ident : term =>
  `(by rw [$hst:ident]; exact ($hS).goto _ _ rfl rfl rfl rfl)

/-- The results of one step of a worker, with any promises. -/
structure SoloRes (x o c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop where
  sinv : SInv x o c oc.thread.st
  rinv : RInv o oc.thread oc.mem
  promIn : PromIn tid oc.thread oc.mem
  back : Good x o c tid oc.thread oc.mem → Good x o c tid t mem ∧
    (t.prom ≠ [] → Ticketed t ∨ HasX x t mem → oc.mem = mem)
  tkt : Ticketed t → Ticketed oc.thread ∧ tk oc.thread = tk t
  pre : ¬ Ticketed oc.thread → oc.thread.prom = t.prom ∧ oc.mem = mem

/-- A promise in the old set, kept by an erase of another timestamp. -/
theorem mem_erase_of_ne' {p : List Time} {a b : Time} (h : a ∈ p) (hne : a ≠ b) : a ∈ p.erase b :=
  (List.mem_erase_of_ne hne).mpr h

theorem wn_setWidth (v : BitVec 128) : wn (UInt64.ofBitVec (BitVec.setWidth 64 (BitVec.setWidth 32 v))) =
    v.toNat % 2 ^ 32 := wn_setWidth32 v

theorem val_setWidth (r : UInt64) : (BitVec.setWidth 128 (BitVec.setWidth 32 r.toBitVec)).toNat = wn r :=
  val_setWidth32 r

/-- **One step of a worker alone**, position by position. -/
theorem step_solo {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hxo : L4 x ≠ L4 o) (hxc : L4 x ≠ L4 c) (hoc : L4 o ≠ L4 c)
    (hS : SInv x o c t.st) (hR : RInv o t mem) (hP : PromIn tid t mem)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : SoloRes x o c tid t mem oc := by
  obtain ⟨hSt, p, hp, hpc⟩ := hS
  obtain ⟨hcapd, hcoh, hpre, -⟩ := stepOne_dord Arch.armv8 hs ho
  have hsinv := (step_sinv ⟨hSt, p, hp, hpc⟩ hs ho).1
  have hPl := hP.le
  -- the facts shared by the steps that keep memory and promises
  have quiet : ∀ q ∈ tkPcs, oc.thread.st.st.2 = pcA q → rk p ≤ rk q → oc.mem = mem → oc.thread.prom = t.prom →
      oc.thread.views.vwOld = t.views.vwOld → (Ticketed oc.thread ↔ Ticketed t) →
      (Ticketed t → tk oc.thread = tk t) → RInv o oc.thread oc.mem →
      SoloRes x o c tid t mem oc := by
    intro q hq hpq hr hm hpr hvw htk hk hRi
    refine ⟨hsinv, hRi, fun ts hts => by rw [hm]; exact hP ts (hpr ▸ hts), fun hg => ⟨?_, fun _ _ => hm⟩,
      fun h => ⟨htk.mpr h, hk h⟩, fun h => ⟨hpr, hm⟩⟩
    rw [hm] at hg
    exact good_quiet hg hpr hcoh (Nat.le_of_eq hvw.symm)
      (fun r h => (rkLe_iff hp hpc r).mpr (Nat.le_trans hr ((rkLe_iff hq hpq r).mp h))) htk hk
  have tkd : ∀ q, q ∈ tkPcs → q ≠ 1 → q ≠ 2 → t.st.st.2 = pcA q → Ticketed t := fun q hq h1 h2 h =>
    ticketed_at h hq h1 h2
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `MOV X6, #1`
    have hex := exec_mov _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    have hvw := spec_done_vw _ _ hex hs ho
    have hnt : ¬ Ticketed oc.thread := fun h => h.2 (by rw [hst])
    refine quiet 2 (by decide) (by rw [hst]) (by decide) hm hpr hvw
      (iff_of_false hnt (fun h => h.1 hpc)) (fun h => absurd hpc h.1) ⟨fun _ => by rw [hst]; rfl, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro i hi h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by omega)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · -- 2: `LDADDA`
    have hex := exec_ldadda _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dx
    obtain ⟨tr, old, hst, hrd, hw⟩ := spec_rmw_p _ _ rfl hex hs ho
    have h6 := hR.f2 hpc
    have htk1 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    have hntk : ¬ Ticketed t := fun h => h.2 hpc
    have hk : tk oc.thread = old.toNat % 2 ^ 32 := by unfold tk; rw [hst]; exact wn_setWidth old
    have hval : (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)).toNat =
        (old.toNat % 2 ^ 32 + 1) % 2 ^ 32 := by
      simp only [wn] at h6
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
      have : t.st.st.1.regs.X6.toBitVec.toNat % 2 ^ 32 = 1 := h6
      rw [this]; omega
    have hrk4 : ∀ r, RkLe oc.thread r ↔ 2 ≤ r := rkLe_iff (p := 4) (by decide) (by rw [hst])
    have hRi : RInv o oc.thread oc.mem := ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun i hi h => ?_, fun h => ?_⟩
    rotate_left
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by omega)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    rcases hw with ⟨hm, hpr, hvw, hat⟩ | ⟨tsx, htsx, hgx, hcx, hm, hpr, hvw, htr, hat⟩
    · -- a fresh write: no `next` promise, no `owner` promise
      have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hvw' : mem.last + 1 ≤ oc.thread.views.vwOld := hvw rfl
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      refine ⟨hsinv, hRi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), fun hg => ?_,
        fun h => absurd h hntk, fun h => absurd htk1 h⟩
      -- every promise is to `c`
      have honly : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 c := by
        intro ts hts w hw
        have hw' : oc.mem.get? ts = some w := by rw [hgm ts hts]; exact hw
        rcases hg.loc ts (hpr' ▸ hts) w hw' with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd ((hrk4 1).mp h) (by decide)
        · exact h
        · exact (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_of_succ_le hvw')
            (hg.vw ts (hpr' ▸ hts) w hw' h)) (hPl ts hts))).elim
      refine ⟨⟨fun ts hts w hw => .inr (.inl ⟨honly ts hts w hw, (rkLe_iff (by decide) hpc 5).mpr (by decide)⟩),
        fun ts1 h1 ts2 h2 w1 w2 hw1 hw2 => hg.uniq ts1 (hpr' ▸ h1) ts2 (hpr' ▸ h2) w1 w2
          (by rw [hgm ts1 h1]; exact hw1) (by rw [hgm ts2 h2]; exact hw2),
        fun ts hts w hw => Nat.lt_of_le_of_lt (hcoh _) (hg.coh ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw)),
        fun ts hts w hw hl => absurd (honly ts hts w hw) (by rw [hl]; exact hoc),
        fun ts hts w hw hl => absurd (honly ts hts w hw) (by rw [hl]; exact hxc),
        fun ts hts w hw hl => absurd (honly ts hts w hw) (by rw [hl]; exact hoc)⟩, fun _ h => ?_⟩
      rcases h with h | ⟨ts, hts, w, hw, hl⟩
      · exact absurd h hntk
      · exact absurd (honly ts hts w hw) (by rw [hl]; exact hxc)
    · -- fulfilling the `next` promise `tsx`
      have hgm : oc.mem = mem := hm
      refine ⟨hsinv, hRi, fun ts hts => by rw [hgm]; exact hP ts (List.mem_of_mem_erase (hpr ▸ hts)),
        fun hg => ?_, fun h => absurd h hntk, fun h => absurd htk1 h⟩
      rw [hgm] at hg
      have hin : ∀ ts ∈ t.prom, ts ≠ tsx → ts ∈ oc.thread.prom := fun ts hts hne => hpr ▸ mem_erase_of_ne' hts hne
      have hnx : ∀ ts ∈ t.prom, ts ≠ tsx → ∀ w, mem.get? ts = some w → w.loc ≠ L4 x := by
        intro ts hts hne w hw hl
        rcases hg.loc ts (hin ts hts hne) w hw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd ((hrk4 1).mp h) (by decide)
        · exact hxc (hl.symm.trans h)
        · exact hxo (hl.symm.trans h)
      have hxeq : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 x → ts = tsx :=
        fun ts hts w hw hl => Classical.byContradiction fun hne => hnx ts hts hne w hw hl
      refine ⟨⟨fun ts hts w hw => ?_, fun ts1 h1 ts2 h2 w1 w2 hw1 hw2 hl => ?_, fun ts hts w hw => ?_,
        fun ts hts w hw hl => ?_, fun ts hts w hw hl => ?_, fun ts hts w hw hl => ?_⟩, fun _ _ => hm⟩
      · by_cases e : ts = tsx
        · subst e; rw [hgx] at hw; cases hw
          exact .inl ⟨rfl, (rkLe_iff (by decide) hpc 1).mpr (by decide)⟩
        · rcases hg.loc ts (hin ts hts e) w hw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd ((hrk4 1).mp h) (by decide)
          · exact .inr (.inl ⟨h, (rkLe_iff (by decide) hpc 5).mpr (by decide)⟩)
          · exact .inr (.inr ⟨h, (rkLe_iff (by decide) hpc 7).mpr (by decide)⟩)
      · by_cases e1 : ts1 = tsx <;> by_cases e2 : ts2 = tsx
        · rw [e1, e2]
        · subst e1; rw [hgx] at hw1; cases hw1
          exact absurd hl.symm (hnx ts2 h2 e2 w2 hw2)
        · subst e2; rw [hgx] at hw2; cases hw2
          exact absurd hl (hnx ts1 h1 e1 w1 hw1)
        · exact hg.uniq ts1 (hin ts1 h1 e1) ts2 (hin ts2 h2 e2) w1 w2 hw1 hw2 hl
      · by_cases e : ts = tsx
        · subst e; rw [hgx] at hw; cases hw; exact hcx
        · exact Nat.lt_of_le_of_lt (hcoh _) (hg.coh ts (hin ts hts e) w hw)
      · have e : ts ≠ tsx := fun e => by subst e; rw [hgx] at hw; cases hw; exact hxo hl
        exact Nat.lt_of_le_of_lt hvw (hg.vw ts (hin ts hts e) w hw hl)
      · obtain rfl := hxeq ts hts w hw hl
        rw [hgx] at hw; cases hw
        exact ⟨tr, old, hrd, htr, hat, hval⟩
      · have e : ts ≠ tsx := fun e => by subst e; rw [hgx] at hw; cases hw; exact hxo hl
        obtain ⟨h1, -⟩ := hg.oval ts (hin ts hts e) w hw hl
        obtain ⟨h1, h2⟩ := h1 htk1
        rw [hk] at h1 h2
        refine ⟨fun h => absurd h hntk, fun _ => ⟨tsx, htsx, _, hgx, rfl, ?_, _, h2, h1.symm⟩⟩
        show w.val.toNat = (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)).toNat
        rw [hval, h1]
  · -- 4: `LDAR`
    have hex := exec_ldar _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO
    obtain ⟨ts, v, hst, hrd, -, hm, hpr, -⟩ := spec_load _ _ hex hs ho
    have hvw := spec_load_vw _ _ hex hs ho
    have h1 := tkd 4 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    refine quiet 5 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
      (fun _ => by unfold tk; rw [hst]; rfl) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro _; rw [hm]; refine ⟨ts, v, hrd, ?_⟩; rw [hst]; exact (wn_setWidth v).symm
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro i hi h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by omega)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · -- 5: `CMP`
    obtain ⟨sf, hex, hz⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    have hvw := spec_done_vw _ _ hex hs ho
    have h1 := tkd 5 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    refine quiet 6 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
      (fun _ => by unfold tk; rw [hst]) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro _ hz'
      rw [hst] at hz'
      have e := (w32_eq_iff _ _).mp (hz.mp hz')
      rw [hm, hst]; show ORd o mem (wn t.st.st.1.regs.X3)
      rw [← e]; exact hR.f5 hpc
    · intro i hi h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by omega)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · -- 6: `B.NE`
    have hex := exec_bne _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    have hvw := spec_done_vw _ _ hex hs ho
    have h1 := tkd 6 (by decide) (by decide) (by decide) hpc
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
      refine quiet 7 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
        (fun _ => by unfold tk; rw [hst]) ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
      · intro _ _ _; rw [hm, hst]; exact hR.f6 hpc hz
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · rw [ite_eq_right hz] at hst
      have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
      refine quiet 4 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
        (fun _ => by unfold tk; rw [hst]) ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
      · intro i hi h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
          (by omega)).elim
      · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · -- 7: `LDR` counter
    have hex := exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc
    obtain ⟨ts, v, hst, hrd, -, hm, hpr, -⟩ := spec_load _ _ hex hs ho
    have hvw := spec_load_vw _ _ hex hs ho
    have h1 := tkd 7 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    refine quiet 8 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
      (fun _ => by unfold tk; rw [hst]; rfl) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro _ _ _; rw [hm, hst]; exact hR.f7 7 (by decide) hpc
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · -- 8: `ADD W5`
    have hex := exec_add5 _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    have hvw := spec_done_vw _ _ hex hs ho
    have h1 := tkd 8 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    refine quiet 9 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
      (fun _ => by unfold tk; rw [hst]; rfl) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro _ _ _; rw [hm, hst]; exact hR.f7 8 (by decide) hpc
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · -- 9: `STR` counter
    have hex := exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc
    obtain ⟨hst, hw⟩ := spec_store_p _ _ hex hs ho
    have h1 := tkd 9 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    have hk : tk oc.thread = tk t := by unfold tk; rw [hst]
    have hrk10 : ∀ r, RkLe oc.thread r ↔ 6 ≤ r := rkLe_iff (p := 10) (by decide) (by rw [hst])
    have hRi : ∀ m', mem.Prefix m' → RInv o oc.thread m' := fun m' hm' =>
      ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun i hi h => ?_, fun h => ?_⟩
    rotate_left
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · rw [hst]; exact (hR.f7 9 (by decide) hpc).mono hm'
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    rcases hw with ⟨hm, hpr, hvw⟩ | ⟨tsc, htsc, hgc, hcc, -, hm, hpr, hvw⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hvw' : mem.last + 1 ≤ oc.thread.views.vwOld := hvw rfl
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      refine ⟨hsinv, hRi _ (by rw [hm]; exact Memory.Prefix.append _ _),
        fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), fun hg => ?_,
        fun _ => ⟨h2, hk⟩, fun h => absurd h2 h⟩
      have hnone : ∀ ts ∈ t.prom, False := by
        intro ts hts
        obtain ⟨w, hw, -⟩ := hP ts hts
        have hw' : oc.mem.get? ts = some w := by rw [hgm ts hts]; exact hw
        rcases hg.loc ts (hpr' ▸ hts) w hw' with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hl, -⟩
        · exact absurd ((hrk10 1).mp h) (by decide)
        · exact absurd ((hrk10 5).mp h) (by decide)
        · exact (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_of_succ_le hvw')
            (hg.vw ts (hpr' ▸ hts) w hw' hl)) (hPl ts hts))).elim
      refine ⟨⟨fun ts hts => (hnone ts hts).elim, fun ts hts => (hnone ts hts).elim, fun ts hts => (hnone ts hts).elim,
        fun ts hts => (hnone ts hts).elim, fun ts hts => (hnone ts hts).elim, fun ts hts => (hnone ts hts).elim⟩,
        fun hne _ => ?_⟩
      obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hnone ts hts).elim
    · have hgm : oc.mem = mem := hm
      refine ⟨hsinv, hRi _ (by rw [hgm]; exact Memory.Prefix.refl _),
        fun ts hts => by rw [hgm]; exact hP ts (List.mem_of_mem_erase (hpr ▸ hts)), fun hg => ?_,
        fun _ => ⟨h2, hk⟩, fun h => absurd h2 h⟩
      rw [hgm] at hg
      have hin : ∀ ts ∈ t.prom, ts ≠ tsc → ts ∈ oc.thread.prom := fun ts hts hne => hpr ▸ mem_erase_of_ne' hts hne
      have honly : ∀ ts ∈ t.prom, ts ≠ tsc → ∀ w, mem.get? ts = some w → w.loc = L4 o := by
        intro ts hts hne w hw
        rcases hg.loc ts (hin ts hts hne) w hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd ((hrk10 1).mp h) (by decide)
        · exact absurd ((hrk10 5).mp h) (by decide)
        · exact h
      have hne_o : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 o → ts ≠ tsc :=
        fun ts hts w hw hl e => by subst e; rw [hgc] at hw; cases hw; exact hoc hl.symm
      refine ⟨⟨fun ts hts w hw => ?_, fun ts1 h1 ts2 h2 w1 w2 hw1 hw2 hl => ?_, fun ts hts w hw => ?_,
        fun ts hts w hw hl => Nat.lt_of_le_of_lt hvw (hg.vw ts (hin ts hts (hne_o ts hts w hw hl)) w hw hl),
        fun ts hts w hw hl => ?_, fun ts hts w hw hl => ?_⟩, fun _ _ => hm⟩
      · by_cases e : ts = tsc
        · subst e; rw [hgc] at hw; cases hw
          exact .inr (.inl ⟨rfl, (rkLe_iff (by decide) hpc 5).mpr (by decide)⟩)
        · exact .inr (.inr ⟨honly ts hts e w hw, (rkLe_iff (by decide) hpc 7).mpr (by decide)⟩)
      · by_cases e1 : ts1 = tsc <;> by_cases e2 : ts2 = tsc
        · rw [e1, e2]
        · subst e1; rw [hgc] at hw1; cases hw1
          exact absurd (hl.trans (honly ts2 h2 e2 w2 hw2)) (Ne.symm hoc)
        · subst e2; rw [hgc] at hw2; cases hw2
          exact absurd (hl.symm.trans (honly ts1 h1 e1 w1 hw1)) (Ne.symm hoc)
        · exact hg.uniq ts1 (hin ts1 h1 e1) ts2 (hin ts2 h2 e2) w1 w2 hw1 hw2 hl
      · by_cases e : ts = tsc
        · subst e; rw [hgc] at hw; cases hw; exact hcc
        · exact Nat.lt_of_le_of_lt (hcoh _) (hg.coh ts (hin ts hts e) w hw)
      · by_cases e : ts = tsc
        · subst e; rw [hgc] at hw; cases hw; exact absurd hl.symm hxc
        · exact absurd (hl.symm.trans (honly ts hts e w hw)) hxo
      · obtain ⟨a, -⟩ := hg.oval ts (hin ts hts (hne_o ts hts w hw hl)) w hw hl
        exact ⟨fun _ => by rw [← hk]; exact a h2, fun h => absurd h1 h⟩
  · -- 10: `ADD W4`
    have hex := exec_add4 _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    have hvw := spec_done_vw _ _ hex hs ho
    have h1 := tkd 10 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    refine quiet 11 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
      (fun _ => by unfold tk; rw [hst]; rfl) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro _ _ _; rw [hm, hst]; exact hR.f7 10 (by decide) hpc
    · intro _
      rw [hst]
      show (BitVec.setWidth 64 (t.st.st.1.regs.X3.toBitVec.take 32 + 1#32)).toNat % 2 ^ 32 =
        (t.st.st.1.regs.X3.toNat % 2 ^ 32 + 1) % 2 ^ 32
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.take, BitVec.extractLsb'_toNat,
        Nat.shiftRight_zero, BitVec.toNat_ofNat, UInt64.toNat]
      omega
  · -- 11: `STLR`
    have hex := exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO
    obtain ⟨hst, hw⟩ := spec_store_p _ _ hex hs ho
    have h1 := tkd 11 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    have hk : tk oc.thread = tk t := by unfold tk; rw [hst]
    have hrk12 : ∀ r, RkLe oc.thread r ↔ 8 ≤ r := rkLe_iff (p := 12) (by decide) (by rw [hst])
    have hRi : RInv o oc.thread oc.mem := ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun i hi h => ?_, fun h => ?_⟩
    rotate_left
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by omega)).elim
    · exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    -- every remaining promise of the resulting thread is impossible
    have hdead : ∀ ts ∈ oc.thread.prom, ∀ w, oc.mem.get? ts = some w → Good x o c tid oc.thread oc.mem → False := by
      intro ts hts w hw hg
      rcases hg.loc ts hts w hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd ((hrk12 1).mp h) (by decide)
      · exact absurd ((hrk12 5).mp h) (by decide)
      · exact absurd ((hrk12 7).mp h) (by decide)
    rcases hw with ⟨hm, hpr, -⟩ | ⟨tso, htso, hgo, hco, hvo, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      have hnone : Good x o c tid oc.thread oc.mem → ∀ ts ∈ t.prom, False := fun hg ts hts => by
        obtain ⟨w, hw, -⟩ := hP ts hts
        exact hdead ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw) hg
      refine ⟨hsinv, hRi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), fun hg => ?_,
        fun _ => ⟨h2, hk⟩, fun h => absurd h2 h⟩
      refine ⟨⟨fun ts hts => (hnone hg ts hts).elim, fun ts hts => (hnone hg ts hts).elim,
        fun ts hts => (hnone hg ts hts).elim, fun ts hts => (hnone hg ts hts).elim,
        fun ts hts => (hnone hg ts hts).elim, fun ts hts => (hnone hg ts hts).elim⟩, fun hne _ => ?_⟩
      obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hnone hg ts hts).elim
    · have hgm : oc.mem = mem := hm
      refine ⟨hsinv, hRi, fun ts hts => by rw [hgm]; exact hP ts (List.mem_of_mem_erase (hpr ▸ hts)), fun hg => ?_,
        fun _ => ⟨h2, hk⟩, fun h => absurd h2 h⟩
      have honly : ∀ ts ∈ t.prom, ts = tso := fun ts hts => Classical.byContradiction fun hne => by
        obtain ⟨w, hw, -⟩ := hP ts hts
        exact hdead ts (hpr ▸ mem_erase_of_ne' hts hne) w (by rw [hgm]; exact hw) hg
      have hwo : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w = (⟨L4 o,
          BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec), tid⟩ : Msg) := fun ts hts w hw => by
        rw [honly ts hts, hgo] at hw; exact (Option.some.inj hw).symm
      refine ⟨⟨fun ts hts w hw => ?_, fun ts1 h1 ts2 h2 _ _ _ _ _ => by rw [honly ts1 h1, honly ts2 h2],
        fun ts hts w hw => ?_, fun ts hts w hw _ => ?_, fun ts hts w hw hl => ?_, fun ts hts w hw hl => ?_⟩,
        fun _ _ => hm⟩
      · rw [hwo ts hts w hw]; exact .inr (.inr ⟨rfl, (rkLe_iff (by decide) hpc 7).mpr (by decide)⟩)
      · rw [hwo ts hts w hw, honly ts hts]; exact hco
      · rw [honly ts hts]; exact hvo rfl
      · rw [hwo ts hts w hw] at hl; exact absurd hl.symm hxo
      · rw [hwo ts hts w hw]
        refine ⟨fun _ => ⟨?_, hR.f7 11 (by decide) hpc⟩, fun h => absurd h1 h⟩
        rw [val_setWidth]; exact hR.f11 hpc
  · -- 12: `B done`
    have hex := exec_b_done _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    have hvw := spec_done_vw _ _ hex hs ho
    have h1 := tkd 12 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    refine quiet 14 (by decide) (by rw [hst]) (by decide) hm hpr hvw (iff_of_true h2 h1)
      (fun _ => by unfold tk; rw [hst]) ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
    · intro i hi h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide)
        (by omega)).elim
    · intro h; exact (pc_ne (s := oc.thread.st) (by rw [hst]) h (by decide) (by decide) (by decide)).elim
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-! ## Along a run -/

theorem threadNPn_prefix {tid n : Nat} {p q : Thread isa × Memory} (h : ThreadNPn Arch.armv8 tid n p q) :
    p.2.Prefix q.2 := h.mem_prefix

section Run

variable {x o c : BitVec 64} {tid : Nat} (hxo : L4 x ≠ L4 o) (hxc : L4 x ≠ L4 c) (hoc : L4 o ≠ L4 c)

include hxo hxc hoc

/-- **A certifiable worker is `Good`.** -/
theorem good_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
    SInv x o c p.1.st → RInv o p.1 p.2 → PromIn tid p.1 p.2 → Good x o c tid p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _ _; exact good_nil hq
  | step hs _ ih =>
    intro hq hS hR hP
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have r := step_solo hxo hxc hoc hS hR hP hs ho
    exact (r.back (ih hq r.sinv r.rinv r.promIn)).1

theorem good_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.armv8 tid t mem fuel)
    (hS : SInv x o c t.st) (hR : RInv o t mem) (hP : PromIn tid t mem) : Good x o c tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; good_of_run hxo hxc hoc hr hp hS hR hP

/-- A certification without fresh writes, against memory `mem`. -/
def NACert (fuel tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∃ t', ThreadNPn Arch.armv8 tid fuel (t, mem) (t', mem) ∧ t'.prom = []

/-- **A ticketed worker, or one holding a `next` promise, certifies without
fresh writes** (stopping once its promise set is empty). -/
theorem nacert_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
    SInv x o c p.1.st → RInv o p.1 p.2 → PromIn tid p.1 p.2 → (Ticketed p.1 ∨ HasX x p.1 p.2) →
    ∃ t', ThreadNPn Arch.armv8 tid n p (t', p.2) ∧ t'.prom = [] := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _ _ _; exact ⟨p.1, .refl _ _, hq⟩
  | @step n p q r hs h ih =>
    intro hq hS hR hP hT
    by_cases hp0 : p.1.prom = []
    · exact ⟨p.1, .refl _ _, hp0⟩
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    have rs := step_solo hxo hxc hoc hS hR hP hs' ho
    have hg := good_of_run hxo hxc hoc h hq rs.sinv rs.rinv rs.promIn
    have hm := (rs.back hg).2 hp0 hT
    have hT' : Ticketed oc.thread ∨ HasX x oc.thread oc.mem := by
      rcases hT with h1 | h1
      · exact .inl (rs.tkt h1).1
      · by_cases h2 : Ticketed oc.thread
        · exact .inl h2
        · obtain ⟨e1, e2⟩ := rs.pre h2
          obtain ⟨ts, hts, w, hw, hl⟩ := h1
          exact .inr ⟨ts, e1 ▸ hts, w, by rw [e2]; exact hw, hl⟩
    obtain ⟨t', h', ht'⟩ := ih hq rs.sinv rs.rinv rs.promIn hT'
    refine ⟨t', .step ⟨outs, oc, hs', ho, rfl⟩ ?_, ht'⟩
    rw [← hm]; exact h'

theorem nacert_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.armv8 tid t mem fuel)
    (hS : SInv x o c t.st) (hR : RInv o t mem) (hP : PromIn tid t mem) (hT : Ticketed t ∨ HasX x t mem) :
    NACert fuel tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; nacert_of_run hxo hxc hoc hr hp hS hR hP hT

end Run

/-! ## Replay and enabledness -/

/-- **A step that keeps memory replays against a larger memory.** -/
theorem replay_tk {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv x o c t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.armv8 t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.armv8 t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  obtain ⟨hSt, p, hpp, hpc⟩ := hS
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replay_done _ _ hp hb hs ho hm (exec_mov _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_rmw _ _ hp hb hs ho hm rfl (exec_ldadda _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dx)
  · exact replay_load _ _ hp hb hs ho hm (exec_ldar _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO)
  · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · exact replay_done _ _ hp hb hs ho hm (exec_bne _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_load _ _ hp hb hs ho hm (exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc)
  · exact replay_done _ _ hp hb hs ho hm (exec_add5 _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_store _ _ hp hb hs ho hm (exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc)
  · exact replay_done _ _ hp hb hs ho hm (exec_add4 _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_store _ _ hp hb hs ho hm (exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO)
  · exact replay_done _ _ hp hb hs ho hm (exec_b_done _ (hSt.at (by decide) (by decide) hpc))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem nacert_replay {x o c : BitVec 64} {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.armv8 tid n p q → p.2 = q.2 → SInv x o c p.1.st → p.1.Bnd p.2.last →
    ∀ mem, p.2.Prefix mem → ThreadNPn Arch.armv8 tid n (p.1, mem) (q.1, mem) :=
  nacertG_replay (SInv x o c) (fun hS hs ho => (step_sinv hS hs ho).1)
    (fun hS hb hp hs ho hm => replay_tk hS hb hp hs ho hm)

theorem NACert.replay {x o c : BitVec 64} {fuel tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    (h : NACert fuel tid t mem0) (hS : SInv x o c t.st) (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) :
    NACert fuel tid t mem :=
  let ⟨t', hr, ht'⟩ := h; ⟨t', nacert_replay hr rfl hS hb mem hp, ht'⟩

/-- **A worker that is not at its end and either has no promise or certifies
without fresh writes can take an instruction step** (semantic machine). -/
theorem instrEnabledSem_of {x o c : BitVec 64} {fuel tid : Nat} {cfg : Config isa} {t : Thread isa}
    (ht : cfg.threads[tid]? = some t) (hS : SInv x o c t.st) (h14 : t.st.st.2 ≠ pcA 14)
    (hb : t.Bnd cfg.mem.last) (hn : t.prom = [] ∨ NACert fuel tid t cfg.mem) :
    InstrEnabledSem Arch.armv8 fuel tid cfg := by
  have hnil : t.prom = [] → InstrEnabledSem Arch.armv8 fuel tid cfg := by
    intro hp0
    have fin := fun outs (oc : Outcome isa) =>
      instrEnabledSem_of_step (A := Arch.armv8) (fuel := fuel) (outs := outs) (oc := oc) ht
    obtain ⟨hSt, p, hpp, hpc⟩ := hS
    simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
    rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid (exec_mov _ (hSt.at (by decide) (by decide) hpc))
        (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
    · obtain ⟨_, _, h1, h2, h3⟩ := en_rmw Arch.armv8 tid rfl hp0 hb
        (exec_ldadda _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dx)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 tid hp0
        (exec_ldar _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO) (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
      obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid hex (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
    · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid (exec_bne _ (hSt.at (by decide) (by decide) hpc))
        (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
    · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 tid hp0
        (exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc) (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid (exec_add5 _ (hSt.at (by decide) (by decide) hpc))
        (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 tid hp0 hb
        (exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid (exec_add4 _ (hSt.at (by decide) (by decide) hpc))
        (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 tid hp0 hb
        (exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid (exec_b_done _ (hSt.at (by decide) (by decide) hpc))
        (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
    · exact absurd hpc h14
  exact instrEnabledSem_of_nacertG ht hnil hn

end Kraken.Promising.Live.TicketSolo
