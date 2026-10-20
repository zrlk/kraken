/-
**Stage 3: solo runs of the x64 ticket-lock worker
with outstanding promises** (`ticketlock3.kl`, `tk3ImageV`, `Arch.tso`). An
adapted copy of `LiveTicketSolo.lean` (AArch64); the argument is unchanged.

A worker's run alone (`ThreadNPn`) can only fulfil a promise at the position
that writes its location: `next` at the `lock xaddl` (position 2), the
counter at the `movl %edx,(counter)` (9), `owner` at the release
`movl %ecx,(owner)` (11); positions are visited in order (`rk`), except for
the spin loop. So a certifiable worker (`Good`, from any certification:
`good_of_run`):

- has promises only to `next` before its `lock xaddl`, to the counter up to
  its counter store, to `owner` up to its release, at most one per location,
  each above its `coh` of the location;
- has its `owner` promise above its `vwOld` (the release is a release store
  on TSO, and any fresh write raises `vwOld` past every promise);
- has, for a `next` promise, the value one above an atomically preceding
  read of `next`; for an `owner` promise, the value one above its ticket (or,
  before its `lock xaddl`, the value of its `next` promise), and a readable
  `owner` message whose value is the ticket.

`RInv` collects the register facts the worker establishes for itself
(`RFact`, per position: `%eax` the ticket, `%ecx` the value read from
`owner`), and `PromIn` that its promises are messages of its own in memory.

A *ticketed* worker, or one holding a `next` promise, certifies without any
fresh write (`nacert_of_run`): such a certification (`NACert`) replays
against any larger memory (`nacert_replay`, through the fencing
`X64SemShape.replay_rmw_tso`) and gives an instruction step
(`instrEnabledSem_of`).
-/
import Kraken.Promising.LiveX64SemStep

namespace Kraken.Promising.Live.X64SemSolo

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketX64Trees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.Sem Kraken.Promising.Live.X64SemShape Kraken.Promising.Live.X64SemStep
open Kraken.Promising.Live.TsoRmw (en_rmw_tso)
open Kraken.Promising.Live.TicketX64Inv (XL OL CL Static Ticketed tk ticketed_at stepOne_end)
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV symTk)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk3ImageV).addrOf

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

/-! ## The solo-run predicates -/

/-- A readable `owner` value: some message (or the initial value) of `owner`
whose low word is `k`. -/
def ORd (mem : Memory) (k : Nat) : Prop :=
  ∃ tr v, mem.read? OL tr = some v ∧ v.toNat % 2 ^ 32 = k

/-- The register facts a worker establishes for itself, by position. -/
def RFact (md : MachineData) (mem : Memory) : Nat → Prop
  | 2 => (eax md).toNat = 1
  | 5 => ORd mem (ecx md).toNat
  | 6 => md.status.zf = true → ORd mem (eax md).toNat ∧ ecx md = eax md
  | 7 | 8 | 9 | 10 => ORd mem (eax md).toNat ∧ ecx md = eax md
  | 11 => ORd mem (eax md).toNat ∧ (ecx md).toNat = ((eax md).toNat + 1) % 2 ^ 32
  | _ => True

/-- The register facts at the thread's position. -/
def RInv (t : Thread isa) (mem : Memory) : Prop := ∀ j ∈ tkPcs, t.st.st.2 = pcA j → RFact t.st.st.1 mem j

theorem RInv.goto {u : Thread isa} {s : isa.State} {md : MachineData} {mem : Memory} {j : Nat}
    (hst : u.st = goto s md (pcA j)) (hj : j ∈ tkPcs) (h : RFact md mem j) : RInv u mem :=
  fun i hi hpi => by
    rw [hst] at hpi ⊢
    rw [addrOf_inj hi hj (Eq.symm hpi)]; exact h

/-- Every promise of `tid` is a message of its own in memory. -/
def PromIn (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.tid = tid

/-- The thread holds a promise to `next`. -/
def HasX (t : Thread isa) (mem : Memory) : Prop :=
  ∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = XL

/-- **What a certifiable worker's promises satisfy.** -/
structure Good (tid : Nat) (t : Thread isa) (mem : Memory) : Prop where
  loc : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w →
    (w.loc = XL ∧ RkLe t 1) ∨ (w.loc = CL ∧ RkLe t 5) ∨ (w.loc = OL ∧ RkLe t 7)
  uniq : ∀ ts1 ∈ t.prom, ∀ ts2 ∈ t.prom, ∀ w1 w2, mem.get? ts1 = some w1 → mem.get? ts2 = some w2 →
    w1.loc = w2.loc → ts1 = ts2
  coh : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts
  vw : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = OL → t.views.vwOld < ts
  xval : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = XL →
    ∃ tr v, mem.read? XL tr = some v ∧ tr < ts ∧ mem.atomic XL tid tr ts = true ∧
      w.val.toNat = (v.toNat % 2 ^ 32 + 1) % 2 ^ 32
  oval : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = OL →
    (Ticketed t → w.val.toNat = (tk t + 1) % 2 ^ 32 ∧ ORd mem (tk t)) ∧
    (¬ Ticketed t → ∃ tsx ∈ t.prom, ∃ wx, mem.get? tsx = some wx ∧ wx.loc = XL ∧
      w.val.toNat = wx.val.toNat ∧ ∃ k, ORd mem k ∧ (k + 1) % 2 ^ 32 = w.val.toNat)

theorem good_nil {tid : Nat} {t : Thread isa} {mem : Memory} (h : t.prom = []) : Good tid t mem := by
  constructor <;> (intro ts hts; rw [h] at hts; cases hts)

/-! ## Larger memories -/

theorem ORd.mono {mem mem' : Memory} (hp : mem.Prefix mem') {k : Nat} (h : ORd mem k) : ORd mem' k := by
  obtain ⟨tr, v, hr, hv⟩ := h
  refine ⟨tr, v, ?_, hv⟩
  have : tr ≤ mem.last := by
    rcases mem.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw, -, -⟩
    · exact Nat.zero_le _
    · exact mem.last_le_of_get?_eq_some hw
  rw [hp.read? this]; exact hr

theorem RInv.mono {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : RInv t mem) : RInv t mem' := by
  intro j hj hpc
  have h' := h j hj hpc
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h'
    | exact ORd.mono hp h'
    | exact ⟨ORd.mono hp h'.1, h'.2⟩
    | exact fun hz => ⟨ORd.mono hp (h' hz).1, (h' hz).2⟩

theorem PromIn.get {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem)
    {ts : Time} (hts : ts ∈ t.prom) : mem'.get? ts = mem.get? ts := by
  obtain ⟨w, hw, -⟩ := h ts hts
  exact hp.get? (mem.last_le_of_get?_eq_some hw)

theorem PromIn.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem) :
    PromIn tid t mem' := fun ts hts => by rw [h.get hp hts]; exact h ts hts

theorem PromIn.le {tid : Nat} {t : Thread isa} {mem : Memory} (h : PromIn tid t mem) : ∀ ts ∈ t.prom, ts ≤ mem.last :=
  fun ts hts => let ⟨_, hw, _⟩ := h ts hts; mem.last_le_of_get?_eq_some hw

theorem Good.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : Good tid t mem) : Good tid t mem' := by
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
theorem good_quiet {tid : Nat} {t t' : Thread isa} {mem : Memory}
    (hg : Good tid t' mem) (hp : t'.prom = t.prom) (hcoh : ∀ l, t.views.getCoh l ≤ t'.views.getCoh l)
    (hvw : t.views.vwOld ≤ t'.views.vwOld) (hrk : ∀ r, RkLe t' r → RkLe t r)
    (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t) : Good tid t mem := by
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

/-- The results of one step of a worker, with any promises. -/
structure SoloRes (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop where
  sinv : SInv oc.thread.st
  rinv : RInv oc.thread oc.mem
  promIn : PromIn tid oc.thread oc.mem
  back : Good tid oc.thread oc.mem → Good tid t mem ∧
    (t.prom ≠ [] → Ticketed t ∨ HasX t mem → oc.mem = mem)
  tkt : Ticketed t → Ticketed oc.thread ∧ tk oc.thread = tk t
  pre : ¬ Ticketed oc.thread → oc.thread.prom = t.prom ∧ oc.mem = mem

/-- A promise in the old set, kept by an erase of another timestamp. -/
theorem mem_erase_of_ne' {p : List Time} {a b : Time} (h : a ∈ p) (hne : a ≠ b) : a ∈ p.erase b :=
  (List.mem_erase_of_ne hne).mpr h

theorem xv_toNat (old : Val) (e : BitVec 32) (he : e.toNat = 1) :
    (xv old e).toNat = (old.toNat % 2 ^ 32 + 1) % 2 ^ 32 := X64SemStep.toNat_xv old e he

theorem tk_of_goto {u : Thread isa} {s : isa.State} {md : MachineData} {pc : Int64} (hst : u.st = goto s md pc) :
    tk u = (eax md).toNat := by
  unfold tk; rw [hst]

/-- **One step of a worker alone**, position by position. -/
theorem step_solo {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hxo : XL ≠ OL) (hxc : XL ≠ CL) (hoc : OL ≠ CL)
    (hS : SInv t.st) (hR : RInv t mem) (hP : PromIn tid t mem)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) : SoloRes tid t mem oc := by
  have hsinv := (step_sinv hS hs ho).1
  obtain ⟨hSt, p, hp, hpc⟩ := hS
  obtain ⟨-, hcoh, -, -⟩ := stepOne_dord Arch.tso hs ho
  have hPl := hP.le
  -- the facts shared by the steps that keep memory and promises
  have quiet : ∀ q ∈ tkPcs, oc.thread.st.st.2 = pcA q → rk p ≤ rk q → Q t mem oc →
      (Ticketed oc.thread ↔ Ticketed t) → (Ticketed t → tk oc.thread = tk t) → RInv oc.thread oc.mem →
      SoloRes tid t mem oc := by
    intro q hq hpq hr ⟨hm, hpr, hvw⟩ htk hk hRi
    refine ⟨hsinv, hRi, fun ts hts => by rw [hm]; exact hP ts (hpr ▸ hts), fun hg => ⟨?_, fun _ _ => hm⟩,
      fun h => ⟨htk.mpr h, hk h⟩, fun _ => ⟨hpr, hm⟩⟩
    rw [hm] at hg
    exact good_quiet hg hpr hcoh (Nat.le_of_eq hvw.symm)
      (fun r h => (rkLe_iff hp hpc r).mpr (Nat.le_trans hr ((rkLe_iff hq hpq r).mp h))) htk hk
  have tkd : ∀ q, q ∈ tkPcs → q ≠ 1 → q ≠ 2 → t.st.st.2 = pcA q → Ticketed t := fun q hq h1 h2 h =>
    ticketed_at h hq h1 h2
  have tka : ∀ {md : MachineData} {q : Nat}, oc.thread.st = goto t.st md (pcA q) → q ∈ tkPcs → q ≠ 1 → q ≠ 2 →
      Ticketed oc.thread := fun hst hq h1 h2 => ticketed_at (by rw [hst]) hq h1 h2
  have tke : ∀ {md : MachineData} {q : Nat}, oc.thread.st = goto t.st md (pcA q) → eax md = eax t.st.st.1 →
      tk oc.thread = tk t := fun hst he => by rw [tk_of_goto hst, he]; rfl
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `movl $1,%eax`
    obtain ⟨hq, md, -, he, hst⟩ := q1 hSt hs ho hpc
    have hnt : ¬ Ticketed oc.thread := fun h => h.2 (by rw [hst])
    exact quiet 2 (by decide) (by rw [hst]) (by decide) hq (iff_of_false hnt (fun h => h.1 hpc))
      (fun h => absurd hpc h.1) (RInv.goto hst (by decide) (show (eax md).toNat = 1 by rw [he]; rfl))
  · -- 2: `lock xaddl`
    obtain ⟨md, -, tr, old, he, hst, hrd, hw⟩ := q2 hSt hs ho hpc
    have h6 : (eax t.st.st.1).toNat = 1 := hR 2 (by decide) hpc
    have htk1 : Ticketed oc.thread := tka hst (by decide) (by decide) (by decide)
    have hntk : ¬ Ticketed t := fun h => h.2 hpc
    have hk : tk oc.thread = old.toNat % 2 ^ 32 := by rw [tk_of_goto hst, he, BitVec.toNat_setWidth]
    have hval := xv_toNat old _ h6
    have hrk4 : ∀ r, RkLe oc.thread r ↔ 2 ≤ r := rkLe_iff (p := 4) (by decide) (by rw [hst])
    have hRi : RInv oc.thread oc.mem := RInv.goto hst (j := 4) (by decide) trivial
    rcases hw with ⟨hm, hpr, hvw', hat⟩ | ⟨tsx, htsx, hgx, hcx, hm, hpr, hvw, htr, hat⟩
    · -- a fresh write: no `next` promise, no `owner` promise
      have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      refine ⟨hsinv, hRi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), fun hg => ?_,
        fun h => absurd h hntk, fun h => absurd htk1 h⟩
      -- every promise is to the counter
      have honly : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = CL := by
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
      have hnx : ∀ ts ∈ t.prom, ts ≠ tsx → ∀ w, mem.get? ts = some w → w.loc ≠ XL := by
        intro ts hts hne w hw hl
        rcases hg.loc ts (hin ts hts hne) w hw with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd ((hrk4 1).mp h) (by decide)
        · exact hxc (hl.symm.trans h)
        · exact hxo (hl.symm.trans h)
      have hxeq : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = XL → ts = tsx :=
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
        show w.val.toNat = (xv old (eax t.st.st.1)).toNat
        rw [hval, h1]
  · -- 4: `movl (owner),%ecx`
    obtain ⟨hq, md, -, he, ts, v, hc, hst, hrd, -, -⟩ := q4 hSt hs ho hpc
    exact quiet 5 (by decide) (by rw [hst]) (by decide) hq
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 4 (by decide) (by decide) (by decide) hpc))
      (fun _ => tke hst he) (RInv.goto hst (by decide) (show ORd oc.mem (ecx md).toNat by
        rw [hq.1]; exact ⟨ts, v, hrd, by rw [hc, BitVec.toNat_setWidth]⟩))
  · -- 5: `cmpl`
    obtain ⟨hq, md, -, he, hc, hz, hst, -⟩ := q5 hSt hs ho hpc
    have h5 : ORd mem (ecx t.st.st.1).toNat := hR 5 (by decide) hpc
    refine quiet 6 (by decide) (by rw [hst]) (by decide) hq
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 5 (by decide) (by decide) (by decide) hpc))
      (fun _ => tke hst he) (RInv.goto hst (by decide) (show md.status.zf = true → _ from fun hz' => ?_))
    have e := hz.mp hz'
    rw [hq.1, he, hc]; exact ⟨e ▸ h5, e⟩
  · -- 6: `jne`
    obtain ⟨hq, hst, -⟩ := q6 hSt hs ho hpc
    have h6 : RFact t.st.st.1 mem 6 := hR 6 (by decide) hpc
    have h1 := tkd 6 (by decide) (by decide) (by decide) hpc
    by_cases hz : t.st.st.1.status.zf = true
    · rw [ite_eq_left hz] at hst
      exact quiet 7 (by decide) (by rw [hst]) (by decide) hq (iff_of_true (tka hst (by decide) (by decide) (by decide)) h1)
        (fun _ => tke hst rfl) (RInv.goto hst (by decide) (by rw [hq.1]; exact h6 hz))
    · rw [ite_eq_right hz] at hst
      exact quiet 4 (by decide) (by rw [hst]) (by decide) hq (iff_of_true (tka hst (by decide) (by decide) (by decide)) h1)
        (fun _ => tke hst rfl) (RInv.goto hst (j := 4) (by decide) trivial)
  · -- 7: `movl (counter),%edx`
    obtain ⟨hq, md, -, he, hc, hst⟩ := q7 hSt hs ho hpc
    have h7 : ORd mem (eax t.st.st.1).toNat ∧ ecx t.st.st.1 = eax t.st.st.1 := hR 7 (by decide) hpc
    exact quiet 8 (by decide) (by rw [hst]) (by decide) hq
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 7 (by decide) (by decide) (by decide) hpc))
      (fun _ => tke hst he) (RInv.goto hst (by decide)
        (show ORd oc.mem (eax md).toNat ∧ ecx md = eax md by rw [hq.1, he, hc]; exact h7))
  · -- 8: `addl $1,%edx`
    obtain ⟨hq, md, -, he, hc, hst⟩ := q8 hSt hs ho hpc
    have h8 : ORd mem (eax t.st.st.1).toNat ∧ ecx t.st.st.1 = eax t.st.st.1 := hR 8 (by decide) hpc
    exact quiet 9 (by decide) (by rw [hst]) (by decide) hq
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 8 (by decide) (by decide) (by decide) hpc))
      (fun _ => tke hst he) (RInv.goto hst (by decide)
        (show ORd oc.mem (eax md).toNat ∧ ecx md = eax md by rw [hq.1, he, hc]; exact h8))
  · -- 9: `movl %edx,(counter)`
    obtain ⟨v, md, -, he, hc, hst, hw⟩ := q9 hSt hs ho hpc
    have h9 : ORd mem (eax t.st.st.1).toNat ∧ ecx t.st.st.1 = eax t.st.st.1 := hR 9 (by decide) hpc
    have h1 := tkd 9 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := tka hst (by decide) (by decide) (by decide)
    have hk : tk oc.thread = tk t := tke hst he
    have hrk10 : ∀ r, RkLe oc.thread r ↔ 6 ≤ r := rkLe_iff (p := 10) (by decide) (by rw [hst])
    have hRi : ∀ m', mem.Prefix m' → RInv oc.thread m' := fun m' hm' => RInv.goto hst (by decide)
      (show ORd m' (eax md).toNat ∧ ecx md = eax md by rw [he, hc]; exact ⟨h9.1.mono hm', h9.2⟩)
    rcases hw with ⟨hm, hpr, hvw'⟩ | ⟨tsc, htsc, hgc, hcc, -, hm, hpr, hvw⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
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
      have honly : ∀ ts ∈ t.prom, ts ≠ tsc → ∀ w, mem.get? ts = some w → w.loc = OL := by
        intro ts hts hne w hw
        rcases hg.loc ts (hin ts hts hne) w hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd ((hrk10 1).mp h) (by decide)
        · exact absurd ((hrk10 5).mp h) (by decide)
        · exact h
      have hne_o : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = OL → ts ≠ tsc :=
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
  · -- 10: `addl $1,%ecx`
    obtain ⟨hq, md, -, he, hc, hst⟩ := q10 hSt hs ho hpc
    have h10 : ORd mem (eax t.st.st.1).toNat ∧ ecx t.st.st.1 = eax t.st.st.1 := hR 10 (by decide) hpc
    exact quiet 11 (by decide) (by rw [hst]) (by decide) hq
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 10 (by decide) (by decide) (by decide) hpc))
      (fun _ => tke hst he) (RInv.goto hst (by decide)
        (show ORd oc.mem (eax md).toNat ∧ (ecx md).toNat = ((eax md).toNat + 1) % 2 ^ 32 by
          rw [hq.1, he, hc, h10.2]; exact ⟨h10.1, by simp [BitVec.toNat_add]⟩))
  · -- 11: `movl %ecx,(owner)`
    obtain ⟨hst, hw⟩ := q11 hSt hs ho hpc
    have h11 : ORd mem (eax t.st.st.1).toNat ∧ (ecx t.st.st.1).toNat = ((eax t.st.st.1).toNat + 1) % 2 ^ 32 :=
      hR 11 (by decide) hpc
    have h1 := tkd 11 (by decide) (by decide) (by decide) hpc
    have h2 : Ticketed oc.thread := tka hst (by decide) (by decide) (by decide)
    have hk : tk oc.thread = tk t := tke hst rfl
    have hrk12 : ∀ r, RkLe oc.thread r ↔ 8 ≤ r := rkLe_iff (p := 12) (by decide) (by rw [hst])
    have hRi : RInv oc.thread oc.mem := RInv.goto hst (j := 12) (by decide) trivial
    -- every remaining promise of the resulting thread is impossible
    have hdead : ∀ ts ∈ oc.thread.prom, ∀ w, oc.mem.get? ts = some w → Good tid oc.thread oc.mem → False := by
      intro ts hts w hw hg
      rcases hg.loc ts hts w hw with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact absurd ((hrk12 1).mp h) (by decide)
      · exact absurd ((hrk12 5).mp h) (by decide)
      · exact absurd ((hrk12 7).mp h) (by decide)
    rcases hw with ⟨hm, hpr, -⟩ | ⟨tso, htso, hgo, hco, hvo, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      have hnone : Good tid oc.thread oc.mem → ∀ ts ∈ t.prom, False := fun hg ts hts => by
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
      have hwo : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w →
          w = (⟨OL, BitVec.setWidth 128 (ecx t.st.st.1), tid⟩ : Msg) := fun ts hts w hw => by
        rw [honly ts hts, hgo] at hw; exact (Option.some.inj hw).symm
      refine ⟨⟨fun ts hts w hw => ?_, fun ts1 h1 ts2 h2 _ _ _ _ _ => by rw [honly ts1 h1, honly ts2 h2],
        fun ts hts w hw => ?_, fun ts hts w hw _ => ?_, fun ts hts w hw hl => ?_, fun ts hts w hw hl => ?_⟩,
        fun _ _ => hm⟩
      · rw [hwo ts hts w hw]; exact .inr (.inr ⟨rfl, (rkLe_iff (by decide) hpc 7).mpr (by decide)⟩)
      · rw [hwo ts hts w hw, honly ts hts]; exact hco
      · rw [honly ts hts]; exact hvo
      · rw [hwo ts hts w hw] at hl; exact absurd hl.symm hxo
      · rw [hwo ts hts w hw]
        refine ⟨fun _ => ⟨?_, h11.1⟩, fun h => absurd h1 h⟩
        show (BitVec.setWidth 128 (ecx t.st.st.1)).toNat = ((eax t.st.st.1).toNat + 1) % 2 ^ 32
        rw [BitVec.toNat_setWidth, h11.2]; omega
  · -- 12: `jmp done`
    obtain ⟨hq, hst, -⟩ := q12 hSt hs ho hpc
    exact quiet 14 (by decide) (by rw [hst]) (by decide) hq
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 12 (by decide) (by decide) (by decide) hpc))
      (fun _ => tke hst rfl) (RInv.goto hst (j := 14) (by decide) trivial)
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-! ## Along a run -/

theorem threadNPn_prefix {tid n : Nat} {p q : Thread isa × Memory} (h : ThreadNPn Arch.tso tid n p q) :
    p.2.Prefix q.2 := h.mem_prefix

section Run

variable {tid : Nat} (hxo : XL ≠ OL) (hxc : XL ≠ CL) (hoc : OL ≠ CL)

include hxo hxc hoc

/-- **A certifiable worker is `Good`.** -/
theorem good_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.tso tid n p q → q.1.prom = [] →
    SInv p.1.st → RInv p.1 p.2 → PromIn tid p.1 p.2 → Good tid p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _ _; exact good_nil hq
  | step hs _ ih =>
    intro hq hS hR hP
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have r := step_solo hxo hxc hoc hS hR hP hs ho
    exact (r.back (ih hq r.sinv r.rinv r.promIn)).1

theorem good_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.tso tid t mem fuel)
    (hS : SInv t.st) (hR : RInv t mem) (hP : PromIn tid t mem) : Good tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; good_of_run hxo hxc hoc hr hp hS hR hP

/-- **A ticketed worker, or one holding a `next` promise, certifies without
fresh writes** (stopping once its promise set is empty). -/
theorem nacert_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.tso tid n p q → q.1.prom = [] →
    SInv p.1.st → RInv p.1 p.2 → PromIn tid p.1 p.2 → (Ticketed p.1 ∨ HasX p.1 p.2) →
    ∃ t', ThreadNPn Arch.tso tid n p (t', p.2) ∧ t'.prom = [] := by
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
    have hT' : Ticketed oc.thread ∨ HasX oc.thread oc.mem := by
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

end Run

/-- A certification without fresh writes, against memory `mem` (unfolds to
`Sem.NACertG Arch.tso`). -/
def NACert (fuel tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∃ t', ThreadNPn Arch.tso tid fuel (t, mem) (t', mem) ∧ t'.prom = []

theorem nacert_of_certOkN {fuel tid : Nat} {t : Thread isa} {mem : Memory} (hxo : XL ≠ OL) (hxc : XL ≠ CL)
    (hoc : OL ≠ CL) (h : CertOkN Arch.tso tid t mem fuel) (hS : SInv t.st) (hR : RInv t mem)
    (hP : PromIn tid t mem) (hT : Ticketed t ∨ HasX t mem) : NACert fuel tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; nacert_of_run hxo hxc hoc hr hp hS hR hP hT

/-! ## Replay and enabledness -/

/-- **A step that keeps memory replays against a larger memory.** -/
theorem replay_tk {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.tso t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.tso t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  obtain ⟨hSt, p, hpp, hpc⟩ := hS
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, -, -, hex⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · obtain ⟨_, -, hex⟩ := exec_xadd _ (hSt.at (by decide) (by decide) hpc) hSt.dx
    exact replay_rmw_tso _ _ hp hb hs ho hm rfl hex
  · obtain ⟨_, -, hex⟩ := exec_ldo _ (hSt.at (by decide) (by decide) hpc) hSt.dO
    exact replay_load _ _ hp hb hs ho hm hex
  · obtain ⟨_, -, -, -, -, hex⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · exact replay_done _ _ hp hb hs ho hm (exec_jne _ (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨_, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact replay_load _ _ hp hb hs ho hm hex
  · obtain ⟨_, -, -, -, hex⟩ := exec_addd _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · obtain ⟨_, _, -, -, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact replay_store _ _ hp hb hs ho hm hex
  · obtain ⟨_, -, -, -, hex⟩ := exec_addc _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · exact replay_store _ _ hp hb hs ho hm (exec_rel _ (hSt.at (by decide) (by decide) hpc) hSt.dO)
  · exact replay_done _ _ hp hb hs ho hm (exec_jmp _ (hSt.at (by decide) (by decide) hpc))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem nacert_replay {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.tso tid n p q → p.2 = q.2 → SInv p.1.st → p.1.Bnd p.2.last →
    ∀ mem, p.2.Prefix mem → ThreadNPn Arch.tso tid n (p.1, mem) (q.1, mem) :=
  nacertG_replay SInv (fun hS hs ho => (step_sinv hS hs ho).1)
    (fun hS hb hp hs ho hm => replay_tk hS hb hp hs ho hm)

theorem NACert.replay {fuel tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    (h : NACert fuel tid t mem0) (hS : SInv t.st) (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) :
    NACert fuel tid t mem :=
  let ⟨t', hr, ht'⟩ := h; ⟨t', nacert_replay hr rfl hS hb mem hp, ht'⟩

/-- **A worker that is not at its end and either has no promise or certifies
without fresh writes can take an instruction step** (semantic machine). -/
theorem instrEnabledSem_of {fuel tid : Nat} {cfg : Config isa} {t : Thread isa}
    (ht : cfg.threads[tid]? = some t) (hS : SInv t.st) (h14 : t.st.st.2 ≠ pcA 14)
    (hb : t.Bnd cfg.mem.last) (hn : t.prom = [] ∨ NACert fuel tid t cfg.mem) :
    InstrEnabledSem Arch.tso fuel tid cfg := by
  have hnil : t.prom = [] → InstrEnabledSem Arch.tso fuel tid cfg := by
    intro hp0
    have fin := fun outs (oc : Outcome isa) =>
      instrEnabledSem_of_step (A := Arch.tso) (fuel := fuel) (outs := outs) (oc := oc) ht
    have fd : ∀ s, isa.exec t.st = some (.done s) → InstrEnabledSem Arch.tso fuel tid cfg := fun s hex =>
      let ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso tid hex (mem := cfg.mem); fin _ _ h1 h2 (h3.trans hp0)
    obtain ⟨hSt, p, hpp, hpc⟩ := hS
    simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
    rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨_, -, -, hex⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc); exact fd _ hex
    · obtain ⟨_, -, hex⟩ := exec_xadd _ (hSt.at (by decide) (by decide) hpc) hSt.dx
      obtain ⟨_, _, h1, h2, h3⟩ := en_rmw_tso Arch.tso tid rfl hp0 hb hex
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, -, hex⟩ := exec_ldo _ (hSt.at (by decide) (by decide) hpc) hSt.dO
      obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso tid hp0 hex (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, -, -, -, -, hex⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc); exact fd _ hex
    · exact fd _ (exec_jne _ (hSt.at (by decide) (by decide) hpc))
    · obtain ⟨_, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
      obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso tid hp0 hex (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, -, -, -, hex⟩ := exec_addd _ (hSt.at (by decide) (by decide) hpc); exact fd _ hex
    · obtain ⟨_, _, -, -, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
      obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso tid hp0 hb hex
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, -, -, -, hex⟩ := exec_addc _ (hSt.at (by decide) (by decide) hpc); exact fd _ hex
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso tid hp0 hb
        (exec_rel _ (hSt.at (by decide) (by decide) hpc) hSt.dO)
      exact fin _ _ h1 h2 h3
    · exact fd _ (exec_jmp _ (hSt.at (by decide) (by decide) hpc))
    · exact absurd hpc h14
  exact instrEnabledSem_of_nacertG ht hnil hn

end Kraken.Promising.Live.X64SemSolo
