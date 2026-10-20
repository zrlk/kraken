/-
**Stage 3: the x64 ticket-lock invariant on the
semantic machine** (`InvP`), with outstanding promises (`ticketlock3.kl`,
`tk3ImageV`, `Arch.tso`). An adapted copy of `LiveTicketInvP.lean`
(AArch64); the argument is unchanged.

`next` and `owner` messages in memory form chains of values: the `next`
messages have the distinct values `1, …, xc` (`xc` its final value), the
`owner` messages the distinct values `1, …, M` (`M` its final value). Each
`next` message of value `k + 1` belongs to the thread that *holds* ticket `k`
(`HoldsK`): it has taken it (`Ticketed`, `tk = k`) or reserved it by its
outstanding `next` promise. Each `owner` message of value `k + 1` belongs to
the holder of `k`, and stays an outstanding promise until its owner is past
its release (`Past`). A ticketed thread past its release has its `owner`
message in memory (`tdone`). Each thread satisfies the solo-run predicates of
`LiveX64SemSolo` (`Good`, and `NACert` when it is ticketed or holds a `next`
promise).

So an appended `next` message has value `xc + 1` (an atomic read of the last
one), and an appended `owner` message value `M + 1` (the holder of `M`
writes it: the holder of a smaller value already wrote, and a second
`owner` message of a thread would be a second promise or a dead one).

- `step_eff`: what an instruction step does to `next` and `owner`.
- `holdsK_inj`: tickets are unique; `xcN`: at most `N` tickets (pigeonhole).
- `inv_step`: `InvP` is kept by every semantic step, and `owner` either
  keeps its value and last write or grows by one.
- `inv_init`, `trace_invP`, `trace_o`.
-/
import Kraken.Promising.LiveX64SemSolo

namespace Kraken.Promising.Live.X64SemInv

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketX64Trees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SemShape Kraken.Promising.Live.X64SemShape
open Kraken.Promising.Live.X64SemStep Kraken.Promising.Live.X64SemSolo
open Kraken.Promising.Live.TicketX64Inv (XL OL CL Static Ticketed tk ticketed_at stepOne_end)
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV symTk)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk3ImageV).addrOf

/-! ## Holders and positions -/

/-- Past the `STLR`: positions 12 and 14. -/
def Past (u : Thread isa) : Prop := ¬ RkLe u 7

/-- Thread `u` holds ticket `k`: taken, or reserved by its `next` promise of
value `k + 1`. -/
def HoldsK (u : Thread isa) (mem : Memory) (k : Nat) : Prop :=
  (Ticketed u ∧ tk u = k) ∨
    (¬ Ticketed u ∧ ∃ ts ∈ u.prom, ∃ w, mem.get? ts = some w ∧ w.loc = XL ∧ w.val.toNat = k + 1)

/-- No promise of the thread is to location `l`. -/
def NoProm (l : Loc) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc ≠ l

/-- **What an instruction step does to `next` and `owner`.** -/
inductive Eff (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- Neither written; ticket, position class and non-counter promises kept. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := CL, val := v, tid }).1)
      (htk : Ticketed oc.thread ↔ Ticketed t) (hk : Ticketed t → tk oc.thread = tk t)
      (hpast : Past oc.thread ↔ Past t)
      (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc ≠ CL → ts ∈ oc.thread.prom)
  /-- `LDADDA`: a fresh write after an atomic read, or the fulfilment of the
  `next` promise. -/
  | tkt (h0 : ¬ Ticketed t) (h1 : Ticketed oc.thread) (hp1 : ¬ Past oc.thread)
      (hw : (∃ tr v, mem.read? (XL) tr = some v ∧ mem.atomic (XL) tid tr (mem.last + 1) = true ∧
          tk oc.thread = v.toNat % 2 ^ 32 ∧ NoProm (XL) t mem ∧ ∃ v' : Val,
          v'.toNat = (tk oc.thread + 1) % 2 ^ 32 ∧ oc.mem = (mem.append { loc := XL, val := v', tid }).1 ∧
          oc.thread.prom = t.prom) ∨
        (∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = XL ∧ w.val.toNat = (tk oc.thread + 1) % 2 ^ 32 ∧
          oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts))
  /-- `STLR`: a fresh write, or the fulfilment of the `owner` promise. -/
  | rel (h0 : Ticketed t) (h1 : Ticketed oc.thread) (hk : tk oc.thread = tk t) (hord : ORd mem (tk t))
      (hp0 : ¬ Past t)
      (hp1 : Past oc.thread)
      (hw : (∃ v' : Val, v'.toNat = (tk t + 1) % 2 ^ 32 ∧ oc.mem = (mem.append { loc := OL, val := v', tid }).1 ∧
          oc.thread.prom = t.prom ∧ NoProm (OL) t mem) ∨
        (∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = OL ∧ w.val.toNat = (tk t + 1) % 2 ^ 32 ∧
          oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts))

theorem past_iff {u : Thread isa} {p : Nat} (hp : p ∈ tkPcs) (h : u.st.st.2 = pcA p) : Past u ↔ ¬ rk p ≤ 7 :=
  not_congr (rkLe_iff hp h 7)

/-- **What an instruction step does to `next` and `owner`**, position by
position (the post-thread `Good`, from its certification, excludes the dead
promises of a fresh `lock xaddl` or release). -/
theorem step_eff {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hxo : XL ≠ OL) (hxc : XL ≠ CL) (hoc : OL ≠ CL)
    (hS : SInv t.st) (hR : RInv t mem) (hP : PromIn tid t mem)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)
    (hg : Good tid oc.thread oc.mem) : Eff tid t mem oc := by
  obtain ⟨hSt, p, hp, hpc⟩ := hS
  have hPl := hP.le
  have Q' : ∀ {md : MachineData} {q : Nat}, q ∈ tkPcs → oc.thread.st = goto t.st md (pcA q) →
      (¬ rk q ≤ 7 ↔ ¬ rk p ≤ 7) → (Ticketed oc.thread ↔ Ticketed t) → (Ticketed t → eax md = eax t.st.st.1) →
      X64SemStep.Q t mem oc → Eff tid t mem oc :=
    fun hq hst hr htk hk ⟨hm, hpr, _⟩ => .quiet (.inl hm) htk (fun h => by rw [tk_of_goto hst, hk h]; rfl)
      ((past_iff hq (by rw [hst])).trans (hr.trans (past_iff hp hpc).symm)) (fun ts hts _ _ _ => hpr ▸ hts)
  have tkd : ∀ q, q ∈ tkPcs → q ≠ 1 → q ≠ 2 → t.st.st.2 = pcA q → Ticketed t := fun q hq h1 h2 h =>
    ticketed_at h hq h1 h2
  have tka : ∀ {md : MachineData} {q : Nat}, oc.thread.st = goto t.st md (pcA q) → q ∈ tkPcs → q ≠ 1 → q ≠ 2 →
      Ticketed oc.thread := fun hst hq h1 h2 => ticketed_at (by rw [hst]) hq h1 h2
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hq, md, -, -, hst⟩ := q1 hSt hs ho hpc
    exact Q' (q := 2) (by decide) hst (by decide) (iff_of_false (fun h => h.2 (by rw [hst])) (fun h => h.1 hpc))
      (fun h => absurd hpc h.1) hq
  · obtain ⟨md, -, tr, old, he, hst, hrd, hw⟩ := q2 hSt hs ho hpc
    have h6 : (eax t.st.st.1).toNat = 1 := hR 2 (by decide) hpc
    have htk1 : Ticketed oc.thread := tka hst (by decide) (by decide) (by decide)
    have hk : tk oc.thread = old.toNat % 2 ^ 32 := by rw [tk_of_goto hst, he, BitVec.toNat_setWidth]
    have hval : (xv old (eax t.st.st.1)).toNat = (tk oc.thread + 1) % 2 ^ 32 := by
      rw [hk]; exact xv_toNat old _ h6
    have hp4 : ¬ RkLe oc.thread 1 := fun h => absurd ((rkLe_iff (p := 4) (by decide) (by rw [hst]) 1).mp h) (by decide)
    refine .tkt (fun h => h.2 hpc) htk1 (fun h => h ((rkLe_iff (p := 4) (by decide) (by rw [hst]) 7).mpr (by decide))) ?_
    rcases hw with ⟨hm, hpr, -, hat⟩ | ⟨ts, hts, hgw, -, hm, hpr, -, -, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      refine .inl ⟨tr, old, hrd, hat, hk, fun ts hts w hw hl => ?_, _, hval, hm, hpr'⟩
      have hw' : oc.mem.get? ts = some w := by rw [hm]; rw [(Memory.Prefix.append _ _).get? (hPl ts hts)]; exact hw
      rcases hg.loc ts (hpr' ▸ hts) w hw' with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact hp4 h
      · exact hxc (hl.symm.trans h)
      · exact hxo (hl.symm.trans h)
    · exact .inr ⟨ts, hts, _, hgw, rfl, hval, hm, hpr⟩
  · obtain ⟨hq, md, -, he, -, -, -, hst, -⟩ := q4 hSt hs ho hpc
    exact Q' (q := 5) (by decide) hst (by decide)
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 4 (by decide) (by decide) (by decide) hpc))
      (fun _ => he) hq
  · obtain ⟨hq, md, -, he, -, -, hst, -⟩ := q5 hSt hs ho hpc
    exact Q' (q := 6) (by decide) hst (by decide)
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 5 (by decide) (by decide) (by decide) hpc))
      (fun _ => he) hq
  · obtain ⟨hq, hst, -⟩ := q6 hSt hs ho hpc
    have h1 := tkd 6 (by decide) (by decide) (by decide) hpc
    by_cases hz : t.st.st.1.status.zf = true
    · rw [ite_eq_left hz] at hst
      exact Q' (q := 7) (by decide) hst (by decide) (iff_of_true (tka hst (by decide) (by decide) (by decide)) h1)
        (fun _ => rfl) hq
    · rw [ite_eq_right hz] at hst
      exact Q' (q := 4) (by decide) hst (by decide) (iff_of_true (tka hst (by decide) (by decide) (by decide)) h1)
        (fun _ => rfl) hq
  · obtain ⟨hq, md, -, he, -, hst⟩ := q7 hSt hs ho hpc
    exact Q' (q := 8) (by decide) hst (by decide)
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 7 (by decide) (by decide) (by decide) hpc))
      (fun _ => he) hq
  · obtain ⟨hq, md, -, he, -, hst⟩ := q8 hSt hs ho hpc
    exact Q' (q := 9) (by decide) hst (by decide)
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 8 (by decide) (by decide) (by decide) hpc))
      (fun _ => he) hq
  · obtain ⟨v, md, -, he, -, hst, hw⟩ := q9 hSt hs ho hpc
    have htk := iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 9 (by decide) (by decide) (by decide) hpc)
    have hpast : Past oc.thread ↔ Past t :=
      (past_iff (p := 10) (by decide) (by rw [hst])).trans ((by decide : (¬ rk 10 ≤ 7 ↔ ¬ rk 9 ≤ 7)).trans
        (past_iff (by decide) hpc).symm)
    have hk : Ticketed t → tk oc.thread = tk t := fun _ => by rw [tk_of_goto hst, he]; rfl
    rcases hw with ⟨hm, hpr, -⟩ | ⟨ts, hts, hgw, -, -, hm, hpr, -⟩
    · exact .quiet (.inr ⟨_, hm⟩) htk hk hpast (fun ts hts _ _ _ => by rw [hpr, erase_fresh hPl]; exact hts)
    · refine .quiet (.inl hm) htk hk hpast fun ts' hts' w hw hl => ?_
      rw [hpr]; refine mem_erase_of_ne' hts' fun e => hl ?_
      subst e; rw [hgw] at hw; cases hw; rfl
  · obtain ⟨hq, md, -, he, -, hst⟩ := q10 hSt hs ho hpc
    exact Q' (q := 11) (by decide) hst (by decide)
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 10 (by decide) (by decide) (by decide) hpc))
      (fun _ => he) hq
  · obtain ⟨hst, hw⟩ := q11 hSt hs ho hpc
    have h11 : ORd mem (eax t.st.st.1).toNat ∧ (ecx t.st.st.1).toNat = ((eax t.st.st.1).toNat + 1) % 2 ^ 32 :=
      hR 11 (by decide) hpc
    have h0 := tkd 11 (by decide) (by decide) (by decide) hpc
    have h1 : Ticketed oc.thread := tka hst (by decide) (by decide) (by decide)
    have hk : tk oc.thread = tk t := by rw [tk_of_goto hst]; rfl
    have hval : (BitVec.setWidth 128 (ecx t.st.st.1)).toNat = (tk t + 1) % 2 ^ 32 := by
      rw [BitVec.toNat_setWidth, h11.2]; unfold tk; omega
    have h12 : ¬ RkLe oc.thread 7 := fun h => absurd ((rkLe_iff (p := 12) (by decide) (by rw [hst]) 7).mp h) (by decide)
    refine .rel h0 h1 hk h11.1 (fun h => h ((rkLe_iff (by decide) hpc 7).mpr (by decide))) h12 ?_
    rcases hw with ⟨hm, hpr, -⟩ | ⟨ts, hts, hgw, -, -, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      refine .inl ⟨_, hval, hm, hpr', fun ts hts w hw hl => ?_⟩
      have hw' : oc.mem.get? ts = some w := by rw [hm]; rw [(Memory.Prefix.append _ _).get? (hPl ts hts)]; exact hw
      rcases hg.loc ts (hpr' ▸ hts) w hw' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact hxo (h.symm.trans hl)
      · exact hoc (hl.symm.trans h)
      · exact h12 h
    · exact .inr ⟨ts, hts, _, hgw, rfl, hval, hm, hpr⟩
  · obtain ⟨hq, hst, -⟩ := q12 hSt hs ho hpc
    exact Q' (q := 14) (by decide) hst (by decide)
      (iff_of_true (tka hst (by decide) (by decide) (by decide)) (tkd 12 (by decide) (by decide) (by decide) hpc))
      (fun _ => rfl) hq
  · rw [stepOne_end hSt hpc] at hs; cases hs


/-! ## Small facts -/

theorem tk_lt (u : Thread isa) : tk u < 2 ^ 32 := (eax u.st.st.1).isLt

theorem read?_of_get? {mem : Memory} {ts : Time} {w : Msg} (hw : mem.get? ts = some w) :
    mem.read? w.loc ts = some w.val := Kraken.Promising.SLR.read?_of_get?' hw

theorem atomic_append_last (mem : Memory) (w : Msg) (l : Loc) (tid : Nat) {tr : Time} (htr : tr ≤ mem.last) :
    (mem.append w).1.atomic l tid tr (mem.last + 1) = mem.atomic l tid tr (mem.last + 1) :=
  atomic_append_of_le mem w l tid htr

theorem rk1 {u : Thread isa} (hS : SInv u.st) (h : RkLe u 1) : ¬ Ticketed u := by
  obtain ⟨-, i, hi, hpc⟩ := hS
  have key : ∀ i ∈ tkPcs, rk i ≤ 1 → i = 1 ∨ i = 2 := by decide
  intro hT
  rcases key i hi (h i hi hpc) with rfl | rfl
  · exact hT.1 hpc
  · exact hT.2 hpc

theorem not_past {u : Thread isa} (hS : SInv u.st) (h : ¬ Ticketed u) : ¬ Past u := by
  obtain ⟨-, i, hi, hpc⟩ := hS
  intro hp
  apply hp
  rw [rkLe_iff hi hpc]
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | exact absurd (ticketed_at hpc (by decide) (by decide) (by decide)) h

theorem HoldsK.keep {tid k : Nat} {t t' : Thread isa} {mem mem' : Memory} (h : HoldsK t mem k)
    (hP : PromIn tid t mem) (hp : mem.Prefix mem') (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = XL → ts ∈ t'.prom) : HoldsK t' mem' k := by
  rcases h with ⟨a, b⟩ | ⟨a, ts, hts, w, hw, hl, hv⟩
  · exact .inl ⟨htk.mpr a, (hk a).trans b⟩
  · exact .inr ⟨fun e => a (htk.mp e), ts, hkeep ts hts w hw hl, w, by rw [hP.get hp hts]; exact hw, hl, hv⟩

/-! ## The invariant -/

/-- The final value of a word (a notation, so that `omega` sees one atom). -/
scoped notation:max "fv " mem:max a:max => BitVec.toNat (Memory.finalVal mem a)

/-- The per-thread part of the invariant. -/
structure TS (fuel : Nat) (i : Nat) (u : Thread isa) (mem : Memory) : Prop where
  sinv : SInv u.st
  rinv : RInv u mem
  promIn : PromIn i u mem
  good : Good i u mem
  nac : Ticketed u ∨ HasX u mem → NACert fuel i u mem

theorem TS.mono {fuel : Nat} {i : Nat} {u : Thread isa} {mem mem' : Memory}
    (hT : TS fuel i u mem) (hb : u.Bnd mem.last) (hp : mem.Prefix mem') : TS fuel i u mem' :=
  ⟨hT.sinv, hT.rinv.mono hp, hT.promIn.mono hp, hT.good.mono hp hT.promIn, fun hh =>
    (hT.nac (hh.imp_right fun ⟨ts, hts, w, hw, hl⟩ => ⟨ts, hts, w, by rw [← hT.promIn.get hp hts]; exact hw, hl⟩)).replay
      hT.sinv hb hp⟩

/-- **The ticket-lock invariant with promises.** -/
structure InvP (fuel N : Nat) (cfg : Config isa) : Prop where
  size : cfg.threads.size = N
  N32 : N + 1 < 2 ^ 32
  hxo : XL ≠ OL
  hxc : XL ≠ CL
  hoc : OL ≠ CL
  bnd : cfg.Bnd
  xv : ∀ ts v, cfg.mem.read? (XL) ts = some v → v.toNat ≤ fv cfg.mem XL
  ov : ∀ ts v, cfg.mem.read? (OL) ts = some v → v.toNat ≤ fv cfg.mem OL
  xinj : ∀ ts1 ts2 w1 w2, cfg.mem.get? ts1 = some w1 → cfg.mem.get? ts2 = some w2 → w1.loc = XL → w2.loc = XL →
    w1.val.toNat = w2.val.toNat → ts1 = ts2
  oinj : ∀ ts1 ts2 w1 w2, cfg.mem.get? ts1 = some w1 → cfg.mem.get? ts2 = some w2 → w1.loc = OL → w2.loc = OL →
    w1.val.toNat = w2.val.toNat → ts1 = ts2
  xsurj : ∀ k < fv cfg.mem XL, ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = XL ∧ w.val.toNat = k + 1
  osurj : ∀ k < fv cfg.mem OL, ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = OL ∧ w.val.toNat = k + 1
  xheld : ∀ ts w, cfg.mem.get? ts = some w → w.loc = XL →
    ∃ k u, w.val.toNat = k + 1 ∧ cfg.threads[w.tid]? = some u ∧ HoldsK u cfg.mem k
  oheld : ∀ ts w, cfg.mem.get? ts = some w → w.loc = OL →
    ∃ k u, w.val.toNat = k + 1 ∧ cfg.threads[w.tid]? = some u ∧ HoldsK u cfg.mem k ∧ (¬ Past u → ts ∈ u.prom)
  tx : ∀ (i : Nat) u, cfg.threads[i]? = some u → Ticketed u →
    ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = XL ∧ w.tid = i ∧ w.val.toNat = tk u + 1
  tdone : ∀ (i : Nat) u, cfg.threads[i]? = some u → Ticketed u → Past u →
    ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = OL ∧ w.val.toNat = tk u + 1
  thr : ∀ (i : Nat) u, cfg.threads[i]? = some u → TS fuel i u cfg.mem

section Facts

variable {fuel N : Nat} {cfg : Config isa} (h : InvP fuel N cfg)
include h

theorem InvP.xv' {ts : Time} {w : Msg} (hw : cfg.mem.get? ts = some w) (hl : w.loc = XL) :
    w.val.toNat ≤ fv cfg.mem XL := h.xv ts w.val (hl ▸ read?_of_get? hw)

theorem InvP.ov' {ts : Time} {w : Msg} (hw : cfg.mem.get? ts = some w) (hl : w.loc = OL) :
    w.val.toNat ≤ fv cfg.mem OL := h.ov ts w.val (hl ▸ read?_of_get? hw)

theorem InvP.holdsK_fun {i k1 k2 : Nat} {u : Thread isa} (hu : cfg.threads[i]? = some u)
    (h1 : HoldsK u cfg.mem k1) (h2 : HoldsK u cfg.mem k2) : k1 = k2 := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, ts1, h1, w1, hw1, hl1, hv1⟩ <;>
    rcases h2 with ⟨a2, b2⟩ | ⟨a2, ts2, h2, w2, hw2, hl2, hv2⟩
  · omega
  · exact absurd a1 a2
  · exact absurd a2 a1
  · have := (h.thr i u hu).good.uniq ts1 h1 ts2 h2 w1 w2 hw1 hw2 (hl1.trans hl2.symm)
    subst this; rw [hw1] at hw2; cases hw2; omega

theorem InvP.holdsK_msg {i k : Nat} {u : Thread isa} (hu : cfg.threads[i]? = some u) (hk : HoldsK u cfg.mem k) :
    ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = XL ∧ w.tid = i ∧ w.val.toNat = k + 1 := by
  rcases hk with ⟨a, rfl⟩ | ⟨-, ts, hts, w, hw, hl, hv⟩
  · exact h.tx i u hu a
  · obtain ⟨w', hw', hid⟩ := (h.thr i u hu).promIn ts hts
    rw [hw] at hw'; cases hw'
    exact ⟨ts, w, hw, hl, hid, hv⟩

/-- **Tickets are unique.** -/
theorem InvP.holdsK_inj {i j k : Nat} {u u' : Thread isa} (hu : cfg.threads[i]? = some u)
    (hu' : cfg.threads[j]? = some u') (h1 : HoldsK u cfg.mem k) (h2 : HoldsK u' cfg.mem k) : i = j := by
  obtain ⟨ts1, w1, hw1, hl1, hid1, hv1⟩ := h.holdsK_msg hu h1
  obtain ⟨ts2, w2, hw2, hl2, hid2, hv2⟩ := h.holdsK_msg hu' h2
  have := h.xinj ts1 ts2 w1 w2 hw1 hw2 hl1 hl2 (hv1.trans hv2.symm)
  subst this; rw [hw1] at hw2; cases hw2; exact hid1.symm.trans hid2

/-- **At most `N` tickets** (pigeonhole). -/
theorem InvP.xcN : fv cfg.mem XL ≤ N := by
  have hch : ∀ k, k < fv cfg.mem XL → ∃ i, i < N ∧ ∃ u, cfg.threads[i]? = some u ∧ HoldsK u cfg.mem k :=
    fun k hk => by
      obtain ⟨ts, w, hw, hl, hv⟩ := h.xsurj k hk
      obtain ⟨k', u, hv', hu, hh⟩ := h.xheld ts w hw hl
      obtain rfl : k' = k := by omega
      exact ⟨w.tid, h.size ▸ lt_size_of_get? hu, u, hu, hh⟩
  obtain ⟨g, hg⟩ := Classical.skolem.mp (fun k => (Classical.em (k < fv cfg.mem XL)).elim
    (fun hk => (hch k hk).imp fun i hi => fun _ => hi) (fun hk => ⟨0, fun h => absurd h hk⟩))
  exact SpinCommon.pigeon N _ g (fun k hk => (hg k hk).1) (fun i j hi hj e => by
    obtain ⟨-, u, hu, h1⟩ := hg i hi
    obtain ⟨-, u', hu', h2⟩ := hg j hj
    rw [e] at hu; rw [hu] at hu'; cases hu'
    exact h.holdsK_fun hu h1 h2)

theorem InvP.tk_lt {i : Nat} {u : Thread isa} (hu : cfg.threads[i]? = some u) (hk : Ticketed u) :
    tk u + 1 ≤ fv cfg.mem XL := by
  obtain ⟨ts, w, hw, hl, -, hv⟩ := h.tx i u hu hk
  have := h.xv' hw hl; omega

theorem InvP.ord_le {k : Nat} (hk : ORd cfg.mem k) : k ≤ fv cfg.mem OL := by
  obtain ⟨tr, v, hr, hv⟩ := hk
  have := h.ov tr v hr; have := Nat.mod_le v.toNat (2 ^ 32); omega

end Facts

/-! ## Preservation -/

/-- The chain facts of one location across a step. -/
theorem chain {mem mem' : Memory} {l : Loc} {tid : Nat}
    (hm : mem' = mem ∨ ∃ w : Msg, w.tid = tid ∧ mem' = (mem.append w).1 ∧
      (w.loc = l → w.val.toNat = (mem.finalVal l).toNat + 1))
    (hv : ∀ ts v, mem.read? l ts = some v → v.toNat ≤ (mem.finalVal l).toNat)
    (hinj : ∀ ts1 ts2 w1 w2, mem.get? ts1 = some w1 → mem.get? ts2 = some w2 → w1.loc = l → w2.loc = l →
      w1.val.toNat = w2.val.toNat → ts1 = ts2)
    (hsurj : ∀ k < (mem.finalVal l).toNat, ∃ ts w, mem.get? ts = some w ∧ w.loc = l ∧ w.val.toNat = k + 1) :
    (∀ ts v, mem'.read? l ts = some v → v.toNat ≤ (mem'.finalVal l).toNat) ∧
    (∀ ts1 ts2 w1 w2, mem'.get? ts1 = some w1 → mem'.get? ts2 = some w2 → w1.loc = l → w2.loc = l →
      w1.val.toNat = w2.val.toNat → ts1 = ts2) ∧
    (∀ k < (mem'.finalVal l).toNat, ∃ ts w, mem'.get? ts = some w ∧ w.loc = l ∧ w.val.toNat = k + 1) ∧
    (∀ ts w, mem'.get? ts = some w → w.loc = l → mem.get? ts = some w ∨ w.tid = tid) ∧
    (((mem'.finalVal l).toNat = (mem.finalVal l).toNat ∧ mem'.lastWrite l = mem.lastWrite l) ∨
      (mem'.finalVal l).toNat = (mem.finalVal l).toNat + 1) := by
  rcases hm with rfl | ⟨w, hwt, rfl, hwv⟩
  · exact ⟨hv, hinj, hsurj, fun ts w h _ => .inl h, .inl ⟨rfl, rfl⟩⟩
  have hg : ∀ {ts w'}, mem.get? ts = some w' → (mem.append w).1.get? ts = some w' := fun h => by
    rw [(Memory.Prefix.append _ _).get? (mem.last_le_of_get?_eq_some h)]; exact h
  by_cases hl : w.loc = l
  · have hf : ((mem.append w).1.finalVal l).toNat = (mem.finalVal l).toNat + 1 := by
      rw [finalVal_append, ite_eq_left hl]; exact hwv hl
    have hw1 := hwv hl
    refine ⟨fun ts v hr => ?_, fun ts1 ts2 w1 w2 h1 h2 l1 l2 e => ?_, fun k hk => ?_, fun ts w' h' _ => ?_, .inr hf⟩
    · rw [hf]; rcases read?_append_eq_some mem w hr with hr | ⟨-, -, rfl⟩
      · have := hv ts v hr; omega
      · omega
    · rcases mem.get?_append_eq_some w h1 with ⟨a1, h1⟩ | ⟨a1, e1⟩ <;>
        rcases mem.get?_append_eq_some w h2 with ⟨a2, h2⟩ | ⟨a2, e2⟩
      · exact hinj ts1 ts2 w1 w2 h1 h2 l1 l2 e
      · have : w2.val.toNat = (mem.finalVal l).toNat + 1 := by subst e2; exact hw1
        have := hv ts1 w1.val (l1 ▸ read?_of_get? h1); omega
      · have : w1.val.toNat = (mem.finalVal l).toNat + 1 := by subst e1; exact hw1
        have := hv ts2 w2.val (l2 ▸ read?_of_get? h2); omega
      · exact a1.trans a2.symm
    · rw [hf] at hk
      by_cases hk' : k < (mem.finalVal l).toNat
      · obtain ⟨ts, w', h1, h2, h3⟩ := hsurj k hk'
        exact ⟨ts, w', hg h1, h2, h3⟩
      · exact ⟨mem.last + 1, w, Memory.get?_append_last mem w, hl, by omega⟩
    · rcases mem.get?_append_eq_some w h' with ⟨-, h⟩ | ⟨-, rfl⟩
      · exact .inl h
      · exact .inr hwt
  · obtain ⟨a1, a2, a3, a4⟩ := mem_frame mem w hl
    refine ⟨fun ts v hr => by rw [a1]; exact hv ts v (a3 ts v hr),
      fun ts1 ts2 w1 w2 h1 h2 l1 l2 e => hinj ts1 ts2 w1 w2 (a4 ts1 w1 h1 l1) (a4 ts2 w2 h2 l2) l1 l2 e,
      fun k hk => ?_, fun ts w' h' hl' => .inl (a4 ts w' h' hl'), .inl ⟨by rw [a1], a2⟩⟩
    rw [a1] at hk
    obtain ⟨ts, w', h1, h2, h3⟩ := hsurj k hk
    exact ⟨ts, w', hg h1, h2, h3⟩

section Pres

variable {fuel N : Nat} {cfg : Config isa} {tid : Nat} {t : Thread isa}
  (h : InvP fuel N cfg) (ht : cfg.threads[tid]? = some t)
include h ht

/-- **The invariant after a step of `tid`**, from the facts about `tid`. -/
theorem build {t' : Thread isa} {mem' : Memory}
    (hpre : cfg.mem.Prefix mem') (hb : (cfg.withThread tid t' mem').Bnd)
    (hm : mem' = cfg.mem ∨ ∃ w : Msg, w.tid = tid ∧ mem' = (cfg.mem.append w).1 ∧
      (w.loc = XL → w.val.toNat = fv cfg.mem XL + 1) ∧ (w.loc = OL → w.val.toNat = fv cfg.mem OL + 1))
    (hT : TS fuel tid t' mem')
    (hxt : ∀ ts w, mem'.get? ts = some w → w.loc = XL → w.tid = tid → ∃ k, w.val.toNat = k + 1 ∧ HoldsK t' mem' k)
    (hot : ∀ ts w, mem'.get? ts = some w → w.loc = OL → w.tid = tid →
      ∃ k, w.val.toNat = k + 1 ∧ HoldsK t' mem' k ∧ (¬ Past t' → ts ∈ t'.prom))
    (htx : Ticketed t' → ∃ ts w, mem'.get? ts = some w ∧ w.loc = XL ∧ w.tid = tid ∧ w.val.toNat = tk t' + 1)
    (htd : Ticketed t' → Past t' → ∃ ts w, mem'.get? ts = some w ∧ w.loc = OL ∧ w.val.toNat = tk t' + 1) :
    InvP fuel N (cfg.withThread tid t' mem') ∧
      ((fv mem' OL = fv cfg.mem OL ∧ mem'.lastWrite (OL) = cfg.mem.lastWrite (OL)) ∨ fv mem' OL = fv cfg.mem OL + 1) := by
  obtain ⟨x1, x2, x3, x4, -⟩ := chain (l := XL) (tid := tid)
    (hm.imp_right fun ⟨w, a, b, d, _⟩ => ⟨w, a, b, d⟩) h.xv h.xinj h.xsurj
  obtain ⟨o1, o2, o3, o4, o5⟩ := chain (l := OL) (tid := tid)
    (hm.imp_right fun ⟨w, a, b, _, e⟩ => ⟨w, a, b, e⟩) h.ov h.oinj h.osurj
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → mem'.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  have hK : ∀ {j k u}, cfg.threads[j]? = some u → HoldsK u cfg.mem k → HoldsK u mem' k := fun hu hh =>
    hh.keep (h.thr _ _ hu).promIn hpre Iff.rfl (fun _ => rfl) (fun ts hts _ _ _ => hts)
  refine ⟨⟨by simp [Config.withThread, h.size], h.N32, h.hxo, h.hxc, h.hoc, hb, x1, o1, x2, o2, x3, o3,
    fun ts w hw hl => ?_, fun ts w hw hl => ?_, fun i u hu hk => ?_, fun i u hu hk hp => ?_, fun i u hu => ?_⟩, o5⟩
  · by_cases e : w.tid = tid
    · obtain ⟨k, hk, hh⟩ := hxt ts w hw hl e
      exact ⟨k, t', hk, by rw [e]; exact wt_tid ht, hh⟩
    · rcases x4 ts w hw hl with hw0 | e'
      · obtain ⟨k, u, hk, hu, hh⟩ := h.xheld ts w hw0 hl
        exact ⟨k, u, hk, by rw [wt_ne ht e]; exact hu, hK hu hh⟩
      · exact absurd e' e
  · by_cases e : w.tid = tid
    · obtain ⟨k, hk, hh, hp⟩ := hot ts w hw hl e
      exact ⟨k, t', hk, by rw [e]; exact wt_tid ht, hh, hp⟩
    · rcases o4 ts w hw hl with hw0 | e'
      · obtain ⟨k, u, hk, hu, hh, hp⟩ := h.oheld ts w hw0 hl
        exact ⟨k, u, hk, by rw [wt_ne ht e]; exact hu, hK hu hh, hp⟩
      · exact absurd e' e
  · rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact htx hk
    · obtain ⟨ts, w, hw, hl, hid, hv⟩ := h.tx i u hu hk
      exact ⟨ts, w, hg hw, hl, hid, hv⟩
  · rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact htd hk hp
    · obtain ⟨ts, w, hw, hl, hv⟩ := h.tdone i u hu hk hp
      exact ⟨ts, w, hg hw, hl, hv⟩
  · rcases wt_get ht hu with ⟨rfl, rfl⟩ | ⟨-, hu⟩
    · exact hT
    · exact (h.thr i u hu).mono (h.bnd i u hu) hpre

/-- **A promise step keeps the invariant.** -/
theorem inv_prom {w : Msg} (hwt : w.tid = tid)
    (hc : CertOkN Arch.tso tid (promThread t cfg.mem w) (cfg.mem.append w).1 fuel)
    (hb : (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1).Bnd) :
    InvP fuel N (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1) ∧
      ((fv (cfg.mem.append w).1 OL = fv cfg.mem OL ∧
        (cfg.mem.append w).1.lastWrite (OL) = cfg.mem.lastWrite (OL)) ∨
        fv (cfg.mem.append w).1 OL = fv cfg.mem OL + 1) := by
  have hT0 := h.thr tid t ht
  have hpre : cfg.mem.Prefix (cfg.mem.append w).1 := Memory.Prefix.append _ _
  have hPl := hT0.promIn.le
  have hxN := h.xcN; have hN32 := h.N32
  have hS' : SInv (promThread t cfg.mem w).st := hT0.sinv
  have hR' : RInv (promThread t cfg.mem w) (cfg.mem.append w).1 :=
    hT0.rinv.mono hpre
  have hmem : ∀ ts, ts ∈ (promThread t cfg.mem w).prom ↔ ts ∈ t.prom ∨ ts = cfg.mem.last + 1 := fun ts => by
    simp only [List.mem_append, List.mem_singleton]; rfl
  have hw0 : (cfg.mem.append w).1.get? (cfg.mem.last + 1) = some w := Memory.get?_append_last _ _
  have hP' : PromIn tid (promThread t cfg.mem w) (cfg.mem.append w).1 := by
    intro ts hts
    rcases (hmem ts).mp hts with hts | rfl
    · rw [hT0.promIn.get hpre hts]; exact hT0.promIn ts hts
    · exact ⟨w, hw0, hwt⟩
  have hG := good_of_certOkN h.hxo h.hxc h.hoc hc hS' hR' hP'
  have hT' : TS fuel tid (promThread t cfg.mem w) (cfg.mem.append w).1 :=
    ⟨hS', hR', hP', hG, nacert_of_certOkN h.hxo h.hxc h.hoc hc hS' hR' hP'⟩
  have hnew : cfg.mem.last + 1 ∈ (promThread t cfg.mem w).prom := (hmem _).mpr (.inr rfl)
  have hold : ∀ ts ∈ t.prom, ts ∈ (promThread t cfg.mem w).prom := fun ts hts => (hmem ts).mpr (.inl hts)
  have hK : ∀ k, HoldsK t cfg.mem k → HoldsK (promThread t cfg.mem w) (cfg.mem.append w).1 k := fun k hh =>
    hh.keep hT0.promIn hpre Iff.rfl (fun _ => rfl) (fun ts hts _ _ _ => hold ts hts)
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → (cfg.mem.append w).1.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  -- the old messages of `tid`
  have oldx : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = XL → w'.tid = tid →
      ∃ k, w'.val.toNat = k + 1 ∧ HoldsK (promThread t cfg.mem w) (cfg.mem.append w).1 k := by
    intro ts w' hw hl e
    obtain ⟨k, u, hk, hu, hh⟩ := h.xheld ts w' hw hl
    rw [e, ht] at hu; cases hu
    exact ⟨k, hk, hK k hh⟩
  have oldo : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = OL → w'.tid = tid →
      ∃ k, w'.val.toNat = k + 1 ∧ HoldsK (promThread t cfg.mem w) (cfg.mem.append w).1 k ∧
        (¬ Past (promThread t cfg.mem w) → ts ∈ (promThread t cfg.mem w).prom) := by
    intro ts w' hw hl e
    obtain ⟨k, u, hk, hu, hh, hp⟩ := h.oheld ts w' hw hl
    rw [e, ht] at hu; cases hu
    exact ⟨k, hk, hK k hh, fun hnp => hold ts (hp hnp)⟩
  have htx : Ticketed (promThread t cfg.mem w) → ∃ ts w', (cfg.mem.append w).1.get? ts = some w' ∧
      w'.loc = XL ∧ w'.tid = tid ∧ w'.val.toNat = tk (promThread t cfg.mem w) + 1 := fun hk =>
    let ⟨ts, w', hw, hl, hid, hv⟩ := h.tx tid t ht hk; ⟨ts, w', hg hw, hl, hid, hv⟩
  have htd : Ticketed (promThread t cfg.mem w) → Past (promThread t cfg.mem w) → ∃ ts w',
      (cfg.mem.append w).1.get? ts = some w' ∧ w'.loc = OL ∧ w'.val.toNat = tk (promThread t cfg.mem w) + 1 :=
    fun hk hp => let ⟨ts, w', hw, hl, hv⟩ := h.tdone tid t ht hk hp; ⟨ts, w', hg hw, hl, hv⟩
  -- splitting the messages of the new memory
  have split : ∀ {ts w'}, (cfg.mem.append w).1.get? ts = some w' →
      cfg.mem.get? ts = some w' ∨ (ts = cfg.mem.last + 1 ∧ w' = w) := fun hw => by
    rcases cfg.mem.get?_append_eq_some w hw with ⟨-, h1⟩ | ⟨a, rfl⟩
    · exact .inl h1
    · exact .inr ⟨a, rfl⟩
  rcases hG.loc _ hnew w hw0 with ⟨hl, hr1⟩ | ⟨hl, -⟩ | ⟨hl, hr7⟩
  · -- a `next` promise: the value `xc + 1`
    have hnt := rk1 hS' hr1
    obtain ⟨tr, v, hr, htr, hat, hval⟩ := hG.xval _ hnew w hw0 hl
    have htr' : tr ≤ cfg.mem.last := Nat.lt_succ_iff.mp htr
    rw [read?_append_of_le _ _ _ htr'] at hr
    rw [atomic_append_last _ _ _ _ htr'] at hat
    have hown : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = XL → w'.tid ≠ tid := by
      intro ts w' hw hl' e
      obtain ⟨k, u, -, hu, hh⟩ := h.xheld ts w' hw hl'
      rw [e, ht] at hu; cases hu
      rcases hh with ⟨a, -⟩ | ⟨-, ts1, h1, w1, hw1, hl1, -⟩
      · exact hnt a
      · have := hG.uniq ts1 (hold ts1 h1) _ hnew w1 w (hg hw1) hw0 (hl1.trans hl.symm)
        have h2 := hPl ts1 h1; rw [this] at h2; exact absurd h2 (Nat.not_succ_le_self _)
    obtain ⟨-, hvx⟩ := atomic_lastWrite _ _ _ hr hat hown
    have hv1 : w.val.toNat = fv cfg.mem XL + 1 := by rw [hval, hvx]; omega
    refine build h ht hpre hb (.inr ⟨w, hwt, rfl, fun _ => hv1, fun hlo => absurd (hl.symm.trans hlo) h.hxo⟩)
      hT' (fun ts w' hw hl' e => ?_) (fun ts w' hw hl' e => ?_) htx htd
    · rcases split hw with hw | ⟨rfl, rfl⟩
      · exact oldx ts w' hw hl' e
      · exact ⟨_, hv1, .inr ⟨hnt, _, hnew, w', hw0, hl, hv1⟩⟩
    · rcases split hw with hw | ⟨rfl, rfl⟩
      · exact oldo ts w' hw hl' e
      · exact absurd (hl.symm.trans hl') h.hxo
  · -- a counter promise
    refine build h ht hpre hb (.inr ⟨w, hwt, rfl, fun hx => absurd (hx.symm.trans hl) h.hxc,
      fun hx => absurd (hx.symm.trans hl) h.hoc⟩) hT' (fun ts w' hw hl' e => ?_) (fun ts w' hw hl' e => ?_) htx htd
    · rcases split hw with hw | ⟨rfl, rfl⟩
      · exact oldx ts w' hw hl' e
      · exact absurd (hl'.symm.trans hl) h.hxc
    · rcases split hw with hw | ⟨rfl, rfl⟩
      · exact oldo ts w' hw hl' e
      · exact absurd (hl'.symm.trans hl) h.hoc
  · -- an `owner` promise: the value `M + 1`
    have hnp : ¬ Past t := fun hp => hp hr7
    obtain ⟨o1, o2⟩ := hG.oval _ hnew w hw0 hl
    have hkey : ∃ k, w.val.toNat = k + 1 ∧ ORd (cfg.mem.append w).1 k ∧
        HoldsK (promThread t cfg.mem w) (cfg.mem.append w).1 k ∧ HoldsK t cfg.mem k := by
      by_cases hk : Ticketed t
      · obtain ⟨a, b⟩ := o1 hk
        have a' : w.val.toNat = (tk t + 1) % 2 ^ 32 := a
        have := h.tk_lt ht hk
        exact ⟨tk t, by rw [a']; omega, b, .inl ⟨hk, rfl⟩, .inl ⟨hk, rfl⟩⟩
      · obtain ⟨tsx, hx, wx, hwx, hlx, hvx, k, hk1, hk2⟩ := o2 hk
        have hxt : tsx ∈ t.prom := by
          rcases (hmem tsx).mp hx with hx | rfl
          · exact hx
          · rw [hw0] at hwx; cases hwx; exact absurd (hlx.symm.trans hl) h.hxo
        have hwx' : cfg.mem.get? tsx = some wx := by rw [← hT0.promIn.get hpre hxt]; exact hwx
        obtain ⟨k', u, hk', -, -⟩ := h.xheld tsx wx hwx' hlx
        have := h.xv' hwx' hlx
        obtain ⟨tr, v, -, hv⟩ := id hk1
        have : k < 2 ^ 32 := by rw [← hv]; exact Nat.mod_lt _ (by decide)
        have e : wx.val.toNat = k + 1 := by omega
        exact ⟨k, by omega, hk1, .inr ⟨hk, tsx, hx, wx, hwx, hlx, e⟩, .inr ⟨hk, tsx, hxt, wx, hwx', hlx, e⟩⟩
    obtain ⟨k, hv, hord, hK1, hK0⟩ := hkey
    have hkM : k ≤ fv cfg.mem OL := by
      obtain ⟨tr, v, hr, hvk⟩ := hord
      rcases read?_append_eq_some _ _ hr with hr | ⟨-, -, rfl⟩
      · have := h.ov tr v hr; have := Nat.mod_le v.toNat (2 ^ 32); omega
      · have := Nat.mod_lt w.val.toNat (by decide : 2 ^ 32 > 0)
        omega
    have hkM' : k = fv cfg.mem OL := by
      apply Classical.byContradiction; intro hne
      obtain ⟨ts', w', hw', hl', hv'⟩ := h.osurj k (by omega)
      obtain ⟨k', u', hk', hu', hh', hp'⟩ := h.oheld ts' w' hw' hl'
      obtain rfl : k' = k := by omega
      have e := h.holdsK_inj hu' ht hh' hK0
      rw [e, ht] at hu'; cases hu'
      have := hG.uniq ts' (hold ts' (hp' hnp)) _ hnew w' w (hg hw') hw0 (hl'.trans hl.symm)
      have h2 := cfg.mem.last_le_of_get?_eq_some hw'; rw [this] at h2; exact absurd h2 (Nat.not_succ_le_self _)
    refine build h ht hpre hb (.inr ⟨w, hwt, rfl, fun hx => absurd (hx.symm.trans hl) h.hxo, fun _ => by omega⟩)
      hT' (fun ts w' hw hl' e => ?_) (fun ts w' hw hl' e => ?_) htx htd
    · rcases split hw with hw | ⟨rfl, rfl⟩
      · exact oldx ts w' hw hl' e
      · exact absurd (hl'.symm.trans hl) h.hxo
    · rcases split hw with hw | ⟨rfl, rfl⟩
      · exact oldo ts w' hw hl' e
      · exact ⟨k, hv, hK1, fun _ => hnew⟩

/-- **An instruction step keeps the invariant.** -/
theorem inv_instr {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hs : stepOne Arch.tso t tid cfg.mem = some outs) (ho : .ok oc ∈ outs)
    (hc : CertOkN Arch.tso tid oc.thread oc.mem fuel) (hb : (cfg.withThread tid oc.thread oc.mem).Bnd) :
    InvP fuel N (cfg.withThread tid oc.thread oc.mem) ∧
      ((fv oc.mem OL = fv cfg.mem OL ∧ oc.mem.lastWrite (OL) = cfg.mem.lastWrite (OL)) ∨
        fv oc.mem OL = fv cfg.mem OL + 1) := by
  have hT0 := h.thr tid t ht
  have r := step_solo h.hxo h.hxc h.hoc hT0.sinv hT0.rinv hT0.promIn hs ho
  have hG := good_of_certOkN h.hxo h.hxc h.hoc hc r.sinv r.rinv r.promIn
  have hT' : TS fuel tid oc.thread oc.mem :=
    ⟨r.sinv, r.rinv, r.promIn, hG, nacert_of_certOkN h.hxo h.hxc h.hoc hc r.sinv r.rinv r.promIn⟩
  have hpre : cfg.mem.Prefix oc.mem := (stepOne_dord _ hs ho).2.2.1
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → oc.mem.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  have hxN := h.xcN; have hN32 := h.N32
  cases step_eff h.hxo h.hxc h.hoc hT0.sinv hT0.rinv hT0.promIn hs ho hG with
  | quiet hm htk hk hpast hkeep =>
    have hK : ∀ k, HoldsK t cfg.mem k → HoldsK oc.thread oc.mem k := fun k hh =>
      hh.keep hT0.promIn hpre htk hk (fun ts hts w hw hl => hkeep ts hts w hw (by rw [hl]; exact h.hxc))
    have hold : ∀ {ts w'} {l : Loc}, l ≠ CL → oc.mem.get? ts = some w' → w'.loc = l → cfg.mem.get? ts = some w' := by
      intro ts w' l hl hw hl'
      rcases hm with hm | ⟨v, hm⟩
      · rw [← hm]; exact hw
      · rw [hm] at hw; exact (mem_frame _ _ (fun e => hl e.symm)).2.2.2 ts w' hw hl'
    refine build h ht hpre hb ?_ hT' (fun ts w hw hl e => ?_) (fun ts w hw hl e => ?_) (fun hk' => ?_)
      (fun hk' hp => ?_)
    · rcases hm with hm | ⟨v, hm⟩
      · exact .inl hm
      · exact .inr ⟨_, rfl, hm, fun hx => absurd hx.symm h.hxc, fun hx => absurd hx.symm h.hoc⟩
    · obtain ⟨k, u, hk1, hu, hh⟩ := h.xheld ts w (hold h.hxc hw hl) hl
      rw [e, ht] at hu; cases hu
      exact ⟨k, hk1, hK k hh⟩
    · have hw0 := hold h.hoc hw hl
      obtain ⟨k, u, hk1, hu, hh, hp⟩ := h.oheld ts w hw0 hl
      rw [e, ht] at hu; cases hu
      exact ⟨k, hk1, hK k hh, fun hnp => hkeep ts (hp fun hp' => hnp (hpast.mpr hp')) w hw0
        (by rw [hl]; exact h.hoc)⟩
    · obtain ⟨ts, w, hw, hl, hid, hv⟩ := h.tx tid t ht (htk.mp hk')
      exact ⟨ts, w, hg hw, hl, hid, by rw [hk (htk.mp hk')]; exact hv⟩
    · obtain ⟨ts, w, hw, hl, hv⟩ := h.tdone tid t ht (htk.mp hk') (hpast.mp hp)
      exact ⟨ts, w, hg hw, hl, by rw [hk (htk.mp hk')]; exact hv⟩
  | tkt h0 h1 hp1 hw =>
    rcases hw with ⟨tr, v, hr, hat, hkv, hnp, v', hv', hm, hpr⟩ | ⟨ts, hts, w, hw, hl, hv, hm, hpr⟩
    · have hown : ∀ ts w, cfg.mem.get? ts = some w → w.loc = XL → w.tid ≠ tid := by
        intro ts w hw hl e
        obtain ⟨k, u, -, hu, hh⟩ := h.xheld ts w hw hl
        rw [e, ht] at hu; cases hu
        rcases hh with ⟨a, -⟩ | ⟨-, ts1, h1, w1, hw1, hl1, -⟩
        · exact h0 a
        · exact hnp ts1 h1 w1 hw1 hl1
      obtain ⟨-, hvx⟩ := atomic_lastWrite _ _ _ hr hat hown
      have htk' : tk oc.thread = fv cfg.mem XL := by rw [hkv, hvx]; omega
      have hv1 : v'.toNat = fv cfg.mem XL + 1 := by rw [hv', htk']; omega
      have split : ∀ {ts w'}, oc.mem.get? ts = some w' →
          cfg.mem.get? ts = some w' ∨ (ts = cfg.mem.last + 1 ∧ w' = { loc := XL, val := v', tid }) := fun hw => by
        rw [hm] at hw
        rcases cfg.mem.get?_append_eq_some _ hw with ⟨-, h1⟩ | ⟨a, rfl⟩
        · exact .inl h1
        · exact .inr ⟨a, rfl⟩
      refine build h ht hpre hb (.inr ⟨_, rfl, hm, fun _ => hv1, fun hx => absurd hx h.hxo⟩) hT'
        (fun ts w hw hl e => ?_) (fun ts w hw hl e => ?_) (fun _ => ?_) (fun _ hp => absurd hp hp1)
      · rcases split hw with hw | ⟨rfl, rfl⟩
        · exact absurd e (hown ts w hw hl)
        · exact ⟨_, hv1, .inl ⟨h1, htk'⟩⟩
      · rcases split hw with hw | ⟨rfl, rfl⟩
        · obtain ⟨k, u, -, hu, hh, -⟩ := h.oheld ts w hw hl
          rw [e, ht] at hu; cases hu
          rcases hh with ⟨a, -⟩ | ⟨-, ts1, h1, w1, hw1, hl1, -⟩
          · exact absurd a h0
          · exact absurd hl1 (hnp ts1 h1 w1 hw1)
        · exact absurd hl h.hxo
      · exact ⟨_, _, by rw [hm]; exact Memory.get?_append_last _ _, rfl, rfl, by rw [htk']; exact hv1⟩
    · obtain ⟨w0, hw0, hid⟩ := hT0.promIn ts hts
      rw [hw] at hw0; cases hw0
      obtain ⟨k, u, hk, hu, -⟩ := h.xheld ts w hw hl
      rw [hid, ht] at hu; cases hu
      have := h.xv' hw hl
      have := tk_lt oc.thread
      have htk' : tk oc.thread = k := by omega
      -- every `next` message of `tid` is `ts`; every holding of `tid` is `k`
      have hk1 : ∀ k', HoldsK t cfg.mem k' → k' = k := by
        intro k' hh
        rcases hh with ⟨a, -⟩ | ⟨-, ts3, h3, w3, hw3, hl3, hv3⟩
        · exact absurd a h0
        · have := hT0.good.uniq ts3 h3 ts hts w3 w hw3 hw (hl3.trans hl.symm)
          subst this; rw [hw] at hw3; cases hw3; omega
      refine build h ht hpre hb (.inl hm) hT' (fun ts2 w2 hw2 hl2 e => ?_) (fun ts2 w2 hw2 hl2 e => ?_)
        (fun _ => ⟨ts, w, hg hw, hl, hid, by rw [htk']; exact hk⟩) (fun _ hp => absurd hp hp1)
      · rw [hm] at hw2
        obtain ⟨k2, u, hk2, hu, hh⟩ := h.xheld ts2 w2 hw2 hl2
        rw [e, ht] at hu; cases hu
        exact ⟨k2, hk2, .inl ⟨h1, by rw [htk', hk1 k2 hh]⟩⟩
      · rw [hm] at hw2
        obtain ⟨k2, u, hk2, hu, hh, hp⟩ := h.oheld ts2 w2 hw2 hl2
        rw [e, ht] at hu; cases hu
        refine ⟨k2, hk2, .inl ⟨h1, by rw [htk', hk1 k2 hh]⟩, fun _ => ?_⟩
        rw [hpr]
        refine mem_erase_of_ne' (hp (not_past hT0.sinv h0)) fun e' => ?_
        subst e'; rw [hw] at hw2; cases hw2; exact h.hxo (hl.symm.trans hl2)
  | rel h0 h1 hk hord hp0 hp1 hw =>
    have hlt := h.tk_lt ht h0
    have hle := h.ord_le hord
    have hK : ∀ k, HoldsK t cfg.mem k → HoldsK oc.thread oc.mem k := fun k hh => by
      rcases hh with ⟨a, b⟩ | ⟨a, -⟩
      · exact .inl ⟨h1, hk.trans b⟩
      · exact absurd h0 a
    have oldx : ∀ ts w, cfg.mem.get? ts = some w → w.loc = XL → w.tid = tid →
        ∃ k, w.val.toNat = k + 1 ∧ HoldsK oc.thread oc.mem k := fun ts w hw hl e => by
      obtain ⟨k, u, hk1, hu, hh⟩ := h.xheld ts w hw hl
      rw [e, ht] at hu; cases hu
      exact ⟨k, hk1, hK k hh⟩
    have htx : Ticketed oc.thread → ∃ ts w, oc.mem.get? ts = some w ∧ w.loc = XL ∧ w.tid = tid ∧
        w.val.toNat = tk oc.thread + 1 := fun _ => by
      obtain ⟨ts, w, hw, hl, hid, hv⟩ := h.tx tid t ht h0
      exact ⟨ts, w, hg hw, hl, hid, by rw [hk]; exact hv⟩
    rcases hw with ⟨v', hv', hm, hpr, hnp⟩ | ⟨ts, hts, w, hw, hl, hv, hm, hpr⟩
    · have htM : tk t = fv cfg.mem OL := by
        apply Classical.byContradiction; intro hne
        obtain ⟨ts', w', hw', hl', hv''⟩ := h.osurj (tk t) (by omega)
        obtain ⟨k', u', hk', hu', hh', hp'⟩ := h.oheld ts' w' hw' hl'
        obtain rfl : k' = tk t := by omega
        have e := h.holdsK_inj hu' ht hh' (.inl ⟨h0, rfl⟩)
        rw [e, ht] at hu'; cases hu'
        exact hnp ts' (hp' hp0) w' hw' hl'
      have hv1 : v'.toNat = fv cfg.mem OL + 1 := by rw [hv']; omega
      have split : ∀ {ts w'}, oc.mem.get? ts = some w' →
          cfg.mem.get? ts = some w' ∨ (ts = cfg.mem.last + 1 ∧ w' = { loc := OL, val := v', tid }) := fun hw => by
        rw [hm] at hw
        rcases cfg.mem.get?_append_eq_some _ hw with ⟨-, h1⟩ | ⟨a, rfl⟩
        · exact .inl h1
        · exact .inr ⟨a, rfl⟩
      refine build h ht hpre hb (.inr ⟨_, rfl, hm, fun hx => absurd hx.symm h.hxo, fun _ => hv1⟩) hT'
        (fun ts w hw hl e => ?_) (fun ts w hw hl e => ?_) htx
        (fun _ _ => ⟨_, _, by rw [hm]; exact Memory.get?_append_last _ _, rfl, by rw [hk, htM]; exact hv1⟩)
      · rcases split hw with hw | ⟨rfl, rfl⟩
        · exact oldx ts w hw hl e
        · exact absurd hl.symm h.hxo
      · rcases split hw with hw | ⟨rfl, rfl⟩
        · obtain ⟨k, u, -, hu, -, hp⟩ := h.oheld ts w hw hl
          rw [e, ht] at hu; cases hu
          exact absurd hl (hnp ts (hp hp0) w hw)
        · exact ⟨tk t, by rw [hv1, htM], .inl ⟨h1, hk⟩, fun hp => absurd hp1 hp⟩
    · refine build h ht hpre hb (.inl hm) hT' (fun ts w hw hl e => oldx ts w (hm ▸ hw) hl e)
        (fun ts w hw hl e => ?_) htx (fun _ _ => ⟨ts, w, by rw [hm]; exact hw, hl, by rw [hk]; omega⟩)
      obtain ⟨k, u, hk1, hu, hh, -⟩ := h.oheld ts w (hm ▸ hw) hl
      rw [e, ht] at hu; cases hu
      exact ⟨k, hk1, hK k hh, fun hp => absurd hp1 hp⟩

/-- **A semantic step keeps the invariant**; `owner` keeps its value and its
last write, or grows by one. -/
theorem inv_step {cfg' : Config isa} (hst : StepSem Arch.tso fuel tid cfg cfg') :
    InvP fuel N cfg' ∧ ((fv cfg'.mem OL = fv cfg.mem OL ∧ cfg'.mem.lastWrite (OL) = cfg.mem.lastWrite (OL)) ∨
      fv cfg'.mem OL = fv cfg.mem OL + 1) := by
  have hb := h.bnd.semStep hst
  rcases hst with ⟨t1, outs, oc, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, hwt, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    exact inv_instr h ht hs ho hc hb
  · rw [ht] at ht1; cases ht1
    exact inv_prom h ht hwt hc hb

end Pres

/-! ## Initially and along traces -/

theorem inv_init {fuel N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketX64.TkStartX N states initMem) : InvP fuel N (Config.init states initMem) := by
  have I0 := TicketX64Inv.inv_init hs
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  have hnt : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t → ¬ Ticketed t :=
    fun i t h hk => absurd (I0.tkLt i t h hk) (Nat.not_lt_zero _)
  have hget : ∀ ts w, (Config.init states initMem : Config isa).mem.get? ts = some w → False := by
    intro ts w h; simp [Memory.get?, Config.init] at h
  have hfx := I0.fx
  have hfo := I0.fo
  refine ⟨I0.size, I0.N32, I0.hxo, I0.hxc, I0.hoc, I0.bnd, fun ts v h => ?_, fun ts v h => by have := I0.ov ts v h; omega,
    fun _ _ _ _ h => (hget _ _ h).elim, fun _ _ _ _ h => (hget _ _ h).elim,
    fun k hk => absurd hk (by omega), fun k hk => absurd hk (by omega), fun _ _ h => (hget _ _ h).elim,
    fun _ _ h => (hget _ _ h).elim, fun i t h ht => absurd ht (hnt i t h), fun i t h ht => absurd ht (hnt i t h),
    fun i t h => ?_⟩
  · rcases Memory.read?_eq_some _ h with ⟨rfl, rfl⟩ | ⟨w, hw, -, -⟩
    · have := hs.hX0; simp only [Config.init] at this ⊢; simp [this]
    · exact (hget _ _ hw).elim
  · have hT := I0.thr i t h
    obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hpc : (Thread.init s : Thread isa).st.st.2 = pcA 1 := by
      show s.st.2 = _
      rw [(hs.hst s hm).pc, (hs.hst s hm).exe]; exact TicketX64Trees.label_worker
    refine ⟨⟨hT.st, 1, by decide, hpc⟩, fun j hj e => ?_, (fun ts h => by simp [Thread.init] at h), good_nil rfl, ?_⟩
    · rw [addrOf_inj hj (by decide) (e.symm.trans hpc)]; trivial
    · rintro (hk | ⟨ts, hts, -⟩)
      · exact absurd hk (hnt i _ h)
      · cases hts

/-- **The invariant along a semantic trace from a start configuration**, and
`owner` at each step. -/
theorem trace_invP {fuel N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketX64.TkStartX N states initMem) (tr : TraceSem Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, InvP fuel N (tr.cfg i)
  | 0 => h0 ▸ inv_init hs
  | i + 1 => by
    have h := trace_invP hs tr h0 i
    rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
    · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact (inv_step h ht hst).1
    · rw [he]; exact h

theorem trace_o {fuel N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketX64.TkStartX N states initMem) (tr : TraceSem Arch.tso fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) :
    (fv (tr.cfg (i + 1)).mem OL = fv (tr.cfg i).mem OL ∧
      (tr.cfg (i + 1)).mem.lastWrite (OL) = (tr.cfg i).mem.lastWrite (OL)) ∨
      fv (tr.cfg (i + 1)).mem OL = fv (tr.cfg i).mem OL + 1 := by
  rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
  · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
      rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
    exact (inv_step (trace_invP hs tr h0 i) ht hst).2
  · rw [he]; exact .inl ⟨rfl, rfl⟩

end Kraken.Promising.Live.X64SemInv
