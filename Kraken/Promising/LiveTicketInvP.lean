/-
**Stage 3: the ticket-lock invariant on the
semantic machine** (`InvP`), with outstanding promises.

`next` (`x`) and `owner` (`o`) messages in memory form chains of values: the
`next` messages have the distinct values `1, …, xc` (`xc` its final value),
the `owner` messages the distinct values `1, …, M` (`M` its final value).
Each `next` message of value `k + 1` belongs to the thread that *holds*
ticket `k` (`HoldsK`): it has taken it (`Ticketed`, `tk = k`) or reserved it
by its outstanding `next` promise. Each `owner` message of value `k + 1`
belongs to the holder of `k`, and stays an outstanding promise until its
owner is past its `STLR` (`Past`). A ticketed thread past its `STLR` has its
`owner` message in memory (`tdone`). Each thread satisfies the solo-run
predicates of `LiveTicketSolo` (`Good`, and `NACert` when it is ticketed or
holds a `next` promise).

So an appended `next` message has value `xc + 1` (an atomic read of the last
one), and an appended `owner` message value `M + 1` (the holder of `M`
writes it: the holder of a smaller value already wrote, and a second
`owner` message of a thread would be a second promise or a dead one).

- `step_eff`: what an instruction step does to `next` and `owner`.
- `holdsK_inj`: tickets are unique; `xcN`: at most `N` tickets (pigeonhole).
- `inv_step`: `InvP` is kept by every semantic step, and `owner` either
  keeps its value and last write or grows by one.
- `inv_init`, `trace_invP`.
-/
import Kraken.Promising.LiveTicketSolo

namespace Kraken.Promising.Live.TicketInvP

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.TicketInv
open Kraken.Promising.Live.TicketDrop Kraken.Promising.Live.Sem Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.TicketSolo
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkWorker).addrOf

/-! ## Holders and positions -/

/-- Past the `STLR`: positions 12 and 14. -/
def Past (u : Thread isa) : Prop := ¬ RkLe u 7

/-- Thread `u` holds ticket `k`: taken, or reserved by its `next` promise of
value `k + 1`. -/
def HoldsK (x : BitVec 64) (u : Thread isa) (mem : Memory) (k : Nat) : Prop :=
  (Ticketed u ∧ tk u = k) ∨
    (¬ Ticketed u ∧ ∃ ts ∈ u.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = k + 1)

/-- No promise of the thread is to location `l`. -/
def NoProm (l : Loc) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc ≠ l

/-- **What an instruction step does to `next` and `owner`.** -/
inductive Eff (x o c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- Neither written; ticket, position class and non-counter promises kept. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (htk : Ticketed oc.thread ↔ Ticketed t) (hk : Ticketed t → tk oc.thread = tk t)
      (hpast : Past oc.thread ↔ Past t)
      (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc ≠ L4 c → ts ∈ oc.thread.prom)
  /-- `LDADDA`: a fresh write after an atomic read, or the fulfilment of the
  `next` promise. -/
  | tkt (h0 : ¬ Ticketed t) (h1 : Ticketed oc.thread) (hp1 : ¬ Past oc.thread)
      (hw : (∃ tr v, mem.read? (L4 x) tr = some v ∧ mem.atomic (L4 x) tid tr (mem.last + 1) = true ∧
          tk oc.thread = v.toNat % 2 ^ 32 ∧ NoProm (L4 x) t mem ∧ ∃ v' : Val,
          v'.toNat = (tk oc.thread + 1) % 2 ^ 32 ∧ oc.mem = (mem.append { loc := L4 x, val := v', tid }).1 ∧
          oc.thread.prom = t.prom) ∨
        (∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = (tk oc.thread + 1) % 2 ^ 32 ∧
          oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts))
  /-- `STLR`: a fresh write, or the fulfilment of the `owner` promise. -/
  | rel (h0 : Ticketed t) (h1 : Ticketed oc.thread) (hk : tk oc.thread = tk t) (hord : ORd o mem (tk t))
      (hp0 : ¬ Past t)
      (hp1 : Past oc.thread)
      (hw : (∃ v' : Val, v'.toNat = (tk t + 1) % 2 ^ 32 ∧ oc.mem = (mem.append { loc := L4 o, val := v', tid }).1 ∧
          oc.thread.prom = t.prom ∧ NoProm (L4 o) t mem) ∨
        (∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 o ∧ w.val.toNat = (tk t + 1) % 2 ^ 32 ∧
          oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts))

theorem past_iff {u : Thread isa} {p : Nat} (hp : p ∈ tkPcs) (h : u.st.st.2 = pcA p) : Past u ↔ ¬ rk p ≤ 7 :=
  not_congr (rkLe_iff hp h 7)

/-- **What an instruction step does to `next` and `owner`**, position by
position (the post-thread `Good`, from its certification, excludes the dead
promises of a fresh `LDADDA` or `STLR`). -/
theorem step_eff {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
    (hxo : L4 x ≠ L4 o) (hxc : L4 x ≠ L4 c) (hoc : L4 o ≠ L4 c)
    (hS : SInv x o c t.st) (hR : RInv o t mem) (hP : PromIn tid t mem)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)
    (hg : Good x o c tid oc.thread oc.mem) : Eff x o c tid t mem oc := by
  obtain ⟨hSt, p, hp, hpc⟩ := hS
  have hPl := hP.le
  have Q : ∀ q ∈ tkPcs, oc.thread.st.st.2 = pcA q → (¬ rk q ≤ 7 ↔ ¬ rk p ≤ 7) →
      (Ticketed oc.thread ↔ Ticketed t) → (Ticketed t → tk oc.thread = tk t) →
      oc.mem = mem → oc.thread.prom = t.prom → Eff x o c tid t mem oc :=
    fun q hq hpq hr htk hk hm hpr => .quiet (.inl hm) htk hk
      ((past_iff hq hpq).trans (hr.trans (past_iff hp hpc).symm)) (fun ts hts _ _ _ => hpr ▸ hts)
  have tkd : ∀ q, q ∈ tkPcs → q ≠ 1 → q ≠ 2 → t.st.st.2 = pcA q → Ticketed t := fun q hq h1 h2 h =>
    ticketed_at h hq h1 h2
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ (exec_mov _ (hSt.at (by decide) (by decide) hpc)) hs ho
    exact Q 2 (by decide) (by rw [hst]) (by decide)
      (iff_of_false (fun h => h.2 (by rw [hst])) (fun h => h.1 hpc)) (fun h => absurd hpc h.1) hm hpr
  · obtain ⟨tr, old, hst, hrd, hw⟩ :=
      spec_rmw_p _ _ rfl (exec_ldadda _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dx) hs ho
    have h6 := hR.f2 hpc
    have htk1 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    have hk : tk oc.thread = old.toNat % 2 ^ 32 := by unfold tk; rw [hst]; exact wn_setWidth old
    have hval : (BitVec.setWidth 128 (BitVec.setWidth 32 old + BitVec.setWidth 32 t.st.st.1.regs.X6.toBitVec)).toNat =
        (tk oc.thread + 1) % 2 ^ 32 := by
      rw [hk]
      simp only [wn] at h6
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
      have : t.st.st.1.regs.X6.toBitVec.toNat % 2 ^ 32 = 1 := h6
      rw [this]; omega
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
  · obtain ⟨ts, v, hst, -, -, hm, hpr, -⟩ :=
      spec_load _ _ (exec_ldar _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO) hs ho
    exact Q 5 (by decide) (by rw [hst]) (by decide)
      (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 4 (by decide) (by decide) (by decide) hpc))
      (fun _ => by unfold tk; rw [hst]; rfl) hm hpr
  · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    exact Q 6 (by decide) (by rw [hst]) (by decide)
      (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 5 (by decide) (by decide) (by decide) hpc))
      (fun _ => by unfold tk; rw [hst]) hm hpr
  · obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ (exec_bne _ (hSt.at (by decide) (by decide) hpc)) hs ho
    by_cases hz : t.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      exact Q 7 (by decide) (by rw [hst]) (by decide)
        (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 6 (by decide) (by decide) (by decide) hpc))
        (fun _ => by unfold tk; rw [hst]) hm hpr
    · rw [ite_eq_right hz] at hst
      exact Q 4 (by decide) (by rw [hst]) (by decide)
        (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 6 (by decide) (by decide) (by decide) hpc))
        (fun _ => by unfold tk; rw [hst]) hm hpr
  · obtain ⟨ts, v, hst, -, -, hm, hpr, -⟩ :=
      spec_load _ _ (exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc) hs ho
    exact Q 8 (by decide) (by rw [hst]) (by decide)
      (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 7 (by decide) (by decide) (by decide) hpc))
      (fun _ => by unfold tk; rw [hst]; rfl) hm hpr
  · obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ (exec_add5 _ (hSt.at (by decide) (by decide) hpc)) hs ho
    exact Q 9 (by decide) (by rw [hst]) (by decide)
      (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 8 (by decide) (by decide) (by decide) hpc))
      (fun _ => by unfold tk; rw [hst]; rfl) hm hpr
  · obtain ⟨hst, hw⟩ := spec_store_p _ _ (exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x2 hSt.dc) hs ho
    have htk := iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide))
      (tkd 9 (by decide) (by decide) (by decide) hpc)
    have hpast : Past oc.thread ↔ Past t :=
      (past_iff (p := 10) (by decide) (by rw [hst])).trans ((by decide : (¬ rk 10 ≤ 7 ↔ ¬ rk 9 ≤ 7)).trans
        (past_iff (by decide) hpc).symm)
    rcases hw with ⟨hm, hpr, -⟩ | ⟨ts, hts, hgw, -, -, hm, hpr, -⟩
    · exact .quiet (.inr ⟨_, hm⟩) htk (fun _ => by unfold tk; rw [hst]) hpast
        (fun ts hts _ _ _ => by rw [hpr, erase_fresh hPl]; exact hts)
    · refine .quiet (.inl hm) htk (fun _ => by unfold tk; rw [hst]) hpast fun ts' hts' w hw hl => ?_
      rw [hpr]; refine mem_erase_of_ne' hts' fun e => hl ?_
      subst e; rw [hgw] at hw; cases hw; rfl
  · obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ (exec_add4 _ (hSt.at (by decide) (by decide) hpc)) hs ho
    exact Q 11 (by decide) (by rw [hst]) (by decide)
      (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 10 (by decide) (by decide) (by decide) hpc))
      (fun _ => by unfold tk; rw [hst]; rfl) hm hpr
  · obtain ⟨hst, hw⟩ := spec_store_p _ _ (exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dO) hs ho
    have h0 := tkd 11 (by decide) (by decide) (by decide) hpc
    have h1 : Ticketed oc.thread := ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)
    have hk : tk oc.thread = tk t := by unfold tk; rw [hst]
    have hval : (BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec)).toNat = (tk t + 1) % 2 ^ 32 := by
      rw [val_setWidth]; exact hR.f11 hpc
    have h12 : ¬ RkLe oc.thread 7 := fun h => absurd ((rkLe_iff (p := 12) (by decide) (by rw [hst]) 7).mp h) (by decide)
    refine .rel h0 h1 hk (hR.f7 11 (by decide) hpc) (fun h => h ((rkLe_iff (by decide) hpc 7).mpr (by decide))) h12 ?_
    rcases hw with ⟨hm, hpr, -⟩ | ⟨ts, hts, hgw, -, -, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      refine .inl ⟨_, hval, hm, hpr', fun ts hts w hw hl => ?_⟩
      have hw' : oc.mem.get? ts = some w := by rw [hm]; rw [(Memory.Prefix.append _ _).get? (hPl ts hts)]; exact hw
      rcases hg.loc ts (hpr' ▸ hts) w hw' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact hxo (h.symm.trans hl)
      · exact hoc (hl.symm.trans h)
      · exact h12 h
    · exact .inr ⟨ts, hts, _, hgw, rfl, hval, hm, hpr⟩
  · obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ (exec_b_done _ (hSt.at (by decide) (by decide) hpc)) hs ho
    exact Q 14 (by decide) (by rw [hst]) (by decide)
      (iff_of_true (ticketed_at (by rw [hst]) (by decide) (by decide) (by decide)) (tkd 12 (by decide) (by decide) (by decide) hpc))
      (fun _ => by unfold tk; rw [hst]) hm hpr
  · rw [stepOne_end hSt hpc] at hs; cases hs


/-! ## Small facts -/

theorem tk_lt (u : Thread isa) : tk u < 2 ^ 32 := Nat.mod_lt _ (by decide)

theorem read?_of_get? {mem : Memory} {ts : Time} {w : Msg} (hw : mem.get? ts = some w) :
    mem.read? w.loc ts = some w.val := Kraken.Promising.SLR.read?_of_get?' hw

theorem atomic_append_last (mem : Memory) (w : Msg) (l : Loc) (tid : Nat) {tr : Time} (htr : tr ≤ mem.last) :
    (mem.append w).1.atomic l tid tr (mem.last + 1) = mem.atomic l tid tr (mem.last + 1) :=
  atomic_append_of_le mem w l tid htr

theorem rk1 {x o c : BitVec 64} {u : Thread isa} (hS : SInv x o c u.st) (h : RkLe u 1) : ¬ Ticketed u := by
  obtain ⟨-, i, hi, hpc⟩ := hS
  have key : ∀ i ∈ tkPcs, rk i ≤ 1 → i = 1 ∨ i = 2 := by decide
  intro hT
  rcases key i hi (h i hi hpc) with rfl | rfl
  · exact hT.1 hpc
  · exact hT.2 hpc

theorem not_past {x o c : BitVec 64} {u : Thread isa} (hS : SInv x o c u.st) (h : ¬ Ticketed u) : ¬ Past u := by
  obtain ⟨-, i, hi, hpc⟩ := hS
  intro hp
  apply hp
  rw [rkLe_iff hi hpc]
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | exact absurd (ticketed_at hpc (by decide) (by decide) (by decide)) h

theorem HoldsK.keep {x : BitVec 64} {tid k : Nat} {t t' : Thread isa} {mem mem' : Memory} (h : HoldsK x t mem k)
    (hP : PromIn tid t mem) (hp : mem.Prefix mem') (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 x → ts ∈ t'.prom) : HoldsK x t' mem' k := by
  rcases h with ⟨a, b⟩ | ⟨a, ts, hts, w, hw, hl, hv⟩
  · exact .inl ⟨htk.mpr a, (hk a).trans b⟩
  · exact .inr ⟨fun e => a (htk.mp e), ts, hkeep ts hts w hw hl, w, by rw [hP.get hp hts]; exact hw, hl, hv⟩

/-! ## The invariant -/

/-- The final value of a word (a notation, so that `omega` sees one atom). -/
scoped notation:max "fv " mem:max a:max => BitVec.toNat (Memory.finalVal mem (L4 a))

/-- The per-thread part of the invariant. -/
structure TS (fuel : Nat) (x o c : BitVec 64) (i : Nat) (u : Thread isa) (mem : Memory) : Prop where
  sinv : SInv x o c u.st
  rinv : RInv o u mem
  promIn : PromIn i u mem
  good : Good x o c i u mem
  nac : Ticketed u ∨ HasX x u mem → NACert fuel i u mem

theorem TS.mono {fuel : Nat} {x o c : BitVec 64} {i : Nat} {u : Thread isa} {mem mem' : Memory}
    (hT : TS fuel x o c i u mem) (hb : u.Bnd mem.last) (hp : mem.Prefix mem') : TS fuel x o c i u mem' :=
  ⟨hT.sinv, hT.rinv.mono hp, hT.promIn.mono hp, hT.good.mono hp hT.promIn, fun hh =>
    (hT.nac (hh.imp_right fun ⟨ts, hts, w, hw, hl⟩ => ⟨ts, hts, w, by rw [← hT.promIn.get hp hts]; exact hw, hl⟩)).replay
      hT.sinv hb hp⟩

/-- **The ticket-lock invariant with promises.** -/
structure InvP (fuel N : Nat) (x o c : BitVec 64) (cfg : Config isa) : Prop where
  size : cfg.threads.size = N
  N32 : N + 1 < 2 ^ 32
  hxo : L4 x ≠ L4 o
  hxc : L4 x ≠ L4 c
  hoc : L4 o ≠ L4 c
  bnd : cfg.Bnd
  xv : ∀ ts v, cfg.mem.read? (L4 x) ts = some v → v.toNat ≤ fv cfg.mem x
  ov : ∀ ts v, cfg.mem.read? (L4 o) ts = some v → v.toNat ≤ fv cfg.mem o
  xinj : ∀ ts1 ts2 w1 w2, cfg.mem.get? ts1 = some w1 → cfg.mem.get? ts2 = some w2 → w1.loc = L4 x → w2.loc = L4 x →
    w1.val.toNat = w2.val.toNat → ts1 = ts2
  oinj : ∀ ts1 ts2 w1 w2, cfg.mem.get? ts1 = some w1 → cfg.mem.get? ts2 = some w2 → w1.loc = L4 o → w2.loc = L4 o →
    w1.val.toNat = w2.val.toNat → ts1 = ts2
  xsurj : ∀ k < fv cfg.mem x, ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = k + 1
  osurj : ∀ k < fv cfg.mem o, ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 o ∧ w.val.toNat = k + 1
  xheld : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x →
    ∃ k u, w.val.toNat = k + 1 ∧ cfg.threads[w.tid]? = some u ∧ HoldsK x u cfg.mem k
  oheld : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 o →
    ∃ k u, w.val.toNat = k + 1 ∧ cfg.threads[w.tid]? = some u ∧ HoldsK x u cfg.mem k ∧ (¬ Past u → ts ∈ u.prom)
  tx : ∀ (i : Nat) u, cfg.threads[i]? = some u → Ticketed u →
    ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 x ∧ w.tid = i ∧ w.val.toNat = tk u + 1
  tdone : ∀ (i : Nat) u, cfg.threads[i]? = some u → Ticketed u → Past u →
    ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 o ∧ w.val.toNat = tk u + 1
  thr : ∀ (i : Nat) u, cfg.threads[i]? = some u → TS fuel x o c i u cfg.mem

section Facts

variable {fuel N : Nat} {x o c : BitVec 64} {cfg : Config isa} (h : InvP fuel N x o c cfg)
include h

theorem InvP.xv' {ts : Time} {w : Msg} (hw : cfg.mem.get? ts = some w) (hl : w.loc = L4 x) :
    w.val.toNat ≤ fv cfg.mem x := h.xv ts w.val (hl ▸ read?_of_get? hw)

theorem InvP.ov' {ts : Time} {w : Msg} (hw : cfg.mem.get? ts = some w) (hl : w.loc = L4 o) :
    w.val.toNat ≤ fv cfg.mem o := h.ov ts w.val (hl ▸ read?_of_get? hw)

theorem InvP.holdsK_fun {i k1 k2 : Nat} {u : Thread isa} (hu : cfg.threads[i]? = some u)
    (h1 : HoldsK x u cfg.mem k1) (h2 : HoldsK x u cfg.mem k2) : k1 = k2 := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, ts1, h1, w1, hw1, hl1, hv1⟩ <;>
    rcases h2 with ⟨a2, b2⟩ | ⟨a2, ts2, h2, w2, hw2, hl2, hv2⟩
  · omega
  · exact absurd a1 a2
  · exact absurd a2 a1
  · have := (h.thr i u hu).good.uniq ts1 h1 ts2 h2 w1 w2 hw1 hw2 (hl1.trans hl2.symm)
    subst this; rw [hw1] at hw2; cases hw2; omega

theorem InvP.holdsK_msg {i k : Nat} {u : Thread isa} (hu : cfg.threads[i]? = some u) (hk : HoldsK x u cfg.mem k) :
    ∃ ts w, cfg.mem.get? ts = some w ∧ w.loc = L4 x ∧ w.tid = i ∧ w.val.toNat = k + 1 := by
  rcases hk with ⟨a, rfl⟩ | ⟨-, ts, hts, w, hw, hl, hv⟩
  · exact h.tx i u hu a
  · obtain ⟨w', hw', hid⟩ := (h.thr i u hu).promIn ts hts
    rw [hw] at hw'; cases hw'
    exact ⟨ts, w, hw, hl, hid, hv⟩

/-- **Tickets are unique.** -/
theorem InvP.holdsK_inj {i j k : Nat} {u u' : Thread isa} (hu : cfg.threads[i]? = some u)
    (hu' : cfg.threads[j]? = some u') (h1 : HoldsK x u cfg.mem k) (h2 : HoldsK x u' cfg.mem k) : i = j := by
  obtain ⟨ts1, w1, hw1, hl1, hid1, hv1⟩ := h.holdsK_msg hu h1
  obtain ⟨ts2, w2, hw2, hl2, hid2, hv2⟩ := h.holdsK_msg hu' h2
  have := h.xinj ts1 ts2 w1 w2 hw1 hw2 hl1 hl2 (hv1.trans hv2.symm)
  subst this; rw [hw1] at hw2; cases hw2; exact hid1.symm.trans hid2

/-- **At most `N` tickets** (pigeonhole). -/
theorem InvP.xcN : fv cfg.mem x ≤ N := by
  have hch : ∀ k, k < fv cfg.mem x → ∃ i, i < N ∧ ∃ u, cfg.threads[i]? = some u ∧ HoldsK x u cfg.mem k :=
    fun k hk => by
      obtain ⟨ts, w, hw, hl, hv⟩ := h.xsurj k hk
      obtain ⟨k', u, hv', hu, hh⟩ := h.xheld ts w hw hl
      obtain rfl : k' = k := by omega
      exact ⟨w.tid, h.size ▸ lt_size_of_get? hu, u, hu, hh⟩
  obtain ⟨g, hg⟩ := Classical.skolem.mp (fun k => (Classical.em (k < fv cfg.mem x)).elim
    (fun hk => (hch k hk).imp fun i hi => fun _ => hi) (fun hk => ⟨0, fun h => absurd h hk⟩))
  exact pigeon N _ g (fun k hk => (hg k hk).1) (fun i j hi hj e => by
    obtain ⟨-, u, hu, h1⟩ := hg i hi
    obtain ⟨-, u', hu', h2⟩ := hg j hj
    rw [e] at hu; rw [hu] at hu'; cases hu'
    exact h.holdsK_fun hu h1 h2)

theorem InvP.tk_lt {i : Nat} {u : Thread isa} (hu : cfg.threads[i]? = some u) (hk : Ticketed u) :
    tk u + 1 ≤ fv cfg.mem x := by
  obtain ⟨ts, w, hw, hl, -, hv⟩ := h.tx i u hu hk
  have := h.xv' hw hl; omega

theorem InvP.ord_le {k : Nat} (hk : ORd o cfg.mem k) : k ≤ fv cfg.mem o := by
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

variable {fuel N : Nat} {x o c : BitVec 64} {cfg : Config isa} {tid : Nat} {t : Thread isa}
  (h : InvP fuel N x o c cfg) (ht : cfg.threads[tid]? = some t)
include h ht

/-- **The invariant after a step of `tid`**, from the facts about `tid`. -/
theorem build {t' : Thread isa} {mem' : Memory}
    (hpre : cfg.mem.Prefix mem') (hb : (cfg.withThread tid t' mem').Bnd)
    (hm : mem' = cfg.mem ∨ ∃ w : Msg, w.tid = tid ∧ mem' = (cfg.mem.append w).1 ∧
      (w.loc = L4 x → w.val.toNat = fv cfg.mem x + 1) ∧ (w.loc = L4 o → w.val.toNat = fv cfg.mem o + 1))
    (hT : TS fuel x o c tid t' mem')
    (hxt : ∀ ts w, mem'.get? ts = some w → w.loc = L4 x → w.tid = tid → ∃ k, w.val.toNat = k + 1 ∧ HoldsK x t' mem' k)
    (hot : ∀ ts w, mem'.get? ts = some w → w.loc = L4 o → w.tid = tid →
      ∃ k, w.val.toNat = k + 1 ∧ HoldsK x t' mem' k ∧ (¬ Past t' → ts ∈ t'.prom))
    (htx : Ticketed t' → ∃ ts w, mem'.get? ts = some w ∧ w.loc = L4 x ∧ w.tid = tid ∧ w.val.toNat = tk t' + 1)
    (htd : Ticketed t' → Past t' → ∃ ts w, mem'.get? ts = some w ∧ w.loc = L4 o ∧ w.val.toNat = tk t' + 1) :
    InvP fuel N x o c (cfg.withThread tid t' mem') ∧
      ((fv mem' o = fv cfg.mem o ∧ mem'.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨ fv mem' o = fv cfg.mem o + 1) := by
  obtain ⟨x1, x2, x3, x4, -⟩ := chain (l := L4 x) (tid := tid)
    (hm.imp_right fun ⟨w, a, b, d, _⟩ => ⟨w, a, b, d⟩) h.xv h.xinj h.xsurj
  obtain ⟨o1, o2, o3, o4, o5⟩ := chain (l := L4 o) (tid := tid)
    (hm.imp_right fun ⟨w, a, b, _, e⟩ => ⟨w, a, b, e⟩) h.ov h.oinj h.osurj
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → mem'.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  have hK : ∀ {j k u}, cfg.threads[j]? = some u → HoldsK x u cfg.mem k → HoldsK x u mem' k := fun hu hh =>
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
    (hc : CertOkN Arch.armv8 tid (promThread t cfg.mem w) (cfg.mem.append w).1 fuel)
    (hb : (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1).Bnd) :
    InvP fuel N x o c (cfg.withThread tid (promThread t cfg.mem w) (cfg.mem.append w).1) ∧
      ((fv (cfg.mem.append w).1 o = fv cfg.mem o ∧
        (cfg.mem.append w).1.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
        fv (cfg.mem.append w).1 o = fv cfg.mem o + 1) := by
  have hT0 := h.thr tid t ht
  have hpre : cfg.mem.Prefix (cfg.mem.append w).1 := Memory.Prefix.append _ _
  have hPl := hT0.promIn.le
  have hxN := h.xcN; have hN32 := h.N32
  have hS' : SInv x o c (promThread t cfg.mem w).st := hT0.sinv
  have hR' : RInv o (promThread t cfg.mem w) (cfg.mem.append w).1 :=
    ⟨hT0.rinv.f2, fun a => (hT0.rinv.f5 a).mono hpre, fun a b => (hT0.rinv.f6 a b).mono hpre,
      fun i hi a => (hT0.rinv.f7 i hi a).mono hpre, hT0.rinv.f11⟩
  have hmem : ∀ ts, ts ∈ (promThread t cfg.mem w).prom ↔ ts ∈ t.prom ∨ ts = cfg.mem.last + 1 := fun ts => by
    simp only [List.mem_append, List.mem_singleton]; rfl
  have hw0 : (cfg.mem.append w).1.get? (cfg.mem.last + 1) = some w := Memory.get?_append_last _ _
  have hP' : PromIn tid (promThread t cfg.mem w) (cfg.mem.append w).1 := by
    intro ts hts
    rcases (hmem ts).mp hts with hts | rfl
    · rw [hT0.promIn.get hpre hts]; exact hT0.promIn ts hts
    · exact ⟨w, hw0, hwt⟩
  have hG := good_of_certOkN h.hxo h.hxc h.hoc hc hS' hR' hP'
  have hT' : TS fuel x o c tid (promThread t cfg.mem w) (cfg.mem.append w).1 :=
    ⟨hS', hR', hP', hG, nacert_of_certOkN h.hxo h.hxc h.hoc hc hS' hR' hP'⟩
  have hnew : cfg.mem.last + 1 ∈ (promThread t cfg.mem w).prom := (hmem _).mpr (.inr rfl)
  have hold : ∀ ts ∈ t.prom, ts ∈ (promThread t cfg.mem w).prom := fun ts hts => (hmem ts).mpr (.inl hts)
  have hK : ∀ k, HoldsK x t cfg.mem k → HoldsK x (promThread t cfg.mem w) (cfg.mem.append w).1 k := fun k hh =>
    hh.keep hT0.promIn hpre Iff.rfl (fun _ => rfl) (fun ts hts _ _ _ => hold ts hts)
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → (cfg.mem.append w).1.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  -- the old messages of `tid`
  have oldx : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 x → w'.tid = tid →
      ∃ k, w'.val.toNat = k + 1 ∧ HoldsK x (promThread t cfg.mem w) (cfg.mem.append w).1 k := by
    intro ts w' hw hl e
    obtain ⟨k, u, hk, hu, hh⟩ := h.xheld ts w' hw hl
    rw [e, ht] at hu; cases hu
    exact ⟨k, hk, hK k hh⟩
  have oldo : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 o → w'.tid = tid →
      ∃ k, w'.val.toNat = k + 1 ∧ HoldsK x (promThread t cfg.mem w) (cfg.mem.append w).1 k ∧
        (¬ Past (promThread t cfg.mem w) → ts ∈ (promThread t cfg.mem w).prom) := by
    intro ts w' hw hl e
    obtain ⟨k, u, hk, hu, hh, hp⟩ := h.oheld ts w' hw hl
    rw [e, ht] at hu; cases hu
    exact ⟨k, hk, hK k hh, fun hnp => hold ts (hp hnp)⟩
  have htx : Ticketed (promThread t cfg.mem w) → ∃ ts w', (cfg.mem.append w).1.get? ts = some w' ∧
      w'.loc = L4 x ∧ w'.tid = tid ∧ w'.val.toNat = tk (promThread t cfg.mem w) + 1 := fun hk =>
    let ⟨ts, w', hw, hl, hid, hv⟩ := h.tx tid t ht hk; ⟨ts, w', hg hw, hl, hid, hv⟩
  have htd : Ticketed (promThread t cfg.mem w) → Past (promThread t cfg.mem w) → ∃ ts w',
      (cfg.mem.append w).1.get? ts = some w' ∧ w'.loc = L4 o ∧ w'.val.toNat = tk (promThread t cfg.mem w) + 1 :=
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
    have hown : ∀ ts w', cfg.mem.get? ts = some w' → w'.loc = L4 x → w'.tid ≠ tid := by
      intro ts w' hw hl' e
      obtain ⟨k, u, -, hu, hh⟩ := h.xheld ts w' hw hl'
      rw [e, ht] at hu; cases hu
      rcases hh with ⟨a, -⟩ | ⟨-, ts1, h1, w1, hw1, hl1, -⟩
      · exact hnt a
      · have := hG.uniq ts1 (hold ts1 h1) _ hnew w1 w (hg hw1) hw0 (hl1.trans hl.symm)
        have h2 := hPl ts1 h1; rw [this] at h2; exact absurd h2 (Nat.not_succ_le_self _)
    obtain ⟨-, hvx⟩ := atomic_lastWrite _ _ _ hr hat hown
    have hv1 : w.val.toNat = fv cfg.mem x + 1 := by rw [hval, hvx]; omega
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
    have hkey : ∃ k, w.val.toNat = k + 1 ∧ ORd o (cfg.mem.append w).1 k ∧
        HoldsK x (promThread t cfg.mem w) (cfg.mem.append w).1 k ∧ HoldsK x t cfg.mem k := by
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
    have hkM : k ≤ fv cfg.mem o := by
      obtain ⟨tr, v, hr, hvk⟩ := hord
      rcases read?_append_eq_some _ _ hr with hr | ⟨-, -, rfl⟩
      · have := h.ov tr v hr; have := Nat.mod_le v.toNat (2 ^ 32); omega
      · have := Nat.mod_lt w.val.toNat (by decide : 2 ^ 32 > 0)
        omega
    have hkM' : k = fv cfg.mem o := by
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
    (hs : stepOne Arch.armv8 t tid cfg.mem = some outs) (ho : .ok oc ∈ outs)
    (hc : CertOkN Arch.armv8 tid oc.thread oc.mem fuel) (hb : (cfg.withThread tid oc.thread oc.mem).Bnd) :
    InvP fuel N x o c (cfg.withThread tid oc.thread oc.mem) ∧
      ((fv oc.mem o = fv cfg.mem o ∧ oc.mem.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
        fv oc.mem o = fv cfg.mem o + 1) := by
  have hT0 := h.thr tid t ht
  have r := step_solo h.hxo h.hxc h.hoc hT0.sinv hT0.rinv hT0.promIn hs ho
  have hG := good_of_certOkN h.hxo h.hxc h.hoc hc r.sinv r.rinv r.promIn
  have hT' : TS fuel x o c tid oc.thread oc.mem :=
    ⟨r.sinv, r.rinv, r.promIn, hG, nacert_of_certOkN h.hxo h.hxc h.hoc hc r.sinv r.rinv r.promIn⟩
  have hpre : cfg.mem.Prefix oc.mem := (stepOne_dord _ hs ho).2.2.1
  have hg : ∀ {ts w'}, cfg.mem.get? ts = some w' → oc.mem.get? ts = some w' := fun h' => by
    rw [hpre.get? (cfg.mem.last_le_of_get?_eq_some h')]; exact h'
  have hxN := h.xcN; have hN32 := h.N32
  cases step_eff h.hxo h.hxc h.hoc hT0.sinv hT0.rinv hT0.promIn hs ho hG with
  | quiet hm htk hk hpast hkeep =>
    have hK : ∀ k, HoldsK x t cfg.mem k → HoldsK x oc.thread oc.mem k := fun k hh =>
      hh.keep hT0.promIn hpre htk hk (fun ts hts w hw hl => hkeep ts hts w hw (by rw [hl]; exact h.hxc))
    have hold : ∀ {ts w'} {l : Loc}, l ≠ L4 c → oc.mem.get? ts = some w' → w'.loc = l → cfg.mem.get? ts = some w' := by
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
    · have hown : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x → w.tid ≠ tid := by
        intro ts w hw hl e
        obtain ⟨k, u, -, hu, hh⟩ := h.xheld ts w hw hl
        rw [e, ht] at hu; cases hu
        rcases hh with ⟨a, -⟩ | ⟨-, ts1, h1, w1, hw1, hl1, -⟩
        · exact h0 a
        · exact hnp ts1 h1 w1 hw1 hl1
      obtain ⟨-, hvx⟩ := atomic_lastWrite _ _ _ hr hat hown
      have htk' : tk oc.thread = fv cfg.mem x := by rw [hkv, hvx]; omega
      have hv1 : v'.toNat = fv cfg.mem x + 1 := by rw [hv', htk']; omega
      have split : ∀ {ts w'}, oc.mem.get? ts = some w' →
          cfg.mem.get? ts = some w' ∨ (ts = cfg.mem.last + 1 ∧ w' = { loc := L4 x, val := v', tid }) := fun hw => by
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
      have hk1 : ∀ k', HoldsK x t cfg.mem k' → k' = k := by
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
    have hK : ∀ k, HoldsK x t cfg.mem k → HoldsK x oc.thread oc.mem k := fun k hh => by
      rcases hh with ⟨a, b⟩ | ⟨a, -⟩
      · exact .inl ⟨h1, hk.trans b⟩
      · exact absurd h0 a
    have oldx : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x → w.tid = tid →
        ∃ k, w.val.toNat = k + 1 ∧ HoldsK x oc.thread oc.mem k := fun ts w hw hl e => by
      obtain ⟨k, u, hk1, hu, hh⟩ := h.xheld ts w hw hl
      rw [e, ht] at hu; cases hu
      exact ⟨k, hk1, hK k hh⟩
    have htx : Ticketed oc.thread → ∃ ts w, oc.mem.get? ts = some w ∧ w.loc = L4 x ∧ w.tid = tid ∧
        w.val.toNat = tk oc.thread + 1 := fun _ => by
      obtain ⟨ts, w, hw, hl, hid, hv⟩ := h.tx tid t ht h0
      exact ⟨ts, w, hg hw, hl, hid, by rw [hk]; exact hv⟩
    rcases hw with ⟨v', hv', hm, hpr, hnp⟩ | ⟨ts, hts, w, hw, hl, hv, hm, hpr⟩
    · have htM : tk t = fv cfg.mem o := by
        apply Classical.byContradiction; intro hne
        obtain ⟨ts', w', hw', hl', hv''⟩ := h.osurj (tk t) (by omega)
        obtain ⟨k', u', hk', hu', hh', hp'⟩ := h.oheld ts' w' hw' hl'
        obtain rfl : k' = tk t := by omega
        have e := h.holdsK_inj hu' ht hh' (.inl ⟨h0, rfl⟩)
        rw [e, ht] at hu'; cases hu'
        exact hnp ts' (hp' hp0) w' hw' hl'
      have hv1 : v'.toNat = fv cfg.mem o + 1 := by rw [hv']; omega
      have split : ∀ {ts w'}, oc.mem.get? ts = some w' →
          cfg.mem.get? ts = some w' ∨ (ts = cfg.mem.last + 1 ∧ w' = { loc := L4 o, val := v', tid }) := fun hw => by
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
theorem inv_step {cfg' : Config isa} (hst : StepSem Arch.armv8 fuel tid cfg cfg') :
    InvP fuel N x o c cfg' ∧ ((fv cfg'.mem o = fv cfg.mem o ∧ cfg'.mem.lastWrite (L4 o) = cfg.mem.lastWrite (L4 o)) ∨
      fv cfg'.mem o = fv cfg.mem o + 1) := by
  have hb := h.bnd.semStep hst
  rcases hst with ⟨t1, outs, oc, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, hwt, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    exact inv_instr h ht hs ho hc hb
  · rw [ht] at ht1; cases ht1
    exact inv_prom h ht hwt hc hb

end Pres

/-! ## Initially and along traces -/

theorem inv_init {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) : InvP fuel N x o c (Config.init states initMem) := by
  have hthr : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t →
      ∃ s ∈ states, t = Thread.init s := fun i t h => by
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, List.mem_of_getElem? hs, rfl⟩
  have hnt : ∀ (i : Nat) t, (Config.init states initMem : Config isa).threads[i]? = some t → ¬ Ticketed t :=
    fun i t h ht => by
      obtain ⟨s, hm, rfl⟩ := hthr i t h
      exact ht.1 ((hs.hst s hm).pc.trans addrOf_0)
  have hget : ∀ ts w, (Config.init states initMem : Config isa).mem.get? ts = some w → False := by
    intro ts w h; simp [Memory.get?, Config.init] at h
  have hfx : fv (Config.init states initMem : Config isa).mem x = 0 := by
    have := hs.hX0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  have hfo : fv (Config.init states initMem : Config isa).mem o = 0 := by
    have := hs.hO0; simp only [Memory.finalVal, Config.init] at this ⊢; simp [this]
  have hrd : ∀ (a : BitVec 64) ts v, (Config.init states initMem : Config isa).mem.read? (L4 a) ts = some v →
      ts = 0 ∧ v = (Config.init states initMem : Config isa).mem.initVal (L4 a) := by
    intro a ts v h
    rcases Memory.read?_eq_some _ h with ⟨rfl, e⟩ | ⟨w, hw, -, -⟩
    · exact ⟨rfl, e⟩
    · exact (hget _ _ hw).elim
  refine ⟨by simp [Config.init, hs.hN], hs.hN32, loc_ne hs.hxo, loc_ne hs.hxc, loc_ne hs.hoc, Config.init_bnd _ _,
    fun ts v h => ?_, fun ts v h => ?_, fun _ _ _ _ h => (hget _ _ h).elim, fun _ _ _ _ h => (hget _ _ h).elim,
    fun k hk => absurd hk (by omega), fun k hk => absurd hk (by omega), fun _ _ h => (hget _ _ h).elim,
    fun _ _ h => (hget _ _ h).elim, fun i t h ht => absurd ht (hnt i t h), fun i t h ht => absurd ht (hnt i t h),
    fun i t h => ?_⟩
  · obtain ⟨-, rfl⟩ := hrd x ts v h; rw [hfx]; have := hs.hX0; simp only [Config.init] at this ⊢; simp [this]
  · obtain ⟨-, rfl⟩ := hrd o ts v h; rw [hfo]; have := hs.hO0; simp only [Config.init] at this ⊢; simp [this]
  · obtain ⟨s, hm, rfl⟩ := hthr i t h
    have hs := hs.hst s hm
    have hpc : (Thread.init s : Thread isa).st.st.2 = pcA 1 := hs.pc.trans addrOf_0
    have hS : SInv x o c (Thread.init s : Thread isa).st :=
      ⟨⟨hs.exe, hs.decls, hs.endPc, hs.x0, hs.x1, hs.x2, hs.dx, hs.dO, hs.dc⟩, 1, by decide, hpc⟩
    have hne : ∀ j ∈ tkPcs, j ≠ 1 → (Thread.init s : Thread isa).st.st.2 = pcA j → False :=
      fun j hj h1 e => pc_ne hpc e (by decide) hj (Ne.symm h1)
    refine ⟨hS, ⟨fun e => (hne 2 (by decide) (by decide) e).elim, fun e => (hne 5 (by decide) (by decide) e).elim,
      fun e => (hne 6 (by decide) (by decide) e).elim, fun i hi e => (hne i ?_ ?_ e).elim,
      fun e => (hne 11 (by decide) (by decide) e).elim⟩, (fun ts h => by simp [Thread.init] at h), good_nil rfl, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega
    · rintro (hk | ⟨ts, hts, -⟩)
      · exact absurd hk (hnt i _ h)
      · cases hts

/-- **The invariant along a semantic trace from a start configuration**, and
`owner` at each step. -/
theorem trace_invP {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) : ∀ i, InvP fuel N x o c (tr.cfg i)
  | 0 => h0 ▸ inv_init hs
  | i + 1 => by
    have h := trace_invP hs tr h0 i
    rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
    · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact (inv_step h ht hst).1
    · rw [he]; exact h

theorem trace_o {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
    (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) :
    (fv (tr.cfg (i + 1)).mem o = fv (tr.cfg i).mem o ∧
      (tr.cfg (i + 1)).mem.lastWrite (L4 o) = (tr.cfg i).mem.lastWrite (L4 o)) ∨
      fv (tr.cfg (i + 1)).mem o = fv (tr.cfg i).mem o + 1 := by
  rcases tr.step i with ⟨tid, hst⟩ | ⟨-, he⟩
  · obtain ⟨t, ht⟩ : ∃ t, (tr.cfg i).threads[tid]? = some t := by
      rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
    exact (inv_step (trace_invP hs tr h0 i) ht hst).2
  · rw [he]; exact .inl ⟨rfl, rfl⟩

end Kraken.Promising.Live.TicketInvP
