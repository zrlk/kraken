/-
**Repeated-acquire ticket-lock liveness on the semantic
machine, promises included** (`ticket_loop_live_sem`), on a valid layout of
`tkLoopWorker`.

On a semantic trace from a start configuration, `TicketLoopInvP.LInv`
holds at every index; write `M` for the value of `owner`. It never decreases
and is at most `N * k`, so it is eventually constant, and then so is its last
write.

**Every fair trace reaches a final configuration** (`final_reached`). If not,
some thread `U` steps infinitely often, hence takes infinitely many
instruction steps (`TraceSem.instr_inf`). Its rank `20 · X7 + rk pc` never
grows, so `U` eventually spins forever with a ticket `K` (`spin_eventually`).

- `K ≤ M` is impossible (`spin_le_false`). If `K < M`, `U`'s own `owner`
  message of value `K + 1` is an outstanding promise (`OH`), and memory
  fairness brings `U`'s `coh` of `owner` past it: a dead promise (`NoDead`).
  If `K = M`, memory fairness makes `U` read `M` and leave its spin loop.
- So `K > M`, and the `next` message of value `M + 1` has a writer `H` that
  holds ticket `M` (`HoldsV`) from then on. If `H` steps infinitely often, it
  too spins forever with some `K' > M`, and its certification after a step
  cannot leave the spin loop (`spin_stuck`: no `owner` value `K'` to read),
  so it has no promise, and `HoldsV` says `K' = M`. If `H` stops stepping, its
  last certification writes nothing fresh (F3, `holder_nacertV`), so it
  replays against every later memory (`nacert_replay_loop`): `H` is
  instruction-enabled forever, and weak fairness makes it step.

At a final configuration every worker is at its end with `X7 = 0`: it has
finished (`ticket_loop_finish_sem`), and a thread that waited in round `r`
(with `X7 ≠ 0`) has acquired in round `r` (`ticket_loop_starve_sem`).
`final_reached` is also `TicketLoopTermSem` (`ticket_loop_term_sem`).

The concrete instance `ticket_loop_live_sem_concrete` fixes the layout
`TicketLoopPF.tkLoopLayout`.
-/
import Kraken.Promising.LiveTicketLoopInvP
import Kraken.Promising.LiveTicketLoopPF

namespace Kraken.Promising.Live.TicketLoopSem

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketLoopInv Kraken.Promising.Live.TicketLoopHolder Kraken.Promising.Live.TicketLoopCert
open Kraken.Promising.Live.TicketLoopInvP
open Kraken.Promising.Live.TicketLoopPF (nextPc rk rk_le rk_lt spin_facts held_ne17 cs_facts next_spin nextPc_mem
  tkLoopLayout tkLoopValid)
open Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape Kraken.Promising.Live.LoopFacts
open Kraken.Promising.Live.SpinSwpStep (getCoh_congr)
open Kraken.Promising.Live.TicketInv (wn L4)
open Kraken.Promising.Live.TicketTrees (w32)
open Kraken.Promising.SLR.A64Trees (At goto)

set_option linter.unusedSectionVars false

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkLoopWorker).addrOf

/-! ## One step, any promise set -/

/-- **The position and registers after a step, with any promise set**
(`TicketLoopPF.pos_step_st` on `TI`): the next position, `X3` kept except at the
`LDADDA`, `X7` kept except at the `SUB`, which lowers it by one. -/
theorem pos_step' {k : Nat} {x o c : BitVec 64} {u : Thread isa} {A : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : TI k x o c A u mem) {p : Nat}
    (hp : p ∈ tkLoopPcs) (hpc : u.st.st.2 = pcA p) (hs : stepOne Arch.armv8 u A mem = some outs)
    (ho : .ok oc ∈ outs) :
    oc.thread.st.st.2 = pcA (nextPc u.st.st.1.status.z (decide (wn u.st.st.1.regs.X7 = 0)) p) ∧
      (p ≠ 4 → oc.thread.st.st.1.regs.X3 = u.st.st.1.regs.X3) ∧
      (p ≠ 14 → oc.thread.st.st.1.regs.X7 = u.st.st.1.regs.X7) ∧
      (p = 14 → wn oc.thread.st.st.1.regs.X7 + 1 = wn u.st.st.1.regs.X7) :=
  TicketLoopPF.pos_step_st h.sinv.st hp hpc (fun e => by subst e; exact h.x7 14 (by decide) hpc) hs ho

/-- **A step of the loop worker that keeps memory replays against a larger
memory** (`TicketSolo.replay_tk` on the loop worker's positions). -/
theorem replay_loop {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv x o c t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.armv8 t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.armv8 t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  obtain ⟨hSt, p, hpp, hpc⟩ := hS
  have hA : p ≠ 17 → At tkLoopWorker t.st p := fun h17 => hSt.at hpp h17 hpc
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replay_done _ _ hp hb hs ho hm (exec_mov _ (hA (by decide)))
  · exact replay_done _ _ hp hb hs ho hm (exec_cbz _ (hA (by decide)))
  · exact replay_rmw _ _ hp hb hs ho hm rfl (exec_ldadda _ (hA (by decide)) hSt.x0 hSt.dx)
  · exact replay_load _ _ hp hb hs ho hm (exec_ldar _ (hA (by decide)) hSt.x1 hSt.dO)
  · exact replay_done _ _ hp hb hs ho hm (exec_cmp _ (hA (by decide))).choose_spec.1
  · exact replay_done _ _ hp hb hs ho hm (exec_bne _ (hA (by decide)))
  · exact replay_load _ _ hp hb hs ho hm (exec_ldr_c _ (hA (by decide)) hSt.x2 hSt.dc)
  · exact replay_done _ _ hp hb hs ho hm (exec_add5 _ (hA (by decide)))
  · exact replay_store _ _ hp hb hs ho hm (exec_str_c _ (hA (by decide)) hSt.x2 hSt.dc)
  · exact replay_done _ _ hp hb hs ho hm (exec_add4 _ (hA (by decide)))
  · exact replay_store _ _ hp hb hs ho hm (exec_stlr _ (hA (by decide)) hSt.x1 hSt.dO)
  · exact replay_done _ _ hp hb hs ho hm (exec_sub _ (hA (by decide)))
  · exact replay_done _ _ hp hb hs ho hm (exec_b_round _ (hA (by decide)))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem nacert_replay_loop {x o c : BitVec 64} {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.armv8 tid n p q → p.2 = q.2 → SInv x o c p.1.st → p.1.Bnd p.2.last →
    ∀ mem, p.2.Prefix mem → ThreadNPn Arch.armv8 tid n (p.1, mem) (q.1, mem) :=
  nacertG_replay (SInv x o c) (fun hS hs ho => (step_sinv hS hs ho).1)
    (fun hS hb hp hs ho hm => replay_loop hS hb hp hs ho hm)

/-- **A spinning worker whose ticket is not readable in `owner` empties no
promise alone**: its certification stays in the spin loop (leaving it needs
the `Z` flag, hence a readable `owner` value equal to its ticket, `TI.f8`),
where no step changes memory or promises. -/
theorem spin_stuck {k : Nat} {x o c : BitVec 64} {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] → TI k x o c tid p.1 p.2 →
    (∃ i ∈ [6, 7, 8], p.1.st.st.2 = pcA i) →
    (∀ tr v, p.2.read? (L4 o) tr = some v → v.toNat % 2 ^ 32 ≠ tk p.1) → p.1.prom = [] := by
  intro n p q h
  induction h with
  | refl => intro hq _ _ _; exact hq
  | @step n p q r hs h ih =>
    intro hq hti hsp hrd
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have hti' := (step_ti hti hs ho).1
    have hS := hti.sinv.st
    obtain ⟨i, hi, hpc⟩ := hsp
    have keep : oc.thread.st.st.1.regs.X3 = p.1.st.st.1.regs.X3 → oc.mem = p.2 →
        ∀ tr v, oc.mem.read? (L4 o) tr = some v → v.toNat % 2 ^ 32 ≠ tk oc.thread := by
      intro h3 hm tr v hr
      unfold tk; rw [h3, hm] at *; exact hrd tr v hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · obtain ⟨ts, v, hst, -, -, hm, hpr, -⟩ := s6 hS hs ho hpc
      rw [← hpr]
      exact ih hq hti' ⟨7, by decide, by rw [hst] <;> rfl⟩ (keep (by rw [hst] <;> rfl) hm)
    · obtain ⟨sf, hst, -, hm, hpr, -⟩ := s7 hS hs ho hpc
      rw [← hpr]
      exact ih hq hti' ⟨8, by decide, by rw [hst] <;> rfl⟩ (keep (by rw [hst] <;> rfl) hm)
    · obtain ⟨hm, hst, hpr, -⟩ := s8 hS hs ho hpc
      by_cases hz : p.1.st.st.1.status.z = true
      · obtain ⟨tr, v, hr, hv, -⟩ := hti.f8 hpc hz
        exact (hrd tr v hr hv).elim
      · rw [ite_eq_right hz] at hst
        rw [← hpr]
        exact ih hq hti' ⟨6, by decide, by rw [hst] <;> rfl⟩ (keep (by rw [hst] <;> rfl) hm)

/-! ## Final configurations -/

theorem final_thread {c : Config isa} (hf : c.final = true) {tid : Nat} {t : Thread isa}
    (ht : c.threads[tid]? = some t) : t.halted = true ∧ t.prom = [] := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  have := (Array.all_eq_true.mp hf) tid hlt
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  exact this

/-- **At a final configuration a worker is at its end.** -/
theorem final_pc {x o c : BitVec 64} {cfg : Config isa} (hf : cfg.final = true) (hb : cfg.Bnd) {tid : Nat}
    {t : Thread isa} (ht : cfg.threads[tid]? = some t) (hS : SInv x o c t.st) : t.st.st.2 = pcA 17 := by
  obtain ⟨hh, hp0⟩ := final_thread hf ht
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨outs, oc, hs, -, -⟩ := en_nil (A := tid) hS hp0 (hb tid t ht) hne
  simp only [Thread.halted, Option.isNone_iff_eq_none] at hh
  simp [stepOne, hh] at hs

omit hv in
/-- **A final configuration stays.** -/
theorem final_stay {fuel : Nat} (tr : TraceSem Arch.armv8 fuel isa) {f : Nat} (hf : (tr.cfg f).final = true) :
    ∀ j, f ≤ j → tr.cfg j = tr.cfg f := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step j _ ih =>
    rcases tr.step j with ⟨tid, hst⟩ | ⟨-, he⟩
    · exact absurd ⟨_, hst⟩ (not_enabledSem_of_final (ih ▸ hf))
    · rw [he, ih]

/-! ## Along a semantic trace -/

/-- Thread `V` spins from `n` on with ticket `K`. -/
def SpinFrom (cfg : Nat → Config isa) (V n K : Nat) : Prop :=
  ∀ j, n ≤ j → ∃ u, (cfg j).threads[V]? = some u ∧ (∃ p ∈ [6, 7, 8], u.st.st.2 = pcA p) ∧ tk u = K

/-- A holder of ticket `M` has a `next` message of value `M + 1`. -/
theorem holdsV_le {k N : Nat} {x o c : BitVec 64} {cfg : Config isa} (h : LInv k N x o c cfg) {H M : Nat}
    {u : Thread isa} (hu : cfg.threads[H]? = some u) (hh : HoldsV x H u cfg.mem M) (hM : M < 2 ^ 32) :
    M + 1 ≤ fv cfg.mem x := by
  have key : ∀ ts w, cfg.mem.get? ts = some w → w.loc = L4 x → w.val.toNat = (M + 1) % 2 ^ 32 →
      M + 1 ≤ fv cfg.mem x := fun ts w hw hl hv => by
    have := h.xv' hw hl
    obtain ⟨v, -, hv', -⟩ := h.xheld ts w hw hl
    omega
  rcases hh with ⟨hk, htk⟩ | ⟨ts, -, w, hw, hl, -, hv⟩
  · obtain ⟨ts, -, w, hw, hl, -, hv⟩ := (h.thr H u hu).ti.txn hk
    exact key ts w hw hl (by rw [hv, htk])
  · exact key ts w hw hl hv

section Trace

variable {fuel k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.armv8 fuel isa}

omit hv in
/-- A step of `H` leaves it certifiable. -/
theorem stepSem_cert {c c' : Config isa} {H : Nat} (h : StepSem Arch.armv8 fuel H c c') :
    ∃ u, c'.threads[H]? = some u ∧ CertOkN Arch.armv8 H u c'.mem fuel := by
  rcases h with ⟨t, outs, oc, ht, -, -, hc, rfl⟩ | ⟨t, w, ht, -, hc, rfl⟩
  · exact ⟨_, withThread_get_self ht, hc⟩
  · exact ⟨_, withThread_get_self ht, hc⟩

omit hv in
/-- A step of another thread leaves `H` alone. -/
theorem stepSem_ne {c c' : Config isa} {tid H : Nat} (h : StepSem Arch.armv8 fuel tid c c') (e : tid ≠ H) :
    c'.threads[H]? = c.threads[H]? := by
  rcases h with ⟨t, outs, oc, ht, -, -, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · exact withThread_get_ne ht (Ne.symm e)
  · exact withThread_get_ne ht (Ne.symm e)

omit hv in
/-- **A thread is in its initial state, or certifiable at the index after its
last step.** -/
theorem cert_or_init (H : Nat) : ∀ j {u : Thread isa}, (tr.cfg j).threads[H]? = some u →
    (tr.cfg 0).threads[H]? = some u ∨
      ∃ j0 ≤ j, (tr.cfg j0).threads[H]? = some u ∧ CertOkN Arch.armv8 H u (tr.cfg j0).mem fuel
  | 0, u, hu => .inl hu
  | j + 1, u, hu => by
    have ih : (tr.cfg j).threads[H]? = some u → (tr.cfg 0).threads[H]? = some u ∨
        ∃ j0 ≤ j + 1, (tr.cfg j0).threads[H]? = some u ∧ CertOkN Arch.armv8 H u (tr.cfg j0).mem fuel :=
      fun h => (cert_or_init H j h).imp_right fun ⟨j0, hj0, h1, h2⟩ => ⟨j0, by omega, h1, h2⟩
    rcases tr.step j with ⟨tid, hst⟩ | ⟨-, he⟩
    · by_cases e : tid = H
      · subst e
        obtain ⟨u', hu', hc⟩ := stepSem_cert hst
        rw [hu] at hu'; cases hu'
        exact .inr ⟨j + 1, Nat.le_refl _, hu, hc⟩
      · exact ih (by rw [← hu]; exact (stepSem_ne hst e).symm)
    · exact ih (by rw [he] at hu; exact hu)

omit hv in
/-- A thread that never steps from `j1` on keeps its state. -/
theorem const_of_nostep {H j1 : Nat}
    (hno : ∀ j, j1 ≤ j → ¬ StepSem Arch.armv8 fuel H (tr.cfg j) (tr.cfg (j + 1))) :
    ∀ j, j1 ≤ j → (tr.cfg j).threads[H]? = (tr.cfg j1).threads[H]? := by
  intro j hj
  induction hj with
  | refl => rfl
  | @step j hj ih =>
    rw [← ih]
    rcases tr.step j with ⟨tid, hst⟩ | ⟨-, he⟩
    · by_cases e : tid = H
      · subst e; exact absurd hst (hno j hj)
      · exact stepSem_ne hst e
    · rw [he]

variable (hs : TkLoopStart k N x o c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
include hs h0

theorem ti_at {T j : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[T]? = some u) :
    TI k x o c T u (tr.cfg j).mem :=
  ((trace_linv hs tr h0 j).thr T u hu).ti

/-- `owner` never decreases. -/
theorem Mo_mono (i j : Nat) (hij : i ≤ j) : fv (tr.cfg i).mem o ≤ fv (tr.cfg j).mem o := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step j _ ih => show _ ≤ fv (tr.cfg (j + 1)).mem o; rcases trace_o hs tr h0 j with ⟨e, -⟩ | e <;> omega

/-- **A thread taking infinitely many instruction steps eventually spins
forever**: its rank `20 · X7 + rk pc` never grows, drops at each step outside
the spin loop and when it leaves it. -/
theorem spin_eventually {V : Nat}
    (hinf : InfOften fun j => InstrSem Arch.armv8 fuel V (tr.cfg j) (tr.cfg (j + 1)))
    {j : Nat} {u : Thread isa} (hu : (tr.cfg j).threads[V]? = some u) : ∃ n K, j ≤ n ∧ SpinFrom tr.cfg V n K := by
  suffices H : ∀ v j u p, (tr.cfg j).threads[V]? = some u → p ∈ tkLoopPcs → u.st.st.2 = pcA p →
      20 * wn u.st.st.1.regs.X7 + rk p ≤ v → ∃ n K, j ≤ n ∧ SpinFrom tr.cfg V n K by
    obtain ⟨-, p, hp, hpc⟩ := (ti_at hs h0 hu).sinv
    exact H _ j u p hu hp hpc (Nat.le_refl _)
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
  intro j u p hu hp hpc hv
  by_cases hsp : p ∈ [6, 7, 8]
  · by_cases hall : SpinFrom tr.cfg V j (tk u)
    · exact ⟨j, tk u, Nat.le_refl _, hall⟩
    -- leaving the spin loop lowers the rank
    have hrk := (spin_facts p hsp).2.2.2.2
    have stay : ∀ d, (∃ u', (tr.cfg (j + d)).threads[V]? = some u' ∧ (∃ q ∈ [6, 7, 8], u'.st.st.2 = pcA q) ∧
        tk u' = tk u ∧ u'.st.st.1.regs.X7 = u.st.st.1.regs.X7) ∨
        ∃ j' u' q, j ≤ j' ∧ (tr.cfg j').threads[V]? = some u' ∧ q ∈ tkLoopPcs ∧ u'.st.st.2 = pcA q ∧
          20 * wn u'.st.st.1.regs.X7 + rk q < v := by
      intro d
      induction d with
      | zero => exact .inl ⟨u, hu, ⟨p, hsp, hpc⟩, rfl, rfl⟩
      | succ d ihd =>
        rcases ihd with ⟨u', hu', ⟨q, hq, hqc⟩, h3, h7⟩ | h
        · rcases tr.same_or_instr (j + d) V hu' with ⟨u'', hu'', e1, -⟩ | ⟨outs, oc, hso, ho, he⟩
          · exact .inl ⟨u'', hu'', ⟨q, hq, by rw [e1]; exact hqc⟩, by unfold tk; rw [e1]; exact h3,
              by rw [e1]; exact h7⟩
          · obtain ⟨hqt, hq4, hq14, -⟩ := spin_facts q hq
            obtain ⟨hn, h3', h7', -⟩ := pos_step' (ti_at hs h0 hu') hqt hqc hso ho
            have hu'' := tr.wt_self hu' he
            have e3 : tk oc.thread = tk u := by unfold tk; rw [h3' hq4]; exact h3
            have e7 := (h7' hq14).trans h7
            rcases next_spin u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) q hq with hq' | hq'
            · exact .inl ⟨oc.thread, hu'', ⟨_, hq', hn⟩, e3, e7⟩
            · refine .inr ⟨j + d + 1, oc.thread, 9, by omega, hu'', by decide, by rw [hn, hq'], ?_⟩
              rw [e7]; simp only [rk]; omega
        · exact .inr h
    obtain ⟨j', hj', hn⟩ : ∃ j', j ≤ j' ∧ ¬ ∃ u', (tr.cfg j').threads[V]? = some u' ∧
        (∃ q ∈ [6, 7, 8], u'.st.st.2 = pcA q) ∧ tk u' = tk u :=
      Classical.byContradiction fun hc => hall fun j' hj' =>
        Classical.byContradiction fun hn => hc ⟨j', hj', hn⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
    rcases stay d with ⟨u', hu', hq, h3, -⟩ | ⟨j'', u', q, hj'', hu', hq, hqc, hlt⟩
    · exact absurd ⟨u', hu', hq, h3⟩ hn
    · obtain ⟨n, K, hn', hsp'⟩ := ih _ hlt j'' u' q hu' hq hqc (Nat.le_refl _)
      exact ⟨n, K, by omega, hsp'⟩
  · -- any other position: the next step lowers the rank
    obtain ⟨k', hk', u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
    have hpc' : u'.st.st.2 = pcA p := by rw [e1]; exact hpc
    have h17 : p ≠ 17 := by
      rintro rfl; rw [stepOne_end (ti_at hs h0 hu').sinv.st hpc'] at hso; cases hso
    obtain ⟨hn, -, h7, h14⟩ := pos_step' (ti_at hs h0 hu') hp hpc' hso ho
    have hq := nextPc_mem u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) p hp
    have e7 : u'.st.st.1.regs.X7 = u.st.st.1.regs.X7 := by rw [e1]
    have hlt : 20 * wn oc.thread.st.st.1.regs.X7 +
        rk (nextPc u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) p) < v := by
      by_cases h14' : p = 14
      · subst h14'
        have := h14 rfl
        have : nextPc u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) 14 = 15 := rfl
        rw [this]; simp only [rk] at hv ⊢; rw [e7] at *; omega
      · have := rk_lt u'.st.st.1.status.z (decide (wn u'.st.st.1.regs.X7 = 0)) p hp hsp h14' h17
        have e7' : wn u'.st.st.1.regs.X7 = wn u.st.st.1.regs.X7 := by rw [e7]
        rw [h7 h14']; omega
    obtain ⟨n, K, hn', hsp'⟩ := ih _ hlt (k' + 1) _ _ (tr.wt_self hu' he) hq hn (Nat.le_refl _)
    exact ⟨n, K, by omega, hsp'⟩

/-! ## A spinner's ticket is above the final `owner` -/

section Owner

variable {n M : Nat} (hM : ∀ j, n ≤ j → fv (tr.cfg j).mem o = M)
  (hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg n).mem.lastWrite (L4 o))
include hM hL

/-- **A thread spinning forever with ticket `K ≤ M` is impossible** (memory
fairness). It reads `owner` infinitely often, so at some point its `coh` of
`owner` is past the last write. If `K < M`, its `owner` message of value
`K + 1` is an outstanding promise below that `coh`: dead. If `K = M`, its
next `LDAR` reads `M` and it leaves the spin loop. -/
theorem spin_le_false {U nU K : Nat}
    (hinf : InfOften fun j => InstrSem Arch.armv8 fuel U (tr.cfg j) (tr.cfg (j + 1)))
    (hsp : SpinFrom tr.cfg U nU K) (hK : K ≤ M) (hmf : MemFair Arch.armv8 tr.cfg) : False := by
  have hn : n ≤ max n nU := Nat.le_max_left _ _
  have hnU : nU ≤ max n nU := Nat.le_max_right _ _
  have out : ∀ j, nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → ∀ q ∈ tkLoopPcs, q ∉ [6, 7, 8] →
      u.st.st.2 = pcA q → False := by
    intro j hj u hu q hq hq' hpc
    obtain ⟨u', hu', ⟨p, hp, hpc'⟩, -⟩ := hsp j hj
    rw [hu] at hu'; cases hu'
    have := addrOf_inj hq (spin_facts p hp).1 (hpc.symm.trans hpc')
    subst this; exact hq' hp
  have tkU : ∀ j, nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → tk u = K := fun j hj u hu => by
    obtain ⟨u', hu', -, h⟩ := hsp j hj; rw [hu] at hu'; cases hu'; exact h
  -- `U` reads `owner` infinitely often
  have r6 : ∀ j, nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 6 →
      ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg U (L4 o) ts k := by
    intro j hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
    obtain ⟨ts, v, -, -, -, -, -, ⟨ν, hlog⟩, -⟩ := s6 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
    exact ⟨k, hk, ts, u', outs, oc, hu', hso, ho, he, v, ν, hlog⟩
  have r8 : ∀ j, nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 8 →
      ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg U (L4 o) ts k := by
    intro j hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
    obtain ⟨-, hst, -⟩ := s8 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
    cases hz : u'.st.st.1.status.z
    · obtain ⟨k', hk', h⟩ := r6 (k + 1) (by omega) _ (tr.wt_self hu' he) (by rw [hst, hz]; rfl)
      exact ⟨k', by omega, h⟩
    · exact (out (k + 1) (by omega) _ (tr.wt_self hu' he) 9 (by decide) (by decide) (by rw [hst, hz]; rfl)).elim
  have reads : InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg U (L4 o) ts i) := by
    intro j0
    obtain ⟨u, hu, ⟨p, hp, hpc⟩, -⟩ := hsp (max nU j0) (Nat.le_max_left _ _)
    have hj0 := Nat.le_max_right nU j0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨k, hk, h⟩ := r6 _ (Nat.le_max_left _ _) u hu hpc; exact ⟨k, by omega, h⟩
    · obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
      obtain ⟨sf, hst, -⟩ := s7 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
      obtain ⟨k', hk', h⟩ := r8 (k + 1) (by omega) _ (tr.wt_self hu' he) (by rw [hst])
      exact ⟨k', by omega, h⟩
    · obtain ⟨k, hk, h⟩ := r8 _ (Nat.le_max_left _ _) u hu hpc; exact ⟨k, by omega, h⟩
  obtain ⟨u0, hu0, -⟩ := hsp (max n nU) hnU
  refine memFair_lastWrite_false hmf reads hu0 fun j hj t ht hc => ?_
  rcases Nat.lt_or_ge K M with hlt | hge
  · -- a dead promise
    have hLj : (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg (max n nU)).mem.lastWrite (L4 o) :=
      (hL j (by omega)).trans (hL _ hn).symm
    have I := trace_linv hs tr h0 j
    have hti := ti_at hs h0 ht
    obtain ⟨⟨p, hp, hpc⟩, htk⟩ : (∃ p ∈ [6, 7, 8], t.st.st.2 = pcA p) ∧ tk t = K := by
      obtain ⟨u', hu', h1, h2⟩ := hsp j (by omega); rw [ht] at hu'; cases hu'; exact ⟨h1, h2⟩
    have hk := (ticketed_iff (spin_facts p hp).1 hpc).mpr (spin_facts p hp).2.2.2.1
    have hfo := hM j (by omega)
    have := I.fo_le; have := I.fx32
    obtain ⟨ts', w', hw', hl', hv'⟩ := I.osurj K (by omega)
    obtain ⟨ts'', w'', hw'', hl'', hid'', hv''⟩ := I.oown ts' w' hw' hl'
    obtain ⟨ts1, -, w1, hw1, hl1, hid1, hv1⟩ := hti.txn hk
    have e := I.xinj ts'' ts1 w'' w1 hw'' hw1 hl'' hl1 (by rw [hv'', hv1, htk, hv']; omega)
    subst e; rw [hw1] at hw''; cases hw''
    have hin := (I.thr U t ht).oh ts' w' hw' hl' (hid''.symm.trans hid1) K (by omega) (.inl ⟨hk, htk⟩)
    have hd := (I.thr U t ht).nd ts' hin w' hw'
    have hle : ts' ≤ (tr.cfg j).mem.lastWrite (L4 o) := Nat.le_of_not_lt fun hgt =>
      (tr.cfg j).mem.not_write_of_lastWrite_lt (L4 o) hgt hw' hl'
    rw [hl'] at hd; omega_t
  · -- `U` reads `M` and leaves its spin loop
    have hKM : K = M := by omega
    have p8z : ∀ j, max n nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 8 →
        u.st.st.1.status.z = true → False := by
      intro j hj u hu hpc hz
      obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
      obtain ⟨-, hst, -⟩ := s8 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
      rw [e1, hz] at hst
      exact out (k + 1) (by omega) _ (tr.wt_self hu' he) 9 (by decide) (by decide) (by rw [hst]; rfl)
    have p7 : ∀ j, max n nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 7 →
        wn u.st.st.1.regs.X4 = M → False := by
      intro j hj u hu hpc h4
      obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
      have h3 := tkU k (by omega) u' hu'
      obtain ⟨sf, hst, hz, -⟩ := s7 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
      unfold tk at h3
      refine p8z (k + 1) (by omega) _ (tr.wt_self hu' he) (by rw [hst]) ?_
      rw [hst]; exact hz.mpr (by rw [e1, h4, ← e1]; exact (h3.trans hKM).symm)
    have p6 : ∀ j, max n nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 6 →
        (tr.cfg (max n nU)).mem.lastWrite (L4 o) ≤ u.views.getCoh (L4 o) → False := by
      intro j hj u hu hpc hc
      obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
      obtain ⟨ts, v, hst, -, hv, -⟩ := s6 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
      have hv := hv (by rw [hL k (by omega), ← hL _ hn, e2]; exact hc)
      have hm : fv (tr.cfg k).mem o = M := hM k (by omega)
      have I := trace_linv hs tr h0 k
      have := I.fo_le; have := I.fx32
      refine p7 (k + 1) (by omega) _ (tr.wt_self hu' he) (by rw [hst]) ?_
      rw [hst]; show (BitVec.setWidth 64 (BitVec.setWidth 32 v)).toNat % 2 ^ 32 = M
      rw [hv]; simp [BitVec.toNat_setWidth]
      omega
    have p8 : ∀ j, max n nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 8 →
        (tr.cfg (max n nU)).mem.lastWrite (L4 o) ≤ u.views.getCoh (L4 o) → False := by
      intro j hj u hu hpc hc
      obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
      obtain ⟨-, hst, -, hcoh⟩ := s8 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
      cases hz : u'.st.st.1.status.z
      · refine p6 (k + 1) (by omega) _ (tr.wt_self hu' he) (by rw [hst, hz]; rfl) ?_
        rw [getCoh_congr hcoh, e2]; exact hc
      · exact p8z k (by omega) u' hu' (by rw [e1]; exact hpc) hz
    have p7' : ∀ j, max n nU ≤ j → ∀ u, (tr.cfg j).threads[U]? = some u → u.st.st.2 = pcA 7 →
        (tr.cfg (max n nU)).mem.lastWrite (L4 o) ≤ u.views.getCoh (L4 o) → False := by
      intro j hj u hu hpc hc
      obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := tr.adv hinf hu
      obtain ⟨sf, hst, -, -, -, hcoh⟩ := s7 (ti_at hs h0 hu').sinv.st hso ho (by rw [e1]; exact hpc)
      refine p8 (k + 1) (by omega) _ (tr.wt_self hu' he) (by rw [hst]) ?_
      rw [getCoh_congr hcoh, e2]; exact hc
    obtain ⟨u', hu', ⟨p, hp, hpc⟩, -⟩ := hsp j (by omega)
    rw [ht] at hu'; cases hu'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact p6 j hj t ht hpc hc
    · exact p7' j hj t ht hpc hc
    · exact p8 j hj t ht hpc hc

end Owner

/-! ## Every fair trace terminates -/

/-- **Every semantic trace from a start configuration under weak and memory
fairness reaches a final configuration.** -/
theorem final_reached (hwf : WeakFairSem Arch.armv8 fuel tr.cfg) (hmf : MemFair Arch.armv8 tr.cfg) :
    ∃ f, (tr.cfg f).final = true := by
  refine Classical.byContradiction fun hnf => ?_
  have hstep : ∀ j, ∃ tid, StepSem Arch.armv8 fuel tid (tr.cfg j) (tr.cfg (j + 1)) := fun j => by
    rcases tr.step j with h | ⟨hf, -⟩
    · exact h
    · exact absurd ⟨j, hf⟩ hnf
  have hwfi := weakFairInstrSem_loop hs tr h0 hwf
  have hinstr : ∀ V, InfOften (fun j => StepSem Arch.armv8 fuel V (tr.cfg j) (tr.cfg (j + 1))) →
      InfOften (fun j => InstrSem Arch.armv8 fuel V (tr.cfg j) (tr.cfg (j + 1))) := fun V h =>
    tr.instr_inf (B := 1) (fun i tid t ht => dropBounded_of_sinv (trace_sinv hs tr h0 i tid t ht)) (n := 0)
      (fun j _ => hstep j) h
  -- `owner` is eventually constant (at most `N * k`), and so is its last write
  obtain ⟨n, -, hc⟩ := SpinCommon.evconst (fun j => fv (tr.cfg j).mem o) (Mo_mono hs h0) (N * k) 0 fun j _ => by
    have I := trace_linv hs tr h0 j; have := I.fo_le; have := I.fx_le; omega
  obtain ⟨M, hMdef⟩ : ∃ M, fv (tr.cfg n).mem o = M := ⟨_, rfl⟩
  have hM : ∀ j, n ≤ j → fv (tr.cfg j).mem o = M := fun j hj => (hc j hj).trans hMdef
  have hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg n).mem.lastWrite (L4 o) := by
    intro j hj
    induction hj with
    | refl => rfl
    | @step j hle ih =>
      rcases trace_o hs tr h0 j with ⟨-, e⟩ | e
      · exact e.trans ih
      · have h1 := hM (j + 1) (Nat.le_succ_of_le hle); have h2 := hM j hle; omega
  have hM32 : M + 1 < 2 ^ 32 := by
    have I := trace_linv hs tr h0 n; have := I.fo_le; have := I.fx32; omega
  -- a thread stepping infinitely often spins forever with a ticket above `M`
  have above : ∀ V, InfOften (fun j => StepSem Arch.armv8 fuel V (tr.cfg j) (tr.cfg (j + 1))) →
      ∃ nV KV, n ≤ nV ∧ SpinFrom tr.cfg V nV KV ∧ M < KV := by
    intro V hV
    obtain ⟨j, -, hj⟩ := hV 0
    obtain ⟨u, hu⟩ : ∃ u, (tr.cfg j).threads[V]? = some u := by
      rcases hj with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
    obtain ⟨nV, KV, -, hsp⟩ := spin_eventually hs h0 (hinstr V hV) hu
    refine ⟨max n nV, KV, Nat.le_max_left _ _, fun j hj => hsp j (by omega), Nat.lt_of_not_le fun hle => ?_⟩
    exact spin_le_false hs h0 hM hL (hinstr V hV) hsp hle hmf
  -- some thread steps infinitely often
  have hsz : ∀ j, (tr.cfg j).threads.size = N := fun j => (trace_linv hs tr h0 j).size
  obtain ⟨U, -, hU⟩ := infOften_pigeon (fun tid j => StepSem Arch.armv8 fuel tid (tr.cfg j) (tr.cfg (j + 1))) N 0
    fun j _ => by
      obtain ⟨tid, hst⟩ := hstep j
      obtain ⟨t, ht⟩ : ∃ t, (tr.cfg j).threads[tid]? = some t := by
        rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
      exact ⟨tid, by rw [← hsz j]; exact (Array.getElem?_eq_some_iff.mp ht).1, hst⟩
  obtain ⟨nU, KU, hnU, hspU, hKU⟩ := above U hU
  -- the `next` message of value `M + 1`, and its writer, which holds `M` from then on
  obtain ⟨u0, hu0, ⟨p0, hp0, hpc0⟩, htk0⟩ := hspU nU (Nat.le_refl _)
  have I0 := trace_linv hs tr h0 nU
  have hk0 := (ticketed_iff (spin_facts p0 hp0).1 hpc0).mpr (spin_facts p0 hp0).2.2.2.1
  have := holdsV_le I0 hu0 (.inl ⟨hk0, htk0⟩) (htk0 ▸ tk_lt u0)
  obtain ⟨ts, w, hw, hl, hv⟩ := I0.xsurj M (by omega)
  have hno : ∀ j ts w, (tr.cfg j).mem.get? ts = some w → w.loc = L4 o → w.val.toNat ≠ M + 1 := by
    intro j ts w hw hl e
    have := (trace_linv hs tr h0 (max j n)).ov' (tr.get_le (Nat.le_max_left _ _) hw) hl
    rw [hM _ (Nat.le_max_right _ _)] at this; omega
  have hold : ∀ j, nU ≤ j → ∃ u, (tr.cfg j).threads[w.tid]? = some u ∧ HoldsV x w.tid u (tr.cfg j).mem M := by
    intro j hj
    obtain ⟨v, u, hv', hu, hh⟩ := (trace_linv hs tr h0 j).xheld ts w (tr.get_le hj hw) hl
    obtain rfl : v = M := by omega
    exact ⟨u, hu, hh.resolve_left fun ⟨ts', w', hw', hl', hv''⟩ => hno j ts' w' hw' hl' hv''⟩
  by_cases hH : InfOften (fun j => StepSem Arch.armv8 fuel w.tid (tr.cfg j) (tr.cfg (j + 1)))
  · -- the holder spins forever above `M`; after a step it certifies, so it has no promise
    obtain ⟨nH, KH, hnH, hspH, hKH⟩ := above w.tid hH
    obtain ⟨j, hj, hst⟩ := hH (max nU nH)
    obtain ⟨u, hu, hc⟩ := stepSem_cert hst
    obtain ⟨u', hu', hsp', htk'⟩ := hspH (j + 1) (by omega)
    rw [hu] at hu'; cases hu'
    obtain ⟨u'', hu'', hh⟩ := hold (j + 1) (by omega)
    rw [hu] at hu''; cases hu''
    have I := trace_linv hs tr h0 (j + 1)
    obtain ⟨tq, mq, hr, hq⟩ := hc
    have hp0 := spin_stuck (p := (u, (tr.cfg (j + 1)).mem)) hr hq (I.thr _ u hu).ti hsp' fun tr' v hr' hv' => by
      have := I.ov tr' v hr'; have := hM (j + 1) (by omega); have := Nat.mod_le v.toNat (2 ^ 32)
      dsimp only at hv'; omega
    rcases hh with ⟨-, htk⟩ | ⟨ts', hts', -⟩
    · omega
    · rw [hp0] at hts'; cases hts'
  · -- the holder stops stepping; its last certification replays, so it is enabled forever
    obtain ⟨j1, hj1⟩ : ∃ j1, ∀ j, j1 ≤ j → ¬ StepSem Arch.armv8 fuel w.tid (tr.cfg j) (tr.cfg (j + 1)) :=
      Classical.byContradiction fun hc => hH fun m => Classical.byContradiction fun hm =>
        hc ⟨m, fun j hj hs => hm ⟨j, hj, hs⟩⟩
    obtain ⟨u, hu, hh⟩ := hold (max j1 nU) (Nat.le_max_right _ _)
    have hconst : ∀ j, max j1 nU ≤ j → (tr.cfg j).threads[w.tid]? = some u := fun j hj => by
      rw [const_of_nostep (fun j' hj' => hj1 j' (by omega)) j hj]; exact hu
    rcases cert_or_init w.tid (max j1 nU) hu with hi | ⟨j0, hj0, hu0, hc0⟩
    · -- not the initial state
      rw [h0] at hi
      simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hi
      obtain ⟨s, hs', rfl⟩ := hi
      have hpc : (Thread.init s : Thread isa).st.st.2 = pcA 1 :=
        ((hs.hst s (List.mem_of_getElem? hs')).pc).trans addrOf_0
      rcases hh with ⟨hk, -⟩ | ⟨ts', hts', -⟩
      · exact absurd ((ticketed_iff (by decide) hpc).mp hk) (by decide)
      · simp [Thread.init] at hts'
    · have I0 := trace_linv hs tr h0 j0
      have hh0 : HoldsV x w.tid u (tr.cfg j0).mem M := HoldsV.back hh (tr.prefix_le hj0) (I0.thr _ u hu0).ti.wf
      have hn := holder_nacertV hs tr h0 j0 hu0 hh0 (by have := holdsV_le I0 hu0 hh0 (by omega); omega)
        (hno j0) hc0
      have hen : ∀ j, max j1 nU ≤ j → InstrEnabledSem Arch.armv8 fuel w.tid (tr.cfg j) := by
        intro j hj
        have huj := hconst j hj
        have hS := trace_sinv hs tr h0 j _ u huj
        have hb := (trace_linv hs tr h0 j).bnd _ u huj
        refine instrEnabledSem_of_nacertG huj (fun hp0 => ?_) ?_
        · have hk : Ticketed u := by
            rcases hh with ⟨hk, -⟩ | ⟨ts', hts', -⟩
            · exact hk
            · rw [hp0] at hts'; cases hts'
          obtain ⟨p, hp, hpc⟩ := hk
          obtain ⟨outs, oc, h1, h2, h3⟩ := en_nil (A := w.tid) (mem := (tr.cfg j).mem) hS hp0 hb fun e =>
            held_ne17 p hp (addrOf_inj (held_sub p hp) (by decide) (hpc.symm.trans e))
          exact instrEnabledSem_of_step huj h1 h2 h3
        · rcases hn with hp0 | ⟨t', hr, ht'⟩
          · exact .inl hp0
          · exact .inr ⟨t', nacert_replay_loop hr rfl (trace_sinv hs tr h0 j0 _ u hu0) (I0.bnd _ u hu0) _
              (tr.prefix_le (by omega)), ht'⟩
      obtain ⟨j, hj, hi⟩ := hwfi w.tid ⟨max j1 nU, hen⟩ (max j1 nU)
      exact hj1 j (by omega) (.inl hi)

end Trace

/-! ## The theorems -/

/-- **Termination** (semantic machine): on a valid layout of `tkLoopWorker`,
for every `fuel`, every semantic trace from a start configuration under weak
and memory fairness reaches a final configuration. -/
theorem ticket_loop_term_sem (fuel : Nat) : TicketLoopTermSem fuel := by
  intro k N x o c states initMem hs tr h0 ⟨hwf, hmf⟩
  exact final_reached hs h0 hwf hmf

/-- **Every thread completes all its rounds** (semantic machine, promises
included): at a final configuration every worker is at its end. -/
theorem ticket_loop_finish_sem (fuel : Nat) : TicketLoopFinishSem fuel := by
  intro k N x o c states initMem hs tr h0 ⟨hwf, hmf⟩ T i ⟨t, ht⟩
  obtain ⟨f, hf⟩ := final_reached hs h0 hwf hmf
  obtain ⟨u, hu⟩ := tr.get_persist ht (max i f) (Nat.le_max_left _ _)
  have hf' : (tr.cfg (max i f)).final = true := by rw [final_stay tr hf _ (Nat.le_max_right _ _)]; exact hf
  exact ⟨max i f, Nat.le_max_left _ _, u, hu,
    final_pc hf' (trace_linv hs tr h0 _).bnd hu (trace_sinv hs tr h0 _ _ u hu)⟩

/-- **Starvation-freedom per round** (semantic machine, promises included): a
thread waiting in round `r` (so with `X7 ≠ 0`) is at its end with `X7 = 0` at
a final configuration: it has acquired in round `r`. -/
theorem ticket_loop_starve_sem (fuel : Nat) : TicketLoopStarveSem fuel := by
  intro k N x o c states initMem hs r tr h0 ⟨hwf, hmf⟩ T i ⟨t, ht, hsp, hr⟩
  obtain ⟨f, hf⟩ := final_reached hs h0 hwf hmf
  obtain ⟨u, hu⟩ := tr.get_persist ht (max i f) (Nat.le_max_left _ _)
  have hf' : (tr.cfg (max i f)).final = true := by rw [final_stay tr hf _ (Nat.le_max_right _ _)]; exact hf
  have h7 := (ti_at hs h0 hu).e7 (final_pc hf' (trace_linv hs tr h0 _).bnd hu (trace_sinv hs tr h0 _ _ u hu))
  simp only [tkLoopSpinPcs, List.mem_map] at hsp
  obtain ⟨p, hp, e⟩ := hsp
  have hmem : p ∈ [4, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega
  have h7' := (ti_at hs h0 ht).x7 p hmem e.symm
  exact ⟨max i f, Nat.le_max_left _ _, u, hu, .inr (by omega)⟩

/-- **Repeated-acquire ticket-lock liveness** (semantic machine, promises
included): starvation-freedom per round and completion of all rounds. -/
theorem ticket_loop_live_sem (fuel : Nat) : TicketLoopLiveSem fuel :=
  ⟨ticket_loop_starve_sem fuel, ticket_loop_finish_sem fuel⟩

/-- `ticket_loop_live_sem` at the concrete layout `TicketLoopPF.tkLoopLayout`:
no hypothesis left. -/
theorem ticket_loop_live_sem_concrete (fuel : Nat) : @TicketLoopLiveSem tkLoopLayout fuel :=
  @ticket_loop_live_sem tkLoopLayout tkLoopValid fuel

end Kraken.Promising.Live.TicketLoopSem

#print axioms Kraken.Promising.Live.TicketLoopSem.ticket_loop_live_sem_concrete
#print axioms Kraken.Promising.Live.TicketLoopSem.ticket_loop_term_sem
