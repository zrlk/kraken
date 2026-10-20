/-
**Stage 3: ticket-lock liveness with promises, on
the machine with semantic certification** (`ticket_live_sem`), on a valid
layout of `tkWorker`.

`Ticket.TicketLive fuel` (`LiveTicket.lean`) is stated over the existing
machine `succs`, which admits a step of a thread with promises only when the
executable search `certify` finds a certification within `fuel`
instructions. `certify.go`'s visited set ignores the remaining fuel, so the
search is incomplete and `succs` is not monotone in fuel (KNOWN_GAPS); the
existing `TicketLive fuel` is a statement about that search and may be false
(it is proved for `fuel = 0`: `LiveTicketZero.ticket_live_zero`).
`TicketLiveSem fuel` is the same statement over the machine of
`LiveSem.lean`, where certification is semantic (`CertOkN`: the thread can
empty its promise set alone within `fuel` instructions), under the semantic
weak fairness `WeakFairSem` and memory fairness `MemFair`. It is a new,
distinct statement; nothing existing is changed.

The proof follows `LiveTicketPF` on the invariant `LiveTicketInvP.InvP`.
Write `M` for the value of `owner`; it never decreases (`trace_o`).

- Thread `T` waits with ticket `K` and never leaves positions 4–6 (it keeps
  its ticket: `tk_persist`). It is always instruction-enabled (it certifies
  without fresh writes: `NACert`), so it reads `owner` infinitely often
  (`reads_inf`).
- `M ≤ K` forever: otherwise the `owner` message of value `K + 1` exists; it
  belongs to the holder of `K`, i.e. `T`, which is not past its `STLR`, so it
  is an outstanding promise of `T`, above `T`'s coherence view of `owner`
  forever (`Good.coh`); memory fairness brings that view up to it.
- So `M` is eventually constant, `K'` say, with its last write. The holder
  `H` of `K'` (taken or reserved: `HoldsK`) is never past its `STLR` (else
  `owner = K' + 1` would exist), so it is always instruction-enabled, never
  gets through its critical section (`cs_false`), reads `owner` infinitely
  often, and memory fairness brings its view of `owner` up to the last write;
  then its next `LDAR` reads `K'` and it enters the critical section
  (`at_false`): contradiction.
-/
import Kraken.Promising.LiveTicketInvP
import Kraken.Promising.LiveTicketPF
import Kraken.Promising.LiveTkHolderP

namespace Kraken.Promising.Live.TicketSem

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.TicketInv
open Kraken.Promising.Live.TicketDrop Kraken.Promising.Live.Sem Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.TicketSolo Kraken.Promising.Live.TicketInvP
open Kraken.Promising.Live.TicketPF (evconst tkLayout tkValid getCoh_eq)
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker StartState)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

set_option hygiene false in
local notation "pcA" => (layout tkWorker).addrOf

/-- **Ticket-lock liveness on the machine with semantic certification**
(Stage 3, with promises): from every start configuration, on every semantic
trace (`TraceSem`) under semantic weak fairness and memory fairness, every
waiting thread is eventually done.

This is *not* the existing `Ticket.TicketLive fuel`: that one is stated over
`succs`, whose certification search `certify` is incomplete (`certify.go`'s
visited set ignores the remaining fuel), so it may be false. Here a promise
or an instruction step needs the thread to be *certifiable within `fuel`*
(`CertOkN`), the intended notion. -/
def TicketLiveSem (fuel : Nat) : Prop :=
  ∀ N x o c states initMem, Ticket.TkStart N x o c states initMem →
    LiveFromSem Arch.armv8 fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.armv8 fuel cfg ∧ MemFair Arch.armv8 cfg) Ticket.TkWaiting Ticket.TkDone

/-! ## The position after a step -/

/-- The position after the instruction at position `p` (`z`: the `Z` flag). -/
def nextPc (z : Bool) : Nat → Nat
  | 1 => 2 | 2 => 4 | 4 => 5 | 5 => 6 | 6 => if z then 7 else 4 | 7 => 8 | 8 => 9 | 9 => 10 | 10 => 11
  | 11 => 12 | _ => 14

theorem pos_step {x o c : BitVec 64} {u : Thread isa} {A : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : Static x o c u.st) {p : Nat}
    (hp : p ∈ tkPcs) (hpc : u.st.st.2 = pcA p) (hs : stepOne Arch.armv8 u A mem = some outs) (ho : .ok oc ∈ outs) :
    oc.thread.st.st.2 = pcA (nextPc u.st.st.1.status.z p) := by
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, -⟩ := spec_done _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho; rw [hst]; rfl
  · obtain ⟨tr, old, hst, -⟩ := spec_rmw_p _ _ rfl (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    rw [hst]; rfl
  · obtain ⟨ts, v, hst, -⟩ := spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    rw [hst]; rfl
  · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨-, hst, -⟩ := spec_done _ _ hex hs ho; rw [hst]; rfl
  · obtain ⟨-, hst, -⟩ := spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho
    by_cases hz : u.st.st.1.status.z = true
    · rw [ite_eq_left hz] at hst
      have : nextPc u.st.st.1.status.z 6 = 7 := by simp [nextPc, hz]
      rw [this, hst]
    · rw [ite_eq_right hz] at hst
      have : nextPc u.st.st.1.status.z 6 = 4 := by simp [nextPc, hz]
      rw [this, hst]
  · obtain ⟨ts, v, hst, -⟩ := spec_load _ _ (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    rw [hst]; rfl
  · obtain ⟨-, hst, -⟩ := spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho; rw [hst]; rfl
  · obtain ⟨hst, -⟩ := spec_store_p _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    rw [hst]; rfl
  · obtain ⟨-, hst, -⟩ := spec_done _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho; rw [hst]; rfl
  · obtain ⟨hst, -⟩ := spec_store_p _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    rw [hst]; rfl
  · obtain ⟨-, hst, -⟩ := spec_done _ _ (exec_b_done _ (hS.at (by decide) (by decide) hpc)) hs ho; rw [hst]; rfl
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- Steps to the next `LDAR` in the spin loop. -/
def pot : Nat → Nat
  | 1 => 2 | 2 => 1 | 5 => 2 | 6 => 1 | _ => 0

theorem pot_lt : ∀ z : Bool, ∀ p ∈ [1, 2, 5, 6], ∀ q ∈ [1, 2, 4, 5, 6], q = nextPc z p → pot q < pot p := by
  decide

theorem past_of_pc {u : Thread isa} {p : Nat} (hp : p ∈ tkPcs) (hpc : u.st.st.2 = pcA p) (h : 7 < rk p) : Past u :=
  (past_iff hp hpc).mpr (by omega)

/-! ## Along a trace -/

section Trace

variable {fuel N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.armv8 fuel isa}

theorem step_prefix (i : Nat) : (tr.cfg i).mem.Prefix (tr.cfg (i + 1)).mem := tr.step_prefix i

theorem prefix_le {i j : Nat} (hij : i ≤ j) : (tr.cfg i).mem.Prefix (tr.cfg j).mem := tr.prefix_le hij

theorem get_le {i j : Nat} (hij : i ≤ j) {ts : Time} {w : Msg} (hw : (tr.cfg i).mem.get? ts = some w) :
    (tr.cfg j).mem.get? ts = some w := tr.get_le hij hw

/-- A step leaves thread `A`'s state and views alone, or is an instruction
step of `A` (from `TraceSem.same_or_instr`). -/
theorem same_or_instr (j A : Nat) {u : Thread isa} (hu : (tr.cfg j).threads[A]? = some u) :
    (∃ u', (tr.cfg (j + 1)).threads[A]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views) ∨
    ∃ outs oc, stepOne Arch.armv8 u A (tr.cfg j).mem = some outs ∧ .ok oc ∈ outs ∧
      tr.cfg (j + 1) = (tr.cfg j).withThread A oc.thread oc.mem :=
  (tr.same_or_instr j A hu).imp (fun ⟨u', h1, h2, h3, _⟩ => ⟨u', h1, h2, h3⟩) id

/-- **`A`'s next instruction step** (weak fairness for instruction steps):
from `j`, `A`'s state and views are unchanged until some `k` where it takes
an instruction step (`TraceSem.adv`). -/
theorem adv (hwfi : WeakFairInstrSem Arch.armv8 fuel tr.cfg) {A n : Nat}
    (hen : ∀ j, n ≤ j → InstrEnabledSem Arch.armv8 fuel A (tr.cfg j)) {j : Nat} (_hj : n ≤ j) {u : Thread isa}
    (hu : (tr.cfg j).threads[A]? = some u) :
    ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[A]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∃ outs oc, stepOne Arch.armv8 u' A (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread A oc.thread oc.mem :=
  tr.adv (hwfi A ⟨n, hen⟩) hu

variable (hs : Ticket.TkStart N x o c states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
include hs h0

theorem M_mono {i j : Nat} (hij : i ≤ j) : fv (tr.cfg i).mem o ≤ fv (tr.cfg j).mem o := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    show _ ≤ BitVec.toNat ((tr.cfg (k + 1)).mem.finalVal (L4 o))
    rcases trace_o hs tr h0 k with ⟨e, -⟩ | e <;> omega

/-- A ticketed thread keeps its ticket. -/
theorem tk_persist {T i : Nat} {t : Thread isa} (ht : (tr.cfg i).threads[T]? = some t) (hk : Ticketed t) :
    ∀ j, i ≤ j → ∃ u, (tr.cfg j).threads[T]? = some u ∧ Ticketed u ∧ tk u = tk t := by
  intro j hj
  induction hj with
  | refl => exact ⟨t, ht, hk, rfl⟩
  | @step k _ ih =>
    obtain ⟨u, hu, hku, htu⟩ := ih
    rcases same_or_instr k T hu with ⟨u', hu', e1, -⟩ | ⟨outs, oc, hs', ho, he⟩
    · exact ⟨u', hu', by unfold Ticketed; rw [e1]; exact hku, by unfold tk; rw [e1]; exact htu⟩
    · have I := trace_invP hs tr h0 k
      have hT := I.thr T u hu
      have r := step_solo I.hxo I.hxc I.hoc hT.sinv hT.rinv hT.promIn hs' ho
      exact ⟨oc.thread, by rw [he]; exact withThread_get_self hu, (r.tkt hku).1, (r.tkt hku).2.trans htu⟩

/-- **A thread always instruction-enabled and in positions 1, 2, 4–6 reads
`owner` infinitely often.** -/
theorem reads_inf (hwfi : WeakFairInstrSem Arch.armv8 fuel tr.cfg) {A n : Nat}
    (hen : ∀ j, n ≤ j → InstrEnabledSem Arch.armv8 fuel A (tr.cfg j))
    (hpos : ∀ j, n ≤ j → ∀ u, (tr.cfg j).threads[A]? = some u → ∃ p ∈ [1, 2, 4, 5, 6], u.st.st.2 = pcA p) :
    InfOften (fun i => ∃ ts, ReadsAt Arch.armv8 tr.cfg A (L4 o) ts i) := by
  suffices H : ∀ d j, n ≤ j → ∀ u p, (tr.cfg j).threads[A]? = some u → u.st.st.2 = pcA p →
      p ∈ [1, 2, 4, 5, 6] → pot p ≤ d → ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.armv8 tr.cfg A (L4 o) ts k by
    intro j0
    obtain ⟨u, hu⟩ : ∃ u, (tr.cfg (max n j0)).threads[A]? = some u := by
      obtain ⟨_, t, _, _, ht, -⟩ := hen _ (Nat.le_max_left n j0); exact ⟨t, ht⟩
    obtain ⟨p, hp, hpc⟩ := hpos _ (Nat.le_max_left _ _) u hu
    obtain ⟨k, hk, h⟩ := H _ _ (Nat.le_max_left _ _) u p hu hpc hp (Nat.le_refl _)
    exact ⟨k, by omega, h⟩
  intro d
  induction d with
  | zero =>
    intro j hj u p hu hpc hp hd
    have h4 : p = 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp_all [pot]
    subst h4
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hwfi hen hj hu
    have hS := ((trace_invP hs tr h0 k).thr A u' hu').sinv.st
    obtain ⟨ts, v, -, -, -, -, -, ν, hlog⟩ :=
      spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) (by rw [e1]; exact hpc)) hS.x1 hS.dO) hso ho
    exact ⟨k, hk, ts, u', outs, oc, hu', hso, ho, he, v, ν, hlog⟩
  | succ d ih =>
    intro j hj u p hu hpc hp hd
    by_cases h4 : p = 4
    · exact ih j hj u p hu hpc hp (by subst h4; simp [pot])
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hwfi hen hj hu
    have hS := ((trace_invP hs tr h0 k).thr A u' hu').sinv.st
    have hp' : p ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hn := pos_step hS hp' (by rw [e1]; exact hpc) hso ho
    have hu1 : (tr.cfg (k + 1)).threads[A]? = some oc.thread := by rw [he]; exact withThread_get_self hu'
    obtain ⟨q, hq, hqc⟩ := hpos (k + 1) (by omega) _ hu1
    have hqt : q ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    have hnt : nextPc u'.st.st.1.status.z p ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> cases u'.st.st.1.status.z <;> decide
    have e := addrOf_inj hqt hnt (hqc.symm.trans hn)
    have hlt := pot_lt _ p (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) q hq e
    obtain ⟨k', hk', h⟩ := ih (k + 1) (by omega) _ q hu1 hqc hq (by omega)
    exact ⟨k', by omega, h⟩

/-! ## The holder of a constant `owner` -/

section Holder

variable {n K H : Nat} (hwfi : WeakFairInstrSem Arch.armv8 fuel tr.cfg) (hK32 : K < 2 ^ 32)
  (hM : ∀ j, n ≤ j → fv (tr.cfg j).mem o = K)
  (hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg n).mem.lastWrite (L4 o))
  (hH : ∀ j, n ≤ j → ∃ u, (tr.cfg j).threads[H]? = some u ∧ HoldsK x u (tr.cfg j).mem K)

include hwfi hK32 hM hL hH

theorem hold {j : Nat} (hj : n ≤ j) {u : Thread isa} (hu : (tr.cfg j).threads[H]? = some u) :
    HoldsK x u (tr.cfg j).mem K ∧ ¬ Past u := by
  obtain ⟨u', hu', hh⟩ := hH j hj
  rw [hu] at hu'; cases hu'
  refine ⟨hh, fun hp => ?_⟩
  have I := trace_invP hs tr h0 j
  have hk : Ticketed u := Classical.byContradiction fun hk => not_past (I.thr H u hu).sinv hk hp
  rcases hh with ⟨-, htk⟩ | ⟨hk', -⟩
  · obtain ⟨ts, w, hw, hl, hv⟩ := I.tdone H u hu hk hp
    have := I.ov' hw hl; have := hM j hj; omega
  · exact hk' hk

theorem henH {j : Nat} (hj : n ≤ j) : InstrEnabledSem Arch.armv8 fuel H (tr.cfg j) := by
  obtain ⟨u, hu, -⟩ := hH j hj
  obtain ⟨hh, hnp⟩ := hold hs h0 hwfi hK32 hM hL hH hj hu
  have I := trace_invP hs tr h0 j
  have hT := I.thr H u hu
  refine instrEnabledSem_of hu hT.sinv (fun e => hnp (past_of_pc (by decide) e (by decide))) (I.bnd H u hu)
    (.inr (hT.nac ?_))
  rcases hh with ⟨a, -⟩ | ⟨-, ts, hts, w, hw, hl, -⟩
  · exact .inl a
  · exact .inr ⟨ts, hts, w, hw, hl⟩

theorem advH (j : Nat) (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) :
    ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[H]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∃ outs oc, stepOne Arch.armv8 u' H (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread H oc.thread oc.mem :=
  adv hwfi (fun _ hj => henH hs h0 hwfi hK32 hM hL hH hj) hj hu

omit hs h0 hwfi hK32 hM hL hH in
theorem wt_H {k : Nat} {u : Thread isa} {oc : Outcome isa} (hu : (tr.cfg k).threads[H]? = some u)
    (he : tr.cfg (k + 1) = (tr.cfg k).withThread H oc.thread oc.mem) :
    (tr.cfg (k + 1)).threads[H]? = some oc.thread := by
  rw [he]; exact withThread_get_self hu

/-- `H` never gets through its critical section: it would get past its
`STLR`. -/
theorem cs_false : ∀ d p j, p + d = 11 → 7 ≤ p → n ≤ j → ∀ u, (tr.cfg j).threads[H]? = some u →
    u.st.st.2 = pcA p → False := by
  intro d
  induction d with
  | zero =>
    intro p j hp _ hj u hu hpc
    obtain rfl : p = 11 := by omega
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := advH hs h0 hwfi hK32 hM hL hH _ hj _ hu
    have hS := ((trace_invP hs tr h0 k).thr H u' hu').sinv.st
    have hn := pos_step hS (p := 11) (by decide) (by rw [e1]; exact hpc) hso ho
    have e : nextPc u'.st.st.1.status.z 11 = 12 := rfl
    rw [e] at hn
    exact (hold hs h0 hwfi hK32 hM hL hH (by omega) (wt_H hu' he)).2 (past_of_pc (by decide) hn (by decide))
  | succ d ih =>
    intro p j hp h7 hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := advH hs h0 hwfi hK32 hM hL hH _ hj _ hu
    have hS := ((trace_invP hs tr h0 k).thr H u' hu').sinv.st
    have hp' : p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
    have hpt : p ∈ tkPcs := by rcases hp' with rfl | rfl | rfl | rfl <;> decide
    have hn := pos_step hS hpt (by rw [e1]; exact hpc) hso ho
    have e : nextPc u'.st.st.1.status.z p = p + 1 := by rcases hp' with rfl | rfl | rfl | rfl <;> rfl
    rw [e] at hn
    exact ih (p + 1) (k + 1) (by omega) (by omega) (by omega) _ (wt_H hu' he) hn

theorem cs_false' (j : Nat) (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) (p : Nat)
    (hp : p ∈ [7, 8, 9, 10, 11]) (hpc : u.st.st.2 = pcA p) : False := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  exact cs_false hs h0 hwfi hK32 hM hL hH (11 - p) p j (by omega) (by omega) hj u hu hpc

/-- `H`'s positions: 1, 2, 4–6. -/
theorem posH {j : Nat} (hj : n ≤ j) (u : Thread isa) (hu : (tr.cfg j).threads[H]? = some u) :
    ∃ p ∈ [1, 2, 4, 5, 6], u.st.st.2 = pcA p := by
  obtain ⟨-, hnp⟩ := hold hs h0 hwfi hK32 hM hL hH hj hu
  obtain ⟨-, p, hp, hpc⟩ := ((trace_invP hs tr h0 j).thr H u hu).sinv
  have hp' := hp
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨_, by decide, hpc⟩
    | exact (cs_false' hs h0 hwfi hK32 hM hL hH _ hj _ hu _ (by decide) hpc).elim
    | exact (hnp (past_of_pc hp' hpc (by decide))).elim

/-- `H`'s spin cells (`LDAR`, `CMP`, `B.NE`, critical section from 7) as
`TkHolderP.SpinCells`. -/
private theorem cells : TkHolderP.SpinCells Arch.armv8 tr.cfg (L4 o) H n K (fun s => s.st.2 = pcA 4)
    (fun s => s.st.2 = pcA 5) (fun s => s.st.2 = pcA 6) (fun s => s.st.2 = pcA 7)
    (fun s => wn s.st.1.regs.X3) (fun s => wn s.st.1.regs.X4) (fun s => s.st.1.status.z) where
  adv j hj u hu := advH hs h0 hwfi hK32 hM hL hH j hj u hu
  tk j hj u hu hpc := by
    rcases (hold hs h0 hwfi hK32 hM hL hH hj hu).1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (ticketed_at hpc (by decide) (by decide) (by decide)) h
  lw := hL
  fval := hM
  cs j hj u hu hpc := cs_false' hs h0 hwfi hK32 hM hL hH j hj u hu 7 (by decide) hpc
  ld k hk u outs oc hu hso ho hpc := by
    have hS := ((trace_invP hs tr h0 k).thr H u hu).sinv.st
    obtain ⟨ts, v, hst, -, hv, -, -, ν, hlog⟩ :=
      spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hso ho
    refine ⟨by rw [hst], fun hc => ?_, ts, v, ν, hlog⟩
    have hm' : v.toNat = K := by rw [hv hc]; exact hM k hk
    rw [hst, hv hc]; show (BitVec.setWidth 64 (BitVec.setWidth 32 _)).toNat % 2 ^ 32 = _
    rw [← hv hc]; simp only [BitVec.toNat_setWidth]; omega
  cmp k hk u outs oc hu hso ho hpc := by
    have hS := ((trace_invP hs tr h0 k).thr H u hu).sinv.st
    obtain ⟨sf, hex, hz⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    obtain ⟨-, hst, -, hcoh⟩ := spec_done _ _ hex hso ho
    exact ⟨by rw [hst], by rw [hst]; exact hz.trans (w32_eq_iff _ _), hcoh⟩
  bne k hk u outs oc hu hso ho hpc := by
    have hS := ((trace_invP hs tr h0 k).thr H u hu).sinv.st
    obtain ⟨-, hst, -, hcoh⟩ := spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hso ho
    refine ⟨?_, hcoh⟩
    rw [hst]; by_cases hz : u.st.st.1.status.z = true <;> simp [hz]

/-- In the spin loop with an up-to-date view of `owner`, `H` enters the
critical section: contradiction (the spin positions by
`TkHolderP.SpinCells.spin_false`; `MOV` and `LDADDA` step into them). -/
theorem at_false {j : Nat} (hj : n ≤ j) {u : Thread isa} (hu : (tr.cfg j).threads[H]? = some u)
    (hc : (tr.cfg n).mem.lastWrite (L4 o) ≤ u.views.getCoh (L4 o)) : False := by
  have C := cells hs h0 hwfi hK32 hM hL hH
  have adv' := advH hs h0 hwfi hK32 hM hL hH
  have hS : ∀ {k u'}, (tr.cfg k).threads[H]? = some u' → Static x o c u'.st := fun hu' =>
    ((trace_invP hs tr h0 _).thr H _ hu').sinv.st
  have grow : ∀ {k u' outs} {oc : Outcome isa}, stepOne Arch.armv8 u' H (tr.cfg k).mem = some outs → .ok oc ∈ outs →
      u'.views.getCoh (L4 o) ≤ oc.thread.views.getCoh (L4 o) := fun hso ho => (stepOne_dord _ hso ho).2.1 _
  have p2 : ∀ j, n ≤ j → ∀ u, (tr.cfg j).threads[H]? = some u → u.st.st.2 = pcA 2 →
      (tr.cfg n).mem.lastWrite (L4 o) ≤ u.views.getCoh (L4 o) → False := by
    intro j hj u hu hpc hc
    obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := adv' _ hj _ hu
    have hn := pos_step (hS hu') (p := 2) (by decide) (by rw [e1]; exact hpc) hso ho
    exact C.spin_false (j := k + 1) (by omega) (wt_H hu' he) (.inl hn)
      (Nat.le_trans (by rw [e2]; exact hc) (grow hso ho))
  obtain ⟨p, hp, hpc⟩ := posH hs h0 hwfi hK32 hM hL hH hj u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := adv' _ hj _ hu
    have hn := pos_step (hS hu') (p := 1) (by decide) (by rw [e1]; exact hpc) hso ho
    exact p2 (k + 1) (by omega) _ (wt_H hu' he) hn (Nat.le_trans (by rw [e2]; exact hc) (grow hso ho))
  · exact p2 j hj u hu hpc hc
  · exact C.spin_false hj hu (.inl hpc) hc
  · exact C.spin_false hj hu (.inr (.inl hpc)) hc
  · exact C.spin_false hj hu (.inr (.inr hpc)) hc

/-- **The holder of a constant `owner` cannot exist** (memory fairness). -/
theorem holder_false (hmf : MemFair Arch.armv8 tr.cfg) : False := by
  obtain ⟨u, hu, -⟩ := hH n (Nat.le_refl _)
  have hr := reads_inf hs h0 hwfi (fun j hj => henH hs h0 hwfi hK32 hM hL hH hj)
    (fun j hj u hu => posH hs h0 hwfi hK32 hM hL hH hj u hu)
  exact memFair_lastWrite_false hmf hr hu fun _ hj _ ht' hc =>
    at_false hs h0 hwfi hK32 hM hL hH hj ht' hc

end Holder

end Trace

/-! ## The theorem -/

/-- **Ticket-lock liveness with promises** (Stage 3, on the machine with
semantic certification): on a valid layout of `tkWorker`, for every `fuel`,
`TicketLiveSem fuel`. -/
theorem ticket_live_sem (fuel : Nat) : TicketLiveSem fuel := by
  intro N x o c states initMem hs tr h0 ⟨hwf, hmf⟩ T i ⟨t, ht, hsp⟩
  apply Classical.byContradiction
  intro hnd
  have I := trace_invP hs tr h0
  have hwfi : WeakFairInstrSem Arch.armv8 fuel tr.cfg :=
    weakFairInstrSem_of_weakFairSem tr (fun i tid t ht => dropBounded_of_sinv ((I i).thr tid t ht).sinv) hwf
  -- `T` holds a ticket `K`, and keeps it
  have hkT : Ticketed t := by
    simp only [Ticket.tkSpinPcs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsp
    rcases hsp with h | h | h <;> exact ticketed_at h (by decide) (by decide) (by decide)
  have hper := tk_persist hs h0 ht hkT
  -- `T` stays in the spin loop
  have hposT : ∀ j, i ≤ j → ∀ u, (tr.cfg j).threads[T]? = some u → ∃ p ∈ [4, 5, 6], u.st.st.2 = pcA p := by
    intro j hj u hu
    have hpre : u.st.st.2 ∈ Ticket.tkPrePcs := Classical.byContradiction fun h => hnd ⟨j, hj, u, hu, h⟩
    obtain ⟨u', hu', hk', -⟩ := hper j hj
    rw [hu] at hu'; cases hu'
    simp only [Ticket.tkPrePcs, List.mem_map, List.mem_range] at hpre
    obtain ⟨r, hr, e⟩ := hpre
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (e.symm.trans addrOf_0) hk'.1
    · exact absurd e.symm hk'.1
    · exact absurd e.symm hk'.2
    · exact ⟨4, by decide, e.symm.trans addrOf_3⟩
    · exact ⟨4, by decide, e.symm⟩
    · exact ⟨5, by decide, e.symm⟩
    · exact ⟨6, by decide, e.symm⟩
  have hnpT : ∀ j, i ≤ j → ∀ u, (tr.cfg j).threads[T]? = some u → ¬ Past u := by
    intro j hj u hu hp
    obtain ⟨p, hp', hpc⟩ := hposT j hj u hu
    have hpt : p ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'; rcases hp' with rfl | rfl | rfl <;> decide
    refine hp ((rkLe_iff hpt hpc 7).mpr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'; rcases hp' with rfl | rfl | rfl <;> decide
  have henT : ∀ j, i ≤ j → InstrEnabledSem Arch.armv8 fuel T (tr.cfg j) := by
    intro j hj
    obtain ⟨u, hu, hku, -⟩ := hper j hj
    have hT := (I j).thr T u hu
    exact instrEnabledSem_of hu hT.sinv (fun e => hnpT j hj u hu (past_of_pc (by decide) e (by decide)))
      ((I j).bnd T u hu) (.inr (hT.nac (.inl hku)))
  have hrT := reads_inf hs h0 hwfi henT (fun j hj u hu => by
    obtain ⟨p, hp, hpc⟩ := hposT j hj u hu
    exact ⟨p, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega, hpc⟩)
  -- `owner ≤ K` from `i` on: otherwise `T` holds a dead `owner` promise
  have hb : ∀ j, i ≤ j → fv (tr.cfg j).mem o ≤ tk t := by
    intro j hj
    apply Classical.byContradiction
    intro hlt
    obtain ⟨ts, w, hw, hl, hv⟩ := (I j).osurj (tk t) (by omega)
    obtain ⟨u, hu, hku, htku⟩ := hper j hj
    obtain ⟨k, u', hk, hu', hh, -⟩ := (I j).oheld ts w hw hl
    obtain rfl : k = tk t := by omega
    have e := (I j).holdsK_inj hu' hu hh (.inl ⟨hku, htku⟩)
    obtain ⟨k', hk', u'', hu'', hc⟩ := memFair_catchup hmf hrT hw hl
    obtain ⟨-, u3, -, hu3, -, hp3⟩ := (I k').oheld ts w (get_le hk' hw) hl
    rw [e, hu''] at hu3; cases hu3
    have := ((I k').thr T u'' hu'').good.coh ts (hp3 (hnpT k' (by omega) u'' hu'')) w (get_le hk' hw)
    rw [hl] at this; exact absurd hc (Nat.not_le_of_lt this)
  obtain ⟨n, hin, hc⟩ := evconst (fun j => fv (tr.cfg j).mem o) (fun i j h => M_mono hs h0 h) (tk t) i hb
  -- `owner` is constant from `n` on, and so is its last write
  have hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite (L4 o) = (tr.cfg n).mem.lastWrite (L4 o) := by
    intro j hj
    induction hj with
    | refl => rfl
    | @step k hle ih =>
      rcases trace_o hs tr h0 k with ⟨-, e⟩ | e
      · exact e.trans ih
      · have h1 : fv (tr.cfg (k + 1)).mem o = fv (tr.cfg n).mem o := hc (k + 1) (Nat.le_succ_of_le hle)
        have h2 : fv (tr.cfg k).mem o = fv (tr.cfg n).mem o := hc k hle
        omega
  -- the holder of `owner`
  obtain ⟨un, hun, hkn, hktn⟩ := hper n hin
  have hbn := hb n hin
  have hlt := (I n).tk_lt hun hkn
  obtain ⟨tsh, wh, hwh, hlh, hvh⟩ := (I n).xsurj (fv (tr.cfg n).mem o) (by omega)
  have hH : ∀ j, n ≤ j → ∃ u, (tr.cfg j).threads[wh.tid]? = some u ∧
      HoldsK x u (tr.cfg j).mem (fv (tr.cfg n).mem o) := by
    intro j hj
    obtain ⟨k, u, hk, hu, hh⟩ := (I j).xheld tsh wh (get_le hj hwh) hlh
    obtain rfl : k = fv (tr.cfg n).mem o := by omega
    exact ⟨u, hu, hh⟩
  exact holder_false hs h0 hwfi (by have := tk_lt t; omega) (fun j hj => hc j hj) hL hH hmf

/-! ## A concrete instance -/

/-- `ticket_live_sem` at the concrete layout `tkLayout`: no hypothesis left. -/
theorem ticket_live_sem_concrete (fuel : Nat) : @TicketLiveSem tkLayout fuel :=
  @ticket_live_sem tkLayout tkValid fuel

end Kraken.Promising.Live.TicketSem
