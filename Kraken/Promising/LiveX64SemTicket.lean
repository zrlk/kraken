/-
**Stage 3: x64 ticket-lock liveness with promises,
on the machine with semantic certification** (`ticket3_x64_live_sem`), on a
valid layout of `tk3ImageV` (`ticketlock3.kl`, `Arch.tso`). An adapted copy
of `LiveTicketSem.lean` (AArch64); the argument is unchanged.

The proof follows `LiveX64TicketPF` on the invariant `X64SemInv.InvP`.
Write `M` for the value of `owner`; it never decreases (`trace_o`).

- Thread `T` waits with ticket `K` and never leaves positions 4–6 (it keeps
  its ticket: `tk_persist`). It is always instruction-enabled (it certifies
  without fresh writes: `NACert`), so it reads `owner` infinitely often
  (`reads_inf`).
- `M ≤ K` forever: otherwise the `owner` message of value `K + 1` exists; it
  belongs to the holder of `K`, i.e. `T`, which is not past its release, so
  it is an outstanding promise of `T`, above `T`'s coherence view of `owner`
  forever (`Good.coh`); memory fairness brings that view up to it.
- So `M` is eventually constant, `K'` say, with its last write. The holder
  `H` of `K'` (taken or reserved: `HoldsK`) is never past its release (else
  `owner = K' + 1` would exist), so it is always instruction-enabled, never
  gets through its critical section (`cs_false`), reads `owner` infinitely
  often, and memory fairness brings its view of `owner` up to the last write;
  then its next `movl (owner),%ecx` reads `K'`, `cmpl` sets `ZF` and `jne`
  falls through into the critical section (`at_false`): contradiction.

The trace lemmas `step_prefix`, `prefix_le`, `get_le`, `same_or_instr`, `adv`
are instances of the generic `TraceSem.*` lemmas of `LiveSem` at `Arch.tso`, as
are those of `LiveTicketSem`.
-/
import Kraken.Promising.LiveX64SemInv
import Kraken.Promising.LiveSpinCommon
import Kraken.Promising.LiveTkHolderP
import Kraken.Promising.SLR.EnvG.TicketXRunner

namespace Kraken.Promising.Live.X64SemTicket

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.TicketX64Trees Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.Sem Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.X64SemStep Kraken.Promising.Live.X64SemSolo Kraken.Promising.Live.X64SemInv
open Kraken.Promising.Live.X64Sem (TicketX64LiveSem)
open Kraken.Promising.Live.SpinCommon (evconst)
open Kraken.Promising.Live.TicketX64Inv (XL OL CL Static Ticketed tk ticketed_at)
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV)

set_option linter.unusedSectionVars false

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk3ImageV).addrOf

theorem getCoh_eq {t t' : Thread isa} (h : t'.views.coh = t.views.coh) (l : Loc) :
    t'.views.getCoh l = t.views.getCoh l :=
  SpinSwpStep.getCoh_congr h l

/-! ## Positions -/

theorem pos_step {u : Thread isa} {A : Nat} {mem : Memory} {outs : List (Except String (Outcome isa))}
    {oc : Outcome isa} (hS : SInv u.st) {p : Nat} (hp : p ∈ tkPcs) (hpc : u.st.st.2 = pcA p)
    (hs : stepOne Arch.tso u A mem = some outs) (ho : .ok oc ∈ outs) :
    oc.thread.st.st.2 = pcA (nextPc u.st.st.1.status.zf p) :=
  (step_sinv hS hs ho).2.2 p hp hpc

/-- Steps to the next `movl (owner),%ecx` in the spin loop. -/
def pot : Nat → Nat
  | 1 => 2 | 2 => 1 | 5 => 2 | 6 => 1 | _ => 0

theorem pot_lt : ∀ z : Bool, ∀ p ∈ [1, 2, 5, 6], ∀ q ∈ [1, 2, 4, 5, 6], q = nextPc z p → pot q < pot p := by
  decide

theorem past_of_pc {u : Thread isa} {p : Nat} (hp : p ∈ tkPcs) (hpc : u.st.st.2 = pcA p) (h : 7 < rk p) : Past u :=
  (past_iff hp hpc).mpr (by omega)

/-! ## Along a trace -/

section Trace

variable {fuel N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
  {tr : TraceSem Arch.tso fuel isa}

theorem step_prefix (i : Nat) : (tr.cfg i).mem.Prefix (tr.cfg (i + 1)).mem := tr.step_prefix i

theorem prefix_le {i j : Nat} (hij : i ≤ j) : (tr.cfg i).mem.Prefix (tr.cfg j).mem := tr.prefix_le hij

theorem get_le {i j : Nat} (hij : i ≤ j) {ts : Time} {w : Msg} (hw : (tr.cfg i).mem.get? ts = some w) :
    (tr.cfg j).mem.get? ts = some w := tr.get_le hij hw

/-- A step leaves thread `A`'s state and views alone, or is an instruction
step of `A` (from `TraceSem.same_or_instr`). -/
theorem same_or_instr (j A : Nat) {u : Thread isa} (hu : (tr.cfg j).threads[A]? = some u) :
    (∃ u', (tr.cfg (j + 1)).threads[A]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views) ∨
    ∃ outs oc, stepOne Arch.tso u A (tr.cfg j).mem = some outs ∧ .ok oc ∈ outs ∧
      tr.cfg (j + 1) = (tr.cfg j).withThread A oc.thread oc.mem :=
  (tr.same_or_instr j A hu).imp (fun ⟨u', h1, h2, h3, _⟩ => ⟨u', h1, h2, h3⟩) id

/-- **`A`'s next instruction step** (weak fairness for instruction steps):
from `j`, `A`'s state and views are unchanged until some `k` where it takes
an instruction step (`TraceSem.adv`). -/
theorem adv (hwfi : WeakFairInstrSem Arch.tso fuel tr.cfg) {A n : Nat}
    (hen : ∀ j, n ≤ j → InstrEnabledSem Arch.tso fuel A (tr.cfg j)) {j : Nat} (_hj : n ≤ j) {u : Thread isa}
    (hu : (tr.cfg j).threads[A]? = some u) :
    ∃ k, j ≤ k ∧ ∃ u', (tr.cfg k).threads[A]? = some u' ∧ u'.st = u.st ∧ u'.views = u.views ∧
      ∃ outs oc, stepOne Arch.tso u' A (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread A oc.thread oc.mem :=
  tr.adv (hwfi A ⟨n, hen⟩) hu

theorem wt_H {H k : Nat} {u : Thread isa} {oc : Outcome isa} (hu : (tr.cfg k).threads[H]? = some u)
    (he : tr.cfg (k + 1) = (tr.cfg k).withThread H oc.thread oc.mem) :
    (tr.cfg (k + 1)).threads[H]? = some oc.thread := by
  rw [he]; exact withThread_get_self hu

variable (hs : TicketX64.TkStartX N states initMem) (h0 : tr.cfg 0 = Config.init states initMem)
include hs h0

theorem M_mono {i j : Nat} (hij : i ≤ j) : fv (tr.cfg i).mem OL ≤ fv (tr.cfg j).mem OL := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    show _ ≤ BitVec.toNat ((tr.cfg (k + 1)).mem.finalVal OL)
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
      exact ⟨oc.thread, wt_H hu he, (r.tkt hku).1, (r.tkt hku).2.trans htu⟩

/-- **A thread always instruction-enabled and in positions 1, 2, 4–6 reads
`owner` infinitely often.** -/
theorem reads_inf (hwfi : WeakFairInstrSem Arch.tso fuel tr.cfg) {A n : Nat}
    (hen : ∀ j, n ≤ j → InstrEnabledSem Arch.tso fuel A (tr.cfg j))
    (hpos : ∀ j, n ≤ j → ∀ u, (tr.cfg j).threads[A]? = some u → ∃ p ∈ [1, 2, 4, 5, 6], u.st.st.2 = pcA p) :
    InfOften (fun i => ∃ ts, ReadsAt Arch.tso tr.cfg A OL ts i) := by
  suffices H : ∀ d j, n ≤ j → ∀ u p, (tr.cfg j).threads[A]? = some u → u.st.st.2 = pcA p →
      p ∈ [1, 2, 4, 5, 6] → pot p ≤ d → ∃ k, j ≤ k ∧ ∃ ts, ReadsAt Arch.tso tr.cfg A OL ts k by
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
    obtain ⟨-, md, -, -, ts, v, -, -, -, -, ν, hlog⟩ := q4 hS hso ho (by rw [e1]; exact hpc)
    exact ⟨k, hk, ts, u', outs, oc, hu', hso, ho, he, v, ν, hlog⟩
  | succ d ih =>
    intro j hj u p hu hpc hp hd
    by_cases h4 : p = 4
    · exact ih j hj u p hu hpc hp (by subst h4; simp [pot])
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := adv hwfi hen hj hu
    have hS := ((trace_invP hs tr h0 k).thr A u' hu').sinv
    have hp' : p ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    have hn := pos_step hS hp' (by rw [e1]; exact hpc) hso ho
    have hu1 : (tr.cfg (k + 1)).threads[A]? = some oc.thread := wt_H hu' he
    obtain ⟨q, hq, hqc⟩ := hpos (k + 1) (by omega) _ hu1
    have hqt : q ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
    have hnt : nextPc u'.st.st.1.status.zf p ∈ tkPcs := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> cases u'.st.st.1.status.zf <;> decide
    have e := addrOf_inj hqt hnt (hqc.symm.trans hn)
    have hlt := pot_lt _ p (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega) q hq e
    obtain ⟨k', hk', h⟩ := ih (k + 1) (by omega) _ q hu1 hqc hq (by omega)
    exact ⟨k', by omega, h⟩

/-! ## The holder of a constant `owner` -/

section Holder

variable {n K H : Nat} (hwfi : WeakFairInstrSem Arch.tso fuel tr.cfg) (hK32 : K < 2 ^ 32)
  (hM : ∀ j, n ≤ j → fv (tr.cfg j).mem OL = K)
  (hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite OL = (tr.cfg n).mem.lastWrite OL)
  (hH : ∀ j, n ≤ j → ∃ u, (tr.cfg j).threads[H]? = some u ∧ HoldsK u (tr.cfg j).mem K)

include hwfi hK32 hM hL hH

theorem hold {j : Nat} (hj : n ≤ j) {u : Thread isa} (hu : (tr.cfg j).threads[H]? = some u) :
    HoldsK u (tr.cfg j).mem K ∧ ¬ Past u := by
  obtain ⟨u', hu', hh⟩ := hH j hj
  rw [hu] at hu'; cases hu'
  refine ⟨hh, fun hp => ?_⟩
  have I := trace_invP hs tr h0 j
  have hk : Ticketed u := Classical.byContradiction fun hk => not_past (I.thr H u hu).sinv hk hp
  rcases hh with ⟨-, htk⟩ | ⟨hk', -⟩
  · obtain ⟨ts, w, hw, hl, hv⟩ := I.tdone H u hu hk hp
    have := I.ov' hw hl; have := hM j hj; omega
  · exact hk' hk

theorem henH {j : Nat} (hj : n ≤ j) : InstrEnabledSem Arch.tso fuel H (tr.cfg j) := by
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
      ∃ outs oc, stepOne Arch.tso u' H (tr.cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
        tr.cfg (k + 1) = (tr.cfg k).withThread H oc.thread oc.mem :=
  adv hwfi (fun _ hj => henH hs h0 hwfi hK32 hM hL hH hj) hj hu

/-- `H` never gets through its critical section: it would get past its
release. -/
theorem cs_false : ∀ d p j, p + d = 11 → 7 ≤ p → n ≤ j → ∀ u, (tr.cfg j).threads[H]? = some u →
    u.st.st.2 = pcA p → False := by
  intro d
  induction d with
  | zero =>
    intro p j hp _ hj u hu hpc
    obtain rfl : p = 11 := by omega
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := advH hs h0 hwfi hK32 hM hL hH _ hj _ hu
    have hS := ((trace_invP hs tr h0 k).thr H u' hu').sinv
    have hn := pos_step hS (p := 11) (by decide) (by rw [e1]; exact hpc) hso ho
    have e : nextPc u'.st.st.1.status.zf 11 = 12 := rfl
    rw [e] at hn
    exact (hold hs h0 hwfi hK32 hM hL hH (by omega) (wt_H hu' he)).2 (past_of_pc (by decide) hn (by decide))
  | succ d ih =>
    intro p j hp h7 hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := advH hs h0 hwfi hK32 hM hL hH _ hj _ hu
    have hS := ((trace_invP hs tr h0 k).thr H u' hu').sinv
    have hp' : p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
    have hpt : p ∈ tkPcs := by rcases hp' with rfl | rfl | rfl | rfl <;> decide
    have hn := pos_step hS hpt (by rw [e1]; exact hpc) hso ho
    have e : nextPc u'.st.st.1.status.zf p = p + 1 := by rcases hp' with rfl | rfl | rfl | rfl <;> rfl
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

/-- `H`'s spin cells (`movl (owner),%ecx`, `cmpl`, `jne`, critical section
from 7) as `TkHolderP.SpinCells`. -/
private theorem cells : TkHolderP.SpinCells Arch.tso tr.cfg OL H n K (fun s => s.st.2 = pcA 4)
    (fun s => s.st.2 = pcA 5) (fun s => s.st.2 = pcA 6) (fun s => s.st.2 = pcA 7)
    (fun s => (eax s.st.1).toNat) (fun s => (ecx s.st.1).toNat) (fun s => s.st.1.status.zf) where
  adv j hj u hu := advH hs h0 hwfi hK32 hM hL hH j hj u hu
  tk j hj u hu hpc := by
    rcases (hold hs h0 hwfi hK32 hM hL hH hj hu).1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd (ticketed_at hpc (by decide) (by decide) (by decide)) h
  lw := hL
  fval := hM
  cs j hj u hu hpc := cs_false' hs h0 hwfi hK32 hM hL hH j hj u hu 7 (by decide) hpc
  ld k hk u outs oc hu hso ho hpc := by
    obtain ⟨-, md, -, -, ts, v, hcx, hst, -, hv, ν, hlog⟩ :=
      q4 ((trace_invP hs tr h0 k).thr H u hu).sinv.st hso ho hpc
    refine ⟨by rw [hst], fun hc => ?_, ts, v, ν, hlog⟩
    have hm' : v.toNat = K := by rw [hv hc]; exact hM k hk
    rw [hst]; show (ecx md).toNat = _
    rw [hcx, ← hv hc, BitVec.toNat_setWidth]; omega
  cmp k hk u outs oc hu hso ho hpc := by
    obtain ⟨-, md, -, -, -, hz, hst, hcoh⟩ := q5 ((trace_invP hs tr h0 k).thr H u hu).sinv.st hso ho hpc
    exact ⟨by rw [hst], by rw [hst]; exact hz.trans BitVec.toNat_inj.symm, hcoh⟩
  bne k hk u outs oc hu hso ho hpc := by
    obtain ⟨-, hst, hcoh⟩ := q6 ((trace_invP hs tr h0 k).thr H u hu).sinv.st hso ho hpc
    refine ⟨?_, hcoh⟩
    rw [hst]; by_cases hz : u.st.st.1.status.zf = true <;> simp [hz]

/-- In the spin loop with an up-to-date view of `owner`, `H` enters the
critical section: contradiction (the spin positions by
`TkHolderP.SpinCells.spin_false`; positions 1 and 2 step into them). -/
theorem at_false {j : Nat} (hj : n ≤ j) {u : Thread isa} (hu : (tr.cfg j).threads[H]? = some u)
    (hc : (tr.cfg n).mem.lastWrite OL ≤ u.views.getCoh OL) : False := by
  have C := cells hs h0 hwfi hK32 hM hL hH
  have adv' := advH hs h0 hwfi hK32 hM hL hH
  have hS : ∀ {k u'}, (tr.cfg k).threads[H]? = some u' → SInv u'.st := fun hu' =>
    ((trace_invP hs tr h0 _).thr H _ hu').sinv
  -- coherence views only grow along `H`'s instruction steps
  have grow : ∀ {k u' outs} {oc : Outcome isa}, stepOne Arch.tso u' H (tr.cfg k).mem = some outs → .ok oc ∈ outs →
      u'.views.getCoh OL ≤ oc.thread.views.getCoh OL := fun hso ho => (stepOne_dord _ hso ho).2.1 _
  have p2 : ∀ j, n ≤ j → ∀ u, (tr.cfg j).threads[H]? = some u → u.st.st.2 = pcA 2 →
      (tr.cfg n).mem.lastWrite OL ≤ u.views.getCoh OL → False := by
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
theorem holder_false (hmf : MemFair Arch.tso tr.cfg) : False := by
  obtain ⟨u, hu, -⟩ := hH n (Nat.le_refl _)
  have hr := reads_inf hs h0 hwfi (fun j hj => henH hs h0 hwfi hK32 hM hL hH hj)
    (fun j hj u hu => posH hs h0 hwfi hK32 hM hL hH hj u hu)
  exact memFair_lastWrite_false hmf hr hu fun _ hj _ ht' hc =>
    at_false hs h0 hwfi hK32 hM hL hH hj ht' hc

end Holder

end Trace

/-! ## The theorem -/

/-- **x64 ticket-lock liveness with promises** (Stage 3, on the machine with
semantic certification): on a valid layout of `tk3ImageV`, for every `fuel`,
`TicketX64LiveSem fuel`. -/
theorem ticket3_x64_live_sem (fuel : Nat) : TicketX64LiveSem fuel := by
  intro N states initMem hs tr h0 ⟨hwf, hmf⟩ T i ⟨t, ht, hsp⟩
  apply Classical.byContradiction
  intro hnd
  have I := trace_invP hs tr h0
  have hwfi : WeakFairInstrSem Arch.tso fuel tr.cfg :=
    weakFairInstrSem_of_weakFairSem tr (fun i tid t ht => dropBounded_of_sinv ((I i).thr tid t ht).sinv) hwf
  -- `T` holds a ticket `K`, and keeps it
  have hkT : Ticketed t := by
    simp only [TicketX64.tkSpinPcsX, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hsp
    rcases hsp with h | h | h <;> exact ticketed_at h (by decide) (by decide) (by decide)
  have hper := tk_persist hs h0 ht hkT
  -- `T` stays in the spin loop
  have hposT : ∀ j, i ≤ j → ∀ u, (tr.cfg j).threads[T]? = some u → ∃ p ∈ [4, 5, 6], u.st.st.2 = pcA p := by
    intro j hj u hu
    have hpre : u.st.st.2 ∈ TicketX64.tkPrePcsX := Classical.byContradiction fun h => hnd ⟨j, hj, u, hu, h⟩
    obtain ⟨u', hu', hk', -⟩ := hper j hj
    rw [hu] at hu'; cases hu'
    simp only [TicketX64.tkPrePcsX, List.mem_map, List.mem_range] at hpre
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
  have henT : ∀ j, i ≤ j → InstrEnabledSem Arch.tso fuel T (tr.cfg j) := by
    intro j hj
    obtain ⟨u, hu, hku, -⟩ := hper j hj
    have hT := (I j).thr T u hu
    exact instrEnabledSem_of hu hT.sinv (fun e => hnpT j hj u hu (past_of_pc (by decide) e (by decide)))
      ((I j).bnd T u hu) (.inr (hT.nac (.inl hku)))
  have hrT := reads_inf hs h0 hwfi henT (fun j hj u hu => by
    obtain ⟨p, hp, hpc⟩ := hposT j hj u hu
    exact ⟨p, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢; omega, hpc⟩)
  -- `owner ≤ K` from `i` on: otherwise `T` holds a dead `owner` promise
  have hb : ∀ j, i ≤ j → fv (tr.cfg j).mem OL ≤ tk t := by
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
  obtain ⟨n, hin, hc⟩ := evconst (fun j => fv (tr.cfg j).mem OL) (fun i j h => M_mono hs h0 h) (tk t) i hb
  -- `owner` is constant from `n` on, and so is its last write
  have hL : ∀ j, n ≤ j → (tr.cfg j).mem.lastWrite OL = (tr.cfg n).mem.lastWrite OL := by
    intro j hj
    induction hj with
    | refl => rfl
    | @step k hle ih =>
      rcases trace_o hs tr h0 k with ⟨-, e⟩ | e
      · exact e.trans ih
      · have h1 : fv (tr.cfg (k + 1)).mem OL = fv (tr.cfg n).mem OL := hc (k + 1) (Nat.le_succ_of_le hle)
        have h2 : fv (tr.cfg k).mem OL = fv (tr.cfg n).mem OL := hc k hle
        omega
  -- the holder of `owner`
  obtain ⟨un, hun, hkn, hktn⟩ := hper n hin
  have hbn := hb n hin
  have hlt := (I n).tk_lt hun hkn
  obtain ⟨tsh, wh, hwh, hlh, hvh⟩ := (I n).xsurj (fv (tr.cfg n).mem OL) (by omega)
  have hH : ∀ j, n ≤ j → ∃ u, (tr.cfg j).threads[wh.tid]? = some u ∧
      HoldsK u (tr.cfg j).mem (fv (tr.cfg n).mem OL) := by
    intro j hj
    obtain ⟨k, u, hk, hu, hh⟩ := (I j).xheld tsh wh (get_le hj hwh) hlh
    obtain rfl : k = fv (tr.cfg n).mem OL := by omega
    exact ⟨u, hu, hh⟩
  exact holder_false hs h0 hwfi (by have := tk_lt t; omega) (fun j hj => hc j hj) hL hH hmf

/-! ## A concrete instance: the `.kl` runner's layout -/

open Kraken.Promising.X64.EnvG.TicketX.Concrete in
/-- `ticket3_x64_live_sem` at the `.kl` runner's layout `tk3LayoutV` (text at
`0x100000`, `next`/`owner`/`counter` at `0x1000000`/`0x1000100`/`0x1000200`):
no hypothesis left. -/
theorem ticket3_x64_live_sem_concrete (fuel : Nat) : @TicketX64LiveSem tk3LayoutV fuel :=
  @ticket3_x64_live_sem tk3LayoutV tk3ValidV fuel

end Kraken.Promising.Live.X64SemTicket
