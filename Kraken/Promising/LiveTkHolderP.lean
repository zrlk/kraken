/-
**The holder argument of the ticket-lock liveness proofs, once**: ISA-, program- and machine-neutral.

Every ticket-lock liveness proof (`LiveTicketPF`, `LiveTicketSem`,
`LiveTicketLoopPF`, `LiveX64TicketPF`, `LiveX64Ticket2PF`, `LiveX64SemTicket`,
`LiveX64Sem2Ticket`, and the `TicketAl` clones) ends the same way. From index
`n` on, thread `H` holds the served ticket `m`, `owner` (location `l`) has the
value `m` and a fixed last write, `H` is always scheduled again (`adv`), and
`H` never reaches the entry of its critical section (`PE`). In its spin loop
(`PL`: the load of `owner`, `PC`: the compare, `PB`: the branch) an up-to-date
view of `owner` makes the load read `m`, the compare set the flag and the
branch fall through into `PE`: contradiction (`spin_false`). If `H` never
leaves the spin loop it reads `owner` infinitely often (`reads_inf`), so memory
fairness gives the up-to-date view (each site's `holder_false`, by
`memFair_lastWrite_false`).

Positions are predicates on the ISA state and register facts are functions of
the state (`tkv`: the ticket register, `rv`: the register the load writes,
`Z`: the flag the compare sets), so the core needs no program, layout or ISA,
and both the executable machine (`TraceS`, where `adv` keeps the thread) and
the semantic machine (`TraceSem`, `TraceSem.adv`) instantiate it. Each proof
builds a `SpinCells` from its step lemmas in a private `cells` theorem; its
`at_false`, `reads_inf` and `holder_false` keep their names and statements.
-/
import Kraken.Promising.LiveRank
import Kraken.Promising.LiveSpinStep
import Kraken.Promising.LiveSpinSwpStep

namespace Kraken.Promising.Live.TkHolderP

open Kraken Kraken.Promising Kraken.Promising.Live

variable {I : ISA}

/-- The facts the instance supplies about `H`'s spin cells from index `n` on. -/
structure SpinCells (A : Arch) (cfg : Nat → Config I) (l : Loc) (H n m : Nat)
    (PL PC PB PE : I.State → Prop) (tkv rv : I.State → Nat) (Z : I.State → Bool) : Prop where
  /-- weak fairness for `H`: its state and views are kept until its next instruction step. -/
  adv : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → ∃ k, j ≤ k ∧ ∃ u', (cfg k).threads[H]? = some u' ∧
    u'.st = u.st ∧ u'.views = u.views ∧ ∃ outs oc, stepOne A u' H (cfg k).mem = some outs ∧ .ok oc ∈ outs ∧
      cfg (k + 1) = (cfg k).withThread H oc.thread oc.mem
  /-- at the compare, the ticket register holds `m`. -/
  tk : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PC u.st → tkv u.st = m
  /-- the last write to `owner` is fixed. -/
  lw : ∀ j, n ≤ j → (cfg j).mem.lastWrite l = (cfg n).mem.lastWrite l
  /-- `owner` has the value `m`. -/
  fval : ∀ j, n ≤ j → ((cfg j).mem.finalVal l).toNat = m
  /-- `H` never reaches the entry of its critical section. -/
  cs : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PE u.st → False
  /-- the load of `owner`: on to the compare, reading the last value if the view is up to date. -/
  ld : ∀ k, n ≤ k → ∀ u outs oc, (cfg k).threads[H]? = some u → stepOne A u H (cfg k).mem = some outs →
    .ok oc ∈ outs → PL u.st → PC oc.thread.st ∧
      ((cfg k).mem.lastWrite l ≤ u.views.getCoh l → rv oc.thread.st = ((cfg k).mem.finalVal l).toNat) ∧
      ∃ ts v ν, TraceEv.read l ts v ν ∈ oc.log
  /-- the compare: on to the branch, the flag set iff the loaded value is the ticket. -/
  cmp : ∀ k, n ≤ k → ∀ u outs oc, (cfg k).threads[H]? = some u → stepOne A u H (cfg k).mem = some outs →
    .ok oc ∈ outs → PC u.st → PB oc.thread.st ∧ (Z oc.thread.st = true ↔ rv u.st = tkv u.st) ∧
      oc.thread.views.coh = u.views.coh
  /-- the branch: into the critical section if the flag is set, else back to the load. -/
  bne : ∀ k, n ≤ k → ∀ u outs oc, (cfg k).threads[H]? = some u → stepOne A u H (cfg k).mem = some outs →
    .ok oc ∈ outs → PB u.st → (if Z u.st = true then PE oc.thread.st else PL oc.thread.st) ∧
      oc.thread.views.coh = u.views.coh

namespace SpinCells

variable {A : Arch} {cfg : Nat → Config I} {l : Loc} {H n m : Nat} {PL PC PB PE : I.State → Prop}
  {tkv rv : I.State → Nat} {Z : I.State → Bool} (C : SpinCells A cfg l H n m PL PC PB PE tkv rv Z)
include C

omit C in
/-- After `H`'s step, `H`'s thread is the outcome's. -/
theorem wt {k : Nat} {u : Thread I} {oc : Outcome I} (hu : (cfg k).threads[H]? = some u)
    (he : cfg (k + 1) = (cfg k).withThread H oc.thread oc.mem) : (cfg (k + 1)).threads[H]? = some oc.thread := by
  rw [he]; exact SpinStep.wt_tid hu

/-- **In the spin loop with an up-to-date view of `owner`, `H` enters its
critical section**: contradiction. -/
theorem spin_false {j : Nat} (hj : n ≤ j) {u : Thread I} (hu : (cfg j).threads[H]? = some u)
    (hp : PL u.st ∨ PC u.st ∨ PB u.st) (hc : (cfg n).mem.lastWrite l ≤ u.views.getCoh l) : False := by
  -- the branch with `Z` set
  have pBz : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PB u.st → Z u.st = true → False := by
    intro j hj u hu hpc hz
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    have hn := (C.bne k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hpc)).1
    simp only [e1, hz, ↓reduceIte] at hn
    exact C.cs _ (by omega) _ (wt hu' he) hn
  -- the compare with the loaded value `m`
  have pC : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PC u.st → rv u.st = m → False := by
    intro j hj u hu hpc h4
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    obtain ⟨hn, hz, -⟩ := C.cmp k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hpc)
    have h3 := C.tk k (by omega) u' hu' (by rw [e1]; exact hpc)
    exact pBz _ (by omega) _ (wt hu' he) hn (hz.mpr (by rw [e1, h4, ← e1, h3]))
  -- the load with an up-to-date view
  have pL : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PL u.st →
      (cfg n).mem.lastWrite l ≤ u.views.getCoh l → False := by
    intro j hj u hu hpc hc
    obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    obtain ⟨hn, hv, -⟩ := C.ld k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hpc)
    have hv := hv (by rw [C.lw k (by omega), e2]; exact hc)
    exact pC _ (by omega) _ (wt hu' he) hn (by rw [hv, C.fval k (by omega)])
  -- the branch, then the compare, with an up-to-date view
  have pB : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PB u.st →
      (cfg n).mem.lastWrite l ≤ u.views.getCoh l → False := by
    intro j hj u hu hpc hc
    obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    obtain ⟨hn, hcoh⟩ := C.bne k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hpc)
    cases hz : Z u'.st
    · rw [hz] at hn
      refine pL _ (by omega) _ (wt hu' he) hn ?_
      rw [SpinSwpStep.getCoh_congr hcoh, e2]; exact hc
    · exact pBz k (by omega) u' hu' (by rw [e1]; exact hpc) hz
  rcases hp with hp | hp | hp
  · exact pL j hj u hu hp hc
  · obtain ⟨k, hk, u', hu', e1, e2, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    obtain ⟨hn, -, hcoh⟩ := C.cmp k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hp)
    refine pB _ (by omega) _ (wt hu' he) hn ?_
    rw [SpinSwpStep.getCoh_congr hcoh, e2]; exact hc
  · exact pB j hj u hu hp hc

/-- **`H` reads `owner` infinitely often**, if it never leaves its spin loop. -/
theorem reads_inf (pos : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PL u.st ∨ PC u.st ∨ PB u.st)
    (ex : ∀ j, n ≤ j → ∃ u, (cfg j).threads[H]? = some u) :
    InfOften (fun i => ∃ ts, ReadsAt A cfg H l ts i) := by
  have rL : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PL u.st →
      ∃ k, j ≤ k ∧ ∃ ts, ReadsAt A cfg H l ts k := by
    intro j hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    obtain ⟨-, -, ts, v, ν, hlog⟩ := C.ld k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hpc)
    exact ⟨k, hk, ts, u', outs, oc, hu', hso, ho, he, v, ν, hlog⟩
  have rB : ∀ j, n ≤ j → ∀ u, (cfg j).threads[H]? = some u → PB u.st →
      ∃ k, j ≤ k ∧ ∃ ts, ReadsAt A cfg H l ts k := by
    intro j hj u hu hpc
    obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := C.adv _ hj _ hu
    obtain ⟨hn, -⟩ := C.bne k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hpc)
    cases hz : Z u'.st
    · rw [hz] at hn
      obtain ⟨k', hk', h⟩ := rL (k + 1) (by omega) _ (wt hu' he) hn
      exact ⟨k', by omega, h⟩
    · simp only [hz, ↓reduceIte] at hn
      exact (C.cs _ (by omega) _ (wt hu' he) hn).elim
  intro j0
  obtain ⟨u, hu⟩ := ex (max n j0) (Nat.le_max_left _ _)
  have hj0 := Nat.le_max_right n j0
  rcases pos _ (Nat.le_max_left _ _) _ hu with hp | hp | hp
  · obtain ⟨k, hk, h⟩ := rL _ (Nat.le_max_left _ _) u hu hp; exact ⟨k, by omega, h⟩
  · obtain ⟨k, hk, u', hu', e1, -, outs, oc, hso, ho, he⟩ := C.adv _ (Nat.le_max_left _ _) _ hu
    obtain ⟨hn, -⟩ := C.cmp k (by omega) u' outs oc hu' hso ho (by rw [e1]; exact hp)
    obtain ⟨k', hk', h⟩ := rB (k + 1) (by omega) _ (wt hu' he) hn
    exact ⟨k', by omega, h⟩
  · obtain ⟨k, hk, h⟩ := rB _ (Nat.le_max_left _ _) u hu hp; exact ⟨k, by omega, h⟩

end SpinCells

end Kraken.Promising.Live.TkHolderP
