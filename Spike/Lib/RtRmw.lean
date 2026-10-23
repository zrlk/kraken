/-
**Runtime read-modify-writes** (the heap counter's atomic add,
`Out.ctrRmw`), Kraken side: an RMW whose read is returned (not `noRet`)
runs to no error (`runTree_rmw_ok`); a thread with no promise, its values
at most `|M|`, at one has an outcome with no promise (`rmw_ok`); and an
RMW of a word outside every placed label keeps `Inv1`, landing at a leaf of
its tree with memory unchanged or one message appended (`inv1_rtRmw`, the
RMW twin of `Inv1.rtStore`).
-/
import Spike.Lib.ExtThread
import Spike.Bridge.Progress
import Scc.Sem.Rows1Rmw
import Kraken.Promising.LiveTsoRmw

namespace Spike.Lib.RtRmw

open Kraken.Promising Kraken.Promising.Lower Scc.Sem Spike.Lib.ExtThread
open Kraken.Promising.Live.TicketStep (ctx0)

variable {I : ISA} (A : Arch)


/-- **An RMW whose read is returned runs to no error.** -/
theorem runTree_rmw_ok {σ : Type} (tid : Nat) (iv : InstrViews) (c : Kraken.Promising.Ctx) (k : Kraken.RmwKind)
    (l : Loc)
    (op : Val → Option Val) (f : Val → σ) :
    ∀ x ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v)), ∃ p, x = .ok p := by
  intro x hx
  simp only [runTree, List.mem_flatMap] at hx
  obtain ⟨⟨tr, old, c1⟩, -, hx⟩ := hx
  dsimp only at hx
  split at hx
  · simp only [List.mem_singleton] at hx; exact ⟨_, hx⟩
  · simp only [List.mem_flatMap, List.mem_singleton] at hx
    obtain ⟨_, -, rfl⟩ := hx
    exact ⟨_, rfl⟩

/-- **A thread with no promise, its values at most `|M|`, at an RMW has an
outcome** with no promise: the read of the last write, and the write, if
any, at the fresh timestamp `|M| + 1`. -/
theorem rmw_ok {t : Thread I} {tid : Nat} {mem : Memory} (hp : t.prom = []) (hb : t.Bnd mem.last)
    {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false L op fun v => .done (g v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  have hc : Kraken.Promising.Ctx.Bnd (ctx0 tid t mem) := ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hiv : (instrViews t (I.deps t.st)).Le (ctx0 tid t mem).mem.last := instrViews_le hb.regs _
  have hp0 : (ctx0 tid t mem).prom = [] := hp
  obtain ⟨c', hr, hpc⟩ : ∃ c', .ok (g ((ctx0 tid t mem).mem.finalVal L), c') ∈
      runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) (.rmw k false L op fun v => .done (g v)) ∧
      c'.prom = [] := by
    cases hA : A.rmwFence
    · obtain ⟨c', hr⟩ := Live.SpinStep.run_rmwo_exists A tid _ hA hp0 hc hiv k L op g
      obtain ⟨-, -, -, -, -, -, hpc, -⟩ := Live.SpinStep.run_rmwo A tid _ hA hp0 hr
      exact ⟨c', hr, hpc⟩
    · obtain ⟨c', hr⟩ := Live.TsoRmw.run_rmwo_tso_exists A tid _ hA hp0 hc hiv k L op g
      obtain ⟨-, -, -, -, -, -, hpc, -⟩ := Live.TsoRmw.run_rmwo_tso A tid _ hA hp0 hr
      exact ⟨c', hr, hpc⟩
  obtain ⟨th, hth⟩ := Spike.Bridge.finishInstr_nonempty t (I.deps t.st) (instrViews t (I.deps t.st)) _ c'
  obtain ⟨outs, o, hs, ho, rfl, -⟩ := (stepOne_ok_iff A tid hex).mpr ⟨_, c', hr, hth, rfl⟩
  exact ⟨outs, o, hs, ho, (finishInstr_relKey hth).1.trans hpc⟩

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory} {tid : Nat}
  {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}

/-- **The runtime RMW row**: an RMW of a word outside every placed label is
a source stutter; the thread lands at the leaf of some value read (a value
of the location in memory), memory
is unchanged (no write, or a fulfilled promise) or has the written message
appended, and `Inv1` holds (`MemRelP.fulfil_runtime`,
`MemRelP.runtime_write`). -/
theorem inv1_rtRmw (h : Inv1 Λ lbl lsize ts t tm sm) {k : Kraken.RmwKind} {noRet : Bool} {a : Nat}
    {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    (hout : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains (wordLoc a).addr.toNat)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) :
    ∃ old, o.thread.st = g old ∧ (∃ tr, tm.read? (wordLoc a) tr = some old) ∧
      (o.mem = tm ∨ ∃ new, op old = some new ∧ o.mem = (tm.append ⟨wordLoc a, new, tid⟩).1) ∧
      Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨old, tr, hst, -, hr, hc⟩ :=
    stepOne_rmw_cases A hex hstep ho h.coh fun p hp => (h.mem.tq_le p hp).2
  have hcoh := stepOne_cohP A hstep ho h.coh
  refine ⟨old, hst, ⟨tr, hr⟩, ?_⟩
  rcases hc with ⟨-, hm, hp⟩ | ⟨new, hop, ⟨q, -, hg, -, hm, hp⟩ | ⟨hm, hp⟩⟩
  · exact ⟨.inl hm, inv1_of_step h hstep ho hm hp⟩
  · refine ⟨.inl hm, ?_, hcoh, hm ▸ h.narrow⟩
    rw [hm, hp]
    exact h.mem.fulfil_runtime hg hout
  · refine ⟨.inr ⟨new, hop, hm⟩, ?_, hcoh, hm ▸ Inv1.narrow_append h.narrow rfl⟩
    rw [hm, hp]
    exact h.mem.runtime_write hout

end Spike.Lib.RtRmw
