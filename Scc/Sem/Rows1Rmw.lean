/-
**The read-modify-write row** of the one-thread invariant (`Scc/Sem/Rows1.lean`),
target side: one RMW of a word (AArch64 `swp`/`ldadd`, x86 `xchg`/`lock xadd`).

- `stepOne_rmw_cases`: an instruction that is one RMW of `wordLoc a` reads
  a message that is the thread's latest to the word outside its promises
  (`TLatestP`); if the operation declines to write, memory and promises are
  unchanged; otherwise the write fulfils an outstanding promise `q` of the
  new message above the reading context's coherence view (memory unchanged),
  or appends it (promises unchanged);
- `Inv1.rmw`: the value read represents the source's latest message to the
  address (`MemRelP.latestP_read`); with no write, the invariant holds with
  the source memory unchanged; with a write, paired with a source append of
  any message to the address a value of the new word represents, it holds
  with that message pushed (`MemRelP.fulfil_unmirrored` or
  `MemRelP.store`).

Not here: the source side (the source RMW reads its latest message and
appends), and that the source message read and the one the target read are
the same write.
-/
import Scc.Sem.Rows1

namespace Scc.Sem

open Kraken Kraken.Promising

/-- `rmwFenceOpt` keeps memory and promises. -/
theorem rmwFenceOpt_mem_prom (A : Arch) (c : Ctx) :
    (Lower.rmwFenceOpt A c).mem = c.mem ∧ (Lower.rmwFenceOpt A c).prom = c.prom := by
  unfold Lower.rmwFenceOpt; split
  · exact ⟨fenceStep_mem c .sy, (fenceStep_fields c .sy).2.2.2.2.1⟩
  · exact ⟨rfl, rfl⟩

/-- `rmwFenceOpt` keeps the cover. -/
theorem rmwFenceOpt_cohP (A : Arch) (c : Ctx) : CohStepP c (Lower.rmwFenceOpt A c) := by
  unfold Lower.rmwFenceOpt; split
  · exact fenceStep_cohP c .sy
  · exact id

/-- `rmwBump` keeps memory and promises. -/
theorem rmwBump_mem_prom (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (Lower.rmwBump k noRet l c).mem = c.mem ∧ (Lower.rmwBump k noRet l c).prom = c.prom := by
  unfold Lower.rmwBump; split <;> exact ⟨rfl, rfl⟩

/-- **An RMW reads the latest and fulfils or appends**: an instruction that
is one RMW of `wordLoc a`, run by a thread whose coherence views cover its
unpromised messages and whose promises are messages of `mem`, reads a value
`old` at a timestamp the thread's latest to the word outside its promises.
If `op old = none` memory and promises are unchanged; if `op old = some new`
the write either fulfils an outstanding promise `q` of the new message,
above a view covering the thread's unpromised messages (memory unchanged,
`q` erased), or appends it (promises unchanged). -/
theorem stepOne_rmw_cases {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversP t.views t.prom mem)
    (hpl : ∀ p ∈ t.prom, p ≤ mem.last) :
    ∃ old tr, o.thread.st = g old ∧ TLatestP mem t.prom a tr ∧ mem.read? (wordLoc a) tr = some old ∧
      ((op old = none ∧ o.mem = mem ∧ o.thread.prom = t.prom) ∨
       (∃ new, op old = some new ∧
        ((∃ q ∈ t.prom, mem.get? q = some ⟨wordLoc a, new, tid⟩ ∧
            (∃ vs : Views, CohCoversP vs t.prom mem ∧ vs.getCoh (wordLoc a) < q) ∧
            o.mem = mem ∧ o.thread.prom = t.prom.erase q) ∨
          (o.mem = (mem.append ⟨wordLoc a, new, tid⟩).1 ∧ o.thread.prom = t.prom)))) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_rmw_iff] at hr
  obtain ⟨tr, old, c1, hx, rfl, hcase⟩ := hr
  obtain ⟨hm0, hp0⟩ := rmwFenceOpt_mem_prom A
    ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Ctx)
  have hc0 := rmwFenceOpt_cohP A
    ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Ctx) hc
  obtain ⟨hl, hv⟩ := readSuccs_tlatestP A _ hx hc0
  have hc1 := readSuccs_cohP A _ hx hc0
  have hm1 : c1.mem = mem := by
    obtain ⟨-, -, -, h⟩ := readSuccs_shape A _ hx
    exact (congrArg Ctx.mem h).trans hm0
  have hp1 : c1.prom = t.prom := (readSuccs_prom A _ hx).trans hp0
  rw [hm0, hp0] at hl
  rw [hm0] at hv
  simp only at hc1
  rw [hm1, hp1] at hc1
  refine ⟨old, tr, finishInstr_st hth, hl, hv, ?_⟩
  rw [(finishInstr_relKey hth).1, hm]
  rcases hcase with ⟨hop, rfl⟩ | ⟨new, c2, hop, hw, rfl⟩
  · obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A c1
    exact .inl ⟨hop, h1.trans hm1, h2.trans hp1⟩
  · refine .inr ⟨new, hop, ?_⟩
    obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A
      (Lower.rmwBump (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true })
    obtain ⟨h3, h4⟩ := rmwBump_mem_prom (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true }
    rw [h1, h3, h2, h4]
    simp only
    rcases (Lower.mem_writeSuccs_iff A tid _).mp hw with ⟨q, hq, hg, hok, rfl⟩ | ⟨-, rfl⟩
    · rw [hp1] at hq
      rw [hm1] at hg
      refine .inl ⟨q, hq, hg, ⟨c1.views, hc1, ?_⟩, hm1, ?_⟩
      · unfold Lower.writeOk at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
      · show c1.prom.erase q = _
        rw [hp1]
    · refine .inr ⟨?_, ?_⟩
      · show (c1.mem.append _).1 = _
        rw [hm1]
      · show (c1.prom ++ [c1.mem.last + 1]).erase (c1.mem.last + 1) = t.prom
        rw [hm1, hp1]
        exact List.erase_append_singleton_self fun hmem => by
          have h1 : @LE.le Nat instLENat (mem.last + 1) mem.last := hpl _ hmem
          omega

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The RMW row**: an RMW of the word `a`, placed for the source address
`sa` whose latest source message is `j`. The value read represents `j`'s.
If the operation does not write, memory and promises are unchanged and the
invariant holds with no source memory step; if it writes `new`, then for
every source message `m` to `sa` whose value `new` represents, the
invariant holds with `m` pushed, `m`'s image being the fulfilled promise or
the appended message. -/
theorem rmw (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    (hj : MemRel.SLatest sm sa j) :
    ∃ old, o.thread.st = g old ∧ (∃ m, sm[j]? = some m ∧ ValRep lbl m.val old.toNat) ∧
      ((op old = none ∧ o.mem = tm ∧ o.thread.prom = t.prom ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm) ∨
       (∃ new, op old = some new ∧ ∀ m : WeakMem.Msg, m.loc = sa → ValRep lbl m.val new.toNat →
          ∃ q, Inv1 Λ lbl lsize (fun k => if k = sm.size then some q else ts k) o.thread o.mem
            (sm.push m))) := by
  obtain ⟨old, tr, hst, hl, hv, hc⟩ :=
    stepOne_rmw_cases A hex hstep ho h.coh fun p hp => (h.mem.tq_le p hp).2
  have hcoh := stepOne_cohP A hstep ho h.coh
  refine ⟨old, hst, h.mem.latestP_read hwf h.narrow ha (SLatestP.nil_iff.mpr hj) hl hv, ?_⟩
  rcases hc with ⟨hop, hm, hp⟩ | ⟨new, hop, hc⟩
  · refine .inl ⟨hop, hm, hp, ?_, hcoh, hm ▸ h.narrow⟩
    rw [hm, hp]; exact h.mem
  · refine .inr ⟨new, hop, fun m hml hvm => ?_⟩
    have ha' : wordAddr lbl m.loc = some a := hml ▸ ha
    have hoff' : m.loc.offset < lsize m.loc.label := hml ▸ hoff
    rcases hc with ⟨q, hq, hg, ⟨vs, hvs, hlt⟩, hm, hp⟩ | ⟨hm, hp⟩
    · refine ⟨q, ?_, hcoh, hm ▸ h.narrow⟩
      rw [hm, hp]
      refine h.mem.fulfil_unmirrored hq hg ha' hoff' hvm ?_
      intro k mk k' hk hl' ht
      obtain ⟨k'', a', v', ht', ha'', hw, -⟩ := h.mem.mem_rep k mk hk
      rw [ht] at ht'; cases ht'
      rw [hl', ha'] at ha''; cases ha''
      rcases Nat.eq_zero_or_pos k' with rfl | hpos
      · exact (h.mem.tq_le q hq).1
      · obtain ⟨w, hgw, hwl, -⟩ := MemRel.wordAt_msg h.narrow hpos hw
        have := hvs k' w hgw (h.mem.tq_img k k' ht)
        rw [hwl] at this
        have h1 : @LT.lt Nat instLTNat (vs.getCoh (wordLoc a)) q := hlt
        have h2 : @LE.le Nat instLENat k' (vs.getCoh (wordLoc a)) := this
        omega
    · refine ⟨tm.last + 1, ?_, hcoh, hm ▸ narrow_append h.narrow rfl⟩
      rw [hm, hp]
      simpa using h.mem.store (tid := tid) ha' hoff' hvm false

end Inv1

end Scc.Sem
