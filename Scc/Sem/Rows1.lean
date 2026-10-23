/-
**The memory rows of the one-thread relation, promises never mirrored**
(`Scc/DESIGN.md` §9.0, "Never-mirror for M1").

The invariant `Inv1`: the memory relation with promises (`MemRelP`) where
no target promise is mirrored (`tp = []`, `sp = []`) and the unmirrored
ones are exactly the thread's outstanding promises (`tq = t.prom`), the
thread's coherence cover (`CohCoversP`), and every target message 8 bytes
wide (`MemRel.Narrow`). One row per kind of target step:

- `stepOne_store_cases`: a plain store fulfils an outstanding promise above
  the thread's coherence view of the location (memory unchanged) or
  appends (promises unchanged);
- `Inv1.store`: either way, paired with a source append of the stored
  message (`MemRelP.fulfil_unmirrored` with the order side condition from
  the cover, or `MemRelP.store` with `b = false`);
- `Inv1.rtStore`: a plain store outside every placed label, a source
  stutter either way (`MemRelP.fulfil_runtime`, `MemRelP.runtime_write`);
- `Inv1.promise`: a promise step, a source stutter
  (`MemRelP.promise_unmirrored`); `Inv1.promise_cert`: the promised message
  is one word wide when the step is certified and the code writes words
  only (`Wide8Code`, `certOkC_prom_narrow`); `Inv1.promise_cert_on`: the
  same for code writing words only from the states of an invariant
  (`Wide8CodeOn`, `WideInv`, `certOkC_prom_narrow_on`);
- `Inv1.load`: a load reads what the source's latest message to the
  address holds (`MemRelP.latestP_read`, `stepOne_load_tlatestP`), memory
  unchanged;
- `stepOne_fence_eq`, `Inv1.fence`: a fence, memory and promises unchanged;
- `Inv1.congr`, `Inv1.retThread`: a thread change that keeps views and
  promises (a system call's return) keeps the invariant.

Not here: the source side of each row (which `Out` it is, and that the
source may take it), runtime writes outside every label other than
plain stores (`MemRelP.runtime_write`), allocation (`MemRelP.alloc`), the kernel's
steps.
-/
import Scc.Sem.MemRelP
import Scc.Sem.Wide

namespace Scc.Sem

open Kraken Kraken.Promising

/-- `(l ++ [x]).erase x = l` when `x ∉ l`. -/
theorem List.erase_append_singleton_self {l : List Nat} {x : Nat} (hx : x ∉ l) : (l ++ [x]).erase x = l := by
  rw [List.erase_append_right _ hx]; simp

/-- **A plain store fulfils or appends**: an instruction that is one plain
(non-exclusive) store of `v` to `wordLoc a`, run by a thread whose promises
are messages of `mem`, either fulfils an outstanding promise `q` of that
message, above the thread's coherence view of the location, leaving memory
alone and erasing `q`, or appends the message and keeps the promises. -/
theorem stepOne_store_cases {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hpl : ∀ p ∈ t.prom, p ≤ mem.last) :
    o.thread.st = s ∧
      ((∃ q ∈ t.prom, mem.get? q = some ⟨wordLoc a, v, tid⟩ ∧ t.views.getCoh (wordLoc a) < q ∧
          o.mem = mem ∧ o.thread.prom = t.prom.erase q) ∨
        (o.mem = (mem.append ⟨wordLoc a, v, tid⟩).1 ∧ o.thread.prom = t.prom)) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, hw⟩ := hr
  refine ⟨finishInstr_st hth, ?_⟩
  rw [(finishInstr_relKey hth).1, hm]
  rcases (Lower.mem_writeSuccs_iff A tid _).mp hw with ⟨q, hq, hg, hok, rfl⟩ | ⟨-, rfl⟩
  · refine .inl ⟨q, hq, hg, ?_, rfl, rfl⟩
    unfold Lower.writeOk at hok
    simp only [Bool.and_true, decide_eq_true_eq] at hok
    exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok
  · refine .inr ⟨rfl, ?_⟩
    show (t.prom ++ [mem.last + 1]).erase (mem.last + 1) = t.prom
    exact List.erase_append_singleton_self fun hm => by
      have h1 : @LE.le Nat instLENat (mem.last + 1) mem.last := hpl _ hm
      omega

/-- **A fence leaves memory and promises alone.** -/
theorem stepOne_fence_eq {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : FenceKind} {s : I.State} (hex : I.exec t.st = some (.fence k fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) :
    o.thread.st = s ∧ o.mem = mem ∧ o.thread.prom = t.prom := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_fence_iff] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨finishInstr_st hth, hm.trans (fenceStep_mem _ k), (finishInstr_relKey hth).1.trans
    (fenceStep_fields _ k).2.2.2.2.1⟩

/-- **The one-thread invariant, promises never mirrored.** -/
structure Inv1 {I : ISA} (Λ : Layout) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (ts : Nat → Option Nat) (t : Thread I) (tm : Memory) (sm : WeakMem.Memory) : Prop where
  /-- The memory relation; the unmirrored promises are the thread's. -/
  mem : MemRelP Λ lbl lsize ts tm sm [] t.prom []
  /-- The thread's coherence views cover what it has not promised. -/
  coh : CohCoversP t.views t.prom tm
  /-- Every target message is one word. -/
  narrow : MemRel.Narrow tm

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- An appended one-word message keeps `Narrow`. -/
theorem narrow_append {tm : Memory} (hn : MemRel.Narrow tm) {w : Msg} (hw : w.loc.bytes = 8) :
    MemRel.Narrow (tm.append w).1 := by
  intro k w' hk
  by_cases he : k = tm.last + 1
  · subst he; rw [Memory.get?_append_new] at hk; cases hk; exact hw
  · exact hn k w' (CohCoversP.get?_append_ne hk he)

/-- **The store row**: a plain store of `v` to the word `a` placed for the
source address `m.loc`, paired with a source append of `m` (a value `v`
represents). Whether the target fulfils or appends, the invariant holds of
the thread after and the source memory with `m` pushed, `m`'s image being
the fulfilled promise or the appended message; earlier images are kept. -/
theorem store (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {m : WeakMem.Msg} (ha : wordAddr lbl m.loc = some a) (hoff : m.loc.offset < lsize m.loc.label)
    (hv : ValRep lbl m.val v.toNat) :
    o.thread.st = s ∧ ∃ q, Inv1 Λ lbl lsize (fun k => if k = sm.size then some q else ts k) o.thread o.mem (sm.push m) := by
  obtain ⟨hst, hc⟩ := stepOne_store_cases A hex hstep ho fun p hp => (h.mem.tq_le p hp).2
  have hcoh := stepOne_cohP A hstep ho h.coh
  refine ⟨hst, ?_⟩
  rcases hc with ⟨q, hq, hg, hlt, hm, hp⟩ | ⟨hm, hp⟩
  · refine ⟨q, ?_, hcoh, hm ▸ h.narrow⟩
    rw [hm, hp]
    refine h.mem.fulfil_unmirrored hq hg ha hoff hv ?_
    intro k mk k' hk hl ht
    obtain ⟨k'', a', v', ht', ha', hw, -⟩ := h.mem.mem_rep k mk hk
    rw [ht] at ht'; cases ht'
    rw [hl, ha] at ha'; cases ha'
    rcases Nat.eq_zero_or_pos k' with rfl | hpos
    · exact (h.mem.tq_le q hq).1
    · obtain ⟨w, hgw, hwl, -⟩ := MemRel.wordAt_msg h.narrow hpos hw
      have := h.coh k' w hgw (h.mem.tq_img k k' ht)
      rw [hwl] at this
      have h1 : @LT.lt Nat instLTNat (t.views.getCoh (wordLoc a)) q := hlt
      have h2 : @LE.le Nat instLENat k' (t.views.getCoh (wordLoc a)) := this
      omega
  · refine ⟨tm.last + 1, ?_, hcoh, hm ▸ narrow_append h.narrow rfl⟩
    · rw [hm, hp]
      simpa using h.mem.store (tid := tid) ha hoff hv false

/-- **The runtime store row**: a plain store of `v` to an 8-byte location
outside every placed label's range is a source stutter, whether the target
fulfils an outstanding promise (`MemRelP.fulfil_runtime`) or appends
(`MemRelP.runtime_write`). -/
theorem rtStore (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kr : StoreKind} {L : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false L v fun _ => .done s)) (hL : L.bytes = 8)
    (hout : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) :
    o.thread.st = s ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  have hLw : L = wordLoc L.addr.toNat := by
    obtain ⟨a, b⟩ := L; simp only at hL; subst hL; simp [wordLoc]
  have hout' : ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains (wordLoc L.addr.toNat).addr.toNat := by
    rwa [← hLw]
  rw [hLw] at hex
  obtain ⟨hst, hc⟩ := stepOne_store_cases A hex hstep ho fun p hp => (h.mem.tq_le p hp).2
  have hcoh := stepOne_cohP A hstep ho h.coh
  refine ⟨hst, ?_⟩
  rcases hc with ⟨q, -, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · refine ⟨?_, hcoh, hm ▸ h.narrow⟩
    rw [hm, hp]
    exact h.mem.fulfil_runtime hg hout'
  · refine ⟨?_, hcoh, hm ▸ narrow_append h.narrow rfl⟩
    rw [hm, hp]
    exact h.mem.runtime_write hout'

/-- **The promise row**: a promise step of the thread (`PromSemC`) is a
source stutter; the promise joins the unmirrored ones. -/
theorem promise (h : Inv1 Λ lbl lsize ts t tm sm) {w : Msg} (hw : w.loc.bytes = 8) :
    Inv1 Λ lbl lsize ts (Live.Sem.promThread t tm w) (tm.append w).1 sm :=
  ⟨h.mem.promise_unmirrored w, h.coh.promise w, narrow_append h.narrow hw⟩

/-- **The promise row, certified**: for code whose every write is one word
wide, a certified promise step (`PromSemC`'s certificate) promises a
one-word message, so the invariant holds after it. -/
theorem promise_cert (h : Inv1 Λ lbl lsize ts t tm sm) {A : Arch} {cs : CertSem I}
    (hW : Wide8Code cs.exec) {tid : Nat} {w : Msg}
    (hc : CertOkC A cs tid (Live.Sem.promThread t tm w) (tm.append w).1) :
    Inv1 Λ lbl lsize ts (Live.Sem.promThread t tm w) (tm.append w).1 sm :=
  h.promise (certOkC_prom_narrow hW hc (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    Memory.get?_append_new)

/-- **The promise row, certified, on an invariant**: `promise_cert` for code
whose trees write words only from the states of an invariant `P` that its
instructions keep, from a thread at a `P` state. -/
theorem promise_cert_on (h : Inv1 Λ lbl lsize ts t tm sm) {A : Arch}
    {cs : CertSem I} {P : I.State → Prop} (hW : Wide8CodeOn P cs.exec)
    (hP : WideInv P cs.exec) (hst : P t.st) {tid : Nat} {w : Msg}
    (hc : CertOkC A cs tid (Live.Sem.promThread t tm w) (tm.append w).1) :
    Inv1 Λ lbl lsize ts (Live.Sem.promThread t tm w) (tm.append w).1 sm :=
  h.promise (certOkC_prom_narrow_on hW hP (t := Live.Sem.promThread t tm w) hst hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) Memory.get?_append_new)

/-- **The load row**: a load of the word `a`, placed for the source address
`sa` whose latest source message is `j`, leaves memory alone and continues
with a value that represents `j`'s. -/
theorem load (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some a) (hj : MemRel.SLatest sm sa j) :
    o.mem = tm ∧ o.thread.prom = t.prom ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm ∧
      ∃ v, o.thread.st = g v ∧ ∃ m, sm[j]? = some m ∧ ValRep lbl m.val v.toNat := by
  obtain ⟨hm, ts0, v, hst, hl, hr⟩ := stepOne_load_tlatestP A hex hstep ho h.coh
  have hp : o.thread.prom = t.prom := by
    obtain ⟨st, c', hrun, hth, -⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
    rw [Lower.run_load_iff] at hrun
    obtain ⟨ts1, v1, hx, -⟩ := hrun
    exact (finishInstr_relKey hth).1.trans (readSuccs_prom A _ hx)
  refine ⟨hm, hp, ⟨?_, stepOne_cohP A hstep ho h.coh, hm ▸ h.narrow⟩, v, hst,
    h.mem.latestP_read hwf h.narrow ha (SLatestP.nil_iff.mpr hj) hl hr⟩
  rw [hm, hp]; exact h.mem

/-- **Only views and promises matter**: a thread with the same views and
promises satisfies the invariant. -/
theorem congr {t' : Thread I} (h : Inv1 Λ lbl lsize ts t tm sm) (hv : t'.views = t.views)
    (hp : t'.prom = t.prom) : Inv1 Λ lbl lsize ts t' tm sm :=
  ⟨hp ▸ h.mem, hv ▸ hp ▸ h.coh, h.narrow⟩

/-- **A system call's return keeps the invariant** (`Kernel.retThread`:
registers and pc only). -/
theorem retThread {K : Kernel.Abi I} (h : Inv1 Λ lbl lsize ts t tm sm) (r : BitVec 64) :
    Inv1 Λ lbl lsize ts (Kernel.retThread K t r) tm sm :=
  h.congr (retThread_views K t r) (Kernel.retThread_prom (K := K) t r)

/-- **The fence row**: memory and promises unchanged, no source memory
step. -/
theorem fence (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat} {k : FenceKind} {s : I.State}
    (hex : I.exec t.st = some (.fence k fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) :
    o.thread.st = s ∧ o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq A hex hstep ho
  refine ⟨hst, hm, ?_, stepOne_cohP A hstep ho h.coh, hm ▸ h.narrow⟩
  rw [hm, hp]; exact h.mem

end Inv1

end Scc.Sem
