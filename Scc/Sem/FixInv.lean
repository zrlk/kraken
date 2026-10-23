/-
**Fixed runtime words** (the X3 memory side): a runtime word the runtime
writes once with a value known per program (hello1: the main thread's
`Tcb.stackLimit`, written by `scc_rt_thread_init`) holds that value or its
initial one in every message, so a runtime load from it lands only for those
values.

The invariant is Kraken's `MemInv G mem` (`Kraken/Promising/PromiseSafe.lean`:
every initial value and every message satisfies `G`; `MemInv.read?`: so does
every value read) for `G = FixG Fix m0`, `Fix` the fixed words (address,
value) and `m0` the memory at load:

- `FixG`; `memInv_fixG_load` (S1): it holds at load, where there is no
  message;
- `fixG_of_placed` (S2): a word of a placed label (`MemRelP`'s `lbl_range`:
  in the heap or the static image) is no fixed word when the fixed words are
  in the pinned region, so `FixG` holds there of any value;
- the rows keep `MemInv G` given their store obligation (S3):
  `stepOne_store_memInv`, `Inv1.store_memInv` and `Inv1.store_fixG` (a
  store to a placed word: the obligation from `fixG_of_placed`),
  `Inv1.rtStore_memInv` (a runtime store: the obligation is the caller's),
  `stepOne_rmw_memInv` and `Inv1.rmw_fixG` (an RMW of a placed word),
  `memInv_promise` (a promise: the obligation is the promised message's,
  the open hypothesis that strengthens `PromShared`).
-/
import Scc.Sem.Rows1Rmw

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **The fixed-word predicate**: at the 8-byte location of a fixed word
`(a, w)`, a value is `w` or the location's initial value in `m0`; anywhere
else, anything. -/
def FixG (Fix : List (Nat × Val)) (m0 : Memory) (l : Loc) (v : Val) : Prop :=
  ∀ a w, (a, w) ∈ Fix → l = ⟨BitVec.ofNat 64 a, 8⟩ → v = w ∨ v = m0.initVal l

/-- **S1: the invariant at load**: a memory with the load memory's initial
values and no message satisfies it. -/
theorem memInv_fixG_load {Fix : List (Nat × Val)} {m0 m : Memory} (hi : m.init = m0.init)
    (hmsgs : m.msgs = #[]) : MemInv (FixG Fix m0) m := by
  refine ⟨fun l a w _ _ => .inr (by simp only [Memory.initVal, hi]), fun w hw => ?_⟩
  simp [hmsgs] at hw

/-- **S2: placed words are not fixed**: under a well-formed layout, with
every fixed word in the pinned region, the word at `x` inside the range of a
label placed by the memory relation (in the heap or the static image) is no
fixed word's location, so any value satisfies `FixG` there. -/
theorem fixG_of_placed {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) {Fix : List (Nat × Val)}
    (hfix : ∀ a w, (a, w) ∈ Fix → Λ.pinned.contains a) {l : WeakMem.AllocLabel} {b x : Nat}
    (hl : lbl l = some b) (hx : (lrange lsize l b).contains x) (m0 : Memory) (v : Val) :
    FixG Fix m0 (wordLoc x) v := by
  intro a w hmem heq
  exfalso
  have hp := hfix a w hmem
  have hpin := hwf.inSpace Λ.pinned (by simp [Layout.regions])
  have hheap := hwf.inSpace Λ.heap (by simp [Layout.regions])
  have hdata := hwf.inSpace Λ.data (by simp [Layout.regions])
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, -⟩ := hwf.disjoint
  simp only [Range.InSpace, Range.contains, Range.Disjoint] at hpin hheap hdata hp hdp hhp
  have hs := (h.lbl_range l b hl).2
  simp only [lrange, Range.contains] at hx
  have hxlt : x < 2 ^ 64 := by
    rcases hs with hs | hs <;> simp only [lrange, Range.Sub] at hs <;> omega
  have hxa : x = a := by
    simp only [wordLoc, Loc.mk.injEq, and_true] at heq
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt (by omega)] at this
  subst hxa
  rcases hs with hs | hs <;> simp only [lrange, Range.Sub] at hs <;> omega

/-- A word placed for an in-bounds source address lies in its label's
range. -/
theorem lrange_contains_of_wordAddr {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {sa : WeakMem.Address} {a : Nat} (ha : wordAddr lbl sa = some a) (ho : sa.offset < lsize sa.label) :
    ∃ b, lbl sa.label = some b ∧ (lrange lsize sa.label b).contains a := by
  simp only [wordAddr, Option.map_eq_some_iff] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := ho
  refine ⟨b, hb, ?_⟩
  simp only [lrange, Range.contains, mul_offset]
  omega

/-- **A promise keeps the invariant** when the promised message satisfies
`G` (for `FixG`, the strengthened promise hypothesis). -/
theorem memInv_promise {G : Loc → Val → Prop} {tm : Memory} (h : MemInv G tm) {w : Msg} (hw : G w.loc w.val) :
    MemInv G (tm.append w).1 :=
  h.append hw

/-- **A plain store keeps the invariant** when the stored value satisfies
`G` at its location: it fulfils (memory unchanged) or appends that
message. -/
theorem stepOne_store_memInv {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hpl : ∀ p ∈ t.prom, p ≤ mem.last)
    {G : Loc → Val → Prop} (hG : MemInv G mem) (hv : G (wordLoc a) v) : MemInv G o.mem := by
  obtain ⟨-, hc⟩ := stepOne_store_cases A hex hstep ho hpl
  rcases hc with ⟨-, -, -, -, hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact hG
  · rw [hm]; exact hG.append hv

/-- **An RMW keeps the invariant** when every value it may write satisfies
`G` at its location. -/
theorem stepOne_rmw_memInv {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversP t.views t.prom mem)
    (hpl : ∀ p ∈ t.prom, p ≤ mem.last) {G : Loc → Val → Prop} (hG : MemInv G mem)
    (hv : ∀ old new, op old = some new → G (wordLoc a) new) : MemInv G o.mem := by
  obtain ⟨old, -, -, -, -, hcase⟩ := stepOne_rmw_cases A hex hstep ho hc hpl
  rcases hcase with ⟨-, hm, -⟩ | ⟨new, hop, ⟨-, -, -, -, hm, -⟩ | ⟨hm, -⟩⟩
  · rw [hm]; exact hG
  · rw [hm]; exact hG
  · rw [hm]; exact hG.append (hv old new hop)

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The store row keeps `MemInv G`** given its store obligation. -/
theorem store_memInv (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {G : Loc → Val → Prop} (hG : MemInv G tm) (hv : G (wordLoc a) v) : MemInv G o.mem :=
  stepOne_store_memInv A hex hstep ho (fun p hp => (h.mem.tq_le p hp).2) hG hv

/-- **The store row keeps the fixed-word invariant**: a store to the word
placed for an in-bounds source address needs no obligation (`fixG_of_placed`)
when the fixed words are in the pinned region. -/
theorem store_fixG (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    {Fix : List (Nat × Val)} (hfix : ∀ a w, (a, w) ∈ Fix → Λ.pinned.contains a) {m0 : Memory}
    (hG : MemInv (FixG Fix m0) tm) : MemInv (FixG Fix m0) o.mem := by
  obtain ⟨b, hb, hc⟩ := lrange_contains_of_wordAddr ha hoff
  exact h.store_memInv A hex hstep ho hG (fixG_of_placed h.mem hwf hfix hb hc m0 v)

/-- **The runtime store row keeps `MemInv G`** given its store obligation
(for `FixG`, the `MemSide` predicate the runtime store row carries). -/
theorem rtStore_memInv (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kr : StoreKind} {L : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false L v fun _ => .done s)) (hL : L.bytes = 8)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {G : Loc → Val → Prop} (hG : MemInv G tm) (hv : G L v) : MemInv G o.mem := by
  have hLw : L = wordLoc L.addr.toNat := by
    obtain ⟨a, b⟩ := L; simp only at hL; subst hL; simp [wordLoc]
  rw [hLw] at hex hv
  exact h.store_memInv A hex hstep ho hG hv

/-- **The RMW row keeps the fixed-word invariant** for an RMW of the word
placed for an in-bounds source address, when the fixed words are in the
pinned region. -/
theorem rmw_fixG (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    {Fix : List (Nat × Val)} (hfix : ∀ a w, (a, w) ∈ Fix → Λ.pinned.contains a) {m0 : Memory}
    (hG : MemInv (FixG Fix m0) tm) : MemInv (FixG Fix m0) o.mem := by
  obtain ⟨b, hb, hc⟩ := lrange_contains_of_wordAddr ha hoff
  exact stepOne_rmw_memInv A hex hstep ho h.coh (fun p hp => (h.mem.tq_le p hp).2) hG
    fun _ new _ => fixG_of_placed h.mem hwf hfix hb hc m0 new

end Inv1

end Scc.Sem
