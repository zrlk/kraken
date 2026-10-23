/-
**The source side of the one-thread memory rows** (`Scc/DESIGN.md` §9.0,
"Never-mirror for M1"): the source steps of WeakCore's promise machine that
the target rows of `Scc/Sem/Rows1.lean` pair with, one word, one thread.

Under never-mirror the source thread makes no promise, so its store always
appends, and its load can always read the latest message to the address:

- `stepStore_append`: `Promises.stepStore` can append, whatever the thread's
  promises;
- `stepStore_noProm`: with no promise, appending is all it can do;
- `stepLoad_latest`: `Promises.stepLoad` can read the latest message to the
  address (`MemRel.readable_latest`), whatever the read bound;
- `Inv1.store_src`: a target store and a promise-free source store keep
  `Inv1`, for every source outcome;
- `Inv1.load_src`: a target load and the source load of the latest message:
  the source has an outcome reading it, and the target's value represents
  it;
- `wordAddr_of_valRep_loc0`, `wordLoc_toNat`: from an untagged locative
  the target address represents to the word the rows take.

Not here: the lift through `TermRun.storeUnits`/`loadUnits` and the `Out`
rows of `Spike/Lib/Seg.lean`.
-/
import Scc.Sem.Rows1

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **A source store can always append** the message of its value and view
at `mem.size`. -/
theorem stepStore_append (k : Promises.Knobs) (arch : WeakMem.Arch) (mem : WeakMem.Memory) (th : Promises.Thread)
    (a : WeakMem.Address) (e : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    ∃ th', (mem.push ⟨a, Promises.rmwNewVal th.regs e, Promises.storeMview th e deps rel⟩, th') ∈
      Promises.stepStore k arch mem th a e deps rel := by
  cases e <;> exact ⟨_, List.mem_append_left _ (List.mem_singleton.mpr rfl)⟩

/-- **A promise-free source store only appends.** -/
theorem stepStore_noProm {k : Promises.Knobs} {arch : WeakMem.Arch} {mem : WeakMem.Memory} {th : Promises.Thread}
    {a : WeakMem.Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} (hp : th.promises = [])
    {x : WeakMem.Memory × Promises.Thread} (hx : x ∈ Promises.stepStore k arch mem th a e deps rel) :
    x.1 = mem.push ⟨a, Promises.rmwNewVal th.regs e, Promises.storeMview th e deps rel⟩ ∧ x.2.promises = [] := by
  unfold Promises.stepStore at hx
  simp only [hp, List.filterMap_nil, List.append_nil, List.mem_singleton] at hx
  subst hx
  exact ⟨by cases e <;> rfl, rfl⟩

/-- **A source load can always read the latest message** to its address:
the outcome whose destination register holds that message's value, view
and timestamp. -/
theorem stepLoad_latest (arch : WeakMem.Arch) {mem : WeakMem.Memory} (pairs : List Nat) (th : Promises.Thread)
    (dst : WeakMem.Reg) {a : WeakMem.Address} (deps : List WeakMem.Reg) (acq : Bool) {j : Nat}
    (hj : MemRel.SLatest mem a j) {m : WeakMem.Msg} (hm : mem[j]? = some m) :
    ∃ th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq, th'.regs dst = ⟨m.val, m.view, j⟩ := by
  have hjs : j < mem.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hmj : mem[j]! = m := by
    rw [getElem!_pos mem j hjs]; exact (Array.getElem?_eq_some_iff.mp hm).2
  refine ⟨_, List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hjs, MemRel.readable_latest hj⟩, rfl⟩, ?_⟩
  simp [hmj]

/-- **An untagged locative's word**: a target word representing `.loc sa 0`
is the word address of `sa`. -/
theorem wordAddr_of_valRep_loc0 {lbl : WeakMem.AllocLabel → Option Nat} {sa : WeakMem.Address} {v : Nat}
    (h : ValRep lbl (.loc sa 0) v) : wordAddr lbl sa = some v := by
  obtain ⟨-, x, hx, rfl⟩ := h
  simpa using hx

/-- The 8-byte location of a 64-bit address is the word location of its
value. -/
theorem wordLoc_toNat (A : BitVec 64) : wordLoc A.toNat = ⟨A, 8⟩ := by
  simp [wordLoc]

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The store row, both sides**: a target store of `v` to the word `a`
placed for the source address `sa`, and any outcome of a promise-free
source store to `sa` of a value `v` represents: the invariant holds after
both, the source outcome having no promise. -/
theorem store_src (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kr : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {k : Promises.Knobs} {arch : WeakMem.Arch} {th : Promises.Thread} {sa : WeakMem.Address}
    {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} (hp : th.promises = [])
    (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    (hv : ValRep lbl (Promises.rmwNewVal th.regs e) v.toNat)
    {x : WeakMem.Memory × Promises.Thread} (hx : x ∈ Promises.stepStore k arch sm th sa e deps rel) :
    o.thread.st = s ∧ x.2.promises = [] ∧
      ∃ q, Inv1 Λ lbl lsize (fun k => if k = sm.size then some q else ts k) o.thread o.mem x.1 := by
  obtain ⟨hx1, hx2⟩ := stepStore_noProm hp hx
  obtain ⟨hst, q, hi⟩ := h.store A hex hstep ho (m := ⟨sa, _, Promises.storeMview th e deps rel⟩) ha hoff hv
  exact ⟨hst, hx2, q, hx1 ▸ hi⟩

/-- **The load row, both sides**: a target load of the word `a` placed for
the source address `sa`, whose latest source message is `j`: the source
load has an outcome reading `j`, and the target's value represents the
value read. -/
theorem load_src (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some a) (hj : MemRel.SLatest sm sa j)
    (arch : WeakMem.Arch) (pairs : List Nat) (th : Promises.Thread) (dst : WeakMem.Reg) (deps : List WeakMem.Reg)
    (acq : Bool) :
    o.mem = tm ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm ∧
      ∃ v, o.thread.st = g v ∧ ∃ m th', sm[j]? = some m ∧ th' ∈ Promises.stepLoad arch sm pairs th dst sa deps acq ∧
        th'.regs dst = ⟨m.val, m.view, j⟩ ∧ ValRep lbl m.val v.toNat := by
  obtain ⟨hm, -, hi, v, hst, m, hmj, hv⟩ := h.load hwf A hex hstep ho ha hj
  obtain ⟨th', hth', hreg⟩ := stepLoad_latest arch pairs th dst deps acq hj hmj
  exact ⟨hm, hi, v, hst, m, th', hmj, hth', hreg, hv⟩

end Inv1

end Scc.Sem
