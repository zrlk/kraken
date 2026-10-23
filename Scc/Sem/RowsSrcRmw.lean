/-
**The source side of the read-modify-write row** (`Scc/Sem/Rows1Rmw.lean`),
under never-mirror: the source RMW of WeakCore's promise machine reads the
latest message to its address and appends, as the source store does
(`Scc/Sem/RowsSrc.lean`).

- `rmwAdjacent_latest`: the latest message to an address and an append are
  adjacent in its modification order;
- `stepRmwAt_latest`, `stepRmw_latest`: a source RMW has an outcome reading
  the latest message, which appends the written value if the RMW succeeds
  on the value read and leaves memory alone if it fails, the promises
  unchanged;
- `Inv1.rmw_src`: a target RMW and that source outcome keep `Inv1`, given
  that the two operations agree on represented values;
- `stepLoad_promises`, `Inv1.rmw_ls_src`: a target RMW that writes, and the
  source swap as a load of the latest message followed by a promise-free
  store (`TermRun.xchgAt`'s `loadUnits` then `storeUnits`, one step), keep
  `Inv1`.

Not here: the lift through `TermRun.xchgAt` and the `Out` rows.
-/
import Scc.Sem.Rows1Rmw
import Scc.Sem.RowsSrc

namespace Scc.Sem

open Kraken Kraken.Promising

/-- The latest message to `a` and an append at `mem.size` are adjacent in
`a`'s modification order. -/
theorem rmwAdjacent_latest {mem : WeakMem.Memory} {a : WeakMem.Address} {j : Nat}
    (hj : MemRel.SLatest mem a j) (hjs : j < mem.size) : WeakMem.rmwAdjacent mem a j mem.size = true := by
  obtain ⟨-, hjl⟩ := hj
  simp only [WeakMem.rmwAdjacent, WeakMem.betweenAt, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.any_eq_false, List.mem_range, not_and]
  refine ⟨hjs, fun t' _ hlt hx => ?_⟩
  cases ht : mem[t']? with
  | none => rw [ht] at hx; cases hx
  | some mt =>
    rw [ht] at hx
    simp only [Option.elim, decide_eq_true_eq] at hx
    exact hjl t' mt hlt.1 ht hx

/-- **`stepRmwAt` can read the latest message and append** (see
`stepRmw_latest`). -/
theorem stepRmwAt_latest (k : Promises.Knobs) (arch : WeakMem.Arch) {mem : WeakMem.Memory} (pairs : List Nat)
    (th : Promises.Thread) (dst : WeakMem.Reg) {a : WeakMem.Address} (kind : WeakMem.RmwKind) (newv : WeakMem.Expr)
    (deps : List WeakMem.Reg) (acq rel : Bool) {j : Nat} (hj : MemRel.SLatest mem a j) {m : WeakMem.Msg}
    (hm : mem[j]? = some m) :
    ∃ mem' th', (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel ∧
      th'.regs dst = Promises.rmwDst kind acq m j ∧ th'.promises = th.promises ∧
      (WeakMem.rmwSucceeds kind m.val = true →
        ∃ mv, mem' = mem.push ⟨a, kind.apply m.val (Promises.rmwNewVal th.regs newv), mv⟩) ∧
      (WeakMem.rmwSucceeds kind m.val = false → mem' = mem) := by
  have hjs : j < mem.size := (Array.getElem?_eq_some_iff.mp hm).1
  have hmj : mem[j]! = m := by
    rw [getElem!_pos mem j hjs]; exact (Array.getElem?_eq_some_iff.mp hm).2
  have hjc : j ∈ (List.range mem.size).filter fun t =>
      WeakMem.readable mem a t (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) a) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hjs, MemRel.readable_latest hj⟩
  unfold Promises.stepRmwAt
  cases hs : WeakMem.rmwSucceeds kind m.val
  · exact ⟨mem, _, List.mem_flatMap.mpr ⟨j, hjc, by
        simp only [hmj, hs, Bool.not_false, ↓reduceIte]; exact List.mem_singleton.mpr rfl⟩,
      by split <;> simp [Promises.stepFence], by split <;> simp [Promises.stepFence], by simp, fun _ => rfl⟩
  · exact ⟨_, _, List.mem_flatMap.mpr ⟨j, hjc, by
        simp only [hmj, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, rmwAdjacent_latest hj hjs]
        exact List.mem_append_left _ (List.mem_singleton.mpr rfl)⟩,
      by split <;> simp [Promises.stepFence], by split <;> simp [Promises.stepFence],
      fun _ => ⟨_, rfl⟩, by simp⟩

/-- **A source RMW can read the latest message and append**: for the
latest message `m` (at `j`) to `a`, some outcome leaves `rmwDst kind acq m j`
in the destination and the promises unchanged; if the RMW succeeds on
`m`'s value, its memory is `mem` with `kind.apply m.val (rmwNewVal th.regs
newv)` appended at `mem.size`, and if it fails, `mem`. -/
theorem stepRmw_latest (k : Promises.Knobs) (arch : WeakMem.Arch) {mem : WeakMem.Memory} (pairs : List Nat)
    (th : Promises.Thread) (dst : WeakMem.Reg) {a : WeakMem.Address} (kind : WeakMem.RmwKind) (newv : WeakMem.Expr)
    (deps : List WeakMem.Reg) (acq rel : Bool) {j : Nat} (hj : MemRel.SLatest mem a j) {m : WeakMem.Msg}
    (hm : mem[j]? = some m) :
    ∃ mem' th', (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel ∧
      th'.regs dst = Promises.rmwDst kind acq m j ∧ th'.promises = th.promises ∧
      (WeakMem.rmwSucceeds kind m.val = true →
        ∃ mv, mem' = mem.push ⟨a, kind.apply m.val (Promises.rmwNewVal th.regs newv), mv⟩) ∧
      (WeakMem.rmwSucceeds kind m.val = false → mem' = mem) := by
  unfold Promises.stepRmw
  have hr : (if arch = .tso then Promises.stepFence th .sy else th).regs = th.regs := by
    split <;> rfl
  have hp : (if arch = .tso then Promises.stepFence th .sy else th).promises = th.promises := by
    split <;> rfl
  have := stepRmwAt_latest k arch pairs (if arch = .tso then Promises.stepFence th .sy else th) dst kind newv
    deps acq rel hj hm
  rw [hr, hp] at this
  exact this

/-- A source load changes the registers and views only: the promises are
kept. -/
theorem stepLoad_promises {arch : WeakMem.Arch} {mem : WeakMem.Memory} {pairs : List Nat} {th : Promises.Thread}
    {dst : WeakMem.Reg} {a : WeakMem.Address} {deps : List WeakMem.Reg} {acq : Bool} {th' : Promises.Thread}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) : th'.promises = th.promises := by
  unfold Promises.stepLoad at h
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
  rfl

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The RMW row, both sides**: a target RMW of the word `a` placed for
the source address `sa`, whose latest source message is `j`, and the source
RMW reading `j`. `hop` says the two operations agree on represented values:
the target declines to write exactly when the source fails, and a value
the target writes represents the one the source writes. Then some source
outcome reads `j`, its promises unchanged, the target's value represents
the value read, and the invariant holds after both. -/
theorem rmw_src (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {kt : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw kt noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    (hj : MemRel.SLatest sm sa j)
    (k : Promises.Knobs) (arch : WeakMem.Arch) (pairs : List Nat) (th : Promises.Thread) (dst : WeakMem.Reg)
    (kind : WeakMem.RmwKind) (newv : WeakMem.Expr) (deps : List WeakMem.Reg) (acq rel : Bool)
    (hop : ∀ old m, sm[j]? = some m → ValRep lbl m.val old.toNat →
      (op old = none ↔ WeakMem.rmwSucceeds kind m.val = false) ∧
      ∀ new, op old = some new → ValRep lbl (kind.apply m.val (Promises.rmwNewVal th.regs newv)) new.toNat) :
    ∃ old, o.thread.st = g old ∧ ∃ m mem' th', sm[j]? = some m ∧ ValRep lbl m.val old.toNat ∧
      (mem', th') ∈ Promises.stepRmw k arch sm pairs th dst sa kind newv deps acq rel ∧
      th'.regs dst = Promises.rmwDst kind acq m j ∧ th'.promises = th.promises ∧
      ∃ ts', Inv1 Λ lbl lsize ts' o.thread o.mem mem' := by
  obtain ⟨old, hst, ⟨m, hmj, hv⟩, hc⟩ := h.rmw hwf A hex hstep ho ha hoff hj
  obtain ⟨mem', th', hx, hreg, hprom, hsucc, hfail⟩ :=
    stepRmw_latest k arch pairs th dst kind newv deps acq rel hj hmj
  obtain ⟨hiff, hnew⟩ := hop old m hmj hv
  refine ⟨old, hst, m, mem', th', hmj, hv, hx, hreg, hprom, ?_⟩
  rcases hc with ⟨hnone, -, -, hi⟩ | ⟨new, hsome, hi⟩
  · exact ⟨ts, hfail (hiff.mp hnone) ▸ hi⟩
  · have hs : WeakMem.rmwSucceeds kind m.val = true := by
      cases hr : WeakMem.rmwSucceeds kind m.val
      · rw [hiff.mpr hr] at hsome; cases hsome
      · rfl
    obtain ⟨mv, rfl⟩ := hsucc hs
    obtain ⟨q, hi⟩ := hi ⟨sa, _, mv⟩ rfl (hnew new hsome)
    exact ⟨_, hi⟩

/-- **The swap row, both sides**: the source swap is a load followed by a
store. A target RMW of the word `a` placed for the source address `sa`,
whose latest source message is `j`; the source loads `j` into `dst` and then
stores `e` with no promise. `hop` says the target writes, a value
representing the one the source stores (`e` read in the registers after
the load). Then the source load has an outcome reading `j`, the target's
value represents the value read, and every outcome of the source store
after it keeps `Inv1` with no promise. -/
theorem rmw_ls_src (h : Inv1 Λ lbl lsize ts t tm sm) (hwf : Λ.WF) (A : Arch) {tid : Nat}
    {kt : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw kt noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs)
    {sa : WeakMem.Address} {j : Nat} (ha : wordAddr lbl sa = some a) (hoff : sa.offset < lsize sa.label)
    (hj : MemRel.SLatest sm sa j)
    (arch : WeakMem.Arch) (pairs : List Nat) (th : Promises.Thread) (dst : WeakMem.Reg) (ldeps : List WeakMem.Reg)
    (acq : Bool) (hp : th.promises = [])
    (k : Promises.Knobs) (e : WeakMem.Expr) (sdeps : List WeakMem.Reg) (rel : Bool)
    (hop : ∀ old m (th' : Promises.Thread), sm[j]? = some m → ValRep lbl m.val old.toNat →
      th'.regs dst = ⟨m.val, m.view, j⟩ → th'.promises = [] →
      ∃ new, op old = some new ∧ ValRep lbl (Promises.rmwNewVal th'.regs e) new.toNat) :
    ∃ old, o.thread.st = g old ∧ ∃ m th', sm[j]? = some m ∧ ValRep lbl m.val old.toNat ∧
      th' ∈ Promises.stepLoad arch sm pairs th dst sa ldeps acq ∧ th'.regs dst = ⟨m.val, m.view, j⟩ ∧
      ∀ x ∈ Promises.stepStore k arch sm th' sa e sdeps rel, x.2.promises = [] ∧
        ∃ q, Inv1 Λ lbl lsize (fun k => if k = sm.size then some q else ts k) o.thread o.mem x.1 := by
  obtain ⟨old, hst, ⟨m, hmj, hv⟩, hc⟩ := h.rmw hwf A hex hstep ho ha hoff hj
  obtain ⟨th', hth', hreg⟩ := stepLoad_latest arch pairs th dst ldeps acq hj hmj
  have hp' : th'.promises = [] := (stepLoad_promises hth').trans hp
  obtain ⟨new, hnew, hvn⟩ := hop old m th' hmj hv hreg hp'
  refine ⟨old, hst, m, th', hmj, hv, hth', hreg, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := stepStore_noProm hp' hx
  rcases hc with ⟨hnone, -⟩ | ⟨new', hsome, hi⟩
  · rw [hnone] at hnew; cases hnew
  · rw [hsome] at hnew; cases hnew
    obtain ⟨q, hi⟩ := hi ⟨sa, _, Promises.storeMview th' e sdeps rel⟩ rfl hvn
    exact ⟨hx2, q, hx1 ▸ hi⟩

end Inv1

end Scc.Sem
