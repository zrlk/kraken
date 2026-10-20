/-
Cell rules of the x64 `xchg` spinlock worker (`X64SpinTrees.spinWorker`, the
`worker` of `Kraken/Examples/LockFree/X64/spinlock2.kl`) for the erasure WP
with bounded reach (`EvTree.EraseWPR`, `SLR/ReachRules.lean`; 
stretch task).

Each `wp_*` theorem restates a cell's tree (`X64SpinTrees.exec_*`) in the
form `ThreadRuleR.wp` consumes: `isa.exec st = some tree →
tree.EraseWPR A tid iv rF T c t Post r g cx`, the remaining obligations stated
on `Post` at the cell's successor states. They are generic in the arch `A`,
the views `iv`, the frame `rF`, the validity set `T`, the postcondition
`Post` and the resource/ghost state: the program-specific choices (which
release predicate holds the lock, the resource split) stay with the caller.

- silent cells (`testl`, `jne`, `movl $1`, `addl`, `jmp`): `Post` at the
  successor (for `testl`, at both values of the undefined `AF`), same
  resources and context;
- the plain loads (`movl (%rdi)`, `movl (%rsi)`): `Post` at every read
  successor (`EvTree.eraseWPR_load`);
- the plain stores (counter, unlock): the obligations of
  `EvTree.eraseWPR_store_pend` (a store fulfilling a pending, prepaid
  promise needs only `Post`), with `Post` for the continuation;
- `xchgl` (`acqRel`, always writes): the obligations of
  `EvTree.eraseWPR_rmw_pend'` (`SLR/RmwPendR.lean`: own pending promises,
  e.g. the prepaid unlock, allowed when they do not claim the slot read);
  there is no failure branch.

## Release and acquire under TSO

The cells' events carry the ISA's kinds (`.plain` loads and stores, an
`.acqRel` RMW); the arch profile maps them. The SLR erasure rules
(`ErAt.store`, `EvTree.eraseWPR_store_pend`, `eraseWPR_store_rel`) do
not inspect the store kind: whether a write carries release slots
(`rel = true`) is a resource-level choice. The kinds matter where a proof
uses view facts, and there `Arch.tso` (the profile the x64 explorer and
litmus runner use with `X64.isa`) supplies them by `rfl`:

- `tso_plainStore`: a plain store is a release (`.rel`), so the unlock
  `movl $0,(%rdi)` is a release write (and an outstanding promise of it is a
  promised release, `Thread.RelFulfils`: under TSO *every* plain store
  promise is, the counter store's too);
- `tso_plainLoad_isAcquire`: a plain load is an (RCpc) acquire, the
  hypothesis of `readSuccs_acq_vwNew`/`rmw_tr_le_wfloor_acq`;
- `tso_xchg_acqRel`: `xchgl`'s RMW is acquire-release and returns its value,
  the hypothesis of `rmw_tr_le_wfloor_acqRel` (the floor bound of an RMW
  that claims update slots).
-/
import Kraken.Promising.SLR.X64SpinTrees
import Kraken.Promising.SLR.RmwPendR

namespace Kraken.Promising.SLR.X64SpinTrees

open Kraken Kraken.Promising Kraken.Promising.X64

/-- Under TSO a plain store is a release store. -/
theorem tso_plainStore : Arch.tso.storeKind .plain = .rel := rfl

/-- Under TSO a plain load is an acquire (RCpc). -/
theorem tso_plainLoad_isAcquire : (Arch.tso.loadKind .plain).isAcquire = true := rfl

/-- Under TSO `xchgl`'s RMW (`.acqRel`, returning) is acquire-release: the
hypothesis of `rmw_tr_le_wfloor_acqRel`. -/
theorem tso_xchg_acqRel : (Arch.tso.rmwKind .acqRel == .acqRel && !false) = true := rfl

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]
  {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config isa}
  {t : Thread isa} {Post : State → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

/-- `movl (%rdi),%eax` (position 1). -/
theorem wp_load_lock (st : State) (h : At st 1) {l : BitVec 64}
    (hx : st.st.1.regs.get64 .rdi = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none)
    (hk : ∀ x ∈ readSuccs A iv cx .plain false ⟨l, 4⟩,
      Post (goto st { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) (BitVec.setWidth 32 x.2.1) }
        ((layout spinWorker).addrOf 2)) r g x.2.2) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_load_lock st h hx hdm, Option.some.injEq] at ht
  subst ht
  exact EvTree.eraseWPR_load hk

/-- `testl %eax,%eax` (position 2). -/
theorem wp_test (st : State) (h : At st 2)
    (hk : ∀ i : Fin 2, Post (goto st
      (let f : StatusFlags := .from_result (st.st.1.regs.get (.low .rax .W32))
          { cf := false, af := i.val == 1, of := false }
       { st.st.1 with status := f }) ((layout spinWorker).addrOf 3)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_test st h, Option.some.injEq] at ht
  subst ht
  exact hk

/-- `jne worker` (position 3). -/
theorem wp_jne_spin (st : State) (h : At st 3)
    (hk : Post (goto st st.st.1
      (if st.st.1.status.zf then (layout spinWorker).addrOf 4 else (layout spinWorker).addrOf 1)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_jne_spin st h, Option.some.injEq] at ht
  subst ht
  exact hk

/-- `movl $1,%eax` (position 4). -/
theorem wp_mov_one (st : State) (h : At st 4)
    (hk : Post (goto st { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) 1#32 }
      ((layout spinWorker).addrOf 5)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_mov_one st h, Option.some.injEq] at ht
  subst ht
  exact hk

/-- `xchgl %eax,(%rdi)` (position 5): `EvTree.eraseWPR_rmw_pend'` at the
swap's tree. -/
theorem wp_xchg (st : State) (h : At st 5) {l : BitVec 64}
    (hx : st.st.1.regs.get64 .rdi = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none)
    (hn : tid < c.threads.size)
    (hp : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind .acqRel).loadKind false ⟨l, 4⟩ false,
      ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind .acqRel).storeKind true ⟨l, 4⟩
        (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32))) (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' ⟨l, 4⟩ (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32))) (some x.1) tw →
      tw ∈ g.pend →
      Post (goto st { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) (BitVec.setWidth 32 x.2.1) }
        ((layout spinWorker).addrOf 6)) r (unpend g tw) (rmwAfter A .acqRel false ⟨l, 4⟩ cx'))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (A.rmwKind .acqRel).loadKind false ⟨l, 4⟩ false,
      ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind .acqRel).storeKind true ⟨l, 4⟩
        (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32))) (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' ⟨l, 4⟩ (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32))) (some x.1) tw →
      tw ∉ g.pend → ErAt rF T c t tid r g x.2.2 →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res),
        (∀ p ∈ x.2.2.prom, p ∈ g.pend → ((⟨l, 4⟩, x.1), p) ∉ g.claims) ∧ 0 < (r.wr ⟨l, 4⟩).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq ⟨l, 4⟩ tw
          (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32))) cx'.mem ss ∧ ¬ g.Claimed (⟨l, 4⟩, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel ⟨l, 4⟩) (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32)))) ∧
        r'.op (Res.prod (ss.map (·.res))) =
          (r.op (Res.prod ((claimedSlots g ⟨l, 4⟩ x.1).map (·.res)))).addW ⟨l, 4⟩
            (BitVec.setWidth 128 (st.st.1.regs.get (.low .rax .W32)), tw) ∧
        (tw ∈ x.2.2.prom → ss = []) ∧
        (claimedSlots g ⟨l, 4⟩ x.1 ≠ [] → x.1 ≤ (rmwAfter A .acqRel false ⟨l, 4⟩ cx').views.wfloor) ∧
        HVal rF T c t tid cx' r' (rmwGhost g ⟨l, 4⟩ x.1 tw rel ss) ∧
        Post (goto st { st.st.1 with regs := st.st.1.regs.set (.low .rax .W32) (BitVec.setWidth 32 x.2.1) }
          ((layout spinWorker).addrOf 6)) r' (rmwGhost g ⟨l, 4⟩ x.1 tw rel ss)
          (rmwAfter A .acqRel false ⟨l, 4⟩ cx')) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_xchg st h hx hdm, Option.some.injEq] at ht
  subst ht
  refine EvTree.eraseWPR_rmw_pend' hn (fun _ _ hop => by cases hop) ?_ ?_
  · intro x hx new hop cx' tw hc hev hpd
    cases hop
    exact hp x hx cx' tw hc hev hpd
  · intro x hx new hop cx' tw hc hev hpd E
    cases hop
    exact hok x hx cx' tw hc hev hpd E

/-- `testl %eax,%eax` (position 6). -/
theorem wp_test2 (st : State) (h : At st 6)
    (hk : ∀ i : Fin 2, Post (goto st
      (let f : StatusFlags := .from_result (st.st.1.regs.get (.low .rax .W32))
          { cf := false, af := i.val == 1, of := false }
       { st.st.1 with status := f }) ((layout spinWorker).addrOf 7)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_test2 st h, Option.some.injEq] at ht
  subst ht
  exact hk

/-- `jne worker` (position 7). -/
theorem wp_jne_retry (st : State) (h : At st 7)
    (hk : Post (goto st st.st.1
      (if st.st.1.status.zf then (layout spinWorker).addrOf 8 else (layout spinWorker).addrOf 1)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_jne_retry st h, Option.some.injEq] at ht
  subst ht
  exact hk

/-- `movl (%rsi),%ecx` (position 8). -/
theorem wp_load_counter (st : State) (h : At st 8) {cc : BitVec 64}
    (hx : st.st.1.regs.get64 .rsi = cc) (hdc : Mem.loadInt st.st.1.dmem cc 4 = none)
    (hk : ∀ x ∈ readSuccs A iv cx .plain false ⟨cc, 4⟩,
      Post (goto st { st.st.1 with regs := st.st.1.regs.set (.low .rcx .W32) (BitVec.setWidth 32 x.2.1) }
        ((layout spinWorker).addrOf 9)) r g x.2.2) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_load_counter st h hx hdc, Option.some.injEq] at ht
  subst ht
  exact EvTree.eraseWPR_load hk

/-- `addl $1,%ecx` (position 9). -/
theorem wp_add (st : State) (h : At st 9)
    (hk : Post (goto st
      (let a := 1#32
       let b := st.st.1.regs.get (.low .rcx .W32)
       let v := a + b
       let f : StatusFlags := .from_result v {
           cf := v.unsigned != a.unsigned + b.unsigned
           af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
           of := v.signed != a.signed + b.signed }
       { st.st.1 with regs := st.st.1.regs.set (.low .rcx .W32) v, status := f })
      ((layout spinWorker).addrOf 10)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_add st h, Option.some.injEq] at ht
  subst ht
  exact hk

omit layout hv in
/-- A plain 4-byte store of `v` at `a` followed by a stop at `s'`:
`EvTree.eraseWPR_store_pend` with the continuation's WP as `Post`. -/
private theorem wp_store_done (hn : tid < c.threads.size) {a : BitVec 64} {v : Val} {s' : State}
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx .plain false ⟨a, 4⟩ v none →
      WriteEv tid cx cx' ⟨a, 4⟩ v none tw → tw ∈ g.pend → Post s' r (unpend g tw) cx')
    (hk : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx .plain false ⟨a, 4⟩ v none →
      WriteEv tid cx cx' ⟨a, 4⟩ v none tw → tw ∉ g.pend → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), 0 < (r.wr ⟨a, 4⟩).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq ⟨a, 4⟩ tw v cx'.mem ss ∧
          ¬ g.Claimed (⟨a, 4⟩, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel ⟨a, 4⟩) v) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW ⟨a, 4⟩ (v, tw) ∧
        (tw ∈ cx.prom → ss = []) ∧
        HVal rF T c t tid cx' r' (storeGhost g ⟨a, 4⟩ tw rel ss) ∧
        Post s' r' (storeGhost g ⟨a, 4⟩ tw rel ss) cx') :
    (EvTree.store .plain false ⟨a, 4⟩ v fun _ => .done s').EraseWPR A tid iv rF T c t Post r g cx :=
  EvTree.eraseWPR_store_pend hn hp hk

/-- `movl %ecx,(%rsi)` (position 10). -/
theorem wp_store_counter (st : State) (h : At st 10) {cc : BitVec 64}
    (hx : st.st.1.regs.get64 .rsi = cc) (hdc : Mem.loadInt st.st.1.dmem cc 4 = none)
    (hn : tid < c.threads.size)
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx .plain false ⟨cc, 4⟩
        (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) none →
      WriteEv tid cx cx' ⟨cc, 4⟩ (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) none tw →
      tw ∈ g.pend → Post (goto st st.st.1 ((layout spinWorker).addrOf 11)) r (unpend g tw) cx')
    (hk : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx .plain false ⟨cc, 4⟩
        (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) none →
      WriteEv tid cx cx' ⟨cc, 4⟩ (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) none tw →
      tw ∉ g.pend → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), 0 < (r.wr ⟨cc, 4⟩).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq ⟨cc, 4⟩ tw
          (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32))) cx'.mem ss ∧ ¬ g.Claimed (⟨cc, 4⟩, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel ⟨cc, 4⟩) (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32)))) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW ⟨cc, 4⟩ (BitVec.setWidth 128 (st.st.1.regs.get (.low .rcx .W32)), tw) ∧
        (tw ∈ cx.prom → ss = []) ∧
        HVal rF T c t tid cx' r' (storeGhost g ⟨cc, 4⟩ tw rel ss) ∧
        Post (goto st st.st.1 ((layout spinWorker).addrOf 11)) r' (storeGhost g ⟨cc, 4⟩ tw rel ss) cx') :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_store_counter st h hx hdc, Option.some.injEq] at ht
  subst ht
  exact wp_store_done hn hp hk

/-- `movl $0,(%rdi)` (position 11): the unlock. A prepaid unlock (its promise
pending) takes `hp`. -/
theorem wp_unlock (st : State) (h : At st 11) {l : BitVec 64}
    (hx : st.st.1.regs.get64 .rdi = l) (hdm : Mem.loadInt st.st.1.dmem l 4 = none)
    (hn : tid < c.threads.size)
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx .plain false ⟨l, 4⟩ 0#128 none →
      WriteEv tid cx cx' ⟨l, 4⟩ 0#128 none tw → tw ∈ g.pend →
      Post (goto st st.st.1 ((layout spinWorker).addrOf 12)) r (unpend g tw) cx')
    (hk : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx .plain false ⟨l, 4⟩ 0#128 none →
      WriteEv tid cx cx' ⟨l, 4⟩ 0#128 none tw → tw ∉ g.pend → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), 0 < (r.wr ⟨l, 4⟩).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq ⟨l, 4⟩ tw 0#128 cx'.mem ss ∧
          ¬ g.Claimed (⟨l, 4⟩, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel ⟨l, 4⟩) 0#128) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW ⟨l, 4⟩ (0#128, tw) ∧
        (tw ∈ cx.prom → ss = []) ∧
        HVal rF T c t tid cx' r' (storeGhost g ⟨l, 4⟩ tw rel ss) ∧
        Post (goto st st.st.1 ((layout spinWorker).addrOf 12)) r' (storeGhost g ⟨l, 4⟩ tw rel ss) cx') :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_unlock st h hx hdm, Option.some.injEq] at ht
  subst ht
  exact wp_store_done hn hp hk

/-- `jmp done` (position 12). -/
theorem wp_jmp_done (st : State) (h : At st 12)
    (hk : Post (goto st st.st.1 ((layout spinWorker).addrOf 14)) r g cx) :
    ∀ tree, isa.exec st = some tree → tree.EraseWPR A tid iv rF T c t Post r g cx := by
  intro tree ht
  rw [exec_jmp_done st h, Option.some.injEq] at ht
  subst ht
  exact hk

end Kraken.Promising.SLR.X64SpinTrees
