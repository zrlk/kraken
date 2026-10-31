/-
**The box allocation's heap use and row with it** (part (c), `let x = new a
in e` of a one-word value, the row `Out.newStore`).

- `heapUse_new`: the memory with the box's cell (its `undef` first message
  and the initialising store) at a fresh label, the thread's allocation
  count bumped and its box label kept: the heap use grows by two (one word,
  one header), the boxes counted by the allocations (`hle`;
  `BoxCount.heapUse_add` over `NewRow.cellAlloc_new`).
- `new_rowS`: `NewRow.row_newStore` at thread `0` with the thread's next
  label from `FreshInv` (`HeapPresCore.fresh_of_inv1`), the heap use after
  (`heapUse_new`) and `FreshInv` moved on (`FreshInv.place`). It does not
  mention `AllocInvAt`.
-/
import Spike.Lib.NewRow
import Spike.Lib.Src.BoxCount
import Spike.Lib.HeapPresCore
import Spike.Lib.AllocInv

namespace Spike.Lib.HeapNew

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (heapUse Inv1 ValRep wordLoc boxCount allocCount Fresh)
open Spike.Lib.AllocInv (FreshInv)
open Spike.Lib.AllocRow (ArenaOK)

/-- **The heap use after the box allocation**: two more (the cell's word
and its header). -/
theorem heapUse_new {c c' : Cfg} {i : Nat} {th th' : TTh} (hi : c.ths[i]? = some th) {l : WeakMem.AllocLabel}
    (hfresh : Fresh c l) {v : WeakMem.Val} {mv : Nat}
    (hmem : c'.mem = (c.mem.push ⟨⟨l, 0⟩, .undef, 0⟩).push ⟨⟨l, 0⟩, v, mv⟩) (hths : c'.ths = c.ths.set! i th')
    (hn : th'.nalloc = th.nalloc + 1) (ht : th'.tidLbl = th.tidLbl) (hle : boxCount c ≤ allocCount c) :
    heapUse c' = heapUse c + 2 :=
  BoxCount.heapUse_add (NewRow.cellAlloc_new hi hfresh hmem hths hn)
    (by rw [BoxCount.allocCount_succ hi hths hn]; omega) (BoxCount.boxCount_set hi hths ht) hle

section Row

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {s : Cfg} {th : TTh}

/-- **The box row at thread `0` with the heap use**: `row_newStore` at the
thread's next label (fresh by `FreshInv`), the heap use two more after, and
`FreshInv` moved past the label placed. -/
theorem new_rowS (h1 : Inv1 Λ lbl lsize ts t tm s.mem) {heap cells old : Nat} {ex : Nat → Prop}
    (ha : ArenaOK Λ lbl lsize t tm heap cells old ex) (hi : s.ths[0]? = some th)
    (hfr : FreshInv lbl s.lbase s.n 0 th.nalloc) (hn0 : 0 < s.n)
    {x : String} {a : At} {T : Option Ty} {e : Expr} {ty : Ty} {w : Word}
    (ht : th.term = .let_ x (.new a T) e) (hea : evalAt th.env a = some (ty, [w]))
    (hu : accs ty = some [.one]) (hp : th.promises = [])
    {off u : Nat} (hoff : off % 8 = 0) (hfit : off + 8 * 1 ≤ 16 * u) (hle : old + u ≤ cells)
    (hex : ∀ a', ex a' → a' < heap + 16 * old + off) (hbx : boxCount s ≤ allocCount s)
    (A : Arch) {tid : Nat} {kr : StoreKind} {v : Val} {st : I.State}
    (hexec : I.exec t.st = some (.store kr false (wordLoc (heap + 16 * old + off)) v fun _ => .done st))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hv : ValRep lbl w.val v.toNat) :
    ∃ mv th', { s with mem := ((s.mem.push ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, w.val, mv⟩), ths := s.ths.set! 0 th' } ∈
          threadSteps p kn arch s 0 ∧ th'.term = e ∧
      th'.env = (x, .ptr .own ty, [cst (.loc ⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      th'.tidLbl = th.tidLbl ∧ o.thread.st = st ∧
      heapUse { s with mem := ((s.mem.push ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, w.val, mv⟩), ths := s.ths.set! 0 th' } = heapUse s + 2 ∧
      (∃ q, Inv1 Λ (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then some (heap + 16 * old + off)
          else lbl l') (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then 1 else lsize l')
        (fun k => if k = s.mem.size + 1 then some q else if s.mem.size ≤ k ∧ k < s.mem.size + 1 then some 0
          else ts k)
        o.thread o.mem ((s.mem.push ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, .undef, 0⟩).push
          ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, w.val, mv⟩)) ∧
      ArenaOK Λ (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then some (heap + 16 * old + off)
          else lbl l') (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then 1 else lsize l')
        o.thread o.mem heap cells (old + u) (fun _ => False) ∧
      FreshInv (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then some (heap + 16 * old + off)
          else lbl l') s.lbase s.n 0 (th.nalloc + 1) := by
  obtain ⟨mv, th', hs, h2, h3, h4, h5, h6, h7, h8, hst, hinv, har⟩ :=
    NewRow.row_newStore (p := p) (kn := kn) (arch := arch) h1 ha hi ht hea hu hp hfr.fresh hoff hfit hle hex
      A hexec hstep ho hv
  refine ⟨mv, th', hs, h2, h3, h4, h5, h6, h7, h8, hst, ?_, hinv, har, hfr.place hn0 _⟩
  exact heapUse_new hi (HeapPres.fresh_of_inv1 h1 hfr) rfl rfl h7 h8 hbx

end Row

/-- info: 'Spike.Lib.HeapNew.heapUse_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms heapUse_new

/-- info: 'Spike.Lib.HeapNew.new_rowS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms new_rowS

end Spike.Lib.HeapNew
