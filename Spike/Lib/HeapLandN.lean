/-
**The box row at the source's heap use**: `HeapNew.new_rowS`
from `AllocInvAt … (heapUse s)` pending at the box (`Pending` over
`AllocSite`; `AllocInv.Pending.box`), landing idle at `heapUse s + units 1 ty`.

- `new_rowA`: `HeapLand.alloc_rowS`'s box twin.
-/
import Spike.Lib.HeapNew
import Spike.Lib.HeapLand
import Spike.Lib.AllocInvN

namespace Spike.Lib.HeapLandN

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (heapUse Inv1 ValRep wordLoc boxCount allocCount)
open Spike.Lib (AllocInvAt AllocSite)
open Spike.Lib.AllocInv (CtrAt Pending FreshInv)
open Spike.Lib.AllocRow (ArenaOK)

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {t : Thread I} {tm : Memory}
  {heap cells ctr : Nat} {units off : Nat → Ty → Nat} {c : Spike.Lib.Ctl}
  {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {s : Cfg} {th : TTh}

/-- **The box row at the source's heap use**: from `AllocInvAt` at
`heapUse s` with the control at `let x = new a in e` holding the counter's
old count `old` (`a` a one-word value of type `ty`, its object within the
cells, `units 1 ty = 2`, `off 1 ty` a word boundary with the word within the
object's cells), thread 0 at the control with no promise and its next label
fresh, the boxes counted by the allocations, the target's store to the box's
base (off the counter word): the held count is `heapUse s`, the source takes
the box's step, the heap use grows by `units 1 ty`, `Inv1` holds with the
label placed, and `AllocInvAt` is idle at `heapUse s + units 1 ty` for a
control holding nothing. -/
theorem new_rowA (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off (heapUse s) c)
    (h1 : Inv1 Λ lbl lsize ts t tm s.mem) (hi : s.ths[0]? = some th) (htc : th.term = c.term)
    (hec : th.env = c.env) (hfr : FreshInv lbl s.lbase s.n 0 th.nalloc) (hn0 : 0 < s.n)
    {x : String} {a : At} {e : Expr} {ty : Ty} {w wold : Word} {old : Nat}
    (ht : c.term = .let_ x (.new a) e) (hea : evalAt c.env a = some (ty, [w])) (hu : accs ty = some [.one])
    (hp : th.promises = []) (hh : c.hold = some (ctr, wold)) (hold : numOf [wold] = some old)
    (hle : old + units 1 ty ≤ cells) (hun : units 1 ty = 2) (hoff : off 1 ty % 8 = 0)
    (hfit : off 1 ty + 8 * 1 ≤ 16 * units 1 ty) (hbx : boxCount s ≤ allocCount s)
    (A : Arch) {tid : Nat} {kr : StoreKind} {v : Val} {st : I.State}
    (hexec : I.exec t.st = some (.store kr false (wordLoc (heap + 16 * old + off 1 ty)) v fun _ => .done st))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    (hb : wordLoc (heap + 16 * old + off 1 ty) ≠ wordLoc ctr) (hv : ValRep lbl w.val v.toNat)
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) :
    old = heapUse s ∧
    ∃ mv th', { s with mem := ((s.mem.push ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, w.val, mv⟩), ths := s.ths.set! 0 th' } ∈
          threadSteps p kn arch s 0 ∧ th'.term = e ∧
      th'.env = (x, .ptr .own ty, [cst (.loc ⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = [] ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      th'.tidLbl = th.tidLbl ∧ o.thread.st = st ∧
      heapUse { s with mem := ((s.mem.push ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, .undef, 0⟩).push
        ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, w.val, mv⟩), ths := s.ths.set! 0 th' } =
          heapUse s + units 1 ty ∧
      (∃ q, Inv1 Λ (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then
            some (heap + 16 * heapUse s + off 1 ty) else lbl l')
          (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then 1 else lsize l')
          (fun k => if k = s.mem.size + 1 then some q else if s.mem.size ≤ k ∧ k < s.mem.size + 1 then some 0
            else ts k)
          o.thread o.mem ((s.mem.push ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, .undef, 0⟩).push
            ⟨⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩, w.val, mv⟩)) ∧
      AllocInvAt Λ (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then
            some (heap + 16 * heapUse s + off 1 ty) else lbl l')
          (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then 1 else lsize l') o.thread o.mem heap cells
          ctr units off (heapUse s + units 1 ty) c' ∧
      FreshInv (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then
          some (heap + 16 * heapUse s + off 1 ty) else lbl l') s.lbase s.n 0 (th.nalloc + 1) := by
  have hw := h.held hh
  subst hw
  obtain rfl : old = heapUse s := by cases hold; rfl
  refine ⟨rfl, ?_⟩
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  rotate_left
  · exact absurd hh (hn _)
  obtain ⟨hctr, hex⟩ := hpd.box ht hea
  rw [← htc] at ht
  rw [← hec] at hea
  obtain ⟨mv, th', hs, h2, h3, h4, h5, h6, h7, h8, hst, hheap, hinv, har, hfr'⟩ :=
    HeapNew.new_rowS (p := p) (kn := kn) (arch := arch) h1 ha hi hfr hn0 ht hea hu hp hoff hfit hle hex hbx
      A hexec hstep ho hv
  refine ⟨mv, th', hs, h2, h3, h4, h5, h6, h7, h8, hst, by rw [hheap, hun], hinv, ?_, hfr'⟩
  exact .inr ⟨fun w h => (by rw [hc'] at h; cases h), AllocInvN.ctrAt_store_ne A hctr hexec hstep ho hpl hb,
    har⟩

/-- info: 'Spike.Lib.HeapLandN.new_rowA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HeapLandN.new_rowA

end Spike.Lib.HeapLandN
