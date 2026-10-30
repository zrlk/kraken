/-
**The heap relation at an allocation-capable consumer's rows** (any ISA):
the pieces of `AllocInvAt … (heapUse s)` (`Spike/Lib/HeapObl.lean`) that a
consumer's step needs beyond `Spike/Lib/HeapPresCore.lean`.

- `ArenaOK.prom_keep`, `CtrAt.prom_congr`, `AllocInvAt.prom_keep`: the memory
  unchanged, a new thread keeping every outstanding promise in the free range
  and agreeing at the counter (a fulfilment elsewhere, an instruction that
  writes nothing, a kernel step).
- `AllocLand`: what a consumer's allocation fragment (`MemSide.xa`) carries
  about the arena at the landing, the buffer of `n` words at `b`: it lies in
  the arena past its first header word (`heap + 8 ≤ b`, `b + 8 · n ≤ heap +
  16 · cells`), and its object, `n + 1` cells with the header, fits the
  arena's `cells`.
- `alloc_rowS`: at an `Out.alloc` row (the counter's old count `old` held, the
  buffer at `A = heap + 16 · old + off k τ`, the object within the cells), from
  `AllocInvAt` at `heapUse s`, the one-thread invariant, `FreshInv` and the
  allocator's units and offsets (`units k τ = n + 1`, `off k τ` a word
  boundary with the buffer's words within the object's cells, `n = k · nWords
  us`): the held count is `heapUse s`, and the source takes `land_step`'s
  allocation.
-/
import Spike.Lib.HeapPresCore

namespace Spike.Lib.HeapLand

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (heapUse Inv1 ValRep wordLoc)
open Spike.Lib (AllocInvAt)
open Spike.Lib.AllocInv (CtrAt Pending FreshInv)
open Spike.Lib.AllocRow (ArenaOK freeR get?_append)

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {tm : Memory} {heap cells ctr : Nat}
  {units off : Nat → Ty → Nat} {hu : Nat} {c : Spike.Lib.Ctl} {ex : Nat → Prop}

/-! ## The thread's promises -/

/-- **The memory unchanged, the outstanding promises in the free range kept**
keeps the contract. -/
theorem _root_.Spike.Lib.AllocRow.ArenaOK.prom_keep (h : ArenaOK Λ lbl lsize t tm heap cells hu ex)
    {t' : Thread I}
    (hp : ∀ k' w, tm.get? k' = some w → (freeR heap cells hu).contains w.loc.addr.toNat → k' ∈ t.prom →
      k' ∈ t'.prom) :
    ArenaOK Λ lbl lsize t' tm heap cells hu ex :=
  h.keep (fun _ _ => rfl) (fun _ _ hk _ hx => .inl ⟨hk, hx⟩) hp

/-- **The counter with the memory unchanged**, a new promise list agreeing
with the old one on every message at the counter. -/
theorem _root_.Spike.Lib.AllocInv.CtrAt.prom_congr {tm : Memory} {prom prom' : List Time} {ctr v : Nat}
    (h : CtrAt tm prom ctr v)
    (hc : ∀ k' w, tm.get? k' = some w → w.loc = wordLoc ctr → (k' ∈ prom' ↔ k' ∈ prom)) :
    CtrAt tm prom' ctr v := by
  obtain ⟨k', ⟨h0, hl⟩, hv⟩ := h
  refine ⟨k', ⟨?_, fun k'' w hlt hg hw => (hc k'' w hg hw).mpr (hl k'' w hlt hg hw)⟩, hv⟩
  rcases h0 with h0 | ⟨w, hg, hw, hn⟩
  · exact .inl h0
  · exact .inr ⟨w, hg, hw, fun hm => hn ((hc k' w hg hw).mp hm)⟩

/-- **`AllocInvAt` with the memory unchanged**, a new thread whose promises
agree with the old ones at the counter and keep every outstanding promise in
the free range (at `hu`): a fulfilment elsewhere, an instruction that writes
nothing, a kernel step. -/
theorem _root_.Spike.Lib.AllocInvAt.prom_keep (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    {t' : Thread I}
    (hc : ∀ k' w, tm.get? k' = some w → w.loc = wordLoc ctr → (k' ∈ t'.prom ↔ k' ∈ t.prom))
    (hp : ∀ k' w, tm.get? k' = some w → (freeR heap cells hu).contains w.loc.addr.toNat → k' ∈ t.prom →
      k' ∈ t'.prom) :
    AllocInvAt Λ lbl lsize t' tm heap cells ctr units off hu c := by
  rcases h with ⟨hh, ex, hpd, ha⟩ | ⟨hn, hctr, ha⟩
  · exact .inl ⟨hh, ex, hpd.keep fun _ hctr => hctr.prom_congr hc, ha.prom_keep hp⟩
  · exact .inr ⟨hn, hctr.prom_congr hc, ha.prom_keep hp⟩

/-! ## The landing -/

/-- **The arena at an allocation's landing**: the buffer of `n` words at `b`
lies in the arena's `cells` past its first header word (`heap + 8 ≤ b`,
`b + 8 · n ≤ heap + 16 · cells`), and the object, `n + 1` cells with the
header, fits the arena's `cells` (`Arena.OK`'s fit premise). -/
def AllocLand (heap cells b n : Nat) : Prop :=
  heap + 8 ≤ b ∧ b + 8 * n ≤ heap + 16 * cells ∧ n + 1 ≤ cells

/-- A held counter word of `AllocInvAt` at `hu` is `hu`'s. -/
theorem _root_.Spike.Lib.AllocInvAt.held (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    {wold : Word} (hh : c.hold = some (ctr, wold)) : wold = cst (.num hu) := by
  rcases h with ⟨hh', -⟩ | ⟨hn, -⟩
  · rw [hh] at hh'
    cases hh'
    rfl
  · exact absurd hh (hn _)

/-- **The allocation row at the source's heap use**: at an `Out.alloc` row
(the control `c` at `let x = newBuf a τ in e` holding the counter's old count
`old`, the buffer at `heap + 16 · old + off k τ`, the object within the
cells, `old + units k τ ≤ cells`), from `AllocInvAt` at `heapUse s`, the
boxes counted by the allocations, the one-thread invariant, thread 0 at `c` with no type arguments and its next label
fresh and the allocator's units and offsets (`off k τ` a word boundary, the
buffer's words within the object's cells): the held count is `heapUse s`, and
`land_step`'s source
allocation, heap use, `Inv1`, `AllocInvAt` (idle at `heapUse s + units k τ`)
and `FreshInv` hold. -/
theorem alloc_rowS {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {ts : Nat → Option Nat} {s : Cfg}
    {th : TTh}
    (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off (heapUse s) c)
    (h1 : Inv1 Λ lbl lsize ts t tm s.mem) (hi : s.ths[0]? = some th) (htc : th.term = c.term)
    (hec : th.env = c.env) (hσ : th.σs = []) (hfr : FreshInv lbl s.lbase s.n 0 th.nalloc) (hn0 : 0 < s.n)
    {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat} {wold : Word} {old : Nat}
    {us : List Acc}
    (ht : c.term = .let_ x (.newBuf a τ) e) (hea : evalAt c.env a = some (ta, ws)) (hk : numOf ws = some k)
    (hh : c.hold = some (ctr, wold)) (hold : numOf [wold] = some old)
    (hle : old + units k τ ≤ cells) (hus : accs (close [] τ) = some us)
    (hun : units k τ = k * nWords us + 1) (hoff : off k τ % 8 = 0)
    (hfit : off k τ + 8 * (k * nWords us) ≤ 16 * units k τ)
    (hz : ∀ vs, zeroWords (close [] τ) = some vs → ∀ v ∈ vs, ∀ lbl' : WeakMem.AllocLabel → Option Nat,
      ValRep lbl' v 0)
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) (hbx : Scc.Sem.boxCount s ≤ Scc.Sem.allocCount s) :
    old = heapUse s ∧
    ∃ th', { s with mem := (allocBuf (freshLabel s.lbase s.n 0 th.nalloc) (k * nWords us)
        (AllocSrc.newBufZero (close th.σs τ)) (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! 0 th' } ∈
          threadSteps p kn arch s 0 ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ)))
          (.ini (.lit (if (AllocSrc.newBufZero (close th.σs τ)).isSome then k else 0))),
        [cst (.loc ⟨freshLabel s.lbase s.n 0 th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      heapUse { s with mem := (allocBuf (freshLabel s.lbase s.n 0 th.nalloc) (k * nWords us)
        (AllocSrc.newBufZero (close th.σs τ)) (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! 0 th' } =
        heapUse s + units k τ ∧
      Inv1 Λ (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then
          some (heap + 16 * heapUse s + off k τ) else lbl l')
        (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then k * nWords us else lsize l')
        (fun k' => if s.mem.size ≤ k' ∧ k' < s.mem.size + k * nWords us then some 0 else ts k') t tm
        (allocBuf (freshLabel s.lbase s.n 0 th.nalloc) (k * nWords us)
          (AllocSrc.newBufZero (close th.σs τ)) (stOf s.mem s.pairs th)).1.mem ∧
      AllocInvAt Λ (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then
          some (heap + 16 * heapUse s + off k τ) else lbl l')
        (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then k * nWords us else lsize l') t tm heap cells
        ctr units off (heapUse s + units k τ) c' ∧
      FreshInv (fun l' => if l' = freshLabel s.lbase s.n 0 th.nalloc then
          some (heap + 16 * heapUse s + off k τ) else lbl l') s.lbase s.n 0 (th.nalloc + 1) := by
  have hw := h.held hh
  subst hw
  have hold' : old = heapUse s := by
    cases hold
    rfl
  subst hold'
  refine ⟨rfl, ?_⟩
  have hus' : accs (close th.σs τ) = some us := by rw [hσ]; exact hus
  exact HeapPres.land_step (p := p) (kn := kn) (arch := arch) h hh h1 hi htc hec ht
    hea hk hus' hfr hn0 hun hoff hfit hle
    (fun vs hv v hm => hz vs (by rw [← hσ]; exact hv) v hm _) hc' hbx

end Spike.Lib.HeapLand
