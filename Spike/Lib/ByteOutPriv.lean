/-
**`byteOut_emit` with `hpriv` from private memory**, on any ISA: the
consumer's premise that the output byte is not a private byte
(`Spike/Lib/ByteOut.lean`), from the thread's `PrivKeys`
(`Spike/Lib/DmemPriv.lean`, which every thread has along every run from
load) and the byte in the layout's heap or static image.

- `byteOut_emit_priv`: `byteOut_emit` so;
- `arena_heap`: a byte of an allocation in an arena of `cells` units at
  `heap` inside the layout's heap is in the heap (the buffer's bytes).
-/
import Spike.Lib.ByteOut
import Spike.Lib.DmemPriv

namespace Spike.Lib.ByteOut

open CoreLang CoreTerm TermRun
open Kraken.Promising
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.DmemPriv
open Scc.Sem.MemRel (SLatest)

/-- **`byteOut_emit` with `hpriv` from `PrivKeys`**: the thread's keys
private, the entry stack clear of the layout, and the byte in the heap or
the static image. -/
theorem byteOut_emit_priv {P : SrcParams} {p : Prog} {I : ISA} {K : Kernel.Abi I} {Λ : Layout} {Ent : Entry}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {t t' : Thread I} {tm : Memory} {A : Arch} {a rd : Nat} {bt : Fin 256} {c1 : Ctl} {Q : Ctl → Prop}
    {s : Cfg} {th : TTh}
    (hP : UsesWc P p) (hbo : ByteOut p lbl t.st a c1 Q) (hinv : Inv1 Λ lbl lsize ts t tm s.mem)
    (hwf : Λ.WF) (hrb : Kernel.readByte K A t tm a rd = some (bt, t'))
    (hd : PrivKeys K Λ Ent t.st) (hE : Ent.clear Λ = true) (ha : Λ.heap.contains a ∨ Λ.data.contains a)
    (hi : s.ths[0]? = some th) (ht : th.term = c1.term) (he : th.env = c1.env) (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, Event.exit x ∉ s.trace)
    (hnum : ∀ sa, wordAddr lbl sa = some (a - a % 8) →
      ∃ j msg n, SLatest s.mem sa j ∧ s.mem[j]? = some msg ∧ msg.val = .num n) :
    Inv1 Λ lbl lsize ts t' tm s.mem ∧
      ∃ th', (source P p).Run s [.out bt] { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        Q ⟨th'.term, th'.env, none⟩ ∧ th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] := by
  have hh := (hwf.inSpace Λ.heap (by simp [Layout.regions])).2
  have hdt := (hwf.inSpace Λ.data (by simp [Layout.regions])).2
  have hlt : a < 2 ^ 64 := by rcases ha with h | h <;> unfold Range.contains at h <;> omega
  have hn := hd.not_mem hwf hE (a := BitVec.ofNat 64 a) (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt])
  exact byteOut_emit hP hbo hinv hwf hrb (loadBytes_one_none (Std.ExtHashMap.getElem?_eq_none hn)) hi ht he hσ
    hst hp hx hnum

/-- **A byte of an allocation in the arena is in the heap**: the arena of
`cells` units at `heap` inside the layout's heap, the allocation at
counter `old` of `u` units, and the byte `k` past its offset `off` inside
them. -/
theorem arena_heap {Λ : Layout} {heap cells old u off k : Nat} (hH : Λ.heap.lo ≤ heap)
    (hHi : heap + 16 * cells ≤ Λ.heap.lo + Λ.heap.size) (hold : old + u ≤ cells) (hk : off + k < 16 * u) :
    Λ.heap.contains (heap + 16 * old + off + k) := by
  unfold Range.contains; omega

end Spike.Lib.ByteOut
