/-
**`byteOut_emit` at `hello1.w`'s buffer, `hpriv` discharged** (x86-64; a
non-vacuity regression of `Spike/Lib/ByteOutPriv.lean`): for a thread of
any configuration reached from `hello1`'s load, the byte `k < 16` of
`rodata`'s buffer, at `A = heap + 16·old + off 2 τ8` in the arena
(`rdPostS`'s facts, `Spike/Test/X64PrintByteOutHello1.lean`'s `bJ`), is not
private: `hpriv` from `PrivInv` along the run (`hello1_privInv_load`,
`Spike/Test/X64DmemPrivHello1.lean`) and the byte in `hello1Λ`'s heap
(`arena_heap`).

`hello1_byteOut_emit_load`: at `print`'s element load of the byte, the byte
step `hbo` discharged too (`ByteOut.load`).

Left open: `byteOut_emit`'s other premises (the byte step `hbo` of
`hello1_byteOut_emit`, the invariant, the kernel's read, the source side), and the arena inside
`hello1Λ`'s heap (`hH`, `hHi`: the memory side's `ms.heap = Λ.heap.lo`).
-/
import Spike.Lib.ByteOutPriv
import Spike.Test.X64DmemPrivHello1
import Spike.Lib.Hello1RodataSrc

namespace Spike.Test.X64ByteOutPrivHello1

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.DmemPriv Spike.Lib.ByteOut SccCode
open Spike.Lib.PrintSrc (loadC nextC)
open Spike.Test.X64DmemPrivHello1 (hello1_privInv_load hello1_clear)
open Spike.Lib.Hello1RodataSrc (τ8)
open Scc.Sem.MemRel (SLatest)

/-- **`byteOut_emit` at byte `k` of `hello1`'s buffer**, `hpriv` discharged. -/
theorem hello1_byteOut_emit {n : Nat} {μ : Marks} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    {tr : List Ev} {c : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Cfg}
    (hrun : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Run μ
      (Scc.Sem.X64.loadProg (Scc.Sem.X64.kernel n) Entry.linux hello1Λ hello1Cells syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (htid : c.1.threads[tid]? = some t)
    {ms : MemSide Kraken.Promising.X64.isa} {A old k : Nat} (hA : A = ms.heap + 16 * old + ms.off 2 τ8)
    (hold : old + ms.units 2 τ8 ≤ ms.cells) (hu : ms.units 2 τ8 = 3) (hoff : ms.off 2 τ8 = 8) (hk : k < 16)
    (hH : hello1Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ hello1Λ.heap.lo + hello1Λ.heap.size)
    {P : SrcParams} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {t' : Thread Kraken.Promising.X64.isa} {tm : Memory} {ar : Arch} {rd : Nat} {bt : Fin 256}
    {c1 : Ctl} {Q : Ctl → Prop} {s : Cfg} {th : TTh}
    (hP : UsesWc P p) (hbo : ByteOut p lbl t.st (A + k) c1 Q) (hinv : Inv1 hello1Λ lbl lsize ts t tm s.mem)
    (hrb : Kernel.readByte Scc.Sem.X64.abi ar t tm (A + k) rd = some (bt, t'))
    (hi : s.ths[0]? = some th) (ht : th.term = c1.term) (he : th.env = c1.env) (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, Event.exit x ∉ s.trace)
    (hnum : ∀ sa, wordAddr lbl sa = some (A + k - (A + k) % 8) →
      ∃ j msg n, SLatest s.mem sa j ∧ s.mem[j]? = some msg ∧ msg.val = .num n) :
    Inv1 hello1Λ lbl lsize ts t' tm s.mem ∧
      ∃ th', (source P p).Run s [.out bt] { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        Q ⟨th'.term, th'.env, none⟩ ∧ th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] := by
  have hd := (Spike.Lib.X64DmemPriv.privInv_run (hello1_privInv_load n syms mem) hrun).dmemPriv tid t htid
  have hb : hello1Λ.heap.contains (A + k) := by
    rw [hA]; exact arena_heap hH hHi hold (by omega)
  exact byteOut_emit_priv hP hbo hinv hello1Λ_wf hrb hd hello1_clear (.inl hb) hi ht he hσ hst hp hx hnum

/-- **`byteOut_emit` at `print`'s element load of byte `k` of `hello1`'s buffer**: `hpriv` and the byte
step `hbo` discharged (`ByteOut.load`), for the buffer word `pw` at the label `l` placed at `A`. -/
theorem hello1_byteOut_emit_load {n : Nat} {μ : Marks} {syms : List (String × Nat)} {mem : List (Loc × Val)}
    {tr : List Ev} {c : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Cfg}
    (hrun : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Run μ
      (Scc.Sem.X64.loadProg (Scc.Sem.X64.kernel n) Entry.linux hello1Λ hello1Cells syms mem) tr c)
    {tid : Nat} {t : Thread Kraken.Promising.X64.isa} (htid : c.1.threads[tid]? = some t)
    {ms : MemSide Kraken.Promising.X64.isa} {A old k : Nat} (hA : A = ms.heap + 16 * old + ms.off 2 τ8)
    (hold : old + ms.units 2 τ8 ≤ ms.cells) (hu : ms.units 2 τ8 = 3) (hoff : ms.off 2 τ8 = 8) (hk : k < 16)
    (hH : hello1Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ hello1Λ.heap.lo + hello1Λ.heap.size)
    {P : SrcParams} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {t' : Thread Kraken.Promising.X64.isa} {tm : Memory} {ar : Arch} {rd : Nat} {bt : Fin 256}
    {pw wn : Word} {l : WeakMem.AllocLabel} {m : Nat} {s : Cfg} {th : TTh}
    (hP : UsesWc P p) (hpw : pw.val = .loc ⟨l, 0⟩ 0)
    (hl : lbl l = some A) (hinv : Inv1 hello1Λ lbl lsize ts t tm s.mem)
    (hrb : Kernel.readByte Scc.Sem.X64.abi ar t tm (A + k) rd = some (bt, t'))
    (hi : s.ths[0]? = some th) (ht : th.term = (loadC pw wn m k).term) (he : th.env = (loadC pw wn m k).env)
    (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, Event.exit x ∉ s.trace)
    (hnum : ∀ sa, wordAddr lbl sa = some (A + k - (A + k) % 8) →
      ∃ j msg n, SLatest s.mem sa j ∧ s.mem[j]? = some msg ∧ msg.val = .num n) :
    Inv1 hello1Λ lbl lsize ts t' tm s.mem ∧
      ∃ th', (source P p).Run s [.out bt] { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        (∃ mw v, (⟨th'.term, th'.env, none⟩ : Ctl) = nextC pw wn m k mw v) ∧ th'.σs = [] ∧
          th'.stack = th.stack ∧ th'.promises = [] :=
  hello1_byteOut_emit hrun htid hA hold hu hoff hk hH hHi hP (ByteOut.load hpw hl) hinv hrb hi ht he hσ hst hp
    hx hnum

end Spike.Test.X64ByteOutPrivHello1
