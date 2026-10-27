/-
**One output byte, kernel side and source side** (prototype for printing
programs): the facts a consumer case for a one-byte `write(1, buf, 1)` needs,
for any ISA and `Abi`, where `scc` lowers WeakCore's `emit b` to such a write
of a byte the thread holds in its private memory (a frame slot).

- **Kernel.** `readByte_priv`: the kernel reads a byte of private memory
  without touching shared memory or the thread (no memory relation is
  needed). `write1_cases`: with no byte out yet, a step of
  `write(1, buf, 1)` at such a byte is the byte itself (event `out b`, one
  byte out), `-EINTR`/`-EAGAIN` (no event, the thread resumes), or a refusal
  (event `writeErr`, the thread resumes); `write1_done`: with the byte out,
  the only step returns `1`, with no event.
- **Source.** `traceOf_emit`: WeakCore's extern step `emit` of the number `b`
  grows the source's observable trace (`SrcSem.traceOf`) by
  `out (b % 256)`.
- **The match.** `emit_match`: if the private byte is `b % 256`, the kernel's
  event list of the byte step is the source's growth.
-/
import Scc.Sem.SysLink
import Scc.Sem.SrcOutProto

namespace Spike.Lib.EmitByte

open Kraken.Promising Scc.Sem Scc.Sem.Kernel
open CoreTerm TermRun

variable {I : ISA} {K : Abi I}

/-! ## Kernel side -/

/-- The kernel's byte of a private byte `x`. -/
def privByte (x : UInt8) : Fin 256 := ⟨x.toNat % 256, Nat.mod_lt _ (by decide)⟩

/-- A one-byte load of private memory is the byte there. -/
theorem loadBytes_one {m : _root_.Mem 64} {a : BitVec 64} {x : UInt8} (h : m[a]? = some x) :
    m.loadBytes a 1 = some [x] := by
  simp [Mem.loadBytes, List.allSome, h]

/-- **The kernel reads a private byte as it is**, leaving the thread alone
(no shared memory, no view change). -/
theorem readByte_priv {A : Arch} {t : Thread I} {mem : Memory} {a rd : Nat} {x : UInt8}
    (h : (K.dmem t.st)[BitVec.ofNat 64 a]? = some x) :
    readByte K A t mem a rd = some (privByte x, t) := by
  simp [readByte, loadBytes_one h, privByte]

/-- **A step of `write(1, buf, 1)` with no byte out**, the byte at `buf`
private (`x`): the byte (event `out x`, one byte out, the thread as it
was), `-EINTR`/`-EAGAIN` (no event), or a refusal (event `writeErr`); in the
last two the thread resumes with the result and the slot is unchanged. -/
theorem write1_cases {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    {t : Thread I} {buf : Nat} {x : UInt8} (ht : c.1.threads[tid]? = some t)
    (hc : callOf K t = some (.write 1 buf 1)) (hw : c.2.wr tid = 0)
    (hx : (K.dmem t.st)[BitVec.ofNat 64 buf]? = some x)
    (h : sysStep K A tid c p = some (es, c')) :
    (es = [.out (privByte x)] ∧ c' = (c.1.withThread tid t c.1.mem, c.2.set tid (.run 1))) ∨
      (∃ r, (r = neg eintr ∨ r = neg eagain) ∧ es = [] ∧
        c' = (c.1.withThread tid (retThread K t r) c.1.mem, c.2)) ∨
      (∃ r, writeRefused r = true ∧ es = [.writeErr] ∧
        c' = (c.1.withThread tid (retThread K t r) c.1.mem, c.2)) := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  cases p with
  | byte rd =>
    simp only [hw, Nat.zero_lt_one, ite_true, Nat.add_zero, readByte_priv (mem := c.1.mem) (rd := rd) hx,
      Option.map_some, Option.some.injEq, Prod.mk.injEq, ite_true] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨rfl, rfl⟩
  | ret r =>
    simp only [hw, Nat.lt_irrefl, ite_false] at h
    by_cases he : r = neg eintr ∨ r = neg eagain
    · simp only [he, ite_true, back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr (.inl ⟨r, he, rfl, rfl⟩)
    · simp only [he, ite_false] at h
      by_cases hr : writeRefused r = true
      · simp only [hr, ite_true, back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr ⟨r, hr, rfl, rfl⟩)
      · simp only [hr, Bool.false_eq_true, ite_false] at h
        cases h
  | abort k => simp at h

/-- **With its one byte out, a step of `write(fd, buf, 1)` returns `1`**,
with no event, and the slot's count is reset. -/
theorem write1_done {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    {t : Thread I} {fd buf : Nat} (ht : c.1.threads[tid]? = some t)
    (hc : callOf K t = some (.write fd buf 1)) (hw : c.2.wr tid = 1)
    (h : sysStep K A tid c p = some (es, c')) :
    es = [] ∧ c' = (c.1.withThread tid (retThread K t 1) c.1.mem, c.2.set tid (.run 0)) := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  cases p with
  | byte rd => simp [hw] at h
  | ret r =>
    simp only [hw, Nat.zero_lt_one, ite_true] at h
    by_cases he : r = BitVec.ofNat 64 1
    · simp only [he, ite_true, back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp [he] at h
  | abort k => simp at h

/-! ## Source side -/

/-- **WeakCore's `emit` of the number `b` grows the observable trace by
`out (b % 256)`.** -/
theorem traceOf_emit (c : Cfg) (i : Nat) (th : TTh) (x : String) (e : Expr) {w : Word} {b : Nat}
    (hw : w.val = .num b) :
    SrcSem.traceOf (extCfg c i th x .emit e [w] []) =
      SrcSem.traceOf c ++ [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] := by
  simp [SrcSem.traceOf, extCfg, ExtName.events, hw, SrcSem.evOf]

/-! ## The match -/

/-- **The kernel's byte is the source's**: if the private byte is `b % 256`,
the event list of the kernel's byte step (`write1_cases`) is the growth of
the source's trace at `emit b` (`traceOf_emit`). -/
theorem emit_match {x : UInt8} {b : Nat} (hb : x.toNat = b % 256) :
    [Ev.out (privByte x)] = [.out ⟨b % 256, Nat.mod_lt _ (by decide)⟩] := by
  simp only [privByte, List.cons.injEq, Ev.out.injEq, and_true]
  exact Fin.ext (by simp [hb])

end Spike.Lib.EmitByte
