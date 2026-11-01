/-
**hello.w: the worker's `write` of the frozen buffer, kernel side** (hello
plan C3, the part independent of the print phase; ISA-generic). The
worker prints the setup's published buffer with `write(1, buf, n)`, `buf`
a byte of the buffer's label `l` placed at `b0`. Each byte step of the call
reads, at thread 1's views, a byte of a frozen word (`Spike/Lib/HelloFrz.lean`).

- `sysStep_write_cases`: **a system-call step at `write(fd, buf, n)`**, for
  any `n` (`EmitByte.write1_cases` / `write1_done` for one byte): the next
  byte (`readByte` at `buf + j`, `j` the slot's count, `j < n`; event
  `out b` for `fd = 1`; the count `j + 1`), the return of the count `j > 0`
  (no event, the count reset), and with no byte out `-EINTR`/`-EAGAIN` or a
  refusal. Memory is unchanged in every case.
- `sysStep_write_byte`: the same at a `.byte` pick: only the first case.
- `hpriv_label`: `DmemPriv.PrivKeys.hpriv` over `MemRelP` (the two-thread
  relation's memory relation): no byte of a placed label is private, so the
  kernel reads it from shared memory.
- `readByte_buf`: **the kernel's read at thread 1 of byte `k` of the frozen
  buffer** is lane `k % 8` of the word `w (k / 8)`
  (`HelloFrz.readByte_frz` at `HelloFrz.hM_frz`, `hpriv_label`).
- `write_byte_buf`: a byte step of thread 1's `write(1, b0 + k0, n)` with
  `j` bytes out emits `out bt`, `bt` lane `(k0 + j) % 8` of
  `w ((k0 + j) / 8)`; memory unchanged; thread 1's promises and cover kept.

Deferred: matching the `out` bytes against the print phase's observable
(waits for C4's `PrintPhase`); the step-level and `KR` side (A64 module).

**The instance's premise** (`hfz`, B8): hello's `Inv2Params` has both words
`⟨l, 0⟩`, `⟨l, 1⟩` of `newBuf` in `frzS` and their target words
`wordLoc (b0 + 8 i)` in `frz`; `newBuf` is placed at the spawn
(`R.lbl l = some b0`) with `lsize l ≥ 2`, and is not the label of `c`.
-/
import Spike.Lib.HelloFrz
import Spike.Lib.DmemPriv

namespace Spike.Lib.HelloWrite

open Kraken.Promising Scc.Sem Scc.Sem.Kernel Spike.Lib.Inv2Core
open Scc.Sem.MemRel (SLatest)

/-! ## The `write` call's steps -/

section Kernel

variable {I : ISA} {K : Abi I}

/-- **A system-call step at `write(fd, buf, n)`** (see the module
docstring), `j = c.2.wr tid` the bytes out so far. -/
theorem sysStep_write_cases {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    {t : Thread I} {fd buf n : Nat} (ht : c.1.threads[tid]? = some t)
    (hc : callOf K t = some (.write fd buf n)) (h : sysStep K A tid c p = some (es, c')) :
    (∃ rd b t', c.2.wr tid < n ∧ readByte K A t c.1.mem (buf + c.2.wr tid) rd = some (b, t') ∧
        es = (if fd = 1 then [.out b] else []) ∧
        c' = (c.1.withThread tid t' c.1.mem, c.2.set tid (.run (c.2.wr tid + 1)))) ∨
      (0 < c.2.wr tid ∧ es = [] ∧
        c' = (c.1.withThread tid (retThread K t (BitVec.ofNat 64 (c.2.wr tid))) c.1.mem, c.2.set tid (.run 0))) ∨
      (c.2.wr tid = 0 ∧ ∃ r, (r = neg eintr ∨ r = neg eagain) ∧ es = [] ∧
        c' = (c.1.withThread tid (retThread K t r) c.1.mem, c.2)) ∨
      (c.2.wr tid = 0 ∧ ∃ r, writeRefused r = true ∧ es = [.writeErr] ∧
        c' = (c.1.withThread tid (retThread K t r) c.1.mem, c.2)) := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  cases p with
  | byte rd =>
    simp only at h
    split at h
    · rename_i hj
      cases hr : readByte K A t c.1.mem (buf + c.2.wr tid) rd with
      | none => rw [hr] at h; cases h
      | some x =>
        obtain ⟨b, t'⟩ := x
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inl ⟨rd, b, t', hj, hr, rfl, rfl⟩
    · cases h
  | ret r =>
    simp only at h
    split at h
    · rename_i hj
      split at h
      · rename_i hr
        subst hr
        simp only [back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inl ⟨hj, rfl, rfl⟩)
      · cases h
    · rename_i hj
      have hj0 : c.2.wr tid = 0 := by omega
      split at h
      · rename_i he
        simp only [back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .inr (.inr (.inl ⟨hj0, r, he, rfl, rfl⟩))
      · split at h
        · rename_i hw
          simp only [back, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .inr (.inr (.inr ⟨hj0, r, hw, rfl, rfl⟩))
        · cases h
  | abort k => simp at h

/-- **A byte pick at `write(fd, buf, n)`**: the first case of
`sysStep_write_cases`. -/
theorem sysStep_write_byte {A : Arch} {tid : Nat} {c c' : Config I × KState} {rd : Nat} {es : List Ev}
    {t : Thread I} {fd buf n : Nat} (ht : c.1.threads[tid]? = some t)
    (hc : callOf K t = some (.write fd buf n)) (h : sysStep K A tid c (.byte rd) = some (es, c')) :
    ∃ b t', c.2.wr tid < n ∧ readByte K A t c.1.mem (buf + c.2.wr tid) rd = some (b, t') ∧
        es = (if fd = 1 then [.out b] else []) ∧
        c' = (c.1.withThread tid t' c.1.mem, c.2.set tid (.run (c.2.wr tid + 1))) := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  simp only at h
  split at h
  · rename_i hj
    cases hr : readByte K A t c.1.mem (buf + c.2.wr tid) rd with
    | none => rw [hr] at h; cases h
    | some x =>
      obtain ⟨b, t'⟩ := x
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨b, t', hj, rfl, rfl, rfl⟩
  · cases h

/-- **No byte of a placed label is private** (`DmemPriv.PrivKeys.hpriv`
over `MemRelP`). -/
theorem hpriv_label {Λ : Layout} {Ent : Entry} {s : I.State} (hd : DmemPriv.PrivKeys K Λ Ent s)
    (hwf : Λ.WF) (hE : Ent.clear Λ = true)
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat} (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp)
    {l : WeakMem.AllocLabel} {b k : Nat} (hl : lbl l = some b) (hk : k < 8 * lsize l) (x : UInt8) :
    (K.dmem s).loadBytes (BitVec.ofNat 64 (b + k)) 1 ≠ some [x] := by
  rcases (hm.lbl_range l b hl).2 with hs | hs | ⟨h0, -⟩
  · exact hd.hpriv_of_range hwf hE (r := lrange lsize l b) (.inl hs) hk x
  · exact hd.hpriv_of_range hwf hE (r := lrange lsize l b) (.inr hs) hk x
  · omega

end Kernel

/-! ## The frozen buffer's bytes -/

section Buf

variable {I : ISA} {Λ : Layout} {R : SpawnRec} {P : Inv2Params I} {G : Loc → Val → Prop}
  {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {sm : WeakMem.Memory}
  {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- **The kernel's read at thread 1 of byte `k` of the frozen buffer**
(the label `l` placed at `b0`, its words `⟨l, i⟩`, `i < N`, frozen on both
sides, `hfz`, holding `w i`, `hb`): lane `k % 8` of `w (k / 8)`; thread 1's
promises and cover kept. -/
theorem readByte_buf (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) (hwf : Λ.WF)
    {K : Abi I} {Ent : Entry} (hd : DmemPriv.PrivKeys K Λ Ent t1.st) (hE : Ent.clear Λ = true)
    {l : WeakMem.AllocLabel} {b0 : Nat} {w : Nat → Nat} {N : Nat} (hl : R.lbl l = some b0)
    (hN : N ≤ R.lsize l) (hb : HelloFrz.FrzBuf R.S l w N sm)
    (hfz : ∀ i < N, P.frzS ⟨l, i⟩ ∧ P.frz (wordLoc (b0 + 8 * i)))
    {A : Arch} {t1' : Thread I} {k rd : Nat} {bt : Fin 256} (hk : k / 8 < N)
    (hrb : readByte K A t1 tm (b0 + k) rd = some (bt, t1')) :
    bt.val = TermRun.laneN .w8 (w (k / 8)) (k % 8) ∧ t1'.prom = t1.prom ∧
      CohCoversL t1'.views t1'.prom tm (P.cov 1) := by
  have hb8 : b0 % 8 = 0 := (h.mem.lbl_range l b0 hl).1
  have ha : b0 + k - (b0 + k) % 8 = b0 + 8 * (k / 8) := by omega
  have hm8 : (b0 + k) % 8 = k % 8 := by omega
  obtain ⟨hfS, hfT⟩ := hfz (k / 8) hk
  obtain ⟨j, msg, hj, hm, hv⟩ := HelloFrz.hM_frz h hb hk hfS
  have hwa : wordAddr R.lbl ⟨l, k / 8⟩ = some (b0 + k - (b0 + k) % 8) := by
    rw [ha]; simp only [wordAddr, hl, Option.map_some]
  have hp := hpriv_label hd hwf hE h.mem hl (k := k) (by omega)
  have hf : P.frz (wordLoc (b0 + k - (b0 + k) % 8)) := by rw [ha]; exact hfT
  have := HelloFrz.readByte_frz h hwf hrb hp hf hwa hj hm hv
  rwa [hm8] at this

/-- **A byte step of thread 1's `write(1, b0 + k0, n)`** with `j` bytes out
(`c.2.wr 1 = j`, `(k0 + j) / 8 < N`): the event is `out bt`, `bt` lane
`(k0 + j) % 8` of `w ((k0 + j) / 8)`; memory unchanged, thread 1 replaced
by `t1'` with its promises and cover kept, the count `j + 1`. -/
theorem write_byte_buf {K : Abi I} {A : Arch} {c c' : Config I × KState} {es : List Ev} {rd : Nat}
    (h : Inv2Core Λ R P G own c.1.mem t0 t1 sm s0 s1 ts tp sp) (hwf : Λ.WF)
    {Ent : Entry} (hd : DmemPriv.PrivKeys K Λ Ent t1.st) (hE : Ent.clear Λ = true)
    {l : WeakMem.AllocLabel} {b0 : Nat} {w : Nat → Nat} {N : Nat} (hl : R.lbl l = some b0)
    (hN : N ≤ R.lsize l) (hb : HelloFrz.FrzBuf R.S l w N sm)
    (hfz : ∀ i < N, P.frzS ⟨l, i⟩ ∧ P.frz (wordLoc (b0 + 8 * i)))
    (ht : c.1.threads[1]? = some t1) {k0 n : Nat} (hc : callOf K t1 = some (.write 1 (b0 + k0) n))
    (hk : (k0 + c.2.wr 1) / 8 < N) (hs : sysStep K A 1 c (.byte rd) = some (es, c')) :
    ∃ bt t1', es = [.out bt] ∧ bt.val = TermRun.laneN .w8 (w ((k0 + c.2.wr 1) / 8)) ((k0 + c.2.wr 1) % 8) ∧
      c' = (c.1.withThread 1 t1' c.1.mem, c.2.set 1 (.run (c.2.wr 1 + 1))) ∧ t1'.prom = t1.prom ∧
      CohCoversL t1'.views t1'.prom c.1.mem (P.cov 1) := by
  obtain ⟨bt, t1', -, hr, he, hc'⟩ := sysStep_write_byte ht hc hs
  rw [Nat.add_assoc] at hr
  obtain ⟨hv, hp, hcov⟩ := readByte_buf h hwf hd hE hl hN hb hfz hk hr
  exact ⟨bt, t1', by simpa using he, hv, hc', hp, hcov⟩

end Buf

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.HelloWrite.write_byte_buf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write_byte_buf

end Spike.Lib.HelloWrite
