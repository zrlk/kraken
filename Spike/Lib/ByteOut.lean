/-
**The output's byte step for `print`** (`MemSide.bo`), on any ISA: what a
producer of the output row (`Out.emit`) states of each byte of a `write(1,
buf, n)` issued inside `print`'s loop, and what a consumer gets from it
against the memory invariant (`Scc.Sem.Inv1`).

- `ByteOut p lbl s a c1 Q`: byte `a` is byte `k` of the location `l`
  placed at `b` (`a = b + k`); from `c1` the source runs locally to
  `print`'s element load of byte `k` (`PrintSrc.loadC`), and whatever number
  `n` it reads there, the control after the byte's `emit`
  (`PrintSrc.nextC`, lane `k % 8` of `n`) runs locally into `Q`. A memory
  side takes it as `bo := ByteOut p lbl` (`MemSide.ofLabels`, `msOf`). It
  says nothing of the thread's private memory in `s`: that the byte is not
  private (so the kernel reads it from shared memory, `Kernel.readByte`) is
  the consumer's premise `hpriv` of `byteOut_emit`, from an invariant of the
  whole run, not a fact of a frame condition (one under `FStable` cannot
  state it: `Spike/Lib/PrivByteVacuous.lean`).
- `ByteOut.closed`: it is closed under local runs before and after (the
  `LocalClosed` of `print_call_segW`, `Spike/Lib/A64PrintCall.lean`,
  `Spike/Lib/X64PrintCall.lean`); `ByteOut.load`: it holds at `print`'s
  element load into the controls after the `emit`, the producer's half
  (`hlb` of `print_call_segW`).
- `byteOut_emit`: the consumer's half. From `ByteOut` at the thread's state,
  the invariant, the kernel's read of the byte, the byte not in the
  thread's private memory (`hpriv`), thread 0 of the source at `c1` inside
  a call and the source's latest message at the byte's word a number
  (`hnum`): the invariant holds after the read, and the source emits
  exactly the kernel's byte and lands in `Q`; `byteOut_emit_n`: so, with
  thread 0's allocation count kept.
-/
import Spike.Lib.PrintSrc
import Scc.Sem.RowsSrc
import Spike.Lib.Mem
import Spike.Lib.SegS

namespace Spike.Lib.ByteOut

open CoreLang CoreTerm TermRun
open Kraken.Promising
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib Spike.Lib.PrintSrc
open Scc.Sem.MemRel (SLatest)

/-- **The byte step of `print`'s loop at byte `a`** in state `s`, from the
source control `c1` into `Q` (see the module docstring): `a` is byte `k` of
the location `l` placed at `b`; `c1` runs locally to the element load of byte `k`, and for every number `n`
read there the control after the byte's `emit` runs locally into `Q`. -/
def ByteOut {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (_s : I.State)
    (a : Nat) (c1 : Ctl) (Q : Ctl → Prop) : Prop :=
  ∃ (pw wn : Word) (l b m k : Nat), pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some b ∧ a = b + k ∧
    LocalRun p c1 (loadC pw wn m k) ∧
    ∀ mw n, mw.val = .num n → ∃ c2, LocalRun p (nextC pw wn m k mw (laneN .w8 n (k % 8))) c2 ∧ Q c2

/-- A local run at any depth from a control with no hold ends with none. -/
theorem _root_.Spike.Lib.LocalRunS.hold_none {p : Prog} {c c' : Ctl} (h : LocalRunS p c c') (h0 : c.hold = none) :
    c'.hold = none := by
  induction h with
  | refl => exact h0
  | step hs _ ih => exact ih hs.1

/-- **`ByteOut` is closed under local runs** before its control and after
its landing. -/
theorem ByteOut.closed {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {s : I.State} {a : Nat} {c c' : Ctl} {Φ Ψ : Ctl → Prop} (hr : LocalRun p c c') (h : ByteOut p lbl s a c' Φ)
    (hΦ : ∀ c1, Φ c1 → ∃ c2, LocalRun p c1 c2 ∧ Ψ c2) : ByteOut p lbl s a c Ψ := by
  obtain ⟨pw, wn, l, b, m, k, hpw, hl, ha, hrun, hQ⟩ := h
  refine ⟨pw, wn, l, b, m, k, hpw, hl, ha, hr.trans hrun, fun mw n hmw => ?_⟩
  obtain ⟨c2, r2, h2⟩ := hQ mw n hmw
  obtain ⟨c3, r3, h3⟩ := hΦ c2 h2
  exact ⟨c3, r2.trans r3, h3⟩

/-- **`ByteOut` at `print`'s element load** of byte `k` of the location `l`
placed at `b`: into the controls after the byte's `emit`. -/
theorem ByteOut.load {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {s : I.State} {pw wn : Word} {l b m k : Nat} (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some b) :
    ByteOut p lbl s (b + k) (loadC pw wn m k) (fun c => ∃ mw v, c = nextC pw wn m k mw v) :=
  ⟨pw, wn, l, b, m, k, hpw, hl, rfl, .refl _, fun mw _ _ => ⟨_, .refl _, mw, _, rfl⟩⟩

/-- A one-byte load where private memory has no byte is no byte. -/
theorem loadBytes_one_none {m : _root_.Mem 64} {a : BitVec 64} (h : m[a]? = none) (x : UInt8) :
    m.loadBytes a 1 ≠ some [x] := by
  simp [Mem.loadBytes, List.allSome, h]

/-- **`byteOut_emit` with the allocation count kept** (`th'.nalloc`, the
source's byte run allocates nothing) and `hnum` asked of the byte's own
location only: for the label `l` placed at `b` of which `a` is byte `k`
(`ByteOut`'s witnesses), the latest message at `⟨l, k / 8⟩` a number. -/
theorem byteOut_emit_n {P : SrcParams} {p : Prog} {I : ISA} {K : Kernel.Abi I} {Λ : Layout}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {t t' : Thread I} {tm : Memory} {A : Arch} {a rd : Nat} {bt : Fin 256} {c1 : Ctl} {Q : Ctl → Prop}
    {s : Cfg} {th : TTh}
    (hP : UsesWc P p) (hbo : ByteOut p lbl t.st a c1 Q) (hinv : Inv1 Λ lbl lsize ts t tm s.mem)
    (hwf : Λ.WF) (hrb : Kernel.readByte K A t tm a rd = some (bt, t'))
    (hpriv : ∀ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x])
    (hi : s.ths[0]? = some th) (ht : th.term = c1.term) (he : th.env = c1.env) (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, Event.exit x ∉ s.trace)
    (hnum : ∀ (pw wn : Word) (l b m k : Nat), pw.val = .loc ⟨l, 0⟩ 0 → lbl l = some b → a = b + k →
      LocalRun p c1 (loadC pw wn m k) →
      ∃ j msg n, SLatest s.mem ⟨l, k / 8⟩ j ∧ s.mem[j]? = some msg ∧ msg.val = .num n) :
    Inv1 Λ lbl lsize ts t' tm s.mem ∧
      ∃ th', (source P p).Run s [.out bt] { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        Q ⟨th'.term, th'.env, none⟩ ∧ th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] ∧
          th'.nalloc = th.nalloc := by
  obtain ⟨pw, wn, l, b, m, k, hpw, hl, rfl, hrun, hQ⟩ := hbo
  have hb8 : b % 8 = 0 := (hinv.mem.lbl_range l b hl).1
  have ha : wordAddr lbl ⟨l, k / 8⟩ = some (b + k - (b + k) % 8) := by
    simp only [wordAddr, hl, Option.map_some]
    congr 1
    omega
  obtain ⟨j, msg, n, hj, hm, hv⟩ := hnum pw wn l b m k hpw hl rfl hrun
  obtain ⟨hi', hbt⟩ := hinv.readByte_src_num hwf hrb hpriv ha hj hm hv
  have hk8 : (b + k) % 8 = k % 8 := by omega
  rw [hk8] at hbt
  refine ⟨hi', ?_⟩
  have R0 := hrun.toS.run_source (traceThs_wc hP) hi ht he hσ hst hp
  obtain ⟨th', mw, R, ht', he', hσ', hst', hp', hmw, hn'⟩ := loadC_byte (P := P) (w := fun _ => n) (wn := wn) (m := m)
    (th := { th with term := (loadC pw wn m k).term, env := (loadC pw wn m k).env }) hP (set0 hi)
    rfl rfl hσ hst hp hpw hx ⟨j, msg, hj, hm, hv⟩
  have hbe : (⟨bt.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = bt := Fin.ext (Nat.mod_eq_of_lt bt.isLt)
  obtain ⟨c2, r2, hQ2⟩ := hQ mw n hmw
  have R01 := R0.trans R
  simp only [set!_set!] at R01
  have hi2 : ({ s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out (laneN .w8 n (k % 8))] } : Cfg).ths[0]?
      = some th' := set0 hi
  have R2 := r2.toS.run_source (traceThs_wc hP) hi2 (by rw [ht']) (by rw [he']) hσ' (hst' ▸ hst) hp'
  have R1 := R01.trans R2
  simp only [set!_set!, List.nil_append, List.append_nil, ← hbt, hbe] at R1
  refine ⟨_, R1, ?_, hσ', hst', hp', hn'⟩
  have h0 : c2.hold = none := r2.toS.hold_none rfl
  obtain ⟨t2, e2, h2⟩ := c2
  simp only at h0
  subst h0
  exact hQ2

/-- **A byte of the output, both sides.** Under `ByteOut` at the thread's
state, the memory invariant and the kernel's read `bt` of byte `a`, not
in the thread's private memory (`hpriv`, from a whole-run invariant of the
consumer: private memory's addresses stay within the private ranges,
disjoint from the placed labels' `Λ.heap`/`Λ.data`, `MemRel.lbl_range`): when
thread 0 of the source is at `c1` (no type variables, inside a call, no
promise, no exit yet) and the source's latest message at the word placed
at `a - a % 8` is a number (`hnum`), the invariant holds after the read,
and the source emits `bt` (`.out bt`, the kernel's event of the byte step)
and lands with thread 0 at a control in `Q`, its frames kept. -/
theorem byteOut_emit {P : SrcParams} {p : Prog} {I : ISA} {K : Kernel.Abi I} {Λ : Layout}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {t t' : Thread I} {tm : Memory} {A : Arch} {a rd : Nat} {bt : Fin 256} {c1 : Ctl} {Q : Ctl → Prop}
    {s : Cfg} {th : TTh}
    (hP : UsesWc P p) (hbo : ByteOut p lbl t.st a c1 Q) (hinv : Inv1 Λ lbl lsize ts t tm s.mem)
    (hwf : Λ.WF) (hrb : Kernel.readByte K A t tm a rd = some (bt, t'))
    (hpriv : ∀ x, (K.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x])
    (hi : s.ths[0]? = some th) (ht : th.term = c1.term) (he : th.env = c1.env) (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, Event.exit x ∉ s.trace)
    (hnum : ∀ sa, wordAddr lbl sa = some (a - a % 8) →
      ∃ j msg n, SLatest s.mem sa j ∧ s.mem[j]? = some msg ∧ msg.val = .num n) :
    Inv1 Λ lbl lsize ts t' tm s.mem ∧
      ∃ th', (source P p).Run s [.out bt] { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        Q ⟨th'.term, th'.env, none⟩ ∧ th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] :=
  let ⟨hi', th', R, hQ, hσ', hst', hp', _⟩ := byteOut_emit_n hP hbo hinv hwf hrb hpriv hi ht he hσ hst hp hx
    fun _ _ l b _ k _ hl ha _ => hnum _ (by
      have hb8 : b % 8 = 0 := (hinv.mem.lbl_range l b hl).1
      subst ha
      simp only [wordAddr, hl, Option.map_some]
      congr 1
      omega)
  ⟨hi', th', R, hQ, hσ', hst', hp'⟩

/-- The labels' memory side carries the byte step it is given. -/
example {I : ISA} (p : Prog) (rd : Word → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) :
    (MemSide.ofLabels (I := I) rd lbl lsize (bo := ByteOut p lbl)).bo = ByteOut p lbl := rfl

/-- By default it has none. -/
example {I : ISA} (rd : Word → Prop) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (s : I.State) (a : Nat) (c : Ctl) (Q : Ctl → Prop) : ¬ (MemSide.ofLabels (I := I) rd lbl lsize).bo s a c Q :=
  id

end Spike.Lib.ByteOut
