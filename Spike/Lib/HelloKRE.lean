/-
**hello.w on AArch64: the kernel relation with the worker's `write` link**
(design (i′)). Mid-`write`, the worker's
target thread is at `print`'s `svc` with `wr 1 = j` bytes out, and the
source worker is at the emit row's `Pw j`. `PT1` sees no kernel state, so
the link `j = wr 1` lives in the kernel relation: `KRHE := KRH ∧ Lk`.

`Lk` reads thread 1 (target and source), so it is not stable under the
kernel-relation frame fields of wake's `WCompat` (`kr`, `krp`: thread 1
arbitrary). Hello's store-phase relation `HelloW1Store.relW` therefore keeps
the thread-0-only `KRH`; `Lk` is rebuilt there from `wr 1 = 0`.

- `EmitCl`: the emit row's byte, return and refusal clauses at a state,
  frames, buffer and count, landing in the worker's invariant `D.Wi`.
- `EmitR`: the worker's target thread at a `write(1, buf, n)` and the
  source worker at the emit row's `Pw j`, `j ≤ n`.
- `WrOth`: the worker's target thread at a `write(fd, …)`, `fd ≠ 1`.
- `Lk`: with `wr 1 > 0`, `EmitR` or `WrOth` at `wr 1`; with the worker off
  its invariant `D.Wi`, `wr 1 > 0`.
- `KRHE`: `KRH ∧ Lk`.
- `lk_wr0` (no byte out, the worker in `D.Wi`), `lk_frame0` (thread 1 and slot 1 kept),
  `lk_congr1` (thread 1's state, the source worker's control and frames
  kept: a promise step), `wr_set_ne`, `wr_set_self`, `wr_set_run_le`.
-/
import Spike.Lib.HelloW1
import Spike.Lib.A64HelloWriteK
import Spike.Lib.WakeW1Step

namespace Spike.Lib.HelloKRE

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.A64HelloWriteK (KRH)

variable {ι : Type}

/-! ## The link -/

/-- **The emit row's clauses** at the state `st` and frames `fs`, for a
`write(1, buf, n)` with byte controls `Pw` and refusal controls `Qw`
(`Out.emit`'s last three premises at `D.ms w fs` and `X := D.Wi w · · fs`). -/
def EmitCl (D : WSideH ι) (w : ι) (st : isaLSE2.State) (fs : List TermRun.Frame) (buf n : Nat)
    (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop) : Prop :=
  (∀ j < n, ∀ c1, Pw j c1 → (D.ms w fs).bo st (buf + j) c1 (Pw (j + 1))) ∧
    (∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ results (.write 1 buf n), WriteRetOk j r →
      D.Wi w (abi.ret st r) c1 fs ∧ (j = 0 → writeRefused r = true → Qw c1)) ∧
    (∀ c1, Qw c1 → (D.ms w fs).we st c1)

/-- **The worker mid-`write`, `j` bytes out**: its target thread at a
`write(1, buf, n)` system call with the emit row's clauses (`EmitCl`) at the
source worker's frames, and the source worker at `Pw j`, `j ≤ n`. -/
def EmitR (D : WSideH ι) (w : ι) (t1 : Thread isaLSE2) (s1 : TermRun.TTh) (j : Nat) : Prop :=
  ∃ buf n Pw Qw, abi.atSys t1.st = true ∧ decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n) ∧
    EmitCl D w t1.st s1.stack buf n Pw Qw ∧ j ≤ n ∧ Pw j (Ctl.of s1)

/-- **The worker mid-`write` to another descriptor, `j` bytes out**: its
target thread at a `write(fd, buf, n)` system call, `fd ≠ 1`, `j ≤ n` (the
abort path's `write(2, …)`). -/
def WrOth (t1 : Thread isaLSE2) (j : Nat) : Prop :=
  ∃ fd buf n, fd ≠ 1 ∧ abi.atSys t1.st = true ∧
    decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write fd buf n) ∧ j ≤ n

/-- **The `write` link**: with bytes of the worker's current `write` out
(`wr 1 > 0`), the worker is mid-`write` at that count: to `stdout` at the
emit row (`EmitR`), or to another descriptor (`WrOth`); and conversely, with
the worker off its invariant (mid-emit: the source at the emit row's `Pw j`,
`HelloEmitPh.EmitPh`), bytes are out. -/
def Lk (D : WSideH ι) (w : ι) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  (0 < t.2.wr 1 → ∃ t1 s1, t.1.threads[1]? = some t1 ∧ s.ths[1]? = some s1 ∧
    (EmitR D w t1 s1 (t.2.wr 1) ∨ WrOth t1 (t.2.wr 1))) ∧
  ∀ t1 s1, t.1.threads[1]? = some t1 → s.ths[1]? = some s1 → ¬ D.Wi w t1.st (Ctl.of s1) s1.stack →
    0 < t.2.wr 1

/-- **Hello's kernel relation with the `write` link.** -/
def KRHE (D : WSideH ι) (r0 r1 : ι → Range) (w : ι) (t : Cfg) (s : TermRun.Cfg) : Prop :=
  KRH r0 r1 w t s ∧ Lk D w t s

/-! ## The link's frame lemmas -/

variable {D : WSideH ι} {w : ι}

/-- **No byte out, the worker in its invariant**: the link holds. -/
theorem lk_wr0 {t : Cfg} {s : TermRun.Cfg} (h : t.2.wr 1 = 0)
    (hW : ∀ t1 s1, t.1.threads[1]? = some t1 → s.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) :
    Lk D w t s :=
  ⟨fun hp => absurd h (Nat.pos_iff_ne_zero.mp hp), fun t1 s1 h1 h2 hn => absurd (hW t1 s1 h1 h2) hn⟩

/-- **A step keeping thread 1 (target and source) and slot 1's count keeps
the link** (a step of main). -/
theorem lk_frame0 {t t' : Cfg} {s s' : TermRun.Cfg} (h : Lk D w t s)
    (ht : t'.1.threads[1]? = t.1.threads[1]?) (hs : s'.ths[1]? = s.ths[1]?) (hwr : t'.2.wr 1 = t.2.wr 1) :
    Lk D w t' s' := by
  refine ⟨fun hp => ?_, fun t1 s1 h1 h2 hn => ?_⟩
  · rw [hwr] at hp ⊢
    obtain ⟨t1, s1, h1, h2, h3⟩ := h.1 hp
    exact ⟨t1, s1, ht.trans h1, hs.trans h2, h3⟩
  · rw [hwr]
    exact h.2 t1 s1 (ht.symm.trans h1) (hs.symm.trans h2) hn

/-- **`EmitR` reads the target thread's state, the source worker's control
and frames only.** -/
theorem EmitR.congr {t1 t1' : Thread isaLSE2} {s1 s1' : TermRun.TTh} {j : Nat} (h : EmitR D w t1 s1 j)
    (hst : t1'.st = t1.st) (hc : Ctl.of s1' = Ctl.of s1) (hfs : s1'.stack = s1.stack) : EmitR D w t1' s1' j := by
  obtain ⟨buf, n, Pw, Qw, ha, hd, hcl, hj, hP⟩ := h
  exact ⟨buf, n, Pw, Qw, hst ▸ ha, hst ▸ hd, hst ▸ hfs ▸ hcl, hj, hc ▸ hP⟩

/-- **A step keeping thread 1's state, the source worker's control and
frames and slot 1's count keeps the link** (a promise of the worker). -/
theorem lk_congr1 {t t' : Cfg} {s s' : TermRun.Cfg} {t1 t1' : Thread isaLSE2} {s1 s1' : TermRun.TTh}
    (h : Lk D w t s) (ht1 : t.1.threads[1]? = some t1) (hs1 : s.ths[1]? = some s1)
    (ht1' : t'.1.threads[1]? = some t1') (hs1' : s'.ths[1]? = some s1') (hst : t1'.st = t1.st)
    (hc : Ctl.of s1' = Ctl.of s1) (hfs : s1'.stack = s1.stack) (hwr : t'.2.wr 1 = t.2.wr 1) : Lk D w t' s' := by
  refine ⟨fun hp => ?_, fun u1 v1 h1 h2 hn => ?_⟩
  · rw [hwr] at hp ⊢
    obtain ⟨u1, v1, h1, h2, h3⟩ := h.1 hp
    obtain rfl : u1 = t1 := Option.some.inj (h1.symm.trans ht1)
    obtain rfl : v1 = s1 := Option.some.inj (h2.symm.trans hs1)
    refine ⟨t1', s1', ht1', hs1', h3.imp (·.congr hst hc hfs) ?_⟩
    rintro ⟨fd, buf, n, hfd, ha, hd, hj⟩
    exact ⟨fd, buf, n, hfd, hst ▸ ha, hst ▸ hd, hj⟩
  · obtain rfl : u1 = t1' := Option.some.inj (h1.symm.trans ht1')
    obtain rfl : v1 = s1' := Option.some.inj (h2.symm.trans hs1')
    rw [hwr]
    exact h.2 t1 s1 ht1 hs1 (by rw [← hst, ← hc, ← hfs]; exact hn)

/-! ## Slot counts -/

/-- **Setting another slot keeps a slot's count.** -/
theorem wr_set_ne (k : KState) {i j : Nat} (sl : Slot) (h : i ≠ j) : (k.set i sl).wr j = k.wr j := by
  simp only [KState.wr, KState.set, Array.set!, Array.getElem?_setIfInBounds_ne h]

/-- **A slot set running at `m` has count `m`.** -/
theorem wr_set_self (k : KState) {i : Nat} (m : Nat) (h : i < k.slots.size) : (k.set i (.run m)).wr i = m := by
  simp only [KState.wr, KState.set, Array.set!, Array.getElem?_setIfInBounds_self_of_lt h]

/-- **A slot set running at `m` has count at most `m`.** -/
theorem wr_set_run_le (k : KState) (i m : Nat) : (k.set i (.run m)).wr i ≤ m := by
  by_cases h : i < k.slots.size
  · exact Nat.le_of_eq (wr_set_self k m h)
  · simp only [KState.wr, KState.set, Array.set!]
    have e : k.slots.setIfInBounds i (.run m) = k.slots := by simp [Array.setIfInBounds, h]
    rw [e, Array.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

/-- **A slot set running at 0 has count 0.** -/
theorem wr_set_run0_self (k : KState) (i : Nat) : (k.set i (.run 0)).wr i = 0 :=
  Nat.le_zero.mp (wr_set_run_le k i 0)

/-- **A slot set to anything but `run` has count 0.** -/
theorem wr_set_exited (k : KState) (i : Nat) : (k.set i .exited).wr i = 0 := by
  simp only [KState.wr, KState.set, Array.set!]
  by_cases h : i < k.slots.size
  · simp only [Array.getElem?_setIfInBounds_self_of_lt h]
  · have e : k.slots.setIfInBounds i .exited = k.slots := by simp [Array.setIfInBounds, h]
    rw [e, Array.getElem?_eq_none (by omega)]

/-- **A system call other than a `write` keeps a thread's count or zeroes
it** (`sysStep`: its kernel states are the old one, slot `tid` exited, or
the process exited). -/
theorem sysStep_wr_nowrite {A : Arch} {tid : Nat} {t t' : Cfg} {p : Pick} {es : List Ev}
    {t1 : Thread isaLSE2} (ht : t.1.threads[tid]? = some t1)
    (hc : ∀ fd buf n, callOf abi t1 ≠ some (.write fd buf n)) (h : sysStep abi A tid t p = some (es, t')) :
    t'.2.wr tid = t.2.wr tid ∨ t'.2.wr tid = 0 := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  split at h
  · rename_i heq; exact absurd heq (hc _ _ _)
  · rename_i heq; exact absurd heq (hc _ _ _)
  all_goals (repeat' split at h)
  all_goals first
    | (cases h <;> first | exact .inl rfl | exact .inr (wr_set_exited _ _))
    | (simp only [back, Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       first | exact .inl rfl | exact .inr (wr_set_exited _ _))

/-- **Setting a slot running at 0 keeps a count or zeroes it.** -/
theorem wr_set_run0 (k : KState) (i j : Nat) : (k.set j (.run 0)).wr i = k.wr i ∨ (k.set j (.run 0)).wr i = 0 := by
  by_cases h : j = i
  · subst h
    refine .inr ?_
    simp only [KState.wr, KState.set, Array.set!]
    by_cases hl : j < k.slots.size
    · simp only [Array.getElem?_setIfInBounds_self_of_lt hl]
    · have e : k.slots.setIfInBounds j (.run 0) = k.slots := by simp [Array.setIfInBounds, hl]
      rw [e, Array.getElem?_eq_none (by omega)]
  · exact .inl (wr_set_ne k _ h)

/-- **A system call is at a system call.** -/
theorem sysStep_atSys {A : Arch} {tid : Nat} {t t' : Cfg} {p : Pick} {es : List Ev} {t1 : Thread isaLSE2}
    (ht : t.1.threads[tid]? = some t1) (h : sysStep abi A tid t p = some (es, t')) : abi.atSys t1.st = true := by
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  · rename_i hr
    simp only [ready, Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hr
    exact hr.1.1

/-- **A step of a thread other than a `write` system call keeps its count
or zeroes it**: an instruction, a promise, a transfer keep the kernel's
slots; a system call by `sysStep_wr_nowrite`; a `clone` sets a slot
running at 0. -/
theorem wr_step_nowrite {μ : Marks} {tid : Nat} {t t' : Cfg} {es : List Ev} {t1 : Thread isaLSE2}
    (ht : t.1.threads[tid]? = some t1)
    (hnw : abi.atSys t1.st = false ∨ ∀ fd buf n, callOf abi t1 ≠ some (.write fd buf n))
    (hs : (machine (kernel 2)).Step μ tid t es t') : t'.2.wr tid = t.2.wr tid ∨ t'.2.wr tid = 0 := by
  rcases WakeW1.step1_cases ht hs with ⟨-, -, -, -, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨p, hp, -⟩ |
    ⟨-, j, r, hsp⟩ | ⟨-, k, -, hx⟩
  · exact .inl rfl
  · exact .inl rfl
  · rcases hnw with hn | hn
    · rw [sysStep_atSys ht hp] at hn; cases hn
    · exact sysStep_wr_nowrite ht hn hp
  · unfold spawnStep at hsp
    rw [ht] at hsp
    simp only at hsp
    repeat' split at hsp
    all_goals (cases hsp <;> exact wr_set_run0 _ _ _)
  · cases k with
    | take =>
      change takeStep abi tid t = some t' at hx
      unfold takeStep at hx
      rw [ht] at hx
      simp only at hx
      split at hx
      · simp only [Option.some.injEq] at hx; subst hx; exact .inl rfl
      · cases hx
    | release =>
      change releaseStep abi tid t = some t' at hx
      unfold releaseStep at hx
      rw [ht] at hx
      simp only at hx
      split at hx
      · simp only [Option.some.injEq] at hx; subst hx; exact .inl rfl
      · cases hx

/-- **Off a `write`, the worker has no byte out** (`Lk`: mid-`write` it is
at a `write` system call). -/
theorem wr1_zero {t : Cfg} {s : TermRun.Cfg} {t1 : Thread isaLSE2} (h : Lk D w t s)
    (ht : t.1.threads[1]? = some t1)
    (hnw : abi.atSys t1.st = false ∨ ∀ fd buf n, callOf abi t1 ≠ some (.write fd buf n)) : t.2.wr 1 = 0 := by
  refine Nat.eq_zero_of_not_pos fun hp => ?_
  obtain ⟨u1, _, h1, -, hE⟩ := h.1 hp
  obtain rfl : u1 = t1 := Option.some.inj (h1.symm.trans ht)
  obtain ⟨fd, buf, n, ha, hd⟩ : ∃ fd buf n, abi.atSys u1.st = true ∧
      decode abi.nrs (abi.nr u1.st) (abi.arg u1.st) = some (.write fd buf n) := by
    rcases hE with ⟨buf, n, -, -, ha, hd, -⟩ | ⟨fd, buf, n, -, ha, hd, -⟩
    · exact ⟨1, buf, n, ha, hd⟩
    · exact ⟨fd, buf, n, ha, hd⟩
  rcases hnw with hn | hn
  · rw [ha] at hn; cases hn
  · exact hn fd buf n hd

/-- **A step of the worker other than a `write` system call keeps the
link**, at any source configuration with the worker in its invariant (no
byte out before or after). -/
theorem lk_step1_nowrite {μ : Marks} {t t' : Cfg} {s s' : TermRun.Cfg} {es : List Ev} {t1 : Thread isaLSE2}
    (h : Lk D w t s) (ht : t.1.threads[1]? = some t1)
    (hnw : abi.atSys t1.st = false ∨ ∀ fd buf n, callOf abi t1 ≠ some (.write fd buf n))
    (hs : (machine (kernel 2)).Step μ 1 t es t')
    (hW : ∀ t1 s1, t'.1.threads[1]? = some t1 → s'.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) :
    Lk D w t' s' := by
  have h0 := wr1_zero h ht hnw
  refine lk_wr0 ?_ hW
  rcases wr_step_nowrite ht hnw hs with e | e
  · rw [e, h0]
  · exact e

/-- info: 'Spike.Lib.HelloKRE.lk_congr1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lk_congr1

/-- info: 'Spike.Lib.HelloKRE.lk_step1_nowrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lk_step1_nowrite

end Spike.Lib.HelloKRE
