/-
**A consumer of the per-construct judgement on the canonical targets**
(`ExtMachine.ofHooks I A (Kernel.hooks K A n)`), for any ISA: the thread's
steps from code states, generalising the closed toys
`Spike/Lib/A64ExtToy.lean` and `Spike/Lib/A64ExtToy2.lean`.

`Spike/Lib/Thread.lean` is the consumer on the base machine
(`ExtMachine.ofBase`, two threads, `CertOk`); its per-case lemmas are stated
for Kraken's `ThreadStep`. The one-thread analogues under the kernel's
certification semantics (`Kernel.certSem`, `CertOkC`) are re-proved here
rather than generalising `Thread.lean` in place.

**Silent code** (`SilentCode K Q`): every tree the ISA's `exec` yields from
a code state (`Q`) is quiet (choices and plain loads, `Kernel.QuietTree`)
with its leaves code states, and the states the solo projection may resume
the thread in (`Kernel.SoloLeaf`) are code states; so every tree of
`Kernel.soloExec` from `Q` is quiet with leaves in `Q`
(`Kernel.soloExec_cases`).

- `instrSemC_silent`: an instruction step at a quiet tree keeps memory and
  promises and ends at a leaf.
- `not_promSemC`: from silent code no promise step is certified
  (`Spike.Bridge.CertC.no_certOkC_of_closed`).
- `instr_step`: **an instruction step of the canonical machine** from a
  code state with no promise is an instruction at a silent tree: one thread
  replaced, memory and kernel state unchanged, no promise, a code state.

**The one-thread invariant** (`Scc.Sem.Inv1`) across the machine's steps:

- `inv1_retThread`, `inv1_readByte`, `inv1_sysStep`: every kernel step but
  `clone` keeps `Inv1`; `sysStep_wideInv`: and an invariant of
  `certExec K`'s instructions; `bnd_retThread`, `bnd_readByte`,
  `bnd_sysStep`: and the thread's values at most `|M|` (`Thread.Bnd`).
- `inv1_silent`, `inv1_rtLoad`: the silent and runtime-load rows keep
  `Inv1` (the store, load and fence rows are `Inv1.store`, `Inv1.rtStore`,
  `Inv1.load`, `Inv1.fence`).
- `step_cases`: a step of the canonical machine is an instruction (one
  `stepOne` outcome, the thread kept in the invariant), a one-word promise
  of the thread's own that keeps `Inv1`, or a kernel step that keeps `Inv1`; `step_cases_of`:
  the same, the range transfers excluded only where the thread is at a
  transfer site.
-/
import Scc.Sem.KernelStep
import Spike.Bridge.CertC
import Scc.Sem.CertStep
import Scc.Sem.Rows1
import Scc.Sem.SysLink

namespace Spike.Lib.ExtThread

open Kraken.Promising Kraken.Promising.Lower Scc.Sem Spike.Bridge.CertC

variable {I : ISA} {A : Arch}

/-- **An instruction step at a quiet tree**, certified under any `cs`:
memory and promises stay, the thread is at a leaf. -/
theorem instrSemC_silent {cs : CertSem I} {tid : Nat} {c c' : Config I}
    {t : Thread I} {tree : EvTree I.State} (ht : c.threads[tid]? = some t)
    (hex : I.exec t.st = some tree) (hs : Kernel.QuietTree tree) (h : InstrSemC A cs tid c c') :
    ∃ th, c' = c.withThread tid th c.mem ∧ th.prom = t.prom ∧ TreeLeaf tree th.st := by
  obtain ⟨t', outs, o, ht', hso, ho, -, rfl⟩ := h
  obtain rfl : t' = t := Option.some.inj (ht'.symm.trans ht)
  obtain ⟨hm, hp, hl⟩ := Kernel.stepOneWith_quiet (cs := CertSem.ofExec I.exec) hex hs hso ho
  exact ⟨o.thread, by rw [hm], hp, hl⟩

/-- **Silent code**: every tree the ISA's `exec` yields from a state of `Q`
is quiet with its leaves in `Q`, and every state the solo projection may
resume a thread of `Q` in is in `Q`. -/
def SilentCode (K : Kernel.Abi I) (Q : I.State → Prop) : Prop :=
  (∀ s, Q s → ∀ tree, I.exec s = some tree → Kernel.QuietTree tree ∧ ∀ s', TreeLeaf tree s' → Q s') ∧
    ∀ s s', Q s → Kernel.SoloLeaf K s s' → Q s'

/-- Under silent code every tree of `soloExec` is quiet with its leaves in
`Q`. -/
theorem SilentCode.solo {K : Kernel.Abi I} {Q : I.State → Prop} (hQ : SilentCode K Q) {μ : Marks}
    {x : Kernel.KState} {tid : Nat} {s : I.State} (hq : Q s) {tree : EvTree I.State}
    (he : Kernel.soloExec K A μ x tid s = some tree) : Kernel.QuietTree tree ∧ ∀ s', TreeLeaf tree s' → Q s' :=
  (Kernel.soloExec_cases he).elim (hQ.1 _ hq _) fun h => ⟨h.1, fun s' hl => hQ.2 _ _ hq (h.2 s' hl)⟩

/-- **From silent code no promise step is certified**: certification never
fulfils the new promise. -/
theorem not_promSemC {K : Kernel.Abi I} {Q : I.State → Prop} (hQ : SilentCode K Q) {μ : Marks}
    {x : Kernel.KState} {tid : Nat} {c c' : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
    (hq : Q t.st) : ¬ PromSemC A (Kernel.certSem K A μ x tid) tid c c' := by
  rintro ⟨t', w, ht', -, hc, -⟩
  obtain rfl : t' = t := Option.some.inj (ht'.symm.trans ht)
  refine no_certOkC_of_closed (fun t mem q hq h => ?_) (t := Live.Sem.promThread t' c.mem w) hq (by simp) hc
  obtain ⟨outs, o, hso, ho, rfl⟩ := h
  cases hex : Kernel.soloExec K A μ x tid t.st with
  | none => exact absurd ⟨outs, o, hso, ho, rfl⟩ (stepC_none (cs := Kernel.certSem K A μ x tid) hex)
  | some tree =>
    obtain ⟨hqt, hl⟩ := hQ.solo hq hex
    obtain ⟨-, hp, hlf⟩ := Kernel.stepOneWith_quiet (cs := Kernel.certSem K A μ x tid) hex hqt hso ho
    exact ⟨hp, hl _ hlf⟩

variable {n : Nat} {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)}
  {pcf : I.State → Nat}

/-- **An instruction step of the canonical machine from a code state** (off
a system call, as `Step.instr` requires): one thread replaced, memory and
kernel state unchanged, the promises kept, a code state. -/
theorem instr_step {K : Kernel.Abi I} {Q : I.State → Prop} (hQ : SilentCode K Q) {μ : Marks} {tid : Nat}
    {c c' : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hq : Q t.st)
    (hs : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Step μ tid c [] c')
    (hsp : ¬ (Kernel.hooks K A n).spawn μ tid c c') (hsy : ¬ (Kernel.hooks K A n).sys μ tid c [] c')
    (hxf : ∀ k, ¬ (Kernel.hooks K A n).xfer k tid c c') :
    ∃ th, c' = (c.1.withThread tid th c.1.mem, c.2) ∧ th.prom = t.prom ∧ Q th.st := by
  cases hs with
  | instr _ _ _ hstep =>
    rcases hstep with hi | hp
    · cases hE : I.exec t.st with
      | none =>
        exfalso
        obtain ⟨t', outs, o, ht', hso, -⟩ := hi
        rw [ht] at ht'
        cases ht'
        unfold stepOne at hso
        change (I.exec t.st).bind _ = _ at hso
        rw [hE] at hso
        cases hso
      | some tree =>
        obtain ⟨hqt, hl⟩ := hQ.1 _ hq _ hE
        obtain ⟨th, rfl, hpr, hlf⟩ := instrSemC_silent ht hE hqt hi
        exact ⟨th, rfl, hpr, hl _ hlf⟩
    · exact absurd hp (not_promSemC hQ ht hq)
  | spawn _ h => exact absurd h hsp
  | sys _ h => exact absurd h hsy
  | xfer k _ _ h => exact absurd h (hxf k)

/-! ## The kernel's steps keep the one-thread invariant -/

section Kernel

variable (K : Kernel.Abi I)

/-- **The kernel's byte read of a `write` buffer only raises coherence
views**: it is a plain load, or reads private memory. -/
theorem readByte_getCoh_le {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256}
    (h : Kernel.readByte K A t mem a rd = some (b, t')) (l : Loc) : t.views.getCoh l ≤ t'.views.getCoh l := by
  unfold Kernel.readByte at h
  split at h
  · cases h; exact Nat.le_refl _
  · split at h
    · rename_i x v c' hx
      cases h
      obtain ⟨-, -, -, he⟩ := readSuccs_shape A _ (List.mem_of_getElem? hx)
      have hv := congrArg (fun c : Ctx => c.views.getCoh l) he
      simp only at hv
      show t.views.getCoh l ≤ c'.views.getCoh l
      rw [hv]; exact getCoh_le_setCoh _ _ _ _
    · cases h

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}

/-- **`Inv1` of a thread depends on its views and promises only up to
raising coherence views.** -/
theorem inv1_of_views {t t' : Thread I} (h : Inv1 Λ lbl lsize ts t tm sm) (hp : t'.prom = t.prom)
    (hle : ∀ l, t.views.getCoh l ≤ t'.views.getCoh l) : Inv1 Λ lbl lsize ts t' tm sm :=
  ⟨hp ▸ h.mem, hp ▸ h.coh.mono hle, h.narrow⟩

/-- **A return from a system call keeps `Inv1`** (views, promises and memory
unchanged). -/
theorem inv1_retThread {t : Thread I} (h : Inv1 Λ lbl lsize ts t tm sm) (r : BitVec 64) :
    Inv1 Λ lbl lsize ts (Kernel.retThread K t r) tm sm :=
  inv1_of_views h (Kernel.retThread_prom (K := K) t r) fun l => by rw [retThread_views]; exact Nat.le_refl _

/-- **A byte of a `write` keeps `Inv1`** (memory and promises unchanged,
coherence views raised). -/
theorem inv1_readByte {t t' : Thread I} {a rd : Nat} {b : Fin 256} (h : Inv1 Λ lbl lsize ts t tm sm)
    (hb : Kernel.readByte K A t tm a rd = some (b, t')) : Inv1 Λ lbl lsize ts t' tm sm :=
  inv1_of_views h (Kernel.readByte_prom hb) (readByte_getCoh_le K hb)

/-- **Every kernel step other than `clone` keeps `Inv1`**: it leaves the
configuration alone (`exit`, `exit_group`) or replaces thread `tid` by one
satisfying `Inv1` over the same memory (a byte of a `write`, a return). -/
theorem inv1_sysStep {tid : Nat} {c c' : Config I × Kernel.KState} {p : Kernel.Pick} {es : List Ev}
    {t : Thread I} (ht : c.1.threads[tid]? = some t) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : Kernel.sysStep K A tid c p = some (es, c')) :
    c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm := by
  have hb : ∀ (u : Thread I) r x es', Inv1 Λ lbl lsize ts u c.1.mem sm →
      Kernel.back K tid c u r x es' = some (es, c') →
      c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm := by
    intro u r x es' hu hb
    simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact .inr ⟨_, rfl, inv1_retThread K hu r⟩
  unfold Kernel.sysStep at hs
  rw [ht] at hs
  simp only at hs
  split at hs
  · cases hs
  split at hs
  · obtain ⟨⟨b, t'⟩, hr, he⟩ := Option.map_eq_some_iff.mp (by split at hs <;> first | exact hs | cases hs)
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact .inr ⟨t', rfl, inv1_readByte K h hr⟩
  all_goals repeat' first
    | exact hb _ _ _ _ h hs
    | exact hb _ _ _ _ (by exact inv1_of_views h rfl fun _ => Nat.le_refl _) hs
    | (simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs; exact .inl rfl)
    | (cases hs; done)
    | split at hs

/-- **The kernel state after a return** of a call other than `exit` and
`exit_group`: the slot's `write` count reset to 0, or unchanged, the count
being 0 then if the call is a `write`. -/
theorem sysStep_ret_kstate {tid : Nat} {c c' : Config I × Kernel.KState} {r : BitVec 64} {es : List Ev}
    {t : Thread I} (ht : c.1.threads[tid]? = some t) (hs : Kernel.sysStep K A tid c (.ret r) = some (es, c'))
    (hx : Kernel.callOf K t ≠ some .exit) (hg : ∀ v, Kernel.callOf K t ≠ some (.exitGroup v)) :
    c'.2 = c.2.set tid (.run 0) ∨
      (c'.2 = c.2 ∧ ∀ fd buf n, Kernel.callOf K t = some (.write fd buf n) → c.2.wr tid = 0) := by
  have hb : ∀ (u : Thread I) r' x es', Kernel.back K tid c u r' x es' = some (es, c') → c'.2 = x := by
    intro u r' x es' hb
    simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    rfl
  unfold Kernel.sysStep at hs
  rw [ht] at hs
  simp only at hs
  split at hs
  · cases hs
  generalize hcall : Kernel.callOf K t = cl at hs hx hg
  rcases cl with _ | call
  · cases hs
  cases call with
  | write fd buf n =>
    simp only at hs
    split at hs
    · split at hs
      · exact .inl (hb _ _ _ _ hs)
      · cases hs
    · rename_i hj
      refine .inr ⟨?_, fun _ _ _ _ => by omega⟩
      split at hs
      · exact hb _ _ _ _ hs
      · split at hs
        · exact hb _ _ _ _ hs
        · cases hs
  | exit => exact absurd rfl hx
  | exitGroup v => exact absurd rfl (hg v)
  | futexWait =>
    simp only at hs
    split at hs
    · exact .inr ⟨hb _ _ _ _ hs, fun _ _ _ h => by cases h⟩
    · cases hs
  | futexWake n =>
    simp only at hs
    split at hs
    · exact .inr ⟨hb _ _ _ _ hs, fun _ _ _ h => by cases h⟩
    · cases hs
  | rtSigaction =>
    simp only at hs
    split at hs
    · exact .inr ⟨hb _ _ _ _ hs, fun _ _ _ h => by cases h⟩
    · cases hs
  | archSetFs a =>
    simp only at hs
    split at hs
    · exact .inr ⟨hb _ _ _ _ hs, fun _ _ _ h => by cases h⟩
    · cases hs
  | clone st tl =>
    simp only at hs
    split at hs
    · exact .inr ⟨hb _ _ _ _ hs, fun _ _ _ h => by cases h⟩
    · cases hs

/-- **Every kernel step other than `clone` keeps an invariant `P` of
`certExec K`'s instructions** (`WideInv`): a byte of a `write` keeps the
thread's state, a return lands in a state `certSuccs` lists (a leaf of
`certExec K`'s tree at the call), `exit` and `exit_group` change no thread.
A `write` has at most `n` bytes out (`hwr`, as for `Kernel.sysStep_cases`). -/
theorem sysStep_wideInv {P : I.State → Prop} (hP : WideInv P (Kernel.certExec K)) {tid : Nat}
    {c c' : Config I × Kernel.KState} {p : Kernel.Pick} {es : List Ev} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hst : P t.st) (hs : Kernel.sysStep K A tid c p = some (es, c'))
    (hwr : ∀ fd buf n, Kernel.callOf K t = some (.write fd buf n) → c.2.wr tid ≤ n) {t' : Thread I}
    (ht' : c'.1.threads[tid]? = some t') : P t'.st := by
  obtain ⟨hr, call, hcall, hc⟩ := Kernel.sysStep_cases (K := K) ht hs hwr
  rcases hc with ⟨fd, buf, n, rd, b, u, -, -, -, -, hu, -, rfl⟩ | ⟨r, -, -, -, -, -, u, hu, hsu, -⟩ |
    ⟨-, -, -, rfl⟩ | ⟨v, -, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
  · rw [Live.Sem.withThread_get_self ht] at ht'
    cases ht'
    exact hu ▸ hst
  · rw [hu] at ht'
    cases ht'
    have hsys : K.atSys t.st = true := by
      simp only [Kernel.ready, Bool.and_eq_true] at hr; exact hr.1.1
    refine hP _ _ _ hst (Kernel.certExec_of_decode hsys hcall) ?_
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hsu
    exact ⟨⟨i, hi⟩, he.symm⟩
  all_goals rw [ht] at ht'; cases ht'; exact hst

/-! ### Thread values stay at most `|M|` (`Thread.Bnd`) -/

/-- **A return keeps the thread's values at most `n`**: register views set
to 0, views unchanged. -/
theorem bnd_retThread {t : Thread I} {n : Nat} (h : t.Bnd n) (r : BitVec 64) : (Kernel.retThread K t r).Bnd n := by
  have : ∀ (regs : List I.RegId) (u : Thread I), u.Bnd n →
      (regs.foldl (fun t reg => t.setRegView reg 0 0) u).Bnd n := by
    intro regs
    induction regs with
    | nil => exact fun _ h => h
    | cons r rs ih => exact fun u hu => ih _ ⟨hu.views, hu.regs.setRegView r (Nat.zero_le _) (Nat.zero_le _)⟩
  exact this _ _ ⟨h.views, h.regs⟩

/-- **A byte of a `write` keeps the thread's values at most `|M|`**: a
plain load's views (`readSuccs_bnd`), or none changed. -/
theorem bnd_readByte {t t' : Thread I} {mem : Memory} {a rd : Nat} {b : Fin 256} (h : t.Bnd mem.last)
    (hb : Kernel.readByte K A t mem a rd = some (b, t')) : t'.Bnd mem.last := by
  unfold Kernel.readByte at hb
  split at hb
  · cases hb; exact h
  · split at hb
    · rename_i x v c' hx
      cases hb
      have hc : Ctx.Bnd { views := t.views, prom := t.prom, mem } :=
        ⟨h.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
      have hiv : Kernel.iv0.Le mem.last :=
        ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ h => by
          simp [Kernel.iv0] at h⟩
      obtain ⟨hc', -, hm⟩ := readSuccs_bnd A Kernel.iv0 hc hiv (List.mem_of_getElem? hx)
      exact ⟨(show c'.mem = mem from hm) ▸ hc'.views, h.regs⟩
    · cases hb

/-- **Every kernel step other than `clone` keeps the thread's values at
most `|M|`** (as `inv1_sysStep`: the configuration unchanged, or thread
`tid` replaced over the same memory). -/
theorem bnd_sysStep {tid : Nat} {c c' : Config I × Kernel.KState} {p : Kernel.Pick} {es : List Ev}
    {t : Thread I} (ht : c.1.threads[tid]? = some t) (h : t.Bnd c.1.mem.last)
    (hs : Kernel.sysStep K A tid c p = some (es, c')) :
    c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ u.Bnd c.1.mem.last := by
  have hb : ∀ (u : Thread I) r x es', u.Bnd c.1.mem.last →
      Kernel.back K tid c u r x es' = some (es, c') →
      c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ u.Bnd c.1.mem.last := by
    intro u r x es' hu hb
    simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact .inr ⟨_, rfl, bnd_retThread K hu r⟩
  unfold Kernel.sysStep at hs
  rw [ht] at hs
  simp only at hs
  split at hs
  · cases hs
  split at hs
  · obtain ⟨⟨b, t'⟩, hr, he⟩ := Option.map_eq_some_iff.mp (by split at hs <;> first | exact hs | cases hs)
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact .inr ⟨t', rfl, bnd_readByte K h hr⟩
  all_goals repeat' first
    | exact hb _ _ _ _ h hs
    | exact hb _ _ _ _ (by exact ⟨h.views, h.regs⟩) hs
    | (simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs; exact .inl rfl)
    | (cases hs; done)
    | split at hs

end Kernel

/-! ## The thread's silent and runtime-load rows keep the one-thread invariant -/

section Rows

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory} {tid : Nat}
  {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}

/-- **An instruction that keeps memory and promises keeps `Inv1`** (the
cover by `stepOne_cohP`). -/
theorem inv1_of_step (h : Inv1 Λ lbl lsize ts t tm sm) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem = tm) (hp : o.thread.prom = t.prom) : Inv1 Λ lbl lsize ts o.thread o.mem sm :=
  ⟨by rw [hm, hp]; exact h.mem, stepOne_cohP A hstep ho h.coh, hm ▸ h.narrow⟩

/-- **The silent row** (`Out.silent`, `Out.choice`): memory and promises
unchanged, the thread at a leaf, `Inv1` kept. -/
theorem inv1_silent (h : Inv1 Λ lbl lsize ts t tm sm) {tree : EvTree I.State} {P : I.State → Prop}
    (hex : I.exec t.st = some tree) (hs : SilentTree P tree) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) :
    o.mem = tm ∧ o.thread.prom = t.prom ∧ P o.thread.st ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨s, hP, hth, hm⟩ := stepOne_silent_ok A tid hex hs ⟨outs, o, hstep, ho, rfl, rfl⟩
  have hp := (finishInstr_relKey hth).1
  exact ⟨hm, hp, (finishInstr_st hth) ▸ hP, inv1_of_step h hstep ho hm hp⟩

/-- **The runtime-load row** (`Out.rtLoad`): a load of any location leaves
memory and promises alone and continues with some value; `Inv1` kept. -/
theorem inv1_rtLoad (h : Inv1 Λ lbl lsize ts t tm sm) {kl : Kraken.LoadKind} {xcl : Bool} {L : Loc} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl L fun v => .done (g v))) (hstep : stepOne A t tid tm = some outs)
    (ho : .ok o ∈ outs) :
    o.mem = tm ∧ o.thread.prom = t.prom ∧ (∃ v, o.thread.st = g v) ∧ Inv1 Λ lbl lsize ts o.thread o.mem sm := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts1, v, hx, rfl⟩ := hr
  have hmem : c'.mem = tm := by
    obtain ⟨-, -, -, he⟩ := readSuccs_shape A _ hx
    have := congrArg Ctx.mem he; exact this
  have hp : o.thread.prom = t.prom := (finishInstr_relKey hth).1.trans (readSuccs_prom A _ hx)
  have hm' : o.mem = tm := hm.trans hmem
  exact ⟨hm', hp, ⟨v, finishInstr_st hth⟩, inv1_of_step h hstep ho hm' hp⟩

/-- **An instruction step ends at a leaf of its tree.** -/
theorem stepOne_treeLeaf {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hstep : stepOne A t tid tm = some outs) (ho : .ok o ∈ outs) : TreeLeaf tree o.thread.st := by
  unfold stepOne at hstep
  change (I.exec t.st).bind _ = _ at hstep
  rw [hex] at hstep
  have hstep' : _ = outs := Option.some.inj hstep
  subst hstep'
  rw [List.mem_flatMap] at ho
  obtain ⟨r, hr, ho⟩ := ho
  cases r with
  | error m => simp at ho
  | ok q =>
    obtain ⟨st, c'⟩ := q
    simp only [List.mem_map, Except.ok.injEq] at ho
    obtain ⟨th, hth, rfl⟩ := ho
    show TreeLeaf tree th.st
    rw [finishInstr_st hth]
    exact runTree_treeLeaf A tid _ tree _ st c' hr

end Rows

/-! ## A step of the canonical machine keeps the one-thread invariant -/

section Machine

variable {n : Nat} {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)}
  {pcf : I.State → Nat} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {sm : WeakMem.Memory}

/-- **The cases of a step of thread `tid` of the canonical machine** that is
neither a spawn nor a range transfer, from a thread in a state of an
invariant `P` of the ISA's `exec` whose trees write words only, closed under
the solo leaves (`hL`; so `P` is an invariant of `Kernel.soloExec`, which
writes words only: `Kernel.soloExec_wideInv`, `Kernel.soloExec_wide8CodeOn`),
under `Inv1`:

- an instruction off a system call: one `stepOne` outcome, the kernel state
  unchanged, and the thread in `P` (the per-row lemmas of `Rows1` then give
  `Inv1` from the outcome);
- a promise: the promise is one word wide and `Inv1` holds after it
  (`Inv1.promise_cert_on`); the thread's state is unchanged;
- a kernel step (`inv1_sysStep`; `sysStep_wideInv` for `P`).

A range transfer is excluded at the transfer sites (`hxf`; `Step.xfer`
happens only there). -/
theorem step_cases_of {K : Kernel.Abi I} {P : I.State → Prop} (hW : Wide8CodeOn P I.exec)
    (hP : WideInv P I.exec) (hL : ∀ s s', P s → Kernel.SoloLeaf K s s' → P s') {μ : Marks} {tid : Nat}
    {es : List Ev}
    {c c' : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hst : P t.st) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Step μ tid c es c')
    (hsp : ¬ (Kernel.hooks K A n).spawn μ tid c c')
    (hxf : ∀ k, (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).AtSite μ k c tid →
      ¬ (Kernel.hooks K A n).xfer k tid c c') :
    (es = [] ∧ K.atSys t.st = false ∧ ∃ outs o, stepOne A t tid c.1.mem = some outs ∧ .ok o ∈ outs ∧
        c' = (c.1.withThread tid o.thread o.mem, c.2) ∧ P o.thread.st ∧
        CertOkC A (Kernel.certSem K A μ c.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w, c' = (c.1.withThread tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1, c.2) ∧
        Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 sm ∧
        CertOkC A (Kernel.certSem K A μ c.2 tid) tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 ∧
        w.tid = tid) ∨
      (∃ p, Kernel.sysStep K A tid c p = some (es, c') ∧ Kernel.CertAfter K A μ tid c' ∧
        (c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm)) := by
  cases hs with
  | instr _ hna _ hstep =>
    have hns : K.atSys t.st = false := by
      cases hk : K.atSys t.st
      · rfl
      · exact absurd ⟨t, ht, hk⟩ hna
    rcases hstep with ⟨t', outs, o, ht', hso, ho, hco, rfl⟩ | ⟨t', w, ht', hwt, hc, rfl⟩
    · rw [ht] at ht'
      cases ht'
      obtain ⟨tree, hE⟩ : ∃ tree, I.exec t.st = some tree := by
        cases hE : I.exec t.st with
        | none =>
          unfold stepOne at hso
          change (I.exec t.st).bind _ = _ at hso
          rw [hE] at hso
          cases hso
        | some tree => exact ⟨tree, rfl⟩
      exact .inl ⟨rfl, hns, outs, o, hso, ho, rfl, hP _ _ _ hst hE (stepOne_treeLeaf hE hso ho), hco⟩
    · rw [ht] at ht'
      cases ht'
      exact .inr (.inl ⟨rfl, w, rfl,
        h.promise_cert_on (Kernel.soloExec_wide8CodeOn hW) (Kernel.soloExec_wideInv hP hL) hst hc, hc, hwt⟩)
  | spawn _ h => exact absurd h hsp
  | sys _ hsy _ _ _ =>
    obtain ⟨p, hp, hca⟩ := hsy
    exact .inr (.inr ⟨p, hp, hca, inv1_sysStep K ht h hp⟩)
  | xfer k _ hs h => exact absurd h (hxf k hs)

/-- `step_cases_of` for a step that is no range transfer (`hxf`). -/
theorem step_cases {K : Kernel.Abi I} {P : I.State → Prop} (hW : Wide8CodeOn P I.exec)
    (hP : WideInv P I.exec) (hL : ∀ s s', P s → Kernel.SoloLeaf K s s' → P s') {μ : Marks} {tid : Nat}
    {es : List Ev}
    {c c' : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Cfg} {t : Thread I}
    (ht : c.1.threads[tid]? = some t) (hst : P t.st) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : (ExtMachine.ofHooks I A (Kernel.hooks K A n) rv pl pcf).Step μ tid c es c')
    (hsp : ¬ (Kernel.hooks K A n).spawn μ tid c c') (hxf : ∀ k, ¬ (Kernel.hooks K A n).xfer k tid c c') :
    (es = [] ∧ K.atSys t.st = false ∧ ∃ outs o, stepOne A t tid c.1.mem = some outs ∧ .ok o ∈ outs ∧
        c' = (c.1.withThread tid o.thread o.mem, c.2) ∧ P o.thread.st ∧
        CertOkC A (Kernel.certSem K A μ c.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w, c' = (c.1.withThread tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1, c.2) ∧
        Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 sm ∧
        CertOkC A (Kernel.certSem K A μ c.2 tid) tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 ∧
        w.tid = tid) ∨
      (∃ p, Kernel.sysStep K A tid c p = some (es, c') ∧ Kernel.CertAfter K A μ tid c' ∧
        (c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm)) :=
  step_cases_of hW hP hL ht hst h hs hsp fun k _ => hxf k

end Machine

end Spike.Lib.ExtThread
