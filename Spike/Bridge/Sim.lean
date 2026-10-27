/-
The bridge spike, ISA-independent half: the relation `Rel` between Kraken
configurations and WeakCore configurations for the two-thread release/acquire
program, the simulation step (`sim_step`, every `StepSemInf` step matched by
one `TermRun.Step`, promise steps included), reachability (`reach`) and the
`Sim.sim` clause of `Scc.Sem.Sim` for `Target.ofBase` (`sim_clause`).

Everything here is stated for an arbitrary ISA and memory model, over a
`Shape`: the event trees of the two instructions (a non-exclusive store of a
value `v1` with `v1.toNat = 1` to the 8-byte flag `⟨F, 8⟩`, then nothing; a
non-exclusive load of the flag, then nothing). `Spike/Bridge/A64.lean` and
`Spike/Bridge/X64.lean` discharge `Shape` for the parsed `stlr`/`ldar` and
`movq` programs from the per-row `exec` lemmas of `Kraken.Promising.Lower`.

The relation:

* threads: Kraken thread `i` is source thread `i` (`i < 2`);
* memory: `MemRel` (identity timestamp map; every Kraken message is a write
  of `v1` to the flag);
* writer phase (`WPhase`): before its store the Kraken thread is at `st0`
  and the source thread is `writerAt P` with the same promise set `P`;
  after it, at `sW` and `writerDone vs P`; every promise is a timestamp of
  memory (`PromOK`);
* reader phase (`RPhase`): no promises; before its load at `st1` and
  `reader0`; after it at `fR v` and `readerDone vs w u` with `w` the source
  value `num v.toNat`, `v` being `0` or `v1`.

Promise certification is by lockstep (`certified_of_certOk`): the
per-thread relations `TRw`, `TRr` are preserved by every promise-free solo
step (`writer_sim`, `reader_sim`), so the Kraken certification run that
`InstrSemInf`/`PromSemInf` carry is replayed as a source `Solo` run.
A Kraken promise is only certifiable if it is the writer's own store
(`certW_pre_shape`), so its source counterpart is the promise of
`num 1` to the flag, at the same timestamp.

The rest of `Scc.Sem.Sim`:

* `components`: every related pair satisfies `Components` with `witness`
  (thread `i ↦ i`, label `0 ↦ F`, identity timestamps, `f ↦ rF`,
  `r ↦ rR`), given where the registers hold the source words (`Regs`) and
  a layout with the flag in `data` (`FlagIn`);
* `correct_of_progress`: `Correct` for `Target.ofBase` and
  `SrcSem.ofStep prog k arch (· = srcInit)`, every clause discharged but
  progress, which is a hypothesis about the target alone.
-/
import Spike.Bridge.Common
import Kraken.Promising.Lower.Events

namespace Spike.Bridge

open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf
open Scc.Sem (SrcSem ExtMachine Target obs)

/-! ## The instruction shapes -/

/-- **The writer's event tree**: at `st0` one non-exclusive store of `v1`
(with `v1.toNat = 1`) to `⟨F, 8⟩`, then at `sW` with no next instruction.
The writer's half of `Shape`, shared with the spinning reader's variant
(`Spike/Bridge/Loop.lean`). -/
structure WShape (I : ISA) (F : BitVec 64) (v1 : Val) (st0 sW : I.State) : Prop where
  wr : ∃ ks, I.exec st0 = some (.store ks false ⟨F, 8⟩ v1 fun _ => .done sW)
  wd : I.exec sW = none
  one : v1.toNat = 1

/-- **The two instructions' event trees.** The writer at `st0` performs one
non-exclusive store of `v1` to `⟨F, 8⟩` and is then at `sW`, with no next
instruction; the reader at `st1` performs one non-exclusive load of
`⟨F, 8⟩` and is then at `fR v` for the value `v` read, with no next
instruction. The store and load kinds are free (release/acquire on AArch64,
plain on x64). -/
structure Shape (I : ISA) (F : BitVec 64) (v1 : Val) (st0 sW st1 : I.State) (fR : Val → I.State) : Prop
    extends WShape I F v1 st0 sW where
  rd : ∃ kl, I.exec st1 = some (.load kl false ⟨F, 8⟩ fun v => .done (fR v))
  rdd : ∀ v, I.exec (fR v) = none

section Gen

variable {I : ISA} (A : Arch) {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {fR : Val → I.State}

/-! ## One Kraken step of each thread -/

/-- A thread with no next instruction takes no solo step. -/
theorem no_threadStep {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory}
    (hex : I.exec t.st = none) : ¬ ThreadStep A tid (t, mem) q := by
  rintro ⟨outs, o, hs, -, -⟩
  simp [stepOne, hex] at hs

/-- A promise-free solo run of a thread with no next instruction is empty. -/
theorem threadNP_halted {tid : Nat} {q r : Thread I × Memory} (hex : I.exec q.1.st = none)
    (h : ThreadNP A tid q r) : r = q := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (no_threadStep A hex)

/-- A certifiable thread with no next instruction has no promise. -/
theorem cert_halted {tid : Nat} {t : Thread I} {mem : Memory} (hex : I.exec t.st = none)
    (hc : CertOk A tid t mem) : t.prom = [] := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  obtain ⟨rfl, -⟩ := Prod.mk.inj (threadNP_halted A (q := (t, mem)) hex hrun)
  exact hp

section W

variable (hWS : WShape I F v1 st0 sW)
include hWS

/-- **The writer's step** (Kraken side): it ends at `sW`, and either fulfils
an outstanding promise `p` of the message `⟨F, 8⟩ := v1` (memory unchanged,
`p` discharged), or promises now at `|M| + 1` (the message appended, the
promise set `(P ++ [|M| + 1]).erase (|M| + 1)`). -/
theorem writer_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} (ht : t.st = st0)
    (h : ThreadStep A tid (t, mem) q) :
    q.1.st = sW ∧
      ((∃ p ∈ t.prom, mem.get? p = some ⟨⟨F, 8⟩, v1, tid⟩ ∧ q.1.prom = t.prom.erase p ∧ q.2 = mem) ∨
       (q.1.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
          q.2 = (mem.append ⟨⟨F, 8⟩, v1, tid⟩).1)) := by
  obtain ⟨ks, hw⟩ := hWS.wr
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  have hex : I.exec t.st = some _ := ht ▸ hw
  obtain ⟨st, c', hr, hth, hm⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  rw [run_store_iff] at hr
  obtain ⟨rfl, hc'⟩ := hr
  have hst := finishInstr_st hth
  have hpr := (finishInstr_relKey hth).1
  refine ⟨hst, ?_⟩
  rw [mem_writeSuccs_iff] at hc'
  rcases hc' with ⟨p, hp, hg, -, rfl⟩ | ⟨-, rfl⟩
  · exact .inl ⟨p, hp, hg, hpr, hm⟩
  · exact .inr ⟨hpr, hm⟩

/-! ## Certification on the Kraken side -/

/-- **A certifiable writer before its store** has no promise, or exactly
one, of its own store's message. -/
theorem certW_pre_shape {tid : Nat} {t : Thread I} {mem : Memory} (ht : t.st = st0)
    (hc : CertOk A tid t mem) :
    t.prom = [] ∨ ∃ p, t.prom = [p] ∧ mem.get? p = some ⟨⟨F, 8⟩, v1, tid⟩ := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  cases hrun with
  | refl => exact .inl hp
  | step hs hrest =>
    rename_i q
    obtain ⟨hst, hq⟩ := writer_out A hWS ht hs
    have hex : I.exec q.1.st = none := hst ▸ hWS.wd
    obtain rfl := threadNP_halted A hex hrest
    rcases hq with ⟨p, hpm, hg, hpr, -⟩ | ⟨hpr, -⟩
    · rw [hp] at hpr
      have hl := congrArg List.length hpr
      rw [List.length_erase_of_mem hpm] at hl
      have h1 := List.length_pos_of_mem hpm
      simp only [List.length_nil] at hl
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (by omega : t.prom.length = 1)
      rw [hx] at hpm
      obtain rfl := List.mem_singleton.mp hpm
      exact .inr ⟨p, hx, hg⟩
    · rw [hp] at hpr
      have hl := congrArg List.length hpr
      rw [List.length_erase_of_mem (by simp)] at hl
      simp at hl
      exact .inl (List.length_eq_zero_iff.mp hl.symm)

end W

variable (hS : Shape I F v1 st0 sW st1 fR)
include hS

/-- **The reader's step** (Kraken side): memory and promises unchanged, the
thread at `fR v` for a value `v` that a read of the flag at some timestamp
returns. -/
theorem reader_out {tid : Nat} {t : Thread I} {mem : Memory} {q : Thread I × Memory} (ht : t.st = st1)
    (h : ThreadStep A tid (t, mem) q) :
    q.2 = mem ∧ q.1.prom = t.prom ∧ ∃ ts v, q.1.st = fR v ∧ mem.read? ⟨F, 8⟩ ts = some v := by
  obtain ⟨kl, hr⟩ := hS.rd
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  have hex : I.exec t.st = some _ := ht ▸ hr
  obtain ⟨st, c', hrun, hth, hm⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
  rw [run_load_iff] at hrun
  obtain ⟨ts, v, hx, rfl⟩ := hrun
  have hp := readSuccs_prom A _ hx
  obtain ⟨ts', v', he, -, hv, -, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨hm, (finishInstr_relKey hth).1.trans hp, ts, v, finishInstr_st hth, hv⟩

/-- **A reader before its load is certifiable only without promises**: its
load keeps the promise set, and it then has no next instruction. -/
theorem certR_pre {tid : Nat} {t : Thread I} {mem : Memory} (ht : t.st = st1) (hc : CertOk A tid t mem) :
    t.prom = [] := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  cases hrun with
  | refl => exact hp
  | step hs hrest =>
    rename_i q
    obtain ⟨-, hpr, ts, v, hst, -⟩ := reader_out A hS ht hs
    have hex : I.exec q.1.st = none := hst ▸ hS.rdd v
    obtain rfl := threadNP_halted A hex hrest
    exact hpr ▸ hp

end Gen

/-! ## The relation -/

section Rel

variable {I : ISA} {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {fR : Val → I.State}

/-- **The writer's phase**: before its store (Kraken at `st0`, source
`writerAt P`) or after it (Kraken at `sW`, source `writerDone vs P`), with
the same promise set `P` on both sides. -/
def WPhase (st0 sW : I.State) (t : Thread I) (th : TermRun.TTh) : Prop :=
  (t.st = st0 ∧ th = writerAt t.prom) ∨ (t.st = sW ∧ ∃ vs, th = writerDone vs t.prom)

/-- **The reader's phase**: no promises; before its load (Kraken at `st1`,
source `reader0`) or after it (Kraken at `fR v`, source `readerDone vs w u`
with `w` the source value of `v`; `v` is the initial `0` or `v1`). -/
def RPhase (v1 : Val) (st1 : I.State) (fR : Val → I.State) (t : Thread I) (th : TermRun.TTh) : Prop :=
  t.prom = [] ∧ ((t.st = st1 ∧ th = reader0) ∨
    ∃ v w vs u, t.st = fR v ∧ th = readerDone vs w u ∧ w.val = .num v.toNat ∧ (v = 0 ∨ v = v1))

/-- Every promise is a timestamp of memory. -/
def PromOK (t : Thread I) (mem : Memory) : Prop := ∀ p ∈ t.prom, p ≤ mem.last

theorem WPhase.promises {t : Thread I} {th : TermRun.TTh} (h : WPhase st0 sW t th) : th.promises = t.prom := by
  rcases h with ⟨-, rfl⟩ | ⟨-, vs, rfl⟩ <;> rfl

theorem RPhase.promises {t : Thread I} {th : TermRun.TTh} (h : RPhase v1 st1 fR t th) : th.promises = [] := by
  rcases h with ⟨-, ⟨-, rfl⟩ | ⟨v, w, vs, u, -, rfl, -⟩⟩ <;> rfl

/-- **The relation** between a Kraken configuration and a source
configuration: two threads on each side, thread `i` related to thread `i`
by its phase, and the memories related by `MemRel`. -/
def Rel (F : BitVec 64) (v1 : Val) (st0 sW st1 : I.State) (fR : Val → I.State) (c : Config I)
    (s : TermRun.Cfg) : Prop :=
  ∃ t0 t1 th0 th1, c.threads = #[t0, t1] ∧ s.ths = #[th0, th1] ∧ WPhase st0 sW t0 th0 ∧ PromOK t0 c.mem ∧
    RPhase v1 st1 fR t1 th1 ∧ MemRel F (· = v1) c.mem s.mem

/-- The writer's lockstep relation: the source configuration's thread `0`
in the writer's phase for the Kraken thread, promises in memory, memories
related. -/
def TRw (F : BitVec 64) (v1 : Val) (st0 sW : I.State) (q : Thread I × Memory) (s : TermRun.Cfg) : Prop :=
  ∃ th, s.ths[0]? = some th ∧ WPhase st0 sW q.1 th ∧ PromOK q.1 q.2 ∧ MemRel F (· = v1) q.2 s.mem

/-- The reader's lockstep relation. -/
def TRr (F : BitVec 64) (v1 : Val) (st1 : I.State) (fR : Val → I.State) (q : Thread I × Memory)
    (s : TermRun.Cfg) : Prop :=
  ∃ th, s.ths[1]? = some th ∧ RPhase v1 st1 fR q.1 th ∧ MemRel F (· = v1) q.2 s.mem

/-- A Kraken read of the flag returns the initial `0` or `v1`. -/
theorem MemRel.read_val {km : Memory} {sm : WeakMem.Memory} (h : MemRel F (· = v1) km sm) {t : Nat}
    {v : Val} (hr : km.read? ⟨F, 8⟩ t = some v) : v = 0 ∨ v = v1 := by
  unfold Memory.read? at hr
  split at hr
  · left
    simp [Memory.initVal, h.init] at hr
    exact hr.symm
  · cases hg : km.get? t with
    | none => rw [hg] at hr; cases hr
    | some w =>
      rw [hg] at hr
      simp only at hr
      split at hr
      · cases hr
        exact .inr (h.get hg).2.1
      · cases hr

theorem getElem?_set!_self {α : Type} {a : Array α} {i : Nat} {y : α} (h : a[i]? = some y) (x : α) :
    (a.set! i x)[i]? = some x := by
  have hi : i < a.size := by
    rcases Nat.lt_or_ge i a.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at h
  simp [hi]

end Rel

/-! ## One source step per Kraken step -/

section Steps

variable {I : ISA} (A : Arch) {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {fR : Val → I.State}
  {k : Promises.Knobs} {arch : WeakMem.Arch} {pr : CoreTerm.Prog}

section W

variable (hWS : WShape I F v1 st0 sW)
include hWS

/-- **The writer's simulation step**: a promise-free solo step of Kraken
thread `0` from a related pair is a thread step of source thread `0` (the
store appending, or fulfilling the same promise), to a related pair. -/
theorem writer_sim {s : TermRun.Cfg} {th : TermRun.TTh} (h0 : s.ths[0]? = some th) {t : Thread I}
    {mem : Memory} {q : Thread I × Memory} (hW : WPhase st0 sW t th) (hP : PromOK t mem)
    (hM : MemRel F (· = v1) mem s.mem) (h : ThreadStep A 0 (t, mem) q) :
    ∃ sm th', { s with mem := sm, ths := s.ths.set! 0 th' } ∈ TermRun.threadSteps pr k arch s 0 ∧
      WPhase st0 sW q.1 th' ∧ PromOK q.1 q.2 ∧ MemRel F (· = v1) q.2 sm ∧
      (sm = s.mem ∨ sm = s.mem.push ⟨flagA, .num 1, 0⟩) := by
  rcases hW with ⟨hst, rfl⟩ | ⟨hst, vs, rfl⟩
  · obtain ⟨hst', hq⟩ := writer_out A hWS hst h
    rcases hq with ⟨p, hpm, hg, hpr, hm⟩ | ⟨hpr, hm⟩
    · obtain ⟨-, hv, hp0, vw, hsm⟩ := hM.get hg
      simp only at hv
      rw [hWS.one] at hsm
      obtain ⟨vs, hstep⟩ := writer_fulfil (k := k) (arch := arch) s t.prom h0 hpm hp0 hsm
      refine ⟨s.mem, _, hstep, .inr ⟨hst', vs, by rw [hpr]⟩, ?_, hm ▸ hM, .inl rfl⟩
      intro x hx
      rw [hpr] at hx
      rw [hm]
      exact hP x (List.mem_of_mem_erase hx)
    · have hn : mem.last + 1 ∉ t.prom := fun hx => absurd (hP _ hx) (Nat.not_succ_le_self _)
      have hpr' : q.1.prom = t.prom := by rw [hpr]; simp [List.erase_append_right _ hn]
      obtain ⟨vs, hstep⟩ := writer_append (k := k) (arch := arch) s t.prom h0
      refine ⟨_, _, hstep, .inr ⟨hst', vs, by rw [hpr']⟩, ?_, ?_, .inr rfl⟩
      · intro x hx
        rw [hpr'] at hx
        rw [hm]
        show x ≤ (mem.msgs.push _).size
        rw [Array.size_push]
        exact Nat.le_succ_of_le (hP x hx)
      · rw [hm]
        have := hM.push (w := ⟨⟨F, 8⟩, v1, 0⟩) rfl rfl 0
        rwa [hWS.one] at this
  · exact absurd h (no_threadStep A (hst ▸ hWS.wd))

/-- **Lockstep certification of the writer**: a Kraken certification of
thread `0` from a `TRw`-related pair is a WeakCore certification of source
thread `0`. -/
theorem certW {t : Thread I} {mem : Memory} {s : TermRun.Cfg} (h : TRw F v1 st0 sW (t, mem) s)
    (hc : CertOk A 0 t mem) : TermRun.Certified pr k arch s 0 := by
  refine certified_of_certOk (TRw F v1 st0 sW) ?_ ?_ h hc
  · rintro q q' s ⟨th, h0, hW, hP, hM⟩ hs
    obtain ⟨sm, th', hstep, hW', hP', hM', -⟩ := writer_sim A hWS h0 hW hP hM hs
    exact ⟨_, hstep, th', getElem?_set!_self h0 th', hW', hP', hM'⟩
  · rintro q s ⟨th, h0, hW, -, -⟩ hp
    simp [TermRun.noPromises, h0, hW.promises, hp]

/-- **The writer's promise step.** A certifiable Kraken promise of thread
`0` from a related writer is of its own store's message (`certW_pre_shape`:
the writer before its store, with no promise yet; after its store it
certifies only with none, `cert_halted`). Its source counterpart promises
`num 1` to the flag with message view `0`, at the same timestamp (the
source's memory size is Kraken's `last + 1`), certified by lockstep from
the `CertOk` of the Kraken promise. -/
theorem writer_prom {s : TermRun.Cfg} {th0 : TermRun.TTh} (h0 : s.ths[0]? = some th0) {t0 : Thread I}
    {mem : Memory} {w : Msg} (hW : WPhase st0 sW t0 th0) (hM : MemRel F (· = v1) mem s.mem)
    (hcert : CertOk A 0 (promThread t0 mem w) (mem.append w).1) :
    w = ⟨⟨F, 8⟩, v1, 0⟩ ∧ ∃ th0', SrcSem.StepBy pr k arch 0 s (TermRun.promise s 0 flagA (.num 1) 0) ∧
      TermRun.promise s 0 flagA (.num 1) 0 =
        { s with mem := s.mem.push ⟨flagA, .num 1, 0⟩, ths := s.ths.set! 0 th0' } ∧
      WPhase st0 sW (promThread t0 mem w) th0' ∧ PromOK (promThread t0 mem w) (mem.append w).1 ∧
      MemRel F (· = v1) (mem.append w).1 (s.mem.push ⟨flagA, .num 1, 0⟩) := by
  rcases hW with ⟨hst0, rfl⟩ | ⟨hst0, vs, rfl⟩
  · rcases certW_pre_shape A hWS (t := promThread t0 mem w) hst0 hcert with hnil | ⟨p, hp1, hg⟩
    · simp at hnil
    · have hP0 : t0.prom = [] := by
        have hl := congrArg List.length hp1
        simp only [List.length_append, List.length_singleton] at hl
        exact List.length_eq_zero_iff.mp (by omega)
      have hpe : (mem.append w).2 = p := by
        have := hp1
        simp only [hP0, List.nil_append, List.cons.injEq] at this
        exact this.1
      subst hpe
      have hgw : (mem.append w).1.get? (mem.append w).2 = some w := by
        simp [Memory.append, Memory.get?]
      obtain rfl : w = ⟨⟨F, 8⟩, v1, 0⟩ := Option.some.inj (hgw.symm.trans hg)
      have hs' : TermRun.promise s 0 flagA (.num 1) 0 =
          { s with mem := s.mem.push ⟨flagA, .num 1, 0⟩, ths := s.ths.set! 0 (writerAt [s.mem.size]) } := by
        rw [promise_eq s h0, hP0]; rfl
      have hW' : WPhase st0 sW (promThread t0 mem ⟨⟨F, 8⟩, v1, 0⟩) (writerAt [s.mem.size]) := by
        refine .inl ⟨hst0, ?_⟩
        simp [hP0, hM.size, Memory.append]
      have hP' : PromOK (promThread t0 mem ⟨⟨F, 8⟩, v1, 0⟩) (mem.append ⟨⟨F, 8⟩, v1, 0⟩).1 := by
        intro x hx
        simp only [hP0, List.nil_append, List.mem_singleton, Memory.append] at hx
        subst hx
        show _ ≤ (mem.msgs.push _).size
        rw [Array.size_push]
        exact Nat.le_refl _
      have hM' : MemRel F (· = v1) (mem.append ⟨⟨F, 8⟩, v1, 0⟩).1 (s.mem.push ⟨flagA, .num 1, 0⟩) := by
        have := hM.push (w := ⟨⟨F, 8⟩, v1, 0⟩) rfl rfl 0
        rwa [hWS.one] at this
      have hcs : TermRun.Certified pr k arch (TermRun.promise s 0 flagA (.num 1) 0) 0 := by
        rw [hs']
        exact certW A hWS ⟨_, getElem?_set!_self h0 _, hW', hP', hM'⟩ hcert
      refine ⟨rfl, _, .inr ⟨flagA, .num 1, 0, (Array.getElem?_eq_some_iff.mp h0).1, by rw [hM.size]; omega, hcs, rfl⟩,
        hs', hW', hP', hM'⟩
  · have := cert_halted A (hst0 ▸ hWS.wd) hcert
    simp at this

end W

variable (hS : Shape I F v1 st0 sW st1 fR)
include hS

/-- **The reader's simulation step**: a promise-free solo step of Kraken
thread `1` from a related pair leaves memory alone and is a thread step of
source thread `1` (the load of the message at the same timestamp), to a
related pair. -/
theorem reader_sim {s : TermRun.Cfg} {th : TermRun.TTh} (h1 : s.ths[1]? = some th) {t : Thread I}
    {mem : Memory} {q : Thread I × Memory} (hR : RPhase v1 st1 fR t th) (hM : MemRel F (· = v1) mem s.mem)
    (h : ThreadStep A 1 (t, mem) q) :
    q.2 = mem ∧ ∃ th', { s with ths := s.ths.set! 1 th' } ∈ TermRun.threadSteps prog k arch s 1 ∧
      RPhase v1 st1 fR q.1 th' := by
  obtain ⟨hp, hR⟩ := hR
  rcases hR with ⟨hst, rfl⟩ | ⟨v, w, vs, u, hst, rfl, -⟩
  · obtain ⟨hm, hpr, ts, v, hst', hr⟩ := reader_out A hS hst h
    obtain ⟨m, hsm, hl, hval⟩ := hM.read hr
    obtain ⟨vs, u, hstep⟩ := reader_read (k := k) (arch := arch) s h1 hsm hl
    exact ⟨hm, _, hstep, hpr.trans hp, .inr ⟨v, _, vs, u, hst', rfl, hval, hM.read_val hr⟩⟩
  · exact absurd h (no_threadStep A (hst ▸ hS.rdd v))

/-- **Lockstep certification of the reader.** -/
theorem certR {t : Thread I} {mem : Memory} {s : TermRun.Cfg} (h : TRr F v1 st1 fR (t, mem) s)
    (hc : CertOk A 1 t mem) : TermRun.Certified prog k arch s 1 := by
  refine certified_of_certOk (TRr F v1 st1 fR) ?_ ?_ h hc
  · rintro q q' s ⟨th, h1, hR, hM⟩ hs
    obtain ⟨hm, th', hstep, hR'⟩ := reader_sim A hS h1 hR hM hs
    exact ⟨_, hstep, th', getElem?_set!_self h1 th', hR', hm ▸ hM⟩
  · rintro q s ⟨th, h1, hR, -⟩ -
    simp [TermRun.noPromises, h1, hR.promises]

/-- **The simulation step.** Every fuel-free step of Kraken thread `tid`
(an instruction step or a promise step, each carrying its certification)
from a related pair is one step of source thread `tid` (a thread step or a
promise, each certified by lockstep) to a related pair. A Kraken promise
from a related configuration is certifiable only when it is the writer's
first, of its own store's message (`certW_pre_shape`, `certR_pre`,
`cert_halted`); its source counterpart promises `num 1` to the flag with
message view `0`, at the same timestamp. -/
theorem sim_step {c c' : Config I} {s : TermRun.Cfg} {tid : Nat} (hR : Rel F v1 st0 sW st1 fR c s)
    (h : StepSemInf A tid c c') :
    ∃ s', SrcSem.StepBy prog k arch tid s s' ∧ Rel F v1 st0 sW st1 fR c' s' := by
  obtain ⟨t0, t1, th0, th1, hc, hs, hW, hP, hRd, hM⟩ := hR
  have h0 : s.ths[0]? = some th0 := by rw [hs]; rfl
  have h1 : s.ths[1]? = some th1 := by rw [hs]; rfl
  rcases h with ⟨t, outs, o, ht, hst, ho, hcert, rfl⟩ | ⟨t, w, ht, hw, hcert, rfl⟩
  · rw [hc] at ht
    have hts : ThreadStep A tid (t, c.mem) (o.thread, o.mem) := ⟨outs, o, hst, ho, rfl⟩
    match tid, ht, hts, hcert with
    | 0, ht, hts, hcert =>
      change some t0 = some t at ht
      cases ht
      obtain ⟨sm, th', hstep, hW', hP', hM', -⟩ := writer_sim A hS.toWShape h0 hW hP hM hts
      refine ⟨_, .inl ⟨hstep, certW A hS.toWShape ⟨th', getElem?_set!_self h0 th', hW', hP', hM'⟩ hcert⟩, ?_⟩
      refine ⟨o.thread, t1, th', th1, ?_, ?_, hW', hP', hRd, hM'⟩
      · show c.threads.set! 0 o.thread = _
        rw [hc]; rfl
      · show s.ths.set! 0 th' = _
        rw [hs]; rfl
    | 1, ht, hts, hcert =>
      change some t1 = some t at ht
      cases ht
      obtain ⟨hm, th', hstep, hRd'⟩ := reader_sim A hS h1 hRd hM hts
      refine ⟨_, .inl ⟨hstep, certR A hS ⟨th', getElem?_set!_self h1 th', hRd', hm ▸ hM⟩ hcert⟩, ?_⟩
      have hm' : o.mem = c.mem := hm
      refine ⟨t0, o.thread, th0, th', ?_, ?_, hW, ?_, hRd', ?_⟩
      · show c.threads.set! 1 o.thread = _
        rw [hc]; rfl
      · show s.ths.set! 1 th' = _
        rw [hs]; rfl
      · show PromOK t0 o.mem
        rw [hm']; exact hP
      · show MemRel F (· = v1) o.mem s.mem
        rw [hm']; exact hM
    | n + 2, ht, _, _ => simp at ht
  · rw [hc] at ht
    match tid, ht, hw, hcert with
    | 0, ht, hw, hcert =>
      change some t0 = some t at ht
      cases ht
      obtain ⟨-, th0', hb, hpe, hW', hP', hM'⟩ := writer_prom A hS.toWShape h0 hW hM hcert
      refine ⟨_, hb, ?_⟩
      rw [hpe]
      refine ⟨promThread t0 c.mem w, t1, th0', th1, ?_, ?_, hW', hP', hRd, hM'⟩
      · show c.threads.set! 0 _ = _
        rw [hc]; rfl
      · show s.ths.set! 0 _ = _
        rw [hs]; rfl
    | 1, ht, hw, hcert =>
      change some t1 = some t at ht
      cases ht
      obtain ⟨-, ⟨hst1, -⟩ | ⟨v, -, -, -, hst1, -⟩⟩ := hRd
      · have := certR_pre A hS (t := promThread t1 c.mem w) hst1 hcert
        simp at this
      · have := cert_halted A (hst1 ▸ hS.rdd v) hcert
        simp at this
    | n + 2, ht, _, _ => simp at ht

omit hS in
/-- The start configurations are related: Kraken's `Config.init` of the two
start states and the flag's initial write, and `srcInit`. -/
theorem rel_init :
    Rel F v1 st0 sW st1 fR (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) srcInit :=
  ⟨Thread.init st0, Thread.init st1, writerAt [], reader0, rfl, rfl, .inl ⟨rfl, rfl⟩,
    fun _ h => by simp [Thread.init] at h, ⟨rfl, .inl ⟨rfl, rfl⟩⟩, MemRel.start⟩

/-- **Reachability**: every fuel-free Kraken run from a related configuration
is matched by a source run with the empty trace, to a related configuration
(one source step per Kraken step). -/
theorem reach {init : TermRun.Cfg → Prop} {c c' : Config I} (h : ReachableSemInf A c c') :
    ∀ s, Rel F v1 st0 sW st1 fR c s →
      ∃ s', (SrcSem.ofStep prog k arch init).Run s [] s' ∧ Rel F v1 st0 sW st1 fR c' s' := by
  induction h with
  | refl => intro s hs; exact ⟨s, .refl s, hs⟩
  | step tid hst _ ih =>
    intro s hs
    obtain ⟨s1, hb, h1⟩ := sim_step A hS hs hst
    obtain ⟨s', hr, h'⟩ := ih s1 h1
    exact ⟨s', Scc.Sem.LRun.step (es := []) (tr := []) ⟨tid, .inl hb, rfl⟩ hr, h'⟩

/-- **The `Sim.sim` clause, with trace equality**, for the existing machine
as a target (`Target.ofBase`, any register and private-memory observations),
loading the two start states and the flag's initial write: every reachable
target configuration is related to a reachable source configuration whose
trace is exactly the observable target trace (both are empty here). -/
theorem sim_clause_eq (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64))
    (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase I A rv pl).load ([st0, st1], [(⟨F, 8⟩, 0)]) Λ = some t0 →
      (Target.ofBase I A rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep prog k arch (· = srcInit)).Reach tr' s ∧ Rel F v1 st0 sW st1 fR t.1 s ∧
        obs tr = tr' := by
  intro t0 tr t h0 hr
  cases h0
  obtain ⟨rfl, hreach⟩ := ExtMachine.ofBase_run_inv hr
  obtain ⟨s, hrun, hs⟩ := reach A hS hreach srcInit rel_init
  exact ⟨[], s, ⟨srcInit, rfl, hrun⟩, hs, rfl⟩

/-- **The `Sim.sim` clause** in the statement's form (trace prefix), with
`R t s := Rel … t.1 s`. -/
theorem sim_clause (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64))
    (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase I A rv pl).load ([st0, st1], [(⟨F, 8⟩, 0)]) Λ = some t0 →
      (Target.ofBase I A rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep prog k arch (· = srcInit)).Reach tr' s ∧ Rel F v1 st0 sW st1 fR t.1 s ∧
        obs tr <+: tr' := by
  intro t0 tr t h0 hr
  obtain ⟨tr', s, hs, hR, he⟩ := sim_clause_eq A hS (k := k) (arch := arch) rv pl Λ μ t0 tr t h0 hr
  exact ⟨tr', s, hs, hR, he ▸ List.prefix_refl _⟩

end Steps

/-! ## The components of `R` -/

section Explicit

open Scc.Sem (Witness Components ComponentsAll Place placeVal ValRep wordAddr wordLoc labelRange frameEnvs)

variable {I : ISA} {A : Arch} {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {fR : Val → I.State}
  {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)} {rF rR : I.RegId}

/-- **Where the source words live**: register `rF` holds the flag's address
in every phase of both threads, and register `rR` of the reader holds the
value read after its load (its low 64 bits). -/
structure Regs (rv : I.State → I.RegId → BitVec 64) (F : BitVec 64) (st0 sW st1 : I.State)
    (fR : Val → I.State) (rF rR : I.RegId) : Prop where
  f0 : rv st0 rF = F
  fW : rv sW rF = F
  f1 : rv st1 rF = F
  fAfter : ∀ v, rv (fR v) rF = F
  r : ∀ v, rv (fR v) rR = v.setWidth 64

/-- The layout hypotheses: no label is static (the heap-bytes fallback) and
the flag's word is aligned inside `data`. -/
structure FlagIn (Λ : Scc.Sem.Layout) (F : BitVec 64) : Prop where
  static : ∀ l, Λ.static l = none
  align : F.toNat % 8 = 0
  sub : (⟨F.toNat, 8⟩ : Scc.Sem.Range).Sub Λ.data

variable (A rv pl) in
/-- **The witness**: thread `i ↦ i` (`i < 2`), label `0 ↦ F` (one word),
timestamps unchanged, `f ↦ rF` in both threads and `r ↦ rR` in the reader
(current frame, word `0`), no stack pointers. -/
def witness (F : BitVec 64) (rF rR : I.RegId) : Witness (ExtMachine.ofBase I A rv pl) where
  thr i := if i < 2 then some i else none
  lbl l := if l = 0 then some F.toNat else none
  lsize _ := 1
  ts k := some k
  env i d x k := if d = 0 ∧ k = 0 ∧ x = "f" then some (.one (.reg rF))
    else if d = 0 ∧ k = 0 ∧ x = "r" ∧ i = 1 then some (.one (.reg rR)) else none
  marked _ _ := False
  since _ := 0
  tsFrom _ := 0

/-- The writer's frame: no stack, `f` bound, `rF` the flag's address. -/
theorem WPhase.frame (hf0 : rv st0 rF = F) (hfW : rv sW rF = F) {t : Thread I} {th : TermRun.TTh}
    (h : WPhase st0 sW t th) :
    th.stack = [] ∧ (th.env = envF ∨ th.env = ("u", .unit, []) :: envF) ∧ rv t.st rF = F := by
  rcases h with ⟨hst, rfl⟩ | ⟨hst, vs, rfl⟩
  · exact ⟨rfl, .inl rfl, hst ▸ hf0⟩
  · exact ⟨rfl, .inr rfl, hst ▸ hfW⟩

variable (rv F rF rR) in
/-- **The reader's frame**: no stack, `rF` the flag's address, and `f`
bound; or also `r` bound to a number below `2^64` held (as its low 64 bits)
in `rR`. -/
def RFrame (t : Thread I) (th : TermRun.TTh) : Prop :=
  th.stack = [] ∧ rv t.st rF = F ∧ (th.env = envF ∨ ∃ (v : Val) (w : TermRun.Word), th.env = ("r", .int, [w]) :: envF ∧
    w.val = .num v.toNat ∧ v.toNat < 2 ^ 64 ∧ rv t.st rR = v.setWidth 64)

/-- The reader's frame: no stack, `f` bound, `rF` the flag's address; after
the load `r` bound to the value in `rR`. -/
theorem RPhase.frame (hS : Shape I F v1 st0 sW st1 fR) (hRg : Regs rv F st0 sW st1 fR rF rR) {t : Thread I}
    {th : TermRun.TTh} (h : RPhase v1 st1 fR t th) : RFrame F rv rF rR t th := by
  obtain ⟨-, ⟨hst, rfl⟩ | ⟨v, w, vs, u, hst, rfl, hw, hv⟩⟩ := h
  · exact ⟨rfl, hst ▸ hRg.f1, .inl rfl⟩
  · refine ⟨rfl, hst ▸ hRg.fAfter v, .inr ⟨v, w, rfl, hw, ?_, hst ▸ hRg.r v⟩⟩
    rcases hv with rfl | rfl
    · decide
    · rw [hS.one]; decide

theorem lookup_f_envF : TermRun.lookupE envF "f" = some (fTy, [fW]) := rfl
theorem lookup_f_u : TermRun.lookupE (("u", .unit, []) :: envF) "f" = some (fTy, [fW]) := rfl
theorem lookup_f_r (w : TermRun.Word) : TermRun.lookupE (("r", .int, [w]) :: envF) "f" = some (fTy, [fW]) := rfl
theorem lookup_r_envF : TermRun.lookupE envF "r" = none := rfl
theorem lookup_r_r (w : TermRun.Word) : TermRun.lookupE (("r", .int, [w]) :: envF) "r" = some (.int, [w]) := rfl

/-- **Every word a phase's environment binds is `f`'s, or the reader's `r`'s**,
at word index `0`. -/
theorem lookup_word {e : TermRun.Env} {x : String} {ty : CoreLang.Ty} {ws : List TermRun.Word} {k : Nat}
    (he : (e = envF ∨ e = ("u", .unit, []) :: envF) ∨ (e = envF ∨ ∃ w, e = ("r", .int, [w]) :: envF))
    (hlk : TermRun.lookupE e x = some (ty, ws)) (hk : k < ws.length) :
    k = 0 ∧ (x = "f" ∨ (x = "r" ∧ ∃ w, e = ("r", .int, [w]) :: envF)) := by
  obtain ⟨⟨bx, bty, bws⟩, hb, hbe⟩ := Option.map_eq_some_iff.mp hlk
  cases hbe
  have hmem := List.mem_of_find?_eq_some hb
  have hx : (bx == x) = true := List.find?_some (p := fun y : String × CoreLang.Ty × List TermRun.Word => y.1 == x) hb
  rcases he with (rfl | rfl) | (rfl | ⟨w, rfl⟩) <;>
    simp only [envF, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem <;>
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp at hx hk <;> subst hx <;> simp_all

/-- The flag reference is represented by the flag's address. -/
theorem rep_f {st : I.State} (h : rv st rF = F) :
    ∃ v, placeVal (ExtMachine.ofBase I A rv pl) st (.reg rF) = some v ∧
      ValRep (witness A rv pl F rF rR).lbl fW.val v :=
  ⟨F.toNat, by show some (rv st rF).toNat = some F.toNat; rw [h], by
    simp [ValRep, fW, TermRun.cst, Promises.TVal.mk0, wordAddr, witness, flagA]⟩

/-- **The components hold** of every pair whose threads are the writer in a
phase of `WPhase` and a reader with frame `RFrame`, and whose memories are
related, with `witness`: the thread map, the layout injection, the value
representation on memory (timestamp by timestamp) and on the register
environments, and the stack map (vacuous: no stacks). -/
theorem components_of (hf0 : rv st0 rF = F) (hfW : rv sW rF = F) (hone : v1.toNat = 1)
    {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) {t : (ExtMachine.ofBase I A rv pl).Cfg} {s : TermRun.Cfg}
    {t0 t1 : Thread I} {th0 th1 : TermRun.TTh} (hc : t.1.threads = #[t0, t1]) (hs : s.ths = #[th0, th1])
    (hW : WPhase st0 sW t0 th0) (h1 : RFrame F rv rF rR t1 th1) (hM : MemRel F (· = v1) t.1.mem s.mem) :
    Components (ExtMachine.ofBase I A rv pl) Λ (witness A rv pl F rF rR) t s := by
  have hloc : wordLoc F.toNat = ⟨F, 8⟩ := by simp [wordLoc]
  refine ComponentsAll.scoped ?_ (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i hi
    rw [hs] at hi
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    refine ⟨i, by simp [witness, hi], ?_⟩
    rw [hc]; exact hi
  · intro i i' j h h'
    simp only [witness] at h h'
    split at h <;> split at h' <;> simp_all
  · intro j tt _ ht
    rw [hc] at ht
    have hj : j < 2 := (Array.getElem?_eq_some_iff.mp ht).1
    exact ⟨j, by rw [hs]; simpa using hj, by simp [witness, hj]⟩
  · intro l b h
    rw [hΛ.static l] at h; cases h
  · intro l b h
    simp only [witness] at h
    split at h
    · cases h
      exact ⟨hΛ.align, .inr (by simpa [labelRange, witness] using hΛ.sub)⟩
    · cases h
  · intro l l' b b' hne h h'
    simp only [witness] at h h'
    split at h <;> split at h'
    · rename_i h1 h2; exact absurd (h1.trans h2.symm) hne
    all_goals cases h <;> cases h'
  · intro m hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [Array.getElem?_toList] at hi
    have hl := hM.loc hi
    exact ⟨F.toNat, by simp [witness, hl, flagA], by simp [witness, hl, flagA]⟩
  · intro k m hm
    have hl := hM.loc hm
    have haddr : wordAddr (witness A rv pl F rF rR).lbl m.loc = some F.toNat := by
      simp [wordAddr, witness, hl, flagA]
    rcases k with _ | j
    · rw [hM.zero] at hm
      cases hm
      refine ⟨0, F.toNat, _, rfl, haddr, Scc.Sem.wordAt_of_read (v := 0) ?_, ?_⟩
      · rw [hloc]; simp [Memory.read?, Memory.initVal, hM.init]
      · simp [ValRep, flagInit]
    · have hj : j < t.1.mem.msgs.size := by
        rcases Nat.lt_or_ge j t.1.mem.msgs.size with h | h
        · exact h
        · have : s.mem.size ≤ j + 1 := by rw [hM.size]; omega
          simp [Array.getElem?_eq_none this] at hm
      obtain ⟨hl', hv, vw, hs'⟩ := hM.msg j hj
      rw [hs'] at hm
      cases hm
      refine ⟨j + 1, F.toNat, _, rfl, haddr, Scc.Sem.wordAt_of_read (v := t.1.mem.msgs[j].val) ?_, ?_⟩
      · rw [hloc]; simp [Memory.read?, Memory.get?, hl', hj]
      · simp [ValRep, hv, hone]
  · intro k m _ h0 k2 m2 hlt _
    simp only [witness, Option.some.injEq] at h0
    omega
  · intro k1 k2 k1' k2' h1 h2 _ _ hlt
    simp only [witness, Option.some.injEq] at h1 h2
    exact .inl (by omega)
  · intro k' m' hg _
    refine ⟨k', ?_, rfl⟩
    rw [hM.size]
    unfold Memory.get? at hg
    split at hg
    · cases hg
    · rcases Nat.lt_or_ge (k' - 1) t.1.mem.msgs.size with h | h
      · omega
      · simp [Array.getElem?_eq_none h] at hg
  · intro i th j tt hth hthr htt d e he x ty ws hlk k wd pl' hwd henv _hxf
    simp only [witness] at hthr
    split at hthr
    case isFalse => cases hthr
    rename_i hi
    cases hthr
    rw [hs] at hth
    rw [hc] at htt
    -- The thread's current frame is its only one.
    have hfr : ∀ th : TermRun.TTh, th.stack = [] → (frameEnvs th)[d]? = some e → d = 0 ∧ e = th.env := by
      intro th hst h
      simp only [frameEnvs, hst, List.map_nil] at h
      rcases d with _ | d
      · exact ⟨rfl, (Option.some.inj h).symm⟩
      · simp at h
    match i, hi, hth, htt with
    | 0, _, hth, htt =>
      change some th0 = some th at hth
      change some t0 = some tt at htt
      cases hth; cases htt
      obtain ⟨hst, henv0, hf⟩ := hW.frame hf0 hfW
      obtain ⟨rfl, rfl⟩ := hfr _ hst he
      simp only [witness] at henv
      split at henv
      · rename_i h1
        obtain ⟨-, rfl, rfl⟩ := h1
        cases henv
        rcases henv0 with h | h <;> rw [h] at hlk
        · rw [lookup_f_envF] at hlk; cases hlk; cases hwd; exact rep_f hf
        · rw [lookup_f_u] at hlk; cases hlk; cases hwd; exact rep_f hf
      · split at henv
        · rename_i h2; exact absurd h2.2.2.2 (by decide)
        · cases henv
    | 1, _, hth, htt =>
      change some th1 = some th at hth
      change some t1 = some tt at htt
      cases hth; cases htt
      obtain ⟨hst, hf, henv1⟩ := h1
      obtain ⟨rfl, rfl⟩ := hfr _ hst he
      simp only [witness] at henv
      split at henv
      · rename_i h1
        obtain ⟨-, rfl, rfl⟩ := h1
        cases henv
        rcases henv1 with h | ⟨v, w, h, -⟩ <;> rw [h] at hlk
        · rw [lookup_f_envF] at hlk; cases hlk; cases hwd; exact rep_f hf
        · rw [lookup_f_r] at hlk; cases hlk; cases hwd; exact rep_f hf
      split at henv
      case isFalse => cases henv
      · rename_i h2
        obtain ⟨-, rfl, rfl, -⟩ := h2
        cases henv
        rcases henv1 with h | ⟨v, w, h, hw, hlt, hr⟩ <;> rw [h] at hlk
        · rw [lookup_r_envF] at hlk; cases hlk
        · rw [lookup_r_r] at hlk
          cases hlk
          cases hwd
          refine ⟨v.toNat, by simp [placeVal, ExtMachine.ofBase, hr, Nat.mod_eq_of_lt hlt], ?_⟩
          simp [ValRep, hw, hlt]
  · intro i th hth d e xs he _ _ x _ ty ws hlk k hk
    rw [hs] at hth
    have hfr : ∀ th : TermRun.TTh, th.stack = [] → (frameEnvs th)[d]? = some e → d = 0 ∧ e = th.env := by
      intro th hst h
      simp only [frameEnvs, hst, List.map_nil] at h
      rcases d with _ | d
      · exact ⟨rfl, (Option.some.inj h).symm⟩
      · simp at h
    match i, hth with
    | 0, hth =>
      change some th0 = some th at hth
      cases hth
      obtain ⟨hst, henv0, -⟩ := hW.frame hf0 hfW
      obtain ⟨rfl, rfl⟩ := hfr _ hst he
      obtain ⟨rfl, rfl | ⟨rfl, w, hw⟩⟩ := lookup_word (.inl henv0) hlk hk
      · simp [witness]
      · rcases henv0 with h | h <;> rw [h] at hw <;> simp [envF] at hw
    | 1, hth =>
      change some th1 = some th at hth
      cases hth
      obtain ⟨hst, -, henv1⟩ := h1
      obtain ⟨rfl, rfl⟩ := hfr _ hst he
      have hk0 := lookup_word (.inr (henv1.imp_right fun ⟨_, w, h, _⟩ => ⟨w, h⟩)) hlk hk
      obtain ⟨rfl, hx⟩ := hk0
      rcases hx with rfl | ⟨rfl, -⟩ <;> simp [witness]
    | n + 2, hth => simp at hth
  · intro j rg h; simp at h
  · intro j j' rg rg' _ h; simp at h
  · intro j rg h; simp at h
  · intro j rg h; simp at h
  · intro j pl' h; exact h.elim
  · intro i d x k wp pl' j _ _ _ h; exact h
  · intro i th d e x k n _ _ h
    simp only [witness] at h
    repeat' split at h
    all_goals simp_all

/-- **The components of `R` hold** of every related pair, with `witness`. -/
theorem components (hS : Shape I F v1 st0 sW st1 fR) (hRg : Regs rv F st0 sW st1 fR rF rR)
    {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) {t : (ExtMachine.ofBase I A rv pl).Cfg} {s : TermRun.Cfg}
    (hR : Rel F v1 st0 sW st1 fR t.1 s) :
    Components (ExtMachine.ofBase I A rv pl) Λ (witness A rv pl F rF rR) t s := by
  obtain ⟨t0, t1, th0, th1, hc, hs, hW, -, hRd, hM⟩ := hR
  exact components_of hRg.f0 hRg.fW hS.one hΛ hc hs hW (hRd.frame hS hRg) hM

end Explicit

/-! ## The statement, up to progress -/

section Statement

open Scc.Sem (Sim Correct Budget InLayout RouteS)

variable {I : ISA} (A : Arch) {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {fR : Val → I.State}
  {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)} {rF rR : I.RegId}
  {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- The assembly: the two start states and the flag's initial write. -/
abbrev asmOf (st0 st1 : I.State) (F : BitVec 64) : List I.State × List (Loc × Val) :=
  ([st0, st1], [(⟨F, 8⟩, 0)])

/-- Every shared write of a configuration whose memory is related to a
source memory (`MemRel`) is the flag's word, inside `data`. -/
theorem inLayout_of {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) {t : (ExtMachine.ofBase I A rv pl).Cfg}
    {sm : WeakMem.Memory} {V : Val → Prop} (hM : MemRel F V t.1.mem sm) : InLayout Λ t := by
  have hF : Λ.shared F.toNat := by
    have := hΛ.sub
    simp only [Scc.Sem.Range.Sub] at this
    exact .inl (by simp only [Scc.Sem.Range.contains]; omega)
  refine ⟨fun m hm => ?_, fun p hp => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [Array.getElem?_toList] at hi
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
    rw [(hM.msg i hlt).1]
    exact hF
  · rw [hM.init] at hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact .inl hF

/-- Every shared write of a related configuration is the flag's word, inside
`data`. -/
theorem inLayout {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) {t : (ExtMachine.ofBase I A rv pl).Cfg}
    {s : TermRun.Cfg} (hR : Rel F v1 st0 sW st1 fR t.1 s) : InLayout Λ t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hM⟩ := hR
  exact inLayout_of A hΛ hM

variable (rv pl) in
/-- **The progress obligation**, left open: every configuration reachable
from the loaded start configuration has progress (no faulting step; every
live thread can step). It is a statement about the target alone; see
`Spike/Bridge/FINDING.md` for what proving it needs. -/
def ProgressOf (st0 st1 : I.State) (F : BitVec 64) : Prop :=
  ∀ t : (ExtMachine.ofBase I A rv pl).Cfg,
    ReachableSemInf A (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) t.1 → ∀ μ : Scc.Sem.Marks, (∀ k, μ.site k = none) → (ExtMachine.ofBase I A rv pl).Progress μ t

/-- **`Correct`, given progress.** Every clause of `Sim` but progress is
discharged for the existing machine as a target (`Target.ofBase`) and the
WeakCore program from `srcInit`, any knobs and memory model on the source
side, any budget: start, simulation (`sim_clause`), no access outside `Λ`
(`inLayout`), abort (vacuous: the base machine emits no event) and the
explicit components (`components`). Progress (no faulting step, every live
thread can step) is the hypothesis `hprog`; it is a fact about the target
alone. -/
theorem correct_of_progress (hS : Shape I F v1 st0 sW st1 fR) (hRg : Regs rv F st0 sW st1 fR rF rR)
    {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) (hwf : Λ.WF) (B : Budget)
    (hprog : ProgressOf A rv pl st0 st1 F) :
    Correct (Target.ofBase I A rv pl) (SrcSem.ofStep prog k arch (· = srcInit)) Λ B (asmOf st0 st1 F) := by
  refine ⟨{
    R := fun t s => Rel F v1 st0 sW st1 fR t.1 s
    layout := hwf
    start := ⟨_, srcInit, rfl, rfl, rel_init⟩
    progress := ?_
    sim := sim_clause A hS rv pl Λ _
    abort := ?_
    explicit := fun t s hR => ⟨witness A rv pl F rF rR, components hS hRg hΛ hR⟩ }⟩
  · intro t0 tr t h0 hr
    obtain ⟨-, s, -, hR, -⟩ := sim_clause A hS (k := k) (arch := arch) rv pl Λ _ t0 tr t h0 hr
    cases h0
    obtain ⟨-, hre⟩ := ExtMachine.ofBase_run_inv hr
    exact ⟨hprog t hre _ (fun _ => rfl), inLayout A hΛ hR⟩
  · intro t0 tr t tid es t' ak _ _ hs hab
    obtain ⟨rfl, -⟩ := ExtMachine.ofBase_step_inv hs
    cases hab

end Statement

end Spike.Bridge
