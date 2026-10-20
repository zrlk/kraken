/-
**Stage 3: solo runs of the AArch64 CAS spinlock
worker with outstanding promises** (`casTtasWorker`, valid layout).

A worker writes the lock (`l`) at its `CASA` (position 4: `W3`, which is `1`
after position 1, iff it reads `W2 = 0`) and its `STLR` (14: `0`), and the
counter (`c`) at its `STR` (13). Positions are visited in rank order (`rk`),
except for the try/spin loop (one rank). A thread is *pre-acquire*
(`PreAcq`) in the loop and not holding the lock. So a certifiable worker
(`Good`, from any certification: `good_of_run`) has only promises of three
kinds:

- an *acquire* promise (lock, value `≠ 0`): only a `CASA` fulfils it, so the
  thread is pre-acquire;
- a counter promise: up to the `STR`;
- a *release* promise (lock, value `0`): up to the `STLR`, above `vwOld` (a
  release fulfilment), and, for a pre-acquire thread, together with an
  acquire promise (a fresh `CASA` write raises `vwOld` past every promise).

A thread that is not pre-acquire, or holds an acquire promise (`NA`),
certifies without any fresh write (`nacert_of_run`; the run stops once the
promise set is empty): such a certification (`NACert`) replays against any
larger memory (`nacert_replay`) and gives an instruction step
(`instrEnabledSem_of`). A pre-acquire thread with only a counter promise may
be unable to certify; the liveness proof never needs it to step.

`step_solo` also classifies what a step does to the lock (`Eff`), and gives
the drop bound (`dropBounded_of_sinv`: at most one promise per instruction).
-/
import Kraken.Promising.LiveSpinSemShape
import Kraken.Promising.LiveSpinCasInv
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Live.SpinSemSolo

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SemShape Kraken.Promising.Live.SpinSemShape Kraken.Promising.Live.Sem
open Kraken.Promising.Live.SpinCasInv (Static Holder holder_of_pc stepOne_end s1 s3 s5 s7 s8 s9 s11 s12 s15)
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

set_option hygiene false in
local notation "pcA" => (layout casTtasWorker).addrOf

/-! ## Positions, ranks, predicates -/

/-- The register facts: `W3 = 1` after position 1, `W2 = 0` at the `CASA`. -/
def PcI (s : MachineData) (i : Nat) : Prop := (i ≠ 1 → w32 s.regs.X3 = 1#32) ∧ (i = 4 → w32 s.regs.X2 = 0#32)

/-- **The promise-agnostic per-thread invariant**: `Static`, a pc in `spPcs`,
the register facts. -/
structure SInv (l c : BitVec 64) (s : isa.State) : Prop where
  st : Static l c s
  pc : ∃ i ∈ spPcs, s.st.2 = pcA i ∧ PcI s.st.1 i

/-- The order of positions (the try/spin loop is one rank). -/
def rk : Nat → Nat
  | 1 => 0 | 3 => 1 | 4 => 1 | 5 => 1 | 7 => 1 | 8 => 1 | 9 => 1 | 11 => 2 | 12 => 3 | 13 => 4 | 14 => 5
  | 15 => 6 | _ => 7

/-- The thread's position has rank at most `r`. -/
def RkLe (t : Thread isa) (r : Nat) : Prop := ∀ i ∈ spPcs, t.st.st.2 = pcA i → rk i ≤ r

/-- **Pre-acquire**: in the try/spin loop (or before it), not holding the lock. -/
def PreAcq (t : Thread isa) : Prop := RkLe t 1 ∧ ¬ Holder t

/-- The thread holds an acquire promise (to the lock, of a non-zero value). -/
def HasAcq (l : BitVec 64) (t : Thread isa) (mem : Memory) : Prop :=
  ∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 l ∧ w.val ≠ 0

/-- Certifies without fresh writes (`nacert_of_run`): not pre-acquire, or
holding an acquire promise. -/
def NA (l : BitVec 64) (t : Thread isa) (mem : Memory) : Prop := ¬ PreAcq t ∨ HasAcq l t mem

/-- Every promise of `tid` is a message of its own in memory. -/
def PromIn (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.tid = tid

/-- **What a certifiable worker's promises satisfy.** -/
structure Good (l c : BitVec 64) (t : Thread isa) (mem : Memory) : Prop where
  loc : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w →
    (w.loc = L4 l ∧ w.val ≠ 0 ∧ PreAcq t) ∨ (w.loc = L4 c ∧ RkLe t 4) ∨
    (w.loc = L4 l ∧ w.val = 0 ∧ RkLe t 5 ∧ t.views.vwOld < ts ∧ (PreAcq t → HasAcq l t mem))

theorem good_nil {l c : BitVec 64} {t : Thread isa} {mem : Memory} (h : t.prom = []) : Good l c t mem :=
  ⟨fun ts hts => by rw [h] at hts; cases hts⟩

theorem rkLe_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (ht : t.st.st.2 = pcA p) (r : Nat) :
    RkLe t r ↔ rk p ≤ r :=
  ⟨fun h => h p hp ht, fun h i hi hi' => by rw [addrOf_inj hi hp (hi'.symm.trans ht)]; exact h⟩

theorem holder_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (ht : t.st.st.2 = pcA p) :
    Holder t ↔ (p = 5 ∧ w32 t.st.st.1.regs.X2 = 0#32) ∨ p ∈ [11, 12, 13, 14] := by
  constructor
  · rintro (⟨h, hz⟩ | h)
    · exact .inl ⟨addrOf_inj hp (by decide) (ht.symm.trans h), hz⟩
    · right
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;>
        · obtain rfl := addrOf_inj hp (by decide) (ht.symm.trans h); decide
  · rintro (⟨rfl, hz⟩ | h)
    · exact .inl ⟨ht, hz⟩
    · exact holder_of_pc h ht

theorem preAcq_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (ht : t.st.st.2 = pcA p) :
    PreAcq t ↔ rk p ≤ 1 ∧ ¬ (p = 5 ∧ w32 t.st.st.1.regs.X2 = 0#32) := by
  unfold PreAcq
  rw [rkLe_iff hp ht, holder_iff hp ht]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (.inl h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro (h | h)
    · exact h2 h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp [rk] at h1

/-! ## Larger memories -/

theorem PromIn.get {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem)
    {ts : Time} (hts : ts ∈ t.prom) : mem'.get? ts = mem.get? ts := by
  obtain ⟨w, hw, -⟩ := h ts hts
  exact hp.get? (mem.last_le_of_get?_eq_some hw)

theorem PromIn.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem) :
    PromIn tid t mem' := fun ts hts => by rw [h.get hp hts]; exact h ts hts

theorem PromIn.le {tid : Nat} {t : Thread isa} {mem : Memory} (h : PromIn tid t mem) : ∀ ts ∈ t.prom, ts ≤ mem.last :=
  fun ts hts => let ⟨_, hw, _⟩ := h ts hts; mem.last_le_of_get?_eq_some hw

theorem HasAcq.mono {l : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : HasAcq l t mem) : HasAcq l t mem' := by
  obtain ⟨ts, hts, w, hw, hl⟩ := h
  exact ⟨ts, hts, w, by rw [hP.get hp hts]; exact hw, hl⟩

theorem NA.mono {l : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : NA l t mem) : NA l t mem' :=
  h.imp_right (HasAcq.mono hp hP)

theorem Good.mono {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : Good l c t mem) : Good l c t mem' := by
  refine ⟨fun ts hts w hw => ?_⟩
  rcases h.loc ts hts w (by rw [← hP.get hp hts]; exact hw) with a | a | ⟨a1, a2, a3, a4, a5⟩
  · exact .inl a
  · exact .inr (.inl a)
  · exact .inr (.inr ⟨a1, a2, a3, a4, fun h => (a5 h).mono hp hP⟩)

/-! ## The writing positions with promises -/

section Steps

variable {l c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static l c t.st) (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The `CASA` (position 4), with any promise set. -/
theorem s4p (hpc : t.st.st.2 = pcA 4) :
    ∃ tr old, oc.thread.st = SpinCasTrees.goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) }
        (pcA 5) ∧
      mem.read? (L4 l) tr = some old ∧
      (mem.lastWrite (L4 l) ≤ t.views.getCoh (L4 l) → old = mem.finalVal (L4 l)) ∧
      ((BitVec.setWidth 32 old ≠ w32 t.st.st.1.regs.X2 ∧ oc.mem = mem ∧ oc.thread.prom = t.prom ∧
          oc.thread.views.vwOld = t.views.vwOld) ∨
       (BitVec.setWidth 32 old = w32 t.st.st.1.regs.X2 ∧
        ((oc.mem = (mem.append { loc := L4 l, val := BitVec.setWidth 128 (w32 t.st.st.1.regs.X3), tid }).1 ∧
          oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
          mem.last + 1 ≤ oc.thread.views.vwOld ∧ mem.last + 1 ≤ oc.thread.views.getCoh (L4 l)) ∨
         (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 l, val := BitVec.setWidth 128 (w32 t.st.st.1.regs.X3), tid } ∧
          oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld ∧
          ts ≤ oc.thread.views.getCoh (L4 l))))) := by
  obtain ⟨tr, old, hst, hrd, hlw, hcase⟩ :=
    spec_rmwo_p _ _ rfl (exec_casa _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho
  refine ⟨tr, old, hst, hrd, hlw, ?_⟩
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨new, h1, ⟨e1, e2, e3, -, e5, -⟩ | ⟨ts, hts, e1, -, e3, e4, e5, e6, -⟩⟩
  · refine .inl ⟨fun e => ?_, h2, h3, h4⟩
    simp [e] at h1
  · by_cases e : BitVec.setWidth 32 old = w32 t.st.st.1.regs.X2
    · simp only [e, ↓reduceIte, Option.some.injEq] at h1
      subst h1
      exact .inr ⟨e, .inl ⟨e1, e2, e3 rfl, e5⟩⟩
    · simp [e] at h1
  · by_cases e : BitVec.setWidth 32 old = w32 t.st.st.1.regs.X2
    · simp only [e, ↓reduceIte, Option.some.injEq] at h1
      subst h1
      exact .inr ⟨e, .inr ⟨ts, hts, e1, e3, e4, e5, e6⟩⟩
    · simp [e] at h1

/-- The counter `STR` (position 13), with any promise set. -/
theorem s13p (hpc : t.st.st.2 = pcA 13) :
    oc.thread.st = SpinCasTrees.goto t.st t.st.st.1 (pcA 14) ∧
    ((oc.mem = (mem.append
        { loc := L4 c, val := BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec), tid }).1 ∧
      oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
     (∃ ts ∈ t.prom, (∃ w, mem.get? ts = some w ∧ w.loc = L4 c) ∧ oc.mem = mem ∧
      oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld)) := by
  obtain ⟨hst, h⟩ := spec_store_p _ _ (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dc) hs ho
  refine ⟨hst, ?_⟩
  rcases h with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, -, -, e4, e5, e6⟩
  · exact .inl ⟨e1, e2, e3 rfl⟩
  · exact .inr ⟨ts, hts, ⟨_, e1, rfl⟩, e4, e5, e6⟩

/-- The `STLR` (position 14), with any promise set. -/
theorem s14p (hpc : t.st.st.2 = pcA 14) :
    oc.thread.st = SpinCasTrees.goto t.st t.st.st.1 (pcA 15) ∧
    (oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1 ∨
     (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 l, val := 0#128, tid } ∧ t.views.getCoh (L4 l) < ts ∧
      t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts)) ∧
    (oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1 →
      oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1)) := by
  obtain ⟨hst, h⟩ := spec_store_p _ _ (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho
  refine ⟨hst, ?_, fun hm => ?_⟩
  · rcases h with ⟨e1, -, -⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, -⟩
    · exact .inl e1
    · exact .inr ⟨ts, hts, e1, e2, e3 rfl, e4, e5⟩
  · rcases h with ⟨-, e2, -⟩ | ⟨ts, -, -, -, -, e4, -, -⟩
    · exact e2
    · rw [e4] at hm; exact absurd hm.symm (append_ne _ _)

end Steps

/-! ## One step of a worker alone -/

/-- **What an instruction step does to the lock.** -/
inductive Eff (l c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; its promises are kept; a holder stays one. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 l → ts ∈ oc.thread.prom)
      (hh : Holder t → Holder oc.thread)
  /-- A `CASA` appending a non-zero value: the thread now holds the lock. -/
  | acqFresh (v : Val) (hv : v ≠ 0) (hm : oc.mem = (mem.append { loc := L4 l, val := v, tid }).1)
      (hh : Holder oc.thread) (hc : mem.last + 1 ≤ oc.thread.views.getCoh (L4 l))
  /-- A `CASA` fulfilling an acquire promise: the thread now holds the lock. -/
  | acqFul (ts : Time) (hts : ts ∈ t.prom) (w : Msg) (hw : mem.get? ts = some w) (hl : w.loc = L4 l)
      (hv : w.val ≠ 0) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts) (hh : Holder oc.thread)
      (hnh : ¬ Holder t) (hc : ts ≤ oc.thread.views.getCoh (L4 l))
  /-- The `STLR` appending `0`. -/
  | relFresh (hm : oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1) (hh : Holder t)
  /-- The `STLR` fulfilling a release promise, above the coherence view. -/
  | relFul (ts : Time) (hts : ts ∈ t.prom) (hw : mem.get? ts = some { loc := L4 l, val := 0#128, tid })
      (hc : t.views.getCoh (L4 l) < ts) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts)
      (hh : Holder t)

/-- The results of one step of a worker, with any promises. -/
structure SoloRes (l c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop where
  sinv : SInv l c oc.thread.st
  promIn : PromIn tid oc.thread oc.mem
  len : t.prom.length ≤ oc.thread.prom.length + 1
  back : Good l c oc.thread oc.mem → Good l c t mem ∧ (t.prom ≠ [] → NA l t mem → oc.mem = mem)
  keep : NA l t mem → NA l oc.thread oc.mem
  eff : Eff l c tid t mem oc

theorem pci_keep {s s' : MachineData} {p q : Nat} (h : PcI s p) (hp : p ≠ 1) (h3 : s'.regs.X3 = s.regs.X3)
    (hq : q ≠ 4) : PcI s' q :=
  ⟨fun _ => h3 ▸ h.1 hp, fun e => absurd e hq⟩

theorem w32_set2 (r : Reg64s) (old : Val) :
    w32 (r.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 old))).X2 = BitVec.setWidth 32 old := by
  show BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) = _
  simp

theorem len_erase_fresh {p : List Time} {n : Time} (h : ∀ ts ∈ p, ts ≤ n) :
    ((p ++ [n + 1]).erase (n + 1)) = p := erase_fresh h

theorem lt3_absurd {a b d : Nat} (h1 : a + 1 ≤ b) (h2 : b < d) (h3 : d ≤ a) : False := by omega

theorem len_erase {p : List Time} (ts : Time) : p.length ≤ (p.erase ts).length + 1 := by
  rw [List.length_erase]; split <;> omega

local macro "sinvq" hSt:ident hst:ident "," q:num : term =>
  `(⟨by rw [$hst:ident]; exact ($hSt).goto _ _ rfl rfl rfl, $q, by decide, by rw [$hst:ident], ?_⟩)

/-- **One step of a worker alone**, position by position. -/
theorem step_solo {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hlc : L4 l ≠ L4 c)
    (hS : SInv l c t.st) (hP : PromIn tid t mem)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : SoloRes l c tid t mem oc := by
  obtain ⟨hSt, p, hp, hpc, hI⟩ := hS
  have hPl := hP.le
  have quiet : ∀ q ∈ spPcs, oc.thread.st.st.2 = pcA q → rk p ≤ rk q → oc.mem = mem → oc.thread.prom = t.prom →
      t.views.vwOld ≤ oc.thread.views.vwOld → (PreAcq oc.thread ↔ PreAcq t) → (Holder t → Holder oc.thread) →
      SInv l c oc.thread.st → SoloRes l c tid t mem oc := by
    intro q hq hqc hr hm hpr hvw hpa hh hsi
    have hrk : ∀ r, RkLe oc.thread r → RkLe t r := fun r h =>
      (rkLe_iff hp hpc r).mpr (Nat.le_trans hr ((rkLe_iff hq hqc r).mp h))
    have hg : ∀ {ts w}, mem.get? ts = some w → oc.mem.get? ts = some w := fun h => by rw [hm]; exact h
    have hacq : HasAcq l oc.thread oc.mem → HasAcq l t mem := fun ⟨ts, hts, w, hw, h⟩ =>
      ⟨ts, hpr ▸ hts, w, by rw [← hm]; exact hw, h⟩
    have hacq' : HasAcq l t mem → HasAcq l oc.thread oc.mem := fun ⟨ts, hts, w, hw, h⟩ =>
      ⟨ts, by rw [hpr]; exact hts, w, hg hw, h⟩
    refine ⟨hsi, fun ts hts => by rw [hm]; exact hP ts (hpr ▸ hts), by rw [hpr]; omega,
      fun hgd => ⟨⟨fun ts hts w hw => ?_⟩, fun _ _ => hm⟩,
      fun h => h.imp (fun h' h'' => h' (hpa.mp h'')) hacq',
      .quiet (.inl hm) (fun ts hts _ _ _ => by rw [hpr]; exact hts) hh⟩
    rcases hgd.loc ts (by rw [hpr]; exact hts) w (hg hw) with ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b, d, e, f⟩
    · exact .inl ⟨a, b, hpa.mp d⟩
    · exact .inr (.inl ⟨a, hrk _ b⟩)
    · exact .inr (.inr ⟨a, b, hrk _ d, Nat.lt_of_le_of_lt hvw e, fun h => hacq (f (hpa.mpr h))⟩)
  have nh : p ≠ 5 → p ∉ [11, 12, 13, 14] → ¬ Holder t := fun h5 h11 h => by
    rcases (holder_iff hp hpc).mp h with ⟨e, -⟩ | h'
    · exact h5 e
    · exact h11 h'
  have hp' := hp
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `MOV W3, #1`
    have hex := exec_mov3 _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s1 hSt hs ho hpc
    refine quiet 3 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 3) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 3)
    rw [hst]; exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
  · -- 3: `MOV W2, #0`
    have hex := exec_mov2 _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s3 hSt hs ho hpc
    refine quiet 4 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 4) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 4)
    rw [hst]; exact ⟨fun _ => hI.1 (by decide), fun _ => rfl⟩
  · -- 4: `CASA`
    have hz : w32 t.st.st.1.regs.X2 = 0#32 := hI.2 rfl
    have h3 : w32 t.st.st.1.regs.X3 = 1#32 := hI.1 (by decide)
    have hnt : ¬ Holder t := nh (by decide) (by decide)
    have hpre : PreAcq t := (preAcq_iff hp hpc).mpr (by simp [rk])
    obtain ⟨tr, old, hst, -, -, hcase⟩ := s4p hSt hs ho hpc
    have hsi : SInv l c oc.thread.st := ⟨by rw [hst]; exact hSt.goto _ _ rfl rfl rfl, 5, by decide, by rw [hst],
      by rw [hst]; exact pci_keep hI (by decide) rfl (by decide)⟩
    have hw2 : w32 oc.thread.st.st.1.regs.X2 = BitVec.setWidth 32 old := by rw [hst]; exact w32_set2 _ _
    have hv0 : BitVec.setWidth 128 (w32 t.st.st.1.regs.X3) ≠ 0 := by rw [h3]; decide
    rcases hcase with ⟨hne, hm, hpr, hvw⟩ | ⟨heq, ⟨hm, hpr, hvw, hco⟩ | ⟨ts, hts, hw, hm, hpr, hvw, hco⟩⟩
    · refine quiet 5 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq hvw.symm)
        (by rw [preAcq_iff (p := 5) (by decide) (by rw [hst]), preAcq_iff hp hpc, hw2, ← hz]; simp [rk, hne])
        (fun h => absurd h hnt) hsi
    · have hho : Holder oc.thread := .inl ⟨by rw [hst], by rw [hw2, heq, hz]⟩
      have hnpo : ¬ PreAcq oc.thread := fun h => h.2 hho
      have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), by rw [hpr']; exact Nat.le_succ _,
        fun hg => ?_, fun _ => .inl hnpo, .acqFresh _ hv0 hm hho hco⟩
      have honly : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 c := by
        intro ts hts w hw
        rcases hg.loc ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw) with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, -, -, h, -⟩
        · exact absurd h hnpo
        · exact h
        · exact (lt3_absurd hvw h (hPl ts hts)).elim
      refine ⟨⟨fun ts hts w hw => .inr (.inl ⟨honly ts hts w hw, (rkLe_iff hp hpc 4).mpr (by decide)⟩)⟩,
        fun _ hna => ?_⟩
      rcases hna with h | ⟨ts, hts, w, hw, hl, -⟩
      · exact absurd hpre h
      · exact absurd (hl.symm.trans (honly ts hts w hw)) hlc
    · have hho : Holder oc.thread := .inl ⟨by rw [hst], by rw [hw2, heq, hz]⟩
      have hnpo : ¬ PreAcq oc.thread := fun h => h.2 hho
      have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        by rw [hpr]; exact len_erase ts, fun hg => ?_, fun _ => .inl hnpo,
        .acqFul ts hts _ hw rfl hv0 hm hpr hho hnt hco⟩
      rw [hm] at hg
      refine ⟨⟨fun ts' hts' w' hw' => ?_⟩, fun _ _ => hm⟩
      by_cases e : ts' = ts
      · subst e; rw [hw] at hw'; cases hw'
        exact .inl ⟨rfl, hv0, hpre⟩
      · rcases hg.loc ts' (hin ts' hts' e) w' hw' with ⟨-, -, h⟩ | ⟨a, b⟩ | ⟨a, b, d, f, -⟩
        · exact absurd h hnpo
        · exact .inr (.inl ⟨a, (rkLe_iff hp hpc 4).mpr (by decide)⟩)
        · exact .inr (.inr ⟨a, b, (rkLe_iff hp hpc 5).mpr (by decide), Nat.lt_of_le_of_lt hvw f,
            fun _ => ⟨ts, hts, _, hw, rfl, hv0⟩⟩)
  · -- 5: `CBZ`
    have hex := exec_cbz _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s5 hSt hs ho hpc
    have hvw := Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      refine quiet 11 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff (p := 11) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk, hz])
        (fun _ => holder_of_pc (p := 11) (by decide) (by rw [hst])) (sinvq hSt hst, 11)
      rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
    · rw [ite_eq_right hz] at hst
      refine quiet 7 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff (p := 7) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk, hz])
        (fun h => absurd ((holder_iff hp hpc).mp h) (by simp [hz])) (sinvq hSt hst, 7)
      rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · -- 7: `LDR` lock
    have hex := exec_ldr_l _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl
    obtain ⟨ts, v, hst, -, -, hm, hpr, -⟩ := s7 hSt hs ho hpc
    refine quiet 8 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_load_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 8) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 8)
    rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · -- 8: `CBNZ`
    have hex := exec_cbnz _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s8 hSt hs ho hpc
    have hvw := Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      refine quiet 9 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff (p := 9) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
        (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 9)
      rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
    · rw [ite_eq_right hz] at hst
      refine quiet 7 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff (p := 7) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
        (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 7)
      rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · -- 9: `B try`
    have hex := exec_b_try _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s9 hSt hs ho hpc
    refine quiet 3 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 3) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 3)
    rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · -- 11: `LDR` counter
    have hex := exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc
    obtain ⟨ts, v, hst, -, hm, hpr⟩ := s11 hSt hs ho hpc
    refine quiet 12 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_load_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 12) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun _ => holder_of_pc (p := 12) (by decide) (by rw [hst])) (sinvq hSt hst, 12)
    rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · -- 12: `ADD W5`
    have hex := exec_add5 _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s12 hSt hs ho hpc
    refine quiet 13 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 13) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun _ => holder_of_pc (p := 13) (by decide) (by rw [hst])) (sinvq hSt hst, 13)
    rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · -- 13: `STR` counter
    obtain ⟨hst, hcase⟩ := s13p hSt hs ho hpc
    have hsi : SInv l c oc.thread.st := ⟨by rw [hst]; exact hSt.goto _ _ rfl rfl rfl, 14, by decide, by rw [hst],
      by rw [hst]; exact pci_keep hI (by decide) rfl (by decide)⟩
    have hho : Holder oc.thread := holder_of_pc (p := 14) (by decide) (by rw [hst])
    have hnpo : ¬ PreAcq oc.thread := fun h => h.2 hho
    have hrk : ∀ r, RkLe oc.thread r ↔ 5 ≤ r := rkLe_iff (p := 14) (by decide) (by rw [hst])
    rcases hcase with ⟨hm, hpr, hvw⟩ | ⟨ts, hts, ⟨wc, hwc, hlc'⟩, hm, hpr, hvw⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      have hnone : Good l c oc.thread oc.mem → ∀ ts ∈ t.prom, False := fun hg ts hts => by
        obtain ⟨w, hw, -⟩ := hP ts hts
        rcases hg.loc ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw) with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, -, -, h, -⟩
        · exact hnpo h
        · exact absurd ((hrk 4).mp h) (by decide)
        · exact lt3_absurd hvw h (hPl ts hts)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), by rw [hpr']; exact Nat.le_succ _,
        fun hg => ⟨⟨fun ts hts => (hnone hg ts hts).elim⟩, fun hne _ => ?_⟩, fun _ => .inl hnpo,
        .quiet (.inr ⟨_, hm⟩) (fun ts hts _ _ _ => hpr' ▸ hts) (fun _ => hho)⟩
      obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hnone hg ts hts).elim
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        by rw [hpr]; exact len_erase ts, fun hg => ?_, fun _ => .inl hnpo,
        .quiet (.inl hm) (fun ts' hts' w hw hl => hin ts' hts' (fun e => by
          subst e; rw [hwc] at hw; cases hw; exact hlc (hl.symm.trans hlc'))) (fun _ => hho)⟩
      rw [hm] at hg
      refine ⟨⟨fun ts' hts' w' hw' => ?_⟩, fun _ _ => hm⟩
      by_cases e : ts' = ts
      · subst e; rw [hwc] at hw'; cases hw'
        exact .inr (.inl ⟨hlc', (rkLe_iff hp hpc 4).mpr (by decide)⟩)
      · rcases hg.loc ts' (hin ts' hts' e) w' hw' with ⟨-, -, h⟩ | ⟨-, b⟩ | ⟨a, b, d, f, -⟩
        · exact absurd h hnpo
        · exact absurd ((hrk 4).mp b) (by decide)
        · exact .inr (.inr ⟨a, b, (rkLe_iff hp hpc 5).mpr (by decide), Nat.lt_of_le_of_lt hvw f,
            fun h => absurd h (fun h => h.2 (holder_of_pc (p := 13) (by decide) hpc))⟩)
  · -- 14: `STLR`
    obtain ⟨hst, hcase, hpf⟩ := s14p hSt hs ho hpc
    have hsi : SInv l c oc.thread.st := ⟨by rw [hst]; exact hSt.goto _ _ rfl rfl rfl, 15, by decide, by rw [hst],
      by rw [hst]; exact pci_keep hI (by decide) rfl (by decide)⟩
    have hnpo : ¬ PreAcq oc.thread := fun h => absurd ((rkLe_iff (p := 15) (by decide) (by rw [hst]) 1).mp h.1)
      (by decide)
    have hdead : Good l c oc.thread oc.mem → ∀ ts ∈ oc.thread.prom, ∀ w, oc.mem.get? ts = some w → False := by
      intro hg ts hts w hw
      have hrk : ∀ r, RkLe oc.thread r ↔ 6 ≤ r := rkLe_iff (p := 15) (by decide) (by rw [hst])
      rcases hg.loc ts hts w hw with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, -, h, -⟩
      · exact hnpo h
      · exact absurd ((hrk 4).mp h) (by decide)
      · exact absurd ((hrk 5).mp h) (by decide)
    rcases hcase with hm | ⟨ts, hts, hw, hco, hvo, hm, hpr⟩
    · have hpr' : oc.thread.prom = t.prom := (hpf hm).trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      have hnone : Good l c oc.thread oc.mem → ∀ ts ∈ t.prom, False := fun hg ts hts => by
        obtain ⟨w, hw, -⟩ := hP ts hts
        exact hdead hg ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), by rw [hpr']; exact Nat.le_succ _,
        fun hg => ⟨⟨fun ts hts => (hnone hg ts hts).elim⟩, fun hne _ => ?_⟩, fun _ => .inl hnpo,
        .relFresh hm (holder_of_pc (p := 14) (by decide) hpc)⟩
      obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hnone hg ts hts).elim
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        by rw [hpr]; exact len_erase ts, fun hg => ?_, fun _ => .inl hnpo,
        .relFul ts hts hw hco hm hpr (holder_of_pc (p := 14) (by decide) hpc)⟩
      refine ⟨⟨fun ts' hts' w' hw' => ?_⟩, fun _ _ => hm⟩
      by_cases e : ts' = ts
      · subst e; rw [hw] at hw'; cases hw'
        exact .inr (.inr ⟨rfl, rfl, (rkLe_iff hp hpc 5).mpr (by decide), hvo,
          fun h => absurd h (fun h => h.2 (holder_of_pc (p := 14) (by decide) hpc))⟩)
      · exact (hdead hg ts' (hin ts' hts' e) w' (by rw [hm]; exact hw')).elim
  · -- 15: `B done`
    have hex := exec_b_done _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s15 hSt hs ho hpc
    refine quiet 17 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff (p := 17) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide))) (sinvq hSt hst, 17)
    rw [hst]; exact pci_keep hI (by decide) rfl (by decide)
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-! ## Promise-free facts: `SInv` and the drop bound -/

theorem len_fresh (p : List Time) (n : Time) : p.length ≤ ((p ++ [n]).erase n).length + 1 := by
  rw [List.length_erase]; simp

theorem sinv_goto {l c : BitVec 64} {s s' : isa.State} {m : MachineData} {q : Nat}
    (hst : s' = SpinCasTrees.goto s m (pcA q)) (hSt : Static l c (SpinCasTrees.goto s m (pcA q)))
    (hq : q ∈ spPcs) (hI : PcI m q) : SInv l c s' :=
  ⟨by rw [hst]; exact hSt, q, hq, by rw [hst], by rw [hst]; exact hI⟩

/-- **One step keeps `SInv` and drops at most one promise**, against any
memory. -/
theorem step_sinv {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv l c t.st)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv l c oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 := by
  obtain ⟨hSt, p, hp, hpc, hI⟩ := hS
  have eq : ∀ {a b : List Time}, b = a → a.length ≤ b.length + 1 := fun h => by rw [h]; exact Nat.le_succ _
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, hpr, -⟩ := s1 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) ⟨fun _ => rfl, fun h => absurd h (by decide)⟩, eq hpr⟩
  · obtain ⟨-, hst, hpr, -⟩ := s3 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) ⟨fun _ => hI.1 (by decide), fun _ => rfl⟩, eq hpr⟩
  · obtain ⟨tr, old, hst, -, -, hcase⟩ := s4p hSt hs ho hpc
    refine ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), ?_⟩
    rcases hcase with ⟨-, -, hpr, -⟩ | ⟨-, ⟨-, hpr, -⟩ | ⟨ts, -, -, -, hpr, -⟩⟩
    · exact eq hpr
    · rw [hpr]; exact len_fresh _ _
    · rw [hpr]; exact len_erase ts
  · obtain ⟨-, hst, hpr, -⟩ := s5 hSt hs ho hpc
    refine ⟨?_, eq hpr⟩
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      exact sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide))
    · rw [ite_eq_right hz] at hst
      exact sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide))
  · obtain ⟨ts, v, hst, -, -, -, hpr, -⟩ := s7 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), eq hpr⟩
  · obtain ⟨-, hst, hpr, -⟩ := s8 hSt hs ho hpc
    refine ⟨?_, eq hpr⟩
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · rw [ite_eq_left hz] at hst
      exact sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide))
    · rw [ite_eq_right hz] at hst
      exact sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide))
  · obtain ⟨-, hst, hpr, -⟩ := s9 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), eq hpr⟩
  · obtain ⟨ts, v, hst, -, -, hpr⟩ := s11 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), eq hpr⟩
  · obtain ⟨-, hst, hpr, -⟩ := s12 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), eq hpr⟩
  · obtain ⟨hst, hcase⟩ := s13p hSt hs ho hpc
    refine ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), ?_⟩
    rcases hcase with ⟨-, hpr, -⟩ | ⟨ts, -, -, -, hpr, -⟩
    · rw [hpr]; exact len_fresh _ _
    · rw [hpr]; exact len_erase ts
  · obtain ⟨hst, hcase, hpf⟩ := s14p hSt hs ho hpc
    refine ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), ?_⟩
    rcases hcase with hm | ⟨ts, -, -, -, -, -, hpr⟩
    · rw [hpf hm]; exact len_fresh _ _
    · rw [hpr]; exact len_erase ts
  · obtain ⟨-, hst, hpr, -⟩ := s15 hSt hs ho hpc
    exact ⟨sinv_goto hst (hSt.goto _ _ rfl rfl rfl) (by decide) (pci_keep hI (by decide) rfl (by decide)), eq hpr⟩
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {l c : BitVec 64} {tid : Nat} {p q : Thread isa × Memory}
    (h : ThreadNP Arch.armv8 tid p q) (hp : SInv l c p.1.st) : SInv l c q.1.st :=
  ThreadNP.stateInv (SInv l c) (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {l c : BitVec 64} {tid : Nat} {t : Thread isa} (h : SInv l c t.st) :
    DropBounded Arch.armv8 1 tid t :=
  dropBounded_of_stateInv (SInv l c) (fun h hs ho => step_sinv h hs ho) h

/-! ## Along a run -/

/-- A solo run only extends memory (the generic
`ThreadNPn.mem_prefix`; `TicketSolo.threadNPn_prefix` is another instance). -/
theorem threadNPn_prefix {tid n : Nat} {p q : Thread isa × Memory} (h : ThreadNPn Arch.armv8 tid n p q) :
    p.2.Prefix q.2 := h.mem_prefix

/-- A certification without fresh writes, against memory `mem` (as
`TicketSolo.NACert`; both unfold to `Sem.NACertG Arch.armv8`). -/
def NACert (fuel tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∃ t', ThreadNPn Arch.armv8 tid fuel (t, mem) (t', mem) ∧ t'.prom = []

section Run

variable {l c : BitVec 64} {tid : Nat} (hlc : L4 l ≠ L4 c)

include hlc

/-- **A certifiable worker is `Good`.** -/
theorem good_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
    SInv l c p.1.st → PromIn tid p.1 p.2 → Good l c p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _; exact good_nil hq
  | step hs _ ih =>
    intro hq hS hP
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have r := step_solo hlc hS hP hs ho
    exact (r.back (ih hq r.sinv r.promIn)).1

theorem good_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.armv8 tid t mem fuel)
    (hS : SInv l c t.st) (hP : PromIn tid t mem) : Good l c t mem :=
  let ⟨_, _, hr, hp⟩ := h; good_of_run hlc hr hp hS hP

/-- **A worker that is not pre-acquire, or holds an acquire promise,
certifies without fresh writes** (stopping once its promise set is empty). -/
theorem nacert_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
    SInv l c p.1.st → PromIn tid p.1 p.2 → NA l p.1 p.2 →
    ∃ t', ThreadNPn Arch.armv8 tid n p (t', p.2) ∧ t'.prom = [] := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _ _; exact ⟨p.1, .refl _ _, hq⟩
  | @step n p q r hs h ih =>
    intro hq hS hP hN
    by_cases hp0 : p.1.prom = []
    · exact ⟨p.1, .refl _ _, hp0⟩
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    have rs := step_solo hlc hS hP hs' ho
    have hm := (rs.back (good_of_run hlc h hq rs.sinv rs.promIn)).2 hp0 hN
    obtain ⟨t', h', ht'⟩ := ih hq rs.sinv rs.promIn (rs.keep hN)
    refine ⟨t', .step ⟨outs, oc, hs', ho, rfl⟩ ?_, ht'⟩
    rw [← hm]; exact h'

theorem nacert_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.armv8 tid t mem fuel)
    (hS : SInv l c t.st) (hP : PromIn tid t mem) (hN : NA l t mem) : NACert fuel tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; nacert_of_run hlc hr hp hS hP hN

end Run

/-! ## Replay and enabledness -/

/-- **A step that keeps memory replays against a larger memory.** -/
theorem replay_cas {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv l c t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.armv8 t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.armv8 t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  obtain ⟨hSt, p, hpp, hpc, -⟩ := hS
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replay_done _ _ hp hb hs ho hm (exec_mov3 _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_done _ _ hp hb hs ho hm (exec_mov2 _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_rmwo _ _ hp hb hs ho hm rfl (exec_casa _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (exec_cbz _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_load _ _ hp hb hs ho hm (exec_ldr_l _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (exec_cbnz _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_done _ _ hp hb hs ho hm (exec_b_try _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_load _ _ hp hb hs ho hm (exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc)
  · exact replay_done _ _ hp hb hs ho hm (exec_add5 _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_store _ _ hp hb hs ho hm (exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc)
  · exact replay_store _ _ hp hb hs ho hm (exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (exec_b_done _ (hSt.at (by decide) (by decide) hpc))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem nacert_replay {l c : BitVec 64} {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.armv8 tid n p q → p.2 = q.2 → SInv l c p.1.st → p.1.Bnd p.2.last →
    ∀ mem, p.2.Prefix mem → ThreadNPn Arch.armv8 tid n (p.1, mem) (q.1, mem) :=
  nacertG_replay (SInv l c) (fun hS hs ho => (step_sinv hS hs ho).1)
    (fun hS hb hp hs ho hm => replay_cas hS hb hp hs ho hm)

theorem NACert.replay {l c : BitVec 64} {fuel tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    (h : NACert fuel tid t mem0) (hS : SInv l c t.st) (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) :
    NACert fuel tid t mem :=
  let ⟨t', hr, ht'⟩ := h; ⟨t', nacert_replay hr rfl hS hb mem hp, ht'⟩

/-- **A worker that is not at its end and either has no promise or certifies
without fresh writes can take an instruction step** (semantic machine). -/
theorem instrEnabledSem_of {l c : BitVec 64} {fuel tid : Nat} {cfg : Config isa} {t : Thread isa}
    (ht : cfg.threads[tid]? = some t) (hS : SInv l c t.st) (h17 : t.st.st.2 ≠ pcA 17)
    (hb : t.Bnd cfg.mem.last) (hn : t.prom = [] ∨ NACert fuel tid t cfg.mem) :
    InstrEnabledSem Arch.armv8 fuel tid cfg := by
  have hnil : t.prom = [] → InstrEnabledSem Arch.armv8 fuel tid cfg := by
    intro hp0
    have fin := fun outs (oc : Outcome isa) =>
      instrEnabledSem_of_step (A := Arch.armv8) (fuel := fuel) (outs := outs) (oc := oc) ht
    have dn : ∀ {s : isa.State}, isa.exec t.st = some (.done s) → InstrEnabledSem Arch.armv8 fuel tid cfg :=
      fun hex => by
        obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.armv8 tid hex (mem := cfg.mem)
        exact fin _ _ h1 h2 (h3.trans hp0)
    obtain ⟨hSt, p, hpp, hpc, -⟩ := hS
    simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
    rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dn (exec_mov3 _ (hSt.at (by decide) (by decide) hpc))
    · exact dn (exec_mov2 _ (hSt.at (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_rmwo Arch.armv8 tid rfl hp0 hb
        (exec_casa _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl)
      exact fin _ _ h1 h2 h3
    · exact dn (exec_cbz _ (hSt.at (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 tid hp0
        (exec_ldr_l _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl) (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · exact dn (exec_cbnz _ (hSt.at (by decide) (by decide) hpc))
    · exact dn (exec_b_try _ (hSt.at (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 tid hp0
        (exec_ldr_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc) (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · exact dn (exec_add5 _ (hSt.at (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 tid hp0 hb
        (exec_str_c _ (hSt.at (by decide) (by decide) hpc) hSt.x1 hSt.dc)
      exact fin _ _ h1 h2 h3
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 tid hp0 hb
        (exec_stlr _ (hSt.at (by decide) (by decide) hpc) hSt.x0 hSt.dl)
      exact fin _ _ h1 h2 h3
    · exact dn (exec_b_done _ (hSt.at (by decide) (by decide) hpc))
    · exact absurd hpc h17
  exact instrEnabledSem_of_nacertG ht hnil hn

end Kraken.Promising.Live.SpinSemSolo
