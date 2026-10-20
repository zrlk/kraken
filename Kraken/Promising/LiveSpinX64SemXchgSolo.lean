/-
**Stage 3: solo runs of the x64 `xchg`
spinlock workers with outstanding promises** (`spinlock2/3.kl`, the verbatim
image `SpinAbs.spinImageV`, on a valid layout), under `Arch.tso`.

A worker writes the lock at its `xchgl` (position 5: `%eax`'s low word, which
is `1` after `movl $1,%eax`, whatever it reads; `SInv.eax1`) and at its
`movl $0,(lock)` release (11), and the counter at its `movl %ecx,(counter)`
(10). On `Arch.tso` every store is a release and the `xchgl` is an `acqRel`
locked RMW, so (`step_sinv`, `SpinX64SemShape.TsoW`) every fulfilment lies
above `vwOld` and every fresh write raises `vwOld` past `|M|`: **a certifiable
worker certifies without fresh writes** (`nacert_of_certOkN`, from
`SpinX64SemShape.nacertG_of_tsoW`). This removes the AArch64 proof's `NA`
classes (`LiveSpinSemSwpSolo`). Such a certification replays against any
larger memory (`NACertG.replay`) and gives an instruction step
(`instrEnabledSem_of`).

A thread is *pre-acquire* (`PreAcq`) in its test-and-test-and-set loop
(positions 1–7) and not holding the lock. A certifiable worker is `Good`
(`good_of_run`): a non-zero lock promise (*acquire-kind*: only an `xchgl`
fulfils it) makes it pre-acquire, and every promise of `0` to the lock (a
release promise) lies above every acquire-kind promise (the `xchgl` raises the
coherence view of the lock to the fulfilled promise; a fulfilment lies above
it). A failing `xchgl` writes too, so fulfilling an acquire-kind promise need
not acquire; it does when the promise is *pinned* (`AcqAt`), by atomicity
(`SpinSemSwpSolo.read_zero_gap`).

`step_solo` also classifies what a step does to the lock (`Eff`), and
`dropBounded_of_sinv` gives the drop bound (one promise per instruction).
-/
import Kraken.Promising.LiveSpinX64XchgInv
import Kraken.Promising.LiveSpinX64SemShape
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Live.SpinX64SemXchgSolo

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinX64Step
open Kraken.Promising.Live.SemShape Kraken.Promising.Live.Sem Kraken.Promising.Live.TsoRmw
open Kraken.Promising.Live.X64SemShape Kraken.Promising.Live.SpinX64SemShape
open Kraken.Promising.Live.SpinX64XchgInv (Static Holder holder_of_pc not_holder_of_pc stepOne_end LkL CtL s1 s_test
  s_jne s8 s9 s12)
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV spinWorkerV symV)
open Kraken.Promising.Live.SpinSemSwpSolo (ZeroAt ZNot Gap TopZ read_le read_zero_gap writeIn_le)

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

variable {I : ISA}

/-! ## Choices replay (`SpinX64SemShape.replay_choose`) -/

section Replay

variable (A : Arch) (tid : Nat) {t : Thread I} {mem0 mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A choice of register-only outcomes replays against a larger memory**
(`SpinX64SemShape.replay_choose`). -/
theorem replay_choose (hs : stepOne A t tid mem0 = some outs) (ho : .ok o ∈ outs) (hm : o.mem = mem0) {n : Nat}
    {f : Fin n → I.State} (hex : I.exec t.st = some (.choose n fun i => .done (f i))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem :=
  SpinX64SemShape.replay_choose A tid hs ho hm hex

end Replay

/-! ## A fencing RMW reads below its coherence bound -/

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A fencing RMW reads below its coherence bound** (the `writeIn` clause
that `SpinX64SemShape.spec_rmwo_p_tso` does not state; the TSO twin of
`SpinSemSwpSolo.spec_load_w`). A hoist candidate. -/
theorem spec_rmw_w_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧ mem.writeIn l tr (t.views.getCoh l) = false := by
  obtain ⟨tree, c', hex', hr, -, -, -, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  obtain ⟨tr', old', hx', -, hrd, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  rw [fence_mem] at hrd hw
  rw [fence_getCoh] at hw
  refine ⟨tr, old, ?_, hrd, writeIn_le hw (Nat.le_max_right _ _)⟩
  cases hop : op old with
  | none => simp only [hop] at h; exact (run_done A tid (instrViews t (I.deps t.st)) h).1
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, -, h⟩ := h
    exact (run_done A tid (instrViews t (I.deps t.st)) h).1

end Spec

/-! ## Smaller memories (the layout-free `SpinSemSwpSolo.zeroAt_back` etc.) -/

section Back

variable {l : Loc} {mem mem' : Memory}

theorem zeroAt_back {z : Time} (hp : mem.Prefix mem') (hz : z ≤ mem.last) (h : ZeroAt l mem' z) :
    ZeroAt l mem z := SpinSemSwpSolo.zeroAt_back hp hz h

theorem zNot_back {z : Time} {tid : Nat} (hp : mem.Prefix mem') (hz : z ≤ mem.last) (h : ZNot mem' z tid) :
    ZNot mem z tid := SpinSemSwpSolo.zNot_back hp hz h

theorem topZ_back {z : Time} (hp : mem.Prefix mem') (h : TopZ l mem' z) : TopZ l mem z :=
  SpinSemSwpSolo.topZ_back hp h

theorem gap_back {z m : Time} (hp : mem.Prefix mem') (h : Gap l mem' z m) : Gap l mem z m :=
  SpinSemSwpSolo.gap_back hp h

end Back

/-! ## Positions and predicates -/

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-- `movl $1,%eax` (position 4), with the value it sets (the existing
`SpinX64XchgTrees.exec_mov1` does not expose it). -/
theorem exec_mov1' (st : State) (h : At st 4) :
    ∃ md : MachineData, md.dmem = st.st.1.dmem ∧ eax md = 1#32 ∧
      isa.exec st = some (.done (goto st md (pcA 5))) := by
  rw [show pcA 5 = st.st.2 + .ofNat (Kraken.Layout.size Directive 4) by rw [h.pc]; exact addrOf_step (by decide)]
  refine ⟨_, ?_, ?_, by x64cell h 4 spinImageV [spinImageV, spinWorkerV] [label_worker, label_done]; rfl⟩
  · rfl
  have := eax_set64 st.st.1.regs 1#32
  rw [show BitVec.setWidth 64 (1#32) = 1#64 by decide] at this
  exact this

/-- **The promise-agnostic per-thread invariant**: `Static`, a pc in
`spPcs`, and `%eax`'s low word `1` at the `xchgl`. -/
structure SInv (s : isa.State) : Prop where
  st : Static s
  pc : ∃ i ∈ spPcs, s.st.2 = pcA i
  eax1 : s.st.2 = pcA 5 → eax s.st.1 = 1#32

/-- **Pre-acquire**: in the test-and-test-and-set loop (positions 1–7), not
holding the lock. -/
def PreAcq (t : Thread isa) : Prop := (∀ i ∈ spPcs, t.st.st.2 = pcA i → i ≤ 7) ∧ ¬ Holder t

/-- Past the release (positions 12 and 13). -/
def Past (t : Thread isa) : Prop := t.st.st.2 = pcA 12 ∨ t.st.st.2 = pcA 13

/-- The value an `xchgl` writes (`%eax`'s low word `1`, zero-extended). -/
abbrev v1 : Val := BitVec.setWidth 128 (1#32)

theorem v1_ne : v1 ≠ 0 := by decide

/-- Every promise of `tid` is a message of its own in memory. -/
def PromIn (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.tid = tid

/-- Every promise lies above the thread's coherence view of its location
(`Sem.coh_lt_of_certOkN`). -/
def CohLt (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts

/-- **What a certifiable worker's promises satisfy**: an acquire-kind
(non-zero) lock promise makes it pre-acquire; a release (zero) lock promise
lies above every acquire-kind one. -/
structure Good (t : Thread isa) (mem : Memory) : Prop where
  acq : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = LkL → w.val ≠ 0 → PreAcq t
  rel : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = LkL → w.val = 0 →
    ∀ a ∈ t.prom, ∀ wa, mem.get? a = some wa → wa.loc = LkL → wa.val ≠ 0 → a < ts

theorem good_nil {t : Thread isa} {mem : Memory} (h : t.prom = []) : Good t mem :=
  ⟨fun ts hts => (by rw [h] at hts; cases hts), fun ts hts => (by rw [h] at hts; cases hts)⟩

/-- `Good` for a thread without acquire-kind promises. -/
theorem good_of_noAcq {t : Thread isa} {mem : Memory}
    (h : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = LkL → w.val ≠ 0 → False) : Good t mem :=
  ⟨fun ts hts w hw hl hv => (h ts hts w hw hl hv).elim,
    fun _ _ _ _ _ _ a ha wa hwa hla hva => (h a ha wa hwa hla hva).elim⟩

local macro "mems" h:ident : tactic =>
  `(tactic| simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at $h:ident)

theorem holder_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (hpc : t.st.st.2 = pcA p) :
    Holder t ↔ (p = 6 ∧ eax t.st.st.1 = 0#32) ∨ (p = 7 ∧ t.st.st.1.status.zf = true) ∨ p ∈ [8, 9, 10, 11] := by
  constructor
  · rintro (⟨h, hz⟩ | ⟨h, hz⟩ | h)
    · exact .inl ⟨addrOf_inj hp (by decide) (hpc.symm.trans h), hz⟩
    · exact .inr (.inl ⟨addrOf_inj hp (by decide) (hpc.symm.trans h), hz⟩)
    · right; right
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;>
        · obtain rfl := addrOf_inj hp (by decide) (hpc.symm.trans h); decide
  · rintro (⟨rfl, hz⟩ | ⟨rfl, hz⟩ | h)
    · exact .inl ⟨hpc, hz⟩
    · exact .inr (.inl ⟨hpc, hz⟩)
    · exact holder_of_pc h hpc

theorem preAcq_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (hpc : t.st.st.2 = pcA p) :
    PreAcq t ↔ p ≤ 7 ∧ ¬ (p = 6 ∧ eax t.st.st.1 = 0#32) ∧ ¬ (p = 7 ∧ t.st.st.1.status.zf = true) := by
  unfold PreAcq
  rw [holder_iff hp hpc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1 p hp hpc, fun h => h2 (.inl h), fun h => h2 (.inr (.inl h))⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i hi hi' => by rw [addrOf_inj hi hp (hi'.symm.trans hpc)]; exact h1, ?_⟩
    rintro (h | h | h)
    · exact h2 h
    · exact h3 h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem past_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (hpc : t.st.st.2 = pcA p) : Past t ↔ 12 ≤ p := by
  unfold Past
  rw [hpc]
  constructor
  · rintro (h | h)
    · obtain rfl := addrOf_inj hp (by decide) h; decide
    · obtain rfl := addrOf_inj hp (by decide) h; decide
  · intro h; mems hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
    · exact .inl rfl
    · exact .inr rfl

theorem not_past_of_preAcq {t : Thread isa} (h : PreAcq t) : ¬ Past t := by
  rintro (e | e)
  · exact absurd (h.1 12 (by decide) e) (by decide)
  · exact absurd (h.1 13 (by decide) e) (by decide)

/-! ## The steps with promises -/

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : SInv t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The `xchgl` (position 5), with any promise set: an atomic read, then an
append of `1` (raising `vwOld` and the coherence view of the lock past it) or
the release fulfilment of an outstanding promise of `1` above the coherence
view and `vwOld`. -/
theorem s5p (hpc : t.st.st.2 = pcA 5) :
    ∃ tr old md, md.dmem = t.st.st.1.dmem ∧ eax md = BitVec.setWidth 32 old ∧
      oc.thread.st = goto t.st md (pcA 6) ∧ mem.read? LkL tr = some old ∧
      ((oc.mem = (mem.append { loc := LkL, val := v1, tid }).1 ∧
        oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld ∧
        mem.last + 1 ≤ oc.thread.views.getCoh LkL ∧ mem.atomic LkL tid tr (mem.last + 1) = true) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some { loc := LkL, val := v1, tid } ∧ t.views.getCoh LkL < ts ∧
        t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧
        t.views.vwOld ≤ oc.thread.views.vwOld ∧ ts ≤ oc.thread.views.getCoh LkL ∧ tr < ts ∧
        mem.atomic LkL tid tr ts = true)) := by
  obtain ⟨g, hg, hex⟩ := exec_xchg _ (hS.st.at (by decide) (by decide) hpc) hS.st.dl
  rw [hS.eax1 hpc] at hex
  obtain ⟨tr, old, hst, hrd, -, hcase⟩ := spec_rmwo_p_tso _ _ rfl hex hs ho
  refine ⟨tr, old, g old, (hg old).1, (hg old).2, hst, hrd, ?_⟩
  rcases hcase with ⟨h1, -⟩ | ⟨new, h1, ⟨e1, e2, e3, -, e5, e6⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩⟩
  · cases h1
  · cases h1; exact .inl ⟨e1, e2, e3 (by decide), e5, e6⟩
  · cases h1; exact .inr ⟨ts, hts, e1, e2, e3 (by decide), e4, e5, e6, e7, e8, e9⟩

/-- The counter store (position 10), with any promise set. -/
theorem s10p (hpc : t.st.st.2 = pcA 10) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = goto t.st md (pcA 11) ∧
      ((∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1 ∧
        oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
       (∃ ts ∈ t.prom, (∃ w, mem.get? ts = some w ∧ w.loc = CtL) ∧ t.views.vwOld < ts ∧ oc.mem = mem ∧
        oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld)) := by
  obtain ⟨v, md, hd, hex⟩ := exec_stc _ (hS.st.at (by decide) (by decide) hpc) hS.st.dc
  obtain ⟨hst, h⟩ := spec_store_p _ _ hex hs ho
  refine ⟨md, hd, hst, ?_⟩
  rcases h with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, -, e3, e4, e5, e6⟩
  · exact .inl ⟨v, e1, e2, e3 (by decide)⟩
  · exact .inr ⟨ts, hts, ⟨_, e1, rfl⟩, e3 (by decide), e4, e5, e6⟩

/-- The release (position 11), with any promise set: a fulfilment is above
the coherence view and `vwOld`. -/
theorem s11p (hpc : t.st.st.2 = pcA 11) :
    oc.thread.st = goto t.st t.st.st.1 (pcA 12) ∧
      ((oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1 ∧
        oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some { loc := LkL, val := 0#128, tid } ∧ t.views.getCoh LkL < ts ∧
        t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧
        t.views.vwOld ≤ oc.thread.views.vwOld)) := by
  obtain ⟨hst, h⟩ := spec_store_p _ _ (exec_unlock _ (hS.st.at (by decide) (by decide) hpc) hS.st.dl) hs ho
  refine ⟨hst, ?_⟩
  rcases h with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6⟩
  · exact .inl ⟨e1, e2, e3 (by decide)⟩
  · exact .inr ⟨ts, hts, e1, e2, e3 (by decide), e4, e5, e6⟩

end Steps

/-! ## One step: `SInv`, `TsoW` and the drop bound -/

theorem len_fresh (p : List Time) (n : Time) : p.length ≤ ((p ++ [n]).erase n).length + 1 := by
  rw [List.length_erase]; simp

theorem len_erase {p : List Time} (ts : Time) : p.length ≤ (p.erase ts).length + 1 := by
  rw [List.length_erase]; split <;> omega

/-- **One step keeps `SInv`, satisfies the TSO write discipline `TsoW` (for
promises within memory), and drops at most one promise**, against any
memory. -/
theorem step_sinv {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv t.st)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv oc.thread.st ∧ ((∀ ts ∈ t.prom, ts ≤ mem.last) → TsoW t mem oc) ∧
      t.prom.length ≤ oc.thread.prom.length + 1 := by
  have hSt := hS.st
  obtain ⟨p, hp, hpc⟩ := hS.pc
  have g : ∀ {m : MachineData} {q : Nat}, oc.thread.st = goto t.st m (pcA q) → q ∈ spPcs →
      m.dmem = t.st.st.1.dmem → (q = 5 → eax m = 1#32) → SInv oc.thread.st := fun hst hq hd h5 =>
    ⟨by rw [hst]; exact hSt.goto _ _ hd, ⟨_, hq, by rw [hst]⟩,
      fun e => by rw [hst] at e ⊢; exact h5 (addrOf_inj hq (by decide) e)⟩
  have q : SInv oc.thread.st → oc.mem = mem → oc.thread.prom = t.prom →
      oc.thread.views.vwOld = t.views.vwOld →
      SInv oc.thread.st ∧ ((∀ ts ∈ t.prom, ts ≤ mem.last) → TsoW t mem oc) ∧
        t.prom.length ≤ oc.thread.prom.length + 1 := fun h hm hpr hvw =>
    ⟨h, fun hle => tsoW_same hle hm hpr hvw, by rw [hpr]; exact Nat.le_succ _⟩
  have hp' := hp
  mems hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g', -, hex⟩ := exec_ldl _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    obtain ⟨ts, v, md, hd, -, hst, -, hm, hpr, -, -⟩ := s1 hSt hs ho hpc
    exact q (g hst (by decide) hd (fun h => absurd h (by decide))) hm hpr (spec_load_vw _ _ hex hs ho)
  · obtain ⟨g', -, hex⟩ := exec_test _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)
    obtain ⟨md, hd, -, hst, hm, hpr, -⟩ := s_test hSt hs ho (.inl rfl) hpc
    exact q (g hst (by decide) hd (fun h => absurd h (by decide))) hm hpr (spec_choose_vw _ _ hex hs ho)
  · have hex := exec_jne _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s_jne hSt hs ho (.inl rfl) hpc
    have hvw := spec_done_vw _ _ hex hs ho
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst; exact q (g hst (by decide) rfl (fun h => absurd h (by decide))) hm hpr hvw
    · rw [ite_eq_right hz] at hst; exact q (g hst (by decide) rfl (fun h => absurd h (by decide))) hm hpr hvw
  · obtain ⟨md, hd, h1, hex⟩ := exec_mov1' _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    exact q (g hst (by decide) hd fun _ => h1) hm hpr (spec_done_vw _ _ hex hs ho)
  · obtain ⟨tr, old, md, hd, -, hst, -, h⟩ := s5p hS hs ho hpc
    refine ⟨g hst (by decide) hd (fun h => absurd h (by decide)), ?_⟩
    rcases h with ⟨hm, hpr, hvw, -⟩ | ⟨ts, -, -, -, hvt, hm, hpr, hvw, -⟩
    · exact ⟨fun hle => tsoW_fresh hle hm hpr hvw, by rw [hpr]; exact len_fresh _ _⟩
    · exact ⟨fun hle => tsoW_ful hle hm hpr hvt hvw, by rw [hpr]; exact len_erase ts⟩
  · obtain ⟨g', -, hex⟩ := exec_test _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)
    obtain ⟨md, hd, -, hst, hm, hpr, -⟩ := s_test hSt hs ho (.inr rfl) hpc
    exact q (g hst (by decide) hd (fun h => absurd h (by decide))) hm hpr (spec_choose_vw _ _ hex hs ho)
  · have hex := exec_jne _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s_jne hSt hs ho (.inr rfl) hpc
    have hvw := spec_done_vw _ _ hex hs ho
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst; exact q (g hst (by decide) rfl (fun h => absurd h (by decide))) hm hpr hvw
    · rw [ite_eq_right hz] at hst; exact q (g hst (by decide) rfl (fun h => absurd h (by decide))) hm hpr hvw
  · obtain ⟨g', -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    obtain ⟨md, hd, hst, hm, hpr, -⟩ := s8 hSt hs ho hpc
    exact q (g hst (by decide) hd (fun h => absurd h (by decide))) hm hpr (spec_load_vw _ _ hex hs ho)
  · obtain ⟨md, -, hex⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨md', hd, hst, hm, hpr, -⟩ := s9 hSt hs ho hpc
    exact q (g hst (by decide) hd (fun h => absurd h (by decide))) hm hpr (spec_done_vw _ _ hex hs ho)
  · obtain ⟨md, hd, hst, h⟩ := s10p hS hs ho hpc
    refine ⟨g hst (by decide) hd (fun h => absurd h (by decide)), ?_⟩
    rcases h with ⟨v, hm, hpr, hvw⟩ | ⟨ts, -, -, hvt, hm, hpr, hvw⟩
    · exact ⟨fun hle => tsoW_fresh hle hm hpr hvw, by rw [hpr]; exact len_fresh _ _⟩
    · exact ⟨fun hle => tsoW_ful hle hm hpr hvt hvw, by rw [hpr]; exact len_erase ts⟩
  · obtain ⟨hst, h⟩ := s11p hS hs ho hpc
    refine ⟨g hst (by decide) rfl (fun h => absurd h (by decide)), ?_⟩
    rcases h with ⟨hm, hpr, hvw⟩ | ⟨ts, -, -, -, hvt, hm, hpr, hvw⟩
    · exact ⟨fun hle => tsoW_fresh hle hm hpr hvw, by rw [hpr]; exact len_fresh _ _⟩
    · exact ⟨fun hle => tsoW_ful hle hm hpr hvt hvw, by rw [hpr]; exact len_erase ts⟩
  · have hex := exec_jmp _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s12 hSt hs ho hpc
    exact q (g hst (by decide) rfl (fun h => absurd h (by decide))) hm hpr (spec_done_vw _ _ hex hs ho)
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-! ## Pinned promises; larger and smaller memories -/

/-- **A pinned acquire-kind promise** `m` of `tid`: a non-zero lock message
above a zero `z` of the lock that `tid` did not write, with no lock write
strictly between. Its fulfilment reads `z`, so it acquires. -/
structure AcqAt (tid : Nat) (t : Thread isa) (mem : Memory) (m z : Time) : Prop where
  prom : m ∈ t.prom
  msg : ∃ w, mem.get? m = some w ∧ w.loc = LkL ∧ w.val ≠ 0
  lt : z < m
  zero : ZeroAt LkL mem z
  znot : ZNot mem z tid
  gap : Gap LkL mem z m

theorem PromIn.get {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem)
    {ts : Time} (hts : ts ∈ t.prom) : mem'.get? ts = mem.get? ts := by
  obtain ⟨w, hw, -⟩ := h ts hts
  exact hp.get? (mem.last_le_of_get?_eq_some hw)

theorem PromIn.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem') (h : PromIn tid t mem) :
    PromIn tid t mem' := fun ts hts => by rw [h.get hp hts]; exact h ts hts

theorem PromIn.le {tid : Nat} {t : Thread isa} {mem : Memory} (h : PromIn tid t mem) : ∀ ts ∈ t.prom, ts ≤ mem.last :=
  fun ts hts => let ⟨_, hw, _⟩ := h ts hts; mem.last_le_of_get?_eq_some hw

theorem AcqAt.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} {m z : Time}
    (hp : mem.Prefix mem') (h : AcqAt tid t mem m z) : AcqAt tid t mem' m z := by
  obtain ⟨w, hw, h2⟩ := h.msg
  have hm := mem.last_le_of_get?_eq_some hw
  exact ⟨h.prom, ⟨w, by rw [hp.get? hm]; exact hw, h2⟩, h.lt, h.zero.mono hp, h.znot.mono hp,
    h.gap.mono hp (by omega_t)⟩

theorem AcqAt.of_prom {tid : Nat} {t t' : Thread isa} {mem : Memory} {m z : Time}
    (h : AcqAt tid t mem m z) (hm : m ∈ t'.prom) : AcqAt tid t' mem m z :=
  ⟨hm, h.msg, h.lt, h.zero, h.znot, h.gap⟩

theorem AcqAt.back {tid : Nat} {t : Thread isa} {mem mem' : Memory} {m z : Time}
    (hp : mem.Prefix mem') (hP : PromIn tid t mem) (h : AcqAt tid t mem' m z) : AcqAt tid t mem m z := by
  have hm := hP.le m h.prom
  have hlt := h.lt
  obtain ⟨w, hw, h2⟩ := h.msg
  exact ⟨h.prom, ⟨w, by rw [← hp.get? hm]; exact hw, h2⟩, h.lt, zeroAt_back hp (by omega_t) h.zero,
    zNot_back hp (by omega_t) h.znot, gap_back hp h.gap⟩

theorem Good.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : Good t mem) : Good t mem' :=
  ⟨fun ts hts w hw => h.acq ts hts w (by rw [← hP.get hp hts]; exact hw),
    fun ts hts w hw hl hv a ha wa hwa => h.rel ts hts w (by rw [← hP.get hp hts]; exact hw) hl hv a ha wa
      (by rw [← hP.get hp ha]; exact hwa)⟩

/-! ## One step of a worker alone -/

/-- **What an instruction step does to the lock.** -/
inductive Eff (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; its promises are kept; a holder stays one. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1)
      (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = LkL → ts ∈ oc.thread.prom)
      (hh : Holder t → Holder oc.thread)
  /-- An `xchgl` appending `1`; it acquires if it follows a zero it did not
  write. -/
  | swpFresh (hm : oc.mem = (mem.append { loc := LkL, val := v1, tid }).1) (hpr : oc.thread.prom = t.prom)
      (hpre : PreAcq t) (hc : mem.last + 1 ≤ oc.thread.views.getCoh LkL)
      (hz : ∀ z, ZeroAt LkL mem z → ZNot mem z tid → z < mem.last + 1 → Gap LkL mem z (mem.last + 1) →
        Holder oc.thread)
  /-- An `xchgl` fulfilling an acquire-kind promise; it acquires if the
  promise is pinned. -/
  | swpFul (ts : Time) (hts : ts ∈ t.prom) (hw : mem.get? ts = some { loc := LkL, val := v1, tid })
      (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts) (hpre : PreAcq t)
      (hc : ts ≤ oc.thread.views.getCoh LkL)
      (hz : ∀ z, ZeroAt LkL mem z → ZNot mem z tid → z < ts → Gap LkL mem z ts → Holder oc.thread)
  /-- The release appending `0`. -/
  | relFresh (hm : oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1) (hh : Holder t)
      (hpast : Past oc.thread)
  /-- The release fulfilling a release promise, above the coherence view. -/
  | relFul (ts : Time) (hts : ts ∈ t.prom) (hw : mem.get? ts = some { loc := LkL, val := 0#128, tid })
      (hc : t.views.getCoh LkL < ts) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts)
      (hh : Holder t) (hpast : Past oc.thread)

/-- The results of one step of a worker, with any promises. -/
structure SoloRes (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop where
  sinv : SInv oc.thread.st
  promIn : PromIn tid oc.thread oc.mem
  back : Good oc.thread oc.mem → CohLt oc.thread oc.mem → Good t mem
  past : Past t → Past oc.thread
  eff : Eff tid t mem oc

/-- **One step of a worker alone**, position by position. -/
theorem step_solo {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hlc : LkL ≠ CtL)
    (hS : SInv t.st) (hP : PromIn tid t mem)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) : SoloRes tid t mem oc := by
  have hsi := (step_sinv hS hs ho).1
  have hSt := hS.st
  obtain ⟨p, hp, hpc⟩ := hS.pc
  have hPl := hP.le
  have quiet : ∀ q ∈ spPcs, oc.thread.st.st.2 = pcA q → (12 ≤ p → 12 ≤ q) → oc.mem = mem →
      oc.thread.prom = t.prom → (PreAcq oc.thread ↔ PreAcq t) → (Holder t → Holder oc.thread) →
      SoloRes tid t mem oc := by
    intro q hq hqc h12 hm hpr hpa hh
    have hg : ∀ {ts w}, mem.get? ts = some w → oc.mem.get? ts = some w := fun h => by rw [hm]; exact h
    have hi : ∀ {ts}, ts ∈ t.prom → ts ∈ oc.thread.prom := fun h => by rw [hpr]; exact h
    refine ⟨hsi, fun ts hts => by rw [hm]; exact hP ts (hpr ▸ hts), fun hgd _ =>
      ⟨fun ts hts w hw hl hv => hpa.mp (hgd.acq ts (hi hts) w (hg hw) hl hv),
       fun ts hts w hw hl hv a ha wa hwa hla hva => hgd.rel ts (hi hts) w (hg hw) hl hv a (hi ha) wa (hg hwa) hla hva⟩,
      fun h => (past_iff hq hqc).mpr (h12 ((past_iff hp hpc).mp h)),
      .quiet (.inl hm) (fun ts hts _ _ _ => hi hts) hh⟩
  have hp' := hp
  mems hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `movl (lock),%eax`
    obtain ⟨ts, v, md, hd, -, hst, -, hm, hpr, -, -⟩ := s1 hSt hs ho hpc
    exact quiet 2 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 2) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp)
      (fun h => by have := (holder_iff hp hpc).mp h; simp at this)
  · -- 2: `testl`
    obtain ⟨md, hd, -, hst, hm, hpr, -⟩ := s_test hSt hs ho (.inl rfl) hpc
    exact quiet 3 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 3) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp)
      (fun h => by have := (holder_iff hp hpc).mp h; simp at this)
  · -- 3: `jne worker`
    obtain ⟨hm, hst, hpr, -⟩ := s_jne hSt hs ho (.inl rfl) hpc
    have nh : ¬ Holder t := fun h => by have := (holder_iff hp hpc).mp h; simp at this
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      exact quiet 4 (by decide) (by rw [hst]) (by omega) hm hpr
        (by rw [preAcq_iff (p := 4) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp) (fun h => absurd h nh)
    · rw [ite_eq_right hz] at hst
      exact quiet 1 (by decide) (by rw [hst]) (by omega) hm hpr
        (by rw [preAcq_iff (p := 1) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp) (fun h => absurd h nh)
  · -- 4: `movl $1,%eax`
    obtain ⟨md, hd, -, hex⟩ := exec_mov1' _ (hSt.at (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := spec_done _ _ hex hs ho
    exact quiet 5 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 5) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp)
      (fun h => by have := (holder_iff hp hpc).mp h; simp at this)
  · -- 5: `xchgl`
    have hpre : PreAcq t := (preAcq_iff hp hpc).mpr (by simp)
    obtain ⟨tr, old, md, hd, hz, hst, hrd, hcase⟩ := s5p hS hs ho hpc
    have hho : old = 0 → Holder oc.thread := fun e =>
      .inl ⟨by rw [hst], by rw [hst]; show eax md = 0#32; rw [hz, e]; decide⟩
    have hzg : ∀ {m : Time}, mem.atomic LkL tid tr m = true → tr < m → ∀ z, ZeroAt LkL mem z →
        ZNot mem z tid → z < m → Gap LkL mem z m → Holder oc.thread :=
      fun ha htr z h1 h2 h3 h4 => hho (read_zero_gap hrd ha htr h1 h2 h3 h4)
    have hpast : Past t → Past oc.thread := fun h => absurd ((past_iff hp hpc).mp h) (by decide)
    rcases hcase with ⟨hm, hpr, -, hco, ha⟩ | ⟨ts, hts, hw, -, -, hm, hpr, -, hco, htr, ha⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), fun _ hcl => ?_, hpast,
        .swpFresh hm hpr' hpre hco (hzg ha (Nat.lt_succ_of_le (read_le hrd)))⟩
      refine ⟨fun _ _ _ _ _ _ => hpre, fun ts hts w hw hl _ _ _ _ _ _ _ => ?_⟩
      have := hcl ts (by rw [hpr']; exact hts) w (by rw [hgm ts hts]; exact hw)
      rw [hl] at this
      have := hPl ts hts
      omega_t
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')), fun hg hcl => ?_,
        hpast, .swpFul ts hts hw hm hpr hpre hco (hzg ha htr)⟩
      rw [hm] at hg hcl
      refine ⟨fun _ _ _ _ _ _ => hpre, fun ts' hts' w' hw' hl' hv' a ha' wa hwa hla hva => ?_⟩
      have hne : ts' ≠ ts := fun e => by subst e; rw [hw] at hw'; cases hw'; exact v1_ne hv'
      by_cases e : a = ts
      · subst e
        have := hcl ts' (hin ts' hts' hne) w' hw'
        rw [hl'] at this
        omega_t
      · exact hg.rel ts' (hin ts' hts' hne) w' hw' hl' hv' a (hin a ha' e) wa hwa hla hva
  · -- 6: `testl`
    obtain ⟨md, hd, hz, hst, hm, hpr, -⟩ := s_test hSt hs ho (.inr rfl) hpc
    refine quiet 7 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 7) (by decide) (by rw [hst]), preAcq_iff hp hpc, hst]; simp [hz]) fun hh => ?_
    rcases (holder_iff hp hpc).mp hh with ⟨-, he⟩ | ⟨e, -⟩ | e
    · exact .inr (.inl ⟨by rw [hst], by rw [hst]; exact hz.mpr he⟩)
    · omega
    · simp at e
  · -- 7: `jne worker`
    obtain ⟨hm, hst, hpr, -⟩ := s_jne hSt hs ho (.inr rfl) hpc
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      exact quiet 8 (by decide) (by rw [hst]) (by omega) hm hpr
        (by rw [preAcq_iff (p := 8) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [hz])
        (fun _ => holder_of_pc (p := 8) (by decide) (by rw [hst]))
    · rw [ite_eq_right hz] at hst
      exact quiet 1 (by decide) (by rw [hst]) (by omega) hm hpr
        (by rw [preAcq_iff (p := 1) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [hz])
        (fun h => by have := (holder_iff hp hpc).mp h; simp [hz] at this)
  · -- 8: `movl (counter),%ecx`
    obtain ⟨md, hd, hst, hm, hpr, -⟩ := s8 hSt hs ho hpc
    exact quiet 9 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 9) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp)
      (fun _ => holder_of_pc (p := 9) (by decide) (by rw [hst]))
  · -- 9: `addl`
    obtain ⟨md, hd, hst, hm, hpr, -⟩ := s9 hSt hs ho hpc
    exact quiet 10 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 10) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp)
      (fun _ => holder_of_pc (p := 10) (by decide) (by rw [hst]))
  · -- 10: the counter store
    obtain ⟨md, hd, hst, hcase⟩ := s10p hS hs ho hpc
    have hho : Holder oc.thread := holder_of_pc (p := 11) (by decide) (by rw [hst])
    have hnpo : ¬ PreAcq oc.thread := fun h =>
      absurd ((preAcq_iff (p := 11) (by decide) (by rw [hst])).mp h).1 (by decide)
    have hpast : Past t → Past oc.thread := fun h => absurd ((past_iff hp hpc).mp h) (by decide)
    rcases hcase with ⟨v, hm, hpr, -⟩ | ⟨ts, hts, ⟨wc, hwc, hlc'⟩, -, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      exact ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun hg _ => good_of_noAcq fun a ha wa hwa hla hva =>
          hnpo (hg.acq a (by rw [hpr']; exact ha) wa (by rw [hgm a ha]; exact hwa) hla hva),
        hpast, .quiet (.inr ⟨v, hm⟩) (fun ts hts _ _ _ => by rw [hpr']; exact hts) (fun _ => hho)⟩
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      have hnl : ∀ ts' ∈ t.prom, ∀ w, mem.get? ts' = some w → w.loc = LkL → ts' ∈ oc.thread.prom :=
        fun ts' h' w hw hl => hin ts' h' fun e => by
          subst e; rw [hwc] at hw; cases hw; exact hlc (hl.symm.trans hlc')
      exact ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun hg _ => good_of_noAcq fun a ha wa hwa hla hva =>
          hnpo (hg.acq a (hnl a ha wa hwa hla) wa (by rw [hm]; exact hwa) hla hva),
        hpast, .quiet (.inl hm) hnl (fun _ => hho)⟩
  · -- 11: the release
    obtain ⟨hst, hcase⟩ := s11p hS hs ho hpc
    have hht : Holder t := holder_of_pc (p := 11) (by decide) hpc
    have hpo : Past oc.thread := .inl (by rw [hst])
    have hnpo : ¬ PreAcq oc.thread := fun h => not_past_of_preAcq h hpo
    rcases hcase with ⟨hm, hpr, -⟩ | ⟨ts, hts, hw, hco, -, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      exact ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun hg _ => good_of_noAcq fun a ha wa hwa hla hva =>
          hnpo (hg.acq a (by rw [hpr']; exact ha) wa (by rw [hgm a ha]; exact hwa) hla hva),
        fun _ => hpo, .relFresh hm hht hpo⟩
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      have hna : ∀ a ∈ t.prom, ∀ wa, mem.get? a = some wa → wa.val ≠ 0 → a ∈ oc.thread.prom :=
        fun a ha wa hwa hva => hin a ha fun e => by subst e; rw [hw] at hwa; cases hwa; exact hva rfl
      exact ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun hg _ => good_of_noAcq fun a ha wa hwa hla hva =>
          hnpo (hg.acq a (hna a ha wa hwa hva) wa (by rw [hm]; exact hwa) hla hva),
        fun _ => hpo, .relFul ts hts hw hco hm hpr hht hpo⟩
  · -- 12: `jmp done`
    obtain ⟨hm, hst, hpr, -⟩ := s12 hSt hs ho hpc
    exact quiet 13 (by decide) (by rw [hst]) (by omega) hm hpr
      (by rw [preAcq_iff (p := 13) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp)
      (fun h => by have := (holder_iff hp hpc).mp h; simp at this)
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-! ## Along a run -/

section Run

variable {tid : Nat} (hlc : LkL ≠ CtL)

include hlc

/-- **A certifiable worker is `Good`.** -/
theorem good_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.tso tid n p q → q.1.prom = [] →
    SInv p.1.st → PromIn tid p.1 p.2 → Good p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _; exact good_nil hq
  | step hs h ih =>
    intro hq hS hP
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have r := step_solo hlc hS hP hs ho
    exact r.back (ih hq r.sinv r.promIn) fun _ hts _ hw => coh_lt_of_certOkN ⟨_, _, h, hq⟩ hts hw

theorem good_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.tso tid t mem fuel)
    (hS : SInv t.st) (hP : PromIn tid t mem) : Good t mem :=
  let ⟨_, _, hr, hp⟩ := h; good_of_run hlc hr hp hS hP

end Run

/-- **On TSO a certifiable worker certifies without fresh writes**
(`SpinX64SemShape.nacertG_of_tsoW` with `step_sinv`). -/
theorem nacert_of_certOkN {fuel tid : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.tso tid t mem fuel)
    (hS : SInv t.st) (hle : ∀ ts ∈ t.prom, ts ≤ mem.last) : NACertG Arch.tso fuel tid t mem :=
  nacertG_of_tsoW SInv (fun hI hle hs ho => ⟨(step_sinv hI hs ho).1, (step_sinv hI hs ho).2.1 hle⟩) h hS hle

/-! ## Replay and enabledness -/

/-- **A step that keeps memory replays against a larger memory.** -/
theorem replay_x {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.tso t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.tso t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  have hSt := hS.st
  obtain ⟨p, hpp, hpc⟩ := hS.pc
  mems hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, hex⟩ := exec_ldl _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    exact replay_load _ _ hp hb hs ho hm hex
  · obtain ⟨g, -, hex⟩ := exec_test _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)
    exact replay_choose _ _ hs ho hm hex
  · exact replay_done _ _ hp hb hs ho hm (exec_jne _ (.inl rfl) (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨md, -, hex⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · obtain ⟨g, -, hex⟩ := exec_xchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    exact replay_rmwo_tso _ _ hp hb hs ho hm rfl hex
  · obtain ⟨g, -, hex⟩ := exec_test _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)
    exact replay_choose _ _ hs ho hm hex
  · exact replay_done _ _ hp hb hs ho hm (exec_jne _ (.inr rfl) (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨g, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact replay_load _ _ hp hb hs ho hm hex
  · obtain ⟨md, -, hex⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · obtain ⟨v, md, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact replay_store _ _ hp hb hs ho hm hex
  · exact replay_store _ _ hp hb hs ho hm (exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (exec_jmp _ (hSt.at (by decide) (by decide) hpc))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem nacert_replay {fuel tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    (h : NACertG Arch.tso fuel tid t mem0) (hS : SInv t.st) (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) :
    NACertG Arch.tso fuel tid t mem :=
  let ⟨t', hr, ht'⟩ := h
  ⟨t', nacertG_replay SInv (fun hI hs ho => (step_sinv hI hs ho).1)
    (fun hI hb hp hs ho hm => replay_x hI hb hp hs ho hm) hr rfl hS hb mem hp, ht'⟩

/-- **A worker that is not at its end and either has no promise or certifies
without fresh writes can take an instruction step** (semantic machine). -/
theorem instrEnabledSem_of {fuel tid : Nat} {cfg : Config isa} {t : Thread isa}
    (ht : cfg.threads[tid]? = some t) (hS : SInv t.st) (h13 : t.st.st.2 ≠ pcA 13)
    (hb : t.Bnd cfg.mem.last) (hn : t.prom = [] ∨ NACertG Arch.tso fuel tid t cfg.mem) :
    InstrEnabledSem Arch.tso fuel tid cfg := by
  refine instrEnabledSem_of_nacertG ht (fun hp0 => ?_) hn
  have fin : ∀ outs (oc : Outcome isa), stepOne Arch.tso t tid cfg.mem = some outs → .ok oc ∈ outs →
      oc.thread.prom = [] → InstrEnabledSem Arch.tso fuel tid cfg := fun _ _ h1 h2 h3 =>
    instrEnabledSem_of_step ht h1 h2 h3
  have dn : ∀ {s : isa.State}, isa.exec t.st = some (.done s) → InstrEnabledSem Arch.tso fuel tid cfg :=
    fun hex => let ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso tid hex (mem := cfg.mem); fin _ _ h1 h2 (h3.trans hp0)
  have ch : ∀ {f : Fin 2 → isa.State}, isa.exec t.st = some (.choose 2 fun i => .done (f i)) →
      InstrEnabledSem Arch.tso fuel tid cfg := fun hex =>
    let ⟨_, _, h1, h2, h3⟩ := en_choose Arch.tso tid (by decide) hex (mem := cfg.mem); fin _ _ h1 h2 (h3.trans hp0)
  have hSt := hS.st
  obtain ⟨p, hpp, hpc⟩ := hS.pc
  mems hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, hex⟩ := exec_ldl _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso tid hp0 hex (mem := cfg.mem)
    exact fin _ _ h1 h2 h3
  · exact ch (exec_test _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)).choose_spec.2
  · exact dn (exec_jne _ (.inl rfl) (hSt.at (by decide) (by decide) hpc))
  · exact dn (exec_mov1 _ (hSt.at (by decide) (by decide) hpc)).choose_spec.2
  · obtain ⟨g, -, hex⟩ := exec_xchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    obtain ⟨_, _, h1, h2, h3⟩ := en_rmwo_tso Arch.tso tid rfl hp0 hb hex
    exact fin _ _ h1 h2 h3
  · exact ch (exec_test _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)).choose_spec.2
  · exact dn (exec_jne _ (.inr rfl) (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨g, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso tid hp0 hex (mem := cfg.mem)
    exact fin _ _ h1 h2 h3
  · exact dn (exec_add _ (hSt.at (by decide) (by decide) hpc)).choose_spec.2
  · obtain ⟨v, md, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso tid hp0 hb hex
    exact fin _ _ h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso tid hp0 hb
      (exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl)
    exact fin _ _ h1 h2 h3
  · exact dn (exec_jmp _ (hSt.at (by decide) (by decide) hpc))
  · exact absurd hpc h13

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {tid : Nat} {p q : Thread isa × Memory} (h : ThreadNP Arch.tso tid p q)
    (hp : SInv p.1.st) : SInv q.1.st :=
  ThreadNP.stateInv SInv (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {tid : Nat} {t : Thread isa} (h : SInv t.st) : DropBounded Arch.tso 1 tid t :=
  dropBounded_of_stateInv SInv (fun h hs ho => ⟨(step_sinv h hs ho).1, (step_sinv h hs ho).2.2⟩) h

end Kraken.Promising.Live.SpinX64SemXchgSolo
