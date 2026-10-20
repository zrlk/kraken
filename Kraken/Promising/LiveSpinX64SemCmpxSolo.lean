/-
**Stage 3: solo runs of the x64 `lock cmpxchg`
spinlock worker with outstanding promises** (`spinlock_cmpxchg2/3.kl`,
`CmpxAbs.cmpxImageV`, valid layout, `Arch.tso`). The x64 counterpart of
`LiveSpinSemSolo.lean` (AArch64 CAS), simplified by TSO:

- **No fresh writes in a certification.** Every step of the worker satisfies
  `SpinX64SemShape.TsoW` (`step_sinv`): on TSO every store is a release and a
  fresh write raises `vwOld` past `|M|`. So a certifiable worker with
  promises certifies without fresh writes (`nacert_of_certOkN`, from the
  generic `SpinX64SemShape.nacertG_of_tsoW`), whatever its position. The
  AArch64 classes `NA` (not pre-acquire, or holding an acquire promise) are
  not needed.
- A worker writes the lock (`LkL`) at its `lock cmpxchg` (position 3: `%ecx`,
  which is `1`, iff it reads `%eax = 0`) and its release `movl $0,(lock)`
  (8), and the counter (`CtL`) at 7. Positions are visited in rank order
  (`rk`), except for the acquire loop (one rank). So a certifiable worker is
  `Good`: an *acquire* promise (lock, non-zero) only while pre-acquire
  (`PreAcq`), a counter promise up to position 7, a *release* promise (lock,
  `0`) up to position 8, and, while pre-acquire with any promise, an acquire
  promise (`Good.acq`: its no-fresh-write certification must pass the
  `lock cmpxchg` by fulfilling one).

`step_solo` classifies what a step does to the lock (`Eff`); `step_sinv` gives
`TsoW` and the drop bound (`dropBounded_of_sinv`); `nacert_replay` /
`instrEnabledSem_of` give replay and enabledness.
-/
import Kraken.Promising.LiveSpinX64SemShape
import Kraken.Promising.LiveSpinX64CmpxInv

namespace Kraken.Promising.Live.SpinX64SemCmpxSolo

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep
open Kraken.Promising.Live.SemShape Kraken.Promising.Live.Sem Kraken.Promising.Live.SpinX64SemShape
open Kraken.Promising.Live.SpinX64Step (en_choose spec_choose run_choose run_choose_exists)
open Kraken.Promising.Live.TsoRmw (en_rmwo_tso)
open Kraken.Promising.Live.SpinX64CmpxInv (LkL CtL Static Holder holder_of_pc not_holder_of_pc stepOne_end
  s1 s2 s4 s5 s6 s9)
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV symC)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-! ## Positions, ranks, predicates -/

/-- `%ecx`'s low word. -/
abbrev ecx (m : MachineData) : BitVec 32 := m.regs.get (.low .rcx .W32)

/-- The register facts: `%eax = 0` at positions 2 and 3, `%ecx = 1` at 3. -/
def PcI (m : MachineData) (i : Nat) : Prop := (i = 2 ∨ i = 3 → eax m = 0#32) ∧ (i = 3 → ecx m = 1#32)

theorem pci_triv {m : MachineData} {i : Nat} (h2 : i ≠ 2) (h3 : i ≠ 3) : PcI m i :=
  ⟨fun h => (h.elim h2 h3).elim, fun h => (h3 h).elim⟩

/-- **The promise-agnostic per-thread invariant**: `Static`, a pc in
`spPcs`, the register facts. -/
structure SInv (s : isa.State) : Prop where
  st : Static s
  pc : ∃ i ∈ spPcs, s.st.2 = pcA i ∧ PcI s.st.1 i

/-- The order of positions (the acquire loop is one rank). -/
def rk : Nat → Nat
  | 5 => 1 | 6 => 2 | 7 => 3 | 8 => 4 | 9 => 5 | 10 => 6 | _ => 0

/-- The thread's position has rank at most `r`. -/
def RkLe (t : Thread isa) (r : Nat) : Prop := ∀ i ∈ spPcs, t.st.st.2 = pcA i → rk i ≤ r

/-- **Pre-acquire**: in the acquire loop, not holding the lock. -/
def PreAcq (t : Thread isa) : Prop := RkLe t 0 ∧ ¬ Holder t

/-- The thread holds an acquire promise (to the lock, of a non-zero value). -/
def HasAcq (t : Thread isa) (mem : Memory) : Prop :=
  ∃ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.loc = LkL ∧ w.val ≠ 0

/-- Every promise of `tid` is a message of its own in memory. -/
def PromIn (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.tid = tid

/-- **What a certifiable worker's promises satisfy.** -/
structure Good (t : Thread isa) (mem : Memory) : Prop where
  loc : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w →
    (w.loc = LkL ∧ w.val ≠ 0 ∧ PreAcq t) ∨ (w.loc = CtL ∧ RkLe t 3) ∨ (w.loc = LkL ∧ w.val = 0 ∧ RkLe t 4)
  acq : t.prom ≠ [] → PreAcq t → HasAcq t mem

theorem good_nil {t : Thread isa} {mem : Memory} (h : t.prom = []) : Good t mem :=
  ⟨fun ts hts => (by rw [h] at hts; cases hts), fun hn => absurd h hn⟩

theorem rkLe_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (ht : t.st.st.2 = pcA p) (r : Nat) :
    RkLe t r ↔ rk p ≤ r :=
  ⟨fun h => h p hp ht, fun h i hi hi' => by rw [addrOf_inj hi hp (hi'.symm.trans ht)]; exact h⟩

theorem holder_iff {t : Thread isa} {p : Nat} (hp : p ∈ spPcs) (ht : t.st.st.2 = pcA p) :
    Holder t ↔ (p = 4 ∧ t.st.st.1.status.zf = true) ∨ p ∈ [5, 6, 7, 8] := by
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
    PreAcq t ↔ rk p = 0 ∧ ¬ (p = 4 ∧ t.st.st.1.status.zf = true) := by
  unfold PreAcq
  rw [rkLe_iff hp ht, holder_iff hp ht]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, fun h => h2 (.inl h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, ?_⟩
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

theorem Good.mono {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : Good t mem) : Good t mem' := by
  refine ⟨fun ts hts w hw => h.loc ts hts w (by rw [← hP.get hp hts]; exact hw), fun hn hpa => ?_⟩
  obtain ⟨ts, hts, w, hw, hl⟩ := h.acq hn hpa
  exact ⟨ts, hts, w, by rw [hP.get hp hts]; exact hw, hl⟩

/-! ## The writing positions with promises -/

section Steps

variable {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static t.st) (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs)

include hS hs ho

/-- The `lock cmpxchg` (position 3), with any promise set: no write (`ZF`
clear), or a write of `%ecx` (`ZF` set), appended or fulfilling a promise
above `vwOld`. -/
theorem s3p (hpc : t.st.st.2 = pcA 3) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 4) ∧
      ((md.status.zf = false ∧ oc.mem = mem ∧ oc.thread.prom = t.prom ∧
          oc.thread.views.vwOld = t.views.vwOld) ∨
       (md.status.zf = true ∧
        ((oc.mem = (mem.append { loc := LkL, val := BitVec.setWidth 128 (ecx t.st.st.1), tid }).1 ∧
          oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
          mem.last + 1 ≤ oc.thread.views.vwOld ∧ mem.last + 1 ≤ oc.thread.views.getCoh LkL) ∨
         (∃ ts ∈ t.prom, mem.get? ts = some { loc := LkL, val := BitVec.setWidth 128 (ecx t.st.st.1), tid } ∧
          t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧
          t.views.vwOld ≤ oc.thread.views.vwOld ∧ ts ≤ oc.thread.views.getCoh LkL)))) := by
  obtain ⟨g, hg, hex⟩ := exec_cmpxchg _ (hS.at (by decide) (by decide) hpc) hS.dl
  obtain ⟨tr, old, hst, -, -, hcase⟩ := spec_rmwo_p_tso _ _ rfl hex hs ho
  refine ⟨g old, (hg old).1, hst, ?_⟩
  have hz := (hg old).2
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨new, h1, ⟨e1, e2, e3, -, e5, -⟩ | ⟨ts, hts, e1, -, e3, e4, e5, e6, e7, -⟩⟩
  · have hne : BitVec.setWidth 32 old ≠ eax t.st.st.1 := fun e => by simp [e] at h1
    refine .inl ⟨?_, h2, h3, h4⟩
    cases e : (g old).status.zf
    · rfl
    · exact absurd (hz.mp e) hne
  · by_cases e : BitVec.setWidth 32 old = eax t.st.st.1
    · simp only [e, ↓reduceIte, Option.some.injEq] at h1
      subst h1
      exact .inr ⟨hz.mpr e, .inl ⟨e1, e2, e3 rfl, e5⟩⟩
    · simp [e] at h1
  · by_cases e : BitVec.setWidth 32 old = eax t.st.st.1
    · simp only [e, ↓reduceIte, Option.some.injEq] at h1
      subst h1
      exact .inr ⟨hz.mpr e, .inr ⟨ts, hts, e1, e3 rfl, e4, e5, e6, e7⟩⟩
    · simp [e] at h1

/-- The counter store (position 7), with any promise set. -/
theorem s7p (hpc : t.st.st.2 = pcA 7) :
    ∃ md : MachineData, md.dmem = t.st.st.1.dmem ∧ oc.thread.st = SpinX64CmpxTrees.goto t.st md (pcA 8) ∧
      ((∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1 ∧
          oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
       (∃ ts ∈ t.prom, (∃ w, mem.get? ts = some w ∧ w.loc = CtL) ∧ t.views.vwOld < ts ∧ oc.mem = mem ∧
          oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld)) := by
  obtain ⟨v, md, hd, hex⟩ := exec_stc _ (hS.at (by decide) (by decide) hpc) hS.dc
  obtain ⟨hst, h⟩ := spec_store_p _ _ hex hs ho
  refine ⟨md, hd, hst, ?_⟩
  rcases h with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, -, e3, e4, e5, e6⟩
  · exact .inl ⟨v, e1, e2, e3 rfl⟩
  · exact .inr ⟨ts, hts, ⟨_, e1, rfl⟩, e3 rfl, e4, e5, e6⟩

/-- The release `movl $0,(lock)` (position 8), with any promise set. -/
theorem s8p (hpc : t.st.st.2 = pcA 8) :
    oc.thread.st = SpinX64CmpxTrees.goto t.st t.st.st.1 (pcA 9) ∧
      ((oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1 ∧
          oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some { loc := LkL, val := 0#128, tid } ∧ t.views.getCoh LkL < ts ∧
          t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧
          t.views.vwOld ≤ oc.thread.views.vwOld)) := by
  obtain ⟨hst, h⟩ := spec_store_p _ _ (exec_unlock _ (hS.at (by decide) (by decide) hpc) hS.dl) hs ho
  refine ⟨hst, ?_⟩
  rcases h with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6⟩
  · exact .inl ⟨e1, e2, e3 rfl⟩
  · exact .inr ⟨ts, hts, e1, e2, e3 rfl, e4, e5, e6⟩

end Steps

/-! ## Promise-agnostic facts: `SInv`, `TsoW`, the drop bound -/

theorem len_fresh (p : List Time) (n : Time) : p.length ≤ ((p ++ [n]).erase n).length + 1 := by
  rw [List.length_erase]; simp

theorem len_erase {p : List Time} (ts : Time) : p.length ≤ (p.erase ts).length + 1 := by
  rw [List.length_erase]; split <;> omega

theorem sinv_goto {s s' : isa.State} {m : MachineData} {q : Nat} (hst : s' = SpinX64CmpxTrees.goto s m (pcA q))
    (hS : Static s) (hd : m.dmem = s.st.1.dmem) (hq : q ∈ spPcs) (hI : PcI m q) : SInv s' :=
  ⟨by rw [hst]; exact hS.goto _ _ hd, q, hq, by rw [hst], by rw [hst]; exact hI⟩

/-- **One step keeps `SInv`, drops at most one promise, and satisfies the TSO
write discipline**, against any memory. -/
theorem step_sinv {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv t.st)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 ∧
      ((∀ ts ∈ t.prom, ts ≤ mem.last) → TsoW t mem oc) := by
  obtain ⟨hSt, p, hp, hpc, hI⟩ := hS
  have eq : ∀ {a b : List Time}, b = a → a.length ≤ b.length + 1 := fun h => by rw [h]; exact Nat.le_succ _
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hm, ⟨md, hd, hz, hst⟩, hpr, -⟩ := s1 hSt hs ho hpc
    exact ⟨sinv_goto hst hSt hd (by decide) ⟨fun _ => hz, fun h => absurd h (by decide)⟩, eq hpr,
      fun hle => tsoW_same hle hm hpr (spec_choose_vw _ _ (exec_xor _ (hSt.at (by decide) (by decide) hpc)) hs ho)⟩
  · obtain ⟨hm, hst, hpr, -⟩ := s2 hSt hs ho hpc
    exact ⟨sinv_goto hst hSt rfl (by decide) ⟨fun _ => hI.1 (.inl rfl), fun _ => rfl⟩, eq hpr,
      fun hle => tsoW_same hle hm hpr (spec_done_vw _ _ (exec_movc _ (hSt.at (by decide) (by decide) hpc)) hs ho)⟩
  · obtain ⟨md, hd, hst, hcase⟩ := s3p hSt hs ho hpc
    refine ⟨sinv_goto hst hSt hd (by decide) (pci_triv (by decide) (by decide)), ?_⟩
    rcases hcase with ⟨-, hm, hpr, hvw⟩ | ⟨-, ⟨hm, hpr, hv1, -⟩ | ⟨ts, -, -, hvt, hm, hpr, hvw, -⟩⟩
    · exact ⟨eq hpr, fun hle => tsoW_same hle hm hpr hvw⟩
    · exact ⟨by rw [hpr]; exact len_fresh _ _, fun hle => tsoW_fresh hle hm hpr hv1⟩
    · exact ⟨by rw [hpr]; exact len_erase ts, fun hle => tsoW_ful hle hm hpr hvt hvw⟩
  · obtain ⟨hm, hst, hpr, -⟩ := s4 hSt hs ho hpc
    have hvw := spec_done_vw _ _ (exec_jne _ (hSt.at (by decide) (by decide) hpc)) hs ho
    refine ⟨?_, eq hpr, fun hle => tsoW_same hle hm hpr hvw⟩
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      exact sinv_goto hst hSt rfl (by decide) (pci_triv (by decide) (by decide))
    · rw [ite_eq_right hz] at hst
      exact sinv_goto hst hSt rfl (by decide) (pci_triv (by decide) (by decide))
  · obtain ⟨md, hd, hst, hm, hpr⟩ := s5 hSt hs ho hpc
    obtain ⟨g, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact ⟨sinv_goto hst hSt hd (by decide) (pci_triv (by decide) (by decide)), eq hpr,
      fun hle => tsoW_same hle hm hpr (spec_load_vw _ _ hex hs ho)⟩
  · obtain ⟨md, hd, hst, hm, hpr⟩ := s6 hSt hs ho hpc
    obtain ⟨md', -, hex⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    exact ⟨sinv_goto hst hSt hd (by decide) (pci_triv (by decide) (by decide)), eq hpr,
      fun hle => tsoW_same hle hm hpr (spec_done_vw _ _ hex hs ho)⟩
  · obtain ⟨md, hd, hst, hcase⟩ := s7p hSt hs ho hpc
    refine ⟨sinv_goto hst hSt hd (by decide) (pci_triv (by decide) (by decide)), ?_⟩
    rcases hcase with ⟨v, hm, hpr, hv1⟩ | ⟨ts, -, -, hvt, hm, hpr, hvw⟩
    · exact ⟨by rw [hpr]; exact len_fresh _ _, fun hle => tsoW_fresh hle hm hpr hv1⟩
    · exact ⟨by rw [hpr]; exact len_erase ts, fun hle => tsoW_ful hle hm hpr hvt hvw⟩
  · obtain ⟨hst, hcase⟩ := s8p hSt hs ho hpc
    refine ⟨sinv_goto hst hSt rfl (by decide) (pci_triv (by decide) (by decide)), ?_⟩
    rcases hcase with ⟨hm, hpr, hv1⟩ | ⟨ts, -, -, -, hvt, hm, hpr, hvw⟩
    · exact ⟨by rw [hpr]; exact len_fresh _ _, fun hle => tsoW_fresh hle hm hpr hv1⟩
    · exact ⟨by rw [hpr]; exact len_erase ts, fun hle => tsoW_ful hle hm hpr hvt hvw⟩
  · obtain ⟨hm, hst, hpr, -⟩ := s9 hSt hs ho hpc
    exact ⟨sinv_goto hst hSt rfl (by decide) (pci_triv (by decide) (by decide)), eq hpr,
      fun hle => tsoW_same hle hm hpr (spec_done_vw _ _ (exec_jmp _ (hSt.at (by decide) (by decide) hpc)) hs ho)⟩
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {tid : Nat} {p q : Thread isa × Memory} (h : ThreadNP Arch.tso tid p q) (hp : SInv p.1.st) :
    SInv q.1.st :=
  ThreadNP.stateInv SInv (fun h hs ho => (step_sinv h hs ho).1) h hp

/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {tid : Nat} {t : Thread isa} (h : SInv t.st) : DropBounded Arch.tso 1 tid t :=
  dropBounded_of_stateInv SInv (fun h hs ho => ⟨(step_sinv h hs ho).1, (step_sinv h hs ho).2.1⟩) h

/-- **A certifiable worker certifies without fresh writes** (TSO; the generic
`SpinX64SemShape.nacertG_of_tsoW` at `SInv`). -/
theorem nacert_of_certOkN {fuel tid : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.tso tid t mem fuel)
    (hS : SInv t.st) (hle : ∀ ts ∈ t.prom, ts ≤ mem.last) : NACertG Arch.tso fuel tid t mem :=
  nacertG_of_tsoW SInv (fun hS hle hs ho => ⟨(step_sinv hS hs ho).1, (step_sinv hS hs ho).2.2 hle⟩) h hS hle

/-! ## One step of a worker alone -/

/-- **What an instruction step does to the lock.** -/
inductive Eff (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; its promises are kept; a holder stays one. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := CtL, val := v, tid }).1)
      (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = LkL → ts ∈ oc.thread.prom)
      (hh : Holder t → Holder oc.thread)
  /-- A `lock cmpxchg` appending a non-zero value: the thread now holds the lock. -/
  | acqFresh (v : Val) (hv : v ≠ 0) (hm : oc.mem = (mem.append { loc := LkL, val := v, tid }).1)
      (hh : Holder oc.thread) (hc : mem.last + 1 ≤ oc.thread.views.getCoh LkL)
  /-- A `lock cmpxchg` fulfilling an acquire promise: the thread now holds the lock. -/
  | acqFul (ts : Time) (hts : ts ∈ t.prom) (w : Msg) (hw : mem.get? ts = some w) (hl : w.loc = LkL)
      (hv : w.val ≠ 0) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts) (hh : Holder oc.thread)
      (hnh : ¬ Holder t) (hc : ts ≤ oc.thread.views.getCoh LkL)
  /-- The release appending `0`. -/
  | relFresh (hm : oc.mem = (mem.append { loc := LkL, val := 0#128, tid }).1) (hh : Holder t)
  /-- The release fulfilling a release promise, above the coherence view. -/
  | relFul (ts : Time) (hts : ts ∈ t.prom) (hw : mem.get? ts = some { loc := LkL, val := 0#128, tid })
      (hc : t.views.getCoh LkL < ts) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts)
      (hh : Holder t)

/-- The results of one step of a worker, with any promises. -/
structure SoloRes (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop where
  sinv : SInv oc.thread.st
  promIn : PromIn tid oc.thread oc.mem
  back : oc.mem = mem → Good oc.thread oc.mem → Good t mem
  eff : Eff tid t mem oc

theorem v1_ne (m : MachineData) (h : ecx m = 1#32) : BitVec.setWidth 128 (ecx m) ≠ 0 := by rw [h]; decide

/-- **One step of a worker alone**, position by position. -/
theorem step_solo {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hlc : LkL ≠ CtL)
    (hS : SInv t.st) (hP : PromIn tid t mem)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok oc ∈ outs) : SoloRes tid t mem oc := by
  have hsi := (step_sinv hS hs ho).1
  obtain ⟨hSt, p, hp, hpc, hI⟩ := hS
  have hPl := hP.le
  have hrk0 : ∀ r, rk p ≤ r → RkLe t r := fun r h => (rkLe_iff hp hpc r).mpr h
  -- a step keeping memory and promises, moving forward in rank
  have quiet : ∀ q ∈ spPcs, oc.thread.st.st.2 = pcA q → rk p ≤ rk q → oc.mem = mem → oc.thread.prom = t.prom →
      (PreAcq oc.thread ↔ PreAcq t) → (Holder t → Holder oc.thread) → SoloRes tid t mem oc := by
    intro q hq hqc hr hm hpr hpa hh
    have hrk : ∀ r, RkLe oc.thread r → RkLe t r := fun r h =>
      hrk0 r (Nat.le_trans hr ((rkLe_iff hq hqc r).mp h))
    refine ⟨hsi, fun ts hts => by rw [hm]; exact hP ts (hpr ▸ hts), fun _ hgd => ⟨fun ts hts w hw => ?_,
      fun hn ha => ?_⟩, .quiet (.inl hm) (fun ts hts _ _ _ => by rw [hpr]; exact hts) hh⟩
    · rcases hgd.loc ts (by rw [hpr]; exact hts) w (by rw [hm]; exact hw) with ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b, d⟩
      · exact .inl ⟨a, b, hpa.mp d⟩
      · exact .inr (.inl ⟨a, hrk _ b⟩)
      · exact .inr (.inr ⟨a, b, hrk _ d⟩)
    · obtain ⟨ts, hts, w, hw, hl⟩ := hgd.acq (by rw [hpr]; exact hn) (hpa.mpr ha)
      exact ⟨ts, hpr ▸ hts, w, by rw [← hm]; exact hw, hl⟩
  -- a holder's write: `t` is a holder at rank `rk p`, so `Good t` needs only its own promises
  have holdBack : Holder t → ∀ {ts : Time} {w : Msg}, (mem.get? ts = some w) → oc.thread.prom = t.prom.erase ts →
      ((w.loc = CtL ∧ RkLe t 3) ∨ (w.loc = LkL ∧ w.val = 0 ∧ RkLe t 4)) →
      (∀ ts' ∈ oc.thread.prom, ∀ w', mem.get? ts' = some w' →
        (w'.loc = CtL ∧ RkLe t 3) ∨ (w'.loc = LkL ∧ w'.val = 0 ∧ RkLe t 4)) → Good t mem := by
    intro hh ts w hw hpr hcl hrest
    refine ⟨fun ts' hts' w' hw' => ?_, fun _ ha => absurd hh ha.2⟩
    by_cases e : ts' = ts
    · subst e; rw [hw] at hw'; cases hw'; exact .inr hcl
    · exact .inr (hrest ts' (by rw [hpr]; exact (List.mem_erase_of_ne e).mpr hts') w' hw')
  have nh : ¬ (p = 4 ∧ t.st.st.1.status.zf = true) → p ∉ [5, 6, 7, 8] → ¬ Holder t := fun h4 h5 h =>
    ((holder_iff hp hpc).mp h).elim h4 h5
  have hp' := hp
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `xorl`
    obtain ⟨hm, ⟨md, -, -, hst⟩, hpr, -⟩ := s1 hSt hs ho hpc
    exact quiet 2 (by decide) (by rw [hst]) (by decide) hm hpr
      (by rw [preAcq_iff (p := 2) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by simp) (by decide)))
  · -- 2: `movl $1,%ecx`
    obtain ⟨hm, hst, hpr, -⟩ := s2 hSt hs ho hpc
    exact quiet 3 (by decide) (by rw [hst]) (by decide) hm hpr
      (by rw [preAcq_iff (p := 3) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by simp) (by decide)))
  · -- 3: `lock cmpxchg`
    have hnt : ¬ Holder t := nh (by simp) (by decide)
    have hpre : PreAcq t := (preAcq_iff hp hpc).mpr (by simp [rk])
    have hv0 := v1_ne _ (hI.2 rfl)
    obtain ⟨md, -, hst, hcase⟩ := s3p hSt hs ho hpc
    rcases hcase with ⟨hz, hm, hpr, -⟩ | ⟨hz, ⟨hm, hpr, -, hco⟩ | ⟨ts, hts, hw, -, hm, hpr, -, hco⟩⟩
    · refine quiet 4 (by decide) (by rw [hst]) (by decide) hm hpr
        (by rw [preAcq_iff (p := 4) (by decide) (by rw [hst]), preAcq_iff hp hpc, hst]; simp [rk, hz])
        (fun h => absurd h hnt)
    · have hho : Holder oc.thread := .inl ⟨by rw [hst], by rw [hst]; exact hz⟩
      have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      exact ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun e => absurd (hm.symm.trans e) (append_ne _ _), .acqFresh _ hv0 hm hho hco⟩
    · have hho : Holder oc.thread := .inl ⟨by rw [hst], by rw [hst]; exact hz⟩
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun _ hg => ?_, .acqFul ts hts _ hw rfl hv0 hm hpr hho hnt hco⟩
      rw [hm] at hg
      refine ⟨fun ts' hts' w' hw' => ?_, fun _ _ => ⟨ts, hts, _, hw, rfl, hv0⟩⟩
      by_cases e : ts' = ts
      · subst e; rw [hw] at hw'; cases hw'
        exact .inl ⟨rfl, hv0, hpre⟩
      · rcases hg.loc ts' (by rw [hpr]; exact (List.mem_erase_of_ne e).mpr hts') w' hw' with
          ⟨-, -, h⟩ | ⟨a, -⟩ | ⟨a, b, -⟩
        · exact absurd hho h.2
        · exact .inr (.inl ⟨a, hrk0 3 (by decide)⟩)
        · exact .inr (.inr ⟨a, b, hrk0 4 (by decide)⟩)
  · -- 4: `jne`
    obtain ⟨hm, hst, hpr, -⟩ := s4 hSt hs ho hpc
    by_cases hz : t.st.st.1.status.zf
    · rw [ite_eq_left hz] at hst
      refine quiet 5 (by decide) (by rw [hst]) (by decide) hm hpr
        (by rw [preAcq_iff (p := 5) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk, hz])
        (fun _ => holder_of_pc (p := 5) (by decide) (by rw [hst]))
    · rw [ite_eq_right hz] at hst
      refine quiet 1 (by decide) (by rw [hst]) (by decide) hm hpr
        (by rw [preAcq_iff (p := 1) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk, hz])
        (fun h => absurd h (nh (by simp [hz]) (by decide)))
  · -- 5: counter load
    obtain ⟨md, -, hst, hm, hpr⟩ := s5 hSt hs ho hpc
    exact quiet 6 (by decide) (by rw [hst]) (by decide) hm hpr
      (by rw [preAcq_iff (p := 6) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun _ => holder_of_pc (p := 6) (by decide) (by rw [hst]))
  · -- 6: `addl`
    obtain ⟨md, -, hst, hm, hpr⟩ := s6 hSt hs ho hpc
    exact quiet 7 (by decide) (by rw [hst]) (by decide) hm hpr
      (by rw [preAcq_iff (p := 7) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun _ => holder_of_pc (p := 7) (by decide) (by rw [hst]))
  · -- 7: counter store
    have hht : Holder t := holder_of_pc (p := 7) (by decide) hpc
    obtain ⟨md, -, hst, hcase⟩ := s7p hSt hs ho hpc
    have hho : Holder oc.thread := holder_of_pc (p := 8) (by decide) (by rw [hst])
    rcases hcase with ⟨v, hm, hpr, -⟩ | ⟨ts, hts, ⟨wc, hwc, hlc'⟩, -, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      exact ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun e => absurd (hm.symm.trans e) (append_ne _ _),
        .quiet (.inr ⟨_, hm⟩) (fun ts hts _ _ _ => hpr' ▸ hts) (fun _ => hho)⟩
    · refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun _ hg => ?_, .quiet (.inl hm) (fun ts' hts' w hw hl => by
          rw [hpr]; refine (List.mem_erase_of_ne fun e => ?_).mpr hts'
          subst e; rw [hwc] at hw; cases hw; exact hlc (hl.symm.trans hlc')) (fun _ => hho)⟩
      rw [hm] at hg
      refine holdBack hht hwc hpr (.inl ⟨hlc', hrk0 3 (by decide)⟩) fun ts' hts' w' hw' => ?_
      rcases hg.loc ts' hts' w' hw' with ⟨-, -, h⟩ | ⟨a, -⟩ | ⟨a, b, -⟩
      · exact absurd hho h.2
      · exact .inl ⟨a, hrk0 3 (by decide)⟩
      · exact .inr ⟨a, b, hrk0 4 (by decide)⟩
  · -- 8: release
    have hht : Holder t := holder_of_pc (p := 8) (by decide) hpc
    obtain ⟨hst, hcase⟩ := s8p hSt hs ho hpc
    have hrk9 : ∀ r, RkLe oc.thread r ↔ 5 ≤ r := rkLe_iff (p := 9) (by decide) (by rw [hst])
    rcases hcase with ⟨hm, hpr, -⟩ | ⟨ts, hts, hw, hco, -, hm, hpr, -⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      exact ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun e => absurd (hm.symm.trans e) (append_ne _ _), .relFresh hm hht⟩
    · refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun _ hg => ?_, .relFul ts hts hw hco hm hpr hht⟩
      rw [hm] at hg
      refine holdBack hht hw hpr (.inr ⟨rfl, rfl, hrk0 4 (by decide)⟩) fun ts' hts' w' hw' => ?_
      rcases hg.loc ts' hts' w' hw' with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩
      · exact absurd ((hrk9 0).mp h.1) (by decide)
      · exact absurd ((hrk9 3).mp h) (by decide)
      · exact absurd ((hrk9 4).mp h) (by decide)
  · -- 9: `jmp done`
    obtain ⟨hm, hst, hpr, -⟩ := s9 hSt hs ho hpc
    exact quiet 10 (by decide) (by rw [hst]) (by decide) hm hpr
      (by rw [preAcq_iff (p := 10) (by decide) (by rw [hst]), preAcq_iff hp hpc]; simp [rk])
      (fun h => absurd h (nh (by simp) (by decide)))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-! ## Along a certification -/

/-- **A worker certifying without fresh writes is `Good`.** -/
theorem good_of_run {tid : Nat} (hlc : LkL ≠ CtL) : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.tso tid n p q → p.2 = q.2 → q.1.prom = [] → SInv p.1.st → PromIn tid p.1 p.2 → Good p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro _ hq _ _; exact good_nil hq
  | @step n p q r hs h ih =>
    intro he hq hS hP
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    have hm : oc.mem = p.2 := Memory.Prefix.antisymm (he ▸ h.mem_prefix) (Memory.Prefix.stepOne hs' ho)
    have r := step_solo hlc hS hP hs' ho
    exact r.back hm (ih (hm.trans he) hq r.sinv r.promIn)

theorem good_of_nacert {fuel tid : Nat} {t : Thread isa} {mem : Memory} (hlc : LkL ≠ CtL)
    (h : NACertG Arch.tso fuel tid t mem) (hS : SInv t.st) (hP : PromIn tid t mem) : Good t mem :=
  let ⟨_, hr, hp⟩ := h; good_of_run hlc hr rfl hp hS hP

/-! ## Replay and enabledness -/

/-- A register-only choice replays against a larger memory
(`SpinX64SemShape.replay_choose`). -/
theorem replay_choose {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hs : stepOne Arch.tso t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) {n : Nat} {f : Fin n → isa.State}
    (hex : isa.exec t.st = some (.choose n fun i => .done (f i))) :
    ∃ outs' o', stepOne Arch.tso t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem :=
  SpinX64SemShape.replay_choose Arch.tso tid hs ho hm hex

/-- **A step that keeps memory replays against a larger memory.** -/
theorem replay_cmpx {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.tso t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.tso t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  obtain ⟨hSt, p, hpp, hpc, -⟩ := hS
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replay_choose hs ho hm (exec_xor _ (hSt.at (by decide) (by decide) hpc))
  · exact replay_done _ _ hp hb hs ho hm (exec_movc _ (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨_, -, hex⟩ := exec_cmpxchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    exact replay_rmwo_tso _ _ hp hb hs ho hm rfl hex
  · exact replay_done _ _ hp hb hs ho hm (exec_jne _ (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨_, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact replay_load _ _ hp hb hs ho hm hex
  · obtain ⟨_, -, hex⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    exact replay_done _ _ hp hb hs ho hm hex
  · obtain ⟨_, _, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    exact replay_store _ _ hp hb hs ho hm hex
  · exact replay_store _ _ hp hb hs ho hm (exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (exec_jmp _ (hSt.at (by decide) (by decide) hpc))
  · rw [stepOne_end hSt hpc] at hs; cases hs

/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem NACert.replay {fuel tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    (h : NACertG Arch.tso fuel tid t mem0) (hS : SInv t.st) (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) :
    NACertG Arch.tso fuel tid t mem :=
  let ⟨t', hr, ht'⟩ := h
  ⟨t', nacertG_replay SInv (fun hS hs ho => (step_sinv hS hs ho).1)
    (fun hS hb hp hs ho hm => replay_cmpx hS hb hp hs ho hm) hr rfl hS hb mem hp, ht'⟩

/-- **A worker that is not at its end and either has no promise or certifies
without fresh writes can take an instruction step** (semantic machine). -/
theorem instrEnabledSem_of {fuel tid : Nat} {cfg : Config isa} {t : Thread isa}
    (ht : cfg.threads[tid]? = some t) (hS : SInv t.st) (h10 : t.st.st.2 ≠ pcA 10)
    (hb : t.Bnd cfg.mem.last) (hn : t.prom = [] ∨ NACertG Arch.tso fuel tid t cfg.mem) :
    InstrEnabledSem Arch.tso fuel tid cfg := by
  refine instrEnabledSem_of_nacertG ht (fun hp0 => ?_) hn
  have fin := fun outs (oc : Outcome isa) =>
    instrEnabledSem_of_step (A := Arch.tso) (fuel := fuel) (outs := outs) (oc := oc) ht
  have dn : ∀ {s : isa.State}, isa.exec t.st = some (.done s) → InstrEnabledSem Arch.tso fuel tid cfg :=
    fun hex => by
      obtain ⟨_, _, h1, h2, h3⟩ := en_done Arch.tso tid hex (mem := cfg.mem)
      exact fin _ _ h1 h2 (h3.trans hp0)
  obtain ⟨hSt, p, hpp, hpc, -⟩ := hS
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, _, h1, h2, h3⟩ := en_choose Arch.tso tid (by decide)
      (exec_xor _ (hSt.at (by decide) (by decide) hpc)) (mem := cfg.mem)
    exact fin _ _ h1 h2 (h3.trans hp0)
  · exact dn (exec_movc _ (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨g, -, hex⟩ := exec_cmpxchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    obtain ⟨_, _, h1, h2, h3⟩ := en_rmwo_tso Arch.tso tid rfl hp0 hb hex
    exact fin _ _ h1 h2 h3
  · exact dn (exec_jne _ (hSt.at (by decide) (by decide) hpc))
  · obtain ⟨g, -, hex⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.tso tid hp0 hex (mem := cfg.mem)
    exact fin _ _ h1 h2 h3
  · obtain ⟨md, -, hex⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    exact dn hex
  · obtain ⟨v, md, -, hex⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso tid hp0 hb hex
    exact fin _ _ h1 h2 h3
  · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.tso tid hp0 hb
      (exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl)
    exact fin _ _ h1 h2 h3
  · exact dn (exec_jmp _ (hSt.at (by decide) (by decide) hpc))
  · exact absurd hpc h10

end Kraken.Promising.Live.SpinX64SemCmpxSolo
