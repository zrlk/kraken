/-
**Stage 3: solo runs of the AArch64 SWP spinlock
workers with outstanding promises**, for any program with `SwpCode P` whose
release is a release write (`RelR P`: `STLR` in `swpWorker`, `SWPL` in
`swplWorker`), on a valid layout.

A worker writes the lock (`l`) at its `SWPA` (position 3: `W3`, which is `1`
after position 1, whatever it reads) and at its release (13: `0`), and the
counter (`c`) at its `STR` (12). Positions are visited in rank order (`rk`),
except for the try/spin loop (one rank). A thread is *pre-acquire*
(`PreAcq`) in the loop and not holding the lock. A certifiable worker
(`Good`, from any certification: `good_of_run`) has promises of three kinds:

- an *acquire-kind* promise (lock, value `≠ 0`): only a `SWPA` fulfils it, so
  the thread is pre-acquire;
- a counter promise: up to the `STR`;
- a *release* promise (lock, value `0`): up to the release, above `vwOld` (a
  release fulfilment), and above every acquire-kind promise of the thread.

Unlike the CAS worker's `CASA`, a failing `SWPA` writes, so fulfilling an
acquire-kind promise need not acquire. It does when the promise is *pinned*
(`AcqAt m z`): a zero of the lock at `z < m` (`ZeroAt`), not written by the
thread (`ZNot`), and no lock write strictly between (`Gap`); by atomicity
the fulfilling `SWPA` reads `z` (`read_zero_gap`). A thread that is not
pre-acquire, or holds a pinned promise (`NA`), certifies without fresh
writes (`nacert_of_run`): such a certification (`NACert`) replays against
any larger memory (`nacert_replay`) and gives an instruction step
(`instrEnabledSem_of`).

`step_solo` also classifies what a step does to the lock (`Eff`), and
`dropBounded_of_sinv` gives the drop bound (one promise per instruction).
-/
import Kraken.Promising.LiveSpinSwpInv
import Kraken.Promising.LiveSpinSemShape
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Live.SpinSemSwpSolo

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.TicketStep
open Kraken.Promising.Live.SemShape Kraken.Promising.Live.SpinSemShape Kraken.Promising.Live.Sem
open Kraken.Promising.Live.SpinSwpInv (Static Static.goto Holder holder_of_pc not_holder_of_pc stepOne_end
  s1 s4 s6 s7 s8 s10 s11 s14 w32)
open Kraken.Promising.Live.TicketInv (L4)
open Kraken.Promising.SLR.SwpTrees (goto)

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

variable {I : ISA}

/-! ## Positions, ranks, predicates -/

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)]

set_option hygiene false in
local notation "pcA" => (layout P).addrOf

/-- The release (position 13) is a release write of `0`: a release store, or
a release swap (the old value into `X2`). -/
def RelTreeR (st : State) (l : BitVec 64) (pc : Int64) : Prop :=
  isa.exec st = some (.store .rel false ⟨l, 4⟩ 0#128 fun _ => .done (goto st st.st.1 pc)) ∨
  isa.exec st = some (.rmw .rel false ⟨l, 4⟩ (fun _ => some 0#128) fun v => .done (goto st
    { st.st.1 with regs := st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) } pc))

/-- **What the promise-aware proof needs beyond `SwpCode P`**: the release
is a release write (`SwpCode.rel` allows an RMW of any kind; a promise of a
non-release RMW could be fulfilled after the counter store's fresh write). -/
def RelR (P : Program) : Prop :=
  ∀ st (l : BitVec 64), AtG P st 13 → st.st.1.regs.X0.toBitVec = l → Mem.loadInt st.st.1.dmem l 4 = none →
    RelTreeR st l ((layout P).addrOf 14)

/-- The register fact: `W3 = 1` from the `SWPA` up to the counter store. -/
def PcI (s : MachineData) (i : Nat) : Prop := i ∈ [3, 4, 6, 7, 8, 10, 11, 12] → w32 s.regs.X3 = 1#32

/-- **The promise-agnostic per-thread invariant**: `Static`, a pc in
`swPcs`, the register fact. -/
structure SInv (P : Program) (l c : BitVec 64) (s : isa.State) : Prop where
  st : Static P l c s
  pc : ∃ i ∈ swPcs, s.st.2 = (layout P).addrOf i ∧ PcI s.st.1 i

/-- The order of positions (the try/spin loop is one rank). -/
def rk : Nat → Nat
  | 1 => 0 | 3 => 1 | 4 => 1 | 6 => 1 | 7 => 1 | 8 => 1 | 10 => 2 | 11 => 3 | 12 => 4 | 13 => 5 | 14 => 6
  | _ => 7

/-- The thread's position has rank at most `r`. -/
def RkLe (P : Program) (t : Thread isa) (r : Nat) : Prop :=
  ∀ i ∈ swPcs, t.st.st.2 = (layout P).addrOf i → rk i ≤ r

/-- **Pre-acquire**: in the try/spin loop (or before it), not holding the
lock. -/
def PreAcq (P : Program) (t : Thread isa) : Prop := RkLe P t 1 ∧ ¬ Holder P t

/-- **A pinned acquire-kind promise** `m` of `tid`: a non-zero lock message
above a zero `z` of the lock that `tid` did not write, with no lock write
strictly between. Its fulfilment reads `z`, so it acquires. -/
structure AcqAt (l : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (m z : Time) : Prop where
  prom : m ∈ t.prom
  msg : ∃ w, mem.get? m = some w ∧ w.loc = L4 l ∧ w.val ≠ 0
  lt : z < m
  zero : ZeroAt (L4 l) mem z
  znot : ZNot mem z tid
  gap : Gap (L4 l) mem z m

/-- Certifies without fresh writes (`nacert_of_run`): not pre-acquire, or
holding a pinned acquire-kind promise. -/
def NA (P : Program) (l : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ¬ PreAcq P t ∨ ∃ m z, AcqAt l tid t mem m z

/-- Every promise of `tid` is a message of its own in memory. -/
def PromIn (tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∃ w, mem.get? ts = some w ∧ w.tid = tid

/-- Every promise lies above the thread's coherence view of its location
(`Sem.coh_lt_of_certOkN`). -/
def CohLt (t : Thread isa) (mem : Memory) : Prop :=
  ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts

/-- **What a certifiable worker's promises satisfy.** -/
structure Good (P : Program) (l c : BitVec 64) (t : Thread isa) (mem : Memory) : Prop where
  loc : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w →
    (w.loc = L4 l ∧ w.val ≠ 0 ∧ PreAcq P t) ∨ (w.loc = L4 c ∧ RkLe P t 4) ∨
    (w.loc = L4 l ∧ w.val = 0 ∧ RkLe P t 5 ∧ t.views.vwOld < ts ∧
      ∀ a ∈ t.prom, ∀ wa, mem.get? a = some wa → wa.loc = L4 l → wa.val ≠ 0 → a < ts)

theorem good_nil {l c : BitVec 64} {t : Thread isa} {mem : Memory} (h : t.prom = []) : Good P l c t mem :=
  ⟨fun ts hts => by rw [h] at hts; cases hts⟩

variable (hC : SwpCode P) (hR : RelR P)

include hC in
theorem rkLe_iff {t : Thread isa} {p : Nat} (hp : p ∈ swPcs) (ht : t.st.st.2 = pcA p) (r : Nat) :
    RkLe P t r ↔ rk p ≤ r :=
  ⟨fun h => h p hp ht, fun h i hi hi' => by rw [hC.inj hi hp (hi'.symm.trans ht)]; exact h⟩

include hC in
theorem holder_iff {t : Thread isa} {p : Nat} (hp : p ∈ swPcs) (ht : t.st.st.2 = pcA p) :
    Holder P t ↔ (p = 4 ∧ w32 t.st.st.1.regs.X2 = 0#32) ∨ p ∈ [10, 11, 12, 13] := by
  constructor
  · rintro (⟨h, hz⟩ | h)
    · exact .inl ⟨hC.inj hp (by decide) (ht.symm.trans h), hz⟩
    · right
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;>
        · obtain rfl := hC.inj hp (by decide) (ht.symm.trans h); decide
  · rintro (⟨rfl, hz⟩ | h)
    · exact .inl ⟨ht, hz⟩
    · exact holder_of_pc h ht

include hC in
theorem preAcq_iff {t : Thread isa} {p : Nat} (hp : p ∈ swPcs) (ht : t.st.st.2 = pcA p) :
    PreAcq P t ↔ rk p ≤ 1 ∧ ¬ (p = 4 ∧ w32 t.st.st.1.regs.X2 = 0#32) := by
  unfold PreAcq
  rw [rkLe_iff hC hp ht, holder_iff hC hp ht]
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

theorem AcqAt.mono {l : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} {m z : Time}
    (hp : mem.Prefix mem') (h : AcqAt l tid t mem m z) : AcqAt l tid t mem' m z := by
  obtain ⟨w, hw, h2⟩ := h.msg
  have hm := mem.last_le_of_get?_eq_some hw
  exact ⟨h.prom, ⟨w, by rw [hp.get? hm]; exact hw, h2⟩, h.lt, h.zero.mono hp, h.znot.mono hp,
    h.gap.mono hp (by omega_t)⟩

theorem AcqAt.of_prom {l : BitVec 64} {tid : Nat} {t t' : Thread isa} {mem : Memory} {m z : Time}
    (h : AcqAt l tid t mem m z) (hm : m ∈ t'.prom) : AcqAt l tid t' mem m z :=
  ⟨hm, h.msg, h.lt, h.zero, h.znot, h.gap⟩

theorem Good.mono {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} (hp : mem.Prefix mem')
    (hP : PromIn tid t mem) (h : Good P l c t mem) : Good P l c t mem' := by
  refine ⟨fun ts hts w hw => ?_⟩
  rcases h.loc ts hts w (by rw [← hP.get hp hts]; exact hw) with a | a | ⟨a1, a2, a3, a4, a5⟩
  · exact .inl a
  · exact .inr (.inl a)
  · exact .inr (.inr ⟨a1, a2, a3, a4, fun a ha wa hwa => a5 a ha wa (by rw [← hP.get hp ha]; exact hwa)⟩)

/-! ## Smaller memories (the layout-free `zeroAt_back` etc. of `LiveSemShape`) -/

section Back

variable {l : Loc} {mem mem' : Memory}

theorem ZeroAt.back {z : Time} (hp : mem.Prefix mem') (hz : z ≤ mem.last) (h : ZeroAt l mem' z) :
    ZeroAt l mem z := zeroAt_back hp hz h

theorem ZNot.back {z : Time} {tid : Nat} (hp : mem.Prefix mem') (hz : z ≤ mem.last) (h : ZNot mem' z tid) :
    ZNot mem z tid := zNot_back hp hz h

theorem TopZ.back {z : Time} (hp : mem.Prefix mem') (h : TopZ l mem' z) : TopZ l mem z := topZ_back hp h

theorem Gap.back {z m : Time} (hp : mem.Prefix mem') (h : Gap l mem' z m) : Gap l mem z m := gap_back hp h

end Back

theorem rkLe_mono {t : Thread isa} {r r' : Nat} (h : RkLe P t r) (hr : r ≤ r') : RkLe P t r' :=
  fun i hi hpc => Nat.le_trans (h i hi hpc) hr

theorem AcqAt.back {l : BitVec 64} {tid : Nat} {t : Thread isa} {mem mem' : Memory} {m z : Time}
    (hp : mem.Prefix mem') (hP : PromIn tid t mem) (h : AcqAt l tid t mem' m z) : AcqAt l tid t mem m z := by
  have hm := hP.le m h.prom
  have hlt := h.lt
  obtain ⟨w, hw, h2⟩ := h.msg
  exact ⟨h.prom, ⟨w, by rw [← hp.get? hm]; exact hw, h2⟩, h.lt, h.zero.back hp (by omega_t),
    h.znot.back hp (by omega_t), h.gap.back hp⟩

/-! ## The writing positions with promises -/

section Steps

variable {l c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {oc : Outcome isa}
  (hS : Static P l c t.st) (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs)

include hC hS hs ho

/-- The `SWPA` (position 3), with any promise set. -/
theorem s3p (hpc : t.st.st.2 = pcA 3) :
    ∃ tr old, oc.thread.st = goto t.st
        { t.st.st.1 with regs := t.st.st.1.regs.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) } (pcA 4) ∧
      mem.read? (L4 l) tr = some old ∧ mem.writeIn (L4 l) tr (t.views.getCoh (L4 l)) = false ∧
      ((oc.mem = (mem.append { loc := L4 l, val := BitVec.setWidth 128 (w32 t.st.st.1.regs.X3), tid }).1 ∧
        oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
        mem.last + 1 ≤ oc.thread.views.getCoh (L4 l) ∧ mem.atomic (L4 l) tid tr (mem.last + 1) = true) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 l, val := BitVec.setWidth 128 (w32 t.st.st.1.regs.X3), tid } ∧
        oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld ∧
        ts ≤ oc.thread.views.getCoh (L4 l) ∧ tr < ts ∧ mem.atomic (L4 l) tid tr ts = true)) := by
  obtain ⟨tr, old, hst, hrd, hw, h⟩ :=
    spec_swp_p _ _ rfl (hC.swpa _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl) hs ho
  refine ⟨tr, old, hst, hrd, hw, ?_⟩
  rcases h with h | ⟨ts, hts, e1, -, -, e4, e5, e6, e7, e8, e9⟩
  · exact .inl h
  · exact .inr ⟨ts, hts, e1, e4, e5, e6, e7, e8, e9⟩

/-- The counter `STR` (position 12), with any promise set. -/
theorem s12p (hpc : t.st.st.2 = pcA 12) :
    oc.thread.st = goto t.st t.st.st.1 (pcA 13) ∧
    ((oc.mem = (mem.append
        { loc := L4 c, val := BitVec.setWidth 128 (BitVec.setWidth 32 t.st.st.1.regs.X5.toBitVec), tid }).1 ∧
      oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ oc.thread.views.vwOld) ∨
     (∃ ts ∈ t.prom, (∃ w, mem.get? ts = some w ∧ w.loc = L4 c) ∧ oc.mem = mem ∧
      oc.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ oc.thread.views.vwOld)) := by
  obtain ⟨hst, h⟩ := spec_store_p _ _ (hC.strc _ c (hS.at hC (by decide) (by decide) hpc) hS.x1 hS.dc) hs ho
  refine ⟨hst, ?_⟩
  rcases h with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, -, -, e4, e5, e6⟩
  · exact .inl ⟨e1, e2, e3 rfl⟩
  · exact .inr ⟨ts, hts, ⟨_, e1, rfl⟩, e4, e5, e6⟩

include hR in
/-- The release (position 13), with any promise set: a fulfilment is above
the coherence view and `vwOld`. -/
theorem s13p (hpc : t.st.st.2 = pcA 13) :
    (∃ md, oc.thread.st = goto t.st md (pcA 14) ∧ md.regs.X0 = t.st.st.1.regs.X0 ∧
      md.regs.X1 = t.st.st.1.regs.X1 ∧ md.dmem = t.st.st.1.dmem) ∧
    ((oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1 ∧
      oc.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1)) ∨
     (∃ ts ∈ t.prom, mem.get? ts = some { loc := L4 l, val := 0#128, tid } ∧ t.views.getCoh (L4 l) < ts ∧
      t.views.vwOld < ts ∧ oc.mem = mem ∧ oc.thread.prom = t.prom.erase ts)) := by
  rcases hR _ l (hS.at hC (by decide) (by decide) hpc) hS.x0 hS.dl with hex | hex
  · obtain ⟨hst, h⟩ := spec_store_p _ _ hex hs ho
    refine ⟨⟨_, hst, rfl, rfl, rfl⟩, ?_⟩
    rcases h with ⟨e1, e2, -⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, -⟩
    · exact .inl ⟨e1, e2⟩
    · exact .inr ⟨ts, hts, e1, e2, e3 rfl, e4, e5⟩
  · obtain ⟨tr, old, hst, -, -, h⟩ := spec_swp_p _ _ rfl hex hs ho
    refine ⟨⟨_, hst, rfl, rfl, rfl⟩, ?_⟩
    rcases h with ⟨e1, e2, -⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, -⟩
    · exact .inl ⟨e1, e2⟩
    · exact .inr ⟨ts, hts, e1, e2, e3 rfl, e4, e5⟩

end Steps

/-! ## One step: `SInv` and the drop bound -/

theorem pci_keep {s s' : MachineData} {p q : Nat} (h : PcI s p) (hp : p ∈ [3, 4, 6, 7, 8, 10, 11, 12])
    (h3 : s'.regs.X3 = s.regs.X3) :
    PcI s' q :=
  fun _ => h3 ▸ h hp

theorem w32_set2 (r : Reg64s) (old : Val) :
    w32 (r.setXReg .X2 (BitVec.setWidth 64 (BitVec.setWidth 32 old))).X2 = BitVec.setWidth 32 old := by
  show BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 old)) = _
  simp

theorem len_fresh (p : List Time) (n : Time) : p.length ≤ ((p ++ [n]).erase n).length + 1 := by
  rw [List.length_erase]; simp

theorem len_erase {p : List Time} (ts : Time) : p.length ≤ (p.erase ts).length + 1 := by
  rw [List.length_erase]; split <;> omega

theorem lt3_absurd {a b d : Nat} (h1 : a + 1 ≤ b) (h2 : b < d) (h3 : d ≤ a) : False := by omega

include hC hR in
/-- **One step keeps `SInv` and drops at most one promise**, against any
memory. -/
theorem step_sinv {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv P l c t.st)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) :
    SInv P l c oc.thread.st ∧ t.prom.length ≤ oc.thread.prom.length + 1 := by
  obtain ⟨hSt, p, hp, hpc, hI⟩ := hS
  have eq : ∀ {a b : List Time}, b = a → a.length ≤ b.length + 1 := fun h => by rw [h]; exact Nat.le_succ _
  have g : ∀ {m : MachineData} {q : Nat}, oc.thread.st = goto t.st m (pcA q) → q ∈ swPcs →
      m.regs.X0 = t.st.st.1.regs.X0 → m.regs.X1 = t.st.st.1.regs.X1 → m.dmem = t.st.st.1.dmem → PcI m q →
      SInv P l c oc.thread.st := fun hst hq h0 h1 hd hI' =>
    ⟨by rw [hst]; exact hSt.goto _ _ h0 h1 hd, _, hq, by rw [hst], by rw [hst]; exact hI'⟩
  have k1 : p ∈ [3, 4, 6, 7, 8, 10, 11, 12] → ∀ {m : MachineData}, m.regs.X3 = t.st.st.1.regs.X3 → ∀ q, PcI m q :=
    fun hp1 _ h3 _ => pci_keep hI hp1 h3
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hst, hpr, -⟩ := s1 hC hSt hs ho hpc
    exact ⟨g hst (by decide) rfl rfl rfl fun _ => rfl, eq hpr⟩
  · obtain ⟨tr, old, hst, -, -, h⟩ := s3p hC hSt hs ho hpc
    refine ⟨g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _), ?_⟩
    rcases h with ⟨-, hpr, -⟩ | ⟨ts, -, -, -, hpr, -⟩
    · rw [hpr]; exact len_fresh _ _
    · rw [hpr]; exact len_erase ts
  · obtain ⟨-, hst, hpr, -⟩ := s4 hC hSt hs ho hpc
    refine ⟨?_, eq hpr⟩
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · simp only [hz, ↓reduceIte] at hst; exact g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _)
    · simp only [hz, ↓reduceIte] at hst; exact g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _)
  · obtain ⟨ts, v, hst, -, -, hpr, -⟩ := s6 hC hSt hs ho hpc
    exact ⟨g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _), eq hpr⟩
  · obtain ⟨-, hst, hpr, -⟩ := s7 hC hSt hs ho hpc
    refine ⟨?_, eq hpr⟩
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · simp only [hz, ↓reduceIte] at hst; exact g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _)
    · simp only [hz, ↓reduceIte] at hst; exact g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _)
  · obtain ⟨-, hst, hpr, -⟩ := s8 hC hSt hs ho hpc
    exact ⟨g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _), eq hpr⟩
  · obtain ⟨v, hst, -, hpr, -⟩ := s10 hC hSt hs ho hpc
    exact ⟨g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _), eq hpr⟩
  · obtain ⟨-, hst, hpr, -⟩ := s11 hC hSt hs ho hpc
    exact ⟨g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _), eq hpr⟩
  · obtain ⟨hst, h⟩ := s12p hC hSt hs ho hpc
    refine ⟨g hst (by decide) rfl rfl rfl (k1 (by decide) rfl _), ?_⟩
    rcases h with ⟨-, hpr, -⟩ | ⟨ts, -, -, -, hpr, -⟩
    · rw [hpr]; exact len_fresh _ _
    · rw [hpr]; exact len_erase ts
  · obtain ⟨⟨md, hst, h0, h1, hd⟩, h⟩ := s13p hC hR hSt hs ho hpc
    refine ⟨g hst (by decide) h0 h1 hd fun h => absurd h (by decide), ?_⟩
    rcases h with ⟨-, hpr⟩ | ⟨ts, -, -, -, -, -, hpr⟩
    · rw [hpr]; exact len_fresh _ _
    · rw [hpr]; exact len_erase ts
  · obtain ⟨-, hst, hpr, -⟩ := s14 hC hSt hs ho hpc
    exact ⟨g hst (by decide) rfl rfl rfl fun h => absurd h (by decide), eq hpr⟩
  · rw [stepOne_end hSt hpc] at hs; cases hs

include hC hR in
/-- `SInv` along a run of the thread alone. -/
theorem threadNP_sinv {l c : BitVec 64} {tid : Nat} {p q : Thread isa × Memory}
    (h : ThreadNP Arch.armv8 tid p q) (hp : SInv P l c p.1.st) : SInv P l c q.1.st :=
  ThreadNP.stateInv (SInv P l c) (fun h hs ho => (step_sinv hC hR h hs ho).1) h hp

include hC hR in
/-- **A worker satisfying `SInv` drops at most one promise per instruction.** -/
theorem dropBounded_of_sinv {l c : BitVec 64} {tid : Nat} {t : Thread isa} (h : SInv P l c t.st) :
    DropBounded Arch.armv8 1 tid t :=
  dropBounded_of_stateInv (SInv P l c) (fun h hs ho => step_sinv hC hR h hs ho) h

/-! ## One step of a worker alone -/

/-- **What an instruction step does to the lock.** -/
inductive Eff (P : Program) (l c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) : Prop
  /-- The lock is not written; its promises are kept; a holder stays one. -/
  | quiet (hm : oc.mem = mem ∨ ∃ v, oc.mem = (mem.append { loc := L4 c, val := v, tid }).1)
      (hkeep : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc = L4 l → ts ∈ oc.thread.prom)
      (hh : Holder P t → Holder P oc.thread)
  /-- A `SWPA` appending a non-zero value; it acquires if it follows a zero
  it did not write. -/
  | swpFresh (v : Val) (hv : v ≠ 0) (hm : oc.mem = (mem.append { loc := L4 l, val := v, tid }).1)
      (hpr : oc.thread.prom = t.prom) (hpre : PreAcq P t) (hc : mem.last + 1 ≤ oc.thread.views.getCoh (L4 l))
      (hz : ∀ z, ZeroAt (L4 l) mem z → ZNot mem z tid → z < mem.last + 1 → Gap (L4 l) mem z (mem.last + 1) →
        Holder P oc.thread)
  /-- A `SWPA` fulfilling an acquire-kind promise; it acquires if the promise
  is pinned. -/
  | swpFul (ts : Time) (hts : ts ∈ t.prom) (w : Msg) (hw : mem.get? ts = some w) (hl : w.loc = L4 l)
      (hv : w.val ≠ 0) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts) (hpre : PreAcq P t)
      (hc : ts ≤ oc.thread.views.getCoh (L4 l))
      (hz : ∀ z, ZeroAt (L4 l) mem z → ZNot mem z tid → z < ts → Gap (L4 l) mem z ts → Holder P oc.thread)
  /-- The release appending `0`. -/
  | relFresh (hm : oc.mem = (mem.append { loc := L4 l, val := 0#128, tid }).1) (hh : Holder P t)
      (hpast : ¬ RkLe P oc.thread 5)
  /-- The release fulfilling a release promise, above the coherence view. -/
  | relFul (ts : Time) (hts : ts ∈ t.prom) (hw : mem.get? ts = some { loc := L4 l, val := 0#128, tid })
      (hc : t.views.getCoh (L4 l) < ts) (hm : oc.mem = mem) (hpr : oc.thread.prom = t.prom.erase ts)
      (hh : Holder P t) (hpast : ¬ RkLe P oc.thread 5)

/-- The results of one step of a worker, with any promises. -/
structure SoloRes (P : Program) (l c : BitVec 64) (tid : Nat) (t : Thread isa) (mem : Memory) (oc : Outcome isa) :
    Prop where
  sinv : SInv P l c oc.thread.st
  promIn : PromIn tid oc.thread oc.mem
  back : Good P l c oc.thread oc.mem → CohLt oc.thread oc.mem →
    Good P l c t mem ∧ (t.prom ≠ [] → NA P l tid t mem → oc.mem = mem ∧ NA P l tid oc.thread oc.mem)
  past : ¬ RkLe P t 5 → ¬ RkLe P oc.thread 5
  eff : Eff P l c tid t mem oc

include hC hR in
/-- **One step of a worker alone**, position by position. -/
theorem step_solo {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hlc : L4 l ≠ L4 c)
    (hS : SInv P l c t.st) (hP : PromIn tid t mem)
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : SoloRes P l c tid t mem oc := by
  have hsi := (step_sinv hC hR hS hs ho).1
  obtain ⟨hSt, p, hp, hpc, hI⟩ := hS
  have hPl := hP.le
  have hrk5 : rk p ≤ 5 → ¬ RkLe P t 5 → ¬ RkLe P oc.thread 5 := fun h h' => absurd ((rkLe_iff hC hp hpc 5).mpr h) h'
  have quiet : ∀ q ∈ swPcs, oc.thread.st.st.2 = pcA q → rk p ≤ rk q → oc.mem = mem → oc.thread.prom = t.prom →
      t.views.vwOld ≤ oc.thread.views.vwOld → (PreAcq P oc.thread ↔ PreAcq P t) →
      (Holder P t → Holder P oc.thread) → SoloRes P l c tid t mem oc := by
    intro q hq hqc hr hm hpr hvw hpa hh
    have hrk : ∀ r, RkLe P oc.thread r → RkLe P t r := fun r h =>
      (rkLe_iff hC hp hpc r).mpr (Nat.le_trans hr ((rkLe_iff hC hq hqc r).mp h))
    have hg : ∀ {ts w}, mem.get? ts = some w → oc.mem.get? ts = some w := fun h => by rw [hm]; exact h
    refine ⟨hsi, fun ts hts => by rw [hm]; exact hP ts (hpr ▸ hts),
      fun hgd _ => ⟨⟨fun ts hts w hw => ?_⟩, fun _ hna => ⟨hm, ?_⟩⟩, fun h h' => h (hrk 5 h'),
      .quiet (.inl hm) (fun ts hts _ _ _ => by rw [hpr]; exact hts) hh⟩
    · rcases hgd.loc ts (by rw [hpr]; exact hts) w (hg hw) with ⟨a, b, d⟩ | ⟨a, b⟩ | ⟨a, b, d, e, f⟩
      · exact .inl ⟨a, b, hpa.mp d⟩
      · exact .inr (.inl ⟨a, hrk _ b⟩)
      · exact .inr (.inr ⟨a, b, hrk _ d, Nat.lt_of_le_of_lt hvw e,
          fun a' ha' wa hwa => f a' (by rw [hpr]; exact ha') wa (hg hwa)⟩)
    · rcases hna with h | ⟨m, z, h⟩
      · exact .inl fun h' => h (hpa.mp h')
      · exact .inr ⟨m, z, by rw [hm]; exact h.of_prom (by rw [hpr]; exact h.prom)⟩
  have nh : p ≠ 4 → p ∉ [10, 11, 12, 13] → ¬ Holder P t := fun h4 h10 h => by
    rcases (holder_iff hC hp hpc).mp h with ⟨e, -⟩ | h'
    · exact h4 e
    · exact h10 h'
  have hp' := hp
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- 1: `MOV W3, #1`
    have hex := hC.mov _ (hSt.at hC (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s1 hC hSt hs ho hpc
    refine quiet 3 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff hC (p := 3) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide)))
  · -- 3: `SWPA`
    have h3 : w32 t.st.st.1.regs.X3 = 1#32 := hI (by decide)
    have hpre : PreAcq P t := (preAcq_iff hC hp hpc).mpr (by simp [rk])
    obtain ⟨tr, old, hst, hrd, -, hcase⟩ := s3p hC hSt hs ho hpc
    have hw2 : w32 oc.thread.st.st.1.regs.X2 = BitVec.setWidth 32 old := by rw [hst]; exact w32_set2 _ _
    have hv0 : BitVec.setWidth 128 (w32 t.st.st.1.regs.X3) ≠ 0 := by rw [h3]; decide
    have hho : old = 0 → Holder P oc.thread := fun e => .inl ⟨by rw [hst], by rw [hw2, e]; rfl⟩
    have hzg : ∀ {m : Time}, mem.atomic (L4 l) tid tr m = true → tr < m → ∀ z, ZeroAt (L4 l) mem z →
        ZNot mem z tid → z < m → Gap (L4 l) mem z m → Holder P oc.thread :=
      fun ha htr z h1 h2 h3 h4 => hho (read_zero_gap hrd ha htr h1 h2 h3 h4)
    have hpast : ¬ RkLe P t 5 → ¬ RkLe P oc.thread 5 := hrk5 (by decide)
    rcases hcase with ⟨hm, hpr, hco, ha⟩ | ⟨ts, hts, hw, hm, hpr, hvw, hco, htr, ha⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts), fun hg hcl => ?_, hpast,
        .swpFresh _ hv0 hm hpr' hpre hco (hzg ha (Nat.lt_succ_of_le (read_le hrd)))⟩
      have nolock : ∀ ts ∈ t.prom, ∀ w, mem.get? ts = some w → w.loc ≠ L4 l := fun ts hts w hw hl => by
        have := hcl ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw)
        rw [hl] at this
        exact lt3_absurd hco this (hPl ts hts)
      refine ⟨⟨fun ts hts w hw => ?_⟩, fun _ hna => ?_⟩
      · rcases hg.loc ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw) with ⟨a, -⟩ | ⟨a, -⟩ | ⟨a, -⟩
        · exact absurd a (nolock ts hts w hw)
        · exact .inr (.inl ⟨a, (rkLe_iff hC hp hpc 4).mpr (by decide)⟩)
        · exact absurd a (nolock ts hts w hw)
      · rcases hna with h | ⟨m, z, h⟩
        · exact absurd hpre h
        · obtain ⟨w, hw, hl, -⟩ := h.msg
          exact absurd hl (nolock m h.prom w hw)
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')), fun hg hcl => ?_,
        hpast, .swpFul ts hts _ hw rfl hv0 hm hpr hpre hco (hzg ha htr)⟩
      rw [hm] at hg hcl
      refine ⟨⟨fun ts' hts' w' hw' => ?_⟩, fun _ hna => ⟨hm, ?_⟩⟩
      · by_cases e : ts' = ts
        · subst e; rw [hw] at hw'; cases hw'
          exact .inl ⟨rfl, hv0, hpre⟩
        · rcases hg.loc ts' (hin ts' hts' e) w' hw' with ⟨a, b, -⟩ | ⟨a, -⟩ | ⟨a, b, d, f, g⟩
          · exact .inl ⟨a, b, hpre⟩
          · exact .inr (.inl ⟨a, (rkLe_iff hC hp hpc 4).mpr (by decide)⟩)
          · refine .inr (.inr ⟨a, b, (rkLe_iff hC hp hpc 5).mpr (by decide), Nat.lt_of_le_of_lt hvw f,
              fun a' ha' wa hwa hla hva => ?_⟩)
            by_cases e' : a' = ts
            · subst e'
              have := hcl ts' (hin ts' hts' e) w' hw'
              rw [a] at this
              exact Nat.lt_of_le_of_lt hco this
            · exact g a' (hin a' ha' e') wa hwa hla hva
      · rw [hm]
        by_cases e : old = 0
        · exact .inl fun h => h.2 (hho e)
        · rcases hna with h | ⟨m, z, h⟩
          · exact absurd hpre h
          · by_cases e' : m = ts
            · subst e'
              exact absurd (read_zero_gap hrd ha htr h.zero h.znot h.lt h.gap) e
            · exact .inr ⟨m, z, h.of_prom (hin m h.prom e')⟩
  · -- 4: `CBZ`
    have hex := hC.cbz _ (hSt.at hC (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s4 hC hSt hs ho hpc
    have hvw := Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · simp only [hz, ↓reduceIte] at hst
      refine quiet 10 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff hC (p := 10) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk, hz])
        (fun _ => holder_of_pc (p := 10) (by decide) (by rw [hst]))
    · simp only [hz, ↓reduceIte] at hst
      refine quiet 6 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff hC (p := 6) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk, hz])
        (fun h => absurd ((holder_iff hC hp hpc).mp h) (by simp [hz]))
  · -- 6: `LDR` lock
    have hex := hC.ldr _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl
    obtain ⟨ts, v, hst, -, hm, hpr, -, -⟩ := s6 hC hSt hs ho hpc
    refine quiet 7 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_load_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff hC (p := 7) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide)))
  · -- 7: `CBNZ`
    have hex := hC.cbnz _ (hSt.at hC (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s7 hC hSt hs ho hpc
    have hvw := Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm
    by_cases hz : w32 t.st.st.1.regs.X2 = 0#32
    · simp only [hz, ↓reduceIte] at hst
      refine quiet 8 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff hC (p := 8) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
        (fun h => absurd h (nh (by decide) (by decide)))
    · simp only [hz, ↓reduceIte] at hst
      refine quiet 6 (by decide) (by rw [hst]) (by decide) hm hpr hvw
        (by rw [preAcq_iff hC (p := 6) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
        (fun h => absurd h (nh (by decide) (by decide)))
  · -- 8: `B try`
    have hex := hC.btry _ (hSt.at hC (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s8 hC hSt hs ho hpc
    refine quiet 3 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff hC (p := 3) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide)))
  · -- 10: `LDR` counter
    have hex := hC.ldrc _ c (hSt.at hC (by decide) (by decide) hpc) hSt.x1 hSt.dc
    obtain ⟨v, hst, hm, hpr, -⟩ := s10 hC hSt hs ho hpc
    refine quiet 11 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_load_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff hC (p := 11) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
      (fun _ => holder_of_pc (p := 11) (by decide) (by rw [hst]))
  · -- 11: `ADD W5`
    have hex := hC.add _ (hSt.at hC (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s11 hC hSt hs ho hpc
    refine quiet 12 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff hC (p := 12) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
      (fun _ => holder_of_pc (p := 12) (by decide) (by rw [hst]))
  · -- 12: `STR` counter
    obtain ⟨hst, hcase⟩ := s12p hC hSt hs ho hpc
    have hho : Holder P oc.thread := holder_of_pc (p := 13) (by decide) (by rw [hst])
    have hnpo : ¬ PreAcq P oc.thread := fun h => h.2 hho
    have hrk : ∀ r, RkLe P oc.thread r ↔ 5 ≤ r := rkLe_iff hC (p := 13) (by decide) (by rw [hst])
    have hpast : ¬ RkLe P t 5 → ¬ RkLe P oc.thread 5 := hrk5 (by decide)
    rcases hcase with ⟨hm, hpr, hvw⟩ | ⟨ts, hts, ⟨wc, hwc, hlc'⟩, hm, hpr, hvw⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      have hnone : Good P l c oc.thread oc.mem → ∀ ts ∈ t.prom, False := fun hg ts hts => by
        obtain ⟨w, hw, -⟩ := hP ts hts
        rcases hg.loc ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw) with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, -, -, h, -⟩
        · exact hnpo h
        · exact absurd ((hrk 4).mp h) (by decide)
        · exact lt3_absurd hvw h (hPl ts hts)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun hg _ => ⟨⟨fun ts hts => (hnone hg ts hts).elim⟩, fun hne _ => ?_⟩, hpast,
        .quiet (.inr ⟨_, hm⟩) (fun ts hts _ _ _ => hpr' ▸ hts) (fun _ => hho)⟩
      obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hnone hg ts hts).elim
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun hg _ => ?_, hpast,
        .quiet (.inl hm) (fun ts' hts' w hw hl => hin ts' hts' (fun e => by
          subst e; rw [hwc] at hw; cases hw; exact hlc (hl.symm.trans hlc'))) (fun _ => hho)⟩
      rw [hm] at hg
      refine ⟨⟨fun ts' hts' w' hw' => ?_⟩, fun _ _ => ⟨hm, .inl hnpo⟩⟩
      by_cases e : ts' = ts
      · subst e; rw [hwc] at hw'; cases hw'
        exact .inr (.inl ⟨hlc', (rkLe_iff hC hp hpc 4).mpr (by decide)⟩)
      · rcases hg.loc ts' (hin ts' hts' e) w' hw' with ⟨-, -, h⟩ | ⟨-, b⟩ | ⟨a, b, d, f, g⟩
        · exact absurd h hnpo
        · exact absurd ((hrk 4).mp b) (by decide)
        · refine .inr (.inr ⟨a, b, (rkLe_iff hC hp hpc 5).mpr (by decide), Nat.lt_of_le_of_lt hvw f,
            fun a' ha' wa hwa hla hva => ?_⟩)
          by_cases e' : a' = ts
          · subst e'; rw [hwc] at hwa; cases hwa; exact absurd (hla.symm.trans hlc') hlc
          · exact g a' (hin a' ha' e') wa hwa hla hva
  · -- 13: the release
    obtain ⟨⟨md, hst, h0, h1, hd⟩, hcase⟩ := s13p hC hR hSt hs ho hpc
    have hrk : ∀ r, RkLe P oc.thread r ↔ 6 ≤ r := rkLe_iff hC (p := 14) (by decide) (by rw [hst])
    have hnpo : ¬ PreAcq P oc.thread := fun h => absurd ((hrk 1).mp h.1) (by decide)
    have hpast : ¬ RkLe P oc.thread 5 := fun h => absurd ((hrk 5).mp h) (by decide)
    have hht : Holder P t := holder_of_pc (p := 13) (by decide) hpc
    have hdead : Good P l c oc.thread oc.mem → ∀ ts ∈ oc.thread.prom, ∀ w, oc.mem.get? ts = some w → False := by
      intro hg ts hts w hw
      rcases hg.loc ts hts w hw with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, -, h, -⟩
      · exact hnpo h
      · exact absurd ((hrk 4).mp h) (by decide)
      · exact hpast h
    rcases hcase with ⟨hm, hpr⟩ | ⟨ts, hts, hw, hco, hvo, hm, hpr⟩
    · have hpr' : oc.thread.prom = t.prom := hpr.trans (erase_fresh hPl)
      have hgm : ∀ ts ∈ t.prom, oc.mem.get? ts = mem.get? ts := fun ts hts => by
        rw [hm]; exact (Memory.Prefix.append _ _).get? (hPl ts hts)
      have hnone : Good P l c oc.thread oc.mem → ∀ ts ∈ t.prom, False := fun hg ts hts => by
        obtain ⟨w, hw, -⟩ := hP ts hts
        exact hdead hg ts (hpr' ▸ hts) w (by rw [hgm ts hts]; exact hw)
      refine ⟨hsi, fun ts hts => by rw [hgm ts (hpr' ▸ hts)]; exact hP ts (hpr' ▸ hts),
        fun hg _ => ⟨⟨fun ts hts => (hnone hg ts hts).elim⟩, fun hne _ => ?_⟩, fun _ => hpast,
        .relFresh hm hht hpast⟩
      obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hnone hg ts hts).elim
    · have hin : ∀ ts' ∈ t.prom, ts' ≠ ts → ts' ∈ oc.thread.prom := fun ts' h' hne => by
        rw [hpr]; exact (List.mem_erase_of_ne hne).mpr h'
      refine ⟨hsi, fun ts' hts' => by rw [hm]; exact hP ts' (List.mem_of_mem_erase (hpr ▸ hts')),
        fun hg _ => ?_, fun _ => hpast, .relFul ts hts hw hco hm hpr hht hpast⟩
      refine ⟨⟨fun ts' hts' w' hw' => ?_⟩, fun _ _ => ⟨hm, .inl hnpo⟩⟩
      by_cases e : ts' = ts
      · subst e; rw [hw] at hw'; cases hw'
        refine .inr (.inr ⟨rfl, rfl, (rkLe_iff hC hp hpc 5).mpr (by decide), hvo, fun a ha wa hwa _ hva => ?_⟩)
        by_cases e' : a = ts'
        · subst e'; rw [hw] at hwa; cases hwa; exact absurd rfl hva
        · exact (hdead hg a (hin a ha e') wa (by rw [hm]; exact hwa)).elim
      · exact (hdead hg ts' (hin ts' hts' e) w' (by rw [hm]; exact hw')).elim
  · -- 14: `B done`
    have hex := hC.bdone _ (hSt.at hC (by decide) (by decide) hpc)
    obtain ⟨hm, hst, hpr, -⟩ := s14 hC hSt hs ho hpc
    refine quiet 16 (by decide) (by rw [hst]) (by decide) hm hpr (Nat.le_of_eq (spec_done_vw _ _ hex hs ho).symm)
      (by rw [preAcq_iff hC (p := 16) (by decide) (by rw [hst]), preAcq_iff hC hp hpc]; simp [rk])
      (fun h => absurd h (nh (by decide) (by decide)))
  · rw [stepOne_end hSt hpc] at hs; cases hs


/-! ## Along a run -/

/-- A copy of `SpinSemSolo.threadNPn_prefix` (which carries that file's
layout instance): a solo run only extends memory (an instance of
`ThreadNPn.mem_prefix`). -/
theorem threadNPn_prefix {tid n : Nat} {p q : Thread isa × Memory} (h : ThreadNPn Arch.armv8 tid n p q) :
    p.2.Prefix q.2 := h.mem_prefix

/-- A copy of `SpinSemSolo.NACert`: a certification without fresh writes,
against memory `mem` (both unfold to `Sem.NACertG Arch.armv8`). -/
def NACert (fuel tid : Nat) (t : Thread isa) (mem : Memory) : Prop :=
  ∃ t', ThreadNPn Arch.armv8 tid fuel (t, mem) (t', mem) ∧ t'.prom = []

section Run

variable {l c : BitVec 64} {tid : Nat} (hlc : L4 l ≠ L4 c)

include hC hR hlc

/-- **A certifiable worker is `Good`.** -/
theorem good_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
    SInv P l c p.1.st → PromIn tid p.1 p.2 → Good P l c p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _; exact good_nil hq
  | step hs h ih =>
    intro hq hS hP
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    have r := step_solo hC hR hlc hS hP hs ho
    exact (r.back (ih hq r.sinv r.promIn) fun _ hts _ hw => coh_lt_of_certOkN ⟨_, _, h, hq⟩ hts hw).1

theorem good_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.armv8 tid t mem fuel)
    (hS : SInv P l c t.st) (hP : PromIn tid t mem) : Good P l c t mem :=
  let ⟨_, _, hr, hp⟩ := h; good_of_run hC hR hlc hr hp hS hP

/-- **A worker that is not pre-acquire, or holds a pinned acquire-kind
promise, certifies without fresh writes** (stopping once its promise set is
empty). -/
theorem nacert_of_run : ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
    SInv P l c p.1.st → PromIn tid p.1 p.2 → NA P l tid p.1 p.2 →
    ∃ t', ThreadNPn Arch.armv8 tid n p (t', p.2) ∧ t'.prom = [] := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _ _; exact ⟨p.1, .refl _ _, hq⟩
  | @step n p q r hs h ih =>
    intro hq hS hP hN
    by_cases hp0 : p.1.prom = []
    · exact ⟨p.1, .refl _ _, hp0⟩
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    have rs := step_solo hC hR hlc hS hP hs' ho
    obtain ⟨hm, hN'⟩ := (rs.back (good_of_run hC hR hlc h hq rs.sinv rs.promIn)
      fun _ hts _ hw => coh_lt_of_certOkN ⟨_, _, h, hq⟩ hts hw).2 hp0 hN
    obtain ⟨t', h', ht'⟩ := ih hq rs.sinv rs.promIn hN'
    refine ⟨t', .step ⟨outs, oc, hs', ho, rfl⟩ ?_, ht'⟩
    rw [← hm]; exact h'

theorem nacert_of_certOkN {fuel : Nat} {t : Thread isa} {mem : Memory} (h : CertOkN Arch.armv8 tid t mem fuel)
    (hS : SInv P l c t.st) (hP : PromIn tid t mem) (hN : NA P l tid t mem) : NACert fuel tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; nacert_of_run hC hR hlc hr hp hS hP hN

end Run

/-! ## Replay and enabledness -/

include hC hR in
/-- **A step that keeps memory replays against a larger memory.** -/
theorem replay_swp {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (hS : SInv P l c t.st)
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne Arch.armv8 t tid mem0 = some outs)
    (ho : .ok oc ∈ outs) (hm : oc.mem = mem0) :
    ∃ outs' o', stepOne Arch.armv8 t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = oc.thread ∧ o'.mem = mem := by
  obtain ⟨hSt, p, hpp, hpc, -⟩ := hS
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replay_done _ _ hp hb hs ho hm (hC.mov _ (hSt.at hC (by decide) (by decide) hpc))
  · exact replay_rmw _ _ hp hb hs ho hm rfl (hC.swpa _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (hC.cbz _ (hSt.at hC (by decide) (by decide) hpc))
  · exact replay_load _ _ hp hb hs ho hm (hC.ldr _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl)
  · exact replay_done _ _ hp hb hs ho hm (hC.cbnz _ (hSt.at hC (by decide) (by decide) hpc))
  · exact replay_done _ _ hp hb hs ho hm (hC.btry _ (hSt.at hC (by decide) (by decide) hpc))
  · exact replay_load _ _ hp hb hs ho hm (hC.ldrc _ c (hSt.at hC (by decide) (by decide) hpc) hSt.x1 hSt.dc)
  · exact replay_done _ _ hp hb hs ho hm (hC.add _ (hSt.at hC (by decide) (by decide) hpc))
  · exact replay_store _ _ hp hb hs ho hm (hC.strc _ c (hSt.at hC (by decide) (by decide) hpc) hSt.x1 hSt.dc)
  · rcases hR _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl with hex | hex
    · exact replay_store _ _ hp hb hs ho hm hex
    · exact replay_rmw _ _ hp hb hs ho hm rfl hex
  · exact replay_done _ _ hp hb hs ho hm (hC.bdone _ (hSt.at hC (by decide) (by decide) hpc))
  · rw [stepOne_end hSt hpc] at hs; cases hs

include hC hR in
/-- **A certification without fresh writes replays against a larger
memory.** -/
theorem nacert_replay {l c : BitVec 64} {tid : Nat} : ∀ {n : Nat} {p q : Thread isa × Memory},
    ThreadNPn Arch.armv8 tid n p q → p.2 = q.2 → SInv P l c p.1.st → p.1.Bnd p.2.last →
    ∀ mem, p.2.Prefix mem → ThreadNPn Arch.armv8 tid n (p.1, mem) (q.1, mem) :=
  nacertG_replay (SInv P l c) (fun hS hs ho => (step_sinv hC hR hS hs ho).1)
    (fun hS hb hp hs ho hm => replay_swp hC hR hS hb hp hs ho hm)

include hC hR in
theorem NACert.replay {l c : BitVec 64} {fuel tid : Nat} {t : Thread isa} {mem0 mem : Memory}
    (h : NACert fuel tid t mem0) (hS : SInv P l c t.st) (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) :
    NACert fuel tid t mem :=
  let ⟨t', hr, ht'⟩ := h; ⟨t', nacert_replay hC hR hr rfl hS hb mem hp, ht'⟩

include hC hR in
/-- **A worker that is not at its end and either has no promise or certifies
without fresh writes can take an instruction step** (semantic machine). -/
theorem instrEnabledSem_of {l c : BitVec 64} {fuel tid : Nat} {cfg : Config isa} {t : Thread isa}
    (ht : cfg.threads[tid]? = some t) (hS : SInv P l c t.st) (h16 : t.st.st.2 ≠ pcA 16)
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
    simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
    rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dn (hC.mov _ (hSt.at hC (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_rmw Arch.armv8 tid rfl hp0 hb
        (hC.swpa _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl)
      exact fin _ _ h1 h2 h3
    · exact dn (hC.cbz _ (hSt.at hC (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 tid hp0
        (hC.ldr _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl) (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · exact dn (hC.cbnz _ (hSt.at hC (by decide) (by decide) hpc))
    · exact dn (hC.btry _ (hSt.at hC (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_load Arch.armv8 tid hp0
        (hC.ldrc _ c (hSt.at hC (by decide) (by decide) hpc) hSt.x1 hSt.dc) (mem := cfg.mem)
      exact fin _ _ h1 h2 h3
    · exact dn (hC.add _ (hSt.at hC (by decide) (by decide) hpc))
    · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 tid hp0 hb
        (hC.strc _ c (hSt.at hC (by decide) (by decide) hpc) hSt.x1 hSt.dc)
      exact fin _ _ h1 h2 h3
    · rcases hR _ l (hSt.at hC (by decide) (by decide) hpc) hSt.x0 hSt.dl with hex | hex
      · obtain ⟨_, _, h1, h2, h3⟩ := en_store Arch.armv8 tid hp0 hb hex
        exact fin _ _ h1 h2 h3
      · obtain ⟨_, _, h1, h2, h3⟩ := en_rmw Arch.armv8 tid rfl hp0 hb hex
        exact fin _ _ h1 h2 h3
    · exact dn (hC.bdone _ (hSt.at hC (by decide) (by decide) hpc))
    · exact absurd hpc h16
  exact instrEnabledSem_of_nacertG ht hnil hn

end Kraken.Promising.Live.SpinSemSwpSolo
