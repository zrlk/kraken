/-
**Bounded certification for `treiber2`-shaped
workers, position-parametric** (route R2: the termination rank
applied to solo runs). Everything here is on the
*semantic* machine (`StepSem`/`ReachableSem`, `Arch.armv8`).

For the workers of `LiveTermTreiber2P.lean` (any `W` with `Cells W σ data`),
`n` threads, from the start configurations of `term_sem_genP`:

  **`CertBoundedFrom Arch.armv8 c0 (certF n)`, `certF n = 42 + 20 * (2 * n + 2)`
  (`= 82 + 40 * n`)**,

which depends on the thread count `n` only, not on any fuel
(`certBounded_genP`, `certBounded_genP'`). With `CertBounded.termTransfer`
the existing fixed-fuel `term_sem_genP` at fuel `certF n` becomes the fuel-free
`term_semU_genP : TermBoundSemU Arch.armv8 c0`.

## The argument

- **Headroom** (`head_of_certOkN`): along any run of a worker alone, the sum
  `S u + promAt top u.prom` (successful `CASAL`s executed plus outstanding
  promises to `top`) never drops: a write to `top` either fulfils a promise
  to `top` or appends, and in both cases raises `S` (`StepOK.eff`,
  `count_weff`). A certifying run ends with no promise and `S ≤ 2`
  (`sOf_le`), so a certifiable worker has `S + promAt top ≤ 2`.
- **The fuel-free invariant** `InvU` (proved along `ReachableSem` at every
  fuel, `InvU.step`): the existing `TermTreiber2P.Inv` with the promise-length
  bound `|prom| ≤ fuel` replaced by the headroom. The stepping thread's
  headroom comes from the certification its step carries; the other threads'
  states and promises do not change. With the existing count field,
  `#writes to top ≤ Σ (S + promAt top) ≤ 2 n` (`InvU.cnt_le`).
- **Solo runs are short** (`soloP_step`): along a run of a worker alone, the
  writes to `top` grow by at most the growth of `S`, so they stay at most
  `2 n + 2`; the existing rank `TermTreiber2P.R` at `N = 2 n + 2` drops at every
  step (`StepOK.rank`) and starts at most `42 + 20 N` (`rk_le`).
  `CertBounded.certBoundedFrom_of_soloRank` concludes.
-/
import Kraken.Promising.LiveTermTreiber2P
import Kraken.Promising.LiveCertBounded

namespace Kraken.Promising.Live.CertBoundedTreiber2P

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term Kraken.Promising.Live.CertBounded
open Kraken.Promising.Live.TermTreiber2 (topL fl rk sOf PcI)
open Kraken.Promising.Live.TermTreiber2P

/-- **The fuel-free certification bound for `n` workers**: the existing rank's
maximum `42 + 20 N` at `N = 2 n + 2` writes to `top`. -/
def certF (n : Nat) : Nat := 42 + 20 * (2 * n + 2)

/-- Two workers certify within `162` instructions. -/
example : certF 2 = 162 := rfl

/-- The rank table is at most `42 + 20 N`. -/
theorem rk_le (N p : Nat) (s : MachineData) (cnt : Nat) (cur : Val) : rk N p s cnt cur ≤ 42 + 20 * N := by
  have := fl_le s cur
  unfold rk; split <;> (try split) <;> omega

/-- One write grows the count of all writes to `l` by at most one, and by
none unless it is to `l`. -/
theorem cnt_weff {m m' : Memory} {p p' : List Time} {w : Msg} (l : Loc) (h : WEff m m' p p' w) :
    m.cntBelow l m.last ≤ m'.cntBelow l m'.last ∧
      m'.cntBelow l m'.last ≤ m.cntBelow l m.last + (if w.loc = l then 1 else 0) := by
  rcases h with ⟨rfl, -⟩ | ⟨-, -, -, rfl, -⟩
  · rw [cntBelow_append]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

theorem init_size {I : ISA} (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem : Config I).threads.size = states.length := by
  simp [Config.init]

variable [layout : _root_.Layout]

/-! ## One step of a worker alone -/

section Solo

variable {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data) {t : BitVec 64}
include C

/-- **What one step of a worker alone does** to the writes to `top`, its
successful `CASAL`s `S` and its promises to `top`. -/
theorem solo_step {N : Nat} {u : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hS : Static W σ data t u.st) (hP : PcOK W σ data u.st) (hpl : ∀ ts ∈ u.prom, ts ≤ mem.last)
    (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok o ∈ outs) :
    StepOK W σ data t N u mem o ∧ (∀ ts ∈ o.thread.prom, ts ≤ o.mem.last) ∧
      o.mem.cntBelow (topL t) o.mem.last + (S W σ data u + mem.promAt (topL t) u.prom) ≤
        mem.cntBelow (topL t) mem.last + (S W σ data o.thread + o.mem.promAt (topL t) o.thread.prom) ∧
      mem.cntBelow (topL t) mem.last ≤ o.mem.cntBelow (topL t) o.mem.last ∧
      o.mem.cntBelow (topL t) o.mem.last + S W σ data u ≤ mem.cntBelow (topL t) mem.last + S W σ data o.thread := by
  have r := thread_step (N := N) C hS hs ho hP
  refine ⟨r, ?_⟩
  rcases r.eff with ⟨hm, hp, hle⟩ | ⟨w, hw, hle⟩
  · rw [hm, hp]; exact ⟨hpl, by omega, Nat.le_refl _, by omega⟩
  · obtain ⟨e, hpl'⟩ := count_weff (l := topL t) hpl hw
    obtain ⟨c1, c2⟩ := cnt_weff (topL t) hw
    exact ⟨hpl', by omega, c1, by omega⟩

/-- **Headroom along a certifying run**: `S + promAt top` never drops along a
run of a worker alone, and is at most `2` where the promise set is empty. -/
theorem head_of_threadNPn {tid : Nat} :
    ∀ {n : Nat} {p q : Thread isa × Memory}, ThreadNPn Arch.armv8 tid n p q → q.1.prom = [] →
      Static W σ data t p.1.st → PcOK W σ data p.1.st → (∀ ts ∈ p.1.prom, ts ≤ p.2.last) →
      S W σ data p.1 + p.2.promAt (topL t) p.1.prom ≤ 2 := by
  intro n p q h
  induction h with
  | refl n p =>
    intro hq _ _ _
    have : S W σ data p.1 ≤ 2 := sOf_le _ _
    rw [hq]; simp only [Memory.promAt, List.countP_nil]; omega
  | step hs _ ih =>
    intro hq hS hP hpl
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    obtain ⟨r, hpl', h1, h2, -⟩ := solo_step (N := 0) C hS hP hpl hs ho
    have := ih hq r.st r.pc hpl'
    dsimp only at this
    omega

/-- **A certifiable worker has `S + promAt top ≤ 2`** (at any fuel). -/
theorem head_of_certOkN {tid n : Nat} {u : Thread isa} {mem : Memory}
    (hc : CertOkN Arch.armv8 tid u mem n) (hS : Static W σ data t u.st) (hP : PcOK W σ data u.st)
    (hpl : ∀ ts ∈ u.prom, ts ≤ mem.last) : S W σ data u + mem.promAt (topL t) u.prom ≤ 2 := by
  obtain ⟨u', mem', h, hp⟩ := hc
  exact head_of_threadNPn C h hp hS hP hpl

end Solo

/-! ## The fuel-free invariant -/

section Inv

variable {W : Program} {σ : Nat → Nat} {data : Bool}

/-- **The per-thread invariant, fuel-free**: `TermTreiber2P.TI` with the
promise-length bound replaced by the headroom. -/
structure TIU (W : Program) (σ : Nat → Nat) (data : Bool) (t : BitVec 64) (u : Thread isa) (mem : Memory) :
    Prop where
  st : Static W σ data t u.st
  pc : PcOK W σ data u.st
  fwd : Witness.FwdLeCoh u.views
  promLe : ∀ ts ∈ u.prom, ts ≤ mem.last
  head : S W σ data u + mem.promAt (topL t) u.prom ≤ 2

theorem TIU.mono {t : BitVec 64} {u : Thread isa} {mem mem' : Memory} (h : TIU W σ data t u mem)
    (hp : mem.Prefix mem') : TIU W σ data t u mem' :=
  ⟨h.st, h.pc, h.fwd, fun ts hts => Nat.le_trans (h.promLe ts hts) hp.last_le,
    by rw [promAt_prefix hp h.promLe]; exact h.head⟩

/-- **The invariant, fuel-free** (`TermTreiber2P.Inv` with `TIU`). -/
structure InvU (W : Program) (σ : Nat → Nat) (data : Bool) (n : Nat) (t : BitVec 64) (c : Config isa) :
    Prop where
  bnd : c.Bnd
  size : c.threads.size = n
  thr : ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u → TIU W σ data t u c.mem
  cnt : c.mem.cntBelow (topL t) c.mem.last ≤ tsum c fun _ u => S W σ data u + c.mem.promAt (topL t) u.prom

variable {n : Nat} {t : BitVec 64} {c : Config isa} {tid : Nat} {u : Thread isa}

/-- **At most `2 n` writes to `top`.** -/
theorem InvU.cnt_le (h : InvU W σ data n t c) : c.mem.cntBelow (topL t) c.mem.last ≤ 2 * n := by
  have h2 := tsum_le (c := c) (F := fun _ u => S W σ data u + c.mem.promAt (topL t) u.prom) (M := 2)
    fun j v hv => (h.thr j v hv).head
  rw [h.size] at h2
  have := h.cnt
  omega

/-- At fuel `0` the existing invariant has no promise, so it is the fuel-free
one. -/
theorem InvU.ofInv0 (h : TermTreiber2P.Inv W σ data 0 n t c) : InvU W σ data n t c :=
  ⟨h.bnd, h.size, fun i u hu => by
    have hT := h.thr i u hu
    have hp : u.prom = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hT.plen)
    have : S W σ data u ≤ 2 := sOf_le _ _
    exact ⟨hT.st, hT.pc, hT.fwd, hT.promLe, by rw [hp]; simp only [Memory.promAt, List.countP_nil]; omega⟩,
    h.cnt⟩

/-- The invariant after a step of `tid`. -/
theorem InvU.build (h : InvU W σ data n t c) (ht : c.threads[tid]? = some u) {u' : Thread isa}
    {mem' : Memory} (hpre : c.mem.Prefix mem') (hb : (c.withThread tid u' mem').Bnd)
    (hT : TIU W σ data t u' mem')
    (hcnt : mem'.cntBelow (topL t) mem'.last + (S W σ data u + c.mem.promAt (topL t) u.prom) ≤
      c.mem.cntBelow (topL t) c.mem.last + (S W σ data u' + mem'.promAt (topL t) u'.prom)) :
    InvU W σ data n t (c.withThread tid u' mem') := by
  refine ⟨hb, by rw [withThread_size]; exact h.size, fun i v hv => ?_, ?_⟩
  · rcases SpinStep.wt_get ht hv with ⟨-, rfl⟩ | ⟨-, hv⟩
    · exact hT
    · exact (h.thr i v hv).mono hpre
  · have e := tsum_withThread_add (t' := u') (mem' := mem')
      (F := fun (_ : Nat) (v : Thread isa) => S W σ data v + c.mem.promAt (topL t) v.prom)
      (F' := fun (_ : Nat) (v : Thread isa) => S W σ data v + mem'.promAt (topL t) v.prom) ht fun i v _ hv => by
        simp only [promAt_prefix hpre (h.thr i v hv).promLe]
    have := h.cnt
    show mem'.cntBelow (topL t) mem'.last ≤
      tsum (c.withThread tid u' mem') fun _ v => S W σ data v + mem'.promAt (topL t) v.prom
    omega

/-- **A semantic step at any fuel keeps the fuel-free invariant**: the
stepping thread's headroom comes from the certification the step carries
(`head_of_certOkN`). -/
theorem InvU.step (C : Cells W σ data) (h : InvU W σ data n t c) {fuel : Nat} {c' : Config isa}
    (hst : StepSem Arch.armv8 fuel tid c c') : InvU W σ data n t c' := by
  have hb := h.bnd.semStep hst
  rcases hst with ⟨u, outs, o, ht, hs, ho, hc, rfl⟩ | ⟨u, w, ht, -, hc, rfl⟩
  · have hT := h.thr tid u ht
    obtain ⟨r, hpl', hcnt, -, -⟩ := solo_step (N := 0) C hT.st hT.pc hT.promLe hs ho
    exact h.build ht (stepOne_dord _ hs ho).2.2.1 hb
      ⟨r.st, r.pc, Witness.stepOne_fwdLeCoh hs ho hT.fwd, hpl', head_of_certOkN C hc r.st r.pc hpl'⟩ hcnt
  · have hT := h.thr tid u ht
    have hlast : (c.mem.append w).1.last = c.mem.last + 1 := by simp [Memory.append, Memory.last]
    have hpl' : ∀ ts ∈ (promThread u c.mem w).prom, ts ≤ (c.mem.append w).1.last := fun ts hts => by
      rw [hlast]
      rcases List.mem_append.mp hts with hts | hts
      · exact Nat.le_succ_of_le (hT.promLe ts hts)
      · rw [List.mem_singleton] at hts; rw [hts]; exact Nat.le_refl _
    refine h.build ht (Memory.Prefix.append _ _) hb
      ⟨hT.st, hT.pc, hT.fwd, hpl', head_of_certOkN C hc hT.st hT.pc hpl'⟩ ?_
    show _ + (S W σ data u + _) ≤
      _ + (S W σ data u + (c.mem.append w).1.promAt (topL t) (u.prom ++ [(c.mem.append w).2]))
    rw [cntBelow_append, promAt_promise w hT.promLe]
    omega

/-- The invariant at the start configurations of `term_sem_genP`. -/
theorem InvU.init {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, Static W σ data t s ∧ s.st.2 = pcS W σ (startPos data)) :
    InvU W σ data states.length t (Config.init states initMem) := by
  refine ⟨Config.init_bnd _ _, init_size _ _, fun i u hu => ?_, ?_⟩
  · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hu
    obtain ⟨s, hm, rfl⟩ := hu
    obtain ⟨hS, hpc⟩ := hs s (List.mem_of_getElem? hm)
    have : S W σ data (Thread.init s) ≤ 2 := sOf_le _ _
    exact ⟨hS, ⟨_, by cases data <;> decide, hpc, by cases data <;> trivial⟩, Witness.fwdLeCoh_of_nil rfl,
      fun ts h => by simp [Thread.init] at h, by
        have hp : (Thread.init s : Thread isa).prom = [] := by simp [Thread.init]
        rw [hp]; simp only [Memory.promAt, List.countP_nil, Nat.add_zero]; exact this⟩
  · have : (Config.init states initMem : Config isa).mem.last = 0 := rfl
    rw [this]
    exact Nat.zero_le _

end Inv

/-! ## Solo runs are short -/

section Rank

variable {W : Program} {σ : Nat → Nat} {data : Bool} (C : Cells W σ data) {t : BitVec 64}

/-- The step invariant of a run of a worker alone from a configuration with
`n` threads satisfying `InvU`. -/
def SoloP (W : Program) (σ : Nat → Nat) (data : Bool) (n : Nat) (t : BitVec 64) (p : Thread isa × Memory) :
    Prop :=
  Static W σ data t p.1.st ∧ PcOK W σ data p.1.st ∧ Witness.FwdLeCoh p.1.views ∧ p.1.Bnd p.2.last ∧
    (∀ ts ∈ p.1.prom, ts ≤ p.2.last) ∧ p.2.cntBelow (topL t) p.2.last ≤ 2 * n + S W σ data p.1

include C in
/-- **A step of a worker alone keeps `SoloP` and lowers the rank at
`N = 2 n + 2`.** -/
theorem soloP_step {n tid : Nat} {p q : Thread isa × Memory} (hp : SoloP W σ data n t p)
    (hq : ThreadStep Arch.armv8 tid p q) :
    SoloP W σ data n t q ∧ R W σ data (2 * n + 2) t q.1 q.2 < R W σ data (2 * n + 2) t p.1 p.2 := by
  obtain ⟨hS, hP, hf, hb, hpl, hc⟩ := hp
  obtain ⟨outs, o, hs, ho, rfl⟩ := hq
  obtain ⟨r, hpl', -, -, hc'⟩ := solo_step (N := 2 * n + 2) C hS hP hpl hs ho
  have hS2 : S W σ data o.thread ≤ 2 := sOf_le _ _
  have hc2 : o.mem.cntBelow (topL t) o.mem.last ≤ 2 * n + S W σ data o.thread := by omega
  refine ⟨⟨r.st, r.pc, Witness.stepOne_fwdLeCoh hs ho hf, (stepOne_bnd _ hs ho hb).1, hpl', hc2⟩,
    r.rank hf (hb.views.le.coh (topL t)) ?_⟩
  have := cntBelow_le_last o.mem (topL t) (o.thread.views.getCoh (topL t))
  omega

include C in
/-- **Bounded certification from any `InvU` start** (semantic machine, every
fuel): `CertBoundedFrom Arch.armv8 c0 (certF n)`. -/
theorem certBounded_genP' {n : Nat} {c0 : Config isa} (h0 : InvU W σ data n t c0) :
    CertBoundedFrom Arch.armv8 c0 (certF n) :=
  certBoundedFrom_of_soloRank (InvU W σ data n t) h0 (fun _ _ _ _ h hst => h.step C hst)
    (fun _ _ => SoloP W σ data n t) (fun _ _ p => R W σ data (2 * n + 2) t p.1 p.2)
    (fun c tid u h hu => by
      have hT := h.thr tid u hu
      have := h.cnt_le
      exact ⟨hT.st, hT.pc, hT.fwd, h.bnd tid u hu, hT.promLe, by dsimp only; omega⟩)
    (fun _ _ _ _ _ hp hq => soloP_step C hp hq) (fun _ _ _ _ _ => rk_le _ _ _ _ _)

include C in
/-- **Bounded certification for `treiber2`-shaped workers** (semantic
machine, every fuel): from the start configurations of `term_sem_genP` with
`n = |states|` threads, every certification of a reachable thread fits in
`certF n = 42 + 20 * (2 * n + 2)` instructions. Independent of fuel. -/
theorem certBounded_genP {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, Static W σ data t s ∧ s.st.2 = pcS W σ (startPos data)) :
    CertBoundedFrom Arch.armv8 (Config.init states initMem : Config isa) (certF states.length) :=
  certBounded_genP' C (InvU.init hs)

include C in
/-- **Termination of `treiber2`-shaped workers on the fuel-free semantic
machine, under every schedule** (`TermBoundSemU`, no fairness): every
`TraceSemU` from the start configuration, whatever certification length each
step uses, is final at one index `K`. From `term_sem_genP` at fuel
`certF |states|` by `certBounded_genP` and `CertBounded.termTransfer`. -/
theorem term_semU_genP {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, Static W σ data t s ∧ s.st.2 = pcS W σ (startPos data)) :
    TermBoundSemU Arch.armv8 (Config.init states initMem : Config isa) :=
  termTransfer (certBounded_genP C hs) (term_sem_genP C t hs)

end Rank

end Kraken.Promising.Live.CertBoundedTreiber2P
