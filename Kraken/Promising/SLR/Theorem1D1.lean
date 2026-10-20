/-
Case (d1) of Theorem 1′'s induction (O3):
a promise of thread `j` at real step `J` that is fulfilled on the path by a
release store (`RelFulfilled`) at real step `f`.

The micro-run takes several micro-steps within the one real step `J`
(`PExt`, `PRun.ext`): first `j` *replays* its own instructions of the path
from its current target up to `f`, on hybrid configurations (the virtual
configuration at `J` with `j`'s thread replaced by its real state restricted
to the memory at `J`; these steps are `StutterStep`s since the new promise
stays outstanding until `f`, so they replay against `M_J`:
`stepOne_restrict`), each an `np` micro-step from `j`'s token
(`NPSafe.stepAt`); then a `prepay` micro-step from `j`'s token
(`NPSafe.prepayAt`). Afterwards `j` is advanced with target `f`.

## Generic chain

`caseD1'` needs `GuardOK G` (the prepay hypothesis replays on the restricted
thread, `GuardOK.restrict`), `GuardOK GV` and `G ≤ GV` (the fulfilling
instruction's guard becomes the advanced thread's status). The existing names
are the instances at `G₀`, `GRF`, `K2₀` (end of file).
-/
import Kraken.Promising.SLR.Theorem1Proof

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## Extending a prefix run by several micro-steps -/

section Ext

variable {G GV : PrepayGuard I} {KF : K2Frame (model I)} {Er : ErasureP I} {A : Arch} {fuel : Nat} {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}

/-- Every thread state of `c` is a real thread state of the path, with (some
of) its promises (`AnnRun'.real`). -/
def RealIn (π : Path A fuel I) (c : Config I) : Prop :=
  ∀ (s : Nat) (t : Thread I), c.threads[s]? = some t →
    ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧
      ∀ p ∈ t.prom, p ∈ tj.prom

/-- **An extension of a prefix run** `R` by `K` micro-steps, all within the
real step `J → J + 1`: the fields of `PRun'` for the new micro-indices. -/
structure PExt' (R : PRun' GV KF Er A π B g0 J) where
  K : Nat
  cfg : Nat → Config I
  rF : Nat → Nat → Res
  g : Nat → Ghost
  cfg_zero : cfg 0 = R.cfg R.N
  rF_zero : rF 0 = R.rF R.N
  g_zero : g 0 = R.g R.N
  erase : ∀ μ, μ ≤ K → Er (rF μ) (g μ) (fun _ => True) (cfg μ)
  step : ∀ μ, μ < K → MicroStep' KF A (cfg μ) (rF μ) (g μ) (cfg (μ + 1)) (rF (μ + 1)) (g (μ + 1))
  mem : ∀ μ, μ ≤ K → ∃ j, j ≤ π.len ∧ (cfg μ).mem = (π.cfg j).mem
  real : ∀ μ, μ ≤ K → RealIn π (cfg μ)
  le0 : ∀ μ, μ ≤ K → g0.Le (g μ)

/-- Full erasure at every micro-index of the extension below `μ'`. -/
def PExt'.Clean {R : PRun' GV KF Er A π B g0 J} (X : PExt' R) (μ' : Nat) : Prop :=
  ∀ μ, μ < μ' → Er (X.rF μ) (X.g μ) (fun _ => False) (X.cfg μ)

/-- The empty extension. -/
def PExt'.nil (R : PRun' GV KF Er A π B g0 J) : PExt' R where
  K := 0
  cfg := fun _ => R.cfg R.N
  rF := fun _ => R.rF R.N
  g := fun _ => R.g R.N
  cfg_zero := rfl
  rF_zero := rfl
  g_zero := rfl
  erase := fun _ _ => R.erase R.N (Nat.le_refl _)
  step := fun _ h => absurd h (Nat.not_lt_zero _)
  mem := fun _ _ => R.mem R.N (Nat.le_refl _)
  real := fun _ _ => R.real R.N (Nat.le_refl _)
  le0 := fun _ _ => R.le0 R.N (Nat.le_refl _)

/-- Extend by one micro-step. -/
def PExt'.snoc {R : PRun' GV KF Er A π B g0 J} (X : PExt' R) (c' : Config I) (rF' : Nat → Res) (g' : Ghost)
    (E : Er rF' g' (fun _ => True) c') (hstep : MicroStep' KF A (X.cfg X.K) (X.rF X.K) (X.g X.K) c' rF' g')
    (hmem : ∃ j, j ≤ π.len ∧ c'.mem = (π.cfg j).mem) (hreal : RealIn π c') (hle : g0.Le g') : PExt' R where
  K := X.K + 1
  cfg μ := if μ ≤ X.K then X.cfg μ else c'
  rF μ := if μ ≤ X.K then X.rF μ else rF'
  g μ := if μ ≤ X.K then X.g μ else g'
  cfg_zero := by simp only [Nat.zero_le, ↓reduceIte]; exact X.cfg_zero
  rF_zero := by simp only [Nat.zero_le, ↓reduceIte]; exact X.rF_zero
  g_zero := by simp only [Nat.zero_le, ↓reduceIte]; exact X.g_zero
  erase μ hμ := by
    by_cases h : μ ≤ X.K
    · simp only [h, ↓reduceIte]; exact X.erase μ h
    · simp only [h, ↓reduceIte]; exact E
  step μ hμ := by
    by_cases h : μ + 1 ≤ X.K
    · simp only [show μ ≤ X.K by omega, h, ↓reduceIte]; exact X.step μ (by omega)
    · obtain rfl : μ = X.K := by omega
      simp only [Nat.le_refl, h, ↓reduceIte]; exact hstep
  mem μ hμ := by
    by_cases h : μ ≤ X.K
    · simp only [h, ↓reduceIte]; exact X.mem μ h
    · simp only [h, ↓reduceIte]; exact hmem
  real μ hμ := by
    by_cases h : μ ≤ X.K
    · simp only [h, ↓reduceIte]; exact X.real μ h
    · simp only [h, ↓reduceIte]; exact hreal
  le0 μ hμ := by
    by_cases h : μ ≤ X.K
    · simp only [h, ↓reduceIte]; exact X.le0 μ h
    · simp only [h, ↓reduceIte]; exact hle

section SnocLemmas

variable {R : PRun' GV KF Er A π B g0 J} (X : PExt' R) {c' : Config I} {rF' : Nat → Res} {g' : Ghost}
  {E : Er rF' g' (fun _ => True) c'} {hstep : MicroStep' KF A (X.cfg X.K) (X.rF X.K) (X.g X.K) c' rF' g'}
  {hmem : ∃ j, j ≤ π.len ∧ c'.mem = (π.cfg j).mem} {hreal : RealIn π c'} {hle : g0.Le g'}

theorem PExt'.snoc_K : (X.snoc c' rF' g' E hstep hmem hreal hle).K = X.K + 1 := rfl

theorem PExt'.snoc_cfg : (X.snoc c' rF' g' E hstep hmem hreal hle).cfg (X.K + 1) = c' := by
  simp only [PExt'.snoc, show ¬ (X.K + 1 ≤ X.K) by omega, ↓reduceIte]

theorem PExt'.snoc_rF : (X.snoc c' rF' g' E hstep hmem hreal hle).rF (X.K + 1) = rF' := by
  simp only [PExt'.snoc, show ¬ (X.K + 1 ≤ X.K) by omega, ↓reduceIte]

theorem PExt'.snoc_g : (X.snoc c' rF' g' E hstep hmem hreal hle).g (X.K + 1) = g' := by
  simp only [PExt'.snoc, show ¬ (X.K + 1 ≤ X.K) by omega, ↓reduceIte]

/-- The validity of the extension by one more step gives the validity of the
old one and full erasure at its last configuration. -/
theorem PExt'.snoc_clean (h : (X.snoc c' rF' g' E hstep hmem hreal hle).Clean (X.K + 1)) :
    X.Clean X.K ∧ Er (X.rF X.K) (X.g X.K) (fun _ => False) (X.cfg X.K) := by
  refine ⟨fun μ hμ => ?_, ?_⟩
  · have := h μ (by omega)
    simp only [PExt'.snoc, show μ ≤ X.K by omega, ↓reduceIte] at this
    exact this
  · have := h X.K (by omega)
    simp only [PExt'.snoc, Nat.le_refl, ↓reduceIte] at this
    exact this

end SnocLemmas

/-- The configurations of the prefix run extended by `X`. -/
def PRun'.extCfg (R : PRun' GV KF Er A π B g0 J) (X : PExt' R) (μ : Nat) : Config I :=
  if μ ≤ R.N then R.cfg μ else X.cfg (μ - R.N)

def PRun'.extRF (R : PRun' GV KF Er A π B g0 J) (X : PExt' R) (μ : Nat) : Nat → Res :=
  if μ ≤ R.N then R.rF μ else X.rF (μ - R.N)

def PRun'.extG (R : PRun' GV KF Er A π B g0 J) (X : PExt' R) (μ : Nat) : Ghost :=
  if μ ≤ R.N then R.g μ else X.g (μ - R.N)

section ExtLemmas

variable (R : PRun' GV KF Er A π B g0 J) (X : PExt' R)

theorem PRun'.extCfg_lo {μ : Nat} (h : μ ≤ R.N) : R.extCfg X μ = R.cfg μ := by simp [PRun'.extCfg, h]
theorem PRun'.extRF_lo {μ : Nat} (h : μ ≤ R.N) : R.extRF X μ = R.rF μ := by simp [PRun'.extRF, h]
theorem PRun'.extG_lo {μ : Nat} (h : μ ≤ R.N) : R.extG X μ = R.g μ := by simp [PRun'.extG, h]

theorem PRun'.extCfg_hi {μ : Nat} (h : R.N ≤ μ) : R.extCfg X μ = X.cfg (μ - R.N) := by
  unfold PRun'.extCfg
  by_cases h' : μ ≤ R.N
  · obtain rfl : μ = R.N := by omega
    simp [X.cfg_zero]
  · simp [h']

theorem PRun'.extRF_hi {μ : Nat} (h : R.N ≤ μ) : R.extRF X μ = X.rF (μ - R.N) := by
  unfold PRun'.extRF
  by_cases h' : μ ≤ R.N
  · obtain rfl : μ = R.N := by omega
    simp [X.rF_zero]
  · simp [h']

theorem PRun'.extG_hi {μ : Nat} (h : R.N ≤ μ) : R.extG X μ = X.g (μ - R.N) := by
  unfold PRun'.extG
  by_cases h' : μ ≤ R.N
  · obtain rfl : μ = R.N := by omega
    simp [X.g_zero]
  · simp [h']

end ExtLemmas

/-- **Extend a prefix run by an extension** to the next real index: the last
configuration of the extension is the virtual configuration at `J + 1`. -/
def PRun'.ext (R : PRun' GV KF Er A π B g0 J) (X : PExt' R) (hV : (π.cfg (J + 1)).VirtualOfG GV A (X.cfg X.K))
    (hdone : R.Clean GV KF Er A π B g0 R.N ∧ X.Clean X.K →
      ∀ tid, (X.cfg X.K).Done tid → B (X.cfg X.K) (X.rF X.K tid) (X.g X.K)) :
    PRun' GV KF Er A π B g0 (J + 1) where
  N := R.N + X.K
  cfg := R.extCfg X
  rF := R.extRF X
  g := R.extG X
  pos k := if k ≤ J then R.pos k else R.N + X.K
  pos_zero := by simp [R.pos_zero]
  pos_mono k hk := by
    by_cases h : k + 1 ≤ J
    · simp only [show k ≤ J by omega, h, ↓reduceIte]; exact R.pos_mono k (by omega)
    · simp only [show k ≤ J by omega, h, ↓reduceIte]; rw [show k = J by omega, R.pos_J]; omega
  pos_J := by simp only [show ¬ (J + 1 ≤ J) by omega, ↓reduceIte]
  cfg_zero := by rw [R.extCfg_lo X (Nat.zero_le _)]; exact R.cfg_zero
  erase μ hμ := by
    by_cases h : μ ≤ R.N
    · rw [R.extCfg_lo X h, R.extRF_lo X h, R.extG_lo X h]; exact R.erase μ h
    · rw [R.extCfg_hi X (by omega), R.extRF_hi X (by omega), R.extG_hi X (by omega)]
      exact X.erase _ (by omega)
  step μ hμ := by
    by_cases h : μ + 1 ≤ R.N
    · rw [R.extCfg_lo X (by omega), R.extRF_lo X (by omega), R.extG_lo X (by omega),
        R.extCfg_lo X h, R.extRF_lo X h, R.extG_lo X h]
      exact R.step μ (by omega)
    · rw [R.extCfg_hi X (by omega), R.extRF_hi X (by omega), R.extG_hi X (by omega),
        R.extCfg_hi X (by omega), R.extRF_hi X (by omega), R.extG_hi X (by omega),
        show μ + 1 - R.N = μ - R.N + 1 by omega]
      exact X.step _ (by omega)
  virtual k hk := by
    by_cases h : k ≤ J
    · simp only [h, ↓reduceIte]
      rw [R.extCfg_lo X (R.pos_le GV KF Er A π B g0 k h)]
      exact R.virtual k h
    · obtain rfl : k = J + 1 := by omega
      simp only [h, ↓reduceIte]
      rw [R.extCfg_hi X (by omega), show R.N + X.K - R.N = X.K by omega]
      exact hV
  mem μ hμ := by
    by_cases h : μ ≤ R.N
    · rw [R.extCfg_lo X h]; exact R.mem μ h
    · rw [R.extCfg_hi X (by omega)]; exact X.mem _ (by omega)
  real μ hμ := by
    by_cases h : μ ≤ R.N
    · rw [R.extCfg_lo X h]; exact R.real μ h
    · rw [R.extCfg_hi X (by omega)]; exact X.real _ (by omega)
  le0 μ hμ := by
    by_cases h : μ ≤ R.N
    · rw [R.extG_lo X h]; exact R.le0 μ h
    · rw [R.extG_hi X (by omega)]; exact X.le0 _ (by omega)
  doneB k hk hc tid hd := by
    by_cases h : k ≤ J
    · simp only [h, ↓reduceIte] at hc hd ⊢
      have hp := R.pos_le GV KF Er A π B g0 k h
      rw [R.extCfg_lo X hp] at hd ⊢
      rw [R.extRF_lo X hp, R.extG_lo X hp]
      refine R.doneB k h (fun μ hμ => ?_) tid hd
      have := hc μ hμ
      rw [R.extCfg_lo X (by omega), R.extRF_lo X (by omega), R.extG_lo X (by omega)] at this
      exact this
    · simp only [h, ↓reduceIte] at hc hd ⊢
      rw [R.extCfg_hi X (by omega), show R.N + X.K - R.N = X.K by omega] at hd ⊢
      rw [R.extRF_hi X (by omega), R.extG_hi X (by omega), show R.N + X.K - R.N = X.K by omega]
      refine hdone ⟨fun μ hμ => ?_, fun μ hμ => ?_⟩ tid hd
      · have := hc μ (by omega)
        rw [R.extCfg_lo X (by omega), R.extRF_lo X (by omega), R.extG_lo X (by omega)] at this
        exact this
      · have := hc (R.N + μ) (by omega)
        rw [R.extCfg_hi X (by omega), R.extRF_hi X (by omega), R.extG_hi X (by omega),
          show R.N + μ - R.N = μ by omega] at this
        exact this

section ExtRun

variable (R : PRun' GV KF Er A π B g0 J) (X : PExt' R) {hV : (π.cfg (J + 1)).VirtualOfG GV A (X.cfg X.K)}
  {hdone : R.Clean GV KF Er A π B g0 R.N ∧ X.Clean X.K →
      ∀ tid, (X.cfg X.K).Done tid → B (X.cfg X.K) (X.rF X.K tid) (X.g X.K)}

theorem PRun'.ext_N : (R.ext X hV hdone).N = R.N + X.K := rfl

theorem PRun'.ext_cfg : (R.ext X hV hdone).cfg (R.ext X hV hdone).N = X.cfg X.K := by
  show R.extCfg X (R.N + X.K) = _
  rw [R.extCfg_hi X (by omega), show R.N + X.K - R.N = X.K by omega]

theorem PRun'.ext_rF : (R.ext X hV hdone).rF (R.ext X hV hdone).N = X.rF X.K := by
  show R.extRF X (R.N + X.K) = _
  rw [R.extRF_hi X (by omega), show R.N + X.K - R.N = X.K by omega]

theorem PRun'.ext_g : (R.ext X hV hdone).g (R.ext X hV hdone).N = X.g X.K := by
  show R.extG X (R.N + X.K) = _
  rw [R.extG_hi X (by omega), show R.N + X.K - R.N = X.K by omega]

/-- The validity of the extended run gives that of the old run and of the
extension. -/
theorem PRun'.ext_clean (h : (R.ext X hV hdone).Clean GV KF Er A π B g0 (R.ext X hV hdone).N) :
    R.Clean GV KF Er A π B g0 R.N ∧ X.Clean X.K := by
  refine ⟨fun μ hμ => ?_, fun μ hμ => ?_⟩
  · have := h μ (by show μ < R.N + X.K; omega)
    change Er (R.extRF X μ) (R.extG X μ) _ (R.extCfg X μ) at this
    rw [R.extCfg_lo X (by omega), R.extRF_lo X (by omega), R.extG_lo X (by omega)] at this
    exact this
  · have := h (R.N + μ) (by show R.N + μ < R.N + X.K; omega)
    change Er (R.extRF X _) (R.extG X _) _ (R.extCfg X _) at this
    rw [R.extCfg_hi X (by omega), R.extRF_hi X (by omega), R.extG_hi X (by omega),
      show R.N + μ - R.N = μ by omega] at this
    exact this

end ExtRun

end Ext

/-! ## Helpers: the prepay conjunct, and the frame with a new pending mark -/

section Helpers

variable {G GV : PrepayGuard I} {KF : K2Frame (model I)} {A : Arch} {fuel : Nat}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))


/-- **The status of a thread that does not step, with a new pending mark**
(`status_frameG` where the new ghost may also mark `tsN` pending, a timestamp
that is never a promise of `i` from `J` on). -/
theorem status_frameG' [I.LawfulState] {π : Path A fuel I} {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J < π.len)
    {v v' : Config I} {g g' : Ghost} {i p : Nat} {tsN : Time}
    (hthr : (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]?)
    (hvv : v'.threads[i]? = v.threads[i]?)
    (hkeep : ∀ ts ∈ g.pend, (∃ t, v'.threads[i]? = some t ∧ ts ∈ t.prom) → ts ∈ g'.pend)
    (hback : ∀ ts ∈ g'.pend, ts ∈ g.pend ∨ ts = tsN)
    (hnotN : ∀ q tq, J ≤ q → q ≤ π.len → (π.cfg q).threads[i]? = some tq → tsN ∉ tq.prom)
    (hrestr : ∀ q tq, J < q → q ≤ π.len → (π.cfg q).threads[i]? = some tq →
      tq.restrict (π.cfg (J + 1)).mem = tq.restrict (π.cfg J).mem)
    (hJp : J ≤ p) (hst : Status' GV A π J v g i p) :
    ∃ p', J + 1 ≤ p' ∧ p' ≤ π.len ∧ (π.len - p') + (π.len - (J + 1)) ≤ (π.len - p) + (π.len - J) ∧
      Status' GV A π (J + 1) v' g' i p' := by
  rcases hst with ⟨hpJ, hv, hnp⟩ | ⟨hpl, tp, htp, hv, ⟨ts, hpend, htsp, hrel, hq⟩, ⟨tp', htp', hnps, hful⟩⟩
  · refine ⟨J + 1, Nat.le_refl _, hJ, by omega, .inl ⟨rfl, by rw [hvv, hv, hthr], fun t ht ts hts hp => ?_⟩⟩
    have ht' : v.threads[i]? = some t := by rw [← hvv]; exact ht
    rcases hback ts hp with hp | rfl
    · exact hnp t ht' ts hts hp
    · rw [hv] at ht'
      exact hnotN J t (Nat.le_refl _) (Nat.le_of_lt hJ) ht' hts
  · have hpJ : J ≠ p := by
      rintro rfl
      rw [hthr, htp] at htp'
      cases htp'
      exact hful ts hpend htsp htsp
    refine ⟨p, by omega, Nat.le_of_lt hpl, by omega, .inr ⟨hpl, tp, htp, ?_,
      ⟨ts, ?_, htsp, hrel, fun q h1 h2 => hq q (by omega) h2⟩,
      ⟨tp', htp', hnps, fun ts' h' h'' => ?_⟩⟩⟩
    · rw [hvv, hv, hrestr p tp (by omega) (Nat.le_of_lt hpl) htp]
    · apply hkeep ts hpend
      obtain ⟨tJ, htJ, htsJ⟩ := hq J (Nat.le_refl _) hJp
      have hle := ((π.wf h0 J (by omega)) i tJ htJ).2 ts htsJ
      refine ⟨tp.restrict (π.cfg J).mem, by rw [hvv, hv], ?_⟩
      simp only [Thread.restrict]
      exact List.mem_filter.mpr ⟨htsp, by simpa using hle⟩
    · rcases hback ts' h' with h' | rfl
      · exact hful ts' h' h''
      · exact absurd h'' (hnotN p tp hJp (Nat.le_of_lt hpl) htp)

end Helpers

/-! ## Case (d1) -/

section D1

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem caseD1' {G GV : PrepayGuard I} {KF : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) [I.LawfulState] {A : Arch} {fuel : Nat} : CaseD1' (I := I) G GV KF Er S A fuel := by
  intro π B g0 states initMem h0 hfin hNT J hJ R hok j t pw ht hw hJ1 hrf
  obtain ⟨f, hJf, hfl, hint, tf, tf', htf, hrelfL, htf', htsf'⟩ := hrf
  have hrelf := hGV _ _ _ _ _ hrelfL
  have hV := R.virtual J (Nat.le_refl _)
  rw [R.pos_J] at hV
  obtain ⟨hvm, hvs, -⟩ := hV
  have hjn : j < (π.cfg J).threads.size := lt_size_of_get? ht
  have hjv : j < (R.cfg R.N).threads.size := by rw [hvs]; exact hjn
  have hthj : (π.cfg (J + 1)).threads[j]? = some { t with prom := t.prom ++ [(π.cfg J).mem.last + 1] } := by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_left rfl]; rfl
  have hthr : ∀ i, i ≠ j → (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]? := fun i hi => by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_right (Ne.symm hi)]
  have hJ1m : (π.cfg (J + 1)).mem = ((π.cfg J).mem.append { pw.1 with tid := j }).1 := by rw [hJ1]; rfl
  have hJ1last : (π.cfg (J + 1)).mem.last = (π.cfg J).mem.last + 1 := by rw [hJ1m, Memory.last_append]
  have E0 := R.erase R.N (Nat.le_refl _)
  have hfl' : f ≤ π.len := Nat.le_of_lt hfl
  have htsf : (π.cfg J).mem.last + 1 ∈ tf.prom := by
    obtain ⟨tq, htq, h⟩ := hint f hJf (Nat.le_refl _)
    rw [htf] at htq; cases htq; exact h
  have hlive : ∀ q, q ≤ π.len → ∀ i, (π.cfg q).WfProm i := fun q hq i =>
    liveWfProm A fuel states initMem _ (by rw [← h0]; exact π.reachable q hq) (π.live hfin q hq) i
  have hrestr : ∀ (i : Nat) (ti : Thread I), (R.cfg R.N).threads[i]? = some ti →
      ∃ (q : Nat) (tq : Thread I), J ≤ q ∧ q ≤ π.len ∧ (π.cfg q).threads[i]? = some tq ∧
        ti = tq.restrict (π.cfg J).mem := by
    intro i ti hti
    obtain ⟨pi, _, _, _, hJpi, hpli, _, _, _, _, _, hsti⟩ := hok i (lt_size_of_get? hti)
    exact Status'.restrictOf h0 (by omega) hpli hJpi hsti hti
  have hinv0 : (R.cfg R.N).MachInv := machInv_of_restrict h0 hvm hrestr
  -- a pending promise that is a promise of `j` at a later index is `j`'s in the virtual configuration
  have hpendj : ∀ ts', ts' ∈ (R.g R.N).pend → ∀ q tq, J ≤ q → q ≤ π.len → (π.cfg q).threads[j]? = some tq →
      ts' ∈ tq.prom → ∃ tv, (R.cfg R.N).threads[j]? = some tv ∧ ts' ∈ tv.prom := by
    intro ts' hp q tq hJq hq htq hts'
    obtain ⟨-, i, ti, hti, htsi⟩ := (ErOK.toErase E0).pend ts' hp
    obtain ⟨w, hw1, hw2⟩ := hinv0.promWf i ti hti ts' htsi
    obtain ⟨w', hw1', hw2'⟩ := (π.machInv h0 q hq).promWf j tq htq ts' hts'
    rw [hvm] at hw1
    have hle := (π.cfg J).mem.last_le_of_get?_eq_some hw1
    rw [(π.mem_prefix hJq hq).get? hle, hw1] at hw1'
    cases hw1'
    obtain rfl : i = j := hw2.symm.trans hw2'
    exact ⟨ti, hti, htsi⟩
  obtain ⟨p, s, gs, n, hJp, hpl, hsafe, hext, hgs, hown, hbud, hst⟩ := hok j hjv
  -- the start of the replay: `q0`, with `j`'s virtual thread its real state at `q0` restricted to `M_J`
  have hstart : ∃ q0 tq0, J + 1 ≤ q0 ∧ q0 ≤ f ∧ (π.cfg q0).threads[j]? = some tq0 ∧
      (R.cfg R.N).threads[j]? = some (tq0.restrict (π.cfg J).mem) ∧ (π.len - q0) + (π.len - J) < n ∧
      (∀ ts', ts' ∈ (R.g R.N).pend → ts' ∈ tf.prom → ts' ∉ tf'.prom) ∧
      -- every replay step of `j` fulfils `j`'s pending promises (the step guard's condition)
      ∀ q tq tq', q0 ≤ q → q < f → (π.cfg q).threads[j]? = some tq → (π.cfg (q + 1)).threads[j]? = some tq' →
        ∀ ts', ts' ∈ (R.g R.N).pend → ts' ∈ tq.prom → ts' ∉ tq'.prom := by
    rcases hst with ⟨hpJ, hv, hnp⟩ | ⟨hpl', tp, htp, hv, ⟨ts0, hpend, htsp, hrel, hq⟩, hlast⟩
    · have hvj : (R.cfg R.N).threads[j]? = some t := by rw [hv, ht]
      have hres : ({ t with prom := t.prom ++ [(π.cfg J).mem.last + 1] } : Thread I).restrict (π.cfg J).mem = t := by
        have hle := ((π.wf h0 J (by omega)) j t ht).2
        show { t with prom := (t.prom ++ [(π.cfg J).mem.last + 1]).filter _ } = t
        rw [List.filter_append, List.filter_eq_self.mpr (fun x hx => decide_eq_true (hle x hx))]
        have : ¬ ((π.cfg J).mem.last + 1 ≤ (π.cfg J).mem.last) := by omega_t
        simp [this]
      refine ⟨J + 1, _, Nat.le_refl _, hJf, hthj, by rw [hres]; exact hvj, by omega, fun ts' hp hts' _ => ?_,
        fun q tq _ hq0 hqf htq _ ts' hp hts' _ => ?_⟩
      · obtain ⟨tv, htv, htsv⟩ := hpendj ts' hp f tf (by omega) hfl' htf hts'
        rw [hvj] at htv; cases htv
        exact hnp t hvj ts' htsv hp
      · obtain ⟨tv, htv, htsv⟩ := hpendj ts' hp q tq (by omega) (by omega) htq hts'
        rw [hvj] at htv; cases htv
        exact hnp t hvj ts' htsv hp
    · obtain ⟨tJ, htJ, hts0J⟩ := hq J (Nat.le_refl _) hJp
      rw [ht] at htJ; cases htJ
      obtain ⟨tp', htp', hnps, hful⟩ := hlast
      have hJp' : J < p := by
        rcases Nat.lt_or_ge J p with h | h
        · exact h
        · exfalso
          obtain rfl : J = p := by omega
          rw [ht] at htp; cases htp
          rw [hthj] at htp'; cases htp'
          exact hful ts0 hpend htsp (List.mem_append_left _ htsp)
      have hplp : p ≤ π.len := Nat.le_of_lt hpl'
      obtain ⟨tp2, htp2, hop⟩ := Thread.HasOrPassed.reachable (π.wf h0 (J + 1) hJ) (Reachable.toK (π.reachBetween hJp' hplp)) hthj
        (ts := (π.cfg J).mem.last + 1) (.inl (List.mem_append_right _ (List.mem_singleton_self _)))
      rw [htp] at htp2; cases htp2
      have htsp' : (π.cfg J).mem.last + 1 ∈ tp.prom := by
        rcases hop with h | h
        · exact h
        · exfalso
          have hb := GVOK.relPre_lt hrel ((π.wf h0 p hplp) j tp htp).1
          have hnt := (hNT p hplp j tp htp).1 ts0
          have hle := (π.wf h0 J (by omega) j t ht).2 ts0 hts0J
          unfold Thread.NoNTStores at hnt
          omega_t
      have hpf : p ≤ f := by
        rcases Nat.lt_or_ge f p with h | h
        · exfalso
          have hle : (π.cfg J).mem.last + 1 ≤ (π.cfg (f + 1)).mem.last := by
            rw [← hJ1last]; exact (π.mem_prefix (by omega) (by omega)).last_le
          exact Thread.notProm_reachable (π.wf h0 (f + 1) (by omega)) (Reachable.toK (π.reachBetween h hplp)) hle
            (fun t' ht' => by rw [htf'] at ht'; cases ht'; exact htsf') tp htp htsp'
        · exact h
      refine ⟨p, tp, by omega, hpf, htp, hv, by omega, fun ts' hp hts' hts'' => ?_,
        fun q tq tq' hpq hqf htq htq' ts' hp hts' hts'' => ?_⟩
      · obtain ⟨tv, htv, htsv⟩ := hpendj ts' hp f tf (by omega) hfl' htf hts'
        rw [hv] at htv; cases htv
        have htsvp : ts' ∈ tp.prom := (List.mem_filter.mp htsv).1
        have hgone := hful ts' hp htsvp
        rcases Nat.lt_or_ge p f with hpf' | hpf'
        · have hle : ts' ≤ (π.cfg (p + 1)).mem.last := by
            have := (List.mem_filter.mp htsv).2
            simp only [decide_eq_true_eq] at this
            exact Nat.le_trans this (π.mem_prefix (by omega) (by omega)).last_le
          exact Thread.notProm_reachable (π.wf h0 (p + 1) (by omega)) (Reachable.toK (π.reachBetween hpf' hfl')) hle
            (fun t' ht' => by rw [htp'] at ht'; cases ht'; exact hgone) tf htf hts'
        · obtain rfl : p = f := by omega
          rw [htp] at htf; cases htf
          rw [htp'] at htf'; cases htf'
          exact hgone hts''
      · -- `j`'s pending promises are gone after its fulfilling step `p`, and stay gone
        obtain ⟨tv, htv, htsv⟩ := hpendj ts' hp q tq (by omega) (by omega) htq hts'
        rw [hv] at htv; cases htv
        have hgone := hful ts' hp (List.mem_filter.mp htsv).1
        have hle : ts' ≤ (π.cfg (p + 1)).mem.last := by
          have := (List.mem_filter.mp htsv).2
          simp only [decide_eq_true_eq] at this
          exact Nat.le_trans this (π.mem_prefix (by omega) (by omega)).last_le
        exact Thread.notProm_reachable (π.wf h0 (p + 1) (by omega))
          (Reachable.toK (π.reachBetween (show p + 1 ≤ q + 1 by omega) (by omega))) hle
          (fun t' ht' => by rw [htp'] at ht'; cases ht'; exact hgone) tq' htq' hts''
  obtain ⟨q0, tq0, hq0J, hq0f, htq0, hvj, hbud0, hpendOK, hfulq⟩ := hstart
  -- the hybrid configuration at real index `q` restricts `j`'s real thread to `M_J`
  have hrsX : ∀ (c : Config I) (q : Nat) (tq : Thread I), J ≤ q → q ≤ π.len → (π.cfg q).threads[j]? = some tq →
      c.threads[j]? = some (tq.restrict (π.cfg J).mem) →
      (∀ i, i ≠ j → c.threads[i]? = (R.cfg R.N).threads[i]?) →
      ∀ (i : Nat) (ti : Thread I), c.threads[i]? = some ti →
        ∃ (q : Nat) (tq : Thread I), J ≤ q ∧ q ≤ π.len ∧ (π.cfg q).threads[i]? = some tq ∧
          ti = tq.restrict (π.cfg J).mem := by
    intro c q tq hJq hq htq hcj hco i ti hti
    by_cases hij : i = j
    · subst hij; rw [hcj] at hti; cases hti
      exact ⟨q, tq, hJq, hq, htq, rfl⟩
    · rw [hco i hij] at hti; exact hrestr i ti hti
  -- the replay loop
  have loop : ∀ d, q0 + d ≤ f → ∃ X : PExt' R,
      (X.cfg X.K).mem = (π.cfg J).mem ∧ (X.cfg X.K).threads.size = (R.cfg R.N).threads.size ∧
      (∀ i, i ≠ j → (X.cfg X.K).threads[i]? = (R.cfg R.N).threads[i]?) ∧
      (∃ tq, (π.cfg (q0 + d)).threads[j]? = some tq ∧
        (X.cfg X.K).threads[j]? = some (tq.restrict (π.cfg J).mem)) ∧
      (∃ s gs k, NPSafePS (modelErase I Er) A B j G KF S (k + 1) 0 (R.Clean GV KF Er A π B g0 R.N ∧ X.Clean X.K) s (X.rF X.K j) gs ∧
        EnvExt j s (X.cfg X.K) ∧ gs.Le (X.g X.K) ∧
        (∀ t', (X.cfg X.K).threads[j]? = some t' → ∀ ts' ∈ t'.prom, ts' ∈ (X.g X.K).pend → ts' ∈ gs.pend) ∧
        (π.len - (q0 + d)) + (π.len - J) < k) ∧
      (∀ i, i ≠ j → X.rF X.K i = R.rF R.N i) ∧ (∀ i, i ≠ j → EnvExt i (R.cfg R.N) (X.cfg X.K)) ∧
      (R.g R.N).Le (X.g X.K) ∧
      (∀ ts', ts' ∈ (R.g R.N).pend → (∃ i t', i ≠ j ∧ (R.cfg R.N).threads[i]? = some t' ∧ ts' ∈ t'.prom) →
        ts' ∈ (X.g X.K).pend) ∧
      (∀ ts', ts' ∈ (X.g X.K).pend → ts' ∈ (R.g R.N).pend) := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨PExt'.nil R, hvm, rfl, fun _ _ => rfl, ⟨tq0, htq0, hvj⟩,
        ⟨s, gs, n, NPSafePS.mono_flag (fun h => h.1) hsafe, hext, hgs, hown, hbud0⟩,
        fun _ _ => rfl, fun _ _ => EnvExt.refl _ _, Ghost.Le.refl _, fun _ h _ => h, fun _ h => h⟩
    | succ d ih =>
      intro hd
      obtain ⟨X, hcm, hcs, hco, ⟨tq, htq, hcj⟩, ⟨s1, gs1, k, hsafe1, hext1, hgs1, hown1, hbud1⟩,
        hro, hexto, hgle, hkeepo, hbacko⟩ := ih (by omega)
      have hq : q0 + d < π.len := by omega
      rw [show q0 + (d + 1) = q0 + d + 1 by omega]
      have hsk := succs_cases (π.step (q0 + d) hq)
      generalize hc' : π.cfg (q0 + d + 1) = c' at hsk
      cases hsk with
      | @instr i ti outs o hti hs ho =>
        by_cases hij : i = j
        · subst hij
          rw [htq] at hti; cases hti
          have hq1 : q0 + d + 1 ≤ f := by omega
          have hthq1 : (π.cfg (q0 + d + 1)).threads[i]? = some o.thread := by
            rw [hc', Config.withThread_get? _ _ _ (lt_size_of_get? htq), ite_eq_left rfl]
          have hwfq := π.wf h0 (q0 + d) (by omega)
          have hwfq1 := π.wf h0 (q0 + d + 1) (by omega)
          obtain ⟨t2, ht2, hrel2⟩ := (π.reachBetween hq1 hfl').relPre_mono hwfq1 hthq1
          obtain ⟨t3, ht3, hnt3⟩ := (π.reachBetween hq1 hfl').vwOldNT_mono hwfq1 hthq1
          rw [htf] at ht2 ht3; cases ht2; cases ht3
          have hbf := GVOK.relPre_lt hrelf ((π.wf h0 f hfl') i tf htf).1
          have hntf := (hNT f hfl' i tf htf).1 ((π.cfg J).mem.last + 1)
          unfold Thread.NoNTStores at hntf
          have hM : (π.cfg J).mem.Prefix (π.cfg (q0 + d)).mem := π.mem_prefix (by omega) (by omega)
          obtain ⟨-, outs', hs', ho'⟩ := stepOne_restrict A hM hs ho (hwfq i tq htq).1
            (by omega_t) (by omega_t)
          have hjc : i < (X.cfg X.K).threads.size := lt_size_of_get? hcj
          let c2 := (X.cfg X.K).withThread i (o.thread.restrict (π.cfg J).mem) (π.cfg J).mem
          have hc2j : c2.threads[i]? = some (o.thread.restrict (π.cfg J).mem) := by
            show ((X.cfg X.K).withThread i _ _).threads[i]? = _
            rw [Config.withThread_get? _ _ _ hjc, ite_eq_left rfl]
          have hc2o : ∀ i', i' ≠ i → c2.threads[i']? = (X.cfg X.K).threads[i']? := fun i' hi => by
            show ((X.cfg X.K).withThread i _ _).threads[i']? = _
            rw [Config.withThread_get? _ _ _ hjc, ite_eq_right (Ne.symm hi)]
          have hnp : NPStepBy A i (X.cfg X.K) c2 :=
            ⟨_, _, _, hcj, ⟨outs', _, by rw [hcm]; exact hs', ho', rfl⟩, rfl⟩
          have hinv : (X.cfg X.K).MachInv :=
            machInv_of_restrict h0 hcm (hrsX _ (q0 + d) tq (by omega) (by omega) htq hcj hco)
          have hw : (X.cfg X.K).WfProm i := fun t' ht' => by
            rw [hcj] at ht'; cases ht'; rw [hcm]
            exact Thread.hasDeadPromise_restrict hM (hlive (q0 + d) (by omega) i tq htq)
          have hw' : c2.WfProm i := fun t' ht' => by
            rw [hc2j] at ht'; cases ht'
            have hM1 : (π.cfg J).mem.Prefix (π.cfg (q0 + d + 1)).mem := π.mem_prefix (by omega) (by omega)
            exact Thread.hasDeadPromise_restrict hM1 (hlive (q0 + d + 1) (by omega) i o.thread hthq1)
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have E1 := X.erase X.K (Nat.le_refl _)
          have hupd : (modelErase I Er).upd (X.rF X.K) i (X.rF X.K i) = X.rF X.K := funext fun i' => by
            simp only [ResModel.upd]
            by_cases h : i' = i <;> simp only [h, ↓reduceIte] <;> exact rfl
          have hsf : StepFulP (model I) i (X.cfg X.K) (X.g X.K) c2 := by
            intro t1 t1' ht1 ht1' ts' hts' hp hts''
            rw [hcj] at ht1; cases ht1
            rw [hc2j] at ht1'; cases ht1'
            exact hfulq (q0 + d) tq o.thread (by omega) (by omega) htq hthq1 ts' (hbacko ts' hp)
              (List.mem_filter.mp hts').1 (List.mem_filter.mp hts'').1
          obtain ⟨r', g', E', hg', hkeep, hback, hsafe', hacq, howns, hK2, hK1⟩ :=
            NPSafePS.stepAt hsafe1 hext1 hgs1 hown1 (X.rF X.K) c2 (by rw [hupd]; exact E1) hnp hinv hw hw' hsf
          have hrF'j : (modelErase I Er).upd (X.rF X.K) i r' i = r' := by simp only [ResModel.upd, ↓reduceIte]
          have hrF'o : ∀ i', i' ≠ i → (modelErase I Er).upd (X.rF X.K) i r' i' = X.rF X.K i' := fun i' hi => by
            simp only [ResModel.upd, hi, ↓reduceIte] <;> exact rfl
          have hstep : MicroStep' KF A (X.cfg X.K) (X.rF X.K) (X.g X.K) c2 ((modelErase I Er).upd (X.rF X.K) i r') g' :=
            MicroStep'.np i _ _ hcj hnp hc2j hrF'o hg' (fun ts h ho => hkeep ts h ho) hback
              (fun x hx => hacq x (by rw [← hrF'j]; exact hx)) (fun w hw => howns w hw)
              hK2
              (fun b hb hmax x h => hK1 b hb (fun t' ht' => by rw [hc2j] at ht'; cases ht'; exact hmax) x
                (by rw [← hrF'j]; exact h))
          have hreal2 : RealIn π c2 := fun s' t' ht' => by
            by_cases hs' : s' = i
            · subst hs'; rw [hc2j] at ht'; cases ht'
              exact ⟨q0 + d + 1, o.thread, by omega, hthq1, rfl, fun x hx => (List.mem_filter.mp hx).1⟩
            · rw [hc2o s' hs'] at ht'; exact X.real X.K (Nat.le_refl _) s' t' ht'
          let X' := X.snoc c2 ((modelErase I Er).upd (X.rF X.K) i r') g' E' hstep ⟨J, by omega, rfl⟩ hreal2
            ((X.le0 X.K (Nat.le_refl _)).trans hg')
          have e1 : X'.cfg X'.K = c2 := X.snoc_cfg
          have e2 : X'.rF X'.K = (modelErase I Er).upd (X.rF X.K) i r' := X.snoc_rF
          have e3 : X'.g X'.K = g' := X.snoc_g
          refine ⟨X', ?_⟩
          rw [← hc', e1, e2, e3]
          refine ⟨rfl, by show ((X.cfg X.K).withThread i _ _).threads.size = _; rw [Config.withThread_size]; exact hcs,
            fun i' hi => by rw [hc2o i' hi]; exact hco i' hi, ⟨o.thread, hthq1, hc2j⟩,
            ⟨c2, g', k', ?_, EnvExt.refl _ _, Ghost.Le.refl _, fun _ _ _ _ h => h, by omega⟩,
            fun i' hi => by rw [hrF'o i' hi]; exact hro i' hi,
            fun i' hi => (hexto i' hi).trans (hnp.envExt_other (Ne.symm hi)), hgle.trans hg',
            fun ts' hp ⟨i', t', hi, ht', hts'⟩ => hkeep ts' (hkeepo ts' hp ⟨i', t', hi, ht', hts'⟩)
              ⟨i', t', by rw [hc2o i' hi, hco i' hi]; exact ht', hts'⟩,
            fun ts' hp => hbacko ts' (hback ts' hp)⟩
          rw [hrF'j]
          exact NPSafePS.mono_flag (fun h => by
            obtain ⟨h1, h2⟩ := X.snoc_clean h.2
            exact ⟨⟨h.1, h1⟩, by rw [hupd]; exact h2⟩) hsafe'
        · have : (π.cfg (q0 + d + 1)).threads[j]? = some tq := by
            rw [hc', Config.withThread_get? _ _ _ (lt_size_of_get? hti), ite_eq_right hij]; exact htq
          rw [← hc']
          exact ⟨X, hcm, hcs, hco, ⟨tq, this, hcj⟩, ⟨s1, gs1, k, hsafe1, hext1, hgs1, hown1, by omega⟩,
            hro, hexto, hgle, hkeepo, hbacko⟩
      | @promise i ti pw' hti _ =>
        have : ∃ tq', (π.cfg (q0 + d + 1)).threads[j]? = some tq' ∧
            tq'.restrict (π.cfg J).mem = tq.restrict (π.cfg J).mem := by
          by_cases hij : i = j
          · subst hij; rw [htq] at hti; cases hti
            refine ⟨_, by rw [hc', Config.withThread_get? _ _ _ (lt_size_of_get? htq), ite_eq_left rfl], ?_⟩
            have hgt : ¬ ((π.cfg (q0 + d)).mem.append { pw'.1 with tid := i }).2 ≤ (π.cfg J).mem.last := by
              have := (π.mem_prefix (show J ≤ q0 + d by omega) (by omega)).last_le
              show ¬ ((π.cfg (q0 + d)).mem.last + 1 ≤ _)
              omega_t
            show { tq with prom := _ } = { tq with prom := _ }
            rw [List.filter_append]
            simp only [List.filter_cons, decide_eq_true_eq, hgt, ↓reduceIte, List.filter_nil, List.append_nil]
          · exact ⟨tq, by rw [hc', Config.withThread_get? _ _ _ (lt_size_of_get? hti), ite_eq_right hij]; exact htq,
              rfl⟩
        obtain ⟨tq', htq', hres⟩ := this
        rw [← hc']
        exact ⟨X, hcm, hcs, hco, ⟨tq', htq', by rw [hres]; exact hcj⟩,
          ⟨s1, gs1, k, hsafe1, hext1, hgs1, hown1, by omega⟩, hro, hexto, hgle, hkeepo, hbacko⟩
  obtain ⟨X, hcm, hcs, hco, ⟨tq, htq, hcj⟩, ⟨s1, gs1, k, hsafe1, hext1, hgs1, hown1, hbud1⟩,
    hro, hexto, hgle, hkeepo, hbacko⟩ := loop (f - q0) (by omega)
  rw [show q0 + (f - q0) = f by omega] at htq hbud1
  rw [htf] at htq; cases htq
  -- the prepay micro-step
  have hsorted := Path.promSorted π h0 f hfl' j tf htf
  have hres : tf.restrict (π.cfg (J + 1)).mem =
      { tf.restrict (π.cfg J).mem with prom := (tf.restrict (π.cfg J).mem).prom ++ [(π.cfg J).mem.last + 1] } := by
    simp only [Thread.restrict, hJ1last]
    rw [filter_le_succ_of_sorted hsorted htsf]
  have hinv : (X.cfg X.K).MachInv :=
    machInv_of_restrict h0 hcm (hrsX _ f tf (by omega) hfl' htf hcj hco)
  have hrel' : G A j ((X.cfg X.K).mem.append { pw.1 with tid := j }).2 ({ tf.restrict (π.cfg J).mem with
        prom := (tf.restrict (π.cfg J).mem).prom ++ [((X.cfg X.K).mem.append { pw.1 with tid := j }).2] } : Thread I)
        ((X.cfg X.K).mem.append { pw.1 with tid := j }).1 := by
    have hM : (π.cfg (J + 1)).mem.Prefix (π.cfg f).mem := π.mem_prefix (by omega) hfl'
    have hntf := (hNT f hfl' j tf htf).1 ((π.cfg J).mem.last + 1)
    unfold Thread.NoNTStores at hntf
    have h1 : G A j ((π.cfg J).mem.last + 1) (tf.restrict (π.cfg (J + 1)).mem) (π.cfg (J + 1)).mem :=
      GOK.restrict hM (by rw [hJ1last]; exact Nat.le_refl _) ((π.wf h0 f hfl') j tf htf).1 hrelfL (by rw [hJ1last]; omega_t)
        (hNT f hfl' j tf htf).2
    rw [hres, hJ1m] at h1
    rw [hcm]
    exact h1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have E1 := X.erase X.K (Nat.le_refl _)
  have hupd : (modelErase I Er).upd (X.rF X.K) j (X.rF X.K j) = X.rF X.K := funext fun i' => by
    simp only [ResModel.upd]
    by_cases h : i' = j <;> simp only [h, ↓reduceIte] <;> exact rfl
  obtain ⟨r', g', E', hg', hpendN, hkeep, hback, hsafe', hacq, hK2, hK1⟩ :=
    NPSafePS.prepayAt hsafe1 hext1 hgs1 (X.rF X.K) _ pw.1 hcj (by rw [hupd]; exact E1) hinv
      (fun ts' hts' hp => hown1 _ hcj ts' hts' hp) hrel'
  let c3 := Promised (X.cfg X.K) j (tf.restrict (π.cfg J).mem) pw.1
  have hc3j : c3.threads[j]? = some (tf.restrict (π.cfg (J + 1)).mem) := by
    show (Promised (X.cfg X.K) j (tf.restrict (π.cfg J).mem) pw.1).threads[j]? = _
    rw [promised_get? hcj, ite_eq_left rfl, hcm, hres]
  have hc3o : ∀ i, i ≠ j → c3.threads[i]? = (R.cfg R.N).threads[i]? := fun i hi => by
    show (Promised (X.cfg X.K) j (tf.restrict (π.cfg J).mem) pw.1).threads[i]? = _
    rw [promised_get? hcj, ite_eq_right (Ne.symm hi)]; exact hco i hi
  have hc3m : c3.mem = (π.cfg (J + 1)).mem := by
    show (Promised (X.cfg X.K) j (tf.restrict (π.cfg J).mem) pw.1).mem = _
    rw [promised_mem, hcm, hJ1m]
  have hc3s : c3.threads.size = (π.cfg (J + 1)).threads.size := by
    show (Promised (X.cfg X.K) j (tf.restrict (π.cfg J).mem) pw.1).threads.size = _
    rw [promised_size, hcs, hvs, hJ1, Config.withThread_size]
  have hrF'j : (modelErase I Er).upd (X.rF X.K) j r' j = r' := by simp only [ResModel.upd, ↓reduceIte]
  have hrF'o : ∀ i', i' ≠ j → (modelErase I Er).upd (X.rF X.K) j r' i' = X.rF X.K i' := fun i' hi => by
    simp only [ResModel.upd, hi, ↓reduceIte] <;> exact rfl
  have hstep : MicroStep' KF A (X.cfg X.K) (X.rF X.K) (X.g X.K) c3 ((modelErase I Er).upd (X.rF X.K) j r') g' :=
    MicroStep'.prepay j _ pw.1 hcj hrF'o hg' hpendN (fun ts h => hkeep ts h) hback
      (fun x hx => hacq x (by rw [← hrF'j]; exact hx)) hK2
      (fun b hb hmax x h => hK1 b hb (fun t' ht' => by rw [hcj] at ht'; cases ht'; exact hmax) x
        (by rw [← hrF'j]; exact h))
  have hreal3 : RealIn π c3 := fun s' t' ht' => by
    by_cases hs' : s' = j
    · subst hs'; rw [hc3j] at ht'; cases ht'
      exact ⟨f, tf, hfl', htf, rfl, fun x hx => (List.mem_filter.mp hx).1⟩
    · rw [hc3o s' hs'] at ht'; exact R.real R.N (Nat.le_refl _) s' t' ht'
  let X3 := X.snoc c3 ((modelErase I Er).upd (X.rF X.K) j r') g' E' hstep ⟨J + 1, hJ, hc3m⟩ hreal3
    ((X.le0 X.K (Nat.le_refl _)).trans hg')
  have e1 : X3.cfg X3.K = c3 := X.snoc_cfg
  have e2 : X3.rF X3.K = (modelErase I Er).upd (X.rF X.K) j r' := X.snoc_rF
  have e3 : X3.g X3.K = g' := X.snoc_g
  -- facts for the statuses at `J + 1`
  have hnew : ∀ ts w, (π.cfg J).mem.last < ts → (π.cfg (J + 1)).mem.get? ts = some w → w.tid = j := by
    intro ts w hlt hw
    rw [hJ1m] at hw
    rcases Memory.get?_append_eq_some _ _ hw with ⟨hle, -⟩ | ⟨-, rfl⟩
    · omega_t
    · rfl
  have hnotN : ∀ i, i ≠ j → ∀ q tq, J ≤ q → q ≤ π.len → (π.cfg q).threads[i]? = some tq →
      (π.cfg J).mem.last + 1 ∉ tq.prom := by
    intro i hi q tq hJq hq htq hm
    obtain ⟨w, hw1, hw2⟩ := (π.machInv h0 q hq).promWf i tq htq _ hm
    rcases Nat.lt_or_ge J q with h | h
    · have hle : (π.cfg J).mem.last + 1 ≤ (π.cfg (J + 1)).mem.last := by rw [hJ1last]; exact Nat.le_refl _
      rw [(π.mem_prefix (show J + 1 ≤ q by omega) hq).get? hle] at hw1
      exact hi (hw2.symm.trans (hnew _ w (by omega_t) hw1))
    · have hqJ : q = J := by omega
      subst hqJ
      have := (π.cfg q).mem.last_le_of_get?_eq_some hw1
      omega_t
  have hnpf : NPStepBy A j (π.cfg f) (π.cfg (f + 1)) := by
    have hsk := succs_cases (π.step f hfl)
    generalize hcf : π.cfg (f + 1) = cf at hsk htf'
    cases hsk with
    | @instr i ti outs o hti hs ho =>
      by_cases hij : i = j
      · subst hij; exact ⟨ti, o.thread, o.mem, hti, ⟨outs, o, hs, ho, rfl⟩, rfl⟩
      · exfalso
        rw [Config.withThread_get? _ _ _ (lt_size_of_get? hti), ite_eq_right hij, htf] at htf'
        cases htf'; exact htsf' htsf
    | @promise i ti pw' hti _ =>
      exfalso
      rw [Config.withThread_get? _ _ _ (lt_size_of_get? hti)] at htf'
      split at htf'
      · next he =>
        subst he; rw [htf] at hti; cases hti; cases htf'
        exact htsf' (List.mem_append_left _ htsf)
      · rw [htf] at htf'; cases htf'; exact htsf' htsf
  have hpendN' : (π.cfg J).mem.last + 1 ∈ g'.pend := by
    have h : (X.cfg X.K).mem.last + 1 ∈ g'.pend := hpendN
    rw [hcm] at h; exact h
  have hback' : ∀ ts', ts' ∈ g'.pend → ts' ∈ (X.g X.K).pend ∨ ts' = (π.cfg J).mem.last + 1 := fun ts' hp => by
    rcases hback ts' hp with h | h
    · exact .inl h
    · right; rw [h, ← hcm]; rfl
  -- every thread in order at `J + 1`
  have hok' : ∀ i, i < c3.threads.size →
      ∃ p, ThreadOkP' G GV KF Er S A π B (J + 1) (R.Clean GV KF Er A π B g0 R.N ∧ X3.Clean X3.K) c3
        ((modelErase I Er).upd (X.rF X.K) j r') g' i p := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      refine ⟨f, c3, g', k', by omega, hfl', ?_, EnvExt.refl _ _, Ghost.Le.refl _, fun _ _ _ _ h => h, by omega,
        .inr ⟨hfl, tf, htf, hc3j, ⟨_, hpendN', htsf, hrelf, fun q h1 h2 => hint q (by omega) h2⟩,
          ⟨tf', htf', hnpf, fun ts' hp h1 h2 => ?_⟩⟩⟩
      · rw [hrF'j]
        exact NPSafePS.mono_flag (fun h => by
          obtain ⟨h1, h2⟩ := X.snoc_clean h.2
          exact ⟨⟨h.1, h1⟩, by rw [hupd]; exact h2⟩) hsafe'
      · rcases hback' ts' hp with hp | rfl
        · exact hpendOK ts' (hbacko ts' hp) h1 h2
        · exact htsf' h2
    · have hi' : i < (R.cfg R.N).threads.size := by
        have : (π.cfg (J + 1)).threads.size = (π.cfg J).threads.size := by rw [hJ1, Config.withThread_size]
        omega
      obtain ⟨pi, si, gsi, ni, hJpi, -, hsafei, hexti, hgsi, howni, hbudi, hsti⟩ := hok i hi'
      obtain ⟨p', h1, h2, h3, h4⟩ := status_frameG' h0 hJ (hthr i hij) (hc3o i hij)
        (fun ts' hp ⟨t', ht', hts'⟩ => hkeep ts' (hkeepo ts' hp ⟨i, t', hij, by rw [← hc3o i hij]; exact ht', hts'⟩))
        (fun ts' hp => (hback' ts' hp).imp_left (hbacko ts'))
        (hnotN i hij) (restrict_frame h0 hJ hnew i hij) hJpi hsti
      refine ⟨p', si, gsi, ni, h1, h2, ?_, (hexti.trans (hexto i hij)).trans (EnvExt.promise hcj),
        hgsi.trans (hgle.trans hg'), fun t' ht' ts' hts' hp => ?_, by omega, h4⟩
      · rw [hrF'o i hij, hro i hij]; exact NPSafePS.mono_flag (fun h => h.1) hsafei
      · have ht'' : (R.cfg R.N).threads[i]? = some t' := by rw [← hc3o i hij]; exact ht'
        rcases hback' ts' hp with hp | rfl
        · exact howni t' ht'' ts' hts' (hbacko ts' hp)
        · exfalso
          obtain ⟨q, tq, hJq, hq, htq, rfl⟩ := hrestr i t' ht''
          exact hnotN i hij q tq hJq hq htq (List.mem_filter.mp hts').1
  have hV3 : (π.cfg (J + 1)).VirtualOfG GV A (X3.cfg X3.K) := by
    rw [e1]
    exact virtual_of_status' GVOK h0 hNT hJ hc3m hc3s (fun i hi => by
      obtain ⟨p, _, _, _, hJp, _, _, _, _, _, _, hst'⟩ := hok' i hi
      exact ⟨p, hJp, hst'⟩)
  let R' := R.ext X3 hV3 (fun hcl tid hd => by
    rw [e1] at hd ⊢
    rw [e2, e3]
    obtain ⟨t', ht', hrest⟩ := hd
    obtain ⟨p, hP⟩ := hok' tid (lt_size_of_get? ht')
    exact ThreadOkP'.done hP hcl ⟨t', ht', hrest⟩)
  refine ⟨R', fun i hi => ?_⟩
  have hc : R'.cfg R'.N = c3 := (R.ext_cfg X3).trans e1
  have hr : R'.rF R'.N = (modelErase I Er).upd (X.rF X.K) j r' := (R.ext_rF X3).trans e2
  have hg : R'.g R'.N = g' := (R.ext_g X3).trans e3
  rw [hc] at hi
  obtain ⟨p, hP⟩ := hok' i hi
  refine ⟨p, ?_⟩
  rw [hc, hr, hg]
  exact hP.mono_flag (fun h => R.ext_clean X3 h)

end D1

/-- **Theorem 1′ for the SLR-adapted model from condition (3)**: every case
of the induction step is proved; the remaining hypotheses are `Cond3'` and,
inside `Theorem1IIPure'`, the program hypothesis (O5) `PromisePure'` on the
initial ghost's release predicates. -/
theorem theorem1II_pure' {G GV : PrepayGuard I} {KF : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)}
    {Ob : PromiseOb} (ErOK : ChainExt Er Ob) (GOK : GuardOK G) (GVOK : GuardOK GV)
    (hGV : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → GV A tid ts t mem) [I.LawfulState] {A : Arch} {fuel : Nat}
    (h3 : ∀ states initMem, Cond3' (I := I) GV KF A fuel states initMem) :
    Theorem1IIPureXS' (I := I) G GV KF Er S Ob A fuel :=
  theorem1II_of_cond3' ErOK GVOK h3 (caseD1' ErOK GOK GVOK hGV)

/-! ## The existing names: instances at `G₀`, `GRF`, `K2₀` (`SLR/NPSafePGen.lean`) -/

section MergedExt

variable {A : Arch} {fuel : Nat} {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}


/-- **An extension of a prefix run** of the existing chain: `PExt'` at `GRF`,
`K2₀`. -/
abbrev PExt (R : PRun A π B g0 J) : Type := PExt' R

section MergedPExtFields

variable {R : PRun A π B g0 J}

abbrev PExt.K (self : PExt R) : Nat := PExt'.K self
abbrev PExt.cfg (self : PExt R) : Nat → Config I := PExt'.cfg self
abbrev PExt.rF (self : PExt R) : Nat → Nat → Res := PExt'.rF self
abbrev PExt.g (self : PExt R) : Nat → Ghost := PExt'.g self
theorem PExt.cfg_zero (self : PExt R) : self.cfg 0 = R.cfg R.N := PExt'.cfg_zero self
theorem PExt.rF_zero (self : PExt R) : self.rF 0 = R.rF R.N := PExt'.rF_zero self
theorem PExt.g_zero (self : PExt R) : self.g 0 = R.g R.N := PExt'.g_zero self
theorem PExt.erase (self : PExt R) :
    ∀ μ, μ ≤ self.K → Erase (self.rF μ) (self.g μ) (fun _ => True) (self.cfg μ) :=
  PExt'.erase self
theorem PExt.step (self : PExt R) : ∀ μ, μ < self.K →
    MicroStep A (self.cfg μ) (self.rF μ) (self.g μ) (self.cfg (μ + 1)) (self.rF (μ + 1)) (self.g (μ + 1)) :=
  PExt'.step self
theorem PExt.mem (self : PExt R) : ∀ μ, μ ≤ self.K → ∃ j, j ≤ π.len ∧ (self.cfg μ).mem = (π.cfg j).mem :=
  PExt'.mem self
theorem PExt.real (self : PExt R) : ∀ μ, μ ≤ self.K → RealIn π (self.cfg μ) := PExt'.real self
theorem PExt.le0 (self : PExt R) : ∀ μ, μ ≤ self.K → g0.Le (self.g μ) := PExt'.le0 self

/-- The constructor of `PExt`. -/
abbrev PExt.mk (K : Nat) (cfg : Nat → Config I) (rF : Nat → Nat → Res) (g : Nat → Ghost)
    (cfg_zero : cfg 0 = R.cfg R.N) (rF_zero : rF 0 = R.rF R.N) (g_zero : g 0 = R.g R.N)
    (erase : ∀ μ, μ ≤ K → Erase (rF μ) (g μ) (fun _ => True) (cfg μ))
    (step : ∀ μ, μ < K → MicroStep A (cfg μ) (rF μ) (g μ) (cfg (μ + 1)) (rF (μ + 1)) (g (μ + 1)))
    (mem : ∀ μ, μ ≤ K → ∃ j, j ≤ π.len ∧ (cfg μ).mem = (π.cfg j).mem)
    (real : ∀ μ, μ ≤ K → RealIn π (cfg μ))
    (le0 : ∀ μ, μ ≤ K → g0.Le (g μ)) : PExt R :=
  PExt'.mk K cfg rF g cfg_zero rF_zero g_zero erase step mem real le0

end MergedPExtFields


/-- Full erasure at every micro-index of the extension below `μ'`. -/
def PExt.Clean {R : PRun A π B g0 J} (X : PExt R) (μ' : Nat) : Prop :=
  ∀ μ, μ < μ' → Erase (X.rF μ) (X.g μ) (fun _ => False) (X.cfg μ)

/-- The empty extension. -/
def PExt.nil (R : PRun A π B g0 J) : PExt R := by
  npgen PExt'.nil

/-- Extend by one micro-step. -/
def PExt.snoc {R : PRun A π B g0 J} (X : PExt R) (c' : Config I) (rF' : Nat → Res) (g' : Ghost)
    (E : Erase rF' g' (fun _ => True) c') (hstep : MicroStep A (X.cfg X.K) (X.rF X.K) (X.g X.K) c' rF' g')
    (hmem : ∃ j, j ≤ π.len ∧ c'.mem = (π.cfg j).mem) (hreal : RealIn π c') (hle : g0.Le g') : PExt R := by
  npgen PExt'.snoc


section MergedSnocLemmas

variable {R : PRun A π B g0 J} (X : PExt R) {c' : Config I} {rF' : Nat → Res} {g' : Ghost}
  {E : Erase rF' g' (fun _ => True) c'} {hstep : MicroStep A (X.cfg X.K) (X.rF X.K) (X.g X.K) c' rF' g'}
  {hmem : ∃ j, j ≤ π.len ∧ c'.mem = (π.cfg j).mem} {hreal : RealIn π c'} {hle : g0.Le g'}


theorem PExt.snoc_K : (X.snoc c' rF' g' E hstep hmem hreal hle).K = X.K + 1 := by
  npgen PExt'.snoc_K

theorem PExt.snoc_cfg : (X.snoc c' rF' g' E hstep hmem hreal hle).cfg (X.K + 1) = c' := by
  npgen PExt'.snoc_cfg

theorem PExt.snoc_rF : (X.snoc c' rF' g' E hstep hmem hreal hle).rF (X.K + 1) = rF' := by
  npgen PExt'.snoc_rF

theorem PExt.snoc_g : (X.snoc c' rF' g' E hstep hmem hreal hle).g (X.K + 1) = g' := by
  npgen PExt'.snoc_g

/-- The validity of the extension by one more step gives the validity of the
old one and full erasure at its last configuration. -/
theorem PExt.snoc_clean (h : (X.snoc c' rF' g' E hstep hmem hreal hle).Clean (X.K + 1)) :
    X.Clean X.K ∧ Erase (X.rF X.K) (X.g X.K) (fun _ => False) (X.cfg X.K) := by
  npgen PExt'.snoc_clean


end MergedSnocLemmas


/-- The configurations of the prefix run extended by `X`. -/
def PRun.extCfg (R : PRun A π B g0 J) (X : PExt R) (μ : Nat) : Config I := by
  npgen PRun'.extCfg

def PRun.extRF (R : PRun A π B g0 J) (X : PExt R) (μ : Nat) : Nat → Res := by
  npgen PRun'.extRF

def PRun.extG (R : PRun A π B g0 J) (X : PExt R) (μ : Nat) : Ghost := by
  npgen PRun'.extG


section MergedExtLemmas

variable (R : PRun A π B g0 J) (X : PExt R)


theorem PRun.extCfg_lo {μ : Nat} (h : μ ≤ R.N) : R.extCfg X μ = R.cfg μ := by
  npgen PRun'.extCfg_lo

theorem PRun.extRF_lo {μ : Nat} (h : μ ≤ R.N) : R.extRF X μ = R.rF μ := by
  npgen PRun'.extRF_lo

theorem PRun.extG_lo {μ : Nat} (h : μ ≤ R.N) : R.extG X μ = R.g μ := by
  npgen PRun'.extG_lo

theorem PRun.extCfg_hi {μ : Nat} (h : R.N ≤ μ) : R.extCfg X μ = X.cfg (μ - R.N) := by
  npgen PRun'.extCfg_hi

theorem PRun.extRF_hi {μ : Nat} (h : R.N ≤ μ) : R.extRF X μ = X.rF (μ - R.N) := by
  npgen PRun'.extRF_hi

theorem PRun.extG_hi {μ : Nat} (h : R.N ≤ μ) : R.extG X μ = X.g (μ - R.N) := by
  npgen PRun'.extG_hi


end MergedExtLemmas


/-- **Extend a prefix run by an extension** to the next real index: the last
configuration of the extension is the virtual configuration at `J + 1`. -/
def PRun.ext (R : PRun A π B g0 J) (X : PExt R) (hV : (π.cfg (J + 1)).VirtualOf A (X.cfg X.K))
    (hdone : R.Clean A π B g0 R.N ∧ X.Clean X.K →
      ∀ tid, (X.cfg X.K).Done tid → B (X.cfg X.K) (X.rF X.K tid) (X.g X.K)) :
    PRun A π B g0 (J + 1) := by
  npgen PRun'.ext


section MergedExtRun

variable (R : PRun A π B g0 J) (X : PExt R) {hV : (π.cfg (J + 1)).VirtualOf A (X.cfg X.K)}
  {hdone : R.Clean A π B g0 R.N ∧ X.Clean X.K →
      ∀ tid, (X.cfg X.K).Done tid → B (X.cfg X.K) (X.rF X.K tid) (X.g X.K)}


theorem PRun.ext_N : (R.ext X hV hdone).N = R.N + X.K := by
  npgen PRun'.ext_N

theorem PRun.ext_cfg : (R.ext X hV hdone).cfg (R.ext X hV hdone).N = X.cfg X.K := by
  npgen PRun'.ext_cfg

theorem PRun.ext_rF : (R.ext X hV hdone).rF (R.ext X hV hdone).N = X.rF X.K := by
  npgen PRun'.ext_rF

theorem PRun.ext_g : (R.ext X hV hdone).g (R.ext X hV hdone).N = X.g X.K := by
  npgen PRun'.ext_g

/-- The validity of the extended run gives that of the old run and of the
extension. -/
theorem PRun.ext_clean (h : (R.ext X hV hdone).Clean A π B g0 (R.ext X hV hdone).N) :
    R.Clean A π B g0 R.N ∧ X.Clean X.K := by
  npgen PRun'.ext_clean


end MergedExtRun

end MergedExt

section MergedHelpers

variable {A : Arch} {fuel : Nat}


/-- `NPSafe`'s prepay conjunct at an environment extension, from a token with
at least two step indices: the continuation keeps one. -/
theorem NPSafe.prepayAt {M : ResModel I} {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafe M A B tid (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁)
    (rF : Nat → M.R) (t₁ : Thread I) (w : Msg) (ht : c₁.threads[tid]? = some t₁)
    (E : M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁) (hinv : c₁.MachInv)
    (hown : ∀ ts ∈ t₁.prom, M.pendingAt g₁ ts → M.pendingAt g ts)
    (hrel : { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }.RelFulfilsLive A tid
        (c₁.mem.append { w with tid }).2 (c₁.mem.append { w with tid }).1) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) ∧
        M.ghostLe g₁ g' ∧ M.pendingAt g' (c₁.mem.append { w with tid }).2 ∧
        (∀ ts, M.pendingAt g₁ ts → M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts ∨ ts = (c₁.mem.append { w with tid }).2) ∧
        NPSafe M A B tid (k + 1) 0 (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁)
          (c₁.withThread tid { t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] }
            (c₁.mem.append { w with tid }).1) r' g' ∧
        M.acqLe r' g' r g₁ ∧
        (∀ b, b ≤ c₁.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b) ∧
        (∀ b, b ≤ c₁.mem.last →
          (∀ t, c₁.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g₁ x b) := by
  rw [NPSafe] at h
  have h1 := h (0 + 1)
  rw [NPSafe] at h1
  exact (h1 c₁ g₁ he hg).2.2 rF t₁ w ht E hinv hown hrel

/-- **The status of a thread that does not step, with a new pending mark**
(`status_frame` where the new ghost may also mark `tsN` pending, a timestamp
that is never a promise of `i` from `J` on). -/
theorem status_frame' [I.LawfulState] {π : Path A fuel I} {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J < π.len)
    {v v' : Config I} {g g' : Ghost} {i p : Nat} {tsN : Time}
    (hthr : (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]?)
    (hvv : v'.threads[i]? = v.threads[i]?)
    (hkeep : ∀ ts ∈ g.pend, (∃ t, v'.threads[i]? = some t ∧ ts ∈ t.prom) → ts ∈ g'.pend)
    (hback : ∀ ts ∈ g'.pend, ts ∈ g.pend ∨ ts = tsN)
    (hnotN : ∀ q tq, J ≤ q → q ≤ π.len → (π.cfg q).threads[i]? = some tq → tsN ∉ tq.prom)
    (hrestr : ∀ q tq, J < q → q ≤ π.len → (π.cfg q).threads[i]? = some tq →
      tq.restrict (π.cfg (J + 1)).mem = tq.restrict (π.cfg J).mem)
    (hJp : J ≤ p) (hst : Status A π J v g i p) :
    ∃ p', J + 1 ≤ p' ∧ p' ≤ π.len ∧ (π.len - p') + (π.len - (J + 1)) ≤ (π.len - p) + (π.len - J) ∧
      Status A π (J + 1) v' g' i p' := by
  npgen status_frameG'


end MergedHelpers


theorem caseD1 [I.LawfulState] {A : Arch} {fuel : Nat} : CaseD1 (I := I) A fuel := by
  npgen caseD1'

/-- **Theorem 1′ for the SLR-adapted model from condition (3)**: every case
of the induction step is proved; the remaining hypotheses are `Cond3` and,
inside `Theorem1IIPure`, the program hypothesis (O5) `PromisePure` on the
initial ghost's release predicates. -/
theorem theorem1II_pure [I.LawfulState] {A : Arch} {fuel : Nat}
    (h3 : ∀ states initMem, Cond3 (I := I) A fuel states initMem) :
    Theorem1IIPure (I := I) A fuel := by
  npgen theorem1II_pure'

end Kraken.Promising.SLR
