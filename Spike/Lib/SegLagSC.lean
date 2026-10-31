/-
**A segment held back at a quiet tail** (`SegWS.lagC`), for either ISA:
`SegWS.lagF` (`Spike/Lib/SegLagSF.lean`) with its side conditions asked
only of the pairs a frame run reaches from a held-back pair.

`SegWS.lagF` asks that every control a frame run reaches from *any* pair of
the segment's fragment `W` be `Quiet` and that no state of `W` be at a
`write` to the output. A walk's `W` is the whole body's (calls, outputs,
lane stores, allocations), so these fail for it; but a source held back at a
tail with no source event pending until `main`'s exit (a `let` of an atom,
`+` or `-`, an `if`, a `ret`; `qtail`) only ever runs to `Quiet` controls.
`SegWS.lagC` asks `Quiet` of the controls a frame run reaches from the
held-back pairs (`QuietFrom`) and the output fact of the states of `W` at
the pairs a frame run reaches from them; its proof is `SegWS.lagF`'s.

- `QuietFrom`: every control a frame run reaches from a pair of `C` is
  `Quiet`;
- `SegWS.lagC`: the segment with the pairs held back at the pairs of `C`;
- `LagOk`, `LagOk.seg`: `SegWS.lagC`'s side conditions as one premise;
- `qtail`, `quiet_of_qtail`, `qtail_run`, `quietFrom_qtail`: a control at
  depth 0 at a quiet tail, with no hold, only reaches `Quiet` controls at
  quiet tails at depth 0;
- `HeldAt`, `LagF.heldAt`, `quietFrom_heldAt`: one held-back pair, a real
  pair held back at itself, `QuietFrom` at a quiet tail;
- `not_quietFrom_newBuf`: no held-back pair at an allocation (nor, the
  same way, at a lane store's exchange: `Quiet` excludes both);
- `LagF.mono`, `LagF.or`: `LagF` is monotone and splits a disjunction.
-/
import Spike.Lib.SegLagSF
import Spike.Lib.Frames1

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **Every control a frame run reaches from a pair of `C` is `Quiet`.** -/
def QuietFrom (p : Prog) (C : Ctl → List TermRun.Frame → Prop) : Prop :=
  ∀ c fs, C c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → Quiet c₁

/-- `LagF` is monotone in the fragment held back. -/
theorem LagF.mono {I : ISA} {p : Prog} {C : Ctl → List TermRun.Frame → Prop} {X Y : FragS I}
    (hXY : ∀ s c fs, X s c fs → Y s c fs) {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    (h : LagF p C X s c fs) : LagF p C Y s c fs :=
  let ⟨hc, c', fs', hx, hr⟩ := h
  ⟨hc, c', fs', hXY _ _ _ hx, hr⟩

/-- `LagF` of a disjunction is a disjunction of `LagF`s. -/
theorem LagF.or {I : ISA} {p : Prog} {C : Ctl → List TermRun.Frame → Prop} {X Y : FragS I} {s : I.State}
    {c : Ctl} {fs : List TermRun.Frame} (h : LagF p C (fun s c fs => X s c fs ∨ Y s c fs) s c fs) :
    LagF p C X s c fs ∨ LagF p C Y s c fs :=
  let ⟨hc, c', fs', hx, hr⟩ := h
  hx.elim (fun hx => .inl ⟨hc, c', fs', hx, hr⟩) fun hy => .inr ⟨hc, c', fs', hy, hr⟩

namespace SegWS

variable {I : ISA} {W W' : FragS I} {K : I.State → I.State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q : FragS I}

/-- **A segment held back at the pairs of `C`** (`SegWS.lagF` with its side
conditions at the held-back pairs): if every control a frame run reaches
from a pair of `C` is `Quiet` (`hq`), no state of `W` at a pair a frame run
reaches from one of `C` is at a `write` to the output (`hnw`), the memory
sides agree (`hms`), and the words owned are as for `SegWS.lagF` (`hown`),
the segment from `P` to `Q` gives one from `P` held back to `Q` held back
(`LagF`), inside `W'`, given that the pairs of `W` held back are in `W'`
(`hW`). -/
theorem lagC {C : Ctl → List TermRun.Frame → Prop} (h : SegWS W K p lbl ms P Q) (hq : QuietFrom p C)
    (hnw : ∀ s c fs c' fs', C c fs → FrameRun p (c, fs) (c', fs') → W s c' fs' → ∀ K', (ms []).K = some K' →
      K'.atSys s = true → ∀ buf n, Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n))
    (hms : MsAgree ms)
    (hown : ∀ s c₀ fs₀ c fs, C c₀ fs₀ → FrameRun p (c₀, fs₀) (c, fs) → W s c fs →
      ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms fs₀).own s)
    (hW : ∀ s c fs c' fs', W s c' fs' → FrameRun p (c, fs) (c', fs') → C c fs → W' s c fs) :
    SegWS W' K p lbl ms (LagF p C P) (LagF p C Q) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  -- the memory sides at two frames agree
  have hE : ∀ {f : MemSide I → Prop} (fs fs₁ : List TermRun.Frame),
      (∀ a b : MemSide I, a.rd = b.rd → a.rt = b.rt → a.mp = b.mp → a.G = b.G → a.K = b.K →
        a.abortAt = b.abortAt → f a → f b) → f (ms fs₁) → f (ms fs) :=
    fun fs fs₁ hf h => hf _ _ ((hms.rd fs₁).trans (hms.rd fs).symm) ((hms.rt fs₁).trans (hms.rt fs).symm)
      ((hms.mp fs₁).trans (hms.mp fs).symm) ((hms.G fs₁).trans (hms.G fs).symm)
      ((hms.K fs₁).trans (hms.K fs).symm) ((hms.abortAt fs₁).trans (hms.abortAt fs).symm) h
  -- a landing after a run from the held-back pair is a held-back pair
  have hX : ∀ {s c fs c₁ fs₁ c₂}, FrameRun p (c, fs) (c₁, fs₁) → C c fs → LocalRun p c₁ c₂ →
      Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c₂ fs₁ →
      Pend p (fun s c fs => LagF p C inv s c fs ∨ LagF p C Q s c fs) s c fs := by
    intro s c fs c₁ fs₁ c₂ hr hc hr' ⟨c₃, fs₃, hr'', hx⟩
    have hR := hr.trans ((FrameRun.ofLocal hr' fs₁).trans hr'')
    exact .of (hx.elim (fun hi => .inl ⟨hc, _, _, hi, hR⟩) fun hq => .inr ⟨hc, _, _, hq, hR⟩)
  refine ⟨LagF p C inv, fun s c fs ⟨hc, c', fs', hp, hr⟩ => ⟨hc, c', fs', hP s c' fs' hp, hr⟩,
    fun s c fs ⟨hc, c', fs', hi, hr⟩ => hW s c fs c' fs' (hiW s c' fs' hi) hr hc, ?_⟩
  rintro s c fs ⟨hc, c', fs', hi, hr⟩
  have hWs := hiW s c' fs' hi
  obtain ⟨hout, hk⟩ := hcl s c' fs' hi
  refine ⟨fun hK => ?_, fun s' hks => ?_⟩
  · cases hout hK with
    | frame s₁ c₁ fs₁ he hr' hx =>
      exact .frame s₁ c fs he (.refl _) (hX (hr.trans hr') hc (.refl _) hx)
    | pre c₁ fs₁ hr' ho =>
      have hR := hr.trans hr'
      obtain ⟨hh, hld, hst, hnb, hxs, hnp, hnn⟩ := hq c fs hc c₁ fs₁ hR
      cases ho with
      | silent s₁ c₂ he hr'' hx => exact .lift (.silent s₁ c he (.refl c) (hX hR hc hr'' hx))
      | choice P t he ht hl =>
        exact .lift (.choice P t he ht fun s₁ hs₁ =>
          let ⟨c₂, hr'', hx⟩ := hl s₁ hs₁
          ⟨c, .refl c, hX hR hc hr'' hx⟩)
      | load _ _ _ x a e _ _ _ ht => exact (hld x a e ht).elim
      | store _ _ _ _ x a b e _ _ _ _ _ ht => exact (hst x a b e ht).elim
      | rtStore kr L V s₁ c₂ he hrt hmp hG hr'' hx =>
        exact .lift (.rtStore kr L V s₁ c he (hE (f := fun m => m.rt L.addr.toNat) fs fs₁
          (fun _ _ _ e _ _ _ _ h => e ▸ h) hrt) (hE (f := fun m => m.mp L true) fs fs₁
          (fun _ _ _ _ e _ _ _ h => e ▸ h) hmp) (hE (f := fun m => m.G L V) fs fs₁
          (fun _ _ _ _ _ e _ _ h => e ▸ h) hG) (.refl c) (hX hR hc hr'' hx))
      | rtLoad kl L g c₂ he hrt hmp hr'' hx =>
        exact .lift (.rtLoad kl L g c he (hE (f := fun m => m.rt L.addr.toNat) fs fs₁
          (fun _ _ _ e _ _ _ _ h => e ▸ h) hrt) (hE (f := fun m => m.mp L false) fs fs₁
          (fun _ _ _ _ e _ _ _ h => e ▸ h) hmp) (.refl c) fun v hG ho =>
          hX hR hc hr'' (hx v (hE (f := fun m => m.G L v) fs₁ fs (fun _ _ _ _ _ e _ _ h => e ▸ h) hG)
            fun w hw => ho w (hown s c fs c' fs' hc hr hWs c₁ fs₁ hr' L (Or.inl ⟨kl, g, he⟩) w hw)))
      | rtRmw k L op g c₂ he hrt hmp hr'' hx =>
        exact .lift (.rtRmw k L op g c he (hE (f := fun m => m.rt L.addr.toNat) fs fs₁
          (fun _ _ _ e _ _ _ _ h => e ▸ h) hrt) (hE (f := fun m => m.mp L true) fs fs₁
          (fun _ _ _ _ e _ _ _ h => e ▸ h) hmp) (.refl c) fun old hG ho =>
          let h := hx old (hE (f := fun m => m.G L old) fs₁ fs (fun _ _ _ _ _ e _ _ h => e ▸ h) hG) fun w hw =>
            ho w (hown s c fs c' fs' hc hr hWs c₁ fs₁ hr' L (Or.inr ⟨k, op, g, he⟩) w hw)
          ⟨fun new hn => hE (f := fun m => m.G L new) fs fs₁ (fun _ _ _ _ _ e _ _ h => e ▸ h) (h.1 new hn),
            hX hR hc hr'' h.2⟩)
      | sys K' call hK' hat hd hok hs =>
        by_cases hm : ∃ v, call = .exitGroup v ∧ ¬ (ms fs₁).abortAt s
        · -- `main`'s exit: the row at the real pair, no successor
          obtain ⟨v, rfl, -⟩ := hm
          exact .pre c₁ fs₁ hR (.sys K' _ hK' hat hd hok fun s₁ hs₁ => by
            simp [Scc.Sem.Kernel.certSuccs, Scc.Sem.Kernel.results] at hs₁)
        · refine .lift (.sys K' call (hE (f := fun m => m.K = some K') fs fs₁
            (fun _ _ _ _ _ _ e _ h => e ▸ h) hK') hat hd ⟨hok.1, hok.2.1, hok.2.2.1, fun v hv hn => ?_⟩
            fun s₁ hs₁ => let ⟨c₂, hr'', hx⟩ := hs s₁ hs₁; ⟨c, .refl c, hX hR hc hr'' hx⟩)
          exact (hm ⟨v, hv, hE (f := fun m => ¬ m.abortAt s) fs₁ fs (fun _ _ _ _ _ _ _ e h => e ▸ h) hn⟩).elim
      | holdLoad _ _ _ x sa u v e _ hx => exact (hxs x sa u v e hx).elim
      | xchgStore _ _ _ _ x sa u v e _ _ _ _ hx => exact (hxs x sa u v e hx).elim
      | ctrRmw _ _ _ x τ e _ _ _ _ hs =>
        exact (hs.elim (fun ⟨a, _, _, ht, _⟩ => hnb x a τ e ht) fun ⟨_, a, _, ⟨_, ht⟩, _⟩ => hnn x a _ e ht).elim
      | alloc _ _ x a τ e _ _ _ _ _ _ _ ht => exact (hnb x a τ e ht).elim
      | newStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh' => rw [hh] at hh'; cases hh'
      | emit K' buf n _ _ hK' hat hd _ _ _ _ =>
        exact (hnw s c fs c' fs' hc hr hWs K' (hms.K fs₁ ▸ hK') hat buf n hd).elim
      | fence k s₁ c₂ he hr'' hx =>
        cases hr'' with
        | loc hr'' => exact .lift (.fence k s₁ c he (.loc (.refl c)) (hX hR hc hr'' hx))
        | pub _ hps _ => exact (hnp _ _ hps).elim
  · obtain ⟨c₁, fs₁, hr', hx⟩ := hk s' hks
    exact ⟨c, fs, .refl _, hx.elim (fun hi => .inl ⟨hc, _, _, hi, hr.trans hr'⟩)
      fun hq => .inr ⟨hc, _, _, hq, hr.trans hr'⟩⟩

end SegWS

/-- **`SegWS.lagC`'s side conditions** from `W` to `W'` held back at the
pairs of `C`, as one premise. -/
structure LagOk {I : ISA} (p : Prog) (ms : List TermRun.Frame → MemSide I) (W W' : FragS I)
    (C : Ctl → List TermRun.Frame → Prop) : Prop where
  quiet : QuietFrom p C
  noWr : ∀ s c fs c' fs', C c fs → FrameRun p (c, fs) (c', fs') → W s c' fs' → ∀ K', (ms []).K = some K' →
    K'.atSys s = true → ∀ buf n, Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n)
  agree : MsAgree ms
  own : ∀ s c₀ fs₀ c fs, C c₀ fs₀ → FrameRun p (c₀, fs₀) (c, fs) → W s c fs →
    ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
    ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms fs₀).own s
  held : ∀ s c fs c' fs', W s c' fs' → FrameRun p (c, fs) (c', fs') → C c fs → W' s c fs

/-- **A segment held back under `LagOk`** (`SegWS.lagC`). -/
theorem LagOk.seg {I : ISA} {p : Prog} {ms : List TermRun.Frame → MemSide I} {W W' : FragS I}
    {C : Ctl → List TermRun.Frame → Prop} {K : I.State → I.State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {P Q : FragS I} (hL : LagOk p ms W W' C) (h : SegWS W K p lbl ms P Q) :
    SegWS W' K p lbl ms (LagF p C P) (LagF p C Q) :=
  h.lagC hL.quiet hL.noWr hL.agree hL.own hL.held

/-! ## Quiet tails -/

/-- **A quiet tail**: `let`s of an atom, a `+` or a `-`, `if`s, ending in
`ret`s (no call, no source event). -/
def qtail : Expr → Bool
  | .let_ _ (.atom _) e => qtail e
  | .let_ _ (.add _ _) e => qtail e
  | .let_ _ (.sub _ _) e => qtail e
  | .ifeq _ _ yes no => qtail yes && qtail no
  | .ret _ => true
  | _ => false

variable {p : Prog}

/-- **A control at a quiet tail**, with no hold, is `Quiet`. -/
theorem quiet_of_qtail {c : Ctl} (hq : qtail c.term = true) (hh : c.hold = none) : Quiet c := by
  obtain ⟨t, env, hold⟩ := c
  simp only at hq hh
  refine ⟨hh, ?_, ?_, ?_, fun x sa u v e ⟨_, hx⟩ => ?_, noPub_of_term ?_ ?_, ?_⟩
  · rintro x a e rfl; simp [qtail] at hq
  · rintro x a b e rfl; simp [qtail] at hq
  · rintro x a τ e rfl; simp [qtail] at hq
  · rcases hx with ⟨_, _, _, _, ht, _⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, _⟩ <;>
    · simp only at ht; subst ht; simp [qtail] at hq
  · rintro x a e rfl; simp [qtail] at hq
  · rintro x r a e rfl; simp [qtail] at hq
  · rintro x a _ e rfl; simp [qtail] at hq

/-- **A frame run from a quiet tail at depth 0**, with no hold, stays at
quiet tails at depth 0 with no hold. -/
theorem qtail_run {q q' : Ctl × List TermRun.Frame} (hr : FrameRun p q q') (h0 : q.2 = [])
    (hh : q.1.hold = none) (hq : qtail q.1.term = true) :
    q'.2 = [] ∧ q'.1.hold = none ∧ qtail q'.1.term = true := by
  induction hr with
  | refl => exact ⟨h0, hh, hq⟩
  | @step q q₁ q' hs _ ih =>
    refine ih ?_ hs.hold_none ?_
    · cases hs with
      | loc => exact h0
      | call => simp_all [qtail]
      | ret => cases h0
    · cases hs with
      | @loc c c' fs hs =>
        cases hc : c.term with
        | let_ x op e =>
          simp only [hc] at hq
          cases op <;> simp only [qtail] at hq
          all_goals first | (simp at hq; done) | skip
          case atom a => exact localStep_let1 hs.toLocalStep hc (.inl ⟨a, rfl⟩) ▸ hq
          case add a b => exact localStep_let1 hs.toLocalStep hc (.inr (.inl ⟨a, b, rfl⟩)) ▸ hq
          case sub a b => exact localStep_let1 hs.toLocalStep hc (.inr (.inr ⟨a, b, rfl⟩)) ▸ hq
        | ifeq a b yes no =>
          simp only [hc, qtail, Bool.and_eq_true] at hq
          rcases localStep_ifeq hs.toLocalStep hc with h | h
          · exact h ▸ hq.1
          · exact h ▸ hq.2
        | ret a => exact absurd hc (hs.not_ret a)
        | _ => simp [hc, qtail] at hq
      | call ht => simp [ht, qtail] at hq
      | ret => cases h0

/-- **The controls a frame run reaches from a quiet tail at depth 0**, with
no hold, are `Quiet` (`SegWS.lagC`'s `hq` at such held-back pairs). -/
theorem quietFrom_qtail {C : Ctl → List TermRun.Frame → Prop}
    (h : ∀ c fs, C c fs → fs = [] ∧ c.hold = none ∧ qtail c.term = true) : QuietFrom p C := by
  intro c fs hc c₁ fs₁ hr
  obtain ⟨h0, hh, hq⟩ := h c fs hc
  obtain ⟨-, hh', hq'⟩ := qtail_run hr h0 hh hq
  exact quiet_of_qtail hq' hh'

/-! ## One held-back pair -/

/-- **The one held-back pair** `(c₀, fs₀)`, as `LagF`'s `C`. -/
def HeldAt (c₀ : Ctl) (fs₀ : List TermRun.Frame) (c : Ctl) (fs : List TermRun.Frame) : Prop :=
  c = c₀ ∧ fs = fs₀

/-- **A real pair is held back at itself** (the lag's entry). -/
theorem LagF.heldAt {I : ISA} {X : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}
    (h : X s c fs) : LagF p (HeldAt c fs) X s c fs :=
  ⟨⟨rfl, rfl⟩, c, fs, h, .refl _⟩

/-- **`QuietFrom` at a quiet tail at depth 0** with no hold. -/
theorem quietFrom_heldAt {c₀ : Ctl} (hh : c₀.hold = none) (hq : qtail c₀.term = true) :
    QuietFrom p (HeldAt c₀ []) :=
  quietFrom_qtail fun _ _ ⟨hc, hf⟩ => hc ▸ ⟨hf, hh, hq⟩

/-- **No held-back pair at an allocation**: a source held back there is not
`Quiet` (`SegWS.lagC` does not apply; the source must take the allocation's
step with the target). -/
theorem not_quietFrom_newBuf {C : Ctl → List TermRun.Frame → Prop} {c : Ctl} {fs : List TermRun.Frame}
    (hc : C c fs) {x : String} {a : At} {τ : Ty} {e : Expr} (ht : c.term = .let_ x (.newBuf a τ) e) :
    ¬ QuietFrom p C :=
  fun h => (h c fs hc c fs (.refl _)).2.2.2.1 x a τ e ht

end Spike.Lib

/-- info: 'Spike.Lib.SegWS.lagC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegWS.lagC

/-- info: 'Spike.Lib.quietFrom_qtail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.quietFrom_qtail
