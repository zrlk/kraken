/-
**A segment at depth with the source held back at any frames**
(`SegWS.lagF`), for either ISA: `SegWS.lag` (`Spike/Lib/SegLagS.lean`) with
the held-back pairs at any frames, not only at depth 0.

A segment built over the source's real pairs gives one whose pairs are
held back at the pairs of a set `C` (`LagF`: a frame run reaches a real pair
from the held-back one). As for `SegWS.lag`, every instruction is matched by
the source stuttering, the frame runs kept in the lag, except `main`'s exit:
an `exit_group` off an abort site keeps its row at the real pair after the
run (`OutS.pre`). The pairs' facts at the held-back pair are the obligation
(`hW`). Used to hold `main`'s source at a callee's `ret` (at depth) from that
callee's return through `main`'s exit, so that no pair of the segment is at
`main`'s `ret` at depth 0.

- `LagF`: the held-back fragment;
- `LagS.toF`: `LagS` is `LagF` at the pairs at depth 0;
- `SegWS.lagF`: the segment with the pairs held back.
-/
import Spike.Lib.SegLagS

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **The fragment `X` held back** at the pairs of `C` a frame run reaches
`X`'s pairs from. -/
def LagF {I : ISA} (p : Prog) (C : Ctl → List TermRun.Frame → Prop) (X : FragS I) : FragS I :=
  fun s c fs => C c fs ∧ ∃ c' fs', X s c' fs' ∧ FrameRun p (c, fs) (c', fs')

/-- `LagS` is `LagF` at the pairs at depth 0. -/
theorem LagS.toF {I : ISA} {p : Prog} {C : Ctl → Prop} {X : FragS I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} (h : LagS p C X s c fs) : LagF p (fun c fs => fs = [] ∧ C c) X s c fs := by
  obtain ⟨rfl, hc, h⟩ := h
  exact ⟨⟨rfl, hc⟩, h⟩

namespace SegWS

variable {I : ISA} {W W' : FragS I} {K : I.State → I.State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q : FragS I}

/-- **A segment with the source held back at any frames** (`SegWS.lag` at
`LagF`): if every control a frame run reaches from a pair of `W` is `Quiet`
(`hq`), no state of `W` is at a `write` to the output (`hnw`), the memory
sides agree (`hms`) and, where a state of `W` reads the runtime's memory
(`RtReads`), the words owned at the frames a run from its pair reaches are
owned at the held-back pair's frames (`hown`), the segment from `P` to `Q`
gives one from `P` held back to `Q` held back (`LagF`, at the pairs of `C`),
inside `W'`, given that the pairs of `W` held back are in `W'` (`hW`). -/
theorem lagF {C : Ctl → List TermRun.Frame → Prop} (h : SegWS W K p lbl ms P Q)
    (hq : ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → Quiet c₁)
    (hnw : ∀ s c fs, W s c fs → ∀ K', (ms []).K = some K' → K'.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n))
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
      obtain ⟨hh, hld, hst, hnb, hxs⟩ := hq s c' fs' hWs c₁ fs₁ hr'
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
      | ctrRmw _ _ _ x a τ e _ _ _ _ _ _ ht => exact (hnb x a τ e ht).elim
      | alloc _ _ x a τ e _ _ _ _ _ _ _ ht => exact (hnb x a τ e ht).elim
      | emit K' buf n _ _ hK' hat hd _ _ _ _ =>
        exact (hnw s c' fs' hWs K' (hms.K fs₁ ▸ hK') hat buf n hd).elim
  · obtain ⟨c₁, fs₁, hr', hx⟩ := hk s' hks
    exact ⟨c, fs, .refl _, hx.elim (fun hi => .inl ⟨hc, _, _, hi, hr.trans hr'⟩)
      fun hq => .inr ⟨hc, _, _, hq, hr.trans hr'⟩⟩

end SegWS

end Spike.Lib

/-- info: 'Spike.Lib.SegWS.lagF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.SegWS.lagF
