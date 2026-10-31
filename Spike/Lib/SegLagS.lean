/-
**A segment at depth with the source held back at depth 0** (`SegWS.lag`),
for either ISA: the frames twin of `SegW.lag` (`Spike/Lib/SegLag.lean`).

A segment built over the source's real pairs (a body with calls: each
node's control and frames those a frame run from the function's entry
reaches, `Spike/Lib/A64CallS.lean`) gives one whose pairs are held back at
depth 0 at the controls of a set `C` (`LagS`: a frame run reaches a real pair
from the held-back one). Every instruction is matched by the source
stuttering, the frame runs kept in the lag, except `main`'s exit: an
`exit_group` off an abort site keeps its row at the real pair after the
run (`OutS.pre`; the call has no successor). The pairs' facts at the
held-back pair are the obligation (`hW`).

- `LagS`: the held-back fragment;
- `SegWS.lag`: the segment with the pairs held back, given that every
  control a frame run reaches from a pair of `W` is `Quiet` (`hq`), no
  state of `W` is at a `write` to the output (`hnw`), the memory sides
  at the frames agree with depth 0's on what the rows read (`hms`), and the
  words owned at the frames a run reaches are owned at depth 0 where a row
  reads the runtime's memory (`hown`, `RtReads`: the owned words may depend
  on the frames elsewhere).
- `RtReads`: the state is at a load or read-modify-write of the runtime's
  memory at `L`;
- `ownIncl_of_indep`: `hown` when the owned words do not depend on the
  frames.
- `MainExitS`: `main`'s exit after a frame run back to depth 0 (the source
  at a held-back pair returns from `main` only after its calls return);
  `MainExit.toS`: with the empty run.
-/
import Spike.Lib.SegS
import Spike.Lib.SegLag

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **The fragment `X` held back at depth 0**, at the controls of `C` a frame
run reaches `X`'s pairs from. -/
def LagS {I : ISA} (p : Prog) (C : Ctl → Prop) (X : FragS I) : FragS I :=
  fun s c fs => fs = [] ∧ C c ∧ ∃ c' fs', X s c' fs' ∧ FrameRun p (c, []) (c', fs')

/-- **The memory sides at the frames agree with depth 0's** on what the
rows other than `main`'s exit read: the source's reads, the runtime's
words, their mappings and values, the kernel model and the abort sites (the
words owned may depend on the frames: `SegWS.lag`'s `hown`). -/
structure MsAgree {I : ISA} (ms : List TermRun.Frame → MemSide I) : Prop where
  rd : ∀ fs, (ms fs).rd = (ms []).rd
  rt : ∀ fs, (ms fs).rt = (ms []).rt
  mp : ∀ fs, (ms fs).mp = (ms []).mp
  G : ∀ fs, (ms fs).G = (ms []).G
  K : ∀ fs, (ms fs).K = (ms []).K
  abortAt : ∀ fs, (ms fs).abortAt = (ms []).abortAt

/-- **`main` returns with code `v` after a frame run** from the pair
`(s, c)` at depth 0: the source runs, through calls that return, to a
control at depth 0 from which `main` returns with code `v` (`MainExit`). -/
def MainExitS {I : ISA} (p : Prog) (ms : MemSide I) (s : I.State) (c : Ctl) (v : Nat) : Prop :=
  ∃ c', FrameRun p (c, []) (c', []) ∧ MainExit p ms s c' v

/-- `MainExit` is `MainExitS` with the empty run. -/
theorem MainExit.toS {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl} {v : Nat}
    (h : MainExit p ms s c v) : MainExitS p ms s c v :=
  ⟨c, .refl _, h⟩

/-- **The state reads the runtime's memory at `L`**: it is at a load
(`Out.rtLoad`) or a read-modify-write (`Out.rtRmw`) at `L`, the rows reading
the words owned. -/
def RtReads {I : ISA} (s : I.State) (L : Loc) : Prop :=
  (∃ (kl : Kraken.LoadKind) (g : Val → I.State), I.exec s = some (.load kl false L fun v => .done (g v))) ∨
    ∃ (k : Kraken.RmwKind) (op : Val → Option Val) (g : Val → I.State),
      I.exec s = some (.rmw k false L op fun v => .done (g v))

/-- **`SegWS.lag`'s `hown` when the owned words do not depend on the
frames** (`h`), for any fragment. -/
theorem ownIncl_of_indep {I : ISA} {W : FragS I} {p : Prog} {ms : List TermRun.Frame → MemSide I}
    (h : ∀ fs, (ms fs).own = (ms []).own) :
    ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms []).own s :=
  fun _ _ _ _ _ fs₁ _ _ _ _ hw => h fs₁ ▸ hw

namespace SegWS

variable {I : ISA} {W W' : FragS I} {K : I.State → I.State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q : FragS I}

/-- **A segment at depth with the source held back at depth 0**: if every
control a frame run reaches from a pair of `W` is `Quiet` (`hq`), no state of
`W` is at a `write` to the output (`hnw`), the memory sides agree (`hms`)
and, where a state of `W` reads the runtime's memory (`RtReads`), the words
owned at the frames a run from its pair reaches are owned at depth 0
(`hown`), the segment from `P` to `Q` gives one from `P` held back to `Q` held
back (`LagS`, at the controls of `C`), inside `W'`, given that the pairs of
`W` held back are in `W'` (`hW`). -/
theorem lag {C : Ctl → Prop} (h : SegWS W K p lbl ms P Q)
    (hq : ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → Quiet c₁)
    (hnw : ∀ s c fs, W s c fs → ∀ K', (ms []).K = some K' → K'.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n))
    (hms : MsAgree ms)
    (hown : ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ (ms fs₁).own s → (L, w) ∈ (ms []).own s)
    (hW : ∀ s c c' fs', W s c' fs' → FrameRun p (c, []) (c', fs') → C c → W' s c []) :
    SegWS W' K p lbl ms (LagS p C P) (LagS p C Q) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  -- a landing after a run from the held-back pair is a held-back pair
  have hX : ∀ {s c c₁ fs₁ c₂}, FrameRun p (c, []) (c₁, fs₁) → C c → LocalRun p c₁ c₂ →
      Pend p (fun s c fs => inv s c fs ∨ Q s c fs) s c₂ fs₁ →
      Pend p (fun s c fs => LagS p C inv s c fs ∨ LagS p C Q s c fs) s c [] := by
    intro s c c₁ fs₁ c₂ hr hc hr' ⟨c₃, fs₃, hr'', hx⟩
    have hR := hr.trans ((FrameRun.ofLocal hr' fs₁).trans hr'')
    exact .of (hx.elim (fun hi => .inl ⟨rfl, hc, _, _, hi, hR⟩) fun hq => .inr ⟨rfl, hc, _, _, hq, hR⟩)
  refine ⟨LagS p C inv, fun s c fs ⟨he, hc, c', fs', hp, hr⟩ => ⟨he, hc, c', fs', hP s c' fs' hp, hr⟩,
    fun s c fs ⟨he, hc, c', fs', hi, hr⟩ => he ▸ hW s c c' fs' (hiW s c' fs' hi) hr hc, ?_⟩
  rintro s c fs ⟨rfl, hc, c', fs', hi, hr⟩
  have hWs := hiW s c' fs' hi
  obtain ⟨hout, hk⟩ := hcl s c' fs' hi
  refine ⟨fun hK => ?_, fun s' hks => ?_⟩
  · cases hout hK with
    | frame s₁ c₁ fs₁ he hr' hx =>
      exact .frame s₁ c [] he (.refl _) (hX (hr.trans hr') hc (.refl _) hx)
    | pre c₁ fs₁ hr' ho =>
      have hR := hr.trans hr'
      obtain ⟨hh, hld, hst, hnb, hxs, hnp, hnn⟩ := hq s c' fs' hWs c₁ fs₁ hr'
      cases ho with
      | silent s₁ c₂ he hr'' hx => exact .lift (.silent s₁ c he (.refl c) (hX hR hc hr'' hx))
      | choice P t he ht hl =>
        exact .lift (.choice P t he ht fun s₁ hs₁ =>
          let ⟨c₂, hr'', hx⟩ := hl s₁ hs₁
          ⟨c, .refl c, hX hR hc hr'' hx⟩)
      | load _ _ _ x a e _ _ _ ht => exact (hld x a e ht).elim
      | store _ _ _ _ x a b e _ _ _ _ _ ht => exact (hst x a b e ht).elim
      | rtStore kr L V s₁ c₂ he hrt hmp hG hr'' hx =>
        exact .lift (.rtStore kr L V s₁ c he (hms.rt fs₁ ▸ hrt) (hms.mp fs₁ ▸ hmp) (hms.G fs₁ ▸ hG) (.refl c)
          (hX hR hc hr'' hx))
      | rtLoad kl L g c₂ he hrt hmp hr'' hx =>
        exact .lift (.rtLoad kl L g c he (hms.rt fs₁ ▸ hrt) (hms.mp fs₁ ▸ hmp) (.refl c) fun v hG ho =>
          hX hR hc hr'' (hx v (hms.G fs₁ ▸ hG) fun w hw =>
            ho w (hown s c' fs' hWs c₁ fs₁ hr' L (Or.inl ⟨kl, g, he⟩) w hw)))
      | rtRmw k L op g c₂ he hrt hmp hr'' hx =>
        exact .lift (.rtRmw k L op g c he (hms.rt fs₁ ▸ hrt) (hms.mp fs₁ ▸ hmp) (.refl c) fun old hG ho =>
          let h := hx old (hms.G fs₁ ▸ hG) fun w hw =>
            ho w (hown s c' fs' hWs c₁ fs₁ hr' L (Or.inr ⟨k, op, g, he⟩) w hw)
          ⟨fun new hn => hms.G fs₁ ▸ h.1 new hn, hX hR hc hr'' h.2⟩)
      | sys K' call hK' hat hd hok hs =>
        by_cases hm : ∃ v, call = .exitGroup v ∧ ¬ (ms fs₁).abortAt s
        · -- `main`'s exit: the row at the real pair, no successor
          obtain ⟨v, rfl, -⟩ := hm
          exact .pre c₁ fs₁ hR (.sys K' _ hK' hat hd hok fun s₁ hs₁ => by
            simp [Scc.Sem.Kernel.certSuccs, Scc.Sem.Kernel.results] at hs₁)
        · refine .lift (.sys K' call (hms.K fs₁ ▸ hK') hat hd ⟨hok.1, hok.2.1, hok.2.2.1, fun v hv hn => ?_⟩
            fun s₁ hs₁ => let ⟨c₂, hr'', hx⟩ := hs s₁ hs₁; ⟨c, .refl c, hX hR hc hr'' hx⟩)
          exact (hm ⟨v, hv, hms.abortAt fs₁ ▸ hn⟩).elim
      | holdLoad _ _ _ x sa u v e _ hx => exact (hxs x sa u v e hx).elim
      | xchgStore _ _ _ _ x sa u v e _ _ _ _ hx => exact (hxs x sa u v e hx).elim
      | ctrRmw _ _ _ x τ e _ _ _ _ hs =>
        exact (hs.elim (fun ⟨a, _, _, ht, _⟩ => hnb x a τ e ht) fun ⟨_, a, _, ⟨_, ht⟩, _⟩ => hnn x a _ e ht).elim
      | alloc _ _ x a τ e _ _ _ _ _ _ _ ht => exact (hnb x a τ e ht).elim
      | newStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh' => rw [hh] at hh'; cases hh'
      | emit K' buf n _ _ hK' hat hd _ _ _ _ =>
        exact (hnw s c' fs' hWs K' (hms.K fs₁ ▸ hK') hat buf n hd).elim
      | fence k s₁ c₂ he hr'' hx =>
        cases hr'' with
        | loc hr'' => exact .lift (.fence k s₁ c he (.loc (.refl c)) (hX hR hc hr'' hx))
        | pub _ hps _ => exact (hnp _ _ hps).elim
  · obtain ⟨c₁, fs₁, hr', hx⟩ := hk s' hks
    exact ⟨c, [], .refl _, hx.elim (fun hi => .inl ⟨rfl, hc, _, _, hi, hr.trans hr'⟩)
      fun hq => .inr ⟨rfl, hc, _, _, hq, hr.trans hr'⟩⟩

end SegWS

end Spike.Lib
