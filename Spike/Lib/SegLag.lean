/-
**A segment with the source control held back** (`SegW.lag`), for either ISA.

A segment built by the lowering's proofs (`Spike/Lib/LowerA64/Body.lean`)
moves the source control along with the code: each node's control is the
one a local run from the function's entry reaches. The one-thread consumer
(`SFacts`, `Spike/Lib/A64SegInst.lean`) asks facts of every pair's control,
some of which fail at the controls the run reaches (no pair at `ret`:
after a body's last `let` the control is at its `ret` while the target
still runs the return block).

`SegW.lag`: if no control of the segment's invariant has a source event
pending (`Quiet`: no hold, not at a load, store, exchange, allocation or
publication),
the segment holds with the source control **held back** at any control a
local run reaches each of its controls from (`Lag`), among those of a set
`C`: every instruction is matched by the source stuttering, and the local
runs the original segment takes are kept in the lag. The pairs' facts at
the held-back control are the obligation (`hW`). `SysOk` holds at the
held-back control as `main`'s exit takes a local run first (`MainExit`).
The segment's states make no `write` to the output (`hnw`): a source held
back cannot emit the output row's bytes.

- `Quiet`, `Lag`, `LagJ`, `sysOk_lag`: the controls without pending
  events, the held-back fragment and node invariant, `SysOk` from a later
  control;
- `SegW.lag`: the segment with the controls held back.
-/
import Spike.Lib.SegW

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **A control with no source event pending**: no hold, not at a load,
a store, an allocation, an exchange or a publication (`PubStep`). -/
def Quiet (c : Ctl) : Prop :=
  c.hold = none ∧ (∀ x a e, c.term ≠ .let_ x (.load true a) e) ∧
    (∀ x a b e, c.term ≠ .let_ x (.store true a b none) e) ∧ (∀ x a τ e, c.term ≠ .let_ x (.newBuf a τ) e) ∧
    (∀ x sa u v e, ¬ XchgSite c x sa u v e) ∧ (∀ k c', ¬ PubStep k c c') ∧
    ∀ x a e, c.term ≠ .let_ x (.new a) e

/-- **No publication at a control whose term is no `publish`/`intoRgn`
`let`** (`Quiet`'s last conjunct from the term). -/
theorem noPub_of_term {c : Ctl} (hp : ∀ x a e, c.term ≠ .let_ x (.publish a) e)
    (hr : ∀ x r a e, c.term ≠ .let_ x (.intoRgn r a) e) : ∀ k c', ¬ PubStep k c c' :=
  fun _ _ ⟨_, _, x, a, e, _, _, _, ht, _⟩ => ht.elim (fun h => hp x a e h.1) fun ⟨r, h, _⟩ => hr x r a e h

/-- **The fragment `X` held back** at the controls of `C` a local run
reaches `X`'s controls from. -/
def Lag {I : ISA} (p : Prog) (C : Ctl → Prop) (X : Frag I) : Frag I :=
  fun s c => ∃ c', X s c' ∧ LocalRun p c c' ∧ C c

/-- **A node invariant held back** as `Lag` holds a fragment back: at the
controls of `C` a local run reaches one of `J`'s controls from (for a node
of the held-back fragment, e.g. the abort block after `SegW.lag`). -/
def LagJ {α : Type} (p : Prog) (C : Ctl → Prop) (J : α → Ctl → Prop) : α → Ctl → Prop :=
  fun σ c => ∃ c', J σ c' ∧ LocalRun p c c' ∧ C c

/-- `SysOk` at a control a local run reaches a control from. -/
theorem sysOk_lag {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c c' : Ctl} {call : Scc.Sem.Kernel.Call}
    (h : SysOk p ms s c' call) (hr : LocalRun p c c') : SysOk p ms s c call := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun v hv hn => ?_⟩
  obtain ⟨c'', hr', hpl, hx⟩ := h4 v hv hn
  exact ⟨c'', hr.trans hr', hpl, hx⟩

namespace SegW

variable {I : ISA} {W W' : Frag I} {K : I.State → I.State → Prop} {p : Prog}
  {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I} {P Q : Frag I}

/-- **A segment with the source control held back**: if every control of
`W` is `Quiet` and no state of `W` is at a `write` to the output (`hnw`),
the segment from `P` to `Q` gives one from `P` held back to `Q` held back
(`Lag`, at the controls of `C`), inside `W'`, given that the pairs of `W`
held back are in `W'` (`hW`). -/
theorem lag {C : Ctl → Prop} (h : SegW W K p lbl ms P Q) (hq : ∀ s c, W s c → Quiet c)
    (hnw : ∀ s c, W s c → ∀ K', ms.K = some K' → K'.atSys s = true → ∀ buf n,
      Scc.Sem.Kernel.decode K'.nrs (K'.nr s) (K'.arg s) ≠ some (.write 1 buf n))
    (hW : ∀ s c c', W s c' → LocalRun p c c' → C c → W' s c) :
    SegW W' K p lbl ms (Lag p C P) (Lag p C Q) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  have hX : ∀ {s c c' c''}, LocalRun p c c' → C c → LocalRun p c' c'' → (inv s c'' ∨ Q s c'') →
      (Lag p C inv s c ∨ Lag p C Q s c) := fun hr hc hr' hx =>
    hx.elim (fun hi => .inl ⟨_, hi, hr.trans hr', hc⟩) (fun hq => .inr ⟨_, hq, hr.trans hr', hc⟩)
  refine ⟨Lag p C inv, fun s c ⟨c', hp, hr, hc⟩ => ⟨c', hP s c' hp, hr, hc⟩,
    fun s c ⟨c', hi, hr, hc⟩ => hW s c c' (hiW s c' hi) hr hc, fun s c ⟨c', hi, hr, hc⟩ => ?_⟩
  obtain ⟨hh, hld, hst, hnb, hxs, hnp, hnn⟩ := hq s c' (hiW s c' hi)
  obtain ⟨hout, hk⟩ := hcl s c' hi
  refine ⟨fun hK => ?_, fun s' hks => ?_⟩
  · cases hout hK with
    | silent s' c'' he hr' hx => exact .silent s' c he (.refl c) (hX hr hc hr' hx)
    | choice P t he ht hl =>
      exact .choice P t he ht fun s' hs' =>
        let ⟨c'', hr', hx⟩ := hl s' hs'
        ⟨c, .refl c, hX hr hc hr' hx⟩
    | load _ _ _ x a e _ _ _ ht => exact (hld x a e ht).elim
    | store _ _ _ _ x a b e _ _ _ _ _ ht => exact (hst x a b e ht).elim
    | rtStore kr L V s' c'' he hrt hmp hG hr' hx =>
      exact .rtStore kr L V s' c he hrt hmp hG (.refl c) (hX hr hc hr' hx)
    | rtLoad kl L g c'' he hrt hmp hr' hx =>
      exact .rtLoad kl L g c he hrt hmp (.refl c) fun v hG ho => hX hr hc hr' (hx v hG ho)
    | rtRmw k L op g c'' he hrt hmp hr' hx =>
      exact .rtRmw k L op g c he hrt hmp (.refl c) fun old hG ho =>
        ⟨(hx old hG ho).1, hX hr hc hr' (hx old hG ho).2⟩
    | sys K' call hK' hat hd hok hs =>
      exact .sys K' call hK' hat hd (sysOk_lag hok hr) fun s' hs' =>
        let ⟨c'', hr', hx⟩ := hs s' hs'
        ⟨c, .refl c, hX hr hc hr' hx⟩
    | holdLoad _ _ _ x sa u v e _ hx => exact (hxs x sa u v e hx).elim
    | xchgStore _ _ _ _ x sa u v e _ _ _ _ hx => exact (hxs x sa u v e hx).elim
    | ctrRmw _ _ _ x τ e _ _ _ _ hs =>
      exact (hs.elim (fun ⟨a, _, _, ht, _⟩ => hnb x a τ e ht) fun ⟨_, a, _, ht, _⟩ => hnn x a e ht).elim
    | alloc _ _ x a τ e _ _ _ _ _ _ _ ht => exact (hnb x a τ e ht).elim
    | newStore _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh' => rw [hh] at hh'; cases hh'
    | emit K' buf n _ _ hK' hat hd _ _ _ _ =>
      exact (hnw s c' (hiW s c' hi) K' hK' hat buf n hd).elim
    | fence k s' c'' he hr' hx =>
      cases hr' with
      | loc hr' => exact .fence k s' c he (.loc (.refl c)) (hX hr hc hr' hx)
      | pub _ hps _ => exact (hnp _ _ hps).elim
  · obtain ⟨c'', hr', hx⟩ := hk s' hks
    exact ⟨c, .refl c, hX hr hc hr' hx⟩

end SegW

end Spike.Lib
