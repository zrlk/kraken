import WeakCore.TermOwnCLoad

/-! # TermOwnCPin: the pin word under the window conditions (ownC (iii) caveat (b1))

Under `WinG` (A) at the unit and `PromAbove`, the predecessor of the unit's lowest own promise is
the coherence message (`predAt_coh`): a message strictly between coherence and `tw` at the unit is
an own promise (A) below `tw`, contradicting `LowOwn` — the promise case is vacuous.  The owner's
invariant (`LatestSF`) types the coherence message (`coh_wordOK`): no load reasoning is needed.
-/

namespace TermOwnCPin

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `WordOK` is upward closed in `WLe1`. -/
theorem wordOK_up {E : TEnv} {T : Ty} {o : Nat} {w w' : Word} (h : WordOK E T o w) (hle : WLe1 w w') :
    WordOK E T o w' := by
  obtain ⟨b, S, ws, o', w0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨b, S, ws, o', w0, h1, h2, h3, WLe1_trans h4 hle, h5⟩

/-- **The coherence message is the pin**: under `WinG` (A) at the unit, coherence below the lowest
own promise `tw` there, the predecessor of `tw` is the coherence message.  (An own promise between
them would be below `tw`: vacuous by `LowOwn`.) -/
theorem predAt_coh {E : TEnv} {s : St} {l : AllocLabel} {o : Nat} {tw : Ts} {m : Msg}
    (hlo : TermPlant.LowOwn s ⟨l, o⟩ tw) (hlt : s.vs.coh ⟨l, o⟩ < tw)
    (hm : s.mem[s.vs.coh ⟨l, o⟩]? = some m) (hml : m.loc = ⟨l, o⟩)
    (hW : TermOverCr.WinG E s l o tw) :
    ∀ tw', TermPlant.LowOwn s ⟨l, o⟩ tw' → PredAt s.mem ⟨l, o⟩ tw' (mw m) := by
  intro tw' hl'
  rw [TermPlant.LowOwn_uniq hl' hlo]
  refine ⟨_, m, hlt, hm, hml, rfl, fun t' m' h1 h2 h3 h4 => ?_⟩
  rcases hW.1 t' m' h3 h4 (Nat.le_of_lt h2) with h | h
  · exact absurd (hlo.2.2 t' m' h h3 h4) (Nat.not_le.mpr h2)
  · rw [h4] at h
    exact absurd h (Nat.not_le.mpr h1)

#print axioms predAt_coh

/-- `PromAbove` puts coherence below the lowest own promise at the unit. -/
theorem coh_lt_of_promAbove {s : St} {a : Address} {tw : Ts} (hPA : PromAbove s)
    (hlo : TermPlant.LowOwn s a tw) : s.vs.coh a < tw := by
  obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := hlo
  have := hPA tw htw mw hmw
  rw [hml] at this
  exact this

/-- **The owner's invariant types the coherence message** at an initialised unit of an own cell. -/
theorem coh_wordOK {E : TEnv} {c : Cell} {fr : Option Ts} {mem : Memory} {S : Ts → Prop}
    {coh : Address → Ts} {l : AllocLabel} {o n : Nat} {vals : List Word} {v : Word}
    (hc : CellOK E n c.ty vals)
    (hi : ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → o < n * nWords us)
    (hv : vals[o]? = some v) (hL : LatestSF E c fr mem S coh ⟨l, o⟩ v) :
    ∃ m, mem[coh ⟨l, o⟩]? = some m ∧ m.loc = ⟨l, o⟩ ∧ WordOK E c.ty o (mw m) := by
  obtain ⟨⟨m, hm, hml, hd⟩, -, -⟩ := hL
  refine ⟨m, hm, hml, ?_⟩
  rcases hd with ⟨he, hview⟩ | ⟨-, hT⟩
  · exact wordOK_up (TermStepper.cellOK_wordOK hc hi hv) ⟨he.symm ▸ rfl, fun x g hx => hview x g hx⟩
  · have e : m.loc.offset = o := by rw [hml]
    unfold TypedAt at hT
    rw [e] at hT
    exact hT

#print axioms coh_wordOK

/-- **The pin for `freeQW` under the window conditions**: the coherence message's word, typed. -/
theorem pin_of_winG {E : TEnv} {s : St} {l : AllocLabel} {o n : Nat} {c : Cell} {fr : Option Ts}
    {S : Ts → Prop} {vals : List Word} {v : Word} {tw : Ts}
    (hlo : TermPlant.LowOwn s ⟨l, o⟩ tw) (hPA : PromAbove s) (hW : TermOverCr.WinG E s l o tw)
    (hc : CellOK E n c.ty vals)
    (hi : ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → o < n * nWords us)
    (hv : vals[o]? = some v) (hL : LatestSF E c fr s.mem S s.vs.coh ⟨l, o⟩ v) :
    ∃ w, (∀ tw', TermPlant.LowOwn s ⟨l, o⟩ tw' → PredAt s.mem ⟨l, o⟩ tw' w) ∧ WordOK E c.ty o w := by
  obtain ⟨m, hm, hml, hok⟩ := coh_wordOK hc hi hv hL
  exact ⟨mw m, predAt_coh hlo (coh_lt_of_promAbove hPA hlo) hm hml hW, hok⟩

#print axioms pin_of_winG

end TermOwnCPin
