import WeakCore.TermStep

/-!
# TermPaid: the (H) block vocabulary for the paid clause

The concrete instances of the parameters of `TermPlantPaid.PaidBA` and of
`TermGhostCr.ofPaid`:
- `TwWords mem a n ws`: `ws` are the first writes at the `n` units of the block at `a`;
- `BlkValR E a ws R`: `ws` are a value of the block type at `a`, holding `R`;
- `BlkHeld E s a n H`: memory's latest words at the block's units hold `H`;
- `BlkHeldAfter E s tw a ws H`: the same once `tw` is fulfilled (erased from the promises);
- `Desig E mem tw m n`: `tw` (the message `m`) is a designated promise with a block of width `n`;
- `PaidB E s tw m n Hb crb dbb`: the paid clause of that block.
-/

namespace TermPaid

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- (H) Unit `o` of the block at `a`. -/
def unitAt (a : Address) (o : Nat) : Address := ⟨a.label, a.offset + o⟩

/-- (H) `ws` are the first writes at the `n` units of the block at `a`. -/
def TwWords (mem : Memory) (a : Address) (n : Nat) (ws : List Word) : Prop :=
  ws.length = n ∧ ∀ o x, ws[o]? = some x → ∃ h m, FirstW mem (unitAt a o) h ∧ mem[h]? = some m ∧ x = mw m

/-- (H) `ws` are a value of the block type at `a`, holding `R`. -/
def BlkValR (E : TEnv) (a : Address) (ws : List Word) (R : Res) : Prop :=
  ∃ U, BlkStart E a U ∧ wc U = some ws.length ∧ ValOfR E U ws R

/-- (H) Memory's latest words at the `n` units of the block at `a` hold `H`. -/
def BlkHeld (E : TEnv) (s : St) (a : Address) (n : Nat) (H : Res) : Prop :=
  ∃ U ws, BlkStart E a U ∧ wc U = some n ∧ ws.length = n ∧
    (∀ o x, ws[o]? = some x → LatestNP s.mem (PromAt E s (unitAt a o)) (unitAt a o) x) ∧
    VRR (fun _ => 0) (CE E.unsee) U (shp U) ws H

/-- (H) `BlkHeld` once `tw` is fulfilled by the words `ws`: the promise is erased (the
fulfilling write's words are `tw`'s, so memory is unchanged). -/
def BlkHeldAfter (E : TEnv) (s : St) (tw : Ts) (a : Address) (ws : List Word) (H : Res) : Prop :=
  BlkHeld E { s with promises := s.promises.erase tw } a ws.length H

/-- (H) `tw` (the message `m`) is a designated promise whose block at `m.loc` has width `n`
(`0` at a slot start that starts no block). -/
def Desig (E : TEnv) (mem : Memory) (tw : Ts) (m : Msg) (n : Nat) : Prop :=
  DesigAt E mem m.loc tw ∧
    ((∃ U, BlkStart E m.loc U ∧ wc U = some n) ∨ ((∀ U, ¬ BlkStart E m.loc U) ∧ n = 0))

/-- (R1) **The paid clause** of the block of a designated promise (the `PaidBA`): for every
value `ws` of the block on `tw`'s words, holding `Rv`, the block count after the fulfil `H'`
satisfies `dbb + H' ≤ crb + Hb + Rv`, where `Hb` is memory's count of the block now. -/
def PaidB (E : TEnv) (s : St) (tw : Ts) (m : Msg) (n : Nat) (Hb crb dbb : Res) : Prop :=
  ∀ ws Rv, TwWords s.mem m.loc n ws → BlkValR E m.loc ws Rv →
    ∃ H', BlkHeldAfter E s tw m.loc ws H' ∧ dbb + H' ≤ crb + Hb + Rv

theorem TwWords_length {mem : Memory} {a : Address} {n : Nat} {ws : List Word}
    (h : TwWords mem a n ws) : ws.length = n := h.1
#print axioms TwWords_length

/-- (H) The first writes at a block's units are determined. -/
theorem TwWords_uniq {mem : Memory} {a : Address} {n : Nat} {ws ws' : List Word}
    (h : TwWords mem a n ws) (h' : TwWords mem a n ws') : ws = ws' := by
  apply List.ext_getElem?
  intro o
  cases hx : ws[o]? with
  | none =>
    cases hy : ws'[o]? with
    | none => rfl
    | some y =>
      have h1 : o < ws'.length := (List.getElem?_eq_some_iff.1 hy).1
      have h2 : ¬ o < ws.length := fun hh => by rw [List.getElem?_eq_getElem hh] at hx; cases hx
      rw [h.1] at h2; rw [h'.1] at h1; exact absurd h1 h2
  | some x =>
    cases hy : ws'[o]? with
    | none =>
      have h1 : o < ws.length := (List.getElem?_eq_some_iff.1 hx).1
      have h2 : ¬ o < ws'.length := fun hh => by rw [List.getElem?_eq_getElem hh] at hy; cases hy
      rw [h'.1] at h2; rw [h.1] at h1; exact absurd h1 h2
    | some y =>
      obtain ⟨t, m, hf, hm, rfl⟩ := h.2 o x hx
      obtain ⟨t', m', hf', hm', rfl⟩ := h'.2 o y hy
      obtain rfl : t = t' := FirstW_uniq hf hf'
      rw [hm] at hm'; cases hm'; rfl
#print axioms TwWords_uniq

/-- (H) A designated promise is a `DesigAt` one. -/
theorem Desig.desigAt {E : TEnv} {mem : Memory} {tw : Ts} {m : Msg} {n : Nat} (h : Desig E mem tw m n) :
    DesigAt E mem m.loc tw := h.1
#print axioms Desig.desigAt

/-- (H) A designated promise has a width. -/
theorem Desig_of {E : TEnv} {mem : Memory} {tw : Ts} {m : Msg} (h : DesigAt E mem m.loc tw)
    (hw : ∀ U, BlkStart E m.loc U → ∃ n, wc U = some n) : ∃ n, Desig E mem tw m n := by
  by_cases hb : ∃ U, BlkStart E m.loc U
  · obtain ⟨U, hU⟩ := hb
    obtain ⟨n, hn⟩ := hw U hU
    exact ⟨n, h, Or.inl ⟨U, hU, hn⟩⟩
  · exact ⟨0, h, Or.inr ⟨fun U hU => hb ⟨U, hU⟩, rfl⟩⟩
#print axioms Desig_of

/-- (R1 case 1) **The plant creates `PaidB`**: debit = memory's count, no credit, when after the
fulfil the block is re-counted at the fulfilling value (`hall`). -/
theorem paidB_plant {E : TEnv} {s : St} {tw : Ts} {m : Msg} {n : Nat}
    (hall : ∀ ws Rv, TwWords s.mem m.loc n ws → BlkValR E m.loc ws Rv → BlkHeldAfter E s tw m.loc ws Rv)
    (Rg : Res) : PaidB E s tw m n Rg .zero Rg :=
  fun ws Rv hw hv => ⟨Rv, hall ws Rv hw hv, by rw [Res.zero_add]; exact Res.le_refl _⟩
#print axioms paidB_plant

/-- (R1 case 2) **A step keeps `PaidB`** with the slack `δ` credited
(`hδ : Hb + Rin ≤ δ + Hn + Rt`), given the after-fulfil counts move by the mix bound (`hmix`). -/
theorem paidB_step {E E' : TEnv} {s s' : St} {tw : Ts} {m : Msg} {n : Nat} {Hb Hn crb dbb Rin Rt δ : Res}
    (h : PaidB E s tw m n Hb crb dbb)
    (hw : ∀ ws, TwWords s'.mem m.loc n ws → TwWords s.mem m.loc n ws)
    (hv : ∀ ws Rv, BlkValR E' m.loc ws Rv → BlkValR E m.loc ws Rv)
    (hmix : ∀ ws Rv H', TwWords s.mem m.loc n ws → BlkValR E m.loc ws Rv → BlkHeldAfter E s tw m.loc ws H' →
      ∃ H'', BlkHeldAfter E' s' tw m.loc ws H'' ∧ H'' + Rt ≤ H' + Rin)
    (hδ : Hb + Rin ≤ δ + Hn + Rt) :
    PaidB E' s' tw m n Hn (crb + δ) dbb := by
  intro ws Rv hw' hv'
  obtain ⟨H', hA, hle⟩ := h ws Rv (hw ws hw') (hv ws Rv hv')
  obtain ⟨H'', hA2, hm⟩ := hmix ws Rv H' (hw ws hw') (hv ws Rv hv') hA
  refine ⟨H'', hA2, fun key => ?_⟩
  have e1 := hle key
  have e2 := hm key
  have e3 := hδ key
  simp only [Res.add_apply] at e1 e2 e3 ⊢
  omega
#print axioms paidB_step

/-- (R1 case 1, `hall`) **The block count after the fulfil is the fulfilling value's**, when
memory's latest words at the block's units, `tw` erased from the promises, are the value's
words. -/
theorem blkHeldAfter_of {E : TEnv} {s : St} {tw : Ts} {a : Address} {ws : List Word} {Rv : Res}
    (hv : BlkValR E a ws Rv)
    (hL : ∀ o x, ws[o]? = some x → LatestNP s.mem (PromAt E { s with promises := s.promises.erase tw } (unitAt a o))
      (unitAt a o) x) :
    BlkHeldAfter E s tw a ws Rv := by
  obtain ⟨U, hb, hw, hval, -⟩ := hv
  exact ⟨U, ws, hb, hw, rfl, hL, hval⟩
#print axioms blkHeldAfter_of

/-- (R1 case 1) `paidB_plant` from the latest words: if after erasing `tw` the latest words at
the block's units are its first writes, the plant's `PaidB` holds. -/
theorem paidB_plant_of {E : TEnv} {s : St} {tw : Ts} {m : Msg} {n : Nat}
    (hL : ∀ ws, TwWords s.mem m.loc n ws → ∀ o x, ws[o]? = some x →
      LatestNP s.mem (PromAt E { s with promises := s.promises.erase tw } (unitAt m.loc o)) (unitAt m.loc o) x)
    (Rg : Res) : PaidB E s tw m n Rg .zero Rg :=
  paidB_plant (fun ws _ hw hv => blkHeldAfter_of hv (hL ws hw)) Rg
#print axioms paidB_plant_of

end TermPaid
