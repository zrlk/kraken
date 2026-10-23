/-
**The start of the one-thread invariant** (`Scc/Sem/Rows1.lean`): `Inv1`
holds of a loaded target thread and the source start.

The source starts with empty memory (`Scc/Sem/SrcStart.lean`, `start`) and
the target with no message (`Config.init`: the image is the initial values
`Memory.init`, not messages; `Scc/Sem/TargetA64.lean`, `imageMem`). What is
left of the memory relation is the layout injection: the static labels
where `Λ` puts them, each an aligned word range inside `Λ.data`, distinct
labels disjoint. For `lbl := Λ.static` those come from the static link's
image check (`Scc/Cert/LinkImage.lean`, `imageOk`: `image_sub`,
`image_disj`), given that each static label is placed at a data symbol
of its own whose item covers it (`StaticSyms`).

- `MemRelP.start`: the relation at an empty source memory and a target
  memory with no message, for any injection with the three layout clauses;
- `Inv1.start`: the invariant there, for a thread with no promise;
- `StaticSyms`, `StaticSyms.of_none`: static labels at their symbols (none
  at all: the hello-world layouts);
- `StaticSyms.range`, `StaticSyms.disj`: the layout clauses of
  `lbl := Λ.static`, from `imageOk`;
- `Inv1.start_static`: the invariant at the start with `lbl := Λ.static`.

Not here: the `Components` of the start (`Scc/Sem/Correct.lean`), and the
initial values of static cells (`ImageMatches`, Route S).
-/
import Scc.Sem.Rows1
import Scc.Cert.LinkImage

namespace Scc.Sem

open Kraken Kraken.Promising

/-- Two distinct members of a list pairwise related by a symmetric relation
are related. -/
theorem List.pairwise_mem_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact h1 ▸ h.1 _ h2
    · exact h2 ▸ hs _ _ (h.1 _ h1)
    · exact List.pairwise_mem_ne hs h.2 h1 h2 hne

namespace MemRelP

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

/-- **The relation at the start**: empty source memory, no target message,
the empty map; only the layout injection is left. -/
theorem start {tm : Memory} (htm : tm.msgs = #[])
    (hs : ∀ l b, Λ.static l = some b → lbl l = some b)
    (hr : ∀ l b, lbl l = some b → b % 8 = 0 ∧ ((lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data))
    (hd : ∀ l l' b b', l ≠ l' → lbl l = some b → lbl l' = some b' → (lrange lsize l b).Disjoint (lrange lsize l' b')) :
    MemRelP Λ lbl lsize (fun _ => none) tm #[] [] [] [] where
  lbl_static := hs
  lbl_range := hr
  lbl_disj := hd
  lbl_mem m hm := by simp at hm
  mem_rep k m hk := by simp at hk
  ts_first k m hk := by simp at hk
  ts_mono k1 _ _ _ m1 _ hm1 := by simp at hm1
  mem_onto k' m' hg := by simp [Memory.get?, htm] at hg
  ts_dom _ _ := rfl
  tp_nodup := List.nodup_nil
  sp_nodup := List.nodup_nil
  tp_le _ hp := absurd hp List.not_mem_nil
  sp_lt _ hk := absurd hk List.not_mem_nil
  prom_corr _ _ h := by cases h
  tq_nodup := List.nodup_nil
  tq_le _ hp := absurd hp List.not_mem_nil
  tq_img _ _ _ := List.not_mem_nil
  tp_tq _ hp := absurd hp List.not_mem_nil

end MemRelP

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

/-- **The invariant at the start**: a thread with no promise, a target
memory with no message, the empty source memory. -/
theorem start {t : Thread I} {tm : Memory} (hp : t.prom = []) (htm : tm.msgs = #[])
    (hs : ∀ l b, Λ.static l = some b → lbl l = some b)
    (hr : ∀ l b, lbl l = some b → b % 8 = 0 ∧ ((lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data))
    (hd : ∀ l l' b b', l ≠ l' → lbl l = some b → lbl l' = some b' → (lrange lsize l b).Disjoint (lrange lsize l' b')) :
    Inv1 Λ lbl lsize (fun _ => none) t tm #[] where
  mem := hp ▸ MemRelP.start htm hs hr hd
  coh k w hg := by simp [Memory.get?, htm] at hg
  narrow k w hg := by simp [Memory.get?, htm] at hg

end Inv1

open Scc.Cert.Link in
/-- **Each static label at a data symbol of its own**: `name l` is the
assembler symbol the compiler gives static label `l`; it is one of the data
symbols the image check covers (`symRanges`), at `l`'s address, 8-aligned,
with an item of at least `l`'s words; distinct static labels have distinct
symbols. -/
structure StaticSyms (Λ : Layout) (secs : DataSecs) (code : String → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (name : WeakMem.AllocLabel → String) : Prop where
  sym : ∀ l b, Λ.static l = some b → b % 8 = 0 ∧
    ∃ its, (name l, b, its) ∈ symRanges Λ secs ∧ 8 * lsize l ≤ (itemBytes code its).length
  inj : ∀ l l' b b', Λ.static l = some b → Λ.static l' = some b' → name l = name l' → l = l'

namespace StaticSyms

open Scc.Cert.Link

variable {Λ : Layout} {secs : DataSecs} {code : String → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {name : WeakMem.AllocLabel → String}

/-- **No static label**: nothing to place. -/
theorem of_none (h : ∀ l, Λ.static l = none) : StaticSyms Λ secs code lsize name where
  sym l b hb := by rw [h l] at hb; cases hb
  inj l _ b _ hb := by rw [h l] at hb; cases hb

/-- **A static label is an aligned word range of `Λ.data`** (`image_sub`). -/
theorem range (hs : StaticSyms Λ secs code lsize name) (himg : imageOk Λ secs code = true) :
    ∀ l b, Λ.static l = some b → b % 8 = 0 ∧ ((lrange lsize l b).Sub Λ.heap ∨ (lrange lsize l b).Sub Λ.data) := by
  intro l b hb
  obtain ⟨hal, its, hm, hlen⟩ := hs.sym l b hb
  obtain ⟨h1, h2⟩ := image_sub himg hm
  refine ⟨hal, .inr ⟨h1, ?_⟩⟩
  simp only [lrange]
  omega

/-- **Distinct static labels are disjoint** (`image_disj`). -/
theorem disj (hs : StaticSyms Λ secs code lsize name) (himg : imageOk Λ secs code = true) :
    ∀ l l' b b', l ≠ l' → Λ.static l = some b → Λ.static l' = some b' →
      (lrange lsize l b).Disjoint (lrange lsize l' b') := by
  intro l l' b b' hne hb hb'
  obtain ⟨-, its, hm, hlen⟩ := hs.sym l b hb
  obtain ⟨-, its', hm', hlen'⟩ := hs.sym l' b' hb'
  have hne' : (name l, b, its) ≠ (name l', b', its') := fun he =>
    hne (hs.inj l l' b b' hb hb' (congrArg Prod.fst he))
  have := List.pairwise_mem_ne (fun _ _ h => h.symm) (image_disj himg) hm hm' hne'
  simp only at this
  simp only [lrange, Range.Disjoint]
  omega

end StaticSyms

namespace Inv1

variable {I : ISA} {Λ : Layout} {lsize : WeakMem.AllocLabel → Nat}

open Scc.Cert.Link in
/-- **The invariant at the start, static labels where `Λ` puts them**: the
injection `Λ.static`, its layout clauses from the static link's image
check. -/
theorem start_static {secs : DataSecs} {code : String → Option Nat} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true) (hss : StaticSyms Λ secs code lsize name)
    {t : Thread I} {tm : Memory} (hp : t.prom = []) (htm : tm.msgs = #[]) :
    Inv1 Λ Λ.static lsize (fun _ => none) t tm #[] :=
  start hp htm (fun _ _ h => h) (hss.range himg) (hss.disj himg)

end Inv1

open Scc.Cert.Link in
/-- A layout with no static data has its static labels placed. -/
example (secs : DataSecs) (code : String → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (name : WeakMem.AllocLabel → String) : StaticSyms trivLayout secs code lsize name :=
  .of_none fun _ => rfl

end Scc.Sem
